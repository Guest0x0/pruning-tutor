
open Syntax
open Value
open Normalize


type context =
    { level : int
    ; venv  : value list
    ; tenv  : Value.env }

let empty_ctx =
    { level = 0
    ; venv  = []
    ; tenv  = Empty }

let add_bound name typ ctx =
    { level = ctx.level + 1
    ; venv  = stuck_local ctx.level :: ctx.venv
    ; tenv  = Bound(ctx.tenv, name, typ) }

let add_defined name typ value ctx =
    { level = ctx.level + 1
    ; venv  = value :: ctx.venv
    ; tenv  = Defined(ctx.tenv, name, typ, value) }


let find_var name ctx =
    let rec loop idx env =
        match env with
        | Empty ->
            failwith("unbound variable " ^ name)
        | Bound(env', name', typ) | Defined(env', name', typ, _) ->
            if name' = name
            then idx, typ
            else loop (idx + 1) env'
    in
    loop 0 ctx.tenv


let rec infer ctx expr =
    match expr with
    | Surface.Var name ->
        let idx, typ = find_var name ctx in
        typ, Core.Idx idx

    | Surface.Let(name, rhs, body) ->
        let rhs_typ , rhsC  = infer ctx rhs in
        let body_typ, bodyC = infer (add_defined name rhs_typ (eval ctx.venv rhsC) ctx) body in
        body_typ, Core.Let(name, rhsC, bodyC)

    | Surface.Ann(expr', ann) ->
        let annC = check_typ ctx ann in
        let typ = eval ctx.venv annC in
        let exprC = check ctx typ expr' in
        typ, exprC

    | Surface.Type ->
        Type, Core.Type

    | Surface.TyFun(name, a, b) ->
        let aC = check_typ ctx a in
        let aV = eval ctx.venv aC in
        let bC = check_typ (add_bound name aV ctx) b in
        Type, Core.TyFun(name, aC, bC)

    | Surface.Fun(name, ann, body) ->
        let arg_typ =
            match ann with
            | Some ann ->
                let annC = check_typ ctx ann in
                eval ctx.venv annC
            | None ->
                let meta = MetaContext.fresh_meta () in
                Stuck(Meta meta, List.init ctx.level stuck_local)
        in
        let ret_typ, bodyC = infer (add_bound name arg_typ ctx) body in
        let ret_typC = quote (ctx.level + 1) ret_typ in
        TyFun(name, arg_typ, fun v -> eval (v :: ctx.venv) ret_typC), Core.Fun(name, bodyC)

    | Surface.App(func, arg) ->
        let func_typ, funcC = infer ctx func in
        begin match force func_typ with
        | TyFun(_, a, b) ->
            let argC = check ctx a arg in
            b (eval ctx.venv argC), Core.App(funcC, argC)
        | _ ->
            failwith "function expected"
        end

    | Surface.Hole ->
        let typ_meta  = MetaContext.fresh_meta () in
        let hole_meta = MetaContext.fresh_meta () in
        let args = Unify.env_to_args ctx.tenv in
        Stuck(Meta typ_meta, args), quote ctx.level @@ Stuck(Meta hole_meta, args)


and check_typ ctx expr =
    let typ, core = infer ctx expr in
    match Unify.unify ctx.level typ Type with
    | ()          -> core
    | exception _ -> failwith "type expected"


and check ctx typ expr =
    match force typ, expr with
    | typ, Surface.Let(name, rhs, body) ->
        let rhs_typ, rhsC = infer ctx rhs in
        let bodyC = check (add_defined name rhs_typ (eval [] rhsC) ctx) typ body in
        Core.Let(name, rhsC, bodyC)
    | TyFun(_, a, b), Surface.Fun(name, ann, body) ->
        let arg_typ =
            match ann with
            | Some ann ->
                let annC = check_typ ctx ann in
                let annV = eval [] annC in
                Unify.unify ctx.level annV a;
                annV
            | None ->
                a
        in
        let bodyC = check (add_bound name arg_typ ctx) (b @@ stuck_local ctx.level) body in
        Core.Fun(name, bodyC)
    | _, Surface.Hole ->
        let hole_meta = MetaContext.fresh_meta () in
        quote ctx.level @@ Stuck(Meta hole_meta, Unify.env_to_args ctx.tenv)
    | _ ->
        let typ', core = infer ctx expr in
        Unify.unify ctx.level typ typ';
        core
