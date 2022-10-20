
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
        (* type-in-type, for simplicity *)
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
                let meta = MetaContext.fresh_meta (Unify.env_to_tyfun ctx.tenv Type) in
                Stuck(Meta meta, Unify.boundvars_to_spine ctx.level ctx.tenv)
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
        let typ_meta  = MetaContext.fresh_meta (Unify.env_to_tyfun ctx.tenv Type) in
        let sp = Unify.boundvars_to_spine ctx.level ctx.tenv in
        let typ = Stuck(Meta typ_meta, sp) in
        let hole_meta = MetaContext.fresh_meta typ in
        typ, quote ctx.level @@ Stuck(Meta hole_meta, sp)

    | Surface.Unify(lhs, rhs) ->
        let lhs_typ, lhsC = infer ctx lhs in
        let rhs_typ, rhsC = infer ctx rhs in
        Unify.unify ctx.level ctx.tenv Type lhs_typ rhs_typ;
        Unify.unify ctx.level ctx.tenv lhs_typ (eval ctx.venv lhsC) (eval ctx.venv rhsC);
        lhs_typ, lhsC


and check_typ ctx expr =
    let typ, core = infer ctx expr in
    match Unify.unify ctx.level ctx.tenv Type typ Type with
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
                Unify.unify ctx.level ctx.tenv Type annV a;
                annV
            | None ->
                a
        in
        let bodyC = check (add_bound name arg_typ ctx) (b @@ stuck_local ctx.level) body in
        Core.Fun(name, bodyC)

    | typ, Surface.Hole ->
        let hole_meta = MetaContext.fresh_meta (Unify.env_to_tyfun ctx.tenv typ) in
        quote ctx.level @@ Stuck(Meta hole_meta, Unify.boundvars_to_spine ctx.level ctx.tenv)

    | typ, Surface.Unify(lhs, rhs) ->
        let lhsC = check ctx typ lhs in
        let rhsC = check ctx typ rhs in
        Unify.unify ctx.level ctx.tenv typ (eval ctx.venv lhsC) (eval ctx.venv rhsC);
        lhsC

    | _ ->
        let typ', core = infer ctx expr in
        Unify.unify ctx.level ctx.tenv Type typ typ';
        core
