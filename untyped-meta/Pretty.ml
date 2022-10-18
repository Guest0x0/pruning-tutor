
open Syntax
open Format


let prec_binder = 10
let prec_app    = 20


type pp_context =
    { names   : string list
    ; level   : int
    ; prec    : int }


let add_var name ctx =
    let name = if List.mem name ctx.names then "" else name in
    ( name, { ctx with names = name :: ctx.names; level = ctx.level + 1 })

let pp_name fmt (name, lvl) =
    if name = ""
    then fprintf fmt "$%d" lvl
    else fprintf fmt "%s" name


let incr_prec  ctx = { ctx with prec  = ctx.prec  + 1 }


let rec pp_core ctx fmt core =
    match core with
    | Core.Idx idx ->
        pp_name fmt (List.nth ctx.names idx, ctx.level - idx - 1)

    | Core.Let(name, rhs, body) when ctx.prec <= prec_binder ->
        let name, ctx' = add_var name ctx in
        fprintf fmt "@[<hv>@[<hv2>let %s =@ %a@]@ in@ %a@]"
            name (pp_core { ctx with prec = prec_binder }) rhs
            (pp_core { ctx' with prec = prec_binder }) body

    | Core.Type ->
        fprintf fmt "Type"

    | Core.TyFun(name, a, b) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>forall %a@]"
            (pp_core_tyfun { ctx with prec = prec_binder }) (name, a, b)

    | Core.Fun(name, body) when ctx.prec <= prec_binder ->
        fprintf fmt "@[<hov2>fun %a@]"
            (pp_core_fun { ctx with prec = prec_binder }) (name, body)

    | Core.App(f, a) when ctx.prec <= prec_app ->
        fprintf fmt "@[<hov2>%a@]" (pp_core_app { ctx with prec = prec_app }) (f, a)

    | Core.Meta meta ->
        fprintf fmt "?%d" meta

    | _ ->
        fprintf fmt "(%a)" (pp_core { ctx with prec = 0 }) core


and pp_core_tyfun ctx fmt (name, a, b) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "(%a : %a)"
        pp_name (name, ctx.level)
        (pp_core @@ incr_prec ctx) a;
    match b with
    | Core.TyFun(name', a', b') -> fprintf fmt "@ %a" (pp_core_tyfun ctx') (name', a', b')
    | _                         -> fprintf fmt " ->@ %a" (pp_core ctx') b


and pp_core_fun ctx fmt (name, body) =
    let name, ctx' = add_var name ctx in
    fprintf fmt "%a" pp_name (name, ctx.level);
    match body with
    | Core.Fun(name', body') -> fprintf fmt "@ %a" (pp_core_fun ctx') (name', body')
    | _                      -> fprintf fmt " ->@ %a" (pp_core ctx') body


and  pp_core_app ctx fmt (f, a) =
    begin match f with
    | Core.App(f', a') -> pp_core_app ctx fmt (f', a')
    | _             -> pp_core ctx fmt f
    end;
    fprintf fmt "@ %a" (pp_core @@ incr_prec ctx) a



let rec names_of_env = function
    | Value.Empty                                                  -> []
    | Value.Bound(env', name, _) | Value.Defined(env', name, _, _) -> name :: names_of_env env'

let pp_core names =
    pp_core { names; level = List.length names; prec = 0 }
