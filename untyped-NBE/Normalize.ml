
open Syntax



let apply vf va =
    match vf with
    | Value.Fun(_, f)      -> f va
    | Value.Stuck(h, args) -> Value.Stuck(h, va :: args)
    | _                    -> failwith "runtime error: not a function"

let apply_spine vf args = List.fold_right (Fun.flip apply) args vf


let rec force value =
    match value with
    | Value.Stuck(Meta m, args) ->
        begin match MetaContext.find_meta m with
        | Free     -> value
        | Solved v -> force (apply_spine v args)
        end
    | _ ->
        value

let rec eval env = function
    | Core.Idx idx           -> List.nth env idx
    | Core.Let(_, rhs, body) -> eval (eval env rhs :: env) body 
    | Core.Type              -> Value.Type
    | Core.TyFun(name, a, b) -> Value.TyFun(name, eval env a, fun v -> eval (v :: env) b)
    | Core.Fun(name, body)   -> Value.Fun(name, fun v -> eval (v :: env) body)
    | Core.App(vf, va)       -> apply (eval env vf) (eval env va)
    | Core.Meta meta         ->
        match MetaContext.find_meta meta with
        | Value.Free          -> Value.(Stuck(Meta meta, []))
        | Value.Solved v      -> v
        | exception Not_found -> failwith("unbound meta ?" ^ string_of_int meta)



let rec quote level value =
    match force value with
    | Value.Stuck(head, args) ->
        List.fold_right (fun a f -> Core.App(f, quote level a)) args (quote_head level head)
    | Value.Type ->
        Core.Type
    | Value.TyFun(name, a, b) ->
        Core.TyFun(name, quote level a, quote (level + 1) @@ b @@ Value.stuck_local level)
    | Value.Fun(name, f) ->
        Core.Fun(name, quote (level + 1) @@ f @@ Value.stuck_local level)

and quote_head level = function
    | Value.Lvl lvl   -> Core.Idx(level - lvl - 1)
    | Value.Meta meta -> Core.Meta meta
