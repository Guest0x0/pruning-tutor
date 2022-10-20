
open Syntax



let apply vf va =
    match vf with
    | Value.Fun(_, f)    -> f va
    | Value.Stuck(h, sp) -> Value.Stuck(h, Value.App(sp, va))
    | _                  -> failwith "runtime error: not a function"

let rec apply_spine vf = function
    | Value.EmptySp        -> vf
    | Value.App(sp', argv) -> apply (apply_spine vf sp') argv


let rec force value =
    match value with
    | Value.Stuck(Meta m, args) ->
        begin match MetaContext.find_meta m with
        | Free _   -> value
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
        | Value.Free _        -> Value.(Stuck(Meta meta, EmptySp))
        | Value.Solved v      -> v
        | exception Not_found -> failwith("unbound meta ?" ^ string_of_int meta)



let rec quote level value =
    match force value with
    | Value.Stuck(head, sp) ->
        quote_spine level (quote_head level head) sp
    | Value.Type ->
        Core.Type
    | Value.TyFun(name, a, b) ->
        Core.TyFun(name, quote level a, quote (level + 1) @@ b @@ Value.stuck_local level)
    | Value.Fun(name, f) ->
        Core.Fun(name, quote (level + 1) @@ f @@ Value.stuck_local level)

and quote_head level = function
    | Value.Lvl lvl   -> Core.Idx(level - lvl - 1)
    | Value.Meta meta -> Core.Meta meta

and quote_spine level headC = function
    | Value.EmptySp        -> headC
    | Value.App(sp', argv) -> Core.App(quote_spine level headC sp', quote level argv)
