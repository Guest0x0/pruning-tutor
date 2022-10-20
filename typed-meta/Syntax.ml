
type meta  = int
type level = int

module Value = struct
    type value =
        | Stuck of head * spine
        | Type
        (* The strings are variable names, used for pretty printing only *)
        | TyFun of string * value * (value -> value)
        | Fun   of string * (value -> value)

    and head =
        (* de Bruijn level *)
        | Lvl  of level
        | Meta of meta

    and spine =
        | EmptySp
        | App of spine * value

    let stuck_local lvl = Stuck(Lvl lvl, EmptySp)


    type meta_info =
        | Free   of value
        | Solved of value

    type env =
        | Empty
        | Bound   of env * string * value
        | Defined of env * string * value * value

    let rec lookup_idx idx env =
        match idx, env with
        | _, Empty                                        -> raise Not_found
        | 0, (Bound(_, _, typ)  | Defined(_, _, typ, _))  -> typ
        | n, (Bound(env', _, _) | Defined(env', _, _, _)) -> lookup_idx (n - 1) env'
end


module Core = struct
    type expr =
        (* de Bruijn index *)
        | Idx   of int
        (* The strings are variable names, used for pretty printing only *)
        | Let   of string * expr * expr
        | Type
        | TyFun of string * expr * expr
        | Fun   of string * expr
        | App   of expr * expr
        | Meta  of meta
end


module Surface = struct
    type expr =
        (* surface syntax uses named variables *)
        | Var   of string
        | Let   of string * expr * expr
        | Ann   of expr * expr
        | Type
        | TyFun of string * expr * expr
        | Fun   of string * expr option * expr
        | App   of expr * expr
        | Hole
        | Unify of expr * expr
end
