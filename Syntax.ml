
type meta  = int
type level = int

module Value = struct
    type value =
        | Stuck of head * value list
        | Type
        | TyFun of string * value * (value -> value)
        | Fun   of string * (value -> value)

    and head =
        | Lvl  of level
        | Meta of meta

    let stuck_local lvl = Stuck(Lvl lvl, [])


    type meta_info =
        | Free
        | Solved of value

    type env =
        | Empty
        | Bound   of env * string * value
        | Defined of env * string * value * value
end


module Core = struct
    type expr =
        | Idx   of int
        | Let   of string * expr * expr
        | Type
        | TyFun of string * expr * expr
        | Fun   of string * expr
        | App   of expr * expr
        | Meta  of meta
end


module Surface = struct
    type expr =
        | Var   of string
        | Let   of string * expr * expr
        | Ann   of expr * expr
        | Type
        | TyFun of string * expr * expr
        | Fun   of string * expr option * expr
        | App   of expr * expr
        | Hole
end
