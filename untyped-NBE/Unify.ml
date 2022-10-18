
open Syntax
open Value
open Normalize



(* some utilities *)
let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))

let level_to_args level = List.init level (fun idx -> stuck_local (level - idx - 1))


(* A [psubst] is a partial substitution, such that all values in it are bound variables.
   Here:
   - [dom] is (the length of) the domain of the partial substitution
   - [cod] is (the length of) the codomain of the partial substitution
   - [map] is a parial mapping from variables in [dom] to variables in [cod],
   represented as an association list *)
type psubst =
    { dom : level
    ; cod : level
    ; map : (level * level) list }


let empty_psubst =
    { dom = 0
    ; cod = 0
    ; map = [] }


(* Add a new bound variable to a partial substitution [psub].
   Assume:
       Γ |- psub : Δ
   then:
       Γ, x : A[psub] |- add_boundvar psub : Δ, x : A
   such that:
       x[add_boundvar psub] = x *)
let add_boundvar psub =
    { dom = psub.dom + 1
    ; cod = psub.cod + 1
    ; map = (psub.dom, psub.cod) :: psub.map }



(* Calculate the inverse substitution of a list of arguments.
   The list of arguments [args] should live in a context with length [level].
   That is, assume:
       Γ(level) |- args : Δ
   we should have:
       Δ |- invert_args level args : Γ *)
let rec invert_args level args =
    match args with
    | [] ->
        { empty_psubst with dom = level }
    | Stuck(Lvl lvl, []) :: args' ->
        (* We are now processing the [psub.cod]-th argument,
           it should correspond to the [level]-th bound variable
           in the codomain of the inverse substitution *)
        let psub = invert_args level args' in
        if List.mem_assoc lvl psub.map
        then failwith "the same variable occurs twice in arguments of meta"
        else { psub with cod = psub.cod + 1; map = (lvl, psub.cod) :: psub.map }
    | _ ->
        failwith "arguments of meta not a bound variable"




(* Every [true] in a pruning [pr : pruning]
   indicates that the item at the same position in an argument list should be discarded. *)
type pruning = bool list

(* [prune_args pr args] drop the arguments that should be pruned in [args],
   according to [pr]. *)
let rec prune_args pr args =
    match pr, args with
    | [], [] ->
        []
    | should_prune :: pr', arg :: args' ->
        let args' = prune_args pr' args' in
        if should_prune
        then args'
        else arg :: args'
    | _ ->
        failwith "runtime error"


(* Let [args] be a list of bound variables,
   [args_to_pruning pr args] calculates a pruning that prune away those variables in [args]
   that do not fall in the domain of [psub]. *)
let args_to_pruning psub args =
    args |> List.map @@ fun argv ->
    match force argv with
    | Stuck(Lvl lvl, []) -> not (List.mem_assoc lvl psub.map)
    | _                  -> failwith "arguments of meta not a bound variable"


(* [intersect_args args1 args2] calculates a pruning that prune away those arguments
   that differ in [args1] and [args2]. *)
let rec intersect_args args1 args2 =
    match args1, args2 with
    | [], [] ->
        []
    | Stuck(Lvl lvl1, []) :: args1'
    , Stuck(Lvl lvl2, []) :: args2' ->
        (lvl1 <> lvl2) :: intersect_args args1' args2'
    | _ ->
        failwith "runtime error"


(* [discard_defined env] discards the defined variables in [env]. *)
let rec discard_defined env : pruning =
    match env with
    | Empty                  -> []
    | Bound(env', _, _)      -> false :: discard_defined env'
    | Defined(env', _, _, _) -> true  :: discard_defined env'


(* [boundvars_to_args level env] returns the list of all bound variables in [env]
   (of length [level]). *)
let boundvars_to_args level env =
    prune_args (discard_defined env) (level_to_args level)




(* [apply_psubst m psub v] apply the partial renaming [psub] to value [v],
   checking for occurence of [m] at the same time.
   [v] should live in [psub.dom], and the result should live in [psub.cod], i.e.:

       Γ(psub.cod) |- psub : Δ(psub.dom)
       Δ(psub.dom) |- v : A
      --------------------------------------
       Γ(psub.cod) |- apply_psubst m psub v : A[psub]

   Since [apply_psubst] must recurse down the structure of [v],
   the result is a core expression, similar to quoting in NBE.

   When no occurs check need to be performed, [m] can be set to [-1]. *)
let rec apply_psubst m psub value =
    match force value with
    | Stuck(Lvl lvl, args) -> 
        begin match List.assoc lvl psub.map with
        | lvl' ->
            List.fold_right (fun a f -> Core.App(f, apply_psubst m psub a))
                args (quote psub.cod @@ stuck_local lvl')
        | exception Not_found -> failwith "variable may escape its scope"
        end

    (* Failed occurs check *)
    | Stuck(Meta m', _) when m' = m ->
        failwith("meta ?" ^ string_of_int m ^ " occurs recursively in its solution")

   (* Renaming a meta differnt from [m].
      This is the so-called "pruning" operation
      and corresponds to the flex-flex case of the rewrite rules. *)
    | Stuck(Meta m', args) ->
        let level = List.length args in
        let pr = args_to_pruning psub args in
        if List.for_all not pr
        then List.fold_right (fun a f -> Core.App(f, apply_psubst m psub a)) args (Core.Meta m')
        else
            let new_meta = MetaContext.fresh_meta () in
            let solution =
                let args = level_to_args level in
                Stuck(Meta new_meta, prune_args pr args)
                |> Normalize.quote level
                |> Normalize.eval []
            in
            let _ = MetaContext.solve_meta m' solution in
            List.fold_right (fun a f -> Core.App(f, apply_psubst m psub a))
                (prune_args pr args) (Core.Meta new_meta)
    | Type ->
        Core.Type
    | TyFun(name, a, b) ->
        Core.TyFun(name, apply_psubst m psub a, apply_psubst m (add_boundvar psub) @@ b @@ stuck_local psub.dom)
    | Fun(name, f) ->
        Core.Fun(name, apply_psubst m (add_boundvar psub) @@ f @@ stuck_local psub.dom)



let rec unify level v1 v2 =
    match force v1, force v2 with
    | Type, Type ->
        ()

    | TyFun(_, a1, b1), TyFun(_, a2, b2) ->
        unify level a1 a2;
        let var = stuck_local level in
        unify (level + 1) (b1 var) (b2 var)

    (* Performs η expansion if necessary,
       so that the conversion check respects η *)
    | Fun(_, _), _
    | _, Fun(_, _) ->
        let var = stuck_local level in
        unify (level + 1) (apply v1 var) (apply v2 var)

    (* flex-flex case with same meta *)
    | Stuck(Meta m1, args1), Stuck(Meta m2, args2) when m1 = m2 ->
        let pr = intersect_args args1 args2 in
        if List.exists Fun.id pr then
            let level = List.length args1 in
            let new_meta = MetaContext.fresh_meta () in
            let solution =
                let args = level_to_args level in
                Stuck(Meta new_meta, prune_args pr args)
                |> Normalize.quote level
                |> Normalize.eval []
            in
            MetaContext.solve_meta m1 solution

    (* flex-rigid or flex-flex with different metas *)
    | Stuck(Meta m, args), v
    | v, Stuck(Meta m, args) ->
        let psub = invert_args level args in
        let solution =
            apply_psubst m psub v
            |> make_fun psub.cod
            |> eval []
        in
        MetaContext.solve_meta m solution

    | Stuck(Lvl lvl1, args1), Stuck(Lvl lvl2, args2) when lvl1 = lvl2 ->
        begin try List.iter2 (unify level) args1 args2 with
          Invalid_argument _ -> failwith "unsolvable equation"
        end

    | _ ->
        failwith "unsolvable equation"
