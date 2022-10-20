
open Syntax
open Value
open Normalize



(* some utilities *)
let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))

let rec level_to_spine = function
    | 0 -> EmptySp
    | n -> App(level_to_spine (n - 1), stuck_local (n - 1))


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
   The list of arguments [sp] should live in a context with length [level].
   That is, assume:
       Γ(level) |- sp : Δ
   we should have:
       Δ |- invert_spine level sp : Γ *)
let rec invert_spine level sp =
    match sp with
    | EmptySp ->
        { empty_psubst with dom = level }
    | App(sp', Stuck(Lvl lvl, EmptySp)) ->
        (* We are now processing the [psub.cod]-th argument,
           it should correspond to the [psub.cod]-th bound variable
           in the codomain of the inverse substitution *)
        let psub = invert_spine level sp' in
        if List.mem_assoc lvl psub.map
        then failwith "the same variable occurs twice in arguments of meta"
        else { psub with cod = psub.cod + 1; map = (lvl, psub.cod) :: psub.map }
    | _ ->
        failwith "arguments of meta not a bound variable"



(* A [pruning] is a series of instruction indicating which arguments to discard.
   Note that syntactically, pruning is in reverse order of argument lists.
   See [prune_spine] below for their relationship. *)
type pruning =
    | EmptyPr
    | Keep of pruning
    | Skip of pruning

let rec pruning_length = function
    | EmptyPr  -> (0, 0)
    | Keep pr' -> let (tot, rem) = pruning_length pr' in (tot + 1, rem + 1)
    | Skip pr' -> let (tot, rem) = pruning_length pr' in (tot + 1, rem)


(* [prune_spine pr sp] drop the arguments that should be pruned in [sp],
   according to [pr]. *)
let rec prune_spine pr sp =
    match pr, sp with
    | EmptyPr , EmptySp     -> EmptySp
    | Keep pr', App(sp', v) -> App(prune_spine pr' sp', v)
    | Skip pr', App(sp', _) -> prune_spine pr' sp'
    | _                     -> failwith "runtime error"


(* Let [sp] be a list of bound variables,
   [spine_to_pruning pr sp] calculates a pruning that prune away those variables in [sp]
   that do not fall in the domain of [psub]. *)
let rec spine_to_pruning psub = function
    | EmptySp ->
        EmptyPr
    | App(sp', Stuck(Lvl lvl, EmptySp)) -> 
        if List.mem_assoc lvl psub.map
        then Keep (spine_to_pruning psub sp')
        else Skip (spine_to_pruning psub sp')
    | _ ->
        failwith "arguments of meta not a bound variable"


(* [intersect_spine sp1 sp2] calculates a pruning that prune away those arguments
   that differ in [sp1] and [sp2]. *)
let rec intersect_spine sp1 sp2 =
    match sp1, sp2 with
    | EmptySp, EmptySp ->
        EmptyPr
    | App(sp1', Stuck(Lvl lvl1, EmptySp))
    , App(sp2', Stuck(Lvl lvl2, EmptySp)) ->
        if lvl1 = lvl2
        then Keep (intersect_spine sp1' sp2')
        else Skip (intersect_spine sp1' sp2')
    | _ ->
        failwith "runtime error"


(* [discard_defined env] discards the defined variables in [env]. *)
let rec discard_defined env : pruning =
    match env with
    | Empty                  -> EmptyPr
    | Bound(env', _, _)      -> Keep (discard_defined env')
    | Defined(env', _, _, _) -> Skip (discard_defined env')


(* [boundvars_to_spine level env] returns the list of all bound variables in [env]
   (of length [level]). *)
let boundvars_to_spine level env =
    prune_spine (discard_defined env) (level_to_spine level)



(* the following operations are mutually recursive. *)

(* [prune_tyfun pr typ] prune away the arguments in [typ] (expected to be a function type)
   according to [pr]. *)
let rec prune_tyfun pr typ =
    (* [psub] is the partial substitution that forgets those variables
       that are already pruned away. *)
    let rec loop psub pr typ =
        match pr, force typ with
        | EmptyPr, typ ->
            apply_psubst (-1) psub typ
        | Keep pr', TyFun(name, a, b) ->
            Core.TyFun( name
                      , apply_psubst (-1) psub a
                      , loop (add_boundvar psub) pr' (b @@ stuck_local psub.dom) )
        | Skip pr', TyFun(_, _, b) ->
            loop { psub with dom = psub.dom + 1 } pr' (b @@ stuck_local psub.dom)
        | _ ->
            failwith "runtime error"
    in
    eval [] @@ loop empty_psubst pr typ


(* [apply_psubst m psub v] apply the partial substitution [psub] to value [v],
   checking for occurence of [m] at the same time.
   [v] should live in [psub.dom], and the result should live in [psub.cod], i.e.:

       Γ(psub.cod) |- psub : Δ(psub.dom)
       Δ(psub.dom) |- v : A
      --------------------------------------
       Γ(psub.cod) |- apply_psubst m psub v : A[psub]

   Since [apply_psubst] must recurse down the structure of [v],
   the result is a core expression, similar to quoting in NBE.

   When no occurs check need to be performed, [m] can be set to [-1]. *)
and apply_psubst m psub value =
    match force value with
    | Stuck(Lvl lvl, sp) -> 
        begin match List.assoc lvl psub.map with
        | lvl' ->
            apply_psubst_spine m psub (Core.Idx(psub.cod - lvl' - 1)) sp
        | exception Not_found ->
            failwith "variable may escape its scope"
        end

    (* Failed occurs check *)
    | Stuck(Meta m', _) when m' = m ->
        failwith("meta ?" ^ string_of_int m ^ " occurs recursively in its solution")

    (* Substituting a meta differnt from [m].
       This is the so-called "pruning" operation
       and corresponds to the flex-flex case of the rewrite rules. *)
    | Stuck(Meta m', sp) ->
        let [@warning "-8"] (Free typ) = MetaContext.find_meta m' in
        let pr = spine_to_pruning psub sp in
        let (sp_len, pruned_len) = pruning_length pr in
        if sp_len = pruned_len
        then apply_psubst_spine m psub (Core.Meta m') sp
        else
            let new_meta = MetaContext.fresh_meta (prune_tyfun pr typ) in
            let solution =
                Stuck(Meta new_meta, prune_spine pr @@ level_to_spine sp_len)
                |> Normalize.quote sp_len
                |> make_fun sp_len
                |> Normalize.eval []
            in
            let _ = MetaContext.solve_meta m' solution in
            apply_psubst_spine m psub (Core.Meta new_meta) (prune_spine pr sp)

    | Type ->
        Core.Type
    | TyFun(name, a, b) ->
        Core.TyFun(name, apply_psubst m psub a, apply_psubst m (add_boundvar psub) @@ b @@ stuck_local psub.dom)
    | Fun(name, f) ->
        Core.Fun(name, apply_psubst m (add_boundvar psub) @@ f @@ stuck_local psub.dom)


and apply_psubst_spine m psub headC = function
    | EmptySp        -> headC
    | App(sp', argv) -> Core.App(apply_psubst_spine m psub headC sp', apply_psubst m psub argv)



let env_to_tyfun env typ =
    (* [loop env] returns a pair [(psub, add_args)],
       where [psub] is a partial substitution obtained by forgetting all the defined variables
       in [env],
       and [add_args : value -> value] is a function that, when applied to a type,
       prefix it with a [TyFun] for each variable in [env]. *)
    let rec loop env =
        match env with
        | Empty ->
            empty_psubst, Fun.id 
        | Bound(env', name, a) ->
            let psub, add_args = loop env' in
            ( add_boundvar psub
            , fun ret_typ -> add_args @@ Core.TyFun(name, apply_psubst (-1) psub a, ret_typ) )
        | Defined(env', _, _, _) ->
            let psub, add_args = loop env' in
            { psub with dom = psub.dom + 1 }, add_args
    in
    let psub, add_args = loop env in
    eval [] @@ add_args @@ apply_psubst (-1) psub typ




let rec unify level env typ v1 v2 =
    match force typ, force v1, force v2 with
    | Type, Type, Type ->
        ()

    | Type, TyFun(name, a1, b1), TyFun(_, a2, b2) ->
        unify level env typ a1 a2;
        let var = stuck_local level in
        unify (level + 1) (Bound(env, name, a1)) typ (b1 var) (b2 var)

    | TyFun(name, a, b), v1, v2 ->
        let var = stuck_local level in
        unify (level + 1) (Bound(env, name, a)) (b var) (apply v1 var) (apply v2 var)

    (* flex-flex case with same meta *)
    | _, Stuck(Meta m1, sp1), Stuck(Meta m2, sp2) when m1 = m2 ->
        let [@warning "-8"] (Free typ) = MetaContext.find_meta m1 in
        let pr = intersect_spine sp1 sp2 in
        let (sp_len, rem_len) = pruning_length pr in
        if sp_len = rem_len then
            let new_meta = MetaContext.fresh_meta (prune_tyfun pr typ) in
            let solution =
                Stuck(Meta new_meta, prune_spine pr @@ level_to_spine sp_len)
                |> Normalize.quote level
                |> make_fun sp_len
                |> Normalize.eval []
            in
            MetaContext.solve_meta m1 solution

    (* flex-rigid or flex-flex with different metas *)
    | _, Stuck(Meta m, sp), v
    | _, v, Stuck(Meta m, sp) ->
        let psub = invert_spine level sp in
        let solution =
            apply_psubst m psub v
            |> make_fun psub.cod
            |> eval []
        in
        MetaContext.solve_meta m solution

    | _, Stuck(Lvl lvl1, sp1), Stuck(Lvl lvl2, sp2) when lvl1 = lvl2 ->
        let head_typ = lookup_idx (level - lvl1 - 1) env in
        ignore (unify_spine level env head_typ sp1 sp2)

    | _ ->
        failwith "unsolvable equation"


and unify_spine level env head_typ sp1 sp2 =
    match sp1, sp2 with
    | EmptySp, EmptySp ->
        head_typ
    | App(sp1', v1), App(sp2', v2) ->
        begin match force @@ unify_spine level env head_typ sp1' sp2' with
        | TyFun(_, a, b) ->
            unify level env a v1 v2;
            b v1
        | _ ->
            failwith "runtime error"
        end
    | _ ->
        failwith "unsolvable equation"
