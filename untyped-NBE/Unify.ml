
open Syntax
open Value
open Normalize


(* A [renaming] is a partial substitution, such that all values in it are bound variables.
   Here:
   - [dom] is (the length of) the domain of a renaming
   - [cod] is (the length of) the codomain of a renaming
   - [map] is a parial mapping from variables in [dom] to values in [cod],
   represented as an association list *)
type renaming =
    { dom : level
    ; cod : level
    ; map : (level * value) list }


let empty_renaming =
    { dom = 0
    ; cod = 0
    ; map = [] }


(* Add a new bound variable to a renaming [ren].
   Assume:
       Γ |- ren : Δ
   then:
       Γ, x : A[ren] |- add_boundvar ren : Δ, x : A
   such that:
       x[add_boundvar ren] = x *)
let add_boundvar ren =
    { dom = ren.dom + 1
    ; cod = ren.cod + 1
    ; map = (ren.dom, stuck_local ren.cod) :: ren.map }



(* Convert all bound variables in a context Γ to a list of arguments *)
let env_to_args env =
    (* loop env = (length of env, argument list of bound variables in env) *)
    let rec loop = function
        | Empty ->
            0, []
        | Bound(env', _, _) ->
            let level, args = loop env' in
            level + 1, stuck_local level :: args
        | Defined(env', _, _, _) ->
            let level, args = loop env' in
            level + 1, args
    in
    snd (loop env)


(* Calculate the inverse substitution of a list of arguments.
   The list of arguments [args] should live in a context with length [level].
   That is, assume:
       Γ(level) |- args : Δ
   we should have:
       Δ |- args_to_renaming level args : Γ *)
let args_to_renaming level args =
    (* generate the mapping part of the inverse substitution.
       gen_map args = (length of args, inverse mapping generated from args) *)
    let rec gen_map args =
        match args with
        | [] ->
            0, []
        | Stuck(Lvl lvl, []) :: args' ->
            (* We are now processing the [level]-th argument,
               it should correspond to the [level]-th bound variable
               in the codomain of the inverse substitution *)
            let level, map = gen_map args' in
            if List.mem_assoc lvl map
            then failwith "the same variable occurs twice in arguments of meta"
            else (level + 1, (lvl, stuck_local level) :: map)
        | _ ->
            failwith "arguments of meta not a bound variable"
    in
    let args_len, map = gen_map args in
    { dom = level; cod = args_len; map }


(* Given a context Γ with length [level],
   prune out those variables in Γ that do not satisfy [filter]
   to obtain a context Γ',
   and returns the weaking substitution, i.e.:
       Γ(level) |- weakening_renaming ~filter level : Γ' *)
let rec weakening_renaming ~filter level =
    if level = 0
    then empty_renaming
    else
        let ren = weakening_renaming ~filter (level - 1) in
        if filter level
        then add_boundvar ren
        else
            (* the variable at [level] should be pruned away,
               so [cod] is not increased *)
            { ren with dom = ren.dom + 1 }



let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))



(* [rename m ren v] apply the partial renaming [ren] to value [v],
   checking for occurence of [m] at the same time.
   [v] should live in [ren.dom], and the result should live in [ren.cod], i.e.:

       Γ(ren.cod) |- ren : Δ(ren.dom)
       Δ(ren.dom) |- v : A
      --------------------------------------
       Γ(ren.cod) |- rename m ren v : A[ren]

   Since [rename] must recurse down the structure of [v],
   the result is a core expression, similar to quoting in NBE.

   When no occurs check need to be performed, [m] can be set to [-1]. *)
let rec rename m ren value =
    match force value with
    | Stuck(Lvl lvl, args) -> 
        begin match List.assoc lvl ren.map with
        | value ->
            List.fold_right (fun a f -> Core.App(f, rename m ren a))
                args (quote ren.cod value)
        | exception Not_found -> failwith "variable may escape its scope"
        end

    (* Failed occurs check *)
    | Stuck(Meta m', _) when m' = m ->
        failwith("meta ?" ^ string_of_int m ^ " occurs recursively in its solution")

   (* Renaming a meta differnt from [m].
      This is the so-called "pruning" operation
      and corresponds to the flex-flex case of the rewrite rules.
      Assume that:
          m' : Γₘ -> A
          Γ(ren.dom) |- args : Γₘ *)
    | Stuck(Meta m', args) ->
        (* check if [args] is a list of distinct bound variable.
           [ren'.cod] = length of args = length of Γₘ *)
        let ren' = args_to_renaming ren.dom args in
        (* [args_is_ok lvl] checks if the [lvl]-th argument in [args] is valid,
           i.e. need to be pruned away *)
        let arg_is_ok lvl =
            match List.nth args (ren'.cod - lvl - 1) with
            | Stuck(Lvl lvl, []) -> List.mem_assoc lvl ren.map
            | _                  -> false
        in
        (* Γₘ |- wk_ren : Γₘ',
           where Γₘ' is Γₘ with variables not in the domain of [ren] pruned away *)
        let wk_ren = weakening_renaming ~filter:arg_is_ok ren'.cod in
        if wk_ren.cod = ren'.cod
        (* no variables are pruned away, no need to solve [m'] and allocate a new meta,
           simply rename [args] with [ren] *)
        then List.fold_right (fun a f -> Core.App(f, rename m ren a)) args (Core.Meta m')
        (* some variables are pruned away, should solve [m'] *)
        else
            (* new_meta : Γₘ' -> A', where A'[wk_ren] = A.
               [A'] must not mention variables pruned away from Γₘ,
               otherwise the equation will be ill-typed *)
            let new_meta = MetaContext.fresh_meta () in
            let solution =
                (* Γₘ' |- (new_meta Γₘ') : A' *)
                Stuck (Meta new_meta, List.init wk_ren.cod stuck_local)
                (* Γₘ' |- (new_meta Γₘ')[wk_ren] : A'[wk_ren] = A *)
                |> rename (-1) wk_ren
                (* λΓₘ . (new_meta Γₘ')[wk_ren] : Γₘ -> A *)
                |> make_fun wk_ren.cod
                |> eval []
            in
            MetaContext.solve_meta m' solution;
            (* apply the solution to [args] and rename it with [ren] again *)
            rename m ren (List.fold_right (Fun.flip apply) args solution)
    | Type ->
        Core.Type
    | TyFun(name, a, b) ->
        Core.TyFun(name, rename m ren a, rename m (add_boundvar ren) @@ b @@ stuck_local ren.dom)
    | Fun(name, f) ->
        Core.Fun(name, rename m (add_boundvar ren) @@ f @@ stuck_local ren.dom)



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
        let ren1 = args_to_renaming level args1 in
        let ren2 = args_to_renaming level args2 in
        if ren1.cod <> ren2.cod then
            failwith "unsolvable equation";

        (* check if the [lvl]-th argument in [args1] and [args2] agree *)
        let arg_is_ok lvl =
            let idx = ren1.cod - lvl - 1 in
            match List.nth args1 idx, List.nth args2 idx with
            | Stuck(Lvl lvl1, []), Stuck(Lvl lvl2, []) -> lvl1 = lvl2
            | _                                        -> false
        in
        (* prune away those arguments that don't agree *)
        let wk_ren = weakening_renaming ~filter:arg_is_ok ren1.cod in

        let new_meta = MetaContext.fresh_meta () in
        let solution =
            Stuck(Meta new_meta, List.init wk_ren.cod stuck_local)
            |> rename (-1) wk_ren
            |> make_fun ren1.cod
            |> eval []
        in
        MetaContext.solve_meta m1 solution

    (* flex-rigid or flex-flex with different metas *)
    | Stuck(Meta m, args), v
    | v, Stuck(Meta m, args) ->
        let ren = args_to_renaming level args in
        let solution =
            rename m ren v
            |> make_fun ren.cod
            |> eval []
        in
        MetaContext.solve_meta m solution

    | Stuck(Lvl lvl1, args1), Stuck(Lvl lvl2, args2) when lvl1 = lvl2 ->
        begin try List.iter2 (unify level) args1 args2 with
          Invalid_argument _ -> failwith "unsolvable equation"
        end

    | _ ->
        failwith "unsolvable equation"
