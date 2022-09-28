
open Syntax
open Value
open Normalize


type renaming =
    { dom : level
    ; cod : level
    ; map : (level * value) list }


let empty_renaming =
    { dom = 0
    ; cod = 0
    ; map = [] }

let add_boundvar ren =
    { dom = ren.dom + 1
    ; cod = ren.cod + 1
    ; map = (ren.dom, stuck_local ren.cod) :: ren.map }



let env_to_args env =
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


let args_to_renaming level args =
    let rec gen_map args =
        match args with
        | [] ->
            0, []
        | Stuck(Lvl lvl, []) :: args' ->
            let level, map = gen_map args' in
            if List.mem_assoc lvl map
            then failwith "the same variable occurs twice in arguments of meta"
            else (level + 1, (lvl, stuck_local level) :: map)
        | _ ->
            failwith "arguments of meta not a bound variable"
    in
    let args_len, map = gen_map args in
    { dom = level; cod = args_len; map }


let rec weakening_renaming ~filter level =
    if level = 0
    then empty_renaming
    else
        let ren = weakening_renaming ~filter (level - 1) in
        if filter level
        then add_boundvar ren
        else { ren with dom = ren.dom + 1 }



let rec make_fun n body =
    if n = 0
    then body
    else make_fun (n - 1) (Core.Fun("", body))

let rec rename m ren value =
    match force value with
    | Stuck(Lvl lvl, args) -> 
        begin match List.assoc lvl ren.map with
        | value               ->
            List.fold_right (fun a f -> Core.App(f, rename m ren a))
                args (quote ren.cod value)
        | exception Not_found -> failwith "variable may escape its scope"
        end
    | Stuck(Meta m', _) when m' = m ->
        failwith("meta ?" ^ string_of_int m ^ " occurs recursively in its solution")
    | Stuck(Meta m', args) ->
        let ren' = args_to_renaming ren.dom args in
        let arg_is_ok lvl =
            match List.nth args (ren'.cod - lvl - 1) with
            | Stuck(Lvl lvl, []) -> List.mem_assoc lvl ren.map
            | _                  -> false
        in
        let wk_ren = weakening_renaming ~filter:arg_is_ok ren'.cod in
        if wk_ren.cod = ren'.cod
        then List.fold_right (fun a f -> Core.App(f, rename m ren a)) args (Core.Meta m')
        else
            let new_meta = MetaContext.fresh_meta () in
            let solution =
                Stuck (Meta new_meta, List.init wk_ren.cod stuck_local)
                |> rename (-1) wk_ren
                |> make_fun wk_ren.cod
                |> eval []
            in
            MetaContext.solve_meta m' solution;
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

    | Fun(_, _), _
    | _, Fun(_, _) ->
        let var = stuck_local level in
        unify (level + 1) (apply v1 var) (apply v2 var)

    | Stuck(Meta m1, args1), Stuck(Meta m2, args2) when m1 = m2 ->
        let ren1 = args_to_renaming level args1 in
        let ren2 = args_to_renaming level args2 in
        if ren1.cod <> ren2.cod then
            failwith "unsolvable equation";

        let arg_is_ok lvl =
            let idx = ren1.cod - lvl - 1 in
            match List.nth args1 idx, List.nth args2 idx with
            | Stuck(Lvl lvl1, []), Stuck(Lvl lvl2, []) -> lvl1 = lvl2
            | _                                        -> false
        in
        let wk_ren = weakening_renaming ~filter:arg_is_ok ren1.cod in

        let new_meta = MetaContext.fresh_meta () in
        let solution =
            Stuck(Meta new_meta, List.init wk_ren.cod stuck_local)
            |> rename (-1) wk_ren
            |> make_fun ren1.cod
            |> eval []
        in
        MetaContext.solve_meta m1 solution

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
