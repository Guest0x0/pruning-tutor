
open Syntax

module MetaMap = Map.Make(Int)


let meta_count = ref 0
let metas : Value.meta_info MetaMap.t ref = ref (MetaMap.empty)


let reset () =
    meta_count := 0;
    metas := MetaMap.empty



let fresh_meta typ =
    let m = !meta_count in
    incr meta_count;
    metas := MetaMap.add m (Value.Free typ) !metas;
    m

let find_meta m = MetaMap.find m !metas

let solve_meta m v =
    let metas' = !metas |> MetaMap.update m @@ function
        | Some(Value.Solved _) -> failwith("meta ?" ^ string_of_int m ^ " already solved")
        | Some Value.Free _    -> Some(Value.Solved v)
        | None                 -> failwith("unbound meta ?" ^ string_of_int m)
    in
    metas := metas'
