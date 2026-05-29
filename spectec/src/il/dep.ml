open Ast
open Util
open Source

module Map = Map.Make(String)

let error at msg = Error.error at "dependency" msg

let origins i (map : int Map.t ref) (set : Free.Set.t) =
  Free.Set.iter (fun id -> map := Map.add id i !map) set

let deps (map : int Map.t) (set : Free.Set.t) : int array =
  Array.map (fun id ->
    try Map.find id map with Not_found -> failwith ("recursify dep " ^ id)
  ) (Array.of_seq (Free.Set.to_seq set))


let check_recursion (ds' : def list) =
  List.iter (fun d' ->
    match d'.it, (List.hd ds').it with
    | HintD _, _ | _, HintD _
    | TypD _, TypD _
    | RelD _, RelD _
    | DecD _, DecD _
    | GramD _, GramD _ -> ()
    | _, _ ->
      error (List.hd ds').at (" " ^ string_of_region d'.at ^
        ": invalid recursion between definitions of different sort:\n" ^
        "  ▹ " ^ Print.string_of_def_id d' ^ "\n" ^
        "  ▹ " ^ Print.string_of_def_id (List.hd ds') ^ "\n")
  ) ds'
  (* TODO(4, rossberg): check that notations are non-recursive and defs are inductive? *)

let flatten ds : script =
  List.concat_map (fun d -> match d.it with
  | RecD ds -> ds
  | _ -> [d]
  ) ds

let recursify_defs (ds : script) : script =
  let open Free in
  let da = Array.of_list (flatten ds) in
  let map_typid = ref Map.empty in
  let map_relid = ref Map.empty in
  let map_defid = ref Map.empty in
  let map_gramid = ref Map.empty in
  let frees = Array.map Free.free_def da in
  let bounds = Array.map Free.bound_def da in
  Array.iteri (fun i bound ->
    origins i map_typid bound.typid;
    origins i map_relid bound.relid;
    origins i map_defid bound.defid;
    origins i map_gramid bound.gramid;
  ) bounds;
  let graph =
    Array.map (fun free ->
      Array.concat
        [ deps !map_typid free.typid;
          deps !map_relid free.relid;
          deps !map_defid free.defid;
          deps !map_gramid free.gramid;
        ];
    ) frees
  in
  let sccs = Scc.sccs graph in
  List.map (fun set ->
    let ds'' = List.map (fun i -> da.(i)) (Scc.Set.elements set) in
    check_recursion ds'';
    let i = Scc.Set.choose set in
    match ds'' with
    | [d'] when Free.disjoint bounds.(i) frees.(i) -> d'
    | ds'' -> RecD ds'' $ Source.over_region (List.map at ds'')
  ) sccs
