open Util
open Source
open Il.Ast

let error at msg = Error.error at "handle-explicit-ignores" msg

(* Every id carrying hint(nobackendrender), gathered from the script's HintD
   entries. A HintD is its own top-level script entry, sibling to (not
   nested inside) the def it annotates -- see il/ast.ml's def'/hintdef'. *)
let gather_ignored_ids (il : script) : string list =
  List.filter_map (fun (d : def) -> match d.it with
    | HintD { it = TypH (id, hints); _ }
    | HintD { it = RelH (id, hints); _ }
    | HintD { it = DecH (id, hints); _ }
    | HintD { it = GramH (id, hints); _ }
      when List.exists (fun h -> h.hintid.it = Il.Hints.hint_ignore_in_backend) hints ->
      Some id.it
    | _ -> None
  ) il

(* Every id referenced in `il`, with the location of that reference -- as a
   def-call, a higher-order argument, a relation premise, a type use, or a
   grammar use. Callers must pass the script with any ignored defs already
   filtered out: Iter's visit_defid/visit_relid/visit_typid/visit_gramid
   fire on a def's own *declaring* occurrence too (its own name in its own
   header), not just on uses elsewhere, so walking an ignored def's own body
   would wrongly report it as referencing itself. CallE and DefA both
   already route through visit_defid (see iter.ml: `CallE (x,_) -> defid x`,
   `DefA x -> defid x`), so overriding it alone catches direct calls and
   higher-order-argument passing uniformly; visit_relid/visit_typid/
   visit_gramid cover RulePr/type-use/grammar-use the same way. *)
let gather_referenced_ids (il : script) : (string * region) list =
  let collected = ref [] in
  let module Visitor = Il.Iter.Make(struct
    include Il.Iter.Skip
    let visit_defid (id : id) = collected := (id.it, id.at) :: !collected
    let visit_relid (id : id) = collected := (id.it, id.at) :: !collected
    let visit_typid (id : id) = collected := (id.it, id.at) :: !collected
    let visit_gramid (id : id) = collected := (id.it, id.at) :: !collected
  end) in
  List.iter Visitor.def il;
  !collected

let rec filter_def (ignored : string list) (d : def) : def option =
  match d.it with
  | TypD (id, _, _) | RelD (id, _, _, _, _) | DecD (id, _, _, _) | GramD (id, _, _, _) ->
    if List.mem id.it ignored then None else Some d
  | HintD { it = TypH (id, _); _ }
  | HintD { it = RelH (id, _); _ }
  | HintD { it = DecH (id, _); _ }
  | HintD { it = GramH (id, _); _ } ->
    if List.mem id.it ignored then None else Some d
  | HintD { it = RuleH (rel_id, _, _); _ } ->
    if List.mem rel_id.it ignored then None else Some d
  | RecD defs ->
    (match List.filter_map (filter_def ignored) defs with
     | [] -> None
     | defs' -> Some { d with it = RecD defs' })

let transform (il : script) : script =
  match gather_ignored_ids il with
  | [] -> il
  | ignored ->
    (* Filter first, then scan only the survivors for references -- see the
       comment on gather_referenced_ids for why the ignored defs' own bodies
       must not be part of the reference scan. *)
    let kept = List.filter_map (filter_def ignored) il in
    let referenced = gather_referenced_ids kept in
    List.iter (fun name ->
      match List.find_opt (fun (n, _) -> n = name) referenced with
      | Some (_, at) ->
        error at
          (Printf.sprintf
             "`%s` is tagged hint(nobackendrender) but is still referenced here -- \
              remove the reference, or remove the hint"
             name)
      | None -> ()
    ) ignored;
    kept
