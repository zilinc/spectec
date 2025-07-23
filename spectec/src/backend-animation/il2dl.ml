open Il.Ast
open Il2al.Def
open Il2al.Il2al_util
open Util.Source


(* Error *)

let error at msg = Util.Error.error at "IL -> DL" msg


(* Relations *)

(* extract reduction rules for wasm instructions *)
let extract_rules (def: def) =
  match def.it with
  | RelD (id, _, _, rules) -> List.map (fun rule -> id, rule) rules
  | _ -> []


let rule_to_tup rel_id rule =
  let RuleD (id, _, _, exp, prems) = rule.it in
  match exp.it with
  | TupE [ lhs; rhs ] when List.mem rel_id.it [ "Step"; "Step_read"; "Step_pure" ]
  -> (lhs, rhs, prems)
  | TupE [ z1; lhs; z2; rhs ] when rel_id.it = "Eval_expr"
  -> ({exp with it = TupE [z1; lhs]}, {exp with it = TupE [z2; rhs]}, prems)
  | _ -> error exp.at ("form of reduction rule: [" ^ rel_id.it ^ "]" ^ Il.Print.string_of_exp exp)



(* group reduction rules that have same name *)
let rec group_rules : (id * rule) list -> rule_def list = function
  | [] -> []
  | h :: t ->
    let (rel_id, rule) = h in
    let name = name_of_rule rule in
    let t1, t2 =
      List.partition (fun (_, rule) -> name_of_rule rule = name) t in
    let rules = rule :: List.map (fun (rel_id', rule') ->
      if rel_id = rel_id' then rule' else
        error rule'.at
        "this reduction rule uses a different relation compared to the previous rules"
    ) t1 in
    let tups = List.map (rule_to_tup rel_id) rules in
    let at = rules |> List.map at |> over_region in

    ((name, rel_id, tups) $ at) :: group_rules t2


(* Helper Definitions *)

let get_partial_func def =
  let is_partial_hint hint = hint.hintid.it = "partial" in
  match def.it with
  | HintD { it = DecH (id, hints); _ } when List.exists is_partial_hint hints ->
    Some (id)
  | _ -> None


let extract_helpers partial_funcs (def: def) =
  match def.it with
  | DecD (id, _, _, clauses) when List.length clauses > 0 ->
    let partial = if List.mem id partial_funcs then Partial else Total in
    Some ((id, clauses, partial) $ def.at)
  | _ -> None



(* Entry *)

let il2dl (il: script) : dl_def list =
  let rule_defs =
    il
    |> List.concat_map extract_rules
    |> group_rules
    |> List.map (fun rdef -> RuleDef rdef)
  in

  let partial_funcs = List.filter_map get_partial_func il in
  let helper_defs =
    il
    |> List.filter_map (extract_helpers partial_funcs)
    |> List.map (fun hdef -> HelperDef hdef)
  in

  rule_defs @ helper_defs
