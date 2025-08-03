open Il.Ast
open Il.Print
open Il2al.Il2al_util
open Util.Source
open Def


(* Error *)

let error at msg = Util.Error.error at "IL -> DL" msg


(* Type definitions *)

let extract_typedefs (def: def) : type_def list =
  match def.it with
  | TypD (id, params, insts) -> [(id, params, insts) $ def.at]
  | _ -> []


(* Relations *)

(* extract reduction rules for wasm instructions *)
let extract_rules (def: def) =
  match def.it with
  | RelD (rel_id, _, typ, rules) -> List.map (fun rule -> (rel_id, typ, rule)) rules
  | _ -> []


let il2dl_rule_clause rel_id rule : rule_clause =
  let RuleD (id, _, _, exp, prems) = rule.it in
  match exp.it with
  | TupE [ lhs; rhs ] when List.mem rel_id.it [ "Step"; "Step_read"; "Step_pure" ]
  -> (id, lhs, rhs, prems) $ rule.at
  | TupE [ z1; lhs; z2; rhs ] when rel_id.it = "Eval_expr"
  -> (id, {exp with it = TupE [z1; lhs]}, {exp with it = TupE [z2; rhs]}, prems) $ rule.at
  | _ -> error exp.at ("Wrong exp form of reduction rule: [" ^ rel_id.it ^ "]" ^ Il.Print.string_of_exp exp)

let il2dl_rule_def rule_name rel_id typ rules at : rule_def =
  let rule_clauses = List.map (il2dl_rule_clause rel_id) rules in
  match typ.it with
  | TupT [(_, t1); (_, t2)] -> (rule_name, rel_id, t1, t2, rule_clauses) $ at
  | _ -> error at ("Invalid rule type: " ^ string_of_typ typ)

(* Group reduction rules that have same rule name. *)
let rec group_rules : (id * typ * rule) list -> rule_def list = function
  | [] -> []
  | h::t ->
    let (rel_id, typ, rule) = h in
    let rule_name = name_of_rule rule in
    let t1, t2 =
      List.partition (fun (_, _, rule) -> name_of_rule rule = rule_name) t in
    let rules = rule :: List.map (fun (rel_id', typ', rule') ->
      if rel_id = rel_id' then rule' else
        error rule'.at
        "this reduction rule uses a different relation compared to the previous rules"
    ) t1 in
    let at = rules |> List.map at |> over_region in
    let rule_def = il2dl_rule_def rule_name rel_id typ rules at in

    rule_def :: group_rules t2


(* Helper Definitions *)

let get_partial_func def =
  let is_partial_hint hint = hint.hintid.it = "partial" in
  match def.it with
  | HintD { it = DecH (id, hints); _ } when List.exists is_partial_hint hints ->
    Some (id)
  | _ -> None


let extract_funcs partial_funcs (def: def): func_def option =
  match def.it with
  | DecD (id, params, typ, clauses) when List.length clauses > 0 ->
    let partial = if List.mem id partial_funcs then Partial else Total in
    Some ((id, params, typ, clauses, Some partial) $ def.at)
  | _ -> None



(* Entry *)

let il2dl (il: script) : dl_def list =
  let type_defs =
    il
    |> List.concat_map extract_typedefs
    |> List.map (fun tdef -> TypeDef tdef)
  in

  let rule_defs =
    il
    |> List.concat_map extract_rules
    |> group_rules
    |> List.map (fun rdef -> RuleDef rdef)
  in

  let partial_funcs = List.filter_map get_partial_func il in
  let func_defs =
    il
    |> List.filter_map (extract_funcs partial_funcs)
    |> List.map (fun hdef -> FuncDef hdef)
  in

  type_defs @ rule_defs @ func_defs
