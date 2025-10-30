open Il.Ast
open Il.Print
open Il2al.Il2al_util
open Util.Source
open Def
open Il_util

(* Debug *)

let rec list_all_il_defs' lv (il: script) : unit =
  let indent n = String.make (2*n) ' ' in
  List.iter (fun def -> match def.it with
    | RecD defs -> print_endline "{"; list_all_il_defs' (lv+1) defs; print_endline "}"
    | TypD (id, _, _)    -> print_endline (indent lv ^ "typ | " ^ string_of_id id)
    | DecD (id, _, _, _) -> print_endline (indent lv ^ "dec | " ^ string_of_id id)
    | RelD (id, _, _, _) -> print_endline (indent lv ^ "rel | " ^ string_of_id id)
    | _ -> ()
  ) il
let list_all_il_defs (il: script) : unit = list_all_il_defs' 0 il

let rec list_all_dl_defs' lv dl : unit =
  let indent n = String.make (2*n) ' ' in
  List.iter (function
    | RecDef  defs -> print_endline "{"; list_all_dl_defs' (lv+1) defs; print_endline "}"
    | TypeDef tdef ->
      let id, _, _ = tdef.it in
      print_endline (indent lv ^ "type | " ^ string_of_id id)
    | FuncDef fdef ->
      let id, _, _, _, _ = fdef.it in
      print_endline (indent lv ^ "func | " ^ string_of_id id)
    | RuleDef rdef ->
      let _, id, _, _, _ = rdef.it in
      print_endline (indent lv ^ "rule | " ^ string_of_id id)
  ) dl
let list_all_dl_defs (dl: dl_def list) : unit = list_all_dl_defs' 0 dl


(* Error *)

let error at msg = Util.Error.error at "IL -> DL" msg


(* Relations *)

let il2dl_rule_clause rel_id rule : rule_clause =
  let RuleD (id, binds, _, exp, prems) = rule.it in
  match exp.it with
  | TupE [ lhs; rhs ] when List.mem rel_id.it Common.step_relids
  -> (id, binds, lhs, rhs, prems) $ rule.at
  | TupE [ z1; lhs; z2; rhs ] when rel_id.it = "Eval_expr"
  -> let at1 = over_region [z1.at; lhs.at] in
     let at2 = over_region [z2.at; rhs.at] in
     let lhs' = mk_case' ~at:at1 "config" [[];[";"];[]] [z1; lhs] in
     let rhs' = mk_case' ~at:at1 "config" [[];[";"];[]] [z2; rhs] in
     (id, binds, lhs', rhs', prems) $ rule.at
  | _ -> error exp.at ("Wrong exp form of reduction rule: [" ^ rel_id.it ^ "]" ^ Il.Print.string_of_exp exp)

let il2dl_rule_def rule_name rel_id typ rules at : rule_def =
  let rule_clauses = List.map (il2dl_rule_clause rel_id) rules in
  let t1, t2 =
    (match typ.it with
    | TupT [ (_, t1); (_, t2) ] when List.mem rel_id.it Common.step_relids ->
      t1, t2
    | TupT [ et11; et12; et21; et22 ] when rel_id.it = "Eval_expr" ->
      let at1 = over_region [(fst et11).at; (snd et12).at] in
      let at2 = over_region [(fst et21).at; (snd et22).at] in
      t_var ~at:at1 "config", t_var ~at:at2 "config"
    | _ -> error at ("Invalid rule type: " ^ string_of_typ typ)
    )
  in
  (rule_name, rel_id, t1, t2, rule_clauses) $ at


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

let get_partial_func def : id option =
  let is_partial_hint hint = hint.hintid.it = "partial" in
  match def.it with
  | HintD { it = DecH (id, hints); _ } when List.exists is_partial_hint hints ->
    Some (id)
  | _ -> None


(* Entry *)


let rec il2dl (il: script) : dl_def list =
  let partial_funcs = List.filter_map get_partial_func il in
  List.concat_map (fun def ->
    match def.it with
    | TypD (id, params, insts) -> [TypeDef ((id, params, insts) $ def.at)]
    | DecD (id, params, typ, clauses) ->
      let partial = if List.mem id partial_funcs then Partial else Total in
      [FuncDef ((id, params, typ, clauses, Some partial) $ def.at)]
    | RelD (rel_id, _, typ, rules) ->
      let rules = List.map (fun rule -> (rel_id, typ, rule)) rules in
      let rule_def = group_rules rules in
      List.map (fun r -> RuleDef r) rule_def
    | RecD defs ->
      let defs' = il2dl defs in
      if List.is_empty defs' then [] else [RecDef defs']
    | _ -> []
  ) il
