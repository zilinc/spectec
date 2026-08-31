open Il.Ast
open Il2al.Il2al_util
open Def
open Util
open Source
open Middlend
module H = State_v.Hints


let build_animation_hints il : unit =
  let hints = List.filter_map (fun def ->
    (match def.it with
    | HintD hdef -> Some hdef
    | _  -> None
    )
  ) il in
  List.iter (fun hdef ->
    match hdef.it with
    | DecH (fid, hints) ->
      List.iter (fun hint ->
        (match hint.hintid.it with
        | "animate"
        | "animate_manual" -> print_endline ("Warning: hint(animate) and hint(animate_manual) on function " ^ fid.it ^ " are not yet implemented."); ()
        | "animate_inverse" -> H.add_anim_inv fid.it (H.parse_opt_fid fid.it hint.hintexp)
        | "no_animate"      -> H.add_no_anim_func fid.it
        | _                 -> ()
        )
      ) hints
    | RelH (rid, hints) ->
      List.iter (fun hint ->
        (match hint.hintid.it with
        | "animate"         -> H.add_anim_rel rid.it (H.parse_mode hint.hintexp)
        | "animate_manual"  -> H.add_anim_manual rid.it (H.parse_fid_mode hint.hintexp)
        | "animate_inverse" -> H.add_anim_inv rid.it (H.parse_opt_fid rid.it hint.hintexp)
        | "no_animate"      -> print_endline ("Warning: hint(no_animate) on relation " ^ rid.it ^ " is not used."); ()
        | _                 -> ()
        )
      ) hints
    | RuleH (rel_id, rule_id, hints) ->
      List.iter (fun hint ->
        (match hint.hintid.it with
        | "no_animate" -> H.add_no_anim_rule rel_id.it rule_id.it 
        | _ -> ()
        )
      ) hints
    | TypH _ | GramH _  -> ()
  ) hints

let rec is_anim_target il_def =
  match il_def.it with
  | DecD (id, ps, t, _) when H.is_no_anim_func id.it -> Some (DecD (id, ps, t, []) $ il_def.at)
  | RelD (id, quants, mixop, t, rules) when H.is_anim_rel id.it ->
    let rules' = List.fold_left (fun rs r ->
      match r.it with
      | RuleD (rule_id, _, _, _, _) when H.is_no_anim_rule id.it rule_id.it -> rs
      | _ -> r::rs
    ) [] rules |> List.rev in
    Some (RelD (id, quants, mixop, t, rules') $ il_def.at)
  | RelD _ -> None
  | RecD defs -> Some (RecD (List.filter_map is_anim_target defs) $ il_def.at)
  | _ -> Some il_def


(* Remove or (Mostly copied as-is from Il2al.Preprocess). *)

let rec remove_or_exp e : exp list =
  match e.it with (* TODO: recursive *)
  | BinE (`OrOp, _, e1, e2) -> remove_or_exp e1 @ remove_or_exp e2
  | _ -> [ e ]

let rec remove_or_prem prem : prem list =
  match prem.it with
  | IfPr e -> e |> remove_or_exp |> List.map (fun e' -> IfPr e' $ prem.at)
  | IterPr (prem, iterexp) ->
    prem
    |> remove_or_prem
    |> List.map (fun new_prem -> IterPr (new_prem, iterexp) $ prem.at)
  | _ -> [ prem ]

let remove_or_rule rule : rule list =
  match rule.it with
  | RuleD (id, binds, mixop, args, prems) ->
    let premss = List.map remove_or_prem prems in
    let premss' = Lib.List.combinations premss in
    if List.length premss' = 1 then
      [ rule ]
    else
      (* Don't change the name of the rule. *)
      List.map (fun prems' -> RuleD (id, binds, mixop, args, prems') $ rule.at) premss'

let remove_or_clause clause =
  match clause.it with
  | DefD (binds, args, exp, prems) ->
    let premss = List.map remove_or_prem prems in
    let premss' = Lib.List.combinations premss in
    if List.length premss' = 1 then
      [ clause ]
    else
      List.map (fun prems' -> DefD (binds, args, exp, prems') $ clause.at) premss'

let rec remove_or def =
  match def.it with
  | RelD (id, quants, mixop, typ, rules) ->
    RelD (id, quants, mixop, typ, List.concat_map remove_or_rule rules) $ def.at
  | DecD (id, params, typ, clauses) ->
    DecD (id, params, typ, List.concat_map remove_or_clause clauses) $ def.at
  | RecD defs -> RecD (List.map remove_or defs) $ def.at
  | _ -> def


(* Entry *)

let pp il print_dl =
  H.init_animation_hints ();
  build_animation_hints il;
  (* temporary fix *)
  H.add_anim_inv "proj_num__0" "inv_proj_num__0";
  let pp_dl = il |> List.filter_map is_anim_target
                 |> List.map remove_or
                 |> Il2dl.il2dl
  in
  if print_dl then
    print_endline (List.map string_of_dl_def pp_dl |> String.concat "\n");

  let env = Il.Env.env_of_script il in
  env, pp_dl

let run il print_dl inline =
  let env, pp_dl = pp il false in
  let env, dl = Animate.animate env pp_dl in
  let dl' = if inline then List.map Inline.inline_dl_def dl else dl in
  (* FIXME(zilinc): During the following step we lose the distinction between a relation
     name and a rule name in function definitions, because in IL there's only a single
     function Id position to store the info, while in DL we have the optional subid field.
  *)
  let il' = Dl2il.dl2il dl' in
  let il'' = Il.Dep.recursify_defs il' in
  let dl'' = Il2dl.il2dl il'' in
  if print_dl then
    print_endline (List.map string_of_dl_def dl'' |> String.concat "\n");
  (env, dl'')
