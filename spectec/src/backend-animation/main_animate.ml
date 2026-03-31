open Il.Ast
open Il2al.Il2al_util
open Def
open Util
open Source
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
        | "animate"         -> print_endline ("Warning: hint(animate) on function " ^ fid.it ^ " is not yet implemented."); ()
        | "animate_builtin" -> H.add_anim_builtin fid.it (H.parse_mode hint.hintexp)
        | "animate_inverse" -> H.add_anim_inv fid.it
        | "no_animate"      -> H.add_no_anim_func fid.it
        | _                 -> ()
        )
      ) hints
    | RelH (rid, hints) ->
      List.iter (fun hint ->
        (match hint.hintid.it with
        | "animate"         -> H.add_anim_rel rid.it (H.parse_mode hint.hintexp)
        | "animate_builtin" -> H.add_anim_builtin rid.it (H.parse_mode hint.hintexp)
        | "animate_as"      -> H.add_anim_as_func rid.it (H.parse_fid_mode hint.hintexp)
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

let remove_or_exp e : exp list =
  match e.it with (* TODO: recursive *)
  | BinE (`OrOp, _, e1, e2) -> [ e1; e2 ]
  | _ -> [ e ]

let rec remove_or_prem prem : prem list =
  match prem.it with
  | IfPr e -> e |> remove_or_exp |> List.map (fun e' -> IfPr e' $ prem.at)
  | IterPr ([prem], iterexp) ->
    prem
    |> remove_or_prem
    |> List.map (fun new_prem -> IterPr ([new_prem], iterexp) $ prem.at)
  | IterPr (_, _) -> assert false
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
let run il print_dl inline =
  H.init_animation_hints ();
  build_animation_hints il;
  (* H.add_a_inv "proj_num__0"; *)
  let (env, dl) = il
                  |> List.filter_map is_anim_target
                  |> List.map remove_or
                  |> Il2dl.il2dl
                  |> fun dl -> (dl, il)
                  |> Animate.animate
                  |> fun (il_env, dl) -> (il_env, if inline then List.map Inline.inline_dl_def dl else dl)
  in
  (* Il2dl.list_all_dl_defs dl; *)
  if print_dl then
    print_endline (List.map string_of_dl_def dl |> String.concat "\n");
  (env, dl)
