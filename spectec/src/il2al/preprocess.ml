open Il
open Ast
open Util.Source
open Def
open Il2al_util

let typing_functions = ref []

let rec transform_rulepr_prem prem =
  match prem.it with
  | IterPr (prem, iterexp) ->
    prem
    |> transform_rulepr_prem
    |> (fun new_prem -> IterPr (new_prem, iterexp) $ prem.at)
  | IfPr ({ it = CmpE (`EqOp, _, { it = CallE (id, args); note; at }, rhs); _ })
  when List.mem id.it !typing_functions ->
    IfPr (CallE (id, args @ [ExpA rhs $ rhs.at]) $$ at % note) $ prem.at
  | _ -> prem

let transform_rulepr_rule (rule: rule_clause) : rule_clause =
  let (lhs, rhs, prems) = rule in
  (lhs, rhs, List.map transform_rulepr_prem prems)

let transform_rulepr_clause (clause: clause) : clause =
  let DefD (binds, args, exp, prems) = clause.it in
  DefD (binds, args, exp, List.map transform_rulepr_prem prems) $ clause.at

let transform_rulepr_def (def: dl_def) : dl_def =
  match def with
  | RuleDef rdef ->
    let (rel_id, rule_name, rules) = rdef.it in
    RuleDef ((rel_id, rule_name, List.map transform_rulepr_rule rules) $ rdef.at)
  | HelperDef hdef ->
    let (id, clauses, partial) = hdef.it in
    HelperDef ((id, List.map transform_rulepr_clause clauses, partial) $ hdef.at)

let transform_rulepr = List.map transform_rulepr_def

(* Remove or *)
let remove_or_exp e =
  match e.it with (* TODO: recursive *)
  | BinE (`OrOp, _, e1, e2) -> [ e1; e2 ]
  | _ -> [ e ]

let rec remove_or_prem prem =
  match prem.it with
  | IfPr e -> e |> remove_or_exp |> List.map (fun e' -> IfPr e' $ prem.at)
  | IterPr (prem, iterexp) ->
    prem
    |> remove_or_prem
    |> List.map (fun new_prem -> IterPr (new_prem, iterexp) $ prem.at)
  | _ -> [ prem ]

let remove_or_rule rule =
  let (lhs, rhs, prems) = rule in
  let premss = List.map remove_or_prem prems in
  let premss' = Util.Lib.List.combinations premss in

  if List.length premss' = 1 then [ rule ] else

  List.map (fun prems' -> (lhs, rhs, prems')) premss'

let remove_or_clause clause =
  match clause.it with
  | DefD (binds, args, exp, prems) ->
    let premss = List.map remove_or_prem prems in
    let premss' = Util.Lib.List.combinations premss in

    if List.length premss' = 1 then [ clause ] else

    List.map (fun prems' -> DefD (binds, args, exp, prems') $ clause.at) premss'

let remove_or def =
  match def with
  | RuleDef rdef ->
    let (rel_id, rule_name, rules) = rdef.it in
    RuleDef ((rel_id, rule_name, List.concat_map remove_or_rule rules) $ rdef.at)
  | HelperDef hdef ->
    let (id, clauses, partial) = hdef.it in
    HelperDef ((id, List.concat_map remove_or_clause clauses, partial) $ hdef.at)

(* HARDCODE: Remove a reduction rule for the block context, specifically, for THROW_REF *)
let is_block_context_exp e =
  match e.it with
  (* instr* =/= [] *)
  | CmpE (`NeOp, _, e1, e2) ->
    begin match e1.it, e2.it with
    | IterE (var, (List, _)), ListE []
    | ListE [], IterE (var, (List, _)) ->
      begin match var.it with
      | VarE id -> id.it = "instr"
      | _ -> false
      end
    | _ -> false
    end
  | _ -> false
let is_block_context_prem prem =
  match prem.it with
  | IfPr e -> is_block_context_exp e
  | _ -> false
let is_block_context_rule (_, _, prems) =
  match prems with
  | [prem] -> is_block_context_prem prem
  | _ -> false
let remove_block_context def =
  match def with
  | RuleDef rdef ->
    let (rel_id, rule_name, rules) = rdef.it in
    RuleDef ((rel_id, rule_name, Util.Lib.List.filter_not is_block_context_rule rules) $ rdef.at)
  | _ -> def


(* Pre-process a premise *)
let rec preprocess_prem prem =
  match prem.it with
  | IterPr (prem, iterexp) ->
    prem
    |> preprocess_prem
    |> List.map (fun new_prem -> IterPr (new_prem, iterexp) $ prem.at)
  | RulePr (id, mixop, exp) ->
    let lhs_rhs_opt = 
      match mixop, exp.it with
      (* `id`: |- `lhs` : `rhs` *)
      | [[turnstile]; [colon]; []], TupE [lhs; rhs]
      (* `id`: C |- `lhs` : `rhs` *)
      | [[]; [turnstile]; [colon]; []], TupE [_; lhs; rhs]
      when turnstile.it = Turnstile && colon.it = Colon ->
        typing_functions := id.it :: !typing_functions;
        Some (lhs, rhs)
      (* `lhs` ~~ `rhs` *)
      | [[]; [approx]; []], TupE [lhs; rhs] when approx.it = Approx -> Some (lhs, rhs)
      | _ -> None
    in
    (match lhs_rhs_opt with
    | Some (lhs, rhs) -> 
      let function_call =
        CallE (id, [ExpA lhs $ lhs.at]) $$ exp.at % rhs.note
      in
      let new_prem =
        IfPr (CmpE (`EqOp, `BoolT, function_call, rhs) $$ prem.at % (BoolT $ no_region))
      in

      (* Add function definition to AL environment *)
      if not (Env.mem_def !Al.Valid.il_env id) then (
        let param = ExpP ("_" $ no_region, lhs.note) $ lhs.at in
        Al.Valid.il_env := Env.bind_def !Al.Valid.il_env id ([param], rhs.note, [])
      );

      [ new_prem $ prem.at ]
    | None -> [ prem ])
  (* Split -- if e1 /\ e2 *)
  | IfPr ( { it = BinE (`AndOp, _, e1, e2); _ } ) ->
    preprocess_prem (IfPr e1 $ prem.at) @ preprocess_prem (IfPr e2 $ prem.at)
  | _ -> [ prem ]

let preprocess_rule (rule: rule_clause) : rule_clause =
  let (lhs, rhs, prems) = rule in
  (lhs, rhs, List.concat_map preprocess_prem prems)

let preprocess_clause (clause: clause) : clause =
  let DefD (binds, args, exp, prems) = clause.it in
  DefD (binds, args, exp, List.concat_map preprocess_prem prems) $ clause.at

let preprocess_def (def: dl_def) : dl_def =
  let def' =
    def
    |> remove_or
    |> remove_block_context
  in

  match def' with
  | RuleDef rdef ->
    let (rel_id, rule_name, rules) = rdef.it in
    RuleDef ((rel_id, rule_name, List.map preprocess_rule rules) $ rdef.at)
  | HelperDef hdef ->
    let (id, clauses, partial) = hdef.it in
    HelperDef ((id, List.map preprocess_clause clauses, partial) $ hdef.at)

let init_il_env def =
  match def.it with
  | TypD (id, ps, insts) ->
    Al.Valid.il_env := Env.bind_typ !Al.Valid.il_env id (ps, insts)
  | RelD (id, mixop, t, rules) ->
    Al.Valid.il_env := Env.bind_rel !Al.Valid.il_env id (mixop, t, rules)
  | DecD (id, ps, t, clauses) ->
    Al.Valid.il_env := Env.bind_def !Al.Valid.il_env id (ps, t, clauses)
  | GramD (id, ps, t, prods) ->
    Al.Valid.il_env := Env.bind_gram !Al.Valid.il_env id (ps, t, prods)
  | RecD _ -> assert (false);
  | HintD hintdef -> hintdefs := hintdef :: !hintdefs


let flatten_rec def =
  match def.it with
  | RecD defs -> defs
  | _ -> [ def ]

let is_al_target def =
  match def.it with
  | DecD (id, _, _, _) when id.it = "utf8" -> None
  | RelD (id, mixop, t, rules) when List.mem id.it [ "Step"; "Step_read"; "Step_pure" ] ->
    (* HARDCODE: Exclude administrative rules *)
    let filter_rule rule =
      ["pure"; "read"; "trap"; "ctxt"]
      |> List.mem (name_of_rule rule)
      |> not
    in
    Some (RelD (id, mixop, t, List.filter filter_rule rules) $ def.at)
  | RelD (id, _, _, _) when List.mem id.it [ "Eval_expr" ] ->
    Some def
  | RelD _ -> None
  | _ -> Some def

let pp_to_dl (il: script) : dl_def list =
  il
  |> List.concat_map flatten_rec
  |> List.filter_map is_al_target
  |> (fun defs -> let _ = List.map init_il_env defs in defs)
  |> Il2dl.il2dl

let pp_anim_helpers (dl: dl_def list) : dl_def list =
  dl |> Animate.transform

let preprocess (il: script) : dl_def list =
  (* Experiments(kash) *)
  let dl = il 
    |> pp_to_dl
    |> fun dl -> (dl, il)
    (* Experiments(zilinc) *)
    |> Animate_new.animate
  in 
  Il_validator_new.validate dl; 
  dl 

  (*Zilin's code:*)
  (*il 
  |> pp_to_dl
  |> fun dl -> (dl, il)
  (* Each pass is DL -> DL *)

  (* Experiments(zilinc) *)
  |> Animate_new.animate *)
  (* |> Encode.transform *)
  (* |> Animate.transform *)
  (* |> pp_anim_helpers *) 

  

  (* The original pipeline
  |> List.map preprocess_def  (* hacks for throw_ref rule *)
  |> Encode.transform
  |> Animate.transform
  |> transform_rulepr  (* typing premises in rules -> typing functions *)
  |> Unify.unify true true
  *)

