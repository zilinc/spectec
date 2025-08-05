open Il.Ast
open Il2al.Il2al_util
open Def
open Util
open Source


(* FIXME(zilinc): we may want to do differently than the AL route. *)
let rec is_anim_target def =
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
  | RelD _ -> None
  | RecD defs -> Some (RecD (List.filter_map is_anim_target defs) $ def.at)
  | _ -> Some def


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
  | RelD (id, mixop, typ, rules) ->
    RelD (id, mixop, typ, List.concat_map remove_or_rule rules) $ def.at
  | DecD (id, params, typ, clauses) ->
    DecD (id, params, typ, List.concat_map remove_or_clause clauses) $ def.at
  | RecD defs -> RecD (List.map remove_or defs) $ def.at
  | _ -> def


(* Entry *)
let animate il print_dl =
  let dl = il
           |> List.filter_map is_anim_target
           |> List.map remove_or
           |> Il2dl.il2dl
           |> fun dl -> (dl, il)
           |> Animate.animate 
  in
  (* Il2dl.list_all_dl_defs dl; *)
  Valid.valid dl;
  begin if print_dl then
    print_endline (List.map string_of_dl_def dl |> String.concat "\n")
  else
    print_endline ("Animation validation passed.")
  end;
  dl