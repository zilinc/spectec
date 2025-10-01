open Il
open Il.Ast
open Il.Free
open Il.Print
open Def
open Util
open Error
open Source


(* Error *)

let string_of_error at msg = string_of_region at ^ " DL animation validation error:\n" ^ msg
let error at msg = Error.error at "DL validation" msg
let error_pr at msg prem = error at (msg ^ "\n" ^ "In premise: " ^ string_of_prem prem)

let free_vars_exp e = (Il2al.Free.free_exp false e).varid
let free_vars_args args = (free_list (Il2al.Free.free_arg false) args).varid

let rec valid_prem (known : Set.t) (prem : prem) : Set.t =
  match prem.it with
  | RulePr (_, _, e) -> error_pr prem.at "RulePr found: shouldn't happen." prem
  | IfPr e ->
    let fvs = free_vars_exp e in
    let unknowns = Set.diff fvs known in
    if not (Set.is_empty unknowns) then
      error_pr prem.at ("IfPr uses unknown variables: " ^ string_of_varset unknowns) prem;
    known
  | LetPr (lhs, rhs, vars) ->
    let vars_set = Set.of_list vars in
    let rhs_fvs = free_vars_exp rhs in
    let unknowns = Set.diff rhs_fvs known in
    if not (Set.is_empty unknowns) then
      error_pr rhs.at ("LetPr RHS uses unknown variables: " ^ string_of_varset unknowns) prem;
    (match lhs.it with
      | VarE lhs_var
      | OptE (Some { it = VarE lhs_var; _})
      | SubE ({ it = VarE lhs_var; _ }, _, _)
      -> if List.length vars <> 1 then
           error_pr prem.at ("Only one binder is allowed on this -- where premise but got " ^ string_of_varset vars_set) prem;
         let var = List.hd vars in
         if lhs_var.it <> var then
           error_pr lhs.at ("Variable `" ^ lhs_var.it ^ "` on the LHS of this -- where premise doesn't match binder `" ^ var ^ "`.") prem
      | IterE ({ it = VarE lhs_var; _ }, (Opt, xes))
      -> if List.length vars <> 1 then
           error_pr prem.at ("Only one binder is allowed on this -- where premise but got " ^ string_of_varset vars_set) prem;
         let var = List.hd vars in
         let var_question = match xes with
         | [(x, { it = VarE v_question; _ })] when Il.Eq.eq_id x lhs_var -> v_question
         | _ -> error_pr lhs.at ("Iterator binding list of " ^ string_of_exp lhs ^ " is invalid.") prem
         in
         if var_question.it <> var then
           error_pr lhs.at ("Variable `" ^ var_question.it ^ "` on the LHS of this -- where premise doesn't match binder `" ^ var ^ "`.") prem
      | CaseE (_, { it = TupE es; _ }) ->
        let lhs_vars = List.fold_left Set.union Set.empty (List.map free_vars_exp es) in
        if Set.equal lhs_vars vars_set |> not then
          error_pr lhs.at ("LHS of LetPr " ^ string_of_exp lhs ^ " doesn't match binding list " ^ string_of_varset vars_set) prem
      | _ -> error_pr lhs.at ("Ill-formed LHS of -- where premise: " ^ string_of_exp lhs) prem
    );
    if Set.subset vars_set known then
      error_pr prem.at ("Some -- where premise binders " ^ string_of_varset vars_set ^ " already known.\n" ^
                        "  ▹ Knowns: " ^ string_of_varset known) prem;
    Set.union vars_set known
  | IterPr (plist, (iter, pairs)) ->
    (* In-flow *)
    let in_flow_knowns acc (x, e) =
      match e.it with
      | VarE id -> if (Set.mem id.it known) then
        (if (Set.mem x.it known) then
          error_pr e.at ("Iteration binding {x <- e} ill-formed." ^
            "both x and e cannot be known (" ^ string_of_id x ^ ", " ^ string_of_exp e ^ ")") prem
        else Set.add x.it acc)
        else acc
      | _ -> error_pr e.at ("Iteration binding {x <- e} ill-formed." ^
            "e should be VarE but got " ^ string_of_exp e) prem in
    let new_knowns = List.fold_left in_flow_knowns known pairs in
    (* add optional index to knowns and check if length is known *)
    let new_knowns' =
      (match iter with
        | ListN (l, idopt) ->
          let fv_l = free_vars_exp l in
          let unknown_l = Set.diff fv_l known in
          if Set.is_empty unknown_l then
            match idopt with
            | Some id -> Set.add id.it new_knowns
            | None -> new_knowns
          else
            error_pr l.at ("IterN length `" ^ string_of_exp l ^ "` contains unknowns: " ^ string_of_varset unknown_l) prem
        | _ -> new_knowns
      ) in
    (* Validate body premise *)
    let new_knowns'' = (List.fold_left valid_prem new_knowns' plist) in
    (* Out-flow *)
    let out_flow_knowns acc (x, e) =
      if (Set.mem x.it new_knowns'') then
        Set.union acc (free_vars_exp e)
      else
        error_pr e.at ("Iteration binding {x <- e} ill-formed. " ^
          "Either x or e must be known: (" ^ string_of_id x ^ ", " ^ string_of_exp e ^ ")") prem
    in
    List.fold_left out_flow_knowns known pairs
  | ElsePr -> known

let valid_clause clause : unit =
  Debug.(log_in "animate.valid_clause" line);
  let DefD (bs, args, e, prems) = clause.it in
  let initial_known = free_vars_args args in
  let known_after_premises =
    List.fold_left valid_prem initial_known prems
  in
  let ret_fvs = free_vars_exp e in
  if not (Set.subset ret_fvs known_after_premises) then
    error clause.at ("Return value uses unknown variables: \n" ^ string_of_varset (Set.diff ret_fvs known_after_premises))


let rec infer_def envr (def: dl_def) : unit =
  match def with
  | TypeDef { it = (id, ps, _insts); _ } ->
    let envr' = Valid.local_env envr in
    List.iter (Valid.valid_param envr') ps;
    envr := Env.bind_typ !envr id (ps, [])
  | RuleDef rdef -> error rdef.at "RuleDef found: shouldn't happen."
  | FuncDef { it = (id, ps, t, clauses, _); _ } ->
    let envr' = Valid.local_env envr in
    List.iter (Valid.valid_param envr') ps;
    Valid.valid_typ !envr' t;
    envr := Env.bind_def !envr id (ps, t, clauses)
  | RecDef defs -> List.iter (infer_def envr) defs


let rec valid_def envr (def: dl_def) : unit =
  Debug.(log_in "animate.valid_def" line);
  Debug.(log_in "animate.valid_def" (fun _ -> string_of_dl_def def));
  match def with
  | TypeDef td ->
    let id, ps, insts = td.it in
    let envr' = Valid.local_env envr in
    List.iter (Valid.valid_param envr') ps;
    List.iter (Valid.valid_inst envr ps) insts;
    envr := Env.bind_typ !envr id (ps, insts)
  | RuleDef rd ->
    error rd.at "RuleDef found: shouldn't happen."
  | FuncDef fd ->
    let (id, ps, t, clauses, _) = fd.it in
    let envr' = Valid.local_env envr in
    (* *)
    (*
    List.iter (Valid.valid_param envr') ps;
    Valid.valid_typ !envr' t;
    List.iter (Valid.valid_clause envr ps t) clauses;  (* IL validation *)
    *)
    (* *)
    envr := Env.bind_def !envr id (ps, t, clauses);
    List.iter valid_clause clauses  (* For animation *)
  | RecDef ds ->
    List.iter (infer_def envr) ds;
    List.iter (valid_def envr) ds;
    List.iter (fun d ->
      match List.hd ds, d with
      | TypeDef _, TypeDef _
      | FuncDef _, FuncDef _ -> ()
      | _, _ -> error (dl_loc def) ("Invalid recursion between definitions of different sort.")
    ) ds


(* Entry *)
let valid (dl : dl_def list) : unit =
  let envr = ref Env.empty in
  List.iter (valid_def envr) dl
