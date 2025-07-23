open Il.Ast
open Il2al
open Util.Source

exception InvalidDL of string

module StringSet = Set.Make(String);;

(* Helper: collect free variables from expressions and args *)
let rec free_vars_exp (e : exp) : StringSet.t =
  match e.it with
  | VarE id -> StringSet.singleton id.it
  | BoolE _ | NumE _ | TextE _ |  OptE None -> StringSet.empty
  | UnE (_, _, e1) | TheE e1 | OptE (Some e1) | LiftE e1 | LenE e1 
  | ProjE (e1, _) | DotE (e1, _) | CaseE (_, e1) | UncaseE (e1, _) 
  | CvtE (e1, _, _) | SubE (e1, _, _) -> free_vars_exp e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2)
  | CatE (e1, e2) | CompE (e1, e2) | MemE (e1, e2)
  | UpdE (e1, _, e2) | ExtE (e1, _, e2) | IdxE (e1, e2) -> 
    StringSet.union (free_vars_exp e1) (free_vars_exp e2)
  | TupE es | ListE es ->
    List.fold_left (fun acc e -> StringSet.union acc (free_vars_exp e)) StringSet.empty es
  | CallE (_, args) -> free_vars_args args
  | IterE (e1, (iter, xes)) ->
    let bound_ids = List.map fst xes |> List.map (fun id -> id.it) |> StringSet.of_list in
    let bound_idx = match iter with 
      | ListN (_, Some id) -> StringSet.singleton id.it
      | _ -> StringSet.empty
    in
    let bindings = List.map snd xes |> List.map free_vars_exp |> List.fold_left StringSet.union StringSet.empty in
    let body_fvs = free_vars_exp e1 in
    let itervar = match iter with
      | ListN (e2, _) -> free_vars_exp e2
      | _ -> StringSet.empty 
    in 
    let body_fvs' = StringSet.diff body_fvs bound_ids in
    StringSet.union (StringSet.union bindings (StringSet.diff body_fvs' bound_idx)) itervar
  | SliceE (e1, e2, e3) ->
    List.fold_left (fun acc e -> StringSet.union acc (free_vars_exp e)) StringSet.empty [e1; e2; e3]
  | StrE efs ->
    List.fold_left (fun acc (_, e) -> StringSet.union acc (free_vars_exp e)) StringSet.empty efs

and free_vars_args (args : arg list) : StringSet.t =
  List.fold_left (fun acc a -> match a.it with
    | ExpA e -> StringSet.union acc (free_vars_exp e)
    | _ -> acc (* TODO *)
  ) StringSet.empty args

(* Validate a single premise *)
let rec validate_prem (known : StringSet.t) (prem : prem) : StringSet.t =
  match prem.it with
  (* idk about RulePr *)
  | IfPr e | RulePr (_, _, e) ->
    let fvs = free_vars_exp e in
    if not (StringSet.subset fvs known) then
      raise (InvalidDL ("Check premise uses unknown variables: \n" ^ Il.Print.string_of_prem prem));
    known
  | LetPr (lhs, rhs, vars) ->
    let rhs_fvs = free_vars_exp rhs in
    if not (StringSet.subset rhs_fvs known) then
      raise (InvalidDL ("Let binding RHS uses unknown variables at premise: \n" ^ Il.Print.string_of_prem prem));
    let lhs_fvs = free_vars_exp lhs in
    List.iter (fun v ->
      if not (StringSet.mem v lhs_fvs) then
        raise (InvalidDL (("Let binding output " ^ v ^ " not in LHS at premise: \n" ^ Il.Print.string_of_prem prem)));
      if (StringSet.mem v known) then
        raise (InvalidDL ("Let binding output " ^ v ^ " already known at premise: \n" ^ Il.Print.string_of_prem prem));
    ) vars;
    let new_known = StringSet.diff lhs_fvs known in
    StringSet.iter (fun v ->
      if not (List.mem v vars) then
        raise (InvalidDL ("Let binding output " ^ v ^ " not added to known" ^ Il.Print.string_of_prem prem)))
      new_known;
    StringSet.union known lhs_fvs
  | IterPr (p, (iter, pairs)) ->
    (* Validate all RHS expressions in the binding pairs *)
    List.iter (fun (_, e) ->
      let fvs = free_vars_exp e in
      if not (StringSet.subset fvs known) then
        raise (InvalidDL (
          "Iteration binding uses unknown variables: " ^
          String.concat ", " (StringSet.elements (StringSet.diff fvs known)) ^
          "\nIn: " ^ Il.Print.string_of_prem prem
        ))
    ) pairs;
    (* Add bound variables and index variable to known set *)
    let bound_ids =
      List.map fst pairs |> List.map (fun id -> id.it) |> StringSet.of_list
    in
    let bound_idx =
      match iter with
      | ListN (_, Some id) -> StringSet.singleton id.it
      | _ -> StringSet.empty
    in
    let known' = StringSet.union known (StringSet.union bound_ids bound_idx) in
    (* Validate iter expression if it’s ListN (exp, _) *)
    (match iter with
     | ListN (e, _) ->
        let fvs = free_vars_exp e in
        if not (StringSet.subset fvs known) then
          raise (InvalidDL (
            "Iteration expression uses unknown variables: " ^
            String.concat ", " (StringSet.elements (StringSet.diff fvs known)) ^
            "\nIn: " ^ Il.Print.string_of_prem prem
          ))
     | _ -> ());
    (* Validate body premise *)
    validate_prem known' p
  | ElsePr -> known

(* Validate a single rule clause *)
let validate_clause args e prems : unit =
  let initial_known = free_vars_args args in 
  let known_after_premises =
    List.fold_left validate_prem initial_known prems
  in
  let ret_fvs = free_vars_exp e in
  if not (StringSet.subset ret_fvs known_after_premises) then
    raise (InvalidDL "Return value uses unknown variables")

(* Validate a full func_def *)
let validate_func_def (fd : Def.func_def) oc : unit =
  let (fdid, clauses) = fd.it in
  List.iter (fun clause ->
    match clause.it with 
      | DefD (_, args, e, prems) -> 
        try 
          validate_clause args e prems 
        with 
          InvalidDL msg -> 
            let msg = msg ^ "\n of clause: \n" ^ (Il.Print.string_of_clause fdid clause) ^ "\n\n" in
            output_string oc msg
  ) clauses

let validate (dl : Def.dl_def list) : unit =
  let open Def in 
  let oc = open_out "dl-err.log" in
  List.iter (fun def -> 
    match def with
      | RuleDef _ -> () (* TODO *)
      | HelperDef _ -> () (* TODO *)
      | FuncDef fd -> validate_func_def fd oc
  ) dl;
  close_out oc