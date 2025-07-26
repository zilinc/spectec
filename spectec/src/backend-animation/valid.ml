open Il.Ast
open Il.Free
open Il2al
open Util
open Error
open Source

exception InvalidDL of string


(* Helper: collect free variables from expressions and args *)
let rec free_vars_exp (e : exp) : Set.t =
  match e.it with
  | VarE id -> Set.singleton id.it
  | BoolE _ | NumE _ | TextE _ |  OptE None -> Set.empty
  | UnE (_, _, e1) | TheE e1 | OptE (Some e1) | LiftE e1 | LenE e1 
  | ProjE (e1, _) | DotE (e1, _) | CaseE (_, e1) | UncaseE (e1, _) 
  | CvtE (e1, _, _) | SubE (e1, _, _) -> free_vars_exp e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2)
  | CatE (e1, e2) | CompE (e1, e2) | MemE (e1, e2)
  | UpdE (e1, _, e2) | ExtE (e1, _, e2) | IdxE (e1, e2) -> 
    Set.union (free_vars_exp e1) (free_vars_exp e2)
  | TupE es | ListE es ->
    List.fold_left (fun acc e -> Set.union acc (free_vars_exp e)) Set.empty es
  | CallE (_, args) -> free_vars_args args
  | IterE (e1, (iter, xes)) ->
    let bound_ids = List.map fst xes |> List.map (fun id -> id.it) |> Set.of_list in
    let bound_idx = match iter with 
      | ListN (_, Some id) -> Set.singleton id.it
      | _ -> Set.empty
    in
    let bindings = List.map snd xes |> List.map free_vars_exp |> List.fold_left Set.union Set.empty in
    let body_fvs = free_vars_exp e1 in
    let itervar = match iter with
      | ListN (e2, _) -> free_vars_exp e2
      | _ -> Set.empty 
    in 
    let body_fvs' = Set.diff body_fvs bound_ids in
    Set.union (Set.union bindings (Set.diff body_fvs' bound_idx)) itervar
  | SliceE (e1, e2, e3) ->
    List.fold_left (fun acc e -> Set.union acc (free_vars_exp e)) Set.empty [e1; e2; e3]
  | StrE efs ->
    List.fold_left (fun acc (_, e) -> Set.union acc (free_vars_exp e)) Set.empty efs

and free_vars_args (args : arg list) : Set.t =
  List.fold_left (fun acc a -> match a.it with
    | ExpA e -> Set.union acc (free_vars_exp e)
    | _ -> acc (* TODO *)
  ) Set.empty args

(* Validate a single premise *)
let rec validate_prem (known : Set.t) (prem : prem) : Set.t =
  match prem.it with
  (* idk about RulePr *)
  | IfPr e | RulePr (_, _, e) ->
    let fvs = free_vars_exp e in
    let unknowns = Set.diff fvs known in
    if not (Set.is_empty unknowns) then
      raise (InvalidDL ("Check premise uses unknown variables:\n" ^ Il.Print.string_of_prem prem ^ "\n" ^
                        "  ▹ unknowns: " ^ string_of_varset unknowns));
    known
  | LetPr (lhs, rhs, vars) ->
    let rhs_fvs = free_vars_exp rhs in
    let unknowns = Set.diff rhs_fvs known in
    if not (Set.is_empty unknowns) then
      raise (InvalidDL ("Let binding RHS uses unknown variables at premise:\n" ^ Il.Print.string_of_prem prem ^ "\n" ^
                        "  ▹ unknowns: " ^ string_of_varset unknowns));
    let lhs_fvs = free_vars_exp lhs in
    List.iter (fun v ->
      if not (Set.mem v lhs_fvs) then
        raise (InvalidDL (("Let binding output " ^ v ^ " not in LHS at premise:\n" ^ Il.Print.string_of_prem prem)));
      if (Set.mem v known) then
        raise (InvalidDL ("Let binding output " ^ v ^ " already known at premise:\n" ^ Il.Print.string_of_prem prem));
    ) vars;
    let new_known = Set.diff lhs_fvs known in
    Set.iter (fun v ->
      if not (List.mem v vars) then
        raise (InvalidDL ("Let binding output " ^ v ^ " not added to known" ^ Il.Print.string_of_prem prem)))
      new_known;
    Set.union known lhs_fvs
  | IterPr ([p], (iter, pairs)) ->
    (* Validate all RHS expressions in the binding pairs *)
    List.iter (fun (_, e) ->
      let fvs = free_vars_exp e in
      if not (Set.subset fvs known) then
        raise (InvalidDL (
          "Iteration binding uses unknown variables: " ^
          string_of_varset (Set.diff fvs known) ^
          "\nIn: " ^ Il.Print.string_of_prem prem
        ))
    ) pairs;
    (* Add bound variables and index variable to known set *)
    let bound_ids =
      List.map fst pairs |> List.map (fun id -> id.it) |> Set.of_list
    in
    let bound_idx =
      match iter with
      | ListN (_, Some id) -> Set.singleton id.it
      | _ -> Set.empty
    in
    let known' = Set.union known (Set.union bound_ids bound_idx) in
    (* Validate iter expression if it’s ListN (exp, _) *)
    (match iter with
     | ListN (e, _) ->
        let fvs = free_vars_exp e in
        if not (Set.subset fvs known) then
          raise (InvalidDL (
            "Iteration expression uses unknown variables: " ^
            string_of_varset (Set.diff fvs known) ^
            "\nIn: " ^ Il.Print.string_of_prem prem
          ))
     | _ -> ());
    (* Validate body premise *)
    validate_prem known' p
  | IterPr (_, _) -> todo "Backend_animation.Valid.validate_prem"
  | ElsePr -> known

(* Validate a single rule clause *)
let validate_clause args e prems : unit =
  let initial_known = free_vars_args args in 
  let known_after_premises =
    List.fold_left validate_prem initial_known prems
  in
  let ret_fvs = free_vars_exp e in
  if not (Set.subset ret_fvs known_after_premises) then
    raise (InvalidDL "Return value uses unknown variables")

(* Validate a full func_def *)
let validate_func_def (fd : Def.func_def) : string list option =
  let (fdid, clauses) = fd.it in
  List.map (fun clause ->
    match clause.it with 
      | DefD (_, args, e, prems) -> 
        match
          validate_clause args e prems 
        with 
        | exception (InvalidDL msg) -> 
            let msg = msg ^ "\n... of clause:" ^ (Il.Print.string_of_clause fdid clause) ^ "\n" in
            Some msg
        | _ -> None
  ) clauses |> Lib.Option.cat_opts_opt

let validate (dl : Def.dl_def list) : string list option =
  let open Def in 
  List.map (fun def -> 
    match def with
      | RuleDef   _ -> Some ["RuleDef found: shouldn't happen."]
      | HelperDef _ -> Some ["HelperDef found: shouldn't happen."]
      | FuncDef fd -> validate_func_def fd
  ) dl |> Lib.Option.cat_opts_opt |> Option.map List.flatten
