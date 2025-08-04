open Il.Ast
open Il.Free
open Il.Print
open Def
open Util
open Error
open Source


let string_of_error at msg = string_of_region at ^ " DL animation validation error:\n" ^ msg
let error at msg = Error.error at "DL validation" msg
let error_pr at msg prem = error at (msg ^ "\n" ^ "In premise: " ^ string_of_prem prem)


(* Helper: collect free variables from expressions and args *)
let rec free_vars_path (p : path) : Set.t =
  match p.it with
  | RootP -> Set.empty
  | IdxP (p1, e) -> Set.union (free_vars_path p1) (free_vars_exp e)
  | SliceP (p1, e1, e2) -> Set.union (Set.union (free_vars_path p1) (free_vars_exp e1)) (free_vars_exp e2)
  | DotP (p1, _) -> free_vars_path p1
and free_vars_exp (e : exp) : Set.t =
  match e.it with
  | VarE id -> Set.singleton id.it
  | BoolE _ | NumE _ | TextE _ |  OptE None -> Set.empty
  | UnE (_, _, e1) | TheE e1 | OptE (Some e1) | LiftE e1 | LenE e1
  | ProjE (e1, _) | DotE (e1, _) | CaseE (_, e1) | UncaseE (e1, _)
  | CvtE (e1, _, _) | SubE (e1, _, _) | SupE (e1, _, _) -> free_vars_exp e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2)
  | CatE (e1, e2) | CompE (e1, e2) | MemE (e1, e2) | IdxE (e1, e2) ->
    Set.union (free_vars_exp e1) (free_vars_exp e2)
  | UpdE (e1, p, e2) | ExtE (e1, p, e2) ->
    Set.union (free_vars_exp e1) (Set.union (free_vars_path p) (free_vars_exp e2))
  | TupE es | ListE es ->
    List.fold_left (fun acc e -> Set.union acc (free_vars_exp e)) Set.empty es
  | CallE (_, args) -> free_vars_args args
  | IterE (e1, (iter, xes)) ->
    let bound_ids = List.map fst xes |> List.map (fun id -> id.it) |> Set.of_list in
    let bound_idx = match iter with
      | ListN (_, Some id) -> Set.singleton id.it
      | _ -> Set.empty
    in
    let bindings = List.filter_map (fun (x, e) -> if (Set.mem x.it bound_idx) then None else Some e) xes |> List.map free_vars_exp |> List.fold_left Set.union Set.empty in
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
    | _ -> acc
  ) Set.empty args


let valid_type_def td = ()


(* Validate a single premise *)
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
    if not (List.length vars = 1) then
      error_pr prem.at ("LetPr can only bind one variable, but got " ^ string_of_varset (Set.of_list vars)) prem;
    let var = List.hd vars in
    let rhs_fvs = free_vars_exp rhs in
    let unknowns = Set.diff rhs_fvs known in
    if not (Set.is_empty unknowns) then
      error_pr rhs.at ("LetPr RHS uses unknown variables: " ^ string_of_varset unknowns) prem;
    (match lhs.it with
      | VarE lhs_var ->
        if lhs_var.it <> var then
          error_pr lhs.at ("LetPr LHS variable `" ^ lhs_var.it ^ "` doesn't match binder `" ^ var ^ "`.") prem
      | _ -> error_pr lhs.at ("Let binding LHS must be a variable, but got " ^ string_of_exp lhs) prem
    );
    if Set.mem var known then
      error_pr prem.at ("LetPr binder `" ^ var ^ "` already known") prem;
    Set.add var known
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
    let bound_idx =
      (match iter with
        | ListN (l, idopt) ->
          let fv_l = free_vars_exp l in
          let unknown_l = Set.diff fv_l known in
          if Set.is_empty unknown_l then
            match idopt with
            | Some id -> Set.singleton id.it
            | None -> Set.empty
          else
            error_pr l.at ("IterN length `" ^ string_of_exp l ^ "` contains unknowns: " ^ string_of_varset unknown_l) prem
        | _ -> Set.empty
      ) in
    (* Validate body premise *)
    let new_knowns = (List.fold_left valid_prem (Set.union new_knowns bound_idx) plist) in
    (* Out-flow *)
    let out_flow_knowns acc (x, e) =
      (* we don't need to out-flow `i*` if i is the index *)
      if (Set.mem x.it bound_idx) then acc else 
      if (Set.mem x.it acc) then 
        (* this iterator is now out of scope *)
        let rmv_iter = Set.diff acc (Set.singleton x.it) in
        Set.union rmv_iter (free_vars_exp e)
      else
        error_pr e.at ("Iteration binding {x <- e} ill-formed." ^
          "Either x or e must be known: (" ^ string_of_id x ^ ", " ^ string_of_exp e ^ ")") prem
    in
    List.fold_left out_flow_knowns new_knowns pairs
  | ElsePr -> known

(* Validate a single rule clause *)
let valid_clause at args e prems : unit =
  let initial_known = free_vars_args args in
  let known_after_premises =
    List.fold_left valid_prem initial_known prems
  in
  let ret_fvs = free_vars_exp e in
  if not (Set.subset ret_fvs known_after_premises) then
    error at ("Return value uses unknown variables: \n" ^ string_of_varset (Set.diff ret_fvs known_after_premises))

(* Validate a full func_def *)
let valid_func_def (fd : func_def) : unit =
  let (fdid, ps, t, clauses, _) = fd.it in
  List.iter (fun clause ->
    let DefD (_, args, e, prems) = clause.it in
    valid_clause clause.at args e prems
  ) clauses

let valid_def (def: dl_def) : unit = match def with
  | TypeDef td -> valid_type_def td
  | RuleDef rd -> error rd.at "RuleDef found: shouldn't happen."
  | FuncDef fd -> valid_func_def fd

let valid (dl : dl_def list) : unit =
  List.iter valid_def dl
