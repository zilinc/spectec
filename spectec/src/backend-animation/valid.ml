open Il.Ast
open Il.Free
open Il.Print
open Il2al
open Util
open Error
open Source


exception InvalidDL of string

let string_of_error at msg = string_of_region at ^ " DL animation validation error:\n" ^ msg
let error at msg = raise (InvalidDL (string_of_error at msg))
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

(* Validate a single premise *)
let rec validate_prem (known : Set.t) (prem : prem) : Set.t =
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
    (* {t <- t*} is bidirectional so only one side should be known *)
    let new_knowns = ref known in
    (* [knowniters] can be either in-flow or out-flow.
       [unknowniters] are those that we know neither side.
    *)
    let knowniters, unknowniters = List.partition (
      fun (x, e) ->
        let fvs = free_vars_exp e in
        if not (Set.subset fvs known) then
          (* Not in-flow. *)
          if Set.mem x.it known then
            (* Out-flow. *)
            (match e.it with
            | VarE id' ->
              (new_knowns := Set.add id'.it !new_knowns; true)
            | _ -> error_pr e.at
              ("Out-flowing iteration binding {x <- e} ill-formed." ^
               "e should be VarE but got " ^ string_of_exp e) prem
            )
          else  (* No-flow. *)
            false
        else
          (* In-flow. *)
          (new_knowns := Set.add x.it !new_knowns; true)
    ) pairs in
    (* add optional index to knowns since it is bound *)
    (match iter with
      | ListN (l, Some id) ->
        let fv_l = free_vars_exp l in
        let unknown_l = Set.diff fv_l known in
        if Set.is_empty unknown_l then
          new_knowns := Set.add id.it !new_knowns
        else
          error_pr l.at ("IterN length `" ^ string_of_exp l ^ "` contains unknowns: " ^ string_of_varset unknown_l) prem
      | _ -> ()
    );
    (* Validate body premise *)
    new_knowns := (List.fold_left validate_prem !new_knowns plist);
    let unknowniterids = Set.of_list (List.map (fun (x, _) -> x.it) unknowniters) in
    let unknowns = Set.diff unknowniterids !new_knowns in
    if not (Set.is_empty unknowns) then
      error_pr prem.at
        ("Either the IterVars or their binders must be known, but got unknowns: " ^ string_of_varset unknowns) prem
    else
      let learnediters = Set.of_list (List.concat_map (fun (x, e) -> Set.elements (free_vars_exp e)) unknowniters) in
      new_knowns := Set.union !new_knowns learnediters;
    !new_knowns
  | ElsePr -> known

(* Validate a single rule clause *)
let validate_clause at args e prems : unit =
  let initial_known = free_vars_args args in
  let known_after_premises =
    List.fold_left validate_prem initial_known prems
  in
  let ret_fvs = free_vars_exp e in
  if not (Set.subset ret_fvs known_after_premises) then
    error at ("Return value uses unknown variables: \n" ^ string_of_varset (Set.diff ret_fvs known_after_premises))

(* Validate a full func_def *)
let validate_func_def (fd : Def.func_def) : string list option =
  let (fdid, clauses) = fd.it in
  List.map (fun clause ->
    match clause.it with
      | DefD (_, args, e, prems) ->
        match
          validate_clause clause.at args e prems
        with
        | exception (InvalidDL msg) -> Some msg
        | _ -> None
  ) clauses |> Lib.Option.cat_opts_opt

let validate (dl : Def.dl_def list) : string list option =
  let open Def in
  List.map (fun def ->
    match def with
      | RuleDef   rd -> Some [string_of_error rd.at "RuleDef found: shouldn't happen."]
      | HelperDef hd -> Some [string_of_error hd.at "HelperDef found: shouldn't happen."]
      | FuncDef fd -> validate_func_def fd
  ) dl |> Lib.Option.cat_opts_opt |> Option.map List.flatten
