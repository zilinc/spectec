(* let rec render_command (cmd : Lean_ast.command) : string =
  match cmd with
  | Lean_ast.DefAsgn (modifier, decl_id, opt_decl_sig, term) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let term_str = render_term term in
    Printf.sprintf "%s def %s %s := %s" modifier_str decl_id decl_sig_str term_str
  | Lean_ast.DefCaseMatch (modifier, decl_id, opt_decl_sig, cases) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let cases_str = String.concat "\n" (List.map render_case cases) in
    Printf.sprintf "%s def %s %s\n\t%s" modifier_str decl_id decl_sig_str cases_str *)

let rec render_command (cmd : Lean_ast.command) : string =
  match cmd with
  | Lean_ast.Def def -> render__def def
  | Lean_ast.Inductive ind -> render__inductive ind
  | Lean_ast.Abbrev ab -> render__abbrev ab

and render__def (def : Lean_ast._def) : string =
  match def with
  | Lean_ast.DefAsgn (modifier, decl_id, opt_decl_sig, term) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let term_str = render_term term in
    Printf.sprintf "%s def %s %s := %s" modifier_str decl_id decl_sig_str term_str
  | Lean_ast.DefCases (modifier, decl_id, opt_decl_sig, cases) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let cases_str = String.concat "\n" (List.map render__def_case cases) in
    Printf.sprintf "%s def %s %s\n\t%s" modifier_str decl_id decl_sig_str cases_str

and render__def_case (case : Lean_ast._def_case) : string =
  let (pattern, body) = case in
  let pattern_str = render_term pattern in
  let body_str = render_term body in
  Printf.sprintf "| %s => %s" pattern_str body_str

and render__inductive (ind : Lean_ast._inductive) : string =
  let (modifier, decl_id, opt_decl_sig, cases, deriving) = ind in
  let modifier_str = render_decl_modifier modifier in
  let decl_sig_str = render_opt_decl_sig opt_decl_sig in
  let cases_str = String.concat "\n" (List.map render__inductive_case cases) in
  let deriving_str = render__inductive_deriving deriving in
  Printf.sprintf "%s inductive %s %s\n\t%s\n%s" modifier_str decl_id decl_sig_str cases_str deriving_str

and render__inductive_case (case : Lean_ast._inductive_case) : string =
  let (decl_id, ident, opt_decl_sig) = case in
  let decl_sig_str = render_opt_decl_sig opt_decl_sig in
  Printf.sprintf "| %s %s %s" decl_id ident decl_sig_str

and render__abbrev (abbrev : Lean_ast._abbrev) : string =
  match abbrev with
  | Lean_ast.AbbrevAsgn (modifier, decl_id, opt_decl_sig, term) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let term_str = render_term term in
    Printf.sprintf "%s abbrev %s %s := %s" modifier_str decl_id decl_sig_str term_str
  | Lean_ast.AbbrevCases (modifier, decl_id, opt_decl_sig, cases) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let cases_str = String.concat "\n" (List.map render__def_case cases) in
    Printf.sprintf "%s abbrev %s %s\n\t%s" modifier_str decl_id decl_sig_str cases_str

and render__inductive_deriving (deriving : Lean_ast._inductive_deriving) : string =
  match deriving with
  | [] -> ""
  | idents -> Printf.sprintf "deriving %s" (String.concat ", " idents)

and render_decl_modifier (modifier : Lean_ast.decl_modifier) : string =
  let comment_str = match modifier.comment with
    | Some comment -> Printf.sprintf "/- %s -/\n" comment
    | None -> ""
  in
  let visibility_str = match modifier.visibility with
    | Some Lean_ast.Private -> "private"
    | Some Lean_ast.Protected -> "protected"
    | Some Lean_ast.Public -> "public"
    | None -> ""
  in
  let noncomputable_str = if modifier.noncomputable then "noncomputable" else "" in
  let unsafe_str = if modifier.unsafe then "unsafe" else "" in
  let recursion_str = match modifier.recursion_modifer with
    | Some Lean_ast.Partial -> "partial"
    | Some Lean_ast.NonRec -> "nonrec"
    | None -> ""
  in
  String.concat " " [comment_str; visibility_str; noncomputable_str; unsafe_str; recursion_str]

and render_opt_decl_sig (opt_decl_sig : Lean_ast.opt_decl_sig) : string =
  match opt_decl_sig with
  | (params, Some term) -> 
    let params_str = String.concat " " (List.map render_params params) in
    let term_str = render_term term in
    Printf.sprintf "%s : %s" params_str term_str
  | (params, None) ->
    let params_str = String.concat " " (List.map render_params params) in
    Printf.sprintf "%s" params_str

and render_params (param : Lean_ast._params) : string =
  match param with
  | Lean_ast.Ident ident -> ident
  | Lean_ast.Hole _ -> "_"
  | Lean_ast.BracketedBinder binder -> render_bracketed_binder binder

and render__ident_or_hole (ioh : Lean_ast._ident_or_hole) : string =
  match ioh with
  | Lean_ast.Ident ident -> ident
  | Lean_ast.Hole _ -> "_"

and render_bracketed_binder (binder : Lean_ast.bracketed_binder) : string =
  match binder with
  | Lean_ast.ExplicitParam (idents, term) ->
    let idents_str = String.concat " " (List.map render__ident_or_hole (idents.head :: idents.tail)) in
    let term_str = render_term term in
    Printf.sprintf "(%s : %s)" idents_str term_str
  | Lean_ast.OptAutoParam (idents, term1, term2) ->
    let idents_str = String.concat " " (List.map render__ident_or_hole (idents.head :: idents.tail)) in
    let term1_str = render_term term1 in
    let term2_str = render_term term2 in
    Printf.sprintf "(%s : %s := %s)" idents_str term1_str term2_str
  | Lean_ast.ImplicitParam (idents, term) ->
    let idents_str = String.concat " " (List.map render__ident_or_hole (idents.head :: idents.tail)) in
    let term_str = render_term term in
    Printf.sprintf "{%s : %s}" idents_str term_str

and render_term (term : Lean_ast.term) : string =
  match term with
  | Lean_ast.Hole _ -> "_"
  | Lean_ast.Fun (ident, body) ->
    let body_str = render_term body in
    Printf.sprintf "fun %s => %s" ident body_str

