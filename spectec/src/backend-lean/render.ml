open Lean_ast

module NonEmptyList = Util.Lib.NonEmptyList

(* let rec render_command (cmd : command) : string =
  match cmd with
  | DefAsgn (modifier, decl_id, opt_decl_sig, term) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let term_str = render_term term in
    Printf.sprintf "%s def %s %s := %s" modifier_str decl_id decl_sig_str term_str
  | DefCaseMatch (modifier, decl_id, opt_decl_sig, cases) ->
    let modifier_str = render_decl_modifier modifier in
    let decl_sig_str = render_opt_decl_sig opt_decl_sig in
    let cases_str = String.concat "\n" (List.map render_case cases) in
    Printf.sprintf "%s def %s %s\n  %s" modifier_str decl_id decl_sig_str cases_str *)

let rec render_command (cmd : command) : string =
  match cmd with
  | Def def -> render__def def
  | Inductive ind -> render__inductive ind
  | Abbrev ab -> render__abbrev ab
  | Structure s -> render__structure s
  | Opaque o -> render_opaque o
  | Mutual m -> render_mutual m

and render_mutual (mutual : mutual) : string =
  match mutual with
  | MutualInductiveStructure (inds, structs) ->
    let inds_str = String.concat "\n" (List.map render__inductive inds) in
    let structs_str = String.concat "\n" (List.map render__structure structs) in
    Printf.sprintf
      "mutual\n%s\n%s\n end"
      inds_str
      structs_str

  | MutualDefAbbrev (defs, abbrevs) ->
    let defs_str = String.concat "\n" (List.map render__def defs) in
    let abbrevs_str = String.concat "\n" (List.map render__abbrev abbrevs) in
    Printf.sprintf
      "mutual\n%s\n%s\n end"
      defs_str
      abbrevs_str

and render_opaque (op : opaque) : string =
  let modifier_str = render_decl_modifier op.modifier in
  let id_str = render_id op.id in
  let decl_sig_str = render_decl_sig op.signature in
  let rhs_string = match op.rhs with
  | None -> ""
  | Some r -> Printf.sprintf ":= %s" (render_term r)
  in
  Printf.sprintf
    "%s opaque %s %s %s"
    modifier_str
    id_str
    decl_sig_str
    rhs_string

and render_argument (arg : argument) : string =
  match arg with
  | Term t -> render_term t

and render_num (num : _numtype) : string =
  match num with
  | LeanNat n -> Z.to_string n
  | LeanInt i ->
    if i >= Z.zero then
      Z.to_string i
    else
      Printf.sprintf "-%s" (Z.to_string (Z.abs i))
  | LeanRat q -> Printf.sprintf "%s/%s" (Z.to_string (Q.num q)) (Z.to_string (Q.den q))
  | LeanReal r -> Printf.sprintf "%.17g" r (* 17 significant digits seems to be minimum for exact representation of any IEEE 754 double-precision float *)

and render_struct_inst_l_val (silv : struct_inst_l_val) : string =
  match silv with
  | Ident_SILV id -> render_id id
  | Num_SILV i -> string_of_int i

and render_struct_inst_field (sif : struct_inst_field) : string =
  match sif with
  | Ident_SIF id -> render_id id
  | AssignedField {
      l_val = l_val;
      is_private = is_private;
      term = term;
  } ->
    let l_val_str = render_struct_inst_l_val l_val in
    let privacy_str = if is_private then "private " else "" in
    let term_str = render_term term in
    Printf.sprintf
      "%s%s := %s"
      privacy_str
      l_val_str
      term_str

and render__index_type (index_type : _index_type) : string =
  match index_type with
  | Plain -> ""
  | Option -> "?"
  | Unsafe -> "!"

and render__slice_bounds (bounds : _slice_bounds) : string =
  match bounds with
  | SliceFrom e -> string_of_int 0 ^ " : " ^ render_term e
  | SliceTo e -> render_term e ^ " : _"
  | SliceBetween (e1, e2) -> render_term e1 ^ " : " ^ render_term e2

and render_fun_binder (binder : fun_binder) : string =
  match binder with
  | Ident_FB id -> render_id id

(* TODO: adapt more properly from original backend *)
and render_id a = match a with
  | "rec" -> "rec_"
  | "bool" -> "nat_of_bool"
  | "mut" | "local" | "export" | "import" | "catch" | "syntax" | "at"
    -> Printf.sprintf "«%s»" a
  | _ -> a

and render_term (term : term) : string =
  match term with
  | Hole _ -> "_"

  | FunType (t1, t2) ->
      Printf.sprintf "%s -> %s" (render_term t1) (render_term t2)

  | Ident id -> render_id id

  | Sort level -> Printf.sprintf "Sort %s" (render_level level)

  | Type None -> "Type"

  | Type (Some level) -> Printf.sprintf "Type %s" (render_level level)

  | Prop -> "Prop"

  | ProdType (t1, t2) -> Printf.sprintf "%s × %s" (render_term t1) (render_term t2)

  | FunApp (t1, args) ->
      let args_str = String.concat " " (List.map render_argument (NonEmptyList.to_list args)) in
      Printf.sprintf
        "%s %s"
        (render_term t1)
        args_str

  | FunAppEllipsis (t1, args) ->
      let args_str = String.concat " " (List.map render_argument args) in
      Printf.sprintf
        "%s %s ..."
        (render_term t1)
        args_str

  | Num num -> render_num num

  | Text s -> Printf.sprintf "\"%s\"" s

  | BinaryInfixFunApp (arg1, term, arg2)
    ->
      let arg1_str = render_argument arg1 in
      let term_str = render_term term in
      let arg2_str = render_argument arg2 in
      Printf.sprintf
        "%s %s %s"
        arg1_str
        term_str
        arg2_str

  | Tuple terms ->
      let terms_str = String.concat ", " (List.map render_term terms) in
      Printf.sprintf
        "(%s)"
        terms_str

  | DotProj (t1, t2) ->
      let t1_str = render_term t1 in
      let t2_str = render_term t2 in
      Printf.sprintf
        "%s.%s"
        t1_str
        t2_str

  | Struct {
    fields = fields;
    type_annotation = type_annotation;
  } ->
      let fields = List.map render_struct_inst_field fields in
      let fields_str = String.concat "\n" fields in
      let type_annotation_str = match type_annotation with
        | None -> ""
        | Some t -> Printf.sprintf "\n : %s" (render_term t)
       in
      Printf.sprintf
        "{\n%s%s\n}"
        fields_str
        type_annotation_str

  | List terms -> 
      let terms_str = String.concat ", " (List.map render_term terms) in
      Printf.sprintf
        "[%s]"
        terms_str

  | Index {
    collection = collection;
    index = index;
    index_type = index_type;
  } ->
      let collection_str = render_term collection in
      let index_str = render_term index in
      let index_type_str = render__index_type index_type in
      Printf.sprintf
        "%s[%s]%s"
        collection_str
        index_str
        index_type_str

  | Slice {
    collection = collection;
    bounds = bounds;
  } ->
      let collection_str = render_term collection in
      let bounds_str = render__slice_bounds bounds in
      Printf.sprintf
        "%s[%s]"
        collection_str
        bounds_str

  | UpdateStruct {
    struct_to_update = struct_to_update;
    fields_to_update = fields_to_update;
  } ->
      let struct_to_update_str = render_term struct_to_update in
      let struct_inst_field_strs = List.map render_struct_inst_field fields_to_update in
      let fields_to_update_str = String.concat "\n" struct_inst_field_strs in
      Printf.sprintf
        "{\n%s with \n%s\n}"
        struct_to_update_str
        fields_to_update_str

  | Lambda {
    params = params;
    body = body;
  } ->
      let params_str = String.concat " " (List.map render_fun_binder (NonEmptyList.to_list params)) in
      let body_str = render_term body in
      Printf.sprintf
        "fun %s => %s"
        params_str
        body_str

  | IfThenElse {
    cond = cond;
    then_branch = then_branch;
    else_branch = else_branch;
  } ->
      let cond_str = render_term cond in
      let then_branch_str = render_term then_branch in
      let else_branch_str = render_term else_branch in
      Printf.sprintf
        "if %s then %s else %s"
        cond_str
        then_branch_str
        else_branch_str

and render_level (level : level) : string =
  match level with
  | LevelLit n -> string_of_int n
  | LevelVar id -> render_id id

and render__structure (s : _structure) : string =
  let modifier_str = render_decl_modifier s.modifier in
  let id_str = render_id s.id in
  let binders = String.concat "" (List.map render_bracketed_binder s.binders) in
  let universe = match s.universe with
  | None -> ""
  | Some r -> render_term r
  in
  let constructor = match s.constructor with
  | None -> ""
  | Some (constructor_modifier, constructor_id) -> (render_decl_modifier constructor_modifier) ^ (render_id constructor_id) ^ ":: "
  in
  let fields_str = String.concat "\n" (List.map render_struct_field s.fields) in
  let deriving_str = match s.deriving with 
  | None -> ""
  | Some der -> render__deriving der
  in
  Printf.sprintf
    "%s structure %s %s %s where %s \n %s \n %s"
    modifier_str
    id_str
    binders
    universe
    constructor
    fields_str
    deriving_str

and render_struct_field (sf : struct_field) : string =
  match sf with
  | StructSimpleBinder ssb
    ->
      Printf.sprintf
        "%s %s %s"
        (render_decl_modifier ssb.modifier)
        (render_id ssb.id)
        (render_opt_decl_sig ssb.signature)

and render__def (def : _def) : string =
  match def with
  | DefAsgn d ->
    let modifier_str = render_decl_modifier d.modifier in
    let id_str = render_id d.id in
    let decl_sig_str = render_opt_decl_sig d.signature in
    let term_str = render_term d.body in
    Printf.sprintf
      "%s def %s %s := %s"
      modifier_str
      id_str
      decl_sig_str
      term_str

  | DefCases d ->
    let modifier_str = render_decl_modifier d.modifier in
    let id_str = render_id d.id in
    let decl_sig_str = render_opt_decl_sig d.signature in
    let cases_str = String.concat "\n" (List.map render__def_case d.body) in
    Printf.sprintf
      "%s def %s %s\n  %s"
      modifier_str
      id_str
      decl_sig_str
      cases_str

and render__def_case (case : _def_case) : string =
  let (pattern, body) = case in
  let pattern_str = render_term pattern in
  let body_str = render_term body in
  Printf.sprintf "| %s => %s" pattern_str body_str

and render__inductive (ind : _inductive) : string =
  (* let (modifier, decl_id, opt_decl_sig, cases, deriving) = ind in *)
  let modifier_str = render_decl_modifier ind.modifier in
  let id_str = render_id ind.id in
  let decl_sig_str = render_opt_decl_sig ind.signature in
  let cases_str = String.concat "\n" (List.map render__inductive_case ind.cases) in
  let deriving_str = match ind.deriving with 
    | None -> ""
    | Some der -> render__deriving der
  in
  Printf.sprintf
    "%s inductive %s %s where\n  %s\n%s"
    modifier_str
    id_str
    decl_sig_str
    cases_str
    deriving_str

and render__inductive_case (case : _inductive_case) : string =
  let modifier_str = render_decl_modifier case.modifier in
  let id_str = render_id case.id in
  let decl_sig_str = render_opt_decl_sig case.signature in
  Printf.sprintf
    "| %s %s %s"
    modifier_str
    id_str
    decl_sig_str

and render__abbrev (abbrev : _abbrev) : string =
  match abbrev with
  | AbbrevAsgn a ->
    let modifier_str = render_decl_modifier a.modifier in
    let id_str = render_id a.id in
    let decl_sig_str = render_opt_decl_sig a.signature in
    let term_str = render_term a.body in
    Printf.sprintf
      "%s abbrev %s %s := %s"
      modifier_str
      id_str
      decl_sig_str
      term_str
  | AbbrevCases a ->
    let modifier_str = render_decl_modifier a.modifier in
    let id_str = render_id a.id in
    let decl_sig_str = render_opt_decl_sig a.signature in
    let cases_str = String.concat "\n" (List.map render__def_case a.body) in
    Printf.sprintf
      "%s abbrev %s %s\n  %s"
      modifier_str
      id_str
      decl_sig_str
      cases_str

and render__deriving (deriving : _deriving) : string =
  match deriving with
  | [] -> ""
  | idents -> Printf.sprintf "deriving %s" (String.concat ", " idents)

and render_decl_modifier (modifier : decl_modifier) : string =
  let comment_str = match modifier.comment with
    | Some comment -> Printf.sprintf "/- %s -/\n" comment
    | None -> ""
  in
  let visibility_str = match modifier.visibility with
    | Some Private -> "private"
    | Some Protected -> "protected"
    | Some Public -> "public"
    | None -> ""
  in
  let noncomputable_str = if modifier.noncomputable then "noncomputable" else "" in
  let unsafe_str = if modifier.unsafe then "unsafe" else "" in
  let recursion_str = match modifier.recursion_modifer with
    | Some Partial -> "partial"
    | Some NonRec -> "nonrec"
    | None -> ""
  in
  String.concat " " [comment_str; visibility_str; noncomputable_str; unsafe_str; recursion_str]

and render_decl_sig (params, term : decl_sig) : string =
  (* Technically this is a subset of opt_decl_sig, but Lean's reference found it convenient to distinguish the two *)
  let params_str = String.concat " " (List.map render_params params) in
  let term_str = render_term term in
  Printf.sprintf
    "%s : %s"
    params_str
    term_str

and render_opt_decl_sig (opt_decl_sig : opt_decl_sig) : string =
  match opt_decl_sig with
  | (params, Some term) -> 
    prerr_endline ("rendering decl sig with term: " ^ render_term term);
    let params_str = String.concat " " (List.map render_params params) in
    let term_str = render_term term in
    Printf.sprintf
      "%s : %s"
      params_str
      term_str

  | (params, None) ->
    prerr_endline ("rendering decl sig without term" );
    let params_str = String.concat " " (List.map render_params params) in
    Printf.sprintf
      "%s"
      params_str

and render_params (param : _params) : string =
  match param with
  | Ident ident -> render_id ident
  | Hole _ -> "_"
  | BracketedBinder binder -> render_bracketed_binder binder

and render__ident_or_hole (ioh : _ident_or_hole) : string =
  match ioh with
  | Ident ident -> render_id ident
  | Hole _ -> "_"

and render_bracketed_binder (binder : bracketed_binder) : string =
  match binder with
  | ExplicitParam (idents, term) ->
    let idents_str = String.concat " " (List.map render__ident_or_hole (NonEmptyList.to_list idents)) in
    let term_str = render_term term in
    Printf.sprintf "(%s : %s)" idents_str term_str
  | OptAutoParam (idents, term1, term2) ->
    let idents_str = String.concat " " (List.map render__ident_or_hole (NonEmptyList.to_list idents)) in
    let term1_str = render_term term1 in
    let term2_str = render_term term2 in
    Printf.sprintf "(%s : %s := %s)" idents_str term1_str term2_str
  | ImplicitParam (idents, term) ->
    let idents_str = String.concat " " (List.map render__ident_or_hole (NonEmptyList.to_list idents)) in
    let term_str = render_term term in
    Printf.sprintf "{%s : %s}" idents_str term_str

(* NOTE: _script isn't a Lean AST construct at time of writing; this function is
just for convenience *)
and render__script (script : command list) : string =
  let commands_str = String.concat "\n\n" (List.map render_command script) in
  commands_str