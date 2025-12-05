open Il.Ast
open Il.Print
open Util.Source
open Xl
open Def
open Util_ocaml
open Util.Error 

module TypeM   = Util_ocaml.TypeM
open TypeM

exception CannotAnimate

(* used to catch refutable patterns inside iterators, so the maps may be made monadic as well *)
let rec is_monadic (prems : prem list) = 
  List.exists (fun p -> match p.it with 
    | LetPr (lhs_exp, _, _) -> begin match lhs_exp.it with
      | CaseE _ | OptE _ | SubE _ -> true
      | _ -> false
      end
    | IterPr (inner_prems, _) -> is_monadic inner_prems
    | _ -> false
  ) prems


let rec get_dl_def_region (dl_def : dl_def) : region =
  match dl_def with
  | FuncDef fd -> fd.at
  | TypeDef td -> td.at
  | RecDef (rd :: _) -> get_dl_def_region rd
  | RuleDef rd -> rd.at

(* type variables need to be prefixed with '*)
let typevars_of_params (ps : param list) : Set.t =
  ps
  |> List.filter_map (fun p ->
       match p.it with
       | TypP id -> Some (sanitize_name id.it)
       | _ -> None)
  |> Set.of_list

let collect_vars (e : exp) : string list t = match e.it with 
  | VarE id -> 
    let* () = add_known id.it in 
    return [sanitize_name id.it]
  | TupE es ->
      let rec go acc = function
        | [] -> return (List.rev acc)
        | {it = VarE id; _} :: rest ->
            let* () = add_known id.it in
            go (sanitize_name id.it :: acc) rest
        | _ :: _ -> raise CannotAnimate
      in
      go [] es
  | _ -> raise CannotAnimate

(* generate a tuple of fresh variables for cased expressions *)
let fresh_tuple n : string =
  match n with
  | 0 -> "()"
  | 1 -> "freshvar_0"
  | n ->
      "(" ^ String.concat ", "
               (List.init n (fun i -> Printf.sprintf "freshvar_%d" i))
      ^ ")"

(* TODOs: 
REFACTOR (always)
the above functions should be reused when the LHS of a let pr is case e
do not import the typeM stuff above
compose funcdefs and calls need types to be resolved correctly
the typecasts writer should be renamed, now it may also contain uncasings *)

(* This exception is raised when the OCaml generator sees a pattern that it does not expect (for example, if ruled out by validation) / unreachable code *) 
let error at msg = error at "OCaml CodeGen" msg

let get_type e = 
  match e.note.it with
  | VarT (id, _) -> id.it
  | BoolT -> "bool"
  | NumT num -> begin match num with 
    | `NatT | `IntT -> "int"
    | `RatT | `RealT -> "float" end 
  | TextT -> "string"                    
  | TupT _ -> "todo"
  | IterT _ -> "todo"

(* as of now, we do not error if the type is NOT a tuple as the IL elaboration converts a Tup [t] into t. depending on how the parser is defined and used this can cause issues later *)
let rec get_tupsize (t : typ) : int option t =
  match t.it with
  | TupT ts -> return (Some (List.length ts))
  | VarT (id, _) -> 
    let* typedef = get_typedef id.it in 
    let td = match typedef with
    | Some (TypeDef td) -> td 
    | _ -> error t.at "Unknown typevariable in projection"
    in begin
    match td.it with 
    | (_, _, [ {it = InstD (_, as_, dt); _} ]) -> begin
      match dt.it with
      | AliasT alias -> get_tupsize alias
      | _ -> return (Some 1)
      end
    | _ -> error t.at "todo: projection for multiple instance types"
    end
  | IterT (_, List) | IterT (_, List1) | IterT (_, ListN _) -> return None 
  (*| _ -> error t.at "Projection in non-tuple/list/alias"*)
  | _ -> return (Some 1)

let rmv_nonexp (p: param) : bool = match p.it with 
  | ExpP _ -> true
  | _ -> false

let known_exps (es : exp list) : bool t =
  allM (fun e -> begin
    match e.it with
    | VarE id -> is_known (sanitize_name id.it)
    | _ -> error e.at "Invalid Iterator expression x <- e: e must be a variable."
  end) es

let get_unknown_vars (es : (id * exp) list) : string list t =
  foldM (fun acc (id, e) ->
    match e.it with
    | VarE id' -> let* known = is_known (sanitize_name id'.it) in 
      if known then return acc else return (id.it :: acc)
    | _ -> error e.at "Invalid Iterator expression x <- e: e must be a variable."
  ) [] es

let get_cons_args typargs = 
  match typargs.it with
  | VarT _ | NumT _ | IterT _ | BoolT | TextT ->
    (1, "fv_0", "fv_0")
  | TupT es ->
    let n = List.length es in
    if n = 0 then (0, "", "")
    else
      let vs = List.init n (fun i -> "fv_" ^ string_of_int i) in
        (n, "(" ^ String.concat ", " vs ^ ")",
            (*"Some (" ^ String.concat ", " vs ^ ")")*)
            String.concat ", " vs)

(* messy as of now *)
type step_path =
  | RootSP
  | IdxSP of exp
  | SliceSP of exp * exp
  | DotSP of atom * typ 

let rec flatten_path (p : path) (acc : step_path list) : step_path list =
  match p.it with
  | RootP -> acc 
  | IdxP (p, e) -> flatten_path p (IdxSP e :: acc)
  | SliceP (p1, e1, e2) -> flatten_path p1 (SliceSP (e1, e2) :: acc)
  | DotP (p, atom) -> flatten_path p (DotSP (atom, p.note) :: acc)


(* this is very incomplete, not sure how much is necessary *)
let check_eq_exp e1 e2 = 
  match e1.it, e2.it with
  | VarE id1, VarE id2 -> id1.it = id2.it
  | _ -> false

let rec check_eq_typs t1 t2 =
  match t1.it, t2.it with
  | VarT (id1, a1), VarT (id2, a2) -> id1.it = id2.it && List.length a1 = List.length a2 (* TODO: need to check each arg *)
  | BoolT, BoolT -> true
  | NumT _, NumT _ -> true (* TODO: implement *)
  | TextT, TextT -> true
  | TupT ets1, TupT ets2 ->
    List.length ets1 = List.length ets2 &&
    List.for_all2 (fun (e1, t1) (e2, t2) -> check_eq_exp e1 e2 && check_eq_typs t1 t2) ets1 ets2
  | IterT (t11, iter1), IterT (t21, iter2) ->
    check_eq_typs t11 t21 && iter1 = iter2
  | _ -> false

let get_common_consts tcs1 tcs2 =
  (*Printf.printf "Typcase 1 len:\n%d\n" (List.length tcs1);
  Printf.printf "Typcase 2 len:\n%d\n" (List.length tcs2);*)
  let consts1 = List.map (fun (op, (_, t, _), _) -> (Util_ocaml.mixop_to_atom_str op, t)) tcs1 in
  let consts2 = List.map (fun (op, (_, t, _), _) -> (Util_ocaml.mixop_to_atom_str op, t)) tcs2 in
  (*List.iter (fun (op, t) -> Printf.printf "Const 1: %s : %s\n" op (string_of_typ t)) consts1;
  List.iter (fun (op, t) -> Printf.printf "Const 2: %s : %s\n" op (string_of_typ t)) consts2;*)
  let comm = 
  List.filter (fun c ->
    List.exists (fun c2 -> fst c = fst c2 && check_eq_typs (snd c) (snd c2)) consts2
  ) consts1 in 
  (*Printf.printf "Common consts len: %d\n" (List.length comm);*)
  comm

let ocaml_of_numtyp = Num.string_of_typ

(* may have to change to option type *)
let generate_type_arms t1name t2name td1 td2 =
  let get_deftyp td = (match td with
  | _, _, [{it = InstD (_, _, dt); _}] -> Some dt
  | _ -> None) in
  let dt1 = get_deftyp td1
  and dt2 = get_deftyp td2 in
  if dt1 != None && dt2 != None then
    let dt1 = Option.get dt1
    and dt2 = Option.get dt2 in
    let arms =
      match dt1.it, dt2.it with
      | VariantT tcs1, VariantT tcs2 ->
        let common_consts = get_common_consts tcs1 tcs2 in
        let arms =
          List.map (fun (consname, typargs) ->
            let cons1 = (sanitize_name ~typecons:true ~typename:false consname) ^ "_" ^ t1name in
            let cons2 = (sanitize_name ~typecons:true ~typename:false consname) ^ "_" ^ t2name in
            let _, argstr, retstr = get_cons_args typargs in
            Printf.sprintf "  | %s -> Some (%s)" (append_sep cons1 argstr " ") (append_sep cons2 argstr " ")
          ) common_consts in
        String.concat "\n" arms (*^ "\n  | _ -> None\n"*)
      | _ -> "TODO: non-variant type conversion not implemented yet" in
      arms
  else
    "TODO: multiple insts in type conversion not implemented yet"

(* generates a function to project element i out of an n-tuple *)
let generate_proj n i : unit t = 
  let funcname = Printf.sprintf "proj_%d_%d" n i in
  let* is_defined = is_defined funcname in
  if is_defined then return () else
  let* () = add_func funcname in
  let type_vars = List.init n (fun i -> String.make 1 Char.(chr (code 'a' + i))) in
  let tuple_ty = String.concat " * " (List.map (fun v -> "'" ^ v) type_vars) in
  let ret_ty = "'" ^ List.nth type_vars i in
  let xs = List.init n (fun i -> "x" ^ string_of_int (i+1)) in
  let pat = String.concat ", " xs in
  let body = List.nth xs i in
  tell (Printf.sprintf "let %s : %s -> %s = function\n  | %s -> %s\n"
    funcname tuple_ty ret_ty pat body)

let typedef_of_dl_def (def : dl_def option) : type_def option =
  match def with
  | Some (TypeDef td) -> Some td
  | _ -> None

let generate_type_conv (t1 : typ) (t2 : typ) : unit t =
  match t1.it, t2.it with
  | VarT (id1, _), VarT (id2, _) ->
    let lhs  = sanitize_name id1.it
    and rhs  = sanitize_name id2.it in
    let funcname = Printf.sprintf "%s_of_%s" rhs lhs in
    (*Printf.printf "generating %s:\n" funcname;*)
    let* is_defined = is_defined funcname in
    if is_defined then return () else begin
    let* () = add_func funcname in
    let* dl_defs = mapM (get_typedef) [lhs; rhs] in
    let type_defs = List.map typedef_of_dl_def dl_defs in
    match type_defs with
    | [Some _lhs_def; Some _rhs_def] ->
      let func = Printf.sprintf "let %s_of_%s (arg : %s) : (%s option) =\n  match arg with\n" rhs lhs lhs rhs in
      let arms = generate_type_arms lhs rhs _lhs_def.it _rhs_def.it in
      let failcase = "  | _ -> None\n" in 
      tell (func ^ arms ^ failcase)
    | [None; _] -> error t1.at (Printf.sprintf "Type %s: appears in sub/super type but is not defined" lhs)
    | [_; None] -> error t2.at (Printf.sprintf "Type %s: appears in sub/super type but is not defined" rhs)
    end
  | _ -> tell "TODO: type conversion between non-VarTs not implemented yet\n"


let generate_numtype_conv (t1 : numtyp) (t2 : numtyp) : string t =
  let funcname = ocaml_of_numtyp t1 ^ "_of_" ^ ocaml_of_numtyp t2 in
  let* is_defined = is_defined funcname in
  if is_defined then return "" else begin
  let funcdef = "let " ^ funcname ^ " (arg : " ^ ocaml_of_numtyp t2 ^ ") : " ^ ocaml_of_numtyp t1 ^ " =\n" in
  let funcbody = "Num.cvt " ^ ocaml_of_numtyp t1 ^  " arg\n" in
  let* () = add_func funcname in
  return (funcdef ^ funcbody)
  end

(* this may be repeated but just grouping all terminals from the IL AST into one type for now - this should probably just refer to the generated ocaml types oops *)
type value =
  | NumV of Num.num
  | TextV of string
  | IdV of string
  | AtomV of Atom.atom
  | MixopV of Mixop.mixop

let ocaml_of_literal (e : exp) : string =
  match e.it with
  | NumE n -> Num.to_string n
  | TextE s -> Printf.sprintf "%S" s
  | BoolE b -> string_of_bool b
  | _ -> "_"

let ocaml_of_cmpop op =
  match Il.Print.string_of_cmpop op with
  | "=/=" -> "<>"
  | s -> s

let rec ocaml_of_exp ?(typearg=false) ?(funcdef=false) ?(funccall=false) (e : exp) : string t =
  (* for now, we don't support dependent types. *)
  if typearg then return "(* TODO:typearg *)" else 
  (* function arguments must be (subtyped/supertyped/cased) variables *)
  if funcdef then begin match e.it with 
  (* todo: whenever we call ocaml_of_typ here we MAY need to set consannot to true *)
  | VarE id -> 
    let* () = add_known id.it in 
    let* typevars = get_typevars () in
    (*Printf.printf "typevars in scope are: -----\n";
    Set.iter (Printf.printf "%s " ) typevars;
    Printf.printf "-----\n";*)
    let* typ_annot = ocaml_of_typ e.note in 
    return (Printf.sprintf "(%s : %s)" (sanitize_name ~typearg id.it) typ_annot)
  | SubE (e1, typ1, typ2) ->
    (* if an argument is of the form e : t1 <: t2, 
       the function expects an arg of type t1 but casts it to a type t2 in the body. so we have to add "let e = t2_of_t1 arg" to make it typecheck *)
    let* freshvarname = get_freshvar () in
    let* () = generate_type_conv typ2 typ1 in
    let* e1str = match e1.it with
    | VarE id -> let* () = add_known id.it in return (sanitize_name ~typearg id.it)
    | _ -> error e1.at "Invalid supertype/subtype argument: expected a variable."
    in 
    let* typ1str = ocaml_of_typ typ1 in
    let* typ2str = ocaml_of_typ typ2 in
    let* () =  add_typecast ("  let* " ^ e1str ^ " = " ^ typ1str ^ "_of_" ^ typ2str ^ " " ^ freshvarname ^ " in") in
    return (Printf.sprintf "(%s : %s)" freshvarname typ2str)
  | CaseE (mixop, e1) -> 
    (* todo: deal with nested cons *)
    let* cased_vars = collect_vars e1 in
    let newvararity = List.length cased_vars in
    let lhsvars = if (newvararity = 0) then "()" else 
      String.concat "," cased_vars 
    in
    let* freshvar = get_freshvar () in
    let* mixopstr = ocaml_of_mixop mixop e.note in
    let* typannot = ocaml_of_typ e.note in
    let retvals = fresh_tuple newvararity in
    let mixopargs = if (newvararity = 0) then "" else retvals in 
    let uncasing = Printf.sprintf "  let* %s = match %s with\n  | %s -> Some %s\n  | _ -> None\n  in" lhsvars freshvar (append_sep mixopstr mixopargs " ") retvals in
    let* () = add_typecast uncasing in
    return (Printf.sprintf "(%s : %s)" freshvar typannot)
  | _ -> raise CannotAnimate
  end else match e.it with
  | NumE n -> return (Num.to_string n)
  | TextE s -> return (Printf.sprintf "%S" s)
  | BoolE b -> return (string_of_bool b)
  | VarE id -> return (sanitize_name ~typearg id.it)
  | ListE es -> let* es_strs = concat_mapM "; " (ocaml_of_exp ~typearg) es in
    return ("[" ^ es_strs ^ "]")
  | TupE [] -> return ""
  | TupE es -> let* es_strs = concat_mapM ", " (ocaml_of_exp ~typearg) es in
    return ("(" ^ es_strs ^ ")")
  | CallE (id, args) ->
    let fname = sanitize_name id.it in
    let* args' = ocaml_of_args ~typearg ~funcdef ~funccall:true args in
    let args'' = if args' = "" then "()" else args' in
    return ("(" ^ fname ^ " " ^ args'' ^ ")")
  | CaseE (mixop, e1) ->
    (*Printf.printf "Generating case expression for mixop %s\n" (Util_ocaml.mixop_to_atom_str mixop);*)
    let* consdef = resolve_variant e.note in
    let* typename = ocaml_of_typ ~consannot:true (Option.get consdef) in
    let label = (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop)) ^ "_" ^ typename in
    let* e1str = ocaml_of_exp e1 in
    if not (e1str = "") then
      return ("(" ^ label ^ " " ^ e1str ^ ")")
    else return label 
  | BinE (op, _, e1, e2) -> 
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    let e1type = get_type e1 in
    let e2type = get_type e2 in
    (* ASSUMING THAT IF E IS NOT A FLOAT IT MUST BE AN INT: might be wrong *)
    let floatify estr etype float opstr =
      if (etype = "int") && (float || opstr = "**") then
        "(float_of_int " ^ estr ^ ")"
      else estr
    in 
    (* if either e1 or e2 is a float, we need to use a floating point operation (+. instead of +, for example) and convert the other exp to a float as well. *)
    let float = e1type = "float" || e2type = "float" in
    let binopstr = ocaml_of_binop ~float op in
    let e1str' = floatify e1str e1type float binopstr in
    let e2str' = floatify e2str e2type float binopstr in
    (* if both e1 and e2 were ints, but we used the float power operator, we need to convert the result back to an int *)
    if (e1type = "int") && (e2type = "int") && (binopstr = "**") then
      return ("(int_of_float (" ^ e1str' ^ " " ^ binopstr ^ " " ^ e2str' ^ "))")
    else return ("(" ^ e1str' ^ " " ^ binopstr ^ " " ^ e2str' ^ ")")
  | UnE (op, _, e1) ->
    let* e1str = ocaml_of_exp e1 in
    return (ocaml_of_unop op ^ "(" ^ e1str ^ ")")
  | UncaseE (e1, mixop) -> 
    let* consdef = resolve_variant e1.note in
    let* exptyp = ocaml_of_typ ~consannot:true (Option.get consdef) in 
    let* expstr = ocaml_of_exp e1 in
    let mixopstr = (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop)) ^ "_" ^ exptyp in 
    return (Printf.sprintf "(uncase_%s_%s (%s))" exptyp (String.lowercase_ascii mixopstr) expstr)
  | ProjE (e, n) -> 
    let* expstr = ocaml_of_exp e in
    let* typstr = ocaml_of_typ e.note in
    (*Printf.printf "projecting out of exp: %s, type: %s" expstr typstr;*)
    let* tupsize = get_tupsize e.note in begin 
    match tupsize with 
    | Some len -> 
      if n < 0 || n >= len then 
      error e.at "Tuple projection out of bounds." 
      else 
      let* () = generate_proj len n in 
      return (Printf.sprintf "(proj_%d_%d %s)" len n expstr)
    (* if not a tuple, we are projecting out of a list *)
    | None -> return (Printf.sprintf "(List.nth %s %d)" expstr n) end
    (*return (Printf.sprintf "(proj_%d_%d %s)" n n expstr)*)
  | CmpE (op, _, e1, e2) ->
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("(" ^ e1str ^ " " ^ ocaml_of_cmpop op ^ " " ^ e2str ^ ")")
  | IterE (e1, (iter, bindings)) ->
    let es = List.map snd bindings in
    let* all_inflows = known_exps es in
    if not all_inflows then begin 
    let* unknown_vars = get_unknown_vars bindings in
    match unknown_vars with
    | [x] -> 
      match iter with
      | ListN (e, optid) ->
        let* lenstr = ocaml_of_exp e in
        let idstr = match optid with
          | Some id -> id.it
          | None -> ""
        in
        if (not (idstr = x)) || (idstr = "") then return ("(* TODO: outflow in IterE *)")
        else 
        let* body_str = ocaml_of_exp e1 in 
        return ("(List.init (" ^ lenstr ^ ") (fun " ^ (sanitize_name idstr) ^ " -> " ^ body_str ^ "))")
    | _ -> return "(* TODO: multiple outflows in IterE *)"
    end else begin
    let* prev_knowns = get_knowns in 
    let new_knowns = List.map (fun i -> sanitize_name (fst i).it) bindings in 
    let* () = add_knowns new_knowns in 
    let* body_str = ocaml_of_exp e1 in
    match bindings with
    | [] -> 
      begin match iter with 
      | ListN (e, optid) ->
        let* lenstr = ocaml_of_exp e in
        let idstr = match optid with
          | Some id -> sanitize_name id.it
          | None -> "_"
        in
        let* () = set_knowns prev_knowns in 
        return ("(List.init (" ^ lenstr ^ ") (fun " ^ idstr ^ " -> " ^ body_str ^ "))")
      | _ -> let* () = set_knowns prev_knowns in  
        return "(* TODO: IterE with no bindings and non-length iterator *)"
      end 
    | bindings -> 
      begin match iter with 
      | List | ListN _ -> 
        let* listnames = mapM ocaml_of_exp es in 
        let varnames = String.concat " " (List.map (fun (id, _) -> (sanitize_name id.it)) bindings) in
        let* () = set_knowns prev_knowns in 
        let* () = add_knowns listnames in 
        let lists = String.concat " " listnames in
        return (Printf.sprintf "(map%d (fun %s -> %s) %s)" (List.length bindings) varnames body_str lists)
      | Opt ->
        (* assumption: if, in any of the bindings x <- x*, `x*` is None, we return None for the whole computation since `x` cannot have a value in that case *)
        let* listnames = mapM ocaml_of_exp es in
        let varnames = List.map (fun (id, _) -> (sanitize_name id.it)) bindings in 
        let get_opts = String.concat "\n" (List.map2 (fun i e -> (Printf.sprintf "    let %s = Option.get %s in" i e)) varnames listnames) in 
        let* () = set_knowns prev_knowns in 
        let* () = add_knowns listnames in 
        return (Printf.sprintf "(try (\n%s\n    Some(%s))\n  with Invalid_argument _ ->  None)" get_opts body_str)
        (*return ("(Some (" ^ get_opts ^ " " ^ body_str ^ "))")*)
      | _ -> 
        return "(* TODO: IterE with multiple-bindings and non-list iterator *)"
      end
    end
  | SubE (e1, typ1, typ2) ->
    (* Subtyping should not be refutable (I think) unless it appears on the LHS of a let or in the argument of a function definition *)
    (*Printf.printf "sube is non-func arg'\n";*)
    let* () = generate_type_conv typ1 typ2 in
    let* e1str = ocaml_of_exp e1 in
    let* typ1str = ocaml_of_typ typ1 in
    let* typ2str = ocaml_of_typ typ2 in
    return ("(Option.get (" ^ typ2str ^ "_of_" ^ typ1str ^ " " ^ e1str ^ "))")
  | CvtE (e1, typ1, typ2) ->
    let* e1str = ocaml_of_exp e1 in
    return ("(" ^ ocaml_of_numtyp typ2 ^ "_of_" ^ ocaml_of_numtyp typ1 ^ " " ^ e1str ^ ")")
  | OptE eo -> if (Option.is_none eo) then return "None" else
    let* eo_str = ocaml_of_exp (Option.get eo) in
    return ("(Some (" ^ eo_str ^ "))")
  | IdxE (e1, e2) ->
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("(List.nth " ^ e1str ^ " " ^ e2str ^ ")")
  | LenE e1 ->
    let* e1str = ocaml_of_exp e1 in
    return ("(List.length " ^ e1str ^ ")")
  | SliceE (e1, start, end_) ->
    let* e1str = ocaml_of_exp e1 in
    let* start_str = ocaml_of_exp start in
    let* end_str = ocaml_of_exp end_ in
    return ("(slice " ^ e1str ^ " " ^ start_str ^ " " ^ end_str ^ ")")
  | CatE (e1, e2) ->
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("(" ^ e1str ^ " @ " ^ e2str ^ ")")
  | MemE (e1, e2) -> (* todo this can also be a choice operator (?) *)
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("List.mem " ^ e1str ^ " " ^ e2str)
  | StrE strlist -> 
    let* recname = ocaml_of_typ ~consannot:true e.note in
    let* recordstr = concat_mapM ";\n  " (ocaml_of_expfield recname) strlist in
    return ("{\n  " ^ recordstr ^ "  }") 
  | DotE (e1, mixop) -> 
    let* e1str = ocaml_of_exp e1 in
    let* typeannot = ocaml_of_typ ~consannot:true e1.note in
    let mixopstr = (Util_ocaml.mixop_to_atom_str ~recordfield:true [[mixop]]) in 
    return (e1str ^ "." ^ mixopstr ^ "_" ^ typeannot)
  | UpdE (e1, p, e2) -> 
    let* e1str = ocaml_of_exp e1 in
    let flat_path = flatten_path p [] in 
    let rec build_update steppaths path_acc : string t =
    begin match steppaths with
    | [] -> ocaml_of_exp e2 
    | DotSP (atom, typname) :: rest ->
      let mixopstr = Util_ocaml.mixop_to_atom_str ~recordfield:true [[atom]] in
      let* typannot = ocaml_of_typ ~consannot:true typname in
      let* inner_update = build_update rest (path_acc ^ "." ^ mixopstr ^ "_" ^ typannot) in
      return ("{ " ^ path_acc ^ " with " ^ mixopstr ^ "_" ^ typannot ^ " = " ^ inner_update ^ " }")
    | IdxSP idexp :: rest ->
      let* idxtsr = ocaml_of_exp idexp in
      let* inner_update = build_update rest ("(List.nth " ^ path_acc ^ " " ^ idxtsr ^ ")") in
      return ("(update_at " ^ idxtsr ^ " " ^ inner_update ^ " " ^ path_acc ^ ")")
    | SliceSP (i, j) :: rest -> 
      let* startstr = ocaml_of_exp i in 
      let* endstr = ocaml_of_exp j in 
      let* inner_update = build_update rest ("(slice " ^ path_acc ^ startstr ^ " " ^ endstr ^ ")") in
      return ("(update_slice " ^ path_acc ^ " " ^ startstr ^ " " ^ endstr ^ " " ^ inner_update ^ ")")
    end in 
    build_update flat_path e1str
  | ExtE (e1, p, e2) -> 
    let* e1str = ocaml_of_exp e1 in
    let flat_path = flatten_path p [] in 
    let rec build_update steppaths path_acc : string t =
    begin match steppaths with
    | [] -> 
      let* e2str = ocaml_of_exp e2 in
      return (path_acc ^ " @ " ^ e2str)
    | DotSP (atom, typname) :: rest ->
      let mixopstr = Util_ocaml.mixop_to_atom_str ~recordfield:true [[atom]] in
      let* typannot = ocaml_of_typ ~consannot:true typname in
      let* inner_update = build_update rest (path_acc ^ "." ^ mixopstr ^ "_" ^ typannot) in 
      return ("{ " ^ path_acc ^ " with " ^ mixopstr ^ "_" ^ typannot ^ " = " ^ inner_update ^ " }")
    | IdxSP idexp :: rest -> 
      let* idxtsr = ocaml_of_exp idexp in 
      let* inner_update = build_update rest ("(List.nth " ^ idxtsr ^ " " ^ path_acc ^ ")") in
      return ("(update_at " ^ idxtsr ^ " " ^ inner_update ^ " " ^ path_acc ^ ")")
    | SliceSP (i, j) :: rest -> 
      let* startstr = ocaml_of_exp i in 
      let* endstr = ocaml_of_exp j in 
      let* inner_update = build_update rest ("(slice " ^ path_acc ^ startstr ^ " " ^ endstr ^ ")") in
      return ("(update_slice " ^ path_acc ^ " " ^ startstr ^ " " ^ endstr ^ " " ^ inner_update ^ ")")
    end in 
    build_update flat_path e1str
  | CompE (e1, e2) -> 
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    let* typename = ocaml_of_typ ~consannot:true e.note in
    return ("compose_" ^ typename ^ " (" ^ e1str ^ ") (" ^ e2str ^ ")")
  | LiftE e1 -> 
    let* e1str = ocaml_of_exp e1 in
    return ("(lift " ^ e1str ^ ")")
  | TheE e1 -> 
    let* e1str = ocaml_of_exp e1 in
    return ("(Option.get " ^ e1str ^ ")")

and ocaml_of_mixop mixop typnote : string t = 
  let* typcons = resolve_variant typnote in
  let* typname = ocaml_of_typ ~consannot:true (Option.get typcons) in
  let label =
    sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop)
  in
  return (label ^ "_" ^ typname)

(* an "uncase exp typcons" function will strip the typecons from the exp (a variant type). but each constructor can take a different number / type of arguments, meaning uncase_type will have different return types for each cons. so we have to generate a separate function for each cons. *)
and generate_uncase tcs typename : unit t =
  let* typevars = get_typevars () in 
  let typevarstr = String.concat " " (List.map (fun s -> "'" ^ s) (Set.to_list typevars)) in
  let gen_one (op, (_, typargs, _), _) : unit t =
    let cons =
      (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op)) ^ "_" ^ typename
    in
    let suffix = String.lowercase_ascii cons in
    let fname  = sanitize_name ("uncase_" ^ typename ^ "_" ^ suffix) in
    (* Figure out arg pattern + return expression shape for this constructor *)
    let numargs, pat_args, ret_expr = get_cons_args typargs in 
    let body =
      Printf.sprintf
        "let %s (arg : %s) =\n\
         \  match arg with\n\
         \  | %s %s -> %s\n"
        fname (append_sep typevarstr typename " ") cons pat_args ret_expr
    in
    if numargs <> 0 then tell body else return ()
  in
  (* Emit one function per constructor *)
  let* _ = mapM gen_one tcs in
  return ()

(* Get deftype from an alias *)
and lookup (typename : string) : deftyp option t =
  let* typdef = get_typedef typename in
  match typdef with
  | Some (TypeDef {it = (_, _, {it = InstD (_, _, dt); _}::_); _}) -> return (Some dt)
  | _ -> return None

(* Resolve a typ to a StructT fields if it denotes a record type.
   Follows aliases. *)
and resolve_struct (typname : typ) (toplvl : bool) : typfield list option t =
  match typname.it with
  | VarT (tid, _) -> 
    (* this should not work; lol *)
    let* typedef = lookup tid.it in begin
    match typedef with
    | Some dt ->
        begin match dt.it with
        | AliasT t' -> resolve_struct t' toplvl
        | StructT fields -> return (Some fields)
        | VariantT _ -> return None
        end
    | None -> return None
    end
  | IterT (_, iter) -> if toplvl then return None else begin 
    match iter with 
    | Opt -> return None 
    | _   -> return (Some [])
    end
  | _ -> return None

(* Follow aliases to resolve a variant type. 
    For example, if type A = alias B and B = CONS of <args>, then CONS is annotated with "B", i.e. we use CONS_B. Whenever type A is used, CONS should _still_ be annotated with B and not A, as A does not have its own constructors. *)
and resolve_variant (typname : typ) : typ option t =
  match typname.it with
  | VarT (tid, _) ->
    (*Printf.printf "Looking for typedef: %s\n" tid.it;*)
    let* typedef = lookup (sanitize_name tid.it) in begin
    match typedef with
    | Some dt ->
        begin match dt.it with
        | AliasT t' -> resolve_variant t'
        | StructT _ -> return None
        | VariantT _ -> return (Some typname)
        end
    | None -> (*Printf.printf "Type %s not found\n" tid.it;*) return None
    end
  | TupT et when List.length et = 1 -> return (Some typname)
  | BoolT -> (*Printf.printf "type is: booltype\n";*) return None
  | NumT _ -> (*Printf.printf "type is: numt\n";*) return None
  | TextT -> (*Printf.printf "type is: text\n";*) return None
  | TupT et -> (*Printf.printf "type is: tupt; len: %d\n" (List.length et);*) return None
  | IterT _ -> (*Printf.printf "type is: iter\n";*) return None

and is_composable tfs : bool t =
  match tfs with
  | (_, (_, inner_type, _), _) -> composable_typ inner_type

and composable_typ (t : typ) : bool t =
  match t.it with
  | IterT (_, iter) -> begin match iter with 
    | Opt -> return false | _ -> return true end
  | _ -> 
    let* tfs = resolve_struct t false in
    match tfs with 
    | Some fields -> allM is_composable fields
    | None -> return false

and typ_is_list (typname : typ) : bool t = 
  let* tfs = resolve_struct typname false in
  match tfs with 
  | Some [] -> return true
  | Some _ -> return false
  | None -> error typname.at "Non-composable type: shouldn't happen."

and build_fields (tfs : typfield list) typename : unit t = 
  (* Verify every field is composable *)
  let* composable = allM is_composable tfs in 
  if not composable then return () else
  let* fields = concat_mapM ";\n" (fun (a, (_, ft, _), _) ->
    let record = (Util_ocaml.mixop_to_atom_str ~recordfield:true [[a]]) in
    let fieldname = record ^ "_" ^ typename in  
    let* is_list = typ_is_list ft in 
    let* fieldtype = ocaml_of_typ ~consannot:true ft in 
    let rhs = if is_list then 
      Printf.sprintf "r1.%s @ r2.%s" fieldname fieldname
    else
      Printf.sprintf "compose_%s r1.%s r2.%s" fieldtype fieldname fieldname
    in
    return (Printf.sprintf "  %s = %s" fieldname rhs)) tfs
  in
  tell (Printf.sprintf "let compose_%s (r1 : %s) (r2 : %s) = {\n%s\n}" typename typename typename fields)

(* Assuming that the top-level is a struct. The nested fields may be lists or structs *)
and generate_compose (dt : deftyp) (typename : string) : unit t =
  match dt.it with
  | StructT tfs -> build_fields tfs typename
  | AliasT inner_type -> begin
    let* tfs = resolve_struct inner_type true in 
    match tfs with 
    | Some tfs' -> build_fields tfs' typename
    | None -> return ()
    end
  | VariantT _ -> return ()

and ocaml_of_expfield typename (a, e) : string t = 
  let* estr = ocaml_of_exp e in 
  return (Util_ocaml.mixop_to_atom_str ~recordfield:true [[a]] ^ "_" ^ typename ^ " = " ^ estr)

and ocaml_of_iter iter : string t =
  match iter with
    | Opt -> return "option"
    | List -> return "list"
    | List1 -> return "List1" (* TODO !!!! *)
    | ListN (e, id_opt) ->
      let* e_str = ocaml_of_exp e in
      let id_str =
        match id_opt with
        | Some id -> "Some " ^ "\"" ^ id.it ^ "\""  (* TODO or sanitize_name id *)
        | None -> "None"
      in
      return ("ListN (" ^ e_str ^ ", " ^ id_str ^ ")")

(* For a variant type type V = A | B ..., we annotate the constructors with the typename like A_V, B_V, etc (since OCaml type inference is not accurate with duplicate constructors). A constructor annotation does not need type arguments. todo: could probably rename to type annotation since we also use it in function definitions *)
and ocaml_of_typ ?(typearg=false) ?(consannot=false) (t : typ) : string t =
  match t.it with
  | VarT (id, args) -> (*Printf.printf "VarT: %s\n" id.it;*) let name = sanitize_name id.it in
    (*Printf.printf "consannot: %b\n" consannot;*)
    let* argstr = ocaml_of_args args ~typearg:true in
    let* is_typevar = is_typevar (sanitize_name id.it) in
    if is_typevar then return ("'" ^ name) 
    else if consannot then return name 
    else return (append_sep argstr name " ")
  | BoolT -> return "bool"
  | NumT numtype -> return (ocaml_of_numtyp numtype)
  | TextT -> return "string"
  | TupT ets -> if List.length ets = 0 then return "unit" else 
    concat_mapM " * " (ocaml_of_typbind ~typearg ~consannot) ets
  | IterT (t1, iter) -> 
    let* t1str = ocaml_of_typ ~typearg ~consannot t1 in
    let* iterstr = ocaml_of_iter iter in
    return (t1str ^ " " ^ iterstr)

(* TODO this is copied from print.ml I don't understand yet *)
and ocaml_of_typbind ?(typearg=false) ?(consannot=false) (e, t) =
  match e.it with
  | VarE {it = "_"; _} -> ocaml_of_typ ~typearg ~consannot t
  (*| _ -> let* estr = ocaml_of_exp e in
    let* tstr = ocaml_of_typ t in
    return (estr ^ " : " ^ tstr)*)
  | _ -> ocaml_of_typ ~typearg ~consannot t

(* funcdef/funcall refer to whether the argument is part of a function definition or function call. When _defining_ a function, an argument can only be a (possibly super/sub typed or cased) variable, but when calling functions, it can be any expr. We ignore dependent types for now so type variables in func calls/defs are ignored.
typearg refers to whether the arg is from a type declaration, like: "type x list", or type defintion, like: "type a = Cons of x" OR "type a = nat list". right now, we only support arguments that are types themselves (polymorphic types). we dont support an arg like "N: nat" (dependent types).
TODO: idk what a GramA arg is *)
and ocaml_of_arg ?(typearg=true) ?(funcdef=false) ?(funccall=false) a =
  match a.it with
  | ExpA e -> ocaml_of_exp ~typearg ~funcdef ~funccall e
  | TypA t -> if not (funccall || funcdef) then 
    ocaml_of_typ ~typearg t else return ""
  | DefA id -> return (sanitize_name id.it)
  | GramA g -> return ("TODO: gram in arg not supported")

and ocaml_of_args ?(typearg=true) ?(funcdef=false) ?(funccall=false) = function
  | [] -> return ""
  | as_ -> concat_mapM " " (ocaml_of_arg ~typearg ~funcdef ~funccall) as_

and ocaml_of_bool_binop = function
  | `AndOp -> "&&"
  | `OrOp -> "||"
  | `ImplOp -> "TODO: ImplOp"
  | `EquivOp -> "TODO: EquivOp"

and ocaml_of_num_binop ?(float=false) op =  
  let opstr = match op with
  | `AddOp -> "+"
  | `SubOp -> "-"
  | `MulOp -> "*"
  | `DivOp -> "/"
  | `ModOp -> "mod"
  | `PowOp -> "**"
  in 
  if float && opstr <> "mod" && opstr <> "**" then (opstr ^ ".") else opstr

and ocaml_of_binop ?(float=false) = function
  | #Bool.binop as op -> ocaml_of_bool_binop op
  | #Num.binop as op -> ocaml_of_num_binop ~float op

and ocaml_of_bool_unop = function
  | `NotOp -> "not"

and ocaml_of_unop = function
  | #Bool.unop as op -> ocaml_of_bool_unop op
  | #Num.unop as op -> Num.string_of_unop op

let get_idx_list (iterlist : (id * exp) list) id_opt region =
  let idx_str = match id_opt with
    | Some id -> id.it
    | None -> "(* TODO: no iterator variable *)"
  in
  let idx_list = List.filter (fun (id, _) -> id.it = idx_str) iterlist in
  match idx_list with 
  | [] -> return ""
  | [(_, e)] -> ocaml_of_exp e
  | _ -> error region ("Index variable " ^ idx_str ^  " can only occur once in binder list")

let gen_case_arm i e : string t = 
  match e.it with 
  | VarE _ -> return (Printf.sprintf "freshvar_%d" i)
  | SubE (e1, t1, t2) ->
      let* t1str = ocaml_of_typ t1 in
      let* t2str = ocaml_of_typ t2 in
      let* () = generate_type_conv t1 t2 in
      return (Printf.sprintf "(%s_of_%s freshvar_%d)" t1str t2str i)
  | _ -> return "(* TODO: LetPr LHS = CaseE(mixop, TupE es) where some e in es is not a combination of tuples, variables, subtypes or supertypes  *)"
let gen_case_arms e : string t = 
  match e.it with 
  | TupE es -> 
    let* retvalues = concat_mapMi ", " gen_case_arm es in
    return ("Some (" ^ retvalues ^ ")")
  | _ -> (*gen_case_arm 0 e*) error e.at "LetPr LHS CaseE(mixop, e) ill-formed: e must be a Tuple"

let rec ocaml_of_prems (prems : prem list) : string t =
  concat_mapM "\n"
  (function p -> match p.it with
    | LetPr (lhs, rhs, vars) ->
        let* () = add_knowns (List.map sanitize_name vars) in
        let* lhs_str = ocaml_of_exp lhs in
        (*Printf.printf "Generating LetPr with LHS: %s\n" lhs_str;*)
        let* rhs_str = ocaml_of_exp rhs in
        (*Printf.printf "Generating LetPr with RHS: %s\n" rhs_str;*)
        begin 
        match lhs.it with
        | VarE id ->
          return (Printf.sprintf "  let %s = %s in" lhs_str rhs_str)
        | CaseE (mixop, e) -> begin
          let let_lhs = match vars with
            | []   -> error p.at "LetPr with no bound vars: shouldn't happen"
            | [v]  -> v
            | vs   -> String.concat ", " vs
          in
          let newvararity = List.length vars in 
          let newvars, failcase = match newvararity with
            | 0 -> error p.at "LetPr with no bound vars: shouldn't happen"
            | 1 -> "freshvar_0", "None"
            | n -> "(" ^ (String.concat ", " (List.init n (fun i -> Printf.sprintf "freshvar_%d" i))) ^ ")", "None"
          in 
          let* rhstypcons = resolve_variant rhs.note in 
          let* rhstyp = ocaml_of_typ ~consannot:true (Option.get rhstypcons) in
          let mixopstr = (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop)) ^ "_" ^ rhstyp in
          let indent = "    " in 
          let* retvalues = gen_case_arms e in
          return (Printf.sprintf "  let* %s = match %s with\n%s| %s %s -> %s\n%s| _ -> %s\n  in" let_lhs rhs_str indent mixopstr newvars retvalues indent failcase)
          end
        | OptE (Some {it = VarE id; _}) -> 
          let lhs_str = sanitize_name id.it in 
          return (Printf.sprintf "  let* %s = %s in" lhs_str rhs_str)
        | IterE ({ it = VarE lhs_var; _ }, (Opt, xes)) -> begin
          match xes with 
          (* x?{x <- `x?`} = y; it looks like `x?` just takes the value of y - translating to `x? = y` for now. *)
          | [(varname, listname)] -> 
            let* liststr = ocaml_of_exp listname in 
            let* () = add_known liststr in
            return (Printf.sprintf "  let %s = %s in\n" liststr rhs_str)
            (*let vardef = Printf.sprintf "  let %s = Option.get %s in\n" (sanitize_name varname.it) rhs_str in
            let* liststr = ocaml_of_exp listname in 
            let outflow_def = Printf.sprintf "  let %s = Some %s in" liststr (sanitize_name varname.it) in 
            let* () = add_known liststr in 
            return (vardef ^ outflow_def)*)
          | _ -> return "(* TODO: LetPr LHS is IterOpt with multiple bindings *)"
          end
        | SubE (lhs', t1, t2) -> 
          let* () = generate_type_conv t2 t1 in 
          let* t1name = ocaml_of_typ t1 in
          let* t2name = ocaml_of_typ t2 in
          let* lhs_str = ocaml_of_exp lhs' in
          return (Printf.sprintf "  let* %s = %s_of_%s (%s) in" lhs_str t1name t2name rhs_str)
        | _ -> error p.at "LetPr ill-formed: LHS must be one of: variable, optional value/iterator, cased expression."
      end 
    | IfPr cond ->
        let* cond_str = ocaml_of_exp cond in
        return (Printf.sprintf "  if not (%s) then None else" cond_str)
    | RulePr _ -> return "(* TODO: RulePr *)"
    | ElsePr -> return ""
    | IterPr (prems, (iter, iterlist)) -> begin 
      (* if x* is known then x <- x* is an inflow.
        Otherwise, it is an outflow. *)
      let* prev_knowns = get_knowns in 
      (* any inner premise needs to know what the inflows are. these inflows will not affect the output of the `partition` function below and will be removed by the reset in the end before adding the outflows - they are only in scope for the inner premises. *)
      let inflows = List.map (fun (x, _) -> sanitize_name x.it) ((List.filter (fun (id, e) -> 
        Il.Free.Set.subset (Set.map sanitize_name (Valid.free_vars_exp e)) prev_knowns
      ) iterlist)) in
      let* () = add_knowns inflows in
      (* this will add new things to knowns, but their scope is limited *)
      let* prem_strs = ocaml_of_prems prems in
      let monadic = is_monadic prems in
      let* new_knowns = get_knowns in 
      let partition id_opt = 
        List.partition (fun (id', e) -> 
          match id_opt with 
          | Some id -> (Il.Free.Set.subset (Set.map sanitize_name (Valid.free_vars_exp e)) new_knowns) || (id.it = id'.it)
          | None -> (Il.Free.Set.subset (Set.map sanitize_name (Valid.free_vars_exp e)) new_knowns) 
      ) iterlist
      in 
      match iter with
      | Opt -> begin
        let inflows, outflows = partition None in 
        let inflow_vars = String.concat " " (List.map (fun (id, _) -> (sanitize_name id.it)) inflows) in
        let* inflow_lists = concat_mapM " " ocaml_of_exp (List.map snd inflows) in
        let inflow_lists = inflow_lists in
        let outflow_vars = String.concat ", " (List.map (fun (id, _) -> (sanitize_name id.it)) outflows) in
        let* outflow_lists = concat_mapM ", " ocaml_of_exp (List.map snd outflows) in
        (* reset knowns: whatever was added by the inner premises can now be removed *)
        let* () = set_knowns prev_knowns in
        (* now add whatever outflows *)
        let* outflow_listvars = mapM ocaml_of_exp (List.map snd outflows) in
        (*Printf.printf "Outflow list vars: %s\n" (String.concat ", " outflow_listvars);*)
        let* () = add_knowns outflow_listvars in
        if (List.length outflows) = 0 then 
          return "TODO: no outflows in iteropt"
        else 
          return (Printf.sprintf "  let %s = unzip_opt%d (map_opt%d (fun %s -> %s %s) %s) in" outflow_lists (List.length outflows) (List.length inflows) inflow_vars prem_strs outflow_vars inflow_lists) 
        end
      | List -> return "(* TODO: IterPr List *)"
      | List1 -> return "(* TODO: IterPr List1 *)"
      | ListN (e, id_opt) -> 
        let inflows, outflows = partition id_opt in 
        let* list_len = ocaml_of_exp e in
        let* idx_list = get_idx_list iterlist id_opt p.at in
        let* freshvar = get_freshvar () in
        let idx_listname = if idx_list = "" then (freshvar ^ "_list") else idx_list in
        let def_idx_list = Printf.sprintf "  let %s = List.init %s (fun i -> i) in\n" idx_listname list_len in
        (* TODO: all the if idx_list = "" checks are a bit hacky and maybe there is a way to generalise them 
        but if we consider the index variable to be an outflow, we will have to add it separately to "fun <inflows> -> ...", which is also annoying *)
        let idx_var, idx_listvar = if idx_list = "" then [freshvar], (freshvar ^ "_list ") else [], "" in
        let inflow_vars = String.concat " " (idx_var @ (List.map (fun (id, _) -> (sanitize_name id.it)) inflows)) in
        let* inflow_lists = concat_mapM " " ocaml_of_exp (List.map snd inflows) in
        let inflow_lists = idx_listvar ^ inflow_lists in 
        let outflow_vars = String.concat ", " (List.map (fun (id, _) -> (sanitize_name id.it)) outflows) in
        let* outflow_lists = concat_mapM ", " ocaml_of_exp (List.map snd outflows) in
        (* reset knowns: whatever was added by the inner premises can now be removed *)
        let* () = set_knowns prev_knowns in
        (* now add whatever outflows *)
        let* outflow_listvars = mapM ocaml_of_exp (List.map snd outflows) in
        (*Printf.printf "Outflow list vars: %s\n" (String.concat ", " outflow_listvars);*)
        let* () = add_knowns outflow_listvars in
        let inflowsize = if idx_list = "" then (List.length inflows + 1) else (List.length inflows) in
        if (List.length outflows) = 0 then 
          (* if there are no outflows, the nested premises must be "ifs" *)
          return (def_idx_list ^ Printf.sprintf "  let* () = map%d (fun %s -> %s Some ()) %s in" (List.length inflows) inflow_vars prem_strs inflow_lists)
        else if monadic then 
          return (def_idx_list ^ Printf.sprintf "  let* %s = unzip%dM (map%dM (fun %s -> %s Some (%s)) %s) in" outflow_lists (List.length outflows) (List.length inflows) inflow_vars prem_strs outflow_vars inflow_lists) 
        else
          return (def_idx_list ^ Printf.sprintf "  let %s = unzip%d (map%d (fun %s -> %s %s) %s) in" outflow_lists (List.length outflows) (List.length inflows) inflow_vars prem_strs outflow_vars inflow_lists) 
        end     
  ) prems

(* todo: the bracketing is possibly wrong, copied from print.ml *)
let ocaml_of_typ_args t =
  match t.it with
  | TupT [] -> return ""
  | TupT _ -> ocaml_of_typ ~typearg:true t
  | _ -> let* argstr = ocaml_of_typ ~typearg:true t in return ("(" ^ argstr ^ ")")

(* Hardcoded for now: i dont know how to deal with this
   without creating a cyclic dependency otherwise 
   & a lot of problems *)
let build_stepcases step = 
  let* instrs = get_typedef "instr" in 
  let (TypeDef {it = (_, _, {it = InstD (_, _, instrsdt); _}::_); _}) = Option.get instrs in
  let (VariantT instr_tcs) = instrsdt.it in
  concat_mapM "\n" (fun (op, (_, t, _), _) -> 
    let consname = sanitize_name ~typename:false (Util_ocaml.mixop_to_atom_str op) in 
    let funcname = sanitize_name (Printf.sprintf "Step_%s/%s" step consname) in
    let* is_defined = func_is_defined funcname in
    let* args = ocaml_of_typ_args t in
    let args_str = if args = "" then "" else " _" in 
    if is_defined then begin
      return (Printf.sprintf "  | %s_instr%s -> %s instrs" consname args_str funcname)
    end else 
      return (Printf.sprintf "  | %s_instr%s -> failwith \"%s not defined.\"" consname args_str funcname)
  ) instr_tcs

let build_dispatch step = 
  let* instr_cases = build_stepcases step in
  return ([Printf.sprintf
  "dispatch_step_%s instr instrs : (instr list) =\n\
  \  if (Builtin.use_step_%s instr) then match instr with \n%s\n\
  \  else failwith \"Instruction is not a %s instruction.\"\n"
  step step instr_cases step])

(* Each clause is it's own function *)
let ocaml_of_func_def (fdef : func_def) : string list t =
  let id, params, rettyp, clauses, _ = fdef.it in
  let name = sanitize_name id.it in
  let* () = add_funcdef name in
  let params' = List.filter rmv_nonexp params in
  let num_params = List.length params' in 
  let argslist = if num_params = 0 then "()" else 
  String.concat " " (List.init num_params (fun i -> Printf.sprintf "a%d" i)) in
  (* horrible way to do hardcoded things for now *)
  if (List.length clauses) = 0 then begin 
    match id.it with 
    | "Step_read_throw_ref_handler" -> 
      return [name ^ " = uc_step_read_slashthrow_ref\n"]
    (* URGENT change this when access to internet lol *)
    | "dispatch_step_pure" -> build_dispatch "pure"
    | "dispatch_step_read" -> build_dispatch "read"
    | _ -> return [name ^ " = Builtin." ^ name ^ "\n"]
  end else begin
  let typevars = typevars_of_params params in
  (*Printf.printf "defining func: %s\n" id.it;
  Set.iter (Printf.printf "%s\n") typevars;*)
  let* () = set_typevars (typevars_of_params params) in
  let* rettypstr = ocaml_of_typ rettyp in
  let* clause_funcs =
  mapMi (fun i clause ->
    match clause.it with
    | DefD (_, params, body, prems) ->
      (* reset knowns each time for different function *)
      (*Printf.printf "translating prems:\n";*)
      let* () = set_knowns (Set.empty) in
      let* prems_block = ocaml_of_prems prems in
      (*Printf.printf "translating ret value:\n";*)
      let* retvalue = ocaml_of_exp body in
      catchM
      (fun () -> 
        let num_params = List.length params in
        (*Printf.printf "translating args:\n";*)
        let* argnames = if num_params = 0 then return "()" else (ocaml_of_args ~typearg:false ~funcdef:true params) in
        let* typecasts = get_typecasts () in
        let* () = set_typecasts "" in
        (* debugging stuff remove later
        let debug = Printf.sprintf "Printf.printf \"calling clause_%s_%d\\n\";" name i in*)
        let bodycode = typecasts ^ prems_block in
        if bodycode = "" then
          return (Printf.sprintf "clause_%s_%d %s : (%s) option = Some (%s)\n" name i argnames rettypstr retvalue)
        else
          return (Printf.sprintf "clause_%s_%d %s : (%s) option =\n%s\n  Some (%s)\n" name i argnames rettypstr bodycode retvalue))
      (function 
      | CannotAnimate ->
        let argnames  = String.concat " " (List.init (List.length params) (fun i -> Printf.sprintf "unanimated%d" i)) in
        return (Printf.sprintf "clause_%s_%d %s = None\n" name i argnames)
      | e -> raise e)
  ) clauses
  in
  let* () = set_typevars (Set.empty) in
  let clause_calls =
  List.mapi
    (fun i _ ->
       if i = 0
       then Printf.sprintf "clause_%s_%d %s" name i argslist
       else Printf.sprintf "(fun () -> clause_%s_%d %s)" name i argslist)
    clauses
  in
  let clause_names = String.concat "\n  <|> " clause_calls in
  let main_func = (Printf.sprintf "%s %s =\n (%s) |> val_or_fail \"%s\"" name argslist clause_names name) in
  return (clause_funcs @ [main_func])
  end

(* ignoring the dependent type annotations for now *)
let ocaml_of_typcase typename (op, (_, t, _), _hints) =
  let* args_str = ocaml_of_typ_args t in
  if args_str = "" then
    return ((sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op)) ^ "_" ^ typename)
  else
    return ((sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op)) ^ "_" ^ typename ^ " of " ^ args_str)

(* all fields are annotated with "_typename" because OCaml cannot directly infer the type with record fields are duplicated across types *)
let ocaml_of_typfield name (atom, (_bs, t, _prems), _hints) =
  let* typ_str = ocaml_of_typ t in
  return (Util_ocaml.mixop_to_atom_str ~recordfield:true [[atom]] ^ "_" ^ name ^ ": " ^ typ_str)

let ocaml_of_deftyp dt name =
  let* () = generate_compose dt name in
  match dt.it with
  | AliasT t -> (*Printf.printf "alias type %s:\n" name;*) ocaml_of_typ t
  | StructT tfs ->
    let* tfs_str = concat_mapM ";\n  " (ocaml_of_typfield name) tfs in
    return ("{\n  " ^ tfs_str ^ "\n}")
  | VariantT tcs -> let* () = generate_uncase tcs name in
    let* tcs_str = concat_mapM "\n  | " (ocaml_of_typcase name) tcs in
    return ("\n  | " ^ tcs_str)

let ocaml_of_typedef (typedef : type_def) : string t =
  match typedef with
  | {it=(id, ps, insts); _} ->
    let* () = add_typedef (sanitize_name id.it) (TypeDef typedef) in
    (*Printf.printf "typedef: %s\n" id.it;*)
    let* () = set_typevars (typevars_of_params ps) in
    match insts with
    (* TODO: for now, we ignore all instances of a type except the first one *)
    | {it = InstD (_, as_, dt); _}::rest ->
      if List.length rest > 0 then
        Printf.printf "Warning: multiple instances of type %s found; only the first one will be translated.\n" id.it;
      let* args_str = ocaml_of_args ~typearg:true as_ in
      let space = if args_str = "" then "" else " " in
      let* dt_str = ocaml_of_deftyp dt (sanitize_name id.it) in
      let* () = set_typevars Set.empty in
      return (args_str ^ space ^ (sanitize_name id.it) ^ " = " ^ dt_str ^ "\n")
    | _ -> return ("(* TODO: no type instances: " ^ (sanitize_name id.it) ^ " = " ^ string_of_params ps ^ " " ^
    String.concat "\n" (List.map (string_of_inst id) insts) ^ "*)\n")

let ocaml_of_dl_def (def : dl_def) : (string * string) t =
  match def with
  | RuleDef rd  -> error rd.at "RuleDef found: should not happen"
  | TypeDef typedef -> let* typestr = ocaml_of_typedef typedef in 
    (* because we don't support multiple instances yet *)
    if String.length typestr >= 2 && String.sub typestr 0 2 = "(*" && String.sub typestr 8 7 <> "typearg" then
      return ("", typestr)
    else
      return ("", "type " ^ typestr)
  | FuncDef fdef -> 
    let* funcslist = ocaml_of_func_def fdef in 
    let funcstr = "let " ^ (String.concat "\nlet " funcslist) in
    let id, _, _, _, _ = fdef.it in
    return (funcstr ^ "\n", "")
  | RecDef dl_defs ->
    match dl_defs with
    | [] -> return ("", "")
    | (FuncDef _)::_ -> let fdefs = List.map (fun def -> match def with
        | FuncDef fdef -> fdef
        | _ -> error (get_dl_def_region def) "RecDef not consistent: should not happen"
      ) dl_defs in
      let* func_blocks = mapM ocaml_of_func_def fdefs in
      let func_strs = List.concat func_blocks in  
      if func_strs = [] then return ("", "") else
      (* hardcoded - we want "Steps" to redirect to "steps" immediately. defining it in another file will cause a cyclic dependency and we have to define it after "steps" is defined but before it is called *)
      let fdef = List.hd fdefs in
      let id, _, _, _, _ = fdef.it in
      let steps = if (sanitize_name id.it) = "steps" then " let uc_steps = steps\n" else "" in
      return ("let rec " ^ String.concat "\nand " func_strs ^ "\n" ^ steps, "")
    | (TypeDef _)::_ -> let typedefs = List.map (fun def -> match def with
        | TypeDef typedef -> typedef
        | _ -> error (get_dl_def_region def) "RecDef not consistent: should not happen"
      ) dl_defs in
      let* typestrs = concat_mapM "\nand " ocaml_of_typedef typedefs in
      if String.length typestrs >= 2 && String.sub typestrs 0 2 = "(*" then
        return ("", typestrs)
      else
        return ("", "type " ^ typestrs)
    | (RuleDef _)::_ -> error (get_dl_def_region def) "Recursive RuleDef: should not happen"

(* Not sure what the most efficient way of doing step/dispatches is for now.
Right now I try to match Zilin's spec so I need a string representation of instructions to be 
able to call the right step_(pure or read or table)/<instr_name> *)
let gen_instr_strs () = 
  let* instrs = get_typedef "instr" in 
  let (TypeDef {it = (_, _, {it = InstD (_, _, instrsdt); _}::_); _}) = Option.get instrs in
  let (VariantT instr_tcs) = instrsdt.it in
  let* cases = concat_mapM "\n" (fun (op, (_, t, _), _) -> 
    let consname = sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op) in 
    let* args = ocaml_of_typ_args t in
    let args_str = if args = "" then "" else " _" in 
    return (Printf.sprintf "| %s_instr%s -> \"%s\"" consname args_str consname)
  ) instr_tcs in
  tell (Printf.sprintf "let instr_to_string = function\n%s\n" cases)

let ocaml_of_dl_defs (defs : dl_def list) : (string * string) t =
  let* def_strs : (string * string) list = mapM ocaml_of_dl_def defs in
  let func_defs, type_defs = List.split def_strs in
  let func_str = concat_nonempty "\n" func_defs in
  let type_str = concat_nonempty "\n" type_defs in
  let* () = gen_instr_strs () in
  return (func_str, type_str)

let generate_ocaml (dl_defs : dl_def list) : string * string * string =
  let main =
    "open Backend_animation.Util_ocaml\n" ^
    "open Backend_animation.Util_ocaml.NumConversions\n\n" ^
    "let (<|>) = Backend_animation.Util_ocaml.mplus\n" ^
    "let (let*) = Option.bind\n"
  in
  let typeimports = "type nat = int\n" in
  let (funcdefs, typedefs), typeconvfuncs =
    eval (ocaml_of_dl_defs dl_defs) in
  (main ^ funcdefs), (typeimports ^ typedefs), typeconvfuncs
