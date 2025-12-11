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
exception CannotSplit of string 

(* This exception is raised when the OCaml generator sees a pattern that it does not expect (for example, if ruled out by validation) / unreachable code *) 
let error at msg = error at "OCaml CodeGen" msg

(* for error messages *)
let rec get_dl_def_region (dl_def : dl_def) : region =
  match dl_def with
  | FuncDef fd -> fd.at
  | TypeDef td -> td.at
  | RecDef (rd :: _) -> get_dl_def_region rd
  | RuleDef rd -> rd.at

(* type variables need to be prefixed with ' *)
let typevars_of_params (ps : param list) : Set.t =
  ps
  |> List.filter_map (fun p ->
       match p.it with
       | TypP id -> Some (sanitize_name id.it)
       | _ -> None)
  |> Set.of_list

(* generate a tuple of fresh variables for cased expressions *)
let fresh_tuple n : string =
  match n with
  | 0 -> "()"
  | 1 -> "freshvar_0"
  | n ->
      "(" ^ String.concat ", "
               (List.init n (fun i -> Printf.sprintf "freshvar_%d" i))
      ^ ")"

(* hardcoded things: `Step` needs to be re-defined manually to call `step`. This makes a group of functions (specifically those on any call path from `step` to `Step`) mutually recursive. Since these functions are not recursive in the original spec, we need to mark them as such manually. *)
let find_recdefs (funcdefs : dl_def list) = 
  Printf.printf "finding mutually recursive functions ...\n";
  flush stdout; 
  let visited = Hashtbl.create (List.length funcdefs) in
  let rec dfs visited start target = 
    Printf.printf "start is: %s\n" start;
    flush stdout; 
    let fdef = find_fdef funcdefs start in
    match Hashtbl.find_opt visited start with
    | Some children -> children 
    | None ->
      Hashtbl.add visited start Set.empty;
      (* if this call-path has reached `Step`, we can add to the recursive functions *)
      if start = target then begin 
        let s = Set.singleton start in
        Hashtbl.add visited start s;
        s
      end else begin
        Hashtbl.add visited start Set.empty; (* to avoid cycles *)
        let children = f_calls fdef in 
        let reachable = List.fold_left Set.union Set.empty (List.map (fun child -> dfs visited child target) (Set.to_list children)) in
        (* if `Step` is reachable from any of the children then it is reachable from `start` *)
        let result = 
          if Set.is_empty reachable then Set.empty
          else Set.add start reachable 
        in 
        Hashtbl.add visited start result;
        result end
  in
  dfs visited "step" "Step"

let hardcode_step (funcdefs : dl_def list) : dl_def list =
  Printf.printf "Hardcoding Step function...\n";
  flush stdout; 
  let rec_funcs = find_recdefs funcdefs in
  (* we need to insert the recursive functions at the same index we removed them from *)
  let index = -1 in 
  let rec mark idx acc rest recdefs = 
    match rest with 
    | [] -> acc, recdefs, idx
    | def :: rest' -> 
      begin match def with 
      | FuncDef {it = ({it=name;_}, _, _, _, _); _} ->
        if Set.mem name rec_funcs then
          let index = if index <> -1 then index else idx in 
          mark (idx+1) acc rest' (recdefs @ [def]) 
        else mark (idx+1) (acc @ [def]) rest' recdefs
      | _ -> mark (idx+1) (acc @ [def]) rest' recdefs
      end
  in
  let rest, recdefs, idx = mark 0 [] funcdefs [] in 
  (List.take idx rest) @ recdefs @ (List.drop idx rest)

(* TODOs: 
REFACTOR (always)
the above functions should be reused when the LHS of a let pr is case e
for now, add the flipsub flag everywehre but later figure if there is a better way to do it
do not import the typeM stuff above
the typecasts writer should be renamed, now it may also contain uncasings
known variables should be sanitized or NOT consistently 
change the casing stuff to be uncased in the argument itself not inside the func 
when generating the split or typecasts or uncasing we need to make the code generic so it can handle an arbitrary combination or nesting of these things *)

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
    | Some td -> td 
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
      if known then return acc else (Printf.printf "%s is unknown\n" (sanitize_name id'.it); return (id.it :: acc))
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
            Printf.sprintf "  | %s -> %s" (append_sep cons1 argstr " ") (append_sep cons2 argstr " ")
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
  let* () = add_funcdef funcname in
  let type_vars = List.init n (fun i -> String.make 1 Char.(chr (code 'a' + i))) in
  let tuple_ty = String.concat " * " (List.map (fun v -> "'" ^ v) type_vars) in
  let ret_ty = "'" ^ List.nth type_vars i in
  let xs = List.init n (fun i -> "x" ^ string_of_int (i+1)) in
  let pat = String.concat ", " xs in
  let body = List.nth xs i in
  tell (Printf.sprintf "let %s : %s -> %s = function\n  | %s -> %s\n"
    funcname tuple_ty ret_ty pat body)

let generate_type_conv (t1 : typ) (t2 : typ) : unit t =
  match t1.it, t2.it with
  | VarT (id1, _), VarT (id2, _) ->
    let lhs  = sanitize_name id1.it
    and rhs  = sanitize_name id2.it in
    let funcname = Printf.sprintf "%s_of_%s" rhs lhs in
    (*Printf.printf "generating %s:\n" funcname;*)
    let* is_defined = is_defined funcname in
    if is_defined then return () else begin
    let* () = add_funcdef funcname in
    let* type_defs = mapM (get_typedef) [lhs; rhs] in
    match type_defs with
    | [Some _lhs_def; Some _rhs_def] ->
      let func = Printf.sprintf "let %s_of_%s (arg : %s) : %s =\n  match arg with\n" rhs lhs lhs rhs in
      let arms = generate_type_arms lhs rhs _lhs_def.it _rhs_def.it in
      let failcase = "\n  | _ -> raise SubtypingFailed\n" in 
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
  let* () = add_funcdef funcname in
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

(* horrible way of flipping subtyping direction 
todo: check at which point we should pass all the flags *)
let rec ocaml_of_exp ?(typearg=false) ?(funcdef=false) ?(funccall=false) ?(flipsub=false) (e : exp) : string t =
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
       the function expects an arg of type t2 but casts it to a type t1 in the body. so we have to add "let e = t1_of_t2 arg" to make it typecheck *)
    let* freshvarname = get_freshvar () in
    let* () = generate_type_conv typ2 typ1 in
    let* e1str = match e1.it with
    | VarE id -> let* () = add_known id.it in return (sanitize_name ~typearg id.it)
    | _ -> error e1.at "Invalid supertype/subtype argument: expected a variable."
    in 
    let* typ1str = ocaml_of_typ typ1 in
    let* typ2str = ocaml_of_typ typ2 in
    let* () =  add_typecast ("  let " ^ e1str ^ " = " ^ typ1str ^ "_of_" ^ typ2str ^ " " ^ freshvarname ^ " in") in
    return (Printf.sprintf "(%s : %s)" freshvarname typ2str)
  | CaseE (mixop, e1) -> 
    (* todo: deal with nested cons - i think this should be fixed *)
    let* cased_vars, split = collect_vars e1 in
    let newvararity = List.length cased_vars in
    let lhsvars = if (newvararity = 0) then "()" else 
      (String.concat "," cased_vars)
    in
    let lhsvars' = if (newvararity = 0) then "" else 
      "(" ^ (String.concat "," cased_vars) ^ ")"
    in
    let* freshvar = get_freshvar () in
    let* mixopstr = ocaml_of_mixop mixop e.note in
    let* typannot = ocaml_of_typ e.note in
    let retvals = fresh_tuple newvararity in
    let mixopargs = if (newvararity = 0) then "" else retvals in 
    let uncasing = Printf.sprintf "  let* %s = match %s with\n  | %s -> Some %s\n  | _ -> None\n  in" lhsvars freshvar (append_sep mixopstr mixopargs " ") retvals in
    let uncasing' = Printf.sprintf "  let %s = %s in\n" (append_sep mixopstr lhsvars' " ") freshvar in
    (*let* () = add_typecast uncasing in*)
    let* () = add_typecast uncasing' in
    let* () = add_typecast split in
    return (Printf.sprintf "(%s : %s)" freshvar typannot)
  | CatE _ -> 
    let* freshvar = get_freshvar () in
    let* typannot = ocaml_of_typ e.note in
    let* split = split_arg e freshvar in
    let* () = add_typecast split in
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
    let* body_str = ocaml_of_exp ~flipsub e1 in
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
    (* Subtyping should not be refutable (I think) unless it appears on the LHS of a let or in the argument of a function definition
    this probably does not matter anymore since we use exceptions instead of options *)
    (*Printf.printf "subE is non-func arg'\n";*)
    let* () = if flipsub then generate_type_conv typ2 typ1 
    else generate_type_conv typ1 typ2 in
    let* e1str = ocaml_of_exp ~flipsub e1 in
    let* typ1str = ocaml_of_typ typ1 in
    let* typ2str = ocaml_of_typ typ2 in
    if flipsub then return ("(" ^ typ1str ^ "_of_" ^ typ2str ^ " " ^ e1str ^ ")") else 
    return ("(" ^ typ2str ^ "_of_" ^ typ1str ^ " " ^ e1str ^ ")")
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

(* a function argument may be an arbitrary concatenation of lists. it is possible to split a list if it is the right combination of length iterators and singleton lists (containing known element). for now we dont deal with length iterators and only split on known singleton lists. we also don't deal with lists of known elements of length greater than 1, e.g. [a;b;c], but these can be split into singletons anyway *)

(* removes all nested concatenations and returns a flattened list *)
and get_lists (e : exp) : exp list = 
  match e.it with 
  | ListE _ | IterE _ -> [e]
  | CatE (e1, e2) -> (get_lists e1) @ (get_lists e2)
  | _ -> 
    raise (CannotSplit (string_of_exp e))

(* finds the element we can split on, i.e., a singleton list with a known element for now. later this can include length iterators 
todo: use rev for efficiency *)
and get_anchor (es : exp list) : exp list * exp * exp list = 
  Printf.printf "Finding split anchor in list: %s\n" (String.concat "; " (List.map (fun e' -> Printf.sprintf "exp: %s;  at: %s\n" (string_of_exp e') (string_of_region e'.at)) es));
  let rec aux before after = 
    match after with 
    | [] -> raise (CannotSplit "no suitable split anchor found")
    | e::rest -> 
      match e.it with 
      | ListE [e1] ->
        (* this needs to be a cased expression or something we know!! but idk how to check that or quantify that right now *)
        begin match e1.it with 
        | CaseE _ -> Printf.printf "Found split anchor: %s\n" (string_of_exp e1); 
          before, e1, rest 
        | _ -> aux (before @ [e]) rest
        end
      | _ -> aux (before @ [e]) rest
  in aux [] es

and split_arg (e : exp) (name : string) : string t = 
  let es = get_lists e in 
  split_arg_helper es name

and split_arg_helper (es : exp list) (name : string) : string t =
  if (List.length es = 1) then 
    (* if we have only one element left, we don't need to split further *)
    let* () = add_known name in 
    (* if this is an iterator of the form <exp>{v <- v*} then we have to generate something of the form let v* = map1 (fun v -> exp) name *)
    match (List.hd es).it with 
    | IterE (body, (iter, bindings)) -> begin 
      match bindings with 
      | [(id, listname)] ->
        let* lhsstr = ocaml_of_exp listname in 
        Printf.printf "adding %s to knowns\n" lhsstr;
        let* () = add_known (sanitize_name lhsstr) in 
        let VarE listvar = listname.it in
        let rhsexp = {(List.hd es) with it = IterE (body, (iter, [(id, {listname with it = VarE {listvar with it = name}})]))} in 
        let* rhsstr = ocaml_of_exp rhsexp ~flipsub:true in
        return (Printf.sprintf "  let %s = %s in\n" lhsstr rhsstr)
      | _ -> failwith "Multiple Bindings in a split-argument"
      end
    | _ -> 
      let* expstr = ocaml_of_exp (List.hd es) in
      (* add the correct variable to known here and also fix "add_knowns" in general for weird concatenated args *)
      return (Printf.sprintf "  let %s = %s\n" expstr name)
  else if (List.length es = 0) then return "" else begin 
    let before, anchor, after = get_anchor es in
    let* beforevar = get_freshvar () in
    let* aftervar = get_freshvar () in
    (* this thing may need to be sanitized or we need to check its type *)
    let CaseE (mixop, _) = anchor.it in
    let split_suffix = sanitize_name (Util_ocaml.mixop_to_atom_str mixop) in
    let* anchorstr = ocaml_of_exp anchor in
    let splitanchor = Printf.sprintf "  let %s, %s, %s = split_on_%s %s in\n" beforevar anchorstr aftervar split_suffix name in
    let* () = generate_split_func split_suffix in 
    let* split_bfr = split_arg_helper before beforevar in
    let* split_aftr = split_arg_helper after aftervar in 
    return (splitanchor ^ split_bfr ^ split_aftr)
 end

(* use rev here to be more efficient (& and in every other list helper func) *)
and generate_split_func (s : string) : unit t =
  let funcname = Printf.sprintf "split_on_%s" s in 
  let* is_defined = is_defined funcname in
  if is_defined then return () else
  let* () = add_funcdef funcname in
  tell (Printf.sprintf 
    "let %s (lst : 'a list) : 'a list * 'a * 'a list =\n\
     \  let rec aux before after =\n\
     \    match after with\n\
     \    | [] -> raise (Match_failure (\"\", 0, 0))\n\
     \    | %s::rest -> before, %s, rest\n\
     \    | x::xs -> aux (before @ [x]) xs\n\
     \  in aux [] lst\n"
    funcname s s)

(* todo: add support for nested cons + add things to knowns correctly *)
(* if there is a concatenation inside a CaseE, we need to generate a split like we normally do, but it needs to occur AFTER the uncasing *)
and collect_vars (e : exp) : (string list * string) t = match e.it with 
  | VarE id -> 
    let* () = add_known id.it in 
    return ([sanitize_name id.it], "")
  | TupE es ->
      let rec go acc = function
        | [] -> return ((List.rev acc), "")
        | {it = VarE id; _} :: rest ->
            let* () = add_known id.it in
            go (sanitize_name id.it :: acc) rest
        | e1 :: rest -> 
          let* vars, split = collect_vars e1 in
          let* restvars, restsplit = go (vars @ acc) rest in 
          return (restvars, split ^ restsplit)
      in
      go [] es
  | CatE _ -> 
      let* freshvar = get_freshvar () in
      let* listsplits = split_arg e freshvar in
      return ([freshvar], listsplits)
  | _ -> raise CannotAnimate

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
  | Some {it = (_, _, {it = InstD (_, _, dt); _}::_); _} -> return (Some dt)
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
          (* this can fail and raise a Match Failure exception, which will be caught by the try_clauses function *)
          let let_lhs = String.concat ", " vars in
          let* rhstypcons = resolve_variant rhs.note in 
          let* rhstyp = ocaml_of_typ ~consannot:true (Option.get rhstypcons) in
          let mixopstr = (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop)) ^ "_" ^ rhstyp in
          let indent = "    " in 
          return (Printf.sprintf "  let %s (%s) = %s in" mixopstr let_lhs rhs_str)
          end
          (*let let_lhs = match vars with
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
          end*)
        | OptE (Some {it = VarE id; _}) -> 
          (* Option.get can raise (not sure?) Invalid_argument but this will be caught by the try_clauses function *)
          let lhs_str = sanitize_name id.it in 
          return (Printf.sprintf "  let %s = Option.get (%s) in" lhs_str rhs_str)
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
          return (Printf.sprintf "  let %s = %s_of_%s (%s) in" lhs_str t1name t2name rhs_str)
        | _ -> error p.at "LetPr ill-formed: LHS must be one of: variable, optional value/iterator, cased expression."
      end 
    | IfPr cond ->
        let* cond_str = ocaml_of_exp cond in
        return (Printf.sprintf "  if not (%s) then raise CondFailed else" cond_str)
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
          (* if there are no outflows, the nested premises must be "ifs" *)
          return (Printf.sprintf "  let _ = map_opt%d (fun %s -> %s ()) %s in" (List.length inflows) inflow_vars prem_strs inflow_lists)
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
          return (def_idx_list ^ Printf.sprintf "  let () = map%d (fun %s -> %s Some ()) %s in" (List.length inflows) inflow_vars prem_strs inflow_lists)
        (*else if monadic then 
          return (def_idx_list ^ Printf.sprintf "  let* %s = unzip%dM (map%dM (fun %s -> %s Some (%s)) %s) in" outflow_lists (List.length outflows) (List.length inflows) inflow_vars prem_strs outflow_vars inflow_lists)*)
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
   without creating a cyclic dependency & a lot of problems otherwise *)
let build_stepcases step = 
  let* instrs = get_typedef "instr" in 
  let {it = (_, _, {it = InstD (_, _, instrsdt); _}::_); _} = Option.get instrs in
  let (VariantT instr_tcs) = instrsdt.it in
  concat_mapM "\n" (fun (op, (_, t, _), _) -> 
    let consname = sanitize_name ~typename:false (Util_ocaml.mixop_to_atom_str op) in 
    let funcname = sanitize_name (Printf.sprintf "Step_%s/%s" step consname) in
    let* is_defined = is_defined funcname in
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
  let argslist' = if num_params = 0 then "" else 
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
  Printf.printf "defining func: %s\n" id.it;
  (*Set.iter (Printf.printf "%s\n") typevars;*)
  let* () = set_typevars (typevars_of_params params) in
  let* rettypstr = ocaml_of_typ rettyp in
  let* clause_funcs =
  mapMi (fun i clause ->
    match clause.it with
    | DefD (_, params, body, prems) ->
      (* reset knowns each time for different function *)
      let* () = set_knowns (Set.empty) in
      catchM
      (fun () -> 
        let num_params = List.length params in
        (*Printf.printf "translating args:\n";*)
        let* argnames = if num_params = 0 then return "()" else (ocaml_of_args ~typearg:false ~funcdef:true params) in
        (*Printf.printf "translating prems:\n";*)
        let* prems_block = ocaml_of_prems prems in
        (*Printf.printf "translating ret value:\n";*)
        let* retvalue = ocaml_of_exp body in
        let* typecasts = get_typecasts () in
        let* () = set_typecasts "" in
        (* debugging stuff remove later*)
        let debug = Printf.sprintf "  Printf.printf \"calling clause_%s_%d\\n\";" name i in
        let bodycode = debug ^ typecasts ^ prems_block in
        if bodycode = "" then
          return (Printf.sprintf "clause_%s_%d %s : %s = %s\n" name i argnames rettypstr retvalue)
        else
          return (Printf.sprintf "clause_%s_%d %s : %s =\n%s\n  %s\n" name i argnames rettypstr bodycode retvalue))
      (function 
      | CannotAnimate ->
        let argnames  = String.concat " " (List.init (List.length params) (fun i -> Printf.sprintf "unanimated%d" i)) in
        return (Printf.sprintf "clause_%s_%d %s = raise (UnanimatedArg \"%s\")\n" name i argnames name)
      | e -> raise e)
  ) clauses
  in
  let* () = set_typevars (Set.empty) in
  let clause_calls = List.mapi
    (fun i _ -> Printf.sprintf "clause_%s_%d" name i)
    clauses
  in
  let clause_names = String.concat ";\n  " clause_calls in
  let err_msg = "function: " ^ name in  
  let main_func = Printf.sprintf "%s %s = try_clauses_%d [\n  %s\n] %s \"%s\"" name argslist num_params clause_names argslist' err_msg in 
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
    let* () = add_typedef (sanitize_name id.it) typedef in
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

(* just for debugging - can remove later *)
let gen_instr_strs () = 
  let* instrs = get_typedef "instr" in 
  let {it = (_, _, {it = InstD (_, _, instrsdt); _}::_); _} = Option.get instrs in
  let (VariantT instr_tcs) = instrsdt.it in
  let* cases = concat_mapM "\n" (fun (op, (_, t, _), _) -> 
    let consname = sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op) in 
    let* args = ocaml_of_typ_args t in
    let args_str = if args = "" then "" else " _" in 
    return (Printf.sprintf "| %s_instr%s -> \"%s\"" consname args_str consname)
  ) instr_tcs in
  tell (Printf.sprintf "let instr_to_string = function\n%s\n" cases)

let ocaml_of_dl_defs (defs : dl_def list) : (string * string) t =
  Printf.printf "Calling hardcode step...\n";
  let processed_defs = hardcode_step defs in
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
