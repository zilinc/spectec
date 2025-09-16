open Il.Ast
open Il.Print
open Util.Source
open Xl
open Def
open Util_ocaml

module TypeM   = Util_ocaml.TypeM
module TypeMap = Util_ocaml.TypeMap
open TypeM

(* TODO: change this to use Error module *)
exception CodegenError of string
exception CannotAnimate of string

(* messy as of now *)
type step_path =
  | RootSP
  | IdxSP of exp
  | SliceSP of exp * exp
  | DotSP of atom

let rec flatten_path (p : path) (acc : step_path list) : step_path list =
  match p.it with
  | RootP -> acc 
  | IdxP (p, e) -> flatten_path p (IdxSP e :: acc)
  | SliceP (p1, e1, e2) -> flatten_path p1 (SliceSP (e1, e2) :: acc)
  | DotP (p, atom) -> flatten_path p (DotSP atom :: acc)

(* not sure if this is even necessary *)
let rec check_eq_typs t1 t2 =
  match t1.it, t2.it with
  | VarT (id1, _), VarT (id2, _) -> id1.it = id2.it
  | BoolT, BoolT -> true
  | NumT _, NumT _ -> true (*TODO: implement *)
  | TextT, TextT -> true
  | TupT ets1, TupT ets2 ->
    List.length ets1 = List.length ets2 &&
    List.for_all2 (fun (e1, t1) (e2, t2) -> e1.it = e2.it && check_eq_typs t1 t2) ets1 ets2
  | IterT (t11, iter1), IterT (t21, iter2) ->
    check_eq_typs t11 t21 && iter1 = iter2
  | _ -> false

let get_common_consts tcs1 tcs2 =
  let consts1 = List.map (fun (op, (_, t, _), _) -> (Util_ocaml.mixop_to_atom_str op, t)) tcs1 in
  let consts2 = List.map (fun (op, (_, t, _), _) -> (Util_ocaml.mixop_to_atom_str op, t)) tcs2 in
  (* TODO: do i even need this *)
  List.filter (fun c ->
    List.exists (fun c2 -> fst c = fst c2 && check_eq_typs (snd c) (snd c2)) consts2
  ) consts1

let ocaml_of_numtyp = Num.string_of_typ

let generate_type_arms td1 td2 =
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
          List.map (fun (consname, _) ->
            let cons = (sanitize_name ~typecons:true ~typename:false consname) in
            Printf.sprintf "  | %s args -> Some (%s args)" cons cons
          ) common_consts in
        String.concat "\n" arms ^ "\n  | _ -> None\n"
      | _ -> "TODO: non-variant type conversion not implemented yet" in
      arms
  else
    "TODO: multiple insts in type conversion not implemented yet"

let typedef_of_dl_def (def : dl_def option) : type_def option =
  match def with
  | Some (TypeDef td) -> Some td
  | _ -> None

let generate_type_conv (t1 : typ) (t2 : typ) : unit t =
  let* st = get in
  match t1.it, t2.it with
  | VarT (id1, _), VarT (id2, _) ->
      let lhs  = sanitize_name id1.it
      and rhs  = sanitize_name id2.it in
      let funcname = Printf.sprintf "%s_of_%s" rhs lhs in
      let* is_defined = is_defined funcname in
      if is_defined then return () else begin
      let* () = add_func funcname in
      let td1  = typedef_of_dl_def (TypeMap.find_opt lhs st.typemap)
      and td2  = typedef_of_dl_def (TypeMap.find_opt rhs st.typemap) in
      match td1, td2 with
      | Some _lhs_def, Some _rhs_def ->
          let func = Printf.sprintf "let %s_of_%s (arg : %s) : %s =\n  match arg with\n" rhs lhs lhs rhs in
          let arms = generate_type_arms _lhs_def.it _rhs_def.it in
          tell (func ^ arms)
      | _ -> raise (CodegenError (Printf.sprintf "error: types %s and %s not defined\n" lhs rhs))
      end
  | _ -> tell "TODO: type conversion not implemented yet\n"


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

let rec ocaml_of_exp ?(typearg=false) ?(is_arg=false) (e : exp) : string t =
  (* function or type arguments must be variables *)
  if is_arg then begin match e.it with 
  | VarE id -> return (sanitize_name ~typearg id.it)
  | _ -> raise (CannotAnimate "non-variable arguments")
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
    let* args' = ocaml_of_args ~typearg args in
    return (fname ^ " " ^ args')
  | CaseE (mixop, e1) ->
    let label = sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop) in
    let* e1str = ocaml_of_exp e1 in
    return (append_sep label e1str " ")
  | BinE (op, _, e1, e2) ->
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("(" ^ e1str ^ " " ^ ocaml_of_binop op ^ " " ^ e2str ^ ")")
  | UnE (op, _, e1) ->
    let* e1str = ocaml_of_exp e1 in
    return (ocaml_of_unop op ^ "(" ^ e1str ^ ")")
  | UncaseE (e, mixop) -> let* expstr = ocaml_of_exp e in
    let mixopstr = sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop) in 
    return ("uncase (" ^ expstr ^ ") (" ^ mixopstr ^ ")")
  | ProjE (e, n) -> let* expstr = ocaml_of_exp e in
    return ("(proj (" ^ expstr ^ ") " ^ string_of_int n ^ ")")
  | CmpE (op, _, e1, e2) ->
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("(" ^ e1str ^ " " ^ ocaml_of_cmpop op ^ " " ^ e2str ^ ")")
  | IterE (e1, (iter, bindings)) ->
    (* TODO: assuming that we always INFLOW, change later
    also needs to be more general *)
    begin
    match bindings with
    | [(id, e)] ->
      let* body_str = ocaml_of_exp e1 in
      let* list_name = ocaml_of_exp e in
      return (Printf.sprintf "(List.map (fun %s -> %s) %s)" (sanitize_name id.it) body_str list_name)
    | [] -> 
      let* body_str = ocaml_of_exp e1 in
      begin match iter with 
      | ListN (e, optid) ->
        let* lenstr = ocaml_of_exp e in
        let idstr = match optid with
          | Some id -> sanitize_name id.it
          | None -> "_"
        in
        return ("List.init (" ^ lenstr ^ ") (fun " ^ idstr ^ " -> " ^ body_str ^ ")")
      | _ -> return "(* TODO: IterE with no bindings and non-length iterator *)"
      end 
    | _ -> return "(* TODO: IterE with multiple bindings *)" 
    end
  | SupE (e1, typ1, typ2) | SubE (e1, typ1, typ2) ->
    let* () = generate_type_conv typ1 typ2 in
    let* e1str = ocaml_of_exp e1 in
    let* typ1str = ocaml_of_typ typ1 in
    let* typ2str = ocaml_of_typ typ2 in
    return (typ1str ^ "_of_" ^ typ2str ^ " (" ^ e1str ^ ")")
  | CvtE (e1, typ1, typ2) ->
    let* e1str = ocaml_of_exp e1 in
    return (ocaml_of_numtyp typ1 ^ "_of_" ^ ocaml_of_numtyp typ2 ^ " (" ^ e1str ^ ")")
  | OptE eo -> if (Option.is_none eo) then return "None" else
    let* eo_str = ocaml_of_exp (Option.get eo) in
    return ("Some (" ^ eo_str ^ ")")
  | IdxE (e1, e2) ->
    let* e1str = ocaml_of_exp e1 in
    let* e2str = ocaml_of_exp e2 in
    return ("List.nth_opt " ^ e1str ^ " " ^ e2str)
  | LenE e1 ->
    let* e1str = ocaml_of_exp e1 in
    return ("List.length (" ^ e1str ^ ")")
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
    let* recordstr = concat_mapM ";\n  " ocaml_of_expfield strlist in
    return ("{\n  " ^ recordstr ^ "  }") 
  | DotE (e1, mixop) -> 
    let* e1str = ocaml_of_exp e1 in
    let mixopstr = (Util_ocaml.mixop_to_atom_str ~recordfield:true [[mixop]]) in 
    return (e1str ^ "." ^ mixopstr)
  | UpdE (e1, p, e2) -> 
    let* e1str = ocaml_of_exp e1 in
    let flat_path = flatten_path p [] in 
    let rec build_update steppaths path_acc : string t =
    begin match steppaths with
    | [] -> ocaml_of_exp e2 
    | DotSP atom :: rest ->
      let mixopstr = Util_ocaml.mixop_to_atom_str ~recordfield:true [[atom]] in
      let* inner_update = build_update rest (path_acc ^ "." ^ mixopstr) in 
      return ("{ " ^ path_acc ^ " with " ^ mixopstr ^ " = " ^ inner_update ^ " }")
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
  | ExtE (e1, p, e2) -> 
    let* e1str = ocaml_of_exp e1 in
    let flat_path = flatten_path p [] in 
    let rec build_update steppaths path_acc : string t =
    begin match steppaths with
    | [] -> 
      let* e2str = ocaml_of_exp e2 in
      return (path_acc ^ e2str)
    | DotSP atom :: rest ->
      let mixopstr = Util_ocaml.mixop_to_atom_str ~recordfield:true [[atom]] in
      let* inner_update = build_update rest (path_acc ^ "." ^ mixopstr) in 
      return ("{ " ^ path_acc ^ " with " ^ mixopstr ^ " = " ^ inner_update ^ " }")
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
  | _ -> return "TODO: other expressions not supported yet"

(* an "uncase exp typcons" function will strip the typecons from the exp (a variant type) *)
and generate_uncase tcs typename : unit t =
  let funcstart = "let uncase_" ^ typename ^ " arg1 arg2 =\n  match arg1, arg2 with\n" in
  let rec gen_match_arms acc tcs = 
    match tcs with 
    | [] -> acc 
    | (op, (_, typargs, _), _) :: rest -> 
      let opstr = sanitize_name ~typecons:true (Util_ocaml.mixop_to_atom_str op) in
      let numargs = begin match typargs.it with 
      | VarT _ | NumT _ | IterT _  | BoolT  | TextT -> 1
      | TupT typarglist -> List.length typarglist
      end in 
      let arglist = List.init numargs (fun i -> "fv_" ^ string_of_int (i)) |> (String.concat ", ") in
      let matcharm = "  | " ^ opstr ^ " (" ^ arglist ^ "), \"" ^ opstr ^ "\" -> Some (" ^ arglist ^ ")\n" in
      gen_match_arms (acc ^ matcharm) rest
  in 
  let matcharms = gen_match_arms "" tcs in 
  if matcharms = "" then return () else
  let nonearm = "  | _ -> None" in 
  tell (funcstart ^ matcharms ^ nonearm)

and ocaml_of_expfield (a, e) : string t = 
  let* estr = ocaml_of_exp e in 
  return (Util_ocaml.mixop_to_atom_str ~recordfield:true [[a]] ^ " = " ^ estr)

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

(* TODO im not sure if the iterator exp can have type conversions *)
and ocaml_of_typ (t : typ) : string t =
  match t.it with
  | VarT (id, _) -> return (sanitize_name id.it)
  | BoolT -> return "bool"
  | NumT numtype -> return (ocaml_of_numtyp numtype)
  | TextT -> return "string"
  | TupT ets ->
    concat_mapM " * " ocaml_of_typbind ets
  | IterT (t1, iter) ->
    let* t1str = ocaml_of_typ t1 in
    let* iterstr = ocaml_of_iter iter in
    return (t1str ^ " " ^ iterstr)

(* this is copied from print.ml I don't understand yet *)
and ocaml_of_typbind (e, t) =
  match e.it with
  | VarE {it = "_"; _} -> ocaml_of_typ t
  (*| _ -> let* estr = ocaml_of_exp e in
    let* tstr = ocaml_of_typ t in
    return (estr ^ " : " ^ tstr)*)
  | _ -> ocaml_of_typ t
and ocaml_of_arg ?(typearg=true) ?(is_arg=false) a =
  match a.it with
  | ExpA e -> ocaml_of_exp ~typearg ~is_arg e
  | TypA t -> let* typstr = ocaml_of_typ t in
    if typearg then return ("'" ^ typstr) else return ""
  | DefA id -> return (sanitize_name ~typearg:false id.it)
  | GramA g -> return ("TODO: grammar in arg not supported")

and ocaml_of_args ?(typearg=true) ?(is_arg=false) = function
  | [] -> return ""
  | as_ -> concat_mapM " " (ocaml_of_arg ~typearg ~is_arg) as_

and ocaml_of_bool_binop = function
  | `AndOp -> "&&"
  | `OrOp -> "||"
  | `ImplOp -> "TODO: ImplOp"
  | `EquivOp -> "TODO: EquivOp"

and ocaml_of_num_binop = function
  | `AddOp -> "+"
  | `SubOp -> "-"
  | `MulOp -> "*"
  | `DivOp -> "/"
  | `ModOp -> "mod"
  | `PowOp -> "**"

and ocaml_of_binop = function
  | #Bool.binop as op -> ocaml_of_bool_binop op
  | #Num.binop as op -> ocaml_of_num_binop op

and ocaml_of_bool_unop = function
  | `NotOp -> "not"

and ocaml_of_unop = function
  | #Bool.unop as op -> ocaml_of_bool_unop op
  | #Num.unop as op -> Num.string_of_unop op

(* don't think this is used anymore *)
let rec get_bound_vars (prems : prem' phrase list) : string list = 
  List.fold_left (fun acc p ->
    match p.it with
    | LetPr (lhs, _, vars) ->
      (match lhs.it with
      | VarE id -> id.it :: acc
      | _ -> acc) (* LHS must be a variable *)
    | IterPr (prems, (iter, iterlist)) -> 
      (* The outflows of a nested premise are also "known" *)
      let from_prems = get_bound_vars prems in
      (* In length iterators i <- i*, the length 'i*' also outflows *)
      let len_iter = begin 
      match iter with
        | ListN (_, id_opt) -> (match id_opt with
          | Some id -> [id.it]
          | None -> [])
        | _ -> []
      end in
      let outflows : (id * exp) list =
        List.filter (fun (x, _) -> List.mem x.it (from_prems @ len_iter)) iterlist in
      let outflow_vars = List.map (
        fun (_, e) -> match e.it with
        | VarE id -> id.it
        | _ -> raise (CodegenError "Outflow iterator is not a variable")
      ) outflows in
      (outflow_vars @ acc) 
    | _ -> acc
  ) [] prems

let get_idx_list (iterlist : (id * exp) list) id_opt =
  let idx_str = match id_opt with
    | Some id -> id.it
    | None -> "(* TODO: no iterator variable *)"
  in
  let idx_list = List.filter (fun (id, _) -> id.it = idx_str) iterlist in
  match idx_list with 
  | [] -> return ""
  | [(_, e)] -> ocaml_of_exp e
  | _ -> raise (CodegenError ("Improper use of index variable " ^ idx_str ^  " in iterator list: Shouldn't happen."))

let gen_case_arm i e : string t = 
  match e.it with 
  | VarE _ -> return (Printf.sprintf "Some freshvar_%d" i)
  | SubE (e1, t1, t2) | SupE (e1, t1, t2) -> 
      let* t1str = ocaml_of_typ t1 in
      let* t2str = ocaml_of_typ t2 in
      let* () = generate_type_conv t1 t2 in
      return (Printf.sprintf "(%s_of_%s freshvar_%d)" t1str t2str i)
  | _ -> return "(* TODO: LetPr LHS = CaseE(mixop, e) where e is not some combination of tuples, variables, subtypes or supertypes  *)"
let gen_case_arms e : string t = 
  match e.it with 
  | TupE es -> concat_mapMi ", " gen_case_arm es 
  | _ -> gen_case_arm 0 e 

let rec ocaml_of_prems (prems : prem list) : string t =
  concat_mapM "\n"
  (function p -> match p.it with
    | LetPr (lhs, rhs, vars) ->
        let* lhs_str = ocaml_of_exp lhs in
        let* rhs_str = ocaml_of_exp rhs in
        begin 
        match lhs.it with
          | VarE id -> begin 
            let* () = add_known id.it in 
            return (Printf.sprintf "  let* %s = %s in" lhs_str rhs_str)
          end
          | CaseE (mixop, e) -> begin
            let let_lhs = match vars with
              | []   -> raise (CodegenError "LetPr with no bound vars: shouldn't happen")
              | [v]  -> v
              | vs   -> String.concat ", " vs
            in
            let newvararity = List.length vars in 
            let newvars, failcase = match newvararity with
              | 0 -> raise (CodegenError "LetPr with no bound vars: shouldn't happen")
              | 1 -> "freshvar_0", "None"
              | n -> "(" ^ (String.concat ", " (List.init n (fun i -> Printf.sprintf "freshvar_%d" i))) ^ ")", (String.concat ", " (List.init n (fun _ -> "None")))
            in 
            let mixopstr = (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str mixop)) in
            let indent = "    " in 
            let* retvalues = gen_case_arms e in
            return (Printf.sprintf "  let* %s = match %s with\n%s| %s %s -> %s\n%s| _ -> %s\n  in" let_lhs rhs_str indent mixopstr newvars retvalues indent failcase)
            end
          | _ -> return "(* TODO: LetPr where LHS is not a variable or CaseE *)"
        end 
    | IfPr cond ->
        let* cond_str = ocaml_of_exp cond in
        return (Printf.sprintf "  if not (%s) then None else" cond_str)
    | RulePr _ -> return "(* TODO: RulePr *)"
    | ElsePr -> return ""
    | IterPr (prems, (iter, iterlist)) -> match iter with
      | Opt -> return "(* TODO: IterPr Opt *)"
      | List -> return "(* TODO: IterPr List *)"
      | List1 -> return "(* TODO: IterPr List1 *)"
      | ListN (e, id_opt) -> 
        (* if x* is known then x <- x* is an inflow.
         Otherwise, it is an outflow. *)
        (* maybe there is a better way to do this *)
        let* prev_knowns = get_knowns in 
        let inflows, outflows = 
          List.partition (fun (id', e) -> 
            match id_opt with 
            | Some id -> (Il.Free.Set.subset prev_knowns (Valid.free_vars_exp e)) || (id.it = id'.it)
            | None -> (Il.Free.Set.subset prev_knowns (Valid.free_vars_exp e)) 
        ) iterlist
        in 
        (* this will add new things to knowns, but their scope is limited *)
        let* prem_strs = ocaml_of_prems prems in
        let* list_len = ocaml_of_exp e in
        let* idx_list = get_idx_list iterlist id_opt in
        let idx_listname = if idx_list = "" then "freshidxlist" else idx_list in
        let def_idx_list = Printf.sprintf "  let %s = List.init %s (fun i -> i) in\n" idx_listname list_len in
        (* TODO: all the if idx_list = "" checks are a bit hacky and maybe there is a way to generalise them 
        but if we consider the index variable to be an outflow, we will have to add it separately to "fun <inflows> -> ...", which is also annoying *)
        let idx_var, idx_listvar = if idx_list = "" then ["freshidxvar"], "freshidxlist " else [], "" in
        let inflow_vars = String.concat " " (idx_var @ (List.map (fun (id, _) -> (sanitize_name id.it)) inflows)) in
        let* inflow_lists = concat_mapM " " ocaml_of_exp (List.map snd inflows) in
        let inflow_lists = idx_listvar ^ inflow_lists in 
        let outflow_vars = String.concat ", " (List.map (fun (id, _) -> (sanitize_name id.it)) outflows) in
        let* outflow_lists = concat_mapM ", " ocaml_of_exp (List.map snd outflows) in
        (* reset knowns: whatever was added by the inner premises can now be removed *)
        let* () = set_knowns prev_knowns in
        (* now add whatever outflows *)
        let* outflow_listvars = mapM ocaml_of_exp (List.map snd outflows) in
        let* () = add_knowns outflow_listvars in
        let inflowsize = if idx_list = "" then (List.length inflows + 1) else (List.length inflows) in
        if (List.length outflows) = 0 then 
          (* if there are no outflows, the nested premises must be "ifs" *)
          return (def_idx_list ^ Printf.sprintf "  let* () = map%d (fun %s -> %s Some ()) %s in" (List.length inflows) inflow_vars prem_strs inflow_lists)
        else 
          return (def_idx_list ^ Printf.sprintf "  let %s = unzip%d (map%d (fun %s -> %s %s) %s) in" outflow_lists (List.length outflows) (List.length inflows) inflow_vars prem_strs outflow_vars inflow_lists)

        (*let* out_flows_strs = concat_mapM ", " (fun (_, e) -> 
        let* e = ocaml_of_exp e in return ("(" ^ e ^ ")")) out_flows in*) 


      (*let* prem_strs = ocaml_of_prems prems in
      let bound_iters = get_bound_vars prems in
      (* if we have "let n = ..." in our premises,
         then n <- n* is an outflow. Otherwise, it is an inflow. *)
      let outflows, inflows =
        List.partition (fun (x, _) -> List.mem x.it bound_iters) iterlist in*)
          
  ) prems

(* todo: the bracketing is possibly wrong *)
let ocaml_of_typ_args t =
  match t.it with
  | TupT [] -> return ""
  | TupT _ -> ocaml_of_typ t
  | _ -> let* argstr = ocaml_of_typ t in return ("(" ^ argstr ^ ")")

(* Each clause is it's own function *)
let ocaml_of_func_def (fdef : func_def) : string list t =
  let id, params, _, clauses, _ = fdef.it in
  if (List.length clauses) = 0 then return [] else begin
  let argslist = String.concat " " (List.init (List.length params) (fun i -> Printf.sprintf "a%d" i)) in
  let name = sanitize_name id.it in
  let* clause_funcs =
  mapMi (fun i clause ->
    match clause.it with
    | DefD (_, params, body, prems) ->
      let* prems_block = ocaml_of_prems prems in
      let* bodycode = ocaml_of_exp body in
      catchM
      (fun () -> 
        let* argnames = ocaml_of_args ~typearg:false ~is_arg:true params in
        return (Printf.sprintf "clause_%s_%d %s =\n%s\n  Some (%s)\n" name i argnames prems_block bodycode))
      (function 
      | CannotAnimate _ ->
        let argnames  = String.concat " " (List.init (List.length params) (fun i -> Printf.sprintf "unanimated%d" i)) in
        return (Printf.sprintf "clause_%s_%d %s = None\n" name i argnames)
      | e -> raise e)
  ) clauses
  in
  let clause_names =
  String.concat "\n  <|> " (List.mapi (fun i _ -> Printf.sprintf "clause_%s_%d %s" name i argslist) clauses)
  in
  let main_func = (Printf.sprintf "%s %s =\n  %s |> Option.value 
  ~default:(failwith \"No matching clause\")\n" name argslist clause_names) in
  return (clause_funcs @ [main_func])
  end

(* ignoring the dependent type annotations for now *)
let ocaml_of_typcase (op, (_, t, _), _hints) =
  let* args_str = ocaml_of_typ_args t in
  if args_str = "" then
    return (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op))
  else
    return (sanitize_name ~typecons:true ~typename:false (Util_ocaml.mixop_to_atom_str op) ^ " of " ^ args_str)

let ocaml_of_typfield (atom, (_bs, t, _prems), _hints) =
  let* typ_str = ocaml_of_typ t in
  return (Util_ocaml.mixop_to_atom_str ~recordfield:true [[atom]] ^ ": " ^ typ_str)

let ocaml_of_deftyp dt name =
  match dt.it with
  | AliasT t -> ocaml_of_typ t
  | StructT tfs ->
    let* tfs_str = concat_mapM ";\n " ocaml_of_typfield tfs in
    return ("{\n  " ^ tfs_str ^ "\n}")
  | VariantT tcs -> let* () = generate_uncase tcs name in 
    let* tcs_str = concat_mapM "\n  | " ocaml_of_typcase tcs in
    return ("\n  | " ^ tcs_str)

let ocaml_of_typedef (typedef : type_def) : string t =
  match typedef with
  | {it=(id, ps, insts); _} ->
    let* st = get in
    let* () = put {st with typemap = TypeMap.add (sanitize_name id.it) (TypeDef typedef) st.typemap} in
    match insts with
    | [ {it = InstD (_, as_, dt); _} ] ->
      let* st = get in
      let* () = put {st with typemap = TypeMap.add (sanitize_name id.it) (TypeDef typedef) st.typemap} in
      let* args_str = ocaml_of_args ~typearg:true as_ in
      let space = if args_str = "" then "" else " " in
      let* dt_str = ocaml_of_deftyp dt (sanitize_name id.it) in
      return (args_str ^ space ^ (sanitize_name id.it) ^ " = " ^ dt_str ^ "\n")
    | _ -> return ("(* TODO: MULTIPLE INSTANCE TYPE: \n type " ^ (sanitize_name id.it) ^ " = " ^ string_of_params ps ^ " " ^
    String.concat "\n" (List.map (string_of_inst id) insts) ^ "*)\n")

let ocaml_of_dl_def (def : dl_def) : (string * string) t =
  match def with
  | RuleDef _  -> raise (CodegenError "RuleDef: should not happen")
  | TypeDef typedef -> let* typestr = ocaml_of_typedef typedef in 
    (* because we don't support multiple instances yet *)
    if String.length typestr >= 2 && String.sub typestr 0 2 = "(*" then
      return ("", typestr)
    else
      return ("", "type " ^ typestr)
  | FuncDef fdef -> 
    let* funcslist = ocaml_of_func_def fdef in 
    if funcslist = [] then return ("", "") else
    (let funcstr = "let " ^ (String.concat "\nlet " funcslist) in
    return (funcstr, ""))
  | RecDef dl_defs ->
    match dl_defs with
    | [] -> return ("", "")
    | (FuncDef _)::_ -> let fdefs = List.map (fun def -> match def with
        | FuncDef fdef -> fdef
        | _ -> raise (CodegenError "RecDef not consistent: should not happen")
      ) dl_defs in
      let* func_blocks = mapM ocaml_of_func_def fdefs in
      let func_strs = List.concat func_blocks in  
      if func_strs = [] then return ("", "") else
      return ("let rec " ^ String.concat "\nand " func_strs, "")
    | (TypeDef _)::_ -> let typedefs = List.map (fun def -> match def with
        | TypeDef typedef -> typedef
        | _ -> raise (CodegenError "RecDef not consistent: should not happen")
      ) dl_defs in
      let* typestrs = concat_mapM "\nand " ocaml_of_typedef typedefs in
      if String.length typestrs >= 2 && String.sub typestrs 0 2 = "(*" then
        return ("", typestrs)
      else
        return ("", "type " ^ typestrs)
    | (RuleDef _)::_ -> raise (CodegenError "RecDef: RuleDef should not happen")

let ocaml_of_dl_defs (defs : dl_def list) : (string * string) t =
  let* def_strs : (string * string) list = mapM ocaml_of_dl_def defs in
  let func_defs, type_defs = List.split def_strs in
  let func_str = concat_nonempty "\n" func_defs in
  let type_str = concat_nonempty "\n" type_defs in
  return (func_str, type_str)

let generate_ocaml (dl_defs : dl_def list) : string * string * string =
  let main =
    "open Xl.Atom\n" ^
    "open Util_ocaml\n\n" ^
    "let (<|>) = Util_ocaml.Lib.Option.mplus\n" ^
    "let ( ** ) = Int.pow\n" ^
    "let (let*) = Option.bind\n\n"
  in
  let (funcdefs, typedefs), typeconvfuncs = 
    eval (ocaml_of_dl_defs dl_defs) in
  (main ^ funcdefs), typedefs, typeconvfuncs
