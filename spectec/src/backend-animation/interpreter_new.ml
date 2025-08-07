open Il.Ast
open Il.Print
open Util.Source
open Xl
open Def

(* this is a bad way of doing it but works for now *)
let typeconversion = ref ""
module TypeMap = Map.Make(String)
module TypeSet = Set.Make(String)
let mytypes = ref TypeMap.empty
let typeconvfuncs = ref TypeSet.empty

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')

let uppcase_first s = 
  match s with
  | "" -> ""                               
  | _  ->
      let first = s.[0] in
      if is_letter first then
        let len = String.length s in
        let first = Char.uppercase_ascii first in
        String.init len (fun i -> if i = 0 then first else s.[i])
      else
        "C" ^ s

let sanitize_name ?(typename = true) ?(typecons = false) id =
  let raw = 
    if typename then String.lowercase_ascii id 
    else id 
  in 
  let raw =
    if typecons then uppcase_first raw
    else raw 
  in
  let replacements = [
    '*', "_star";
    '?', "_opt";
    '%', "Pct";
    '.', "_dot";
  ] in
  let replaced = List.fold_left (fun acc (ch, repl) ->
    String.concat repl (String.split_on_char ch acc)
  ) raw replacements in
  match replaced with
  | "match" | "type" | "let" | "val" | "list" | "in" -> replaced ^ "_"
  | _ -> replaced

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
  let consts1 = List.map (fun (op, (_, t, _), _) -> (Util_new.mixop_to_atom_str op, t)) tcs1 in
  let consts2 = List.map (fun (op, (_, t, _), _) -> (Util_new.mixop_to_atom_str op, t)) tcs2 in 
  (* TODO: do i even need this *)
  List.filter (fun c ->
    List.exists (fun c2 -> fst c = fst c2 && check_eq_typs (snd c) (snd c2)) consts2
  ) consts1

(* Validate premises *)

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
            Printf.sprintf "  | %s args -> %s args" consname consname
          ) common_consts in
        String.concat "\n" arms
      | _ -> "TODO: non-variant type conversion not implemented yet" in 
      arms
  else 
    "TODO: multiple insts in type conversion not implemented yet"

let typedef_of_dl_def (def : dl_def option) : type_def option =
  match def with
  | Some (TypeDef td) -> Some td 
  | _ -> None

let generate_type_conv (t1 : typ) (t2 : typ) : unit  =
  match t1.it, t2.it with
  | VarT (id1, _), VarT (id2, _) ->
      let lhs  = sanitize_name id1.it
      and rhs  = sanitize_name id2.it in
      let funcname = Printf.sprintf "%s_of_%s" rhs lhs in
      if not (TypeSet.mem funcname !typeconvfuncs) then 
      typeconvfuncs := TypeSet.add funcname !typeconvfuncs;
      let td1  = typedef_of_dl_def (TypeMap.find_opt lhs !mytypes)
      and td2  = typedef_of_dl_def (TypeMap.find_opt rhs !mytypes) in
      begin match td1, td2 with
      | Some _lhs_def, Some _rhs_def -> 
          let func = ref "" in
          func := Printf.sprintf "let %s_of_%s (arg : %s) : %s =\n" rhs lhs lhs rhs;
          func := !func ^ "  match arg with\n";
          let arms = generate_type_arms _lhs_def.it _rhs_def.it in
          typeconversion := !typeconversion ^ "\n" ^ !func ^ arms
      | _ -> typeconversion := !typeconversion ^ (Printf.sprintf "error: types %s and %s not defined\n" lhs rhs)
      end
  | _ ->
      typeconversion := !typeconversion ^ Printf.sprintf "todo: type conversion not implemented yet\n"

(* this may be repeated but just grouping all terminals from the IL AST into one type for now - this should probably just refer to the generated ocaml types oops *)
type value =
  | NumV of Num.num
  | TextV of string
  | IdV of string
  | AtomV of Atom.atom
  | MixopV of Mixop.mixop

let ocaml_of_numtyp = Num.string_of_typ

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

let rec ocaml_of_exp_stub (e : exp) : string =
  match e.it with
  | NumE n -> Num.to_string n
  | TextE s -> Printf.sprintf "%S" s
  | BoolE b -> string_of_bool b
  | VarE id -> sanitize_name id.it
  | ListE es -> "[" ^ String.concat "; " (List.map ocaml_of_exp_stub es) ^ "]"
  | TupE [] -> ""
  | TupE es -> "(" ^ String.concat ", " (List.map ocaml_of_exp_stub es) ^ ")"
  | CallE (id, args) ->
    let fname = sanitize_name id.it in
    let args =
      List.map (function arg ->
        match arg.it with
          | ExpA e -> ocaml_of_exp_stub e
          | _ -> "_"
      ) args
    in
    fname ^ " " ^ String.concat " " args
  | CaseE (mixop, e1) ->
    let label = Util_new.mixop_to_atom_str mixop in
    (* maybe there is a better way to generalise this *)
    let e1str = ocaml_of_exp_stub e1 in 
    if (String.length e1str = 0) then label
    else label ^ " " ^ e1str 
  | CvtE (e, _, _) -> ocaml_of_exp_stub e
  | BinE _ -> Il.Print.string_of_exp e
  | UncaseE (e, mixop) -> "uncase (" ^ ocaml_of_exp_stub e ^ ") (" ^ Util_new.mixop_to_atom_str mixop ^ ")"
  | ProjE (e, n) -> "proj (" ^ ocaml_of_exp_stub e ^ ") " ^ string_of_int n 
  | CmpE (op, _, e1, e2) -> "(" ^ ocaml_of_exp_stub e1 ^ " " ^ ocaml_of_cmpop op ^ " " ^ ocaml_of_exp_stub e2 ^ ")"
  | IterE (e1, (iter, bindings)) ->
    let iter_str = ocaml_of_iter iter in
    let bindings_str =
      bindings
      |> List.map (fun (id, e) ->
          "(" ^ (sanitize_name id.it) ^ ", " ^ ocaml_of_exp_stub e ^ ")"
        )
      |> String.concat "; "
    in
    "IterE (" ^ ocaml_of_exp_stub e1 ^ ", (" ^ iter_str ^ ", [" ^ bindings_str ^ "]))"
  | SupE (e1, typ1, typ2) | SubE (e1, typ1, typ2) -> 
    generate_type_conv typ1 typ2;
    ocaml_of_typ typ1 ^ "_of_" ^ ocaml_of_typ typ2 ^ " " ^ ocaml_of_exp_stub e1 
  | _ -> "TODO: other expression types not supported yet"


and ocaml_of_iter iter = 
  match iter with
    | Opt -> "option"
    | List -> "list"
    | List1 -> "List1"
    | ListN (e, id_opt) ->
      let e_str = ocaml_of_exp_stub e in
      let id_str =
        match id_opt with
        | Some id -> "Some " ^ "\"" ^ id.it ^ "\""  (* or sanitize_name id *)
        | None -> "None"
      in
      "ListN (" ^ e_str ^ ", " ^ id_str ^ ")"

and ocaml_of_typ (t : typ) : string =
  match t.it with 
  | VarT (id, _) -> sanitize_name id.it
  | BoolT -> "bool"                        
  | NumT numtype -> ocaml_of_numtyp numtype                  
  | TextT ->  "string"                    
  | TupT ets -> String.concat " * " (List.map ocaml_of_typbind ets)
  | IterT (t1, iter) -> ocaml_of_typ t1 ^ " " ^ ocaml_of_iter iter

and ocaml_of_typbind (e, t) =
  match e.it with
  | VarE {it = "_"; _} -> ocaml_of_typ t
  | _ -> ocaml_of_typ t

and ocaml_of_arg a =
  match a.it with
  | ExpA e -> ocaml_of_exp_stub e (* ignore this for now *)
  | TypA t -> "'" ^ ocaml_of_typ t
  | DefA id -> sanitize_name ~typename:false id.it
  | GramA g -> "TODO: grammar in arg not supported"

and ocaml_of_args = function
  | [] -> ""
  | as_ -> concat " " (List.map ocaml_of_arg as_) 

(*let string_of_clause (clause : func_clause) idx : string =
  match clause.it with
  | DefD (_, params, body, prems) ->
    let param_names =
      List.mapi (fun i arg ->
        match arg.it with
        | ExpA _ -> "x" ^ string_of_int i
        | _ -> "_"
      ) params
    in
    let args_str = String.concat " " param_names in
    let body_str = ocaml_of_exp_stub body in


    (* Extract guards from IfPr premises *)
    let guards =
      prems
      |> List.map (function
          | { it = IfPr cond; _ } -> (ocaml_of_exp_stub cond)
          | _ -> "TODO: other premises not supported yet")
    in

    let guard_str =
      match guards with
      | [] -> ""
      | _ ->
          let cond = String.concat " && " guards in
          Printf.sprintf " when %s" cond
    in

    Printf.sprintf "let clause_%d %s%s = %s" idx args_str guard_str body_str*)

(* Extract guards from IfPr premises *)
let ocaml_of_prems (prems : prem' phrase list) =
  let guards, lets =
  List.fold_right (fun prem (guards, lets) ->
    match prem.it with
    | IfPr cond ->
      ((ocaml_of_exp_stub cond) :: guards, lets)
    | LetPr (lhs, rhs, _) ->
      let letbinding = Printf.sprintf "let %s = %s in" (ocaml_of_exp_stub lhs) (ocaml_of_exp_stub rhs) in 
      (guards, letbinding :: lets)
    | RulePr _ ->
      (guards, "(* TODO: RulePr *)" :: lets)
    | ElsePr ->
      (guards, lets)
    | IterPr (_, _) ->
        (guards, "(* TODO: IterPr *)" :: lets)
  ) prems ([], []) in 
  let guard_str = String.concat " && " guards in
  let let_str = String.concat "\n" lets in
  guard_str, let_str

let ocaml_of_func_def (fdef : func_def) : string * string =
  let id, _, _, clauses, _ = fdef.it in
  let name = sanitize_name id.it in

  let ocaml_of_clause_match clause =
    match clause.it with
    | DefD (_, params, body, prems) ->
      match params with
      | [arg] ->
        let guard_str, let_str = ocaml_of_prems prems in 
        let when_cond = if guard_str = "" then "" else " when " ^ guard_str in  
        let bodycode = ocaml_of_exp_stub body in                                
        let body_with_lets = if let_str = "" then bodycode else 
        (Printf.sprintf "\n    %s\n    %s" let_str bodycode) in
        Printf.sprintf "  | %s%s -> %s" (ocaml_of_arg arg) when_cond body_with_lets
      | _ -> Printf.sprintf "TODO: multiple args in clause"
  in

  let match_arms =
    List.map ocaml_of_clause_match clauses |> String.concat "\n"
  in

  Printf.sprintf {|
let %s arg =
  match arg with
%s
  | _ -> failwith "No matching clause"
|} name match_arms, ""

let ocaml_of_dl_def (def : dl_def) : string * string =
  match def with
  | RuleDef _  -> "", "" (* TODO: should these raise an error? *)
  | TypeDef _ -> "", ""
  | FuncDef fdef -> ocaml_of_func_def fdef

let generate_ocaml (funcs : dl_def list) : string * string =
  let s = ref "" in
  let util = ref "" in
  s := !s ^ "open Xl.Atom\n";
  s := !s ^ "open Util_new\n";
  List.iter (fun fdef ->
    let def, util' = ocaml_of_dl_def fdef in
    s := !s ^ def;
    if def <> "" then s := !s ^ "\n\n";
    util := !util ^ util'; (* this is where types should be returned probably *)
    if util' <> "" then util := !util ^ "\n\n"
  ) funcs;
  (* this is also really badly placed *)
  let oc = open_out "./src/backend-animation/dl_codegen_typeconv.ml" in
  output_string oc !typeconversion;
  close_out oc;
  !s, !util

let ocaml_of_typ_args t =
  match t.it with
  | TupT [] -> ""
  | TupT _ -> ocaml_of_typ t
  | _ -> "(" ^ ocaml_of_typ t ^ ")"

(* ignoring the refinement type annotations for now - animation deals with this? *)
let ocaml_of_typcase (op, (_, t, _), _hints) =
  let args_str = ocaml_of_typ_args t in 
  if args_str = "" then
    sanitize_name ~typecons:true (Util_new.mixop_to_atom_str op)
  else
    sanitize_name ~typecons:true (Util_new.mixop_to_atom_str op) ^ " of " ^ ocaml_of_typ_args t

let ocaml_of_typfield (atom, (_bs, t, _prems), _hints) =
  Util_new.mixop_to_atom_str ~typename:true [[atom]] ^ ": " ^ ocaml_of_typ t 

let ocaml_of_deftyp dt = 
  match dt.it with
  | AliasT t -> ocaml_of_typ t
  | StructT tfs ->
    "{\n  " ^ String.concat ";\n  " (List.map ocaml_of_typfield tfs) ^ "\n}"
  | VariantT tcs ->
    "\n  | " ^ String.concat "\n  | " (List.map ocaml_of_typcase tcs)

let generate_ocaml_types (typedefs : Def.dl_def list) : string =
  Printf.printf "Generating OCaml types...\n";
  let s = ref "" in
  List.iter (fun def ->
    match def with
    | TypeDef {it=(id, _ps, [{it = InstD (_, as_, dt); _}]); _} -> 
        mytypes := TypeMap.add (sanitize_name id.it) def !mytypes;
        s := !s ^ ("type " ^ ocaml_of_args as_ ^ " " ^ (sanitize_name id.it) ^ " = " ^ ocaml_of_deftyp dt ^ "\n")
    | TypeDef {it=(id, ps, insts); _} -> 
      mytypes := TypeMap.add (sanitize_name id.it) def !mytypes;
      s := !s ^ ("type " ^ 
      (sanitize_name id.it) ^ string_of_params ps ^
      String.concat "\n" (List.map (string_of_inst id) insts) ^ "\n")
    | _ -> ()
  ) typedefs;
  !s



