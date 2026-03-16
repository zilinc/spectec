open Util_ocaml
open TypeM
open Il.Ast

type backend = IL | VL
let backend = ref VL

(* Generate an encoding between OCaml <-> IL and OCaml <-> VL for parsing.
It does not support polymorphic record types, as there were none in the spec. *)

let f_prefix () = match !backend with IL -> "il_of_" | VL -> "vl_of_"
let g_prefix () = match !backend with IL -> "g_" | VL -> "g_"

let caseE_str mixop body = match !backend with
  | IL -> Printf.sprintf "CaseE (%s, %s) $$ no %% notyp" mixop body
  | VL -> Printf.sprintf "CaseV (%s, %s)" mixop body

let strE_str fields = match !backend with
  | IL -> Printf.sprintf "StrE [\n   %s\n ] $$ no %% notyp" fields
  | VL -> Printf.sprintf "StrV [\n   %s\n ]" fields

let tupE_str elems = match !backend with
  | IL -> Printf.sprintf "TupE [%s] $$ no %% notyp" elems
  | VL -> Printf.sprintf "TupV [%s]" elems

let exp_type_str () = match !backend with
  | IL -> "Il.Ast.exp"
  | VL -> "Backend_animation.Value.value"

let match_caseE_str () = match !backend with
  | IL -> "CaseE (mixop, {it=TupE es; _})"
  | VL -> "CaseV (mixop, es)"

let match_strE_str () = match !backend with
  | IL -> "StrE"
  | VL -> "StrV"

let mixopstr () = match !backend with
  | IL -> "mixop_to_atom_str"
  | VL -> "val_mixop_to_str"

(* 

This OCaml <-> VL encoding is hardcoded. The VL/IL definitions don't match the spec. the generated ocaml_of and ocaml_to_name will work if vl_of and vl_to are changed to:  

let vl_of_char char = caseV [[];[]] [vl_of_nat char]
let vl_of_name chars = caseV [[];[]] [(vl_of_list vl_of_char chars)] 
and
let vl_to_char exp = 
  match match_caseV "name" exp with
  | ([[];[]], [n]) -> vl_to_int n
  | _ -> error_value "char" exp
let vl_to_name exp =
  match match_caseV "name" exp with
  | ([[];[]], [chars]) -> vl_to_list vl_to_char chars
  | _ -> error_value "name" exp

*)
let gen_ocaml_of_name () = Printf.sprintf "ocaml_of_name (e : value) : DL.name =\n\
\  match e with\n\
\ | CaseV ([[];[]], [TextV s]) ->\n\
\   DL.C_pct__name (List.map (fun c -> DL.C_pct__char (Z.of_int c)) (Reference_interpreter.Utf8.decode s))\n\
\ | _ -> failwith \"ocaml_of_name: expected caseV1 TextV\""

let gen_ocaml_to_name () = Printf.sprintf "vl_of_name (v : DL.name) : Backend_animation.Value.value =\n\
\  match v with\n\
\  | DL.C_pct__name chars -> textV (Reference_interpreter.Utf8.encode (List.map (fun (DL.C_pct__char n) -> (Z.to_int n)) chars)) |> caseV1"

let gen_ocaml_of_hoststate () = Printf.sprintf "ocaml_of_hoststate _ = DL.HOSTSTATE_hoststate\n\n"

let mixop_to_vl_str (mixop : Xl.Mixop.mixop) : string =
  "[" ^
  String.concat "; "
    (List.map (fun atoms ->
      "[" ^ String.concat "; "
        (List.map (fun a ->
          Printf.sprintf "%S" (Xl.Atom.to_string a)
        ) atoms) ^ "]"
    ) mixop) ^
  "]"

let mixop_str mixop = match !backend with
  | IL -> mixop_to_ocaml_str mixop
  | VL -> mixop_to_vl_str mixop

let field_key_str atom = match !backend with
  | IL -> atom_to_ocaml_str atom
  | VL -> Printf.sprintf "%S" (Xl.Atom.to_string atom)


(* ===== IL/VL -> OCaml =====*)

(* assume that this function is called inline, i.e. after <Cons> e -> .... 
the TupE branch assumes the <Cons> has shape TupE es. For other, non-inline calls, we use gen_ocaml_of_typ_fn instead *)
let rec gen_ocaml_of_typ (t : typ) =
  match t.it with
  | VarT (id, args) ->
      let* argstr =
        concat_mapM " "
          (fun (arg : arg) ->
            match arg.it with
            | TypA t -> gen_ocaml_of_typ t
            | _ -> return "")
          args
      in
      let* is_tv = is_typevar (sanitize_name id.it) in
      if is_tv then return ("f_" ^ sanitize_name id.it)
      else return ("ocaml_of_" ^ append_sep (sanitize_name id.it) argstr " ")
  | BoolT -> return "ocaml_of_bool"
  | NumT `NatT -> return "ocaml_of_nat"
  | NumT `IntT -> return "ocaml_of_int"
  | NumT `RealT -> return "ocaml_of_rat"
  | NumT `RatT -> return "ocaml_of_real"
  | TextT -> return "ocaml_of_string"
  | TupT [] -> return ""
  | TupT ets ->
      let* args = mapM (fun (_, t) -> gen_ocaml_of_typ t) ets in
      return
        ("("
        ^ String.concat ", "
            (List.mapi (fun i arg -> Printf.sprintf "(%s (List.nth es %d))" arg i) args)
        ^ ")")
  | IterT (t1, iter) ->
      let* t1_str = gen_ocaml_of_typ t1 in
      (match iter with
      | List -> return (Printf.sprintf "ocaml_of_list (%s)" t1_str)
      | Opt  -> return (Printf.sprintf "ocaml_of_opt (%s)" t1_str)
      | _    -> return "todo: non-list/option iterator")

let gen_ocaml_of_typ_fn (t : typ) =
  let tup_str, it_str = match !backend with
    | IL -> "TupE", ".it"
    | VL -> "TupV", ""
  in
  match t.it with
  | TupT [] -> return "(fun _ -> ())"
  | TupT ets ->
      let* args = mapM (fun (_, t) -> gen_ocaml_of_typ t) ets in
      return
        (Printf.sprintf "(fun (e : %s) -> match e%s with %s es -> (%s) | _ -> failwith (Printf.sprintf \"expected %s. Got: %%s\" (Backend_animation.Value.string_of_value e)))"
          (exp_type_str ()) it_str tup_str
          (String.concat ", "
            (List.mapi (fun i arg -> Printf.sprintf "(%s (List.nth es %d))" arg i) args)) tup_str)
  | _ -> gen_ocaml_of_typ t

let gen_var_match_case typename tcs =
  let mixop, (_, args, _), _ = tcs in
  let consstr =
    sanitize_name ~typecons:true ~typename:false
      (mixop_to_atom_str mixop)
  in
  let* argsstr = gen_ocaml_of_typ args in
  return (Printf.sprintf " | %S -> %s_%s %s" consstr consstr typename argsstr)

let gen_translation_typfield name i (atom, (_bs, t, _prems), _hints) =
  let deref = match !backend with
  | IL -> ""
  | VL -> "!"
  in
  let* typ_str = gen_ocaml_of_typ t in
  return
    (mixop_to_atom_str ~recordfield:true [ [ atom ] ]
    ^ "_" ^ name ^ "= (" ^ typ_str ^ " " ^ deref ^ "e" ^ string_of_int i ^ ")")

let gen_match_typfield _name i (atom, (_bs, _t, _prems), _hints) =
  match !backend with
  | IL ->
    let atom_str = mixop_to_atom_str [ [ atom ] ] in
    return (Printf.sprintf "({it=(Atom \"%s\"); _}, e%d)" atom_str i)
  | VL ->
    let atom_str = Xl.Atom.to_string atom in
    return (Printf.sprintf "(%S, e%d)" atom_str i)

let gen_ocaml_of_str tfs name : string t =
  let funcname = "ocaml_of_" ^ name in
  let name' = "DL." ^ name in
  let exp_t = exp_type_str () in
  let it_str = match !backend with
    | IL -> ".it"
    | VL -> ""
   in
  let arg = Printf.sprintf "(e : %s)" exp_t in
  let* matchfields = concat_mapMi ";\n   " (gen_match_typfield name) tfs in
  let* fields = concat_mapMi ";\n     " (gen_translation_typfield name) tfs in
  let match_con = match_strE_str () in
  let funcdef =
    Printf.sprintf
      "%s %s : %s =\n\
      \ match e%s with\n\
      \ | %s ([\n\
      \   %s]) -> {\n\
      \     %s\n\
      \   }\n\
      \ | _ -> failwith \"Invalid expression for Record type %s: should be a %s\"\n"
      funcname arg name' it_str match_con matchfields fields name match_con
  in
  return funcdef

let gen_ocaml_of_var tcs name args : string t =
  let* typevars = get_typevars () in
  let polymorphic_args =
    String.concat " "
      (List.map
         (fun arg -> Printf.sprintf "(f_%s : %s -> '%s)" arg (exp_type_str ()) arg)
         (Set.to_list typevars))
  in
  let funcname = "ocaml_of_" ^ name in
  let name' = "DL." ^ name in
  let arg = append_sep polymorphic_args (Printf.sprintf "(e : %s)" (exp_type_str ())) " " in
  let* cases = concat_mapM "\n  " (gen_var_match_case name) tcs in
  let match_con = match_caseE_str () in
  let mixopstr = mixopstr () in
  let it_str = match !backend with
    | IL -> ".it"
    | VL -> ""
   in
  let funcdef =
    Printf.sprintf
      "%s %s : %s =\n\
      \ match e%s with\n\
      \ | %s -> begin match (sanitize_name ~typecons:true ~typename:false (%s mixop)) with\n\
      \  %s\n\
      \   end\n\
      \ | _ -> failwith (Printf.sprintf \"Invalid expression for Variant type %s: should be a %s. Got: %%s\" (Backend_animation.Value.string_of_value e))\n"
      funcname arg
      (append_sep args name' " ")
      it_str match_con mixopstr cases name match_con
  in
  return funcdef

(* ===== (OCaml -> IL/VL) ===== *)

let rec gen_typarg_il (t : typ)=
  match t.it with
  | VarT (id, args) ->
      let* argstr =
        concat_mapM " "
          (fun (arg : arg) ->
            match arg.it with
            | TypA t -> gen_typarg_il t
            | _ -> return "")
          args
      in
      let* is_tv = is_typevar (sanitize_name id.it) in
      if is_tv then return (g_prefix () ^ sanitize_name id.it)
      else return (f_prefix () ^ append_sep (sanitize_name id.it) argstr " ")
  | BoolT -> return (f_prefix () ^ "bool")
  | NumT `NatT -> return (f_prefix () ^ "nat")
  | NumT `IntT -> return (f_prefix () ^ "int")
  | NumT `RatT -> return (f_prefix () ^ "rat")
  | NumT `RealT -> return (f_prefix () ^ "real")
  | TextT -> return (f_prefix () ^ "string")
  | TupT [] -> return ""
  | TupT ets ->
      let* args = mapM (fun (_, t) -> gen_typarg_il t) ets in
      return
        ("("
        ^ String.concat ", "
            (List.mapi (fun i arg -> Printf.sprintf "(%s v%d)" arg i) args)
        ^ ")")
  | IterT (t1, iter) ->
      let* t1_str = gen_typarg_il t1 in
      (match iter with
      | List -> return (Printf.sprintf "%slist (%s)" (f_prefix ()) t1_str)
      | Opt  -> return (Printf.sprintf "%sopt (%s)" (f_prefix ()) t1_str)
      | _           -> return "todo: non-list/option iterator")

let gen_il_typfield name i (atom, (_bs, t, _prems), _hints) =
  let ref_ = match !backend with
  | IL -> ""
  | VL -> "ref "
  in
  let* typ_str = gen_typarg_il t in
  let field_name = mixop_to_atom_str ~recordfield:true [ [ atom ] ] ^ "_" ^ name in
  return (Printf.sprintf "(%s, %s(%s v.%s))"
    (field_key_str atom) ref_ typ_str field_name)

let gen_il_cases (typename : string) (tcs : typcase) =
  let mixop, (_, args, _), _ = tcs in
  let consstr =
    sanitize_name ~typecons:true ~typename:false
      (mixop_to_atom_str mixop)
  in
  let* (pat, body) = match args.it with
    | TupT [] ->
        return
          ( consstr ^ "_" ^ typename,
            match !backend with
            | IL -> "TupE [] $$ no % notyp"
            | VL -> "[]" )
    | TupT ets ->
        let n = List.length ets in
        let vars = List.init n (fun i -> Printf.sprintf "a%d" i) in
        let* translators = mapM (fun (_, t) -> gen_typarg_il t) ets in
        let elems = String.concat "; "
          (List.mapi (fun i tr -> Printf.sprintf "(%s a%d)" tr i) translators) in
        let body = match !backend with
          | IL -> Printf.sprintf "TupE [%s] $$ no %% notyp" elems
          | VL -> Printf.sprintf "[%s]" elems
        in
        return
          ( consstr ^ "_" ^ typename ^ " (" ^ String.concat ", " vars ^ ")",
            body )
    | _ ->
        let* tr = gen_typarg_il args in
        let body = match !backend with
          | IL -> Printf.sprintf "(%s a0)" tr
          | VL -> Printf.sprintf "[%s a0]" tr
        in
        return ( consstr ^ "_" ^ typename ^ " a0", body )
  in
  return (Printf.sprintf " | %s -> %s"
    pat (caseE_str (mixop_str mixop) body))

let gen_str_il tfs name : string t =
  let funcname = f_prefix () ^ name in
  let arg = "(v : DL." ^ name ^ ")" in
  let* fields = concat_mapMi ";\n     " (gen_il_typfield name) tfs in
  let funcdef =
    Printf.sprintf "%s %s : %s =\n %s\n"
      funcname arg (exp_type_str ()) (strE_str fields)
  in
  return funcdef

let gen_var_il tcs name args : string t =
  let* typevars = get_typevars () in
  let polymorphic_args =
    String.concat " "
      (List.map
         (fun arg -> Printf.sprintf "(%s%s : '%s -> %s)" (g_prefix ()) arg arg (exp_type_str ()))
         (Set.to_list typevars))
  in
  let funcname = f_prefix () ^ name in
  let arg = append_sep polymorphic_args ("(v : " ^ append_sep args ("DL." ^ name) " " ^ ")") " " in
  let* cases = concat_mapM "\n  " (gen_il_cases name) tcs in
  let funcdef =
    Printf.sprintf "%s %s : %s =\n match v with\n  %s\n"
      funcname arg (exp_type_str ()) cases
  in
  return funcdef

let generate_type_il (dt : deftyp) (name : string) (args : string): string t =
  match dt.it with
  | AliasT t -> (
      match t.it with
      | VarT (id, vargs) ->
          let typedef = f_prefix () ^ sanitize_name id.it in
          let* argsstr =
            concat_mapM " "
              (fun (arg : arg) ->
                match arg.it with
                | TypA t -> gen_typarg_il t
                | _ -> return "")
              vargs
          in
          return
            (Printf.sprintf "%s%s v = %s v" (f_prefix ()) name
               (append_sep typedef argsstr " "))
      | TupT [] ->
          return (Printf.sprintf "%s%s (v : unit) = %s" (f_prefix ()) name
            (caseE_str "[[]]" (match !backend with IL -> "TupE [] $$ no % notyp" | VL -> "[]")))
      | TupT ets ->
          let argstrs =
            String.concat ", "
              (List.mapi (fun i _ -> Printf.sprintf "v%d" i) ets)
          in
          let* targs = mapM (fun (_, t) -> gen_typarg_il t) ets in
          let elems = String.concat "; "
            (List.mapi (fun i arg -> Printf.sprintf "(%s v%d)" arg i) targs) in
          let body = match !backend with
            | IL -> Printf.sprintf "TupE [%s] $$ no %% notyp" elems
            | VL -> Printf.sprintf "[%s]" elems
          in
          return (Printf.sprintf "%s%s (%s) = %s" (f_prefix ()) name argstrs body)
      | _ ->
          let* typedef = gen_typarg_il t in
          return (Printf.sprintf "%s%s v = %s v" (f_prefix ()) name typedef))
  | StructT tfs -> gen_str_il tfs name
  | VariantT tcs -> 
    if name = "name" then return (gen_ocaml_to_name ())
    else gen_var_il tcs name args

let gen_ocaml_of_dt (dt : deftyp) (name : string) (args : string) : string t =
  match dt.it with
  | AliasT t -> (
      match t.it with
      | VarT (id, vargs) ->
          let typedef = "ocaml_of_" ^ sanitize_name id.it in
          let* argsstr =
            concat_mapM " "
              (fun (arg : arg) ->
                match arg.it with
                | TypA t -> gen_ocaml_of_typ t
                | _ -> return "")
              vargs
          in
          return
            (Printf.sprintf "ocaml_of_%s e = %s e" name
               (append_sep typedef argsstr " "))
      | TupT [] -> return (Printf.sprintf "ocaml_of_%s (e : %s) = ()" name (exp_type_str ()))
      | TupT ets ->
          let argstrs =
            String.concat ", "
              (List.mapi (fun i _ -> Printf.sprintf "e%d" i) ets)
          in
          let* targs = mapM (fun (_, t) -> gen_ocaml_of_typ t) ets in
          let body =
            "("
            ^ String.concat ", "
                (List.mapi (fun i arg -> Printf.sprintf "(%s e%d)" arg i) targs)
            ^ ")"
          in
          return (Printf.sprintf "ocaml_of_%s (%s) = %s" name argstrs body)
      | _ ->
          let* typedef = gen_ocaml_of_typ t in
          return (Printf.sprintf "ocaml_of_%s e = %s e" name typedef))
  | StructT tfs -> gen_ocaml_of_str tfs name
  | VariantT tcs -> 
    if name = "name" then return (gen_ocaml_of_name ())
    else if name = "hoststate" then return (gen_ocaml_of_hoststate ())
    else gen_ocaml_of_var tcs name args