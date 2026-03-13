open Il.Ast
open Il.Print
open Util.Source
open Xl
open Def
open Util_ocaml
open Util.Error
open Util_ocaml.TypeM

(* TODOs
remove all the code that tries to replace type families 
also remove the code that checks for comments in type definitions, we no longer comment out multi instance types so no longer need this check *)

exception CannotAnimate
exception CannotSplit of string

(* This exception is raised when the OCaml generator sees a pattern that it does not expect (for example, if ruled out by validation) / unreachable code *)
let error at msg = error at "OCaml CodeGen" msg

(* for error messages *)
let rec get_dl_def_region (dl_def : dl_def) : region =
  match dl_def with
  | FuncDef fd       -> fd.at
  | TypeDef td       -> td.at
  | RecDef (rd :: _) -> get_dl_def_region rd

(* type variables need to be prefixed with ' *)
let typevars_of_params (ps : param list) : Set.t =
  ps
  |> List.filter_map (fun p ->
         match p.it with TypP id -> Some (sanitize_name id.it) | _ -> None)
  |> Set.of_list

(* hardcoded: `Step` needs to be re-defined manually to call `step`. This makes a group of functions (specifically those on any call path from `step` to `Step`) mutually recursive. Since these functions are not recursive in the original spec, we need to mark them as such manually. *)
let find_recdefs (funcdefs : dl_def list) =
  let visited = Hashtbl.create (List.length funcdefs) in
  let rec dfs visited start target =
    let fdef = find_fdef funcdefs start in
    match Hashtbl.find_opt visited start with
    | Some children -> children
    | None ->
        Hashtbl.add visited start Set.empty;
        (* if this call-path has reached `Step`, we can add to the recursive functions *)
        if start = target then (
          let s = Set.singleton start in
          Hashtbl.add visited start s;
          s)
        else (
          Hashtbl.add visited start Set.empty;
          (* to avoid cycles *)
          let children = f_calls fdef in
          let reachable =
            List.fold_left Set.union Set.empty
              (List.map
                 (fun child -> dfs visited child target)
                 (Set.to_list children))
          in
          (* if `Step` is reachable from any of the children then it is reachable from `start` *)
          let result =
            if Set.is_empty reachable then Set.empty
            else Set.add start reachable
          in
          Hashtbl.add visited start result;
          result)
  in
  dfs visited "step" "Step"

let hardcode_step (funcdefs : dl_def list) : dl_def list =
  let rec_funcs = find_recdefs funcdefs in
  let rec mark idx acc rest recdefs insert =
    match rest with
    | [] -> (acc, recdefs, insert)
    | def :: rest' -> (
        (* todo: also need to check every rec def oops *)
        match def with
        | FuncDef { it = { it = name; _ }, _, _, _, _, _; _ } ->
            if Set.mem name rec_funcs then
              (*(Printf.printf "updated insert index: %d\n" insert;*)
              mark (idx + 1) acc rest' (recdefs @ [ def ]) idx
            else mark (idx + 1) (acc @ [ def ]) rest' recdefs insert
        | _ -> mark (idx + 1) (acc @ [ def ]) rest' recdefs insert)
  in
  let rest, recdefs, insert = mark 1 [] funcdefs [] (-1) in
  take (insert - List.length recdefs) rest
  @ [ RecDef recdefs ]
  @ drop (insert - List.length recdefs) rest 

(* manually place "inv_proj_<func>" right after "proj_<func>" *)
let reorder_inv_proj (defs : dl_def list) (inv_name : string) (proj_name : string) : dl_def list =
  match List.partition (fun def ->
    match def with
    | FuncDef fd -> let id, _, _, _, _, _ = fd.it in id.it = inv_name
    | _ -> false
  ) defs with
  | [], _ -> defs  (* inv not found, do nothing *)
  | [inv_def], rest ->
    List.concat_map (fun def ->
      match def with
      | FuncDef fd ->
        let id, _, _, _, _, _ = fd.it in
        if id.it = proj_name then [def; inv_def] else [def]
      | _ -> [def]
    ) rest
  | _ -> defs  (* shouldn't happen *)

(*let gen_il_typfield name i (atom, (_bs, t, _prems), _hints) =
  let* typ_str = gen_typarg_il t in
  let field_name = Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ atom ] ] ^ "_" ^ name in
  return (Printf.sprintf "(%s, (%s v.%s))"
    (atom_to_ocaml_str atom)
    typ_str
    field_name)

let gen_il_cases typename tcs =
  let mixop, (_, args, _), _ = tcs in
  let consstr =
    sanitize_name ~typecons:true ~typename:false
      (Util_ocaml.mixop_to_atom_str mixop)
  in
  let* (pat, body) = match args.it with
    | TupT [] ->
        return
          ( consstr ^ "_" ^ typename,
            "TupE [] $$ no % notyp" )
    | TupT ets ->
        let n = List.length ets in
        let vars = List.init n (fun i -> Printf.sprintf "a%d" i) in
        let* translators = mapM (fun (_, t) -> gen_typarg_il t) ets in
        let body =
          "TupE [" ^
          String.concat "; " (List.mapi (fun i tr -> Printf.sprintf "(%s a%d)" tr i) translators) ^
          "] $$ no % notyp"
        in
        return
          ( consstr ^ "_" ^ typename ^ " (" ^ String.concat ", " vars ^ ")",
            body )
    | _ ->
        let* tr = gen_typarg_il args in
        return
          ( consstr ^ "_" ^ typename ^ " a0",
            Printf.sprintf "(%s a0)" tr )
  in
  return (Printf.sprintf " | %s -> CaseE (%s, %s) $$ no %% notyp"
    pat (mixop_to_ocaml_str mixop) body)

let gen_str_il tfs name : string t =
  let funcname = "il_of_" ^ name in
  let arg = "(v : DL." ^ name ^ ")" in
  let* fields = concat_mapMi ";\n     " (gen_il_typfield name) tfs in
  let funcdef =
    Printf.sprintf
      "%s %s : exp =\n\
      \ StrE [\n\
      \   %s\n\
      \ ] $$ no %% notyp\n"
      funcname arg fields
  in
  return funcdef

let gen_var_il tcs name args : string t =
  let* typevars = get_typevars () in
  let polymorphic_args =
    String.concat " "
      (List.map
         (fun arg -> Printf.sprintf "(g_%s : '%s -> exp)" arg arg)
         (Set.to_list typevars))
  in
  let funcname = "il_of_" ^ name in
  let arg = append_sep polymorphic_args ("(v : " ^ append_sep args ("DL." ^ name) " " ^ ")") " " in
  let* cases = concat_mapM "\n  " (gen_il_cases name) tcs in
  let funcdef =
    Printf.sprintf
      "%s %s : exp =\n\
      \ match v with\n\
      \  %s\n"
      funcname arg cases
  in
  return funcdef

let generate_type_il dt name args : string t =
  match dt.it with
  | AliasT t -> (
      match t.it with
      | VarT (id, args) ->
          let typedef = "il_of_" ^ sanitize_name id.it in
          let* argsstr =
            concat_mapM " "
              (fun arg ->
                match arg.it with
                | TypA t -> gen_typarg_il t
                | _ -> return "")
              args
          in
          return
            (Printf.sprintf "il_of_%s v = %s v" name
               (append_sep typedef argsstr " "))
      | TupT [] -> return (Printf.sprintf "il_of_%s (v : unit) = TupE [] $$ no %% notyp" name)
      | TupT ets ->
          let argstrs =
            String.concat ", "
              (List.mapi (fun i _ -> Printf.sprintf "v%d" i) ets)
          in
          let* args = mapM (fun (_, t) -> gen_typarg_il t) ets in
          let body =
            "TupE ["
            ^ String.concat "; "
                (List.mapi (fun i arg -> Printf.sprintf "(%s v%d)" arg i) args)
            ^ "] $$ no % notyp"
          in
          return (Printf.sprintf "il_of_%s (%s) = %s" name argstrs body)
      | _ ->
          let* typedef = gen_typarg_il t in
          return (Printf.sprintf "il_of_%s v = %s v" name typedef))
  | StructT tfs -> gen_str_il tfs name
  | VariantT tcs -> gen_var_il tcs name args*)

(* as of now, we do not error if the type is NOT a tuple as the IL elaboration converts a Tup [t] into t. *)
let rec get_tupsize (t : typ) : int option t =
  match t.it with
  | TupT ts -> return (Some (List.length ts))
  | VarT (id, _) -> (
      let* typedef = get_typedef id.it in
      let td =
        match typedef with
        | Some td -> td
        | _ -> error t.at "Unknown typevariable in projection"
      in
      match td.it with
      | _, _, [ { it = InstD (_, as_, dt); _ } ] -> (
          match dt.it with
          | AliasT alias -> get_tupsize alias
          | _ -> return (Some 1))
      | _ -> error t.at "todo: projection for multiple instance types")
  | IterT (_, List) | IterT (_, List1) | IterT (_, ListN _) -> return None
  (*| _ -> error t.at "Projection in non-tuple/list/alias"*)
  | _ -> return (Some 1)

let rmv_nonexp (p : param) : bool =
  match p.it with ExpP _ -> true | _ -> false

  let rmv_nonexparg (a : arg) : bool =
  match a.it with TypA _ -> false | _ -> true

let known_exps (es : exp list) : bool t =
  allM
    (fun e -> are_knowns (Set.map sanitize_name (Valid.free_vars_exp e)))
    es

let get_unknown_vars (es : (id * exp) list) : string list t =
  foldM
    (fun acc (id, e) ->
      let* known = are_knowns (Set.map sanitize_name (Valid.free_vars_exp e)) in
      if known then return acc else return (id.it :: acc)
    ) [] es

let are_valid outflows =
  List.iter (fun (_, e) -> 
    match e.it with
    | VarE _ -> ()
    | _ -> error e.at "Invalid Iterator expression x <- e: e must be a variable.")
  outflows

let get_cons_args typargs =
  match typargs.it with
  | VarT _ | NumT _ | IterT _ | BoolT | TextT -> (1, "fv_0", "fv_0")
  | TupT es ->
      let n = List.length es in
      if n = 0 then (0, "", "")
      else
        let vs = List.init n (fun i -> "fv_" ^ string_of_int i) in
        ( n,
          "(" ^ String.concat ", " vs ^ ")",
          String.concat ", " vs )

(* used to generate nested updates to lists and record types *)
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

let rec check_eq_typs t1 t2 =
  match (t1.it, t2.it) with
  | VarT (id1, a1), VarT (id2, a2) ->
      id1.it = id2.it
      && List.length a1 = List.length a2
  | BoolT, BoolT -> true
  | NumT _, NumT _ -> true (* TODO: implement *)
  | TextT, TextT -> true
  | TupT ets1, TupT ets2 ->
      List.length ets1 = List.length ets2
      && List.for_all2
           (fun (_, t1) (_, t2) ->
             (*check_eq_exp e1 e2 &&*) check_eq_typs t1 t2)
           ets1 ets2
  | IterT (t11, iter1), IterT (t21, iter2) ->
      check_eq_typs t11 t21 && iter1 = iter2
  | _ -> false

let get_common_consts tcs1 tcs2 =
  let consts1 =
    List.map
      (fun (op, (_, t, _), _) -> (Util_ocaml.mixop_to_atom_str op, t))
      tcs1
  in
  let consts2 =
    List.map
      (fun (op, (_, t, _), _) -> (Util_ocaml.mixop_to_atom_str op, t))
      tcs2
  in
  let comm =
    List.filter
      (fun c ->
        List.exists
          (fun c2 -> fst c = fst c2 && check_eq_typs (snd c) (snd c2))
          consts2)
      consts1
  in
  comm

let ocaml_of_numtyp = Num.string_of_typ

(* return all type constructors (follows aliases) *)
let rec get_all_tcs name { it = InstD (_, _, dt); _ } =
  match dt.it with
  | AliasT { it = VarT (tid, _); _ } -> 
      let* Some t_def = get_typedef (sanitize_name tid.it) in
      let {it = id, _, insts; _} = t_def in
      foldM (fun acc inst ->
        (*let* new_tcs = get_all_tcs (sanitize_name id.it) inst in*)
        let* new_tcs = get_all_tcs name inst in
        return (new_tcs @ acc))
        [] insts
  | VariantT tcs -> return [(tcs, name)]
  | _ -> error dt.at "Subtyping only implemented between Variant Types"

let generate_type_arms t1name t2name (_, _, insts1) (_, _, insts2) =
  let* resolved1 = mapM (get_all_tcs t1name) insts1 in
  let* resolved2 = mapM (get_all_tcs t2name) insts2 in

  let resolved1 = List.flatten resolved1 in
  let resolved2 = List.flatten resolved2 in

  let arms =
    List.concat_map
      (fun (tcs1, name1) ->
        List.concat_map
          (fun (tcs2, name2) ->
            let common_consts = get_common_consts tcs1 tcs2 in
            List.map
              (fun (consname, typargs) ->
                let cons1 =
                  sanitize_name ~typecons:true ~typename:false consname ^ "_" ^ name1
                in
                let cons2 =
                  sanitize_name ~typecons:true ~typename:false consname ^ "_" ^ name2
                in
                let _, argstr, _ = get_cons_args typargs in
                Printf.sprintf "  | %s -> %s"
                  (append_sep cons1 argstr " ")
                  (append_sep cons2 argstr " "))
              common_consts)
          resolved2)
      resolved1
  in

  return (String.concat "\n" arms)

(* generate subtyping i.e. t2_of_t1 *)
let generate_type_conv (t1 : typ) (t2 : typ) : unit t =
  match (t1.it, t2.it) with
  | VarT (id1, _), VarT (id2, _) -> (
      let lhs = sanitize_name id1.it and rhs = sanitize_name id2.it in
      let funcname = Printf.sprintf "%s_of_%s" rhs lhs in
      (*Printf.printf "generating %s:\n" funcname;*)
      let* is_defined = is_defined funcname in
      if is_defined then return ()
      else
        let* () = add_funcdef funcname in
        let* type_defs = mapM get_typedef [ lhs; rhs ] in
        match type_defs with
        | [ Some _lhs_def; Some _rhs_def ] ->
            let func =
              Printf.sprintf
                "let %s_of_%s (arg : %s) : %s =\n  match arg with\n" rhs lhs lhs
                rhs
            in
            (try 
              (let* arms = generate_type_arms lhs rhs _lhs_def.it _rhs_def.it in
              let failcase = "\n  | _ -> raise SubtypingFailed\n" in
              tell (func ^ arms ^ failcase))
            with _ -> Printf.printf "Warning: cannot generate conversion between %s and %s" lhs rhs; return ())
        | [ None; _ ] ->
            error t1.at
              (Printf.sprintf
                 "Type %s: appears in sub/super type but is not defined" lhs)
        | [ _; None ] ->
            error t2.at
              (Printf.sprintf
                 "Type %s: appears in sub/super type but is not defined" rhs))
  | _ -> tell "TODO: type conversion between non-VarTs not implemented yet\n"

(*let generate_numtype_conv (t1 : numtyp) (t2 : numtyp) : unit t =
  let funcname = ocaml_of_numtyp t1 ^ "_of_" ^ ocaml_of_numtyp t2 in
  let* is_defined = is_defined funcname in
  if is_defined then return ()
  else
    let funcdef =
      "let " ^ funcname ^ " (arg : " ^ ocaml_of_numtyp t2 ^ ") : "
      ^ ocaml_of_numtyp t1 ^ " =\n"
    in
    let funcbody = "Xl.Num.cvt " ^ ocaml_of_numtyp t1 ^ " arg\n" in
    let* () = add_funcdef funcname in
    tell (funcdef ^ funcbody)*)

(* generates a function to project element i out of an n-tuple *)
let generate_proj n i : unit t =
  let funcname = Printf.sprintf "proj_%d_%d" n i in
  let* is_defined = is_defined funcname in
  if is_defined then return ()
  else
    let* () = add_funcdef funcname in
    let type_vars =
      List.init n (fun i -> String.make 1 Char.(chr (code 'a' + i)))
    in
    let tuple_ty =
      String.concat " * " (List.map (fun v -> "'" ^ v) type_vars)
    in
    let ret_ty = "'" ^ List.nth type_vars i in
    let xs = List.init n (fun i -> "x" ^ string_of_int (i + 1)) in
    let pat = String.concat ", " xs in
    let body = List.nth xs i in
    tell
      (Printf.sprintf "let %s : %s -> %s = function\n  | %s -> %s\n" funcname
         tuple_ty ret_ty pat body)

let ocaml_of_cmpop op =
  match Il.Print.string_of_cmpop op with "=/=" -> "<>" | s -> s


let rec ocaml_of_exp ?(typearg = false) ?(funcdef = false) ?(funccall = false) ?(retval = false)
    (e : exp) : string t =
  (* for now, we don't support dependent types. *)
  if typearg then return "(* TODO:typearg *)"
  else if
    (* function arguments must be (subtyped/supertyped/cased) variables *)
    funcdef
  then
    match e.it with
    | VarE id ->
        let* () = add_known (sanitize_name id.it) in
        let* typ_annot = ocaml_of_typ e.note in
        return
          (Printf.sprintf "(%s : %s)" (sanitize_name ~typearg id.it) typ_annot)
    | SubE (e1, typ1, typ2) ->
        (* if an argument is of the form e : t1 <: t2, 
       the function expects an arg of type t2 but casts it to a type t1 in the body. so we have to add "let e = t1_of_t2 arg" to make it typecheck *)
        let* freshvarname = get_freshvar () in
        let* () = generate_type_conv typ2 typ1 in
        let* e1str =
          match e1.it with
          | VarE id ->
              let* () = add_known (sanitize_name id.it) in
              return (sanitize_name ~typearg id.it)
          | _ ->
              error e1.at
                "Invalid supertype/subtype argument: expected a variable."
        in
        let* typ1str = ocaml_of_typ ~consannot:true typ1 in
        let* typ2str = ocaml_of_typ ~consannot:true typ2 in
        let* () =
          add_typecast
            ("  let " ^ e1str ^ " = " ^ typ1str ^ "_of_" ^ typ2str ^ " "
           ^ freshvarname ^ " in")
        in
        return (Printf.sprintf "(%s : %s)" freshvarname typ2str)
    | CaseE (mixop, e1) ->
        let* e1_str = ocaml_of_exp ~funcdef:true e1 in
        let argstr = if e1_str = "" then "" else "(" ^ e1_str ^ ")" in
        let* mixopstr = ocaml_of_mixop mixop e.note in
        let* typannot = ocaml_of_typ e.note in
        return (Printf.sprintf "(%s %s : %s)" mixopstr argstr typannot)
    (*| CatE _ ->
        let* freshvar = get_freshvar () in
        let* typannot = ocaml_of_typ e.note in
        let* split = split_arg e freshvar in
        let* () = add_typecast split in
        return (Printf.sprintf "(%s : %s)" freshvar typannot)*)
    | TupE [] -> return ""
    | TupE es ->
        let* es_strs = concat_mapM ", " (ocaml_of_exp ~funcdef:true) es in
        return ("(" ^ es_strs ^ ")")
    | _ -> raise CannotAnimate
  else
    match e.it with
    | NumE n -> return ("(Z.of_int " ^ Num.to_string n ^ ")")
    | TextE s -> return (Printf.sprintf "%S" s)
    | BoolE b -> return (string_of_bool b)
    | VarE id -> return (sanitize_name ~typearg id.it)
    | ListE es ->
        (* I am not sure if there is a better way to do this *)
        let* es_strs = concat_mapM "; " (ocaml_of_exp ~typearg) es in
        return ("[" ^ es_strs ^ "]")
    | TupE [] -> return ""
    | TupE es ->
        let* es_strs = concat_mapM ", " (ocaml_of_exp ~typearg) es in
        return ("(" ^ es_strs ^ ")")
    | CallE (id, args) ->
        let id' = sanitize_name id.it in
        let fname = id' ^ "_fn" in
        let typ_args, exp_args = List.partition (fun a -> match a.it with TypA _ -> true | _ -> false) args in
        let* typevar_str = concat_mapM " " (fun a ->
          match a.it with
          | TypA t ->
            let* ocaml_tr = Parser_ocaml.gen_ocaml_of_typ t in
            let* il_tr = Parser_ocaml.gen_typarg_il t in
            return (Printf.sprintf "(%s) (%s)" ocaml_tr il_tr)
          | _ -> return ""
        ) typ_args in
        let* args' = ocaml_of_args ~typearg ~funcdef ~funccall:true exp_args in
        let fname', args'' =
          if fname = "uc_steps_fn" then "steps_fn", (args' ^ "(Z.of_int 256)")
          else fname, (if args' = "" && typevar_str = "" then "()" else args') in
        let full_args = append_sep typevar_str args'' " " in
        let full_args' = if full_args = "" then "()" else full_args in
        return ("(" ^ fname' ^ " " ^ full_args' ^ ")")
    | CaseE (mixop, e1) ->
        let* mixopstr = ocaml_of_mixop mixop e.note in
        if mixopstr = "STACK_OVERFLOW_stepresult"  && retval then return "raise Backend_interpreter.Exception.OutOfMemory" else
        let* e1str = ocaml_of_exp e1 in
        let argsstr = if e1str = "" then "" else "(" ^ e1str ^ ")" in
        return (Printf.sprintf "(%s)" (append_sep mixopstr argsstr " "))
    | BinE (op, _, e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        (* if this is a float operation *)
        let* e1type = ocaml_of_typ e1.note in
        let float = (e1type = "float") || (e1type = "rat") in
        let binopstr, infix = ocaml_of_binop ~float op in
        let e2str' = if (not float) && op = `PowOp then "(Z.to_int " ^ e2str ^ ")" else e2str in
        if float || infix then return ("(" ^ e1str ^ " " ^ binopstr ^ " " ^ e2str' ^ ")")
        else return ("(" ^ binopstr ^ " " ^ e1str ^ " " ^ e2str' ^ ")")
    | UnE (op, _, e1) ->
        let* e1str = ocaml_of_exp e1 in
        let* e1type = ocaml_of_typ e1.note in
        let is_float = e1type = "float" || e1type = "rat" in
        let opstr, infix = ocaml_of_unop ~float:is_float op in
        if infix then return ("(" ^ opstr ^ "(" ^ e1str ^ "))")
        else return ("(" ^ opstr ^ " " ^ e1str ^ ")")
    | UncaseE (e1, mixop) ->
        let* consdef = resolve_variant e1.note in
        let* exptyp = ocaml_of_typ ~consannot:true (Option.get consdef) in
        let* expstr = ocaml_of_exp e1 in
        let mixopstr = 
          sanitize_name ~typecons:true ~typename:false
            (Util_ocaml.mixop_to_atom_str mixop)
        in
        return
          (Printf.sprintf "(uncase_%s_%s (%s))" exptyp
             (String.lowercase_ascii mixopstr)
             expstr)
    | ProjE (e, n) -> (
        let* expstr = ocaml_of_exp e in
        let* typstr = ocaml_of_typ e.note in
        let* tupsize = get_tupsize e.note in
        match tupsize with
        | Some len ->
            if n < 0 || n >= len then
              error e.at "Tuple projection out of bounds."
            else
              let* () = generate_proj len n in
              return (Printf.sprintf "(proj_%d_%d %s)" len n expstr)
        (* if not a tuple, we are projecting out of a list *)
        | None -> return (Printf.sprintf "(List.nth %s %d)" expstr n))
    | CmpE (op, _, e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        let* e1type = ocaml_of_typ e1.note in
        let is_nat = e1type = "nat" || e1type = "int" in
        if is_nat then
        let cmpstr = match op with
          | `EqOp  -> "Z.equal"
          | `NeOp -> "(fun a b -> not (Z.equal a b))"
          | `LtOp  -> "Z.lt"
          | `GtOp  -> "Z.gt"
          | `LeOp  -> "Z.leq"
          | `GeOp  -> "Z.geq"
        in
        return ("(" ^ cmpstr ^ " " ^ e1str ^ " " ^ e2str ^ ")")
        else return ("(" ^ e1str ^ " " ^ ocaml_of_cmpop op ^ " " ^ e2str ^ ")")
    | IterE (e1, (iter, bindings)) -> (
        let es = List.map snd bindings in
        let* all_inflows = known_exps es in
        if not all_inflows then
          let* unknown_vars = get_unknown_vars bindings in
          match unknown_vars with
          | [ x ] -> (
              (match iter with
              | ListN (e, optid) ->
                  let* lenstr = ocaml_of_exp e in
                  let idstr =
                    match optid with Some id -> id.it | None -> ""
                  in
                  if (not (idstr = x)) || idstr = "" then
                    return "(* TODO: outflow in IterE *)"
                  else
                    let* body_str = ocaml_of_exp e1 in
                    let lenstr' = "(Z.to_int " ^ lenstr ^ ")" in
                    let idstr_int = if idstr = "_" then "_" else idstr ^ "_int" in
                    let binding = if idstr = "_" then "" else "let " ^ sanitize_name idstr ^ " = Z.of_int " ^ idstr_int ^ " in\n" in
                    return
                      ("(List.init (" ^ lenstr' ^ ") (fun " ^ idstr_int
                     ^ " -> " ^ binding ^ body_str ^ "))")
              | _ -> return "(* TODO: multiple outflows in IterE *)"))
          | _ -> return "(* TODO: multiple outflows in IterE *)"
        else
          let* prev_knowns = get_knowns in
          let new_knowns =
            List.map (fun i -> sanitize_name (fst i).it) bindings
          in
          let* () = add_knowns new_knowns in
          let* body_str = ocaml_of_exp e1 in
          match bindings with
          | [] -> (
              match iter with
              | ListN (e, optid) ->
                  let* lenstr = ocaml_of_exp e in
                  let idstr =
                    match optid with
                    | Some id -> sanitize_name id.it
                    | None -> "_"
                  in
                  let* () = set_knowns prev_knowns in
                  let idstr_int = if idstr = "_" then "_" else idstr ^ "_int" in
                  let binding = if idstr = "_" then "" else "let " ^ idstr ^ " = Z.of_int " ^ idstr_int ^ " in\n" in
                  let lenstr' = "(Z.to_int " ^ lenstr ^ ")" in
                  return
                    ("(List.init (" ^ lenstr' ^ ") (fun " ^ idstr_int ^ " -> " ^ binding
                   ^ body_str ^ "))")
              | _ ->
                  let* () = set_knowns prev_knowns in
                  return
                    ("[" ^ body_str ^ "]")
              )
          | bindings -> (
              match iter with
              | List | ListN _ | List1 ->
                  let* listnames = mapM ocaml_of_exp es in
                  let varnames =
                    String.concat " "
                      (List.map (fun (id, _) -> sanitize_name id.it) bindings)
                  in
                  let* () = set_knowns prev_knowns in
                  let* () = add_knowns listnames in
                  let lists = String.concat " " listnames in
                  return
                    (Printf.sprintf "(map%d (fun %s -> %s) %s)"
                       (List.length bindings) varnames body_str lists)
              | Opt ->
                  (* assumption: if, in any of the bindings x <- x*, `x*` is None, we return None for the whole computation since `x` cannot have a value in that case *)
                  let* listnames = mapM ocaml_of_exp es in
                  let varnames =
                    List.map (fun (id, _) -> sanitize_name id.it) bindings
                  in
                  let get_opts =
                    String.concat "\n"
                      (List.map2
                         (fun i e ->
                           Printf.sprintf "    let %s = Option.get %s in" i e)
                         varnames listnames)
                  in
                  let* () = set_knowns prev_knowns in
                  let* () = add_knowns listnames in
                  return
                    (Printf.sprintf
                       "(try (\n\
                        %s\n\
                       \    Some(%s))\n\
                       \  with Invalid_argument _ ->  None)"
                       get_opts body_str)))
    | SubE (e1, typ1, typ2) ->
        let* flipsub = get_flipsub () in
        let* () =
          if flipsub then generate_type_conv typ2 typ1
          else generate_type_conv typ1 typ2
        in
        let* e1str = ocaml_of_exp e1 in
        let* typ1str = ocaml_of_typ ~consannot:true typ1 in
        let* typ2str = ocaml_of_typ ~consannot:true typ2 in
        if flipsub then
          return ("(" ^ typ1str ^ "_of_" ^ typ2str ^ " " ^ e1str ^ ")")
        else return ("(" ^ typ2str ^ "_of_" ^ typ1str ^ " " ^ e1str ^ ")")
    | CvtE (e1, typ1, typ2) ->
        let* e1str = ocaml_of_exp e1 in
        (match (typ1, typ2) with
        | `NatT, `IntT | `IntT, `NatT -> return e1str
        | _ ->
          return
            ("(" ^ ocaml_of_numtyp typ2 ^ "_of_" ^ ocaml_of_numtyp typ1 ^ " "
          ^ e1str ^ ")"))
    | OptE eo ->
        if Option.is_none eo then return "None"
        else
          let* eo_str = ocaml_of_exp (Option.get eo) in
          return ("(Some (" ^ eo_str ^ "))")
    | IdxE (e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        (* ints and nats are represented using Z.t's, so list indices must be converted back to ints *)
        return ("(List.nth " ^ e1str ^ " (Z.to_int " ^ e2str ^ "))")
    | LenE e1 ->
        let* e1str = ocaml_of_exp e1 in
        return ("(Z.of_int (List.length " ^ e1str ^ "))")
    | SliceE (e1, start, end_) ->
        let* e1str = ocaml_of_exp e1 in
        let* start_str = ocaml_of_exp start in
        let* end_str = ocaml_of_exp end_ in
        return ("(slice " ^ e1str ^ " (Z.to_int " ^ start_str ^ ") (Z.to_int " ^ end_str ^ "))")
    | CatE (e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        return ("(" ^ e1str ^ " @ " ^ e2str ^ ")")
    | MemE (e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        return ("List.mem " ^ e1str ^ " " ^ e2str)
    | StrE strlist ->
        let* recname = ocaml_of_typ ~consannot:true e.note in
        let* recordstr =
          concat_mapM ";\n  " (ocaml_of_expfield recname) strlist
        in
        return ("{\n  " ^ recordstr ^ "  }")
    | DotE (e1, mixop) ->
        let* e1str = ocaml_of_exp e1 in
        let* typeannot = ocaml_of_typ ~consannot:true e1.note in
        let mixopstr =
          Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ mixop ] ]
        in
        return (e1str ^ "." ^ mixopstr ^ "_" ^ typeannot)
    | UpdE (e1, p, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let flat_path = flatten_path p [] in
        let rec build_update steppaths path_acc : string t =
          match steppaths with
          | [] -> ocaml_of_exp e2
          | DotSP (atom, typname) :: rest ->
              let mixopstr =
                Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ atom ] ]
              in
              let* typannot = ocaml_of_typ ~consannot:true typname in
              let* inner_update =
                build_update rest (path_acc ^ "." ^ mixopstr ^ "_" ^ typannot)
              in
              return
                ("{ " ^ path_acc ^ " with " ^ mixopstr ^ "_" ^ typannot ^ " = "
               ^ inner_update ^ " }")
          | IdxSP idexp :: rest ->
              let* idxstr = ocaml_of_exp idexp in
              let idxstr' = "(Z.to_int " ^ idxstr ^ ")" in
              let* inner_update =
                build_update rest ("(List.nth " ^ path_acc ^ " " ^ idxstr' ^ ")")
              in
              return
                ("(update_at " ^ idxstr ^ " " ^ inner_update ^ " " ^ path_acc
               ^ ")")
          | SliceSP (i, j) :: rest ->
              let* startstr = ocaml_of_exp i in
              let* endstr = ocaml_of_exp j in
              let* inner_update =
                build_update rest
                  ("(slice " ^ path_acc ^ startstr ^ " " ^ endstr ^ ")")
              in
              return
                ("(update_slice " ^ path_acc ^ " " ^ startstr ^ " " ^ endstr
               ^ " " ^ inner_update ^ ")")
        in
        build_update flat_path e1str
    | ExtE (e1, p, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let flat_path = flatten_path p [] in
        let rec build_update steppaths path_acc : string t =
          match steppaths with
          | [] ->
              let* e2str = ocaml_of_exp e2 in
              return (path_acc ^ " @ " ^ e2str)
          | DotSP (atom, typname) :: rest ->
              let mixopstr =
                Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ atom ] ]
              in
              let* typannot = ocaml_of_typ ~consannot:true typname in
              let* inner_update =
                build_update rest (path_acc ^ "." ^ mixopstr ^ "_" ^ typannot)
              in
              return
                ("{ " ^ path_acc ^ " with " ^ mixopstr ^ "_" ^ typannot ^ " = "
               ^ inner_update ^ " }")
          | IdxSP idexp :: rest ->
              let* idxtsr = ocaml_of_exp idexp in
              let* inner_update =
                build_update rest ("(List.nth " ^ idxtsr ^ " " ^ path_acc ^ ")")
              in
              return
                ("(update_at " ^ idxtsr ^ " " ^ inner_update ^ " " ^ path_acc
               ^ ")")
          | SliceSP (i, j) :: rest ->
              let* startstr = ocaml_of_exp i in
              let* endstr = ocaml_of_exp j in
              let* inner_update =
                build_update rest
                  ("(slice " ^ path_acc ^ startstr ^ " " ^ endstr ^ ")")
              in
              return
                ("(update_slice " ^ path_acc ^ " " ^ startstr ^ " " ^ endstr
               ^ " " ^ inner_update ^ ")")
        in
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
  let mixopstr = Util_ocaml.mixop_to_atom_str mixop in
  let label = sanitize_name ~typecons:true ~typename:false mixopstr in
  return (label ^ "_" ^ typname)

(* an "uncase exp typcons" function will strip the typecons from the exp (a variant type). but each constructor can take a different number / type of arguments, meaning uncase_type will have different return types for each cons. so we have to generate a separate function for each cons. *)
and generate_uncase tcs typename : unit t =
  let* typevars = get_typevars () in
  let typevarstr =
    String.concat " " (List.map (fun s -> "'" ^ s) (Set.to_list typevars))
  in
  let gen_one (op, (_, typargs, _), _) : unit t =
    let mixop = Util_ocaml.mixop_to_atom_str op in
    let cons = 
      sanitize_name ~typecons:true ~typename:false
        mixop ^ "_" ^ typename
    in
    let suffix = String.lowercase_ascii (sanitize_name ~typecons:true ~typename:false mixop) in
    let fname = sanitize_name ("uncase_" ^ typename ^ "_" ^ suffix) in
    (* Figure out arg pattern + return expression shape for this constructor *)
    let numargs, pat_args, ret_expr = get_cons_args typargs in
    let body =
      Printf.sprintf "let %s (arg : %s) =\n  match arg with\n  | %s %s -> %s\n"
        fname
        (append_sep typevarstr typename " ")
        cons pat_args ret_expr
    in
    if numargs <> 0 then tell body else return ()
  in
  (* Emit one function per constructor *)
  let* _ = mapM gen_one tcs in
  return ()

(* Get deftype from an alias *)
and lookup (typename : string) : (string * deftyp) option t =
  let* typdef = get_typedef typename in
  match typdef with
  | Some { it = id, _, { it = InstD (_, _, dt); _ } :: _; _ } ->
      return (Some (id.it, dt))
  | _ -> return None

(* Resolve a typ to a StructT fields if it denotes a record type.
   Follows aliases. *)
and resolve_struct (typname : typ) (toplvl : bool) :
    (string * typfield list) option t =
  match typname.it with
  | VarT (tid, _) -> (
      let* typedef = lookup tid.it in
      match typedef with
      | Some (id, dt) -> (
          match dt.it with
          | AliasT t' -> resolve_struct t' toplvl
          | StructT fields -> return (Some (id, fields))
          | VariantT _ -> return None)
      | None -> return None)
  | IterT (_, iter) -> (
      if toplvl then return None
      else match iter with Opt -> return None | _ -> return (Some ("", []))
        (* this is just used to check if something is composable so we don't need the name *)
      )
  | _ -> return None

(* Follow aliases to resolve a variant type. 
    For example, if type A = alias B and B = CONS of <args>, then CONS is annotated with "B", i.e. we use CONS_B. Whenever type A is used, CONS should _still_ be annotated with B and not A, as A does not have its own constructors. *)
and resolve_variant (typname : typ) : typ option t =
  match typname.it with
  | VarT (tid, _) -> (
      let tid = (sanitize_name tid.it) in
      let* typedef = lookup tid in
      match typedef with
      | Some (_, dt) -> (
          match dt.it with
          | AliasT t' -> resolve_variant t'
          | StructT _ -> return None
          | VariantT _ -> return (Some typname))
      | None -> (*Printf.printf "Type %s not found\n" tid.it;*) return None)
  | TupT et when List.length et = 1 -> return (Some typname)
  | BoolT -> (*Printf.printf "type is: booltype\n";*) return None
  | NumT _ -> (*Printf.printf "type is: numt\n";*) return None
  | TextT -> (*Printf.printf "type is: text\n";*) return None
  | TupT et ->
      (*Printf.printf "type is: tupt; len: %d\n" (List.length et);*) return None
  | IterT _ -> (*Printf.printf "type is: iter\n";*) return None

and is_composable tfs : bool t =
  match tfs with _, (_, inner_type, _), _ -> composable_typ inner_type

and composable_typ (t : typ) : bool t =
  match t.it with
  | IterT (_, iter) -> (
      match iter with Opt -> return false | _ -> return true)
  | _ -> (
      let* tfs = resolve_struct t false in
      match tfs with
      | Some (_, fields) -> allM is_composable fields
      | None -> return false)

and typ_is_list (typname : typ) : bool t =
  let* tfs = resolve_struct typname false in
  match tfs with
  | Some (_, []) -> return true
  | Some _ -> return false
  | None -> error typname.at "Non-composable type: shouldn't happen."

and build_fields (tfs : typfield list) typename : unit t =
  (* Verify every field is composable *)
  let* composable = allM is_composable tfs in
  if not composable then return ()
  else
    let* fields =
      concat_mapM ";\n"
        (fun (a, (_, ft, _), _) ->
          let record =
            Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ a ] ]
          in
          let fieldname = record ^ "_" ^ typename in
          let* is_list = typ_is_list ft in
          let* fieldtype = ocaml_of_typ ~consannot:true ft in
          let rhs =
            if is_list then Printf.sprintf "r1.%s @ r2.%s" fieldname fieldname
            else
              Printf.sprintf "compose_%s r1.%s r2.%s" fieldtype fieldname
                fieldname
          in
          return (Printf.sprintf "  %s = %s" fieldname rhs))
        tfs
    in
    tell
      (Printf.sprintf "let compose_%s (r1 : %s) (r2 : %s) = {\n%s\n}" typename
         typename typename fields)

(* Assuming that the top-level is a struct. The nested fields may be lists or structs *)
and generate_compose (dt : deftyp) (typename : string) : unit t =
  match dt.it with
  | StructT tfs -> build_fields tfs typename
  | AliasT inner_type -> (
      let* tfs = resolve_struct inner_type true in
      match tfs with
      | Some (id, fields) ->
          (* call compose for the type that is aliased by this type *)
          tell
            (Printf.sprintf
               "let compose_%s (r1 : %s) (r2 : %s) = compose_%s r1 r2" typename
               typename typename (sanitize_name id))
      | None -> return ())
  | VariantT _ -> return ()

and ocaml_of_expfield typename (a, e) : string t =
  let* estr = ocaml_of_exp e in
  return
    (Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ a ] ]
    ^ "_" ^ typename ^ " = " ^ estr)

and ocaml_of_iter iter : string t =
  match iter with
  | Opt -> return "option"
  | List -> return "list"
  | List1 -> return "List1" (* TODO !!!! *)
  | ListN (e, id_opt) ->
      let* e_str = ocaml_of_exp e in
      let id_str =
        match id_opt with
        | Some id ->
            "Some " ^ "\"" ^ id.it ^ "\"" (* TODO or sanitize_name id *)
        | None -> "None"
      in
      return ("ListN (" ^ e_str ^ ", " ^ id_str ^ ")")

(* For a variant type type V = A | B ..., we annotate the constructors with the typename like A_V, B_V, etc (since OCaml type inference is not accurate with duplicate constructors). A constructor annotation does not need type arguments. *)
and ocaml_of_typ ?(typearg = false) ?(consannot = false) (t : typ) : string t =
  match t.it with
  | VarT (id, args) ->
      let name = sanitize_name id.it in
      let* argstr = ocaml_of_args args ~typearg:true in
      let* is_typevar = is_typevar (sanitize_name id.it) in
      if is_typevar then return ("'" ^ name)
      else if consannot then return name
      else return (append_sep argstr name " ")
  | BoolT -> return "bool"
  | NumT numtype -> return (ocaml_of_numtyp numtype)
  | TextT -> return "string"
  | TupT ets ->
      if List.length ets = 0 then return "unit"
      else concat_mapM " * " (ocaml_of_typbind ~typearg ~consannot) ets
  | IterT (t1, iter) ->
      let* t1str = ocaml_of_typ ~typearg ~consannot t1 in
      let* iterstr = ocaml_of_iter iter in
      return (t1str ^ " " ^ iterstr)

and ocaml_of_typbind ?(typearg = false) ?(consannot = false) (e, t) = ocaml_of_typ ~typearg ~consannot t

(* funcdef/funcall refer to whether the argument is part of a function definition or function call. When _defining_ a function, an argument can only be a (possibly super/sub typed or cased) variable, but when calling functions, it can be any expr. We ignore dependent types for now so type variables in func calls/defs are ignored.
typearg refers to whether the arg is from a type declaration, like: "type x list", or type defintion, like: "type a = Cons of x" OR "type a = nat list". right now, we only support arguments that are types themselves (polymorphic types). we dont support an arg like "N: nat" (dependent types). *)
and ocaml_of_arg ?(typearg = true) ?(funcdef = false) ?(funccall = false) a =
  match a.it with
  | ExpA e ->
      ocaml_of_exp ~typearg ~funcdef ~funccall e
  | TypA t ->
      if not (funccall || funcdef) then ocaml_of_typ ~typearg t else return ""
  | DefA id -> return ((sanitize_name id.it) ^ "_fn")
  | GramA g -> return "TODO: Gram in arg not supported"

and ocaml_of_args ?(typearg = true) ?(funcdef = false) ?(funccall = false) =
  function
  | [] -> return ""
  | as_ -> concat_mapM " " (ocaml_of_arg ~typearg ~funcdef ~funccall) as_

and ocaml_of_bool_binop = function
  | `AndOp -> "&&"
  | `OrOp -> "||"
  | `ImplOp -> "TODO: ImplOp"
  | `EquivOp -> "TODO: EquivOp"

and ocaml_of_num_binop ?(float = false) op =
  match op with
  | `AddOp -> if float then "+." else "Z.add"
  | `SubOp -> if float then "-." else "Z.sub"
  | `MulOp -> if float then "*." else "Z.mul"
  | `DivOp -> if float then "/." else "Z.div"
  | `ModOp -> if float then "mod" else "Z.rem"
  | `PowOp -> if float then "**" else "Z.pow"

and ocaml_of_binop ?(float = false) = function
  | #Bool.binop as op -> ocaml_of_bool_binop op, true
  | #Num.binop as op -> ocaml_of_num_binop ~float op, false

and ocaml_of_bool_unop = function `NotOp -> "not"

and ocaml_of_unop ?(float = true) = function
  | #Bool.unop as op -> ocaml_of_bool_unop op, true
  | #Num.unop as op -> 
    begin match op with
    | `PlusOp when not float -> "", false
    | `MinusOp when not float -> "Z.neg", false
    | _ -> Num.string_of_unop op ^ ".", true
    end

let get_idx_list (iterlist : (id * exp) list) id_opt region =
  let idx_str =
    match id_opt with
    | Some id -> id.it
    | None -> "(* TODO: no iterator variable *)"
  in
  let idx_list = List.filter (fun (id, _) -> id.it = idx_str) iterlist in
  match idx_list with
  | [] -> return ""
  | [ (_, e) ] -> ocaml_of_exp e
  | _ ->
      error region
        ("Index variable " ^ idx_str ^ " can only occur once in binder list")

let gen_case_arm i e : string t =
  match e.it with
  | VarE _ -> return (Printf.sprintf "freshvar_%d" i)
  | SubE (e1, t1, t2) ->
      let* t1str = ocaml_of_typ t1 in
      let* t2str = ocaml_of_typ t2 in
      let* () = generate_type_conv t1 t2 in
      return (Printf.sprintf "(%s_of_%s freshvar_%d)" t1str t2str i)
  | _ ->
      return
        "(* TODO: LetPr LHS = CaseE(mixop, TupE es) where some e in es is not \
         a combination of tuples, variables, subtypes or supertypes  *)"

let gen_case_arms e : string t =
  match e.it with
  | TupE es ->
      let* retvalues = concat_mapMi ", " gen_case_arm es in
      return ("Some (" ^ retvalues ^ ")")
  | _ ->
      (*gen_case_arm 0 e*)
      error e.at "LetPr LHS CaseE(mixop, e) ill-formed: e must be a Tuple"

let rec ocaml_of_prems (prems : prem list) : string t =
  concat_mapM "\n"
    (function
      | p -> (
          match p.it with
          | LetPr (lhs, rhs, vars) -> (
              let* () = add_knowns (List.map sanitize_name vars) in
              let* lhs_str = ocaml_of_exp lhs in
              let* rhs_str = ocaml_of_exp rhs in
              match lhs.it with
              | VarE id ->
                  return (Printf.sprintf "  let %s = %s in" lhs_str rhs_str)
              | CaseE (mixop, e) ->
                  (* this can fail and raise a Match Failure exception, which will be caught by the try_clauses function *)
                  let let_lhs = String.concat ", " (List.map sanitize_name vars) in
                  let* mixopstr = ocaml_of_mixop mixop rhs.note in
                  return
                    (Printf.sprintf "  let %s (%s) = %s in" mixopstr let_lhs
                       rhs_str)
              | OptE (Some { it = VarE id; _ }) ->
                  (* Option.get can raise (not sure?) Invalid_argument but this will be caught by the try_clauses function *)
                  let lhs_str = sanitize_name id.it in
                  return
                    (Printf.sprintf "  let %s = Option.get (%s) in" lhs_str
                       rhs_str)
              | IterE ({ it = VarE lhs_var; _ }, (Opt, xes)) -> (
                  match xes with
                  (* x?{x <- `x?`} = y; it looks like `x?` just takes the value of y - translating to `x? = y` for now. *)
                  | [ (varname, listname) ] ->
                      let* liststr = ocaml_of_exp listname in
                      let* () = add_known liststr in
                      return
                        (Printf.sprintf "  let %s = %s in\n" liststr rhs_str)
                  | _ ->
                      return
                        "(* TODO: LetPr LHS is IterOpt with multiple bindings \
                         *)")
              | SubE (lhs', t1, t2) ->
                  let* () = generate_type_conv t2 t1 in
                  let* t1name = ocaml_of_typ t1 in
                  let* t2name = ocaml_of_typ t2 in
                  let* lhs_str = ocaml_of_exp lhs' in
                  return
                    (Printf.sprintf "  let %s = %s_of_%s (%s) in" lhs_str t1name
                       t2name rhs_str)
              | _ ->
                  error p.at
                    "LetPr ill-formed: LHS must be one of: variable, optional \
                     value/iterator, cased expression.")
          | IfPr cond ->
              let* cond_str = ocaml_of_exp cond in
              return
                (Printf.sprintf "  if not (%s) then raise CondFailed else"
                   cond_str)
          | RulePr _ -> return "(* TODO: RulePr *)"
          | ElsePr -> return ""
          | IterPr (prems, (iter, iterlist)) -> (
              (* if x* is known then x <- x* is an inflow.
        Otherwise, it is an outflow. *)
              let* prev_knowns = get_knowns in
              (* any inner premise needs to know what the inflows are. these inflows will not affect the output of the `partition` function below and will be removed by the reset in the end before adding the outflows - they are only in scope for the inner premises. *)
              let inflows =
                List.map
                  (fun (x, _) -> sanitize_name x.it)
                  (List.filter
                     (fun (id, e) ->
                       Il.Free.Set.subset
                         (Set.map sanitize_name (Valid.free_vars_exp e))
                         prev_knowns)
                     iterlist)
              in
              let* () = add_knowns inflows in
              (* this will add new things to knowns, but their scope is limited *)
              let* prem_strs = ocaml_of_prems prems in
              let* new_knowns = get_knowns in
              let partition id_opt =
                List.partition
                  (fun (id', e) ->
                    match id_opt with
                    | Some id ->
                        Il.Free.Set.subset
                          (Set.map sanitize_name (Valid.free_vars_exp e))
                          new_knowns
                        || id.it = id'.it
                    | None ->
                        Il.Free.Set.subset
                          (Set.map sanitize_name (Valid.free_vars_exp e))
                          new_knowns)
                  iterlist
              in
              match iter with
              | Opt ->
                  let inflows, outflows = partition None in
                  are_valid outflows;
                  let inflow_vars =
                    String.concat " "
                      (List.map (fun (id, _) -> sanitize_name id.it) inflows)
                  in
                  let* inflow_lists =
                    concat_mapM " " ocaml_of_exp (List.map snd inflows)
                  in
                  let inflow_lists = inflow_lists in
                  let outflow_vars =
                    String.concat ", "
                      (List.map (fun (id, _) -> sanitize_name id.it) outflows)
                  in
                  let* outflow_lists =
                    concat_mapM ", " ocaml_of_exp (List.map snd outflows)
                  in
                  (* reset knowns: whatever was added by the inner premises can now be removed *)
                  let* () = set_knowns prev_knowns in
                  (* now add whatever outflows *)
                  let* outflow_listvars =
                    mapM ocaml_of_exp (List.map snd outflows)
                  in
                  let* () = add_knowns outflow_listvars in
                  if List.length outflows = 0 then
                    (* if there are no outflows, the nested premises must be "ifs" *)
                    return
                      (Printf.sprintf
                         "  let _ = map_opt%d (fun %s -> %s ()) %s in"
                         (List.length inflows) inflow_vars prem_strs
                         inflow_lists)
                  else
                    return
                      (Printf.sprintf
                         "  let %s = unzip_opt%d (map_opt%d (fun %s -> %s %s) \
                          %s) in"
                         outflow_lists (List.length outflows)
                         (List.length inflows) inflow_vars prem_strs
                         outflow_vars inflow_lists)
              | List -> return "(* TODO: IterPr List *)"
              | List1 -> return "(* TODO: IterPr List1 *)"
              | ListN (e, id_opt) ->
                  let inflows, outflows = partition id_opt in
                  are_valid outflows;
                  let* list_len = ocaml_of_exp e in
                  let* idx_list = get_idx_list iterlist id_opt p.at in
                  let* freshvar = get_freshvar () in
                  let idx_listname =
                    if idx_list = "" then freshvar ^ "_list" else idx_list
                  in
                  let def_idx_list =
                    Printf.sprintf "  let %s = List.init (Z.to_int (%s)) (fun i -> Z.of_int i) in\n"
                      idx_listname list_len
                  in
                  let idx_var, idx_listvar =
                    if idx_list = "" then ([ freshvar ], freshvar ^ "_list ")
                    else ([], "")
                  in
                  let inflow_vars =
                    String.concat " "
                      (idx_var
                      @ List.map (fun (id, _) -> sanitize_name id.it) inflows)
                  in
                  let* inflow_lists =
                    concat_mapM " " ocaml_of_exp (List.map snd inflows)
                  in
                  let inflow_lists = idx_listvar ^ inflow_lists in
                  let outflow_vars =
                    String.concat ", "
                      (List.map (fun (id, _) -> sanitize_name id.it) outflows)
                  in
                  let* outflow_lists =
                    concat_mapM ", " ocaml_of_exp (List.map snd outflows)
                  in
                  (* reset knowns: whatever was added by the inner premises can now be removed *)
                  let* () = set_knowns prev_knowns in
                  (* now add whatever outflows *)
                  let* outflow_listvars =
                    mapM ocaml_of_exp (List.map snd outflows)
                  in
                  let* () = add_knowns outflow_listvars in
                  let inflowsize =
                    if idx_list = "" then List.length inflows + 1
                    else List.length inflows
                  in
                  if List.length outflows = 0 then
                    (* if there are no outflows, the nested premises must be "ifs" *)
                    return
                      (def_idx_list
                      ^ Printf.sprintf
                          "  let _ = map%d (fun %s -> %s Some ()) %s in"
                          (List.length inflows) inflow_vars prem_strs
                          inflow_lists)
                    else
                    let* () = gen_unzip_cls (List.length outflows) in
                    return
                      (def_idx_list
                      ^ Printf.sprintf
                          "  let %s = unzip%d (map%d (fun %s -> %s %s) %s) in"
                          outflow_lists (List.length outflows)
                          (List.length inflows) inflow_vars prem_strs
                          outflow_vars inflow_lists))))
    prems

let ocaml_of_typ_args t =
  match t.it with
  | TupT [] -> return ""
  | TupT _ -> ocaml_of_typ ~typearg:true t
  | _ ->
      let* argstr = ocaml_of_typ ~typearg:true t in
      return ("(" ^ argstr ^ ")")

(* Hardcoded: calls "dispatch_instr" for the right instr *)
let build_stepcases step =
  let* instrs = get_typedef "instr" in
  let { it = _, _, { it = InstD (_, _, instrsdt); _ } :: _; _ } =
    Option.get instrs
  in
  let (VariantT instr_tcs) = instrsdt.it in
  concat_mapM "\n"
    (fun (op, (_, t, _), _) ->
      (* check: the function name should match exactly with the head of the list in the mixop?? *)
      let funcsuffix =
        sanitize_name ~typename:false
          (Util_ocaml.mixop_to_atom_str [ List.hd op ])
      in
      let consname =
        sanitize_name ~typename:false (Util_ocaml.mixop_to_atom_str op)
      in
      let funcname =
        sanitize_name (Printf.sprintf "Step%s/%s" step funcsuffix)
      in
      let* is_defined = is_defined funcname in
      let* args = ocaml_of_typ_args t in
      let args_str = if args = "" then "" else " _" in
      if is_defined then
        return
          (Printf.sprintf "  | %s_instr%s -> %s_fn instrs" consname args_str
             funcname)
      else
        return
          (Printf.sprintf "  | %s_instr%s -> failwith \"%s not defined.\""
             consname args_str funcname))
    instr_tcs

let build_dispatch step =
  let suffix = if step = "" then "" else "_" ^ step in
  let* instr_cases = build_stepcases suffix in
  let rettype = if step = "" then "config" else "instr list" in
  return
    [
      Printf.sprintf
        "dispatch_step%s_fn instr instrs : (%s) =\n\
        \  if (Builtin.use_step%s instr) then match instr with \n\
         %s\n\
        \  else failwith \"Instruction is not a step%s instruction.\"\n"
        suffix rettype suffix instr_cases step;
    ]

(* Each clause is it's own function *)
let ocaml_of_func_def (fdef : func_def) : string list t =
  let id, osubid, params, rettyp, clauses, _ = fdef.it in
  let id' = (match osubid with | None -> id | Some subid -> (id.it ^ "_slash" ^ subid.it $ id.at)) in
  let name = sanitize_name id'.it in
  let* () = add_funcdef name in
  let params' = List.filter rmv_nonexp params in
  let num_params = List.length params' in
  let* () = gen_try_cls num_params in
  let typevars = typevars_of_params params in
  let typevar_args =
    String.concat " "
      (List.map (fun tv -> Printf.sprintf "f_%s g_%s" tv tv) (Set.to_list typevars))
  in
  let argslist =
    if num_params = 0 then "()"
    else
      String.concat " " (List.init num_params (fun i -> Printf.sprintf "a%d" i))
  in
  let argslist' =
    if num_params = 0 then ""
    else
      String.concat " " (List.init num_params (fun i -> Printf.sprintf "a%d" i))
  in
  let full_argslist  = append_sep typevar_args argslist  " " in
  let full_argslist' = append_sep typevar_args argslist' " " in
  (* Built-in functions like module_ok, reftype_sub etc are hardcoded to call their meta-interpeter implementations. Other builtins like dispatch, use_step_*, Step_read_throw are either generated or hardcoded in OCaml. *)
  if List.length clauses = 0 then
    match id.it with
    | "Step_read_throw_ref_handler" ->
        return [ name ^ "_fn = uc_step_read_slashthrow_ref_fn\n" ]
    | "dispatch_step_pure" -> build_dispatch "pure"
    | "dispatch_step_read" -> build_dispatch "read"
    | "dispatch_step" -> build_dispatch ""
    | s when (String.starts_with ~prefix:"use_step" s) -> (
        return [ name ^ "_fn = Builtin." ^ name ^ "\n" ]
      )
    | _ -> (
      let* () = add_builtin name in
      let param_types = List.filter_map (fun p ->
        match p.it with
        | ExpP (_, t) -> Some t
        | _ -> None
      ) params' in
      let* () = set_typevars typevars in
      let wrap_arg a = match !Parser_ocaml.backend with
        | IL -> Printf.sprintf "(Il.Ast.ExpA (%s) $ no)" a
        | VL -> Printf.sprintf "(Backend_animation.Value.ValA (%s))" a
      in
      let* args =
        mapM (fun (i, t) ->
          let* tr = Parser_ocaml.gen_typarg_il t in
          return (Printf.sprintf "%s a%d" tr i)
        ) (List.mapi (fun i t -> (i, t)) param_types)
      in
      let args_str = String.concat "; " (List.map wrap_arg args) in
      let* ret_tr = Parser_ocaml.gen_ocaml_of_typ_fn rettyp in
      let* () = set_typevars Set.empty in
      match !Parser_ocaml.backend with
      | IL ->
      return [ Printf.sprintf "%s_fn %s = %s (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func %S [%s])))\n"
               name full_argslist ret_tr id.it args_str ]
      | VL -> return [ Printf.sprintf "%s_fn %s = %s (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.call_func %S [%s])))\n"
               name full_argslist ret_tr id.it args_str ])
  else if (id.it = "Step" && osubid = None) then return [ "uc_step a0 = step a0\n" ]
  else
    let* () = set_typevars typevars in
    let* rettypstr = ocaml_of_typ rettyp in
    let* clause_funcs =
      mapMi
        (fun i fclause ->
          let _, clause = fclause in
          match clause.it with
          | DefD (_, params, body, prems) ->
              let* () = set_knowns Set.empty in
              catchM
                (fun () ->
                  let params' = List.filter rmv_nonexparg params in
                  let num_params = List.length params' in
                  let* () = set_flipsub true in
                  let* argnames =
                    if num_params = 0 then return "()"
                    else
                      ocaml_of_args ~typearg:false ~funcdef:true params
                  in
                  let* () = set_flipsub false in
                  let* prems_block = ocaml_of_prems prems in
                  let* retvalue = ocaml_of_exp ~retval:true body in
                  let* typecasts = get_typecasts () in
                  let* () = set_typecasts "" in
                  let bodycode = typecasts ^ prems_block in
                  let full_argnames = append_sep typevar_args argnames " " in
                  (*let bodycode = Printf.sprintf "  Printf.printf \"Calling %s (Clause %d)\n%%!\";\n" name (i+1) ^ bodycode in*)
                  if bodycode = "" then
                    return
                      (Printf.sprintf "clause_%s_%d %s : %s = %s\n" name i
                         full_argnames rettypstr retvalue)
                  else
                    return
                      (Printf.sprintf "clause_%s_%d %s : %s =\n%s\n  %s\n" name
                         i full_argnames rettypstr bodycode retvalue))
                (function
                  | CannotAnimate | CannotSplit _ ->
                      let argnames =
                        String.concat " "
                          (List.init (List.length params) (fun i ->
                               Printf.sprintf "unanimated%d" i))
                      in
                      let full_argnames = append_sep typevar_args argnames " " in
                      return
                        (Printf.sprintf
                           "clause_%s_%d %s = raise (UnanimatedArg %S)\n"
                           name i full_argnames name)
                  | e -> Printf.eprintf "Uncaught exception in clause_%s_%d: %s\\n" name i (Printexc.to_string e); raise e))
        clauses
    in
    let* () = set_typevars Set.empty in
    let clause_calls =
    List.mapi (fun i _ ->
      if typevar_args = "" then Printf.sprintf "clause_%s_%d" name i
      else Printf.sprintf "(clause_%s_%d %s)" name i typevar_args
    ) clauses
    in
    let clause_names = String.concat ";\n  " clause_calls in
    let err_msg = "function: " ^ name in
    let main_func =
      (*Printf.sprintf "%s_fn %s = (Printf.printf \"Calling %s\\n\"); try_clauses_%d [\n  %s\n] %s %S 1" name full_argslist name*)
      Printf.sprintf "%s_fn %s = try_clauses_%d [\n  %s\n] %s %S 1" name full_argslist
    num_params clause_names argslist' err_msg
    in
    return (clause_funcs @ [ main_func ])

(* ignoring the dependent type annotations for now *)
let ocaml_of_typcase typename (op, (_, t, _), _hints) =
  let* args_str = ocaml_of_typ_args t in
  if args_str = "" then
    return
      (sanitize_name ~typecons:true ~typename:false
         (Util_ocaml.mixop_to_atom_str op)
      ^ "_" ^ typename)
  else
    return
      (sanitize_name ~typecons:true ~typename:false
         (Util_ocaml.mixop_to_atom_str op)
      ^ "_" ^ typename ^ " of " ^ args_str)

(* all fields are annotated with "_typename" because OCaml cannot directly infer the type when record fields are duplicated across types *)
let ocaml_of_typfield name (atom, (_bs, t, _prems), _hints) =
  let* typ_str = ocaml_of_typ t in
  return
    (Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ atom ] ]
    ^ "_" ^ name ^ ": " ^ typ_str)

let ocaml_of_deftyp dt name =
  let* () = generate_compose dt name in
  match dt.it with
  | AliasT t ->
      (*Printf.printf "AliasT type %s\n" name;*)
      let* t_str = ocaml_of_typ t in
      return t_str
  | StructT tfs ->
      let* tfs_str = concat_mapM ";\n  " (ocaml_of_typfield name) tfs in
      return ("{\n  " ^ tfs_str ^ "\n}")
  | VariantT tcs ->
      let* () = generate_uncase tcs name in
      concat_mapM "\n  | " (ocaml_of_typcase name) tcs

let ocaml_of_typedef (td : type_def) : (string * string * string) t =
  let { it = id, ps, insts; _ } = td in
  let* () = add_typedef (sanitize_name id.it) td in
  let* () = set_typevars (typevars_of_params ps) in
  let name = sanitize_name id.it in
  match insts with
  | [ { it = InstD (_, as_, dt); _ } ] ->
      let* args_str = ocaml_of_args ~typearg:true as_ in
      let space = if args_str = "" then "" else " " in
      let* dt_str = ocaml_of_deftyp dt name in
      let* ocaml_of = Parser_ocaml.gen_ocaml_of_dt dt name args_str in
      let* ocaml_to = Parser_ocaml.generate_type_il dt name args_str in
      let* () = set_typevars Set.empty in
      return
        ( append_sep args_str name " " ^ " = " ^ dt_str ^ "\n",
          ocaml_of, ocaml_to)
  | _ -> error td.at "Multi-instance types not supported"

let ocaml_of_dl_def (def : dl_def) : (string * string) t =
  match def with
  | TypeDef typedef ->
      let* typestr, type_translation, il_translation = ocaml_of_typedef typedef in
      let* () = if type_translation <> "" then add_construct ("let " ^ type_translation) else return () in
      let* () = if il_translation   <> "" then add_construct ("let " ^ il_translation)   else return () in
      return ("", "type " ^ typestr)
  | FuncDef fdef ->
      let* funcslist = ocaml_of_func_def fdef in
      let funcstr = "let " ^ String.concat "\nlet " funcslist in
      let id, _, _, _, _, _ = fdef.it in
      let steps =
        if sanitize_name id.it = "steps" then
          "let uc_steps_fn a0 = steps_fn a0\n"
        else ""
      in
      let funcstr = append_sep funcstr steps "\n" in
      return (funcstr ^ "\n", "")
  | RecDef dl_defs -> (
      match dl_defs with
      | [] -> return ("", "")
      | FuncDef _ :: _ ->
          let fdefs =
            List.map
              (fun def ->
                match def with
                | FuncDef fdef -> fdef
                | _ ->
                    error (get_dl_def_region def)
                      "RecDef not consistent: should not happen")
              dl_defs
          in
          let* func_blocks = mapM ocaml_of_func_def fdefs in
          let func_strs = List.concat func_blocks in
          if func_strs = [] then return ("", "")
          else
            return ("let rec " ^ String.concat "\nand " func_strs ^ "\n", "")
      | TypeDef _ :: _ ->
        let typedefs =
          List.map
            (fun def ->
              match def with
              | TypeDef typedef -> typedef
              | _ ->
                  error (get_dl_def_region def)
                    "RecDef not consistent: should not happen")
          dl_defs
        in
        let* results = mapM ocaml_of_typedef typedefs in
        let typestrs        = List.map (fun (a, _, _) -> a) results in
        let type_translations = List.map (fun (_, b, _) -> b) results in
        let il_translations   = List.map (fun (_, _, c) -> c) results in
        let typestrs_combined = String.concat "\nand " typestrs in
        let ocaml_of_combined = String.concat "\nand " (List.filter (fun s -> s <> "") type_translations) in
        let il_of_combined    = String.concat "\nand " (List.filter (fun s -> s <> "") il_translations) in
        let* () = if ocaml_of_combined <> "" then add_construct ("let rec " ^ ocaml_of_combined) else return () in
        let* () = if il_of_combined    <> "" then add_construct ("let rec " ^ il_of_combined)    else return () in
        return ("", "type " ^ typestrs_combined))

let ocaml_of_dl_defs (defs : dl_def list) : (string * string) t =
  (*Printf.printf "Calling hardcode step...\n";*)
  let processed_defs = hardcode_step defs in
  (* todo: refactor this after removing type family stuff *)
  let processed_defs' = reorder_inv_proj processed_defs "inv_proj_num__0" "proj_num__0" in
  (*Printf.printf "length after resolving typ fams: %d...\n"(List.length processed_defs');*)
  let* def_strs : (string * string) list =
    mapM ocaml_of_dl_def processed_defs'
  in
  let func_defs, type_defs = List.split def_strs in
  let func_str = concat_nonempty "\n" func_defs in
  let type_str = concat_nonempty "\n" type_defs in
  return (func_str, type_str)

let generate_ocaml (dl_defs : dl_def list) : string * string * string * string =
  let main =
    "open Backend_animation.Util_ocaml\n"
    (*^ "open Backend_animation.Util_ocaml.NumConversions\n"*)
    ^ "open Builtin\n\n"
    ^ "let (<|>) = Backend_animation.Util_ocaml.mplus\n"
    ^ "let (let*) = Option.bind\n"
  in
  let hardcoded_funcs = match !Parser_ocaml.backend with
    | IL -> Printf.sprintf "\
    let uc_ref_ok_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func \"Ref_ok\" [(Il.Ast.ExpA (il_of_store a0) $ no); (Il.Ast.ExpA (il_of_ref a1) $ no); (Il.Ast.ExpA (il_of_reftype a2) $ no)])))\n\n\
    let uc_val_ok_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func \"Val_ok\" [(Il.Ast.ExpA (il_of_store a0) $ no); (Il.Ast.ExpA (il_of_val_ a1) $ no); (Il.Ast.ExpA (il_of_valtype a2) $ no)])))\n\n\
    let uc_reftype_sub_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func \"Reftype_sub\" [(Il.Ast.ExpA (il_of_context a0) $ no); (Il.Ast.ExpA (il_of_reftype a1) $ no); (Il.Ast.ExpA (il_of_reftype a2) $ no)])))\n\n\
    let uc_heaptype_sub_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func \"Heaptype_sub\" [(Il.Ast.ExpA (il_of_context a0) $ no); (Il.Ast.ExpA (il_of_heaptype a1) $ no); (Il.Ast.ExpA (il_of_heaptype a2) $ no)])))\n\n\
    let uc_module_ok_fn a0 = ocaml_of_moduletype (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func \"Module_ok\" [(Il.Ast.ExpA (il_of_module_ a0) $ no)])))\n\n\
    let uc_externaddr_ok_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter.OptMonad.run_opt (Backend_animation.Interpreter.call_func \"Externaddr_ok\" [(Il.Ast.ExpA (il_of_store a0) $ no); (Il.Ast.ExpA (il_of_externaddr a1) $ no); (Il.Ast.ExpA (il_of_externtype a2) $ no)])))"
  | VL -> Printf.sprintf "
    let uc_ref_ok_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.ref_ok [Backend_animation.Value.ValA (vl_of_store a0); Backend_animation.Value.ValA (vl_of_ref a1); Backend_animation.Value.ValA (vl_of_reftype a2)])))\n\n\
    let uc_val_ok_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.val_ok [Backend_animation.Value.ValA (vl_of_store a0); Backend_animation.Value.ValA (vl_of_val_ a1); Backend_animation.Value.ValA (vl_of_valtype a2)])))\n\n\
    let uc_reftype_sub_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.reftype_sub [Backend_animation.Value.ValA (vl_of_context a0); Backend_animation.Value.ValA (vl_of_reftype a1); Backend_animation.Value.ValA (vl_of_reftype a2)])))\n\n\
    let uc_heaptype_sub_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.heaptype_sub [Backend_animation.Value.ValA (vl_of_context a0); Backend_animation.Value.ValA (vl_of_heaptype a1); Backend_animation.Value.ValA (vl_of_heaptype a2)])))\n\n\
    let uc_module_ok_fn a0 = ocaml_of_moduletype (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.module_ok [Backend_animation.Value.ValA (vl_of_module_ a0)])))\n\n\
    let uc_externaddr_ok_fn a0 a1 a2 = ocaml_of_bool (Option.get (Backend_animation.Interpreter_v.OptMonad.run_opt (Backend_animation.Interpreter_v.externaddr_ok [Backend_animation.Value.ValA (vl_of_store a0); Backend_animation.Value.ValA (vl_of_externaddr a1); Backend_animation.Value.ValA (vl_of_externtype a2)])))"
  in
  let typeimports = "type nat = Z.t\ntype int = Z.t\ntype rat = float\ntype real = float\n\n" in
  let (funcdefs, typedefs), typeconvfuncs, parser =
    eval (ocaml_of_dl_defs dl_defs)
  in
  (main ^ hardcoded_funcs ^ funcdefs, typeimports ^ typedefs, typeconvfuncs, parser)
