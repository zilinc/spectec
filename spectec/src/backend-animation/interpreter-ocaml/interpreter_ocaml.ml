open Il.Ast
open Il.Print
open Util.Source
open Xl
open Def
open Util_ocaml
open Util.Error
open Util_ocaml.TypeM

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
  (* | RuleDef rd       -> rd.at *)

(* type variables need to be prefixed with ' *)
let typevars_of_params (ps : param list) : Set.t =
  ps
  |> List.filter_map (fun p ->
         match p.it with TypP id -> Some (sanitize_name id.it) | _ -> None)
  |> Set.of_list

(* hardcoded things: `Step` needs to be re-defined manually to call `step`. This makes a group of functions (specifically those on any call path from `step` to `Step`) mutually recursive. Since these functions are not recursive in the original spec, we need to mark them as such manually. *)
let find_recdefs (funcdefs : dl_def list) =
  (*Printf.printf "finding mutually recursive functions ...\n";
  flush stdout; *)
  let visited = Hashtbl.create (List.length funcdefs) in
  let rec dfs visited start target =
    (*Printf.printf "start is: %s\n" start;
    flush stdout; *)
    let fdef = find_fdef funcdefs start in
    match Hashtbl.find_opt visited start with
    | Some children -> children
    | None ->
        Hashtbl.add visited start Set.empty;
        (* if this call-path has reached `Step`, we can add to the recursive functions *)
        if start = target then (
          let s = Set.singleton start in
          Hashtbl.add visited start s;
          (*Printf.printf "%s reached: adding to visited\n" target;*)
          s)
        else (
          Hashtbl.add visited start Set.empty;
          (* to avoid cycles *)
          let children = f_calls fdef in
          (*Printf.printf "%s calls: %s\n" start (String.concat ", " (Set.to_list children));*)
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
  (*Printf.printf "Hardcoding Step function...\n";
  flush stdout; *)
  let rec_funcs = find_recdefs funcdefs in
  (*Set.iter (Printf.printf "Mutually recursive function: %s\n") rec_funcs;*)
  (* we need to insert the recursive functions at the (last) index we removed them from *)
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
  (*Printf.printf "length of recdefs: %d; length of total list: %d; inserting at position: %d\n" (List.length recdefs) (List.length funcdefs) insert;
  Printf.printf "taking first %d elems of list\n" (insert - List.length recdefs);
  Printf.printf "taking last %d elems of list\n" (List.length funcdefs - insert);
  Printf.printf "inserted recdef at index: %d\n" insert;*)
  (*List.take (insert - List.length recdefs) rest
  @ [ RecDef recdefs ]
  @ List.drop (insert - List.length recdefs) rest - comment out temporarily for 5.1 *)
  take (insert - List.length recdefs) rest
  @ [ RecDef recdefs ]
  @ drop (insert - List.length recdefs) rest 

(* a typefamily is a type of form `type x = Alias y | Alias z | ... `
   I assume that all instances of a type have the same `deftyp` i.e. they are all aliases, variants or records. For now:
   - Variant instances are just combined (without making their typeconstructors polymorphic).
   - Alias Types are treated as polymorphic variants
   - Record Types are ignored, not sure if these exist *)

(* only called when we already know `inst` is from a multi-instance type *)
let rec get_aliased_types (insts : inst list) : unit t =
  iterM
    (fun inst ->
      let { it = InstD (_, _, dt); _ } = inst in
      match dt.it with
      | AliasT alias_type -> (
          match alias_type.it with
          (* for now we only handle VarT - I am not sure if an alias can be any other type *)
          | VarT (id, _) ->
              (* aliases can be nested, for example, type A = alias B and type B = alias C, in which case every nested alias is polymorphic *)
              let* (Some typedef) = get_typedef (sanitize_name id.it) in
              let { it = _, _, nested_insts; _ } = typedef in
              let* () = get_aliased_types nested_insts in
              add_typ_fam (sanitize_name id.it) typedef
          | _ -> return ())
      | _ -> return ())
    insts

and set_type_families (dl_defs : dl_def list) : unit t =
  iterM
    (fun def ->
      match def with
      | TypeDef typedef -> (
          (* add every type we see to a map because we constantly need to look up definitions by type name *)
          let { it = id, _, insts; _ } = typedef in
          let* () = add_typedef (sanitize_name id.it) typedef in
          (* typefamilies are multi-instance _alias_ types only *)
          match insts with
          | { it = InstD (_, _, { it = AliasT _; _ }); _ } :: rest
            when List.length rest > 0 ->
              let* () = get_aliased_types insts in
              add_typ_fam (sanitize_name id.it) typedef
          | _ -> return ())
      | RecDef defs -> set_type_families defs
      | _ -> return ())
    dl_defs

let rmv_duplicate_cons (typedef : type_def) =
  let { it = id, params, insts; _ } = typedef in
  let fst_inst = List.nth insts 0 in
  let { it = InstD (bs, as_, dt); _ } = fst_inst in
  match dt.it with
  | VariantT _ ->
      let rec aux acc rest =
        match rest with
        | [] -> acc
        | { it = InstD (_, _, { it = VariantT tcs; _ }); _ } :: rest' ->
            let tcs' =
              List.fold_left
                (fun acc (op, bs, ht) ->
                  (* if we have seen this constructor before, ignore it *)
                  if
                    List.exists
                      (fun (op', _, _) ->
                        mixop_to_atom_str op = mixop_to_atom_str op')
                      acc
                  then acc
                  else (op, bs, ht) :: acc)
                acc tcs
            in
            aux tcs' rest'
      in
      let unique_tcs = aux [] insts in
      (* change to a single instance type with unique constructors *)
      {
        typedef with
        it =
          ( id,
            params,
            [
              {
                fst_inst with
                it = InstD (bs, as_, { dt with it = VariantT unique_tcs });
              };
            ] );
      }
  (* if this is not a VariantType, we don't need to do anything *)
  | _ -> typedef

(* a very bad first attempt at replacing all types with their instantiated counterparts, as trying a minimal thing before trying Diego's passes *)
let rec is_eq_typ (t1 : typ) (t2 : typ) =
  match (t1.it, t2.it) with
  | VarT (id1, a1), VarT (id2, a2) ->
      id1.it = id2.it
      && List.length a1 = List.length a2 (* TODO: need to check each arg *)
  | BoolT, BoolT -> true
  | NumT _, NumT _ -> true (* TODO: implement *)
  | TextT, TextT -> true
  | TupT ets1, TupT ets2 ->
      List.length ets1 = List.length ets2
      && List.for_all2
           (fun (_, t1) (_, t2) ->
             (*check_eq_exp e1 e2 &&*) is_eq_typ t1 t2)
           ets1 ets2
  | IterT (t11, iter1), IterT (t21, iter2) ->
      (*let b1 = check_eq_typs t11 t21 in
    let b2 = iter1 = iter2 in 
    Printf.printf "b1: %b and b2: %b\n" b1 b2;*)
      is_eq_typ t11 t21 && iter1 = iter2
  | _ -> false

let is_eq_arg (a1 : arg) (a2 : arg) = 
  match a1.it, a2.it with
  | TypA t1, TypA t2 
  | ExpA {it = SubE (_, t1, _); _}, ExpA {it = SubE (_, t2, _); _} -> is_eq_typ t1 t2
  | _ -> false (* for now idk how it works if a type is instantiated with an expression *)

let is_eq_args (args1 : arg list) (args2 : arg list) =
  List.length args1 = List.length args2
  && List.for_all2 is_eq_arg args1 args2

let rec replace_e (e : exp) =
  let* e' = match e.it with
  | VarE _ | BoolE _ | NumE _ | TextE _ -> return e
  | UnE (op, t, e1) ->
    let* e1' = replace_e e1 in
    return { e with it = UnE (op, t, e1') }
  | BinE (op, t, e1, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = BinE (op, t, e1', e2') }
  | CmpE (op, t, e1, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = CmpE (op, t, e1', e2') }
  | TupE es ->
    let* es' = mapM replace_e es in
    return { e with it = TupE es' }
  | ProjE (e1, i) ->
    let* e1' = replace_e e1 in
    return { e with it = ProjE (e1', i) }
  | CaseE (op, e1) ->
    let* e1' = replace_e e1 in
    return { e with it = CaseE (op, e1') }
  | UncaseE (e1, op) ->
    let* e1' = replace_e e1 in
    return { e with it = UncaseE (e1', op) }
  | OptE eo ->
    let* eo' = match eo with
    | Some e -> let* e' = replace_e e in return (Some e')
    | None -> return None
    in
    return { e with it = OptE eo' }
  | TheE e1 ->
    let* e1' = replace_e e1 in
    return { e with it = TheE e1' }
  | StrE fields ->
    let* fields' = mapM (fun (a, e) -> let* e' = replace_e e in return (a, e')) fields in
    return { e with it = StrE fields' }
  | DotE (e1, a) ->
    let* e1' = replace_e e1 in
    return { e with it = DotE (e1', a) }
  | CompE (e1, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = CompE (e1', e2') }
  | ListE es ->
    let* es' = mapM replace_e es in
    return { e with it = ListE es' }
  | LiftE e1 ->
    let* e1' = replace_e e1 in
    return { e with it = LiftE e1' }
  | MemE (e1, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = MemE (e1', e2') }
  | LenE e1 ->
    let* e1' = replace_e e1 in
    return { e with it = LenE e1' }
  | CatE (e1, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = CatE (e1', e2') }
  | IdxE (e1, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = IdxE (e1', e2') }
  | SliceE (e1, e2, e3) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    let* e3' = replace_e e3 in
    return { e with it = SliceE (e1', e2', e3') }
  | UpdE (e1, p, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = UpdE (e1', p, e2') }
  | ExtE (e1, p, e2) ->
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { e with it = ExtE (e1', p, e2') }
  | CallE (id, args) ->
    let* args' = mapM replace_arg args in
    return { e with it = CallE (id, args') }
  | IterE (e1, it) ->
    let* e1' = replace_e e1 in
    return { e with it = IterE (e1', it) }
  | CvtE (e1, t1, t2) ->
    let* e1' = replace_e e1 in
    return { e with it = CvtE (e1', t1, t2) }
  | SubE (e1, t1, t2) ->
    let* e1' = replace_e e1 in
    return { e with it = SubE (e1', t1, t2) }
  in
  match e'.note.it with
  | VarT (id, args) ->
    let* td = get_typ_fam (sanitize_name id.it) in begin
    match td with
    | Some td ->
      (* this type has multiple instances like: typename(<typeargs>) = AliasT (<othertype>). 
         we will go through its instances to check what type <args> gives us, and explicitly cast typename into <othertype> *)
      let (tid, _, insts) = td.it in
      Printf.printf "type fam found: %s\n" tid.it; 
      (try
        let { it = InstD (_, _, dt); _} = List.find (fun { it = InstD (_, args', _); _} -> (List.iter (fun a -> Printf.printf "arg: %s\n" (Il.Print.string_of_arg a)) args; List.iter (fun a -> Printf.printf "arg': %s\n" (Il.Print.string_of_arg a)) args'); is_eq_args args args') insts in
        match dt.it with 
          | AliasT t -> (
            let new_e = { e' with it = SubE (e', t, e'.note) } in
            Printf.printf "exp replaced. old: %s, new: %s\n" (Il.Print.string_of_exp e') (Il.Print.string_of_exp new_e);
            return { e' with it = SubE ({e' with note = t}, t, e'.note) })
          | _ -> return e' (* I don't think this should happen *)
      with 
        | Not_found -> return e') (* the arg is not a concrete type (it could be a variable, for example - in which case we do not cast at all )*)
    | None -> return e'
    end
  | _ -> return e'

and replace_arg (a : arg) =
  match a.it with
  | ExpA e -> 
    let* e' = replace_e e in
    return { a with it = ExpA e' }
  | _ -> return a

let rec replace_typ (t : typ) =
  match t.it with
  | VarT (id, args) -> 
    (*Printf.printf "in varT %s\n" (sanitize_name id.it);*)
    let* typ_def = get_typ_fam (sanitize_name id.it) in
    (*Printf.printf "after getting type fam\n";*)
    begin match typ_def with 
    | Some td ->
      Printf.printf "Found type family: %s\n%!" (sanitize_name id.it);
      let _, _, insts = td.it in
      (try
        let { it = InstD (_, _, dt); _} = List.find (fun { it = InstD (_, args', _); _} -> (List.iter (fun a -> Printf.printf "arg: %s\n" (Il.Print.string_of_arg a)) args; List.iter (fun a -> Printf.printf "arg': %s\n" (Il.Print.string_of_arg a)) args'); is_eq_args args args') insts in begin
        match dt.it with 
        | AliasT t' -> Printf.printf "type replaced"; return t'
        | _ -> return t end (* I don't think this should happen *)
      with Not_found -> return t) (* the arg is not a concrete type (it could be a variable, for example, in which case we do not cast at all) *)
    | _ -> (*Printf.printf "not a type family: %s\n" (sanitize_name id.it);*) return t
    end
  | TupT ts -> 
    let* ts' = mapM (fun (e, t) -> 
      let* t' = replace_typ t in
      return (e, t')) ts 
    in
    return { t with it = TupT ts' }
  | IterT (itert, iter) -> 
    let* itert' = replace_typ itert in
    return { t with it = IterT (itert', iter) }
  | _ -> (*(Printf.printf "nothing to replace for type: %s \n" (Il.Print.string_of_typ t)); *)return t


let replace_param (p : param) =
  match p.it with
  | ExpP (id, typP) -> 
    let* typP' = replace_typ typP in
    return { p with it = ExpP (id, typP') }
  | _ -> return p (* in a func_def, we ignore all other params *)

let rec replace_prem (p : prem) =
  match p.it with
  | IfPr e -> 
    let* e' = replace_e e in
    return { p with it = IfPr e' }
  | LetPr (e1, e2, b) -> 
    let* e1' = replace_e e1 in
    let* e2' = replace_e e2 in
    return { p with it = LetPr (e1', e2', b) }
  | IterPr (prems, iter) -> 
    let* prems' = mapM replace_prem prems in
    return { p with it = IterPr (prems', iter) }
  | _ -> return p

let replace_cls (fcl : func_clause) =
  let cl_id, cl = fcl in
  let { it = DefD (bs_, args, retexp, prems); _ } = cl in
  (*Printf.printf "replacing func clause args\n";*)
  let* args' = mapM replace_arg args in
  Printf.printf "replacing ret exp with type: %s\n" (Il.Print.string_of_typ retexp.note);
  let* retexp' = replace_e retexp in
  let* prems' = mapM replace_prem prems in
  return (cl_id, { cl with it = DefD (
    bs_,
    args',
    retexp',
    prems') })

let rec rmv_families (dl_defs : dl_def list) = 
  let rec aux acc dl_defs' =
    match dl_defs' with
    | [] -> return (List.rev acc)
    | (FuncDef fd)::rest ->
      let { it = (fid, fidopt, params, t, fcl_list, partial); _ } = fd in
      Printf.printf "in func: %s\n" fid.it; 
      let* t' = replace_typ t in
      Printf.printf "replacing clauses:\n"; 
      let* fcl_list' = mapM replace_cls fcl_list in
      let* params' = mapM replace_param params in
      aux ((FuncDef { fd with it = (fid, fidopt, params', t', fcl_list', partial)}) :: acc) rest
    | (RecDef defs)::rest -> 
      let* defs' = rmv_families defs in
      aux ((RecDef defs')::acc) rest
    | def::rest -> aux (def::acc) rest
  in 
  aux [] dl_defs

(* as of now, we do not error if the type is NOT a tuple as the IL elaboration converts a Tup [t] into t. depending on how the parser is defined and used this can cause issues later *)
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
          (*"Some (" ^ String.concat ", " vs ^ ")")*)
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
      && List.length a1 = List.length a2 (* TODO: need to check each arg *)
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
      (*let b1 = check_eq_typs t11 t21 in
    let b2 = iter1 = iter2 in 
    Printf.printf "b1: %b and b2: %b\n" b1 b2;*)
      check_eq_typs t11 t21 && iter1 = iter2
  | _ -> false

let get_common_consts tcs1 tcs2 =
  (*Printf.printf "Typcase 1 len:\n%d\n" (List.length tcs1);
  Printf.printf "Typcase 2 len:\n%d\n" (List.length tcs2);*)
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
  (*List.iter (fun (op, t) -> Printf.printf "Const 1: %s : %s\n" op (string_of_typ t)) consts1;
  List.iter (fun (op, t) -> Printf.printf "Const 2: %s : %s\n" op (string_of_typ t)) consts2;*)
  let comm =
    List.filter
      (fun c ->
        List.exists
          (fun c2 -> fst c = fst c2 && check_eq_typs (snd c) (snd c2))
          consts2)
      consts1
  in
  (*Printf.printf "Common consts len: %d\n" (List.length comm);*)
  comm

let ocaml_of_numtyp = Num.string_of_typ

(* in a multiple instance type, all aliases eventually resolve to variant types, and each instance can correspond to _multiple_ variant types *)
(* whole thing needs a refactor any way, but for now i will change the "name" to the original type and NOT the aliased type. so we dont really need to keep track of name anyway *)
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
  | _ -> error dt.at "Multi-instance type must be an AliasT"

(* may have to change to option type *)
(*let generate_type_arms t1name t2name td1 td2 =*)
  (* change this to just use pattern matching *)
  (*Printf.printf "Generating type arms for %s -> %s\n" t1name t2name;*)
  (*let get_deftyp td =
    match td with
    | _, _, [ { it = InstD (_, _, dt); _ } ] -> Some dt
    | _ -> None
  in
  let dt1 = get_deftyp td1 and dt2 = get_deftyp td2 in
  if dt1 != None && dt2 != None then
    let dt1 = Option.get dt1 and dt2 = Option.get dt2 in
    let arms =
      match (dt1.it, dt2.it) with
      | VariantT tcs1, VariantT tcs2 ->
          let common_consts = get_common_consts tcs1 tcs2 in
          let arms =
            List.map
              (fun (consname, typargs) ->
                let cons1 =
                  sanitize_name ~typecons:true ~typename:false consname
                  ^ "_" ^ t1name
                in
                let cons2 =
                  sanitize_name ~typecons:true ~typename:false consname
                  ^ "_" ^ t2name
                in
                let _, argstr, retstr = get_cons_args typargs in
                Printf.sprintf "  | %s -> %s"
                  (append_sep cons1 argstr " ")
                  (append_sep cons2 argstr " "))
              common_consts
          in
          String.concat "\n" arms (*^ "\n  | _ -> None\n"*)
      | _ -> "TODO: non-variant type conversion not implemented yet"
    in
    arms
  else "TODO: multiple insts in type conversion not implemented yet"*)
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

let generate_numtype_conv (t1 : numtyp) (t2 : numtyp) : string t =
  let funcname = ocaml_of_numtyp t1 ^ "_of_" ^ ocaml_of_numtyp t2 in
  let* is_defined = is_defined funcname in
  if is_defined then return ""
  else
    let funcdef =
      "let " ^ funcname ^ " (arg : " ^ ocaml_of_numtyp t2 ^ ") : "
      ^ ocaml_of_numtyp t1 ^ " =\n"
    in
    let funcbody = "Num.cvt " ^ ocaml_of_numtyp t1 ^ " arg\n" in
    let* () = add_funcdef funcname in
    return (funcdef ^ funcbody)

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
  match Il.Print.string_of_cmpop op with "=/=" -> "<>" | s -> s

(* generate a function that will translate an IL exp to an ocaml value of the corresponding type *)
let rec gen_typarg_translation t =
  match t.it with
  | VarT (id, args) ->
      (* a polymorphic type like `a list needs an extra function that will translate `a to ocaml *)
      let* argstr =
        concat_mapM " "
          (fun arg ->
            match arg.it with
            | TypA t -> gen_typarg_translation t
            | _ -> return "")
          args
      in
      let* is_typevar = is_typevar (sanitize_name id.it) in
      if is_typevar then return ("f_" ^ sanitize_name id.it)
      else return ("ocaml_of_" ^ append_sep (sanitize_name id.it) argstr " ")
  | BoolT -> return "ocaml_of_bool"
  | NumT `NatT -> return "ocaml_of_nat"
  | NumT `IntT -> return "ocaml_of_int"
  | NumT _ -> return "todo: non-int/nat num"
  | TextT -> return "ocaml_of_string"
  | TupT [] -> return ""
  (* this is probably still incorrect *)
  | TupT ets ->
      let* args = mapM (fun (_, t) -> gen_typarg_translation t) ets in
      return
        ("("
        ^ String.concat ", "
            (List.mapi
               (fun i arg -> Printf.sprintf "(%s (List.nth es %d))" arg i)
               args)
        ^ ")")
  | IterT (t1, iter) -> (
      let* t1_str = gen_typarg_translation t1 in
      match iter with
      | List -> return (Printf.sprintf "ocaml_of_list (%s)" t1_str)
      | Opt -> return (Printf.sprintf "ocaml_of_opt (%s)" t1_str)
      | _ -> return "todo: non-list/option iterator")

let gen_translation_cases typename tcs =
  let mixop, (_, args, _), _ = tcs in
  let consstr =
    sanitize_name ~typecons:true ~typename:false
      (Util_ocaml.mixop_to_atom_str mixop)
  in
  let* argsstr = gen_typarg_translation args in
  return (Printf.sprintf " | %S -> %s_%s %s" consstr consstr typename argsstr)

let gen_var_translation tcs name args : string t =
  let* typevars = get_typevars () in
  let polymorphic_args =
    String.concat " "
      (List.map
         (fun arg -> Printf.sprintf "(f_%s : exp -> '%s)" arg arg)
         (Set.to_list typevars))
  in
  let funcname = "ocaml_of_" ^ name in
  let name' = "DL." ^ name in
  let arg = append_sep polymorphic_args "(e : exp)" " " in
  let* cases = concat_mapM "\n  " (gen_translation_cases name) tcs in
  let fail_case = Printf.sprintf " | s -> failwith \"Mixop is: \" ^ s" in
  let funcdef =
    Printf.sprintf
      "%s %s : %s =\n\
      \ match e.it with\n\
      \ | CaseE (mixop, {it=TupE es; _}) -> begin match (sanitize_name \
       ~typecons:true ~typename:false (mixop_to_atom_str mixop)) with\n\
      \  %s\n\
      \   end\n\
      \ | _ -> failwith \"Invalid expression for Variant type %s: should be a \
       CaseE\"\n"
      funcname arg
      (append_sep args name' " ")
      cases name
  in
  return funcdef

let gen_translation_typfield name i (atom, (_bs, t, _prems), _hints) =
  let* typ_str = gen_typarg_translation t in
  return
    (Util_ocaml.mixop_to_atom_str ~recordfield:true [ [ atom ] ]
    ^ "_" ^ name ^ "= (" ^ typ_str ^ " e" ^ string_of_int i ^ ")")

let gen_match_typfield name i (atom, (_bs, t, _prems), _hints) =
  let atom_str = Util_ocaml.mixop_to_atom_str [ [ atom ] ] in
  return (Printf.sprintf "({it=(Atom \"%s\"); _}, e%d)" atom_str i)

let gen_str_translation tfs name : string t =
  let funcname = "ocaml_of_" ^ name in
  let name' = "DL." ^ name in
  let arg = "(e : exp)" in
  let* matchfields = concat_mapMi ";\n   " (gen_match_typfield name) tfs in
  let* fields = concat_mapMi ";\n     " (gen_translation_typfield name) tfs in
  let funcdef =
    Printf.sprintf
      "%s %s : %s =\n\
      \ match e.it with\n\
      \ | StrE ([\n\
      \   %s]) -> {\n\
      \     %s\n\
      \   }\n\
      \ | _ -> failwith \"Invalid expression for Record type %s: should be a \
       StrE\"\n"
      funcname arg name' matchfields fields name
  in
  return funcdef

(* todo: not sure if all flags are passed correctly *)
let rec ocaml_of_exp ?(typearg = false) ?(funcdef = false) ?(funccall = false)
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
        (* let* typevars = get_typevars () in *)
        (*Printf.printf "typevars in scope are: -----\n";
    Set.iter (Printf.printf "%s " ) typevars;
    Printf.printf "-----\n";*)
        let* typ_annot = ocaml_of_typ e.note in
        return
          (Printf.sprintf "(%s : %s)" (sanitize_name ~typearg id.it) typ_annot)
    | SubE (e1, typ1, typ2) ->
        (* if an argument is of the form e : t1 <: t2, 
       the function expects an arg of type t2 but casts it to a type t1 in the body. so we have to add "let e = t1_of_t2 arg" to make it typecheck *)
        (*Printf.printf "SubE in arg: %s\n" (Il.Print.string_of_exp e);*)
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
    | CatE _ ->
        let* freshvar = get_freshvar () in
        let* typannot = ocaml_of_typ e.note in
        let* split = split_arg e freshvar in
        let* () = add_typecast split in
        return (Printf.sprintf "(%s : %s)" freshvar typannot)
    | TupE [] -> return ""
    | TupE es ->
        let* es_strs = concat_mapM ", " (ocaml_of_exp ~funcdef:true) es in
        return ("(" ^ es_strs ^ ")")
    | _ -> raise CannotAnimate
  else
    match e.it with
    | NumE n -> return (Num.to_string n)
    | TextE s -> return (Printf.sprintf "%S" s)
    | BoolE b -> return (string_of_bool b)
    | VarE id -> return (sanitize_name ~typearg id.it)
    | ListE es ->
        let* es_strs = concat_mapM "; " (ocaml_of_exp ~typearg) es in
        return ("[" ^ es_strs ^ "]")
    | TupE [] -> return ""
    | TupE es ->
        let* es_strs = concat_mapM ", " (ocaml_of_exp ~typearg) es in
        return ("(" ^ es_strs ^ ")")
    | CallE (id, args) ->
        let fname = (sanitize_name id.it) ^ "_fn" in
        (* this is hack for now *)
        if fname = "uc_nd_fn" then return "true" else
        let* args' = ocaml_of_args ~typearg ~funcdef ~funccall:true args in
        let args'' = if args' = "" then "()" else args' in
        return ("(" ^ fname ^ " " ^ args'' ^ ")")
    | CaseE (mixop, e1) ->
        (*Printf.printf "Generating case expression for mixop %s\n" (Util_ocaml.mixop_to_atom_str mixop);*)
        let* mixopstr = ocaml_of_mixop mixop e.note in
        let* e1str = ocaml_of_exp e1 in
        let argsstr = if e1str = "" then "" else "(" ^ e1str ^ ")" in
        return (Printf.sprintf "(%s)" (append_sep mixopstr argsstr " "))
        (* let* consdef = resolve_variant e.note in
        let* typename = ocaml_of_typ ~consannot:true (Option.get consdef) in
        let* is_poly = is_polyvar typename in
        let backtick = if is_poly then "`" else "" in
        let label =
          sanitize_name ~typecons:true ~typename:false
            (Util_ocaml.mixop_to_atom_str mixop)
          ^ "_" ^ typename
        in
        let* e1str = ocaml_of_exp e1 in
        if not (e1str = "") then
          return ("(" ^ backtick ^ label ^ " " ^ e1str ^ ")")
        else return (backtick ^ label)*)
    | BinE (op, _, e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        (* if this is a float operation *)
        let* e1type = ocaml_of_typ e1.note in
        let float = (e1type = "float") || (e1type = "rat") in
        let binopstr = ocaml_of_binop ~float op in
        (* if both e1 and e2 were ints, but we used the float power operator, we need to convert the result back to an int *)
        if (e1type = "int" || e1type = "nat") && binopstr = "**" then
          return
            ("(int_of_float ((float_of_int (" ^ e1str ^ ")) " ^ binopstr ^ " (float_of_int (" ^ e2str ^ "))))")
        else return ("(" ^ e1str ^ " " ^ binopstr ^ " " ^ e2str ^ ")")
    | UnE (op, _, e1) ->
        let* e1str = ocaml_of_exp e1 in
        return ("(" ^ ocaml_of_unop op ^ "(" ^ e1str ^ "))")
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
        (*Printf.printf "projecting out of exp: %s, type: %s" expstr typstr;*)
        let* tupsize = get_tupsize e.note in
        match tupsize with
        | Some len ->
            if n < 0 || n >= len then
              error e.at "Tuple projection out of bounds."
            else
              let* () = generate_proj len n in
              return (Printf.sprintf "(proj_%d_%d %s)" len n expstr)
        (* if not a tuple, we are projecting out of a list *)
        | None -> return (Printf.sprintf "(List.nth %s %d)" expstr n)
        (*return (Printf.sprintf "(proj_%d_%d %s)" n n expstr)*))
    | CmpE (op, _, e1, e2) ->
        let* e1str = ocaml_of_exp e1 in
        let* e2str = ocaml_of_exp e2 in
        return ("(" ^ e1str ^ " " ^ ocaml_of_cmpop op ^ " " ^ e2str ^ ")")
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
                    return
                      ("(List.init (" ^ lenstr ^ ") (fun " ^ sanitize_name idstr
                     ^ " -> " ^ body_str ^ "))")
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
                  return
                    ("(List.init (" ^ lenstr ^ ") (fun " ^ idstr ^ " -> "
                   ^ body_str ^ "))")
              | _ ->
                  let* () = set_knowns prev_knowns in
                  return
                    "(* TODO: IterE with no bindings and non-length iterator *)"
              )
          | bindings -> (
              match iter with
              | List | ListN _ ->
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
                       get_opts body_str)
                  (*return ("(Some (" ^ get_opts ^ " " ^ body_str ^ "))")*)
              | _ ->
                  return
                    "(* TODO: IterE with multiple-bindings and non-list \
                     iterator *)"))
    | SubE (e1, typ1, typ2) ->
        (* Subtyping should not be refutable (I think) unless it appears on the LHS of a let or in the argument of a function definition
    this probably does not matter anymore since we use exceptions instead of options *)
        (*Printf.printf "subE is non-func arg'\n";*)
        let* flipsub = get_flipsub () in
        let* () =
          if flipsub then generate_type_conv typ2 typ1
          else generate_type_conv typ1 typ2
        in
        let* e1str = ocaml_of_exp e1 in
        (*(if flipsub then Printf.printf "subtyping direction is flipped for term: %s\n" e1str);*)
        let* typ1str = ocaml_of_typ ~consannot:true typ1 in
        let* typ2str = ocaml_of_typ ~consannot:true typ2 in
        if flipsub then
          return ("(" ^ typ1str ^ "_of_" ^ typ2str ^ " " ^ e1str ^ ")")
        else return ("(" ^ typ2str ^ "_of_" ^ typ1str ^ " " ^ e1str ^ ")")
    | CvtE (e1, typ1, typ2) ->
        let* e1str = ocaml_of_exp e1 in
        return
          ("(" ^ ocaml_of_numtyp typ2 ^ "_of_" ^ ocaml_of_numtyp typ1 ^ " "
         ^ e1str ^ ")")
    | OptE eo ->
        if Option.is_none eo then return "None"
        else
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
    | MemE (e1, e2) ->
        (* todo this can also be a choice operator (?) *)
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
              let* idxtsr = ocaml_of_exp idexp in
              let* inner_update =
                build_update rest ("(List.nth " ^ path_acc ^ " " ^ idxtsr ^ ")")
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

(* a function argument may be an arbitrary concatenation of lists. it is possible to split a list if it is the right combination of length iterators and singleton lists (containing known element). for now we dont deal with length iterators and only split on known singleton lists. we also don't deal with lists of known elements of length greater than 1, e.g. [a;b;c], but these can be split into singletons anyway *)

(* removes all nested concatenations and returns a flattened list *)
and get_lists (e : exp) : exp list =
  match e.it with
  | ListE _ | IterE _ -> [ e ]
  | CatE (e1, e2) -> get_lists e1 @ get_lists e2
  | _ -> raise (CannotSplit (string_of_exp e))

(* finds the element we can split on, i.e., a singleton list with a known element for now. later this can include length iterators 
todo: use rev for efficiency *)
and get_anchor (es : exp list) : exp list * exp * exp list =
  (*Printf.printf "Finding split anchor in list: %s\n" (String.concat "; " (List.map (fun e' -> Printf.sprintf "exp: %s;  at: %s\n" (string_of_exp e') (string_of_region e'.at)) es));*)
  let rec aux before after =
    match after with
    | [] -> raise (CannotSplit "no suitable split anchor found")
    | e :: rest -> (
        match e.it with
        | ListE [ e1 ] -> (
            (* this needs to be a cased expression or something we know!! but idk how to check that or quantify that right now *)
            match e1.it with
            | CaseE _ ->
                (*Printf.printf "Found split anchor: %s\n" (string_of_exp e1);*)
                (before, e1, rest)
            | _ -> aux (before @ [ e ]) rest)
        | _ -> aux (before @ [ e ]) rest)
  in
  aux [] es

and split_arg (e : exp) (name : string) : string t =
  let es = get_lists e in
  split_arg_helper es name

and split_arg_helper (es : exp list) (name : string) : string t =
  if List.length es = 1 then
    (* if we have only one element left, we don't need to split further *)
    let* () = add_known name in
    (* if this is an iterator of the form <exp>{v <- v*} then we have to generate something of the form let v* = map1 (fun v -> exp) name *)
    match (List.hd es).it with
    | IterE (body, (iter, bindings)) -> (
        match bindings with
        | [ (id, listname) ] ->
            let* lhsstr = ocaml_of_exp listname in
            (*Printf.printf "adding %s to knowns\n" lhsstr;*)
            let* () = add_known (sanitize_name lhsstr) in
            let (VarE listvar) = listname.it in
            let rhsexp =
              {
                (List.hd es) with
                it =
                  IterE
                    ( body,
                      ( iter,
                        [
                          ( id,
                            {
                              listname with
                              it = VarE { listvar with it = name };
                            } );
                        ] ) );
              }
            in
            let* rhsstr = ocaml_of_exp rhsexp in
            return (Printf.sprintf "  let %s = %s in\n" lhsstr rhsstr)
        | _ -> failwith "Multiple Bindings in a split-argument")
    | _ ->
        let* expstr = ocaml_of_exp (List.hd es) in
        (* add the correct variable to known here and also fix "add_knowns" in general for weird concatenated args *)
        return (Printf.sprintf "  let %s = %s\n" expstr name)
  else if List.length es = 0 then return ""
  else
    let before, anchor, after = get_anchor es in
    let* beforevar = get_freshvar () in
    let* aftervar = get_freshvar () in
    let (CaseE (mixop, _)) = anchor.it in
    let split_suffix = sanitize_name (Util_ocaml.mixop_to_atom_str mixop) in
    let* anchorstr = ocaml_of_exp anchor in
    let splitanchor =
      Printf.sprintf "  let %s, %s, %s = split_on_%s %s in\n" beforevar
        anchorstr aftervar split_suffix name
    in
    let* mixopstr = ocaml_of_exp anchor in
    let* () = generate_split_func split_suffix mixopstr in
    let* split_bfr = split_arg_helper before beforevar in
    let* split_aftr = split_arg_helper after aftervar in
    return (splitanchor ^ split_bfr ^ split_aftr)

(* use rev here to be more efficient (& and in every other list helper func) *)
and generate_split_func (s : string) (pattern : string) : unit t =
  let funcname = Printf.sprintf "split_on_%s" s in
  let* is_defined = is_defined funcname in
  if is_defined then return ()
  else
    let* () = add_funcdef funcname in
    tell
      (Printf.sprintf
         "let %s (lst : 'a list) : 'a list * 'a * 'a list =\n\
         \  let rec aux before after =\n\
         \    match after with\n\
         \    | [] -> raise (Match_failure (\"\", 0, 0))\n\
         \    | (%s)::rest -> before, %s, rest\n\
         \    | x::xs -> aux (before @ [x]) xs\n\
         \  in aux [] lst\n"
         funcname pattern pattern)

(* todo: add support for nested cons + add things to knowns correctly *)
(* if there is a concatenation inside a CaseE, we need to generate a split like we normally do, but it needs to occur AFTER the uncasing *)
and collect_vars (e : exp) : (string list * string) t =
  match e.it with
  | VarE id ->
      let* () = add_known (sanitize_name id.it) in
      return ([ sanitize_name id.it ], "")
  | TupE es ->
      let rec go acc = function
        | [] -> return (List.rev acc, "")
        | { it = VarE id; _ } :: rest ->
            let* () = add_known (sanitize_name id.it) in
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
      return ([ freshvar ], listsplits)
  | _ -> raise CannotAnimate

and ocaml_of_mixop mixop typnote : string t =
  let* typcons = resolve_variant typnote in
  let* typname = ocaml_of_typ ~consannot:true (Option.get typcons) in
  let mixopstr = Util_ocaml.mixop_to_atom_str mixop in
  let label = sanitize_name ~typecons:true ~typename:false mixopstr in
  return (label ^ "_" ^ typname)

(* an "uncase exp typcons" function will strip the typecons from the exp (a variant type). but each constructor can take a different number / type of arguments, meaning uncase_type will have different return types for each cons. so we have to generate a separate function for each cons. *)
(* use ocaml_of_mixop *)
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

(*and generate_type_translation_new {it=(id, params, insts);_} : unit t =
  (* todo: deal with args *)
  let typename = sanitize_name id.it in
  let funcname = "ocaml_of_" ^ typename in
  let* poly = is_polyvar typename in
  let func_body = foldM (fun (acc, seen) {it=InstD (_, _, dt); _} ->
    match dt.it with 
    (* when an aliased type is one of many instances, we need to generate a match case for every variant in each instance and combine them *)
    | AliasT t when poly -> 
      let* var_type = resolve_variant t in begin
        match var_type with
        | Some {it=(VarT (id, _));_} -> 
          let* Some(typename, {it=VariantT tcs;_}) = lookup (sanitize_name id.it) in
          let* cases, seen' = gen_var_translation_new tcs typename "" in 
          return (append_sep acc cases "\n", Set.union seen seen')
        | None -> error dt.at "AliasT in multiple instances must resolve to a variant type"
      end
    (* in case of a single instance type, like type A = alias B (args) we just translate B, i.e. ocaml_of_A e = ocaml_of_B ocaml_of_<args> e *)
    | AliasT t -> 
    
    
    
    
    StructT _ | VariantT _ ->
    let* translation = generate_type_translation dt id.it params in
    return (acc ^ "\n" ^ translation)
  ) "" insts in
  return ()*)

and generate_type_translation dt name args : string t =
  match dt.it with
  | AliasT t -> (
      match t.it with
      | VarT (id, args) ->
          let typedef = "ocaml_of_" ^ sanitize_name id.it in
          (* if t is a polymorphic type initialised with some type t' then we need to pass an argument to translate t' *)
          let* argsstr =
            concat_mapM " "
              (fun arg ->
                match arg.it with
                | TypA t -> gen_typarg_translation t
                | _ -> return "")
              args
          in
          return
            (Printf.sprintf "ocaml_of_%s e = %s e" name
               (append_sep typedef argsstr " "))
      | TupT [] -> return (Printf.sprintf "ocaml_of_%s (e : exp) = ()" name)
      | TupT ets ->
          let argstrs =
            String.concat ", "
              (List.mapi (fun i _ -> Printf.sprintf "e%d" i) ets)
          in
          let* args = mapM (fun (_, t) -> gen_typarg_translation t) ets in
          let body =
            "("
            ^ String.concat ", "
                (List.mapi (fun i arg -> Printf.sprintf "(%s e%d)" arg i) args)
            ^ ")"
          in
          return (Printf.sprintf "ocaml_of_%s (%s) = %s" name argstrs body)
      | _ ->
          let* typedef = gen_typarg_translation t in
          return (Printf.sprintf "ocaml_of_%s e = %s e" name typedef))
  | StructT tfs -> gen_str_translation tfs name
  | VariantT tcs -> gen_var_translation tcs name args

(* Get deftype from an alias *)
and lookup (typename : string) : (string * deftyp) option t =
  (*Printf.printf "Looking up typedef for type: %s\n" typename;*)
  let* typdef = get_typedef typename in
  match typdef with
  | Some { it = id, _, { it = InstD (_, _, dt); _ } :: _; _ } ->
      (*Printf.printf "returning typedef: %s\n" id.it;*)
      return (Some (id.it, dt))
  | _ -> return None

(* Resolve a typ to a StructT fields if it denotes a record type.
   Follows aliases. *)
and resolve_struct (typname : typ) (toplvl : bool) :
    (string * typfield list) option t =
  match typname.it with
  | VarT (tid, _) -> (
      (* ???????? *)
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
      (*Printf.printf "Looking for typedef: %s\n" tid.it;*)
      (* temp - multi instance types are annotated with their own type name even if they are aliased *)
      let tid = (sanitize_name tid.it) in
      let* istypfam = is_typ_fam tid in
      if istypfam then return (Some typname) else begin
      let* typedef = lookup tid in
      match typedef with
      | Some (_, dt) -> (
          match dt.it with
          | AliasT t' -> resolve_variant t'
          | StructT _ -> return None
          | VariantT _ -> return (Some typname))
      | None -> (*Printf.printf "Type %s not found\n" tid.it;*) return None end)
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
      (*Printf.printf "VarT: %s\n" id.it;*)
      let name = sanitize_name id.it in
      (*Printf.printf "consannot: %b\n" consannot;*)
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
typearg refers to whether the arg is from a type declaration, like: "type x list", or type defintion, like: "type a = Cons of x" OR "type a = nat list". right now, we only support arguments that are types themselves (polymorphic types). we dont support an arg like "N: nat" (dependent types).
TODO: idk what a GramA arg is *)
and ocaml_of_arg ?(typearg = true) ?(funcdef = false) ?(funccall = false) a =
  match a.it with
  | ExpA e ->
      (*let* b = get_flipsub () in
    Printf.printf "flipsub in ocaml_of_arg: %b\n" b;*)
      ocaml_of_exp ~typearg ~funcdef ~funccall e
  | TypA t ->
      if not (funccall || funcdef) then ocaml_of_typ ~typearg t else return ""
  | DefA id -> return ((sanitize_name id.it) ^ "_fn")
  | GramA g -> return "TODO: gram in arg not supported"

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
  let opstr =
    match op with
    | `AddOp -> "+"
    | `SubOp -> "-"
    | `MulOp -> "*"
    | `DivOp -> "/"
    | `ModOp -> "mod"
    | `PowOp -> "**"
  in
  if float && opstr <> "mod" && opstr <> "**" then opstr ^ "." else opstr

and ocaml_of_binop ?(float = false) = function
  | #Bool.binop as op -> ocaml_of_bool_binop op
  | #Num.binop as op -> ocaml_of_num_binop ~float op

and ocaml_of_bool_unop = function `NotOp -> "not"

and ocaml_of_unop = function
  | #Bool.unop as op -> ocaml_of_bool_unop op
  | #Num.unop as op -> Num.string_of_unop op

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
              (*Printf.printf "Generating LetPr with LHS: %s\n" lhs_str;*)
              let* rhs_str = ocaml_of_exp rhs in
              (*Printf.printf "Generating LetPr with RHS: %s\n" rhs_str;*)
              match lhs.it with
              | VarE id ->
                  return (Printf.sprintf "  let %s = %s in" lhs_str rhs_str)
              | CaseE (mixop, e) ->
                  (* this can fail and raise a Match Failure exception, which will be caught by the try_clauses function *)
                  let let_lhs = String.concat ", " (List.map sanitize_name vars) in
                  (*let* rhstypcons = resolve_variant rhs.note in
                  let* rhstyp =
                    ocaml_of_typ ~consannot:true (Option.get rhstypcons)
                  in*)
                  let* mixopstr = ocaml_of_mixop mixop rhs.note in
                  (*  sanitize_name ~typecons:true ~typename:false
                      (Util_ocaml.mixop_to_atom_str mixop)
                    ^ "_" ^ rhstyp
                  in*)
                  return
                    (Printf.sprintf "  let %s (%s) = %s in" mixopstr let_lhs
                       rhs_str)
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
                      (*let vardef = Printf.sprintf "  let %s = Option.get %s in\n" (sanitize_name varname.it) rhs_str in
            let* liststr = ocaml_of_exp listname in 
            let outflow_def = Printf.sprintf "  let %s = Some %s in" liststr (sanitize_name varname.it) in 
            let* () = add_known liststr in 
            return (vardef ^ outflow_def)*)
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
                  (*Printf.printf "Outflow list vars: %s\n" (String.concat ", " outflow_listvars);*)
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
                    Printf.sprintf "  let %s = List.init %s (fun i -> i) in\n"
                      idx_listname list_len
                  in
                  (* TODO: all the if idx_list = "" checks are a bit hacky and maybe there is a way to generalise them 
        but if we consider the index variable to be an outflow, we will have to add it separately to "fun <inflows> -> ...", which is also annoying *)
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
                  (*Printf.printf "Outflow list vars: %s\n" (String.concat ", " outflow_listvars);*)
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
                          "  let () = map%d (fun %s -> %s Some ()) %s in"
                          (List.length inflows) inflow_vars prem_strs
                          inflow_lists)
                  (*else if monadic then 
          return (def_idx_list ^ Printf.sprintf "  let* %s = unzip%dM (map%dM (fun %s -> %s Some (%s)) %s) in" outflow_lists (List.length outflows) (List.length inflows) inflow_vars prem_strs outflow_vars inflow_lists)*)
                    else
                    return
                      (def_idx_list
                      ^ Printf.sprintf
                          "  let %s = unzip%d (map%d (fun %s -> %s %s) %s) in"
                          outflow_lists (List.length outflows)
                          (List.length inflows) inflow_vars prem_strs
                          outflow_vars inflow_lists))))
    prems

(* todo: the bracketing is possibly wrong, copied from print.ml *)
let ocaml_of_typ_args t =
  match t.it with
  | TupT [] -> return ""
  | TupT _ -> ocaml_of_typ ~typearg:true t
  | _ ->
      let* argstr = ocaml_of_typ ~typearg:true t in
      return ("(" ^ argstr ^ ")")

(* Hardcoded for now: i dont know how to deal with this
   without creating a cyclic dependency & a lot of problems otherwise *)
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
          (Printf.sprintf "  | %s_instr%s -> %s instrs" consname args_str
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
        "dispatch_step%s instr instrs : (%s) =\n\
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
  (*Printf.printf "translating func: %s\n" id.it;*)
  let* () = add_funcdef name in
  let params' = List.filter rmv_nonexp params in
  let num_params = List.length params' in
  (* generate "try_clauses_n" for the right "n" *)
  let* () = gen_try_cls num_params in
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
  (* these functions are hardcoded *)
  if List.length clauses = 0 then
    match id.it with
    | "Step_read_throw_ref_handler" ->
        return [ name ^ " = uc_step_read_slashthrow_ref\n" ]
    | "dispatch_step_pure" -> build_dispatch "pure"
    | "dispatch_step_read" -> build_dispatch "read"
    | "dispatch_step" -> build_dispatch ""
    | _ -> return [ name ^ "_fn = Builtin." ^ name ^ "\n" ]
  else if id.it = "Step" then return [ "uc_step a0 = step a0\n" ]
    (* this is re-defined to called `step` instead *)
  else
    let typevars = typevars_of_params params in
    (*Printf.printf "defining func: %s\n" id.it;*)
    (*Set.iter (Printf.printf "%s\n") typevars;*)
    let* () = set_typevars (typevars_of_params params) in
    let* rettypstr = ocaml_of_typ rettyp in
    let* clause_funcs =
      mapMi
        (fun i fclause ->
          let _, clause = fclause in
          match clause.it with
          | DefD (_, params, body, prems) ->
              (* reset knowns each time for different function *)
              let* () = set_knowns Set.empty in
              catchM
                (fun () ->
                  (*let* b0 = get_flipsub () in
        Printf.printf "flipsub at catchM entry: %b\n" b0;*)
                  let num_params = List.length params in
                  (*Printf.printf "translating args:\n";*)
                  let* () = set_flipsub true in
                  let* argnames =
                    if num_params = 0 then return "()"
                    else
                      (*let* b = get_flipsub () in 
            Printf.printf "flipsub is %b\n" b;*)
                      ocaml_of_args ~typearg:false ~funcdef:true params
                  in
                  let* () = set_flipsub false in
                  (*Printf.printf "translating prems:\n";*)
                  let* prems_block = ocaml_of_prems prems in
                  (*Printf.printf "translating ret value:\n";*)
                  let* retvalue = ocaml_of_exp body in
                  let* typecasts = get_typecasts () in
                  let* () = set_typecasts "" in
                  (* debugging stuff remove later*)
                  (*let debug = Printf.sprintf "  Printf.printf \"calling clause_%s_%d\\n\";" name i in*)
                  let bodycode = typecasts ^ prems_block in
                  if bodycode = "" then
                    return
                      (Printf.sprintf "clause_%s_%d %s : %s = %s\n" name i
                         argnames rettypstr retvalue)
                  else
                    return
                      (Printf.sprintf "clause_%s_%d %s : %s =\n%s\n  %s\n" name
                         i argnames rettypstr bodycode retvalue))
                (function
                  | CannotAnimate | CannotSplit _ ->
                      let argnames =
                        String.concat " "
                          (List.init (List.length params) (fun i ->
                               Printf.sprintf "unanimated%d" i))
                      in
                      return
                        (Printf.sprintf
                           "clause_%s_%d %s = raise (UnanimatedArg \"%s\")\n"
                           name i argnames name)
                  | e -> raise e))
        clauses
    in
    let* () = set_typevars Set.empty in
    let clause_calls =
      List.mapi (fun i _ -> Printf.sprintf "clause_%s_%d" name i) clauses
    in
    let clause_names = String.concat ";\n  " clause_calls in
    let err_msg = "function: " ^ name in
    (*let debug = Printf.sprintf "  Printf.printf \"Calling function: %s\\n\";" name in*)
    (* "_fn" is added to the main function name because there is one case in the spec where a function name happens to match a local variable name, which causes a type error *)
    let main_func =
      Printf.sprintf "%s_fn %s = try_clauses_%d [\n  %s\n] %s \"%s\"" name argslist
        num_params clause_names argslist' err_msg
    in
    return (clause_funcs @ [ main_func ])

(* ignoring the dependent type annotations for now *)
let ocaml_of_typcase typename (op, (_, t, _), _hints) =
  let* args_str = ocaml_of_typ_args t in
  (*Printf.printf "Generating typcase for type: %s\n" typename;
  Printf.printf "is type polymorphic?: %b\n" is_poly;*)
  (* todo: just use ocaml_of_mixop here *)
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

(* THIS WHOLE THING NEEDS A MAJOR REFACTOR !!!! *)
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
      (*Printf.printf "VariantT type %s\n" name;*)
      let* () = generate_uncase tcs name in
      concat_mapM "\n  | " (ocaml_of_typcase name) tcs

(* this needs major refactoring *)
let ocaml_of_inst name inst =
  (* todo: deal with type args of multi-instance types *)
  let { it = InstD (_, as_, dt); _ } = inst in
  let* all_tcs = get_all_tcs name inst in
  let* dt_str = 
  mapM (fun (tcs, name) -> 
    mapM (ocaml_of_typcase name) tcs) all_tcs in
  let* match_cases =
    mapM (fun (tcs, name) ->
      mapM (gen_translation_cases name) tcs) all_tcs
  in
  (* if we are at the top-level variant type, also generate the uncasing function(s) for its constructors *)
  let* () = match dt.it with
  | VariantT tcs -> generate_uncase tcs name
  | _ -> return () in
  return (List.flatten dt_str, List.flatten match_cases)
  
  
  (*match dt.it with
  | AliasT t -> (
      let* var_type = resolve_variant t in
      match var_type with
      | Some { it = VarT (tid, _); _ } ->
          let* (Some (typename, dt')) = lookup (sanitize_name tid.it) in
          let* dt_str = ocaml_of_deftyp dt' (sanitize_name typename) in
          (* generating the match cases for the ocaml_of_<type> translation function *)
          let () =
            match dt'.it with
            | VariantT _ -> Printf.printf "variant\n"
            | AliasT t -> Printf.printf "alias: %s\n" (string_of_typ t)
            | StructT _ -> Printf.printf "struct\n"
          in
          let { it = VariantT tcs; _ } = dt' in
          let* match_cases =
            concat_mapM "\n  "
              (gen_translation_cases (sanitize_name typename))
              tcs
          in
          return (dt_str, match_cases)
      | None ->
          error dt.at
            "AliasT in multiple instances must resolve to a variant type")
  (* I don't think this is used anymore, since we combine all VariantT's into one instance *)
  | VariantT tcs ->
      let* dt_str = ocaml_of_deftyp dt name in
      (* generating the match cases for the ocaml_of_<type> translation function *)
      let* match_cases = concat_mapM "\n  " (gen_translation_cases name) tcs in
      let* () = generate_uncase tcs name in
      return (dt_str, match_cases)
  | _ -> error dt.at "Multi-instance type must be an AliasT"*)

let ocaml_of_typedef (typedef : type_def) : (string * string) t =
  (* for now, i dont know what happens if there are no instances *)
  (* if we have a Variant type with multiple instances, we just combine all <unique> constructors into one instance. so the only mutli-instance types are Alias types. 
    for now, all duplicate constructors (with possibly different args) are removed :( 
    also, type args may be completely messed up *)
  let td = rmv_duplicate_cons typedef in
  let { it = id, ps, insts; _ } = td in
  (*Printf.printf "defining typedef: %s\n" id.it;*)
  let* () = set_typevars (typevars_of_params ps) in
  let name = sanitize_name id.it in
  let* multi = is_typ_fam name in
  if not multi then
    (* must be a one instance type *)
    match insts with
    | [ { it = InstD (_, as_, dt); _ } ] ->
        let* args_str = ocaml_of_args ~typearg:true as_ in
        let space = if args_str = "" then "" else " " in
        let* dt_str = ocaml_of_deftyp dt name in
        let* type_translation = generate_type_translation dt name args_str in
        let* () = set_typevars Set.empty in
        return
          ( append_sep args_str name " " ^ " = " ^ dt_str ^ "\n",
            type_translation )
    | _ -> error td.at "Non-polymorphic type must have exactly one instance"
  else
    (* we ignore type args for now :( *)
    (* for now, remove duplicated constructors based on string representation
    later, refactor ocaml_of_inst *)
    let* dt_str, cases =
      concat_mapM2' [ "\n  | "; "\n" ] (ocaml_of_inst name) insts
    in
    (*Printf.printf "type trans is empty? %b\n" (cases = "");*)
    let type_translation =
      Printf.sprintf
        "ocaml_of_%s (e : exp) : %s =\n\
        \ match e.it with\n\
        \ | CaseE (mixop, {it=TupE es; _}) -> begin match (sanitize_name \
         ~typecons:true ~typename:false (mixop_to_atom_str mixop)) with\n\
        \    %s\n\
        \   end\n\
        \ | _ -> failwith \"Invalid expression for Aliased-Variant type %s: \
         should be a CaseE\"\n"
        name ("DL." ^ name) cases name
    in
    let* () = set_typevars Set.empty in
    return
      (sanitize_name id.it ^ " =\n  | " ^ dt_str ^ "\n", type_translation)
(*match insts with
    | {it = InstD (_, as_, dt); _}::rest ->
      if List.length rest > 0 then begin
        (* in both aliased instances and variant instances, we just combine the (possibly polymorphic) constructors from each instance *)
        (* todo: generalise this to make the match statement nicer *)
        (* todo: not sure what happens if an instance takes an argument that we actually care about *)
        (* todo: type translation for this *)
        let ocaml_of_inst inst =
          let {it = InstD (_, as_, dt); _} = inst in
          (* todo: this is now very convulated - probably need to change the signature of the resolve_variant *)
          match dt.it with 
          | AliasT t -> begin
            let* var_type = resolve_variant t in 
            match var_type with
            | Some {it=(VarT (id, _));_} -> 
              let* plswork = lookup (sanitize_name id.it) in begin
              match plswork with 
              | Some(typename, dt') -> ocaml_of_deftyp dt' (sanitize_name typename)
              | None -> error dt.at "AliasT in multiple instances must resolve to a variant type" end
            | None -> error dt.at "AliasT in multiple instances must resolve to a variant type"
            end
          | VariantT _ -> ocaml_of_deftyp dt (sanitize_name id.it)
          | _ -> return "(* TODO: multiple instances with non-variant types not supported *)"
        in
        let* dt_strs = concat_mapM "\n  | " ocaml_of_inst insts in
        return ((sanitize_name id.it) ^ " = " ^ dt_strs ^ "\n", "")
      end else begin
        let* args_str = ocaml_of_args ~typearg:true as_ in
        let space = if args_str = "" then "" else " " in
        let* dt_str = ocaml_of_deftyp dt (sanitize_name id.it) in
        let* type_translation = generate_type_translation dt (sanitize_name id.it) args_str in
        let* () = set_typevars Set.empty in
        return ((args_str ^ space ^ (sanitize_name id.it) ^ " = " ^ dt_str ^ "\n"), type_translation) 
        end*)

let ocaml_of_dl_def (def : dl_def) : (string * string) t =
  match def with
  | TypeDef typedef ->
      let* typestr, type_translation = ocaml_of_typedef typedef in
      let { it = id, _, _; _ } = typedef in
      (*Printf.printf "Finished typedef: %s\n" id.it;
      Printf.printf "type translation is empty? %b\n" (type_translation = "");*)
      (* because we don't support multiple instances yet *)
      (* todo: remove this probably *)
      if
        String.length typestr >= 2
        && String.sub typestr 0 2 = "(*"
        && String.sub typestr 8 7 <> "typearg"
      then return ("", typestr)
      else if type_translation <> "" then
        let* () = add_construct ("let " ^ type_translation) in
        return ("", "type " ^ typestr)
      else return ("", "type " ^ typestr)
  | FuncDef fdef ->
      let* funcslist = ocaml_of_func_def fdef in
      let funcstr = "let " ^ String.concat "\nlet " funcslist in
      let id, _, _, _, _, _ = fdef.it in
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
            (* hardcoded - we want "Steps" to redirect to "steps" immediately. defining it in another file will cause a cyclic dependency and we have to define it after "steps" is defined but before it is called *)
            let fdef = List.hd fdefs in
            let id, _, _, _, _, _ = fdef.it in
            let steps =
              if sanitize_name id.it = "steps" then
                "let uc_steps a0 = steps a0\n"
              else ""
            in
            return
              ("let rec " ^ String.concat "\nand " func_strs ^ "\n" ^ steps, "")
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
          let* typestrs, typetranslations =
            concat_mapM2 "\nand " ocaml_of_typedef typedefs
          in
          if String.length typestrs >= 2 && String.sub typestrs 0 2 = "(*" then
            return ("", typestrs)
          else
            let* () = add_construct ("let rec " ^ typetranslations) in
            return ("", "type " ^ typestrs))

(* just for debugging - remove later *)
let gen_instr_strs () =
  let* instrs = get_typedef "instr" in
  let { it = _, _, { it = InstD (_, _, instrsdt); _ } :: _; _ } =
    Option.get instrs
  in
  let (VariantT instr_tcs) = instrsdt.it in
  let* cases =
    concat_mapM "\n"
      (fun (op, (_, t, _), _) ->
        let consname =
          sanitize_name ~typecons:true ~typename:false
            (Util_ocaml.mixop_to_atom_str op)
        in
        let* args = ocaml_of_typ_args t in
        let args_str = if args = "" then "" else " _" in
        return
          (Printf.sprintf "| %s_instr%s -> \"%s\"" consname args_str consname))
      instr_tcs
  in
  tell (Printf.sprintf "let instr_to_string = function\n%s\n" cases)

let ocaml_of_dl_defs (defs : dl_def list) : (string * string) t =
  (*Printf.printf "Calling hardcode step...\n";*)
  let processed_defs = hardcode_step defs in
  (*Printf.printf "length after hardcoding step: %d...\n"(List.length processed_defs);*)
  (* the input may contain type families like: 
    type x = alias <type y> | alias <type z> 
    meaning <type y> OR <type z> can be used where <type x> is expected. in that case, we make types x, y and z polymorphic variants *)
  let* () = set_type_families processed_defs in
  let* typ_fams = get_typ_fams () in
  Printf.printf "Type families found: %s\n"
    (String.concat ", " (List.map (fun (tid, _) -> tid) typ_fams));
  let* processed_defs' = if List.length typ_fams > 0 then
    rmv_families processed_defs 
  else return processed_defs 
  in
  (*Printf.printf "length after resolving typ fams: %d...\n"(List.length processed_defs');*)
  let* def_strs : (string * string) list =
    mapM ocaml_of_dl_def processed_defs'
  in
  let func_defs, type_defs = List.split def_strs in
  let func_str = concat_nonempty "\n" func_defs in
  let type_str = concat_nonempty "\n" type_defs in
  let* () = gen_instr_strs () in
  return (func_str, type_str)

let generate_ocaml (dl_defs : dl_def list) : string * string * string * string =
  let main =
    "open Backend_animation.Util_ocaml\n"
    ^ "open Backend_animation.Util_ocaml.NumConversions\n\n"
    ^ "let (<|>) = Backend_animation.Util_ocaml.mplus\n"
    ^ "let (let*) = Option.bind\n"
  in
  let typeimports = "type nat = int\n" in
  let (funcdefs, typedefs), typeconvfuncs, parser =
    eval (ocaml_of_dl_defs dl_defs)
  in
  (main ^ funcdefs, typeimports ^ typedefs, typeconvfuncs, parser)
