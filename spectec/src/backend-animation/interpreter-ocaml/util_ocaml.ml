open Xl
open Il.Ast
open Def 

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
let is_capital c = 'A' <= c && c <= 'Z'

let uppcase_first s =
  match s with
  | ""                 -> ""
  | _ when s.[0] = '`' -> s (* polymorphic variant, leave as is *)
  | _                  -> 
    let first = s.[0] in
    (* constructors like pos and Pos may map to the same thing but idk how to deal with this *)
    if is_letter first then
      let len = String.length s in
      let first = Char.uppercase_ascii first in
      String.init len (fun i -> if i = 0 then first else s.[i])
    else
      "C" ^ s

(* OCaml convention:
   typenames and record fields are lowercased
   constructors have their first letter uppercased
   constructors cannot begin with non-letter chars
   type arguments are prefixed with a quote (') *)
let sanitize_name ?(typename=true) ?(typecons=false) ?(typearg=false) ?(recordfield = false) id =
  (*Printf.printf "Sanitizing name: %s\n" id;*)
  let lowercased =
    if typename || recordfield then
      (if (id = String.lowercase_ascii id) then id
      (* add a prefix, otherwise variables like N and n will point to the same thing after sanitization *)
      else ("uc_" ^ String.lowercase_ascii id))
    else id
  in
  let raw =
    if typecons then uppcase_first lowercased
    else lowercased
  in
  let raw = if typearg then "'" ^ raw else raw in
  let replacements = [
    '*', "_star";
    '?', "_opt";
    '%', "Pct";
    '.', "_dot_";
    '[', "_lbracksq";
    ']', "_rbracksq";
    '{', "_lbrackcu";
    '}', "_rbrackcu";
    '(', "_lbrackro";
    ')', "_rbrackro";
    '-', "_dash";
    '>', "_right";
    ';', "_semi";
    '/', "_slash"
  ] in
  let replaced = List.fold_left (fun acc (ch, repl) ->
    String.concat repl (String.split_on_char ch acc)
  ) raw replacements in
  match replaced with
  | "match" | "type" | "let" | "val" | "list" | "in" | "module" -> replaced ^ "_"
  | _ -> replaced 

let mixop_to_atom_str ?(recordfield = false) (mixop : Mixop.mixop) =
  (*Printf.printf "mixop to atom: %s\n" (Mixop.to_string mixop);
  Printf.printf "is polymorphic?: %b\n" is_poly;*)
  let frmt name = sanitize_name ~typename:false ~recordfield name in
  match mixop with
  | [{it = Atom.Atom a; _}]::tail when List.for_all ((=) []) tail -> frmt a
  | mixop ->
    let s =
      String.concat "_pct_" (List.map (
        fun atoms -> String.concat "" (List.map (fun x -> x |> Atom.to_string |> frmt) atoms)) mixop
      )
    in s

let rec update_at i v = function
  | _ :: xs when i = 0 -> v :: xs
  | x :: xs            -> x :: update_at (i - 1) v xs
  | [] -> failwith "update_at: index out of bounds" 

let update_slice l i len l' =
  let n = List.length l in
  if i < 0 || len < 0 || i + len > n || List.length l' <> len then
    failwith "update_slice: invalid indices";
  let prefix = List.take i l in
  let suffix = List.drop (i + len) l in
  prefix @ l' @ suffix

let slice l start len =
  if start < 0 || len < 0 || start + len > List.length l then
    failwith "slice: bad indices";
  List.take len (List.drop start l)

let lift e = 
  match e with 
  | Some v -> [v]
  | None -> []

let unzip1 lst = lst 
let unzip2 (lst : ('a * 'b) list) : ('a list * 'b list) =
  let rec aux acc1 acc2 = function
    | [] -> (List.rev acc1, List.rev acc2)
    | (x, y) :: rest -> aux (x :: acc1) (y :: acc2) rest
  in
  aux [] [] lst
let unzip3 (lst : ('a * 'b * 'c) list) : ('a list * 'b list * 'c list) =
  let rec aux acc1 acc2 acc3 = function
    | [] -> (List.rev acc1, List.rev acc2, List.rev acc3)
    | (x, y, z) :: rest -> aux (x :: acc1) (y :: acc2) (z :: acc3) rest
  in
  aux [] [] [] lst

let unzip_opt1 opt_a = opt_a

let map1 = List.map

let rec map2 f xs ys =
  match xs, ys with
  | x::xt, y::yt -> (f x y) :: map2 f xt yt
  | _ -> []

let rec map3 f xs ys zs =
  match xs, ys, zs with
  | x::xt, y::yt, z::zt -> (f x y z) :: map3 f xt yt zt
  | _ -> []

let map_opt1 (f : 'a -> 'b) (opt_a : 'a option) : 'b option =
  match opt_a with
  | Some a -> Some (f a)
  | None -> None

module Map = Map.Make(String) 
module Set = Set.Make(String) 

(* A State+Writer monad: 
   The State keeps track of type definitions, known/bound/type/fresh
   variables, the Writer accumulates type-casting functions *)
module TypeM = struct

  type state = {
    mutable typemap : Def.type_def Map.t; (* maps types to their definitions *)
    mutable functions : unit Map.t; (* defined functions *)
    mutable knowns : Set.t; (* need this to determine inflow/outflow *)
    mutable typecasts : string; (* type-casted function arguments to be moved to the body *)
    mutable freshvaridx : int;
    mutable typevars : Set.t; (* type variables currently in scope *)
    mutable flipsub : bool; (* the subtyping direction is different for function arguments *)
    mutable typ_fams : Def.type_def Map.t (* multi-instance aliases *)
  }

  type 'a t = state -> 'a * state * string * string (* value, new state, util functions, parser functions *)

  let return x : 'a t = fun st -> (x, st, "", "")

  let append_sep a b sep =
    if a = "" then b else if b = "" then a else a ^ sep ^ b
  let append a b = append_sep a b "\n"

  let modify f : unit t = fun st -> ((), f st, "", "")

  (* there has to be a better way of doing this lol *)
  let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
    fun st0 ->
      let (a, st1, w1, p1) = m st0 in
      let (b, st2, w2, p2) = f a st1 in
      (b, st2, append w1 w2, append p1 p2)

  let ( let* ) = bind

  let tell (w : string) : unit t = fun st -> ((), st, w, "")
  let tell_if_nonempty (w : string) : unit t =
    if w = "" then return () else tell w

  let add_construct (f : string) : unit t =
    fun st -> ((), st, "", f)

  let get : state t = fun st -> (st, st, "", "")
  let put (st' : state) : unit t = fun _ -> ((), st', "", "")
  let get_knowns : Set.t t = fun st -> st.knowns, st, "", ""

  let add_typedef (name : string) (typedef : Def.type_def) : unit t =
    modify (fun st -> { st with typemap = Map.add name typedef st.typemap })

  let get_typedef (typename : string) : Def.type_def option t = fun st -> ((Map.find_opt typename st.typemap), st, "", "")

  let add_funcdef (name : string) : unit t =
    modify (fun st -> { st with functions = Map.add name () st.functions })

  let is_defined (funname : string) : bool t = fun st ->
    (Map.mem funname st.functions, st, "", "")

  let get_freshvar () : string t = fun st ->
    let var = Printf.sprintf "v%d" st.freshvaridx in
    st.freshvaridx <- st.freshvaridx + 1;
    (var, st, "", "")

  let get_typecasts () : string t =
    fun st -> (st.typecasts, st, "", "")

  let set_typecasts (xs : string) : unit t =
    modify (fun st -> { st with typecasts = xs })

  let get_flipsub () : bool t = fun st -> (st.flipsub, st, "", "")
  let set_flipsub b : unit t = modify (fun st -> { st with flipsub = b })

  let add_typecast (x : string) : unit t =
    modify (fun st -> { st with typecasts = append_sep st.typecasts x "\n" })

  let set_knowns (xs : Set.t) : unit t =
    modify (fun st -> { st with knowns = xs })

  let add_known (x : string) : unit t =
    modify (fun st -> { st with knowns = Set.add x st.knowns })

  let add_knowns (xs : string list) : unit t =
    modify (fun st ->
      let k = List.fold_left (fun acc s -> Set.add s acc) st.knowns xs in
      { st with knowns = k })

  let is_known (x: string) : bool t =
    fun st -> (Set.mem x st.knowns, st, "", "")

  let are_knowns (xs: Set.t) : bool t = fun st -> 
    (Set.subset xs st.knowns, st, "", "")

  let add_typevar (x : string) : unit t =
    modify (fun st -> { st with typevars = Set.add x st.typevars })

  let get_typevars () : Set.t t =
    fun st -> (st.typevars, st, "", "")

  let set_typevars (s : Set.t) : unit t =
    modify (fun st -> { st with typevars = s })

  let is_typevar (x : string) : bool t =
    fun st -> (Set.mem x st.typevars, st, "", "")

  let get_typ_fams () : (text * type_def) list t =
    fun st -> (Map.bindings st.typ_fams, st, "", "")

  let add_typ_fam (name : string) (typedef : Def.type_def) : unit t =
    modify (fun st -> { st with typ_fams = Map.add name typedef st.typ_fams })

  let set_typ_fams (s : Def.type_def Map.t) : unit t =
    modify (fun st -> { st with typ_fams = s })

  let is_typ_fam (name : string) : bool t =
    fun st -> (Map.mem name st.typ_fams, st, "", "")

  let concat_nonempty sep xs =
  xs |> List.filter (fun s -> s <> "") |> String.concat sep

  let rec iterM (f : 'a -> unit t) (xs : 'a list) : unit t =
    match xs with 
    | [] -> return ()
    | x :: xs -> 
      let* () = f x in
      iterM f xs

  let rec mapM (f : 'a -> 'b t) (xs : 'a list) : 'b list t =
    match xs with
    | []      -> return []
    | x :: xs ->
      let* y  = f x in
      let* ys = mapM f xs in
      return (y :: ys)

  let split3 xs =
    List.fold_right
      (fun (a, b, c) (as_, bs_, cs_) ->
        (a :: as_, b :: bs_, c :: cs_))
      xs
      ([], [], [])

  let rec foldM (f : 'a -> 'b -> 'b t) (acc : 'b) (xs : 'a list) : 'b t =
    match xs with
    | [] -> return acc
    | x :: xs ->
      let* acc' = f x acc in
      foldM f acc' xs

  let concat_mapM sep f xs =
    let* parts = mapM f xs in
    return (concat_nonempty sep parts)

  let concat_mapM2 sep f xs =
    let* parts = mapM f xs in
    let (lefts, rights) = List.split parts in 
    return (concat_nonempty sep lefts, concat_nonempty sep rights)

  let concat_mapM2' seps f xs =
    let* parts = mapM f xs in
    let (lefts, rights) = List.split parts in 
    return (concat_nonempty (List.nth seps 0) lefts, concat_nonempty (List.nth seps 1) rights)

  let fold_mapM3 seps seen f xs =
    foldM (fun x (left_acc, middle_acc, right_acc, seen) -> 
      let* (left, middle, right, seen') = f x seen in
      return ( append_sep left_acc left (List.nth seps 0),
               append_sep middle_acc middle (List.nth seps 1),
               append_sep right_acc right (List.nth seps 2),
               seen' )
    ) ("", "", "", seen) xs

  let concat_mapM3 seps f xs =
    let* parts = mapM f xs in
    let (lefts, middles, rights) = split3 parts in 
    return (concat_nonempty (List.nth seps 0) lefts, concat_nonempty (List.nth seps 1) middles, concat_nonempty (List.nth seps 2) rights)

  let mapMi (f : int -> 'a -> 'b t) (xs : 'a list) : 'b list t =
    let rec aux i = function
      | [] -> return []
      | x :: xs ->
        let* y = f i x in
        let* ys = aux (i + 1) xs in
        return (y :: ys)
    in
    aux 0 xs

  let rec allM (f : 'a -> 'b t) (xs : 'a list) : bool t =
    match xs with 
    | [] -> return true 
    | x::rest -> 
      let* b = f x in 
      if b then allM f rest else return false 

  let concat_mapMi sep f xs =
    let* parts = mapMi f xs in
    return (concat_nonempty sep parts)
  let catchM (thunk: unit -> 'a t) (handler : exn -> 'a t) : 'a t = fun st -> 
    try (thunk ()) st with
    | e -> handler e st

  let rec foldM f acc = function
  | [] -> return acc
  | x :: xs ->
      let* acc' = f acc x in
      foldM f acc' xs

  let eval m = 
    let st0 = { typemap = Map.empty; 
    functions = Map.empty;
    knowns = Set.empty;
    typecasts = "";
    freshvaridx = 0;
    typevars = Set.empty;
    flipsub = false;
    typ_fams = Map.empty
    } in 
    let (a, st1, w, p) = m st0 in (a, w, p) 

end

(* dont think this is used anymore *)
module NumConversions = struct
  type nat = int 
  type real = float 
  type rat = float
  let int_of_nat (n : nat) : int = n
  let nat_of_int (i : int) : nat = i

  let rat_of_int (i : int) : rat = float_of_int i
  let rat_of_nat (n : nat) : rat = float_of_int n
  let nat_of_rat (n : rat) : nat = int_of_float n
end

(* outdated now probably *)
let val_or_fail name val_ = match val_ with
  | Some v -> v
  | None -> failwith (name ^ ": No matching clause")

(* Using the standard mplus operator defined as :
    Some v <|> RHS -> Some v
    Does not work because the RHS is evaluated eagerly. If the RHS throws an error, it will be raised immediately. 
    To delay the evaluation we pass a thunk instead. 
    outdated now probably *)
let mplus (a : 'a option) (b : unit -> 'a option) : 'a option =
  match a with
  | Some _ -> a 
  | None -> b ()

(* Copied from ds.ml for now; but we use the generated ocaml types instead of the reference interpreter types *)
module Register (T : sig type t end) = struct
  type t = T.t
  let _register : t Map.t ref = ref Map.empty
  let _latest = ""

  let add name moduleinst = _register := Map.add name moduleinst !_register

  let add_with_var var moduleinst =
    let open Reference_interpreter.Source in
    add _latest moduleinst;
    match var with
    | Some name -> add name.it moduleinst
    | _ -> ()

  exception ModuleNotFound of string

  let find name =
    match Map.find_opt name !_register with
    | Some x -> x
    | None -> raise @@ ModuleNotFound name

  let get_module_name var =
    let open Reference_interpreter.Source in
    match var with
    | Some name -> name.it
    | None -> _latest
end

(* a clause may fail when
   * an expression does not match a pattern, i.e. in `let pattern = exp` (Match_failure)
   * subtyping/supertyping failure (SubtypingFailed)
   * an `-- if premise` is not satisfied (CondFailed)
   * a nested function call fails (NoMatchingClause) 
   * an option type is none (Invalid_argument) (not sure if this can happen) *)

exception SubtypingFailed
exception NoMatchingClause of string
exception CondFailed
exception UnanimatedArg of string

(* todo: gen try clauses instead of writing them *)
let rec try_clauses_0 clauses err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl () with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_0 rest err_msg
    | e -> raise e

let rec try_clauses_1 clauses arg err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl arg with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_1 rest arg err_msg
    | e -> raise e

let rec try_clauses_2 clauses arg1 arg2 err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl arg1 arg2 with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_2 rest arg1 arg2 err_msg
    | e -> raise e

let rec try_clauses_3 clauses arg1 arg2 arg3 err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl arg1 arg2 arg3 with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_3 rest arg1 arg2 arg3 err_msg
    | e -> raise e

let rec try_clauses_4 clauses arg1 arg2 arg3 arg4 err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl arg1 arg2 arg3 arg4 with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_4 rest arg1 arg2 arg3 arg4 err_msg
    | e -> raise e

let rec try_clauses_5 clauses arg1 arg2 arg3 arg4 arg5 err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl arg1 arg2 arg3 arg4 arg5 with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_5 rest arg1 arg2 arg3 arg4 arg5 err_msg
    | e -> raise e

let rec try_clauses_6 clauses arg1 arg2 arg3 arg4 arg5 arg6 err_msg = 
  match clauses with 
  | [] -> raise (NoMatchingClause err_msg)
  | cl :: rest -> 
    try cl arg1 arg2 arg3 arg4 arg5 arg6 with 
    | Match_failure _ | SubtypingFailed |  NoMatchingClause _ 
    | CondFailed | Invalid_argument _ -> try_clauses_6 rest arg1 arg2 arg3 arg4 arg5 arg6 err_msg
    | e -> raise e
  
(* get a list of all functions (transitively) called by a particular function *)
let rec exp_calls (e: exp) : Set.t = 
  match e.it with
  | NumE _ | TextE _ | BoolE _| VarE _ | OptE None -> Set.empty
  | ListE es | TupE es -> 
    List.fold_left Set.union Set.empty (List.map exp_calls es)
  | CallE (id, args) ->
    Set.add id.it (List.fold_left Set.union Set.empty (List.map arg_calls args))
  | CaseE (_, e1) | UnE (_, _, e1) | UncaseE (e1, _)
  | ProjE (e1, _) | IterE (e1, _) | SubE (e1, _, _) 
  | CvtE (e1, _, _) | OptE (Some e1) | LenE e1 
  | SliceE (e1, _, _) | DotE (e1, _) | LiftE e1 
  | TheE e1 -> exp_calls e1
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) 
  | IdxE (e1, e2) | CatE (e1, e2) | MemE (e1, e2) 
  | UpdE (e1, _, e2) | ExtE (e1, _, e2) 
  | CompE (e1, e2) -> Set.union (exp_calls e1) (exp_calls e2)
  | StrE expfieldlst -> 
    List.fold_left Set.union Set.empty (List.map (fun (_, e) -> exp_calls e) expfieldlst)

and arg_calls (arg : arg) : Set.t = 
  match arg.it with
  | ExpA e -> exp_calls e
  | _      -> Set.empty (* not sure if this is the case but works for now *)

let rec prem_calls (p : prem) : Set.t = 
  match p.it with
  | IfPr e | LetPr (_, e, _) -> exp_calls e
  | IterPr (prems, _) -> List.fold_left Set.union Set.empty (List.map prem_calls prems)
  | _ -> Set.empty

let f_calls (fdef : func_def) : Set.t =
  let (_, _, _, clauses, _) = fdef.it in
  List.fold_left Set.union Set.empty (List.map (fun (clause : clause) ->
    let DefD (_, _, e, prems) = clause.it in
    let from_e = exp_calls e in
    let from_prems = List.fold_left Set.union Set.empty (List.map prem_calls prems) in
    Set.union from_e from_prems
  ) clauses)

(* using a list for now, I think this is called very rarely - nvm it is called a lot *)
let rec find_fdef (flist : dl_def list) (name : string) : func_def =
  match flist with 
  | [] -> raise Not_found
  | FuncDef fdef :: rest -> 
    let (id, _, _, _, _) = fdef.it in 
    if id.it = name then fdef else 
    find_fdef rest name
  | (RecDef defs) :: rest -> 
    begin try 
      find_fdef defs name
    with Not_found -> 
      find_fdef rest name
    end
  | _ :: rest -> find_fdef rest name


(* temp -- for debugging only *)
(*open Il.Ast

let match_typ name (typ : Il.Ast.typ) = 
  match typ.it with 
  | VarT (id, _) -> (sanitize_name id.it) = name
  | _ -> false
let rec arg_occurs vars (arg : arg) =
  match arg.it with
  | ExpA e -> exp_occurs vars e
  | TypA typ -> Set.exists (fun name -> match_typ name typ) vars
  | _ -> false

and exp_occurs vars e = 
  if Set.exists (fun name -> match_typ name e.note) vars then true else
  match e.it with 
  | NumE _ | TextE _ | BoolE _| VarE _ | OptE None -> false
  | ListE es | TupE es -> List.exists (exp_occurs vars) es
  | CallE (id, args) -> List.exists (arg_occurs vars) args
  | CaseE (_, e1) | UnE (_, _, e1) | UncaseE (e1, _)
  | ProjE (e1, _) | IterE (e1, _) | OptE (Some e1) | LenE e1 
  | TheE e1 | DotE (e1, _) | LiftE e1 | SliceE (e1, _, _) 
  | CvtE (e1, _, _) -> exp_occurs vars e1
  | SubE (e1, typ1, typ2) -> 
    exp_occurs vars e1 || Set.exists (fun name -> match_typ name typ1) vars ||
    Set.exists (fun name -> match_typ name typ2) vars
  | BinE (_, _, e1, e2) | CmpE (_, _, e1, e2) | CompE (e1, e2) | MemE (e1, e2)
  | CatE (e1, e2) | IdxE (e1, e2) | UpdE (e1, _, e2) | ExtE (e1, _, e2) -> 
    exp_occurs vars e1 || exp_occurs vars e2
  | StrE expfieldlst -> 
    List.exists (fun (_, e) -> exp_occurs vars e) expfieldlst

let print_all_occ_cl fid vars ({it = DefD (_, params, ret, prems); _} : Def.func_clause) =
  let rec prem_occurs fid vars (p : prem) =
    match p.it with
    | IfPr e -> if exp_occurs vars e then 
      Printf.printf "Function %s: %s\n" fid (Il.Print.string_of_prem p)
    | LetPr (e1, e2, _) -> if exp_occurs vars e1 || exp_occurs vars e2 then 
      Printf.printf "Function %s: %s\n" fid (Il.Print.string_of_prem p)
    | IterPr (prems, _) -> List.iter (prem_occurs fid vars) prems
    | _ -> ()
  in 
  List.iter (prem_occurs fid vars) prems;
  if exp_occurs vars ret then 
    Printf.printf "Function %s: returns %s\n" fid (Il.Print.string_of_exp ret);
  (*List.iter (fun (param : param) ->
    match param.it with
    | ExpP (_, typ) -> 
      if Set.exists (fun name -> match_typ name typ) vars then
        Printf.printf "Function %s: parameter %s\n" fid (Il.Print.string_of_param param)
    | TypP id -> 
      if Set.exists (fun name -> name = (sanitize_name id.it)) vars then
        Printf.printf "Function %s: type parameter %s\n" fid (Il.Print.string_of_param param)
    | _ -> ()
  ) params*)
  if (List.exists (arg_occurs vars) params) then
    Printf.printf "Function %s: has parameters %s\n" fid 
      (String.concat ", " (List.map Il.Print.string_of_arg params))

let rec print_all_occurrences dl_defs vars =
  match dl_defs with
  | [] -> ()
  | FuncDef { it = fid, _ , _, fcl_list, _ ; _ } :: rest ->
    List.iter (print_all_occ_cl fid.it vars) fcl_list;
    print_all_occurrences rest vars
  | RecDef defs :: rest ->
    print_all_occurrences defs vars;
    print_all_occurrences rest vars
  | _ :: rest ->
    print_all_occurrences rest vars

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
  | TypA t1, TypA t2 -> is_eq_typ t1 t2
  | _ -> false (* for now idk how it works if a type is instantiated with an expression *)

let rec get_typedef name dl_defs =
  match dl_defs with
  | [] -> None
  | (TypeDef td)::rest -> let (tid, _, _) = td.it in
    if sanitize_name tid.it = name then Some td else get_typedef name rest
  | (RecDef defs)::rest ->
    match get_typedef name defs with
    | Some td -> Some td
    | None ->  get_typedef name rest

let rec replace_family_es vars dl_defs (e : exp) =
  let rewrite = replace_family_es vars dl_defs in
  let e' = match e.it with
  | VarE _ | BoolE _ | NumE _ | TextE _ -> e
  | UnE (op, t, e1) ->
    { e with it = UnE (op, t, rewrite e1) }
  | BinE (op, t, e1, e2) ->
    { e with it = BinE (op, t, rewrite e1, rewrite e2) }
  | CmpE (op, t, e1, e2) ->
    { e with it = CmpE (op, t, rewrite e1, rewrite e2) }
  | TupE es ->
    { e with it = TupE (List.map rewrite es) }
  | ProjE (e1, i) ->
    { e with it = ProjE (rewrite e1, i) }
  | CaseE (op, e1) ->
    { e with it = CaseE (op, rewrite e1) }
  | UncaseE (e1, op) ->
    { e with it = UncaseE (rewrite e1, op) }
  | OptE eo ->
    { e with it = OptE (Option.map rewrite eo) }
  | TheE e1 ->
    { e with it = TheE (rewrite e1) }
  | StrE fields ->
    let rewrite_field (a, e1) = (a, rewrite e1) in
    { e with it = StrE (List.map rewrite_field fields) }
  | DotE (e1, a) ->
    { e with it = DotE (rewrite e1, a) }
  | CompE (e1, e2) ->
    { e with it = CompE (rewrite e1, rewrite e2) }
  | ListE es ->
    { e with it = ListE (List.map rewrite es) }
  | LiftE e1 ->
    { e with it = LiftE (rewrite e1) }
  | MemE (e1, e2) ->
    { e with it = MemE (rewrite e1, rewrite e2) }
  | LenE e1 ->
    { e with it = LenE (rewrite e1) }
  | CatE (e1, e2) ->
    { e with it = CatE (rewrite e1, rewrite e2) }
  | IdxE (e1, e2) ->
    { e with it = IdxE (rewrite e1, rewrite e2) }
  | SliceE (e1, e2, e3) ->
    { e with it = SliceE (rewrite e1, rewrite e2, rewrite e3) }
  | UpdE (e1, p, e2) ->
    { e with it = UpdE (rewrite e1, p, rewrite e2) }
  | ExtE (e1, p, e2) ->
    { e with it = ExtE (rewrite e1, p, rewrite e2) }
  | CallE (id, args) ->
    let rewrite_arg (a : arg) = match a.it with 
      | ExpA arg_e -> { a with it = ExpA (rewrite arg_e) }
      | _ -> a
    in
    { e with it = CallE (id, List.map rewrite_arg args) }
  | IterE (e1, it) ->
    { e with it = IterE (rewrite e1, it) }
  | CvtE (e1, t1, t2) ->
    { e with it = CvtE (rewrite e1, t1, t2) }
  | SubE (e1, t1, t2) ->
    { e with it = SubE (rewrite e1, t1, t2) }
  in
  match e'.note.it with
  | VarT (id, args)
    when Set.mem (sanitize_name id.it) vars ->
      (* this type has multiple instances like: typename(<typeargs>) = AliasT (<othertype>). 
         we will go through its instances to check what type <args> gives us, and explicitly cast typename into <othertype> *)
      begin
        match get_typedef (sanitize_name id.it) dl_defs with
        | None -> e' (* error here *)
        | Some def ->
            let (_, _, insts) = def.it in
            try
              let { it = InstD (_, _, dt); _} = List.find (fun { it = InstD _, args', _; _} -> is_eq_args args args') insts in
              match dt.it with 
              | AliasT t ->
                { e' with it = SubE (e', e'.note, t) }
              | _ -> e' (* I don't think this should happen *)
            with Not_found -> e' (* the arg is not a concrete type (it could be a variable, for example - in which case we do not cast at all )*)
      end
  | _ -> e'

let replace_param (vars : Set.t) (dl_defs : dl_def list) (p : param) =
  match p.it with
  | ExpP (id, typP) -> 
    let { it = VarT(tid, args); _ } = typP in 
    if Set.mem (sanitize_name tid.it) vars then begin
      match get_typedef (sanitize_name tid.it) dl_defs with
      | None -> p (* error here *)
      | Some def ->
        let (_, _, insts) = def.it in
        try
          let { it = InstD (_, _, dt); _} = List.find (fun { it = InstD _, args', _; _} -> is_eq_args args args') insts in
          match dt.it with 
          | AliasT t ->
            { p with it = ExpP (id, t) }
          | _ -> p (* I don't think this should happen *)
        with Not_found -> p (* the arg is not a concrete type (it could be a variable, for example - in which case we do not cast at all )*)
    end else p
  | _ -> p

let replace_arg (vars : Set.t) (dl_defs : dl_def list) (a : arg) =
  match a.it with
  | ExpA e -> { a with it = ExpA (replace_family_es vars dl_defs e) }
  | _ -> a

let rec replace_prem (vars : Set.t) (dl_defs : dl_def list) (p : prem) =
  match p.it with
  | IfPr e -> { p with it = IfPr (replace_family_es vars dl_defs e) }
  | LetPr (e1, e2, b) -> { p with it = LetPr ((replace_family_es vars dl_defs) e1, (replace_family_es vars dl_defs e2), b) }
  | IterPr (prems, iter) -> { p with it = IterPr (List.map (replace_prem vars dl_defs) prems, iter) }
  | _ -> p

let replace_cls (vars : Set.t) (dl_defs : dl_def list) (cl : func_clause) =
  let { it = DefD (bs_, args, retexp, prems); _ } = cl in
  { cl with it = DefD (
    bs_,
    List.map (replace_arg vars dl_defs) args,
    replace_family_es vars dl_defs retexp,
    List.map (replace_prem vars dl_defs) prems) }

let rec rmv_families vars (dl_defs : dl_def list) = 
  let rec aux acc dl_defs' =
    match dl_defs' with
    | [] -> List.rev acc
    | (FuncDef fd)::rest ->
    let { it = fid, params, t, fcl_list, partial; _ } : func_def = fd in
    aux ((FuncDef { fd with it = fid, List.map (replace_param vars dl_defs) params, t, List.map (repalce_cls vars dl_defs) fcl_list, partial}) :: acc) rest
    | (RecDef defs)::rest -> aux ((RecDef (List.map (rmv_families vars) defs))::acc) rest
    | def::rest -> aux (def::acc) rest
  in 
  aux [] dl_defs*)