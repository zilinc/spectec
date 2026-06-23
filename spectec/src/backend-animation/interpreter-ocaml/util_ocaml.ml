open Xl
open Il.Ast
open Def 


let logging = ref false

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
    '/', "_slash";
    '#', "_hash"
  ] in
  let replaced = List.fold_left (fun acc (ch, repl) ->
    String.concat repl (String.split_on_char ch acc)
  ) raw replacements in
  match replaced with
  | "match" | "type" | "let" | "val" | "list" | "in" | "module" -> replaced ^ "_"
  | _ -> replaced 

let mixop_to_atom_str ?(recordfield = false) (mixop : 'a Mixop.mixop) =
  let frmt name = sanitize_name ~typename:false ~recordfield name in
  match mixop with
  | Atom a -> frmt (Atom.to_string a)
  | mixop -> 
    (* let s =
      String.concat "_pct_" (List.map (
        fun atoms -> String.concat "" (List.map (fun x -> x |> Atom.to_string |> frmt) atoms)) mixop
      )
    in s*)
    (* JUST DO THIS FOR NOW: *)
    Mixop.to_string mixop

let val_mixop_to_str ?(recordfield = false) (mixop : string list list) =
  (*Printf.printf "mixop to atom: %s\n" (Mixop.to_string mixop);
  Printf.printf "is polymorphic?: %b\n" is_poly;*)
  let frmt name = sanitize_name ~typename:false ~recordfield name in
  match mixop with
  | [s]::tail when List.for_all ((=) []) tail -> frmt s
  | mixop ->
    let s =
      String.concat "_pct_" (List.map (
        fun atoms -> String.concat "" (List.map (fun x -> frmt x) atoms)) mixop
      )
    in s

let rec update_at_in i v = function
  | _ :: xs when i = 0 -> v :: xs
  | x :: xs            -> x :: update_at_in (i - 1) v xs
  | [] -> failwith "update_at: index out of bounds" 

let update_at i v = update_at_in (Z.to_int i) v

let update_slice_in l i len l' =
  let n = List.length l in
  if i < 0 || len < 0 || i + len > n || List.length l' <> len then
    failwith "update_slice: invalid indices";
  let prefix = List.take i l in
  let suffix = List.drop (i + len) l in
  prefix @ l' @ suffix

let update_slice l i len l' = update_slice_in l (Z.to_int i) (Z.to_int len) l'

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

let unzip4 (lst : ('a * 'b * 'c * 'd) list) : ('a list * 'b list * 'c list * 'd list) =
  let rec aux acc1 acc2 acc3 acc4 = function
    | [] -> (List.rev acc1, List.rev acc2, List.rev acc3, List.rev acc4)
    | (w, x, y, z) :: rest -> aux (w :: acc1) (x :: acc2) (y :: acc3) (z :: acc4) rest
  in
  aux [] [] [] [] lst

let unzip_opt1 opt_a = opt_a

let unzip_opt3 opt = match opt with 
  | Some (opt_a, opt_b, opt_c) -> (Some opt_a, Some opt_b, Some opt_c)
  | None -> None, None, None

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
    mutable max_args : int; (* the maximum number of args that any function takes *)
    mutable max_zip : int; (* the max int i for which unzip_i is called *)
    mutable builtins : string list; (* list of built-in functions - todo: may no longer be used *)
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

  let add_builtin (name : string) : unit t =
    modify (fun st -> { st with builtins = name::st.builtins })

  let is_builtin (name : string) : bool t =
    fun st -> (List.mem name st.builtins, st, "", "")

  (* TODO: try_clauses, unzip%d and map%d can all be generated at once in the end instead of generating them each time we see a new number *)
  let gen_try_cl i =
    let args = List.init i (fun j -> Printf.sprintf "arg%d" j) in
    let args_str = String.concat " " args in
    let call_str = if i = 0 then "cl ()" else "cl " ^ args_str in
    let rec_call = if i = 0 then Printf.sprintf "try_clauses_0 rest err_msg (idx+1)"
                   else Printf.sprintf "try_clauses_%d rest %s err_msg (idx+1)" i args_str in
    let header = if i = 0 then "try_clauses_0 clauses err_msg idx"
                 else Printf.sprintf "try_clauses_%d clauses %s err_msg idx" i args_str in
    if !logging then
    Printf.sprintf
      "let rec %s = \n\
      \  match clauses with \n\
      \  | [] -> \n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \       String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \       String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \       String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"no matching clause in %%s\\n%%!\" err_msg;\n\
      \      raise (NoMatchingClause err_msg)\n\
      \  | cl :: rest -> \n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \       String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \       String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \       String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"trying clause %%d of %%s\\n%%!\" idx err_msg;\n\
      \    try \n\
      \      let res = %s in\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg || \n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \      Printf.printf \"%%s accepted at clause %%d\\n%%!\" err_msg idx;\n\
      \      res\n\
      \    with\n\
      \    | Match_failure _ as e ->\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"clause %%d failed with %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        %s\n\
      \    | SubtypingFailed as e ->\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"clause %%d failed with %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        %s\n\
      \    | NoMatchingClause _ as e ->\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"clause %%d failed with %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        %s\n\
      \    | CondFailed as e ->\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"clause %%d failed with %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        %s\n\
      \    | Invalid_argument _ as e ->\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"clause %%d failed with %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        %s\n\
      \    | CompositionFailed as e ->\n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then
      \        Printf.printf \"clause %%d failed with %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        %s\n\
      \    | e -> \n\
      \      if String.starts_with ~prefix:\"function: step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: dispatch\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: uc_step\" err_msg ||\n\
      \         String.starts_with ~prefix:\"function: reduce\" err_msg then\n\
      \        Printf.printf \"unexpected exception at clause %%d: %%s\\n%%!\" idx (Printexc.to_string e);\n\
      \        raise e\n"
      header call_str rec_call rec_call rec_call rec_call rec_call rec_call
      else 
      Printf.sprintf "let rec %s = match clauses with \n\
      \ | [] -> raise (NoMatchingClause err_msg)\n\
      \ | cl :: rest ->\n\
      \ try %s with \n\
      \ | Match_failure _ | SubtypingFailed | NoMatchingClause _ \n\
      \ | CondFailed | Invalid_argument _ | CompositionFailed -> %s\n\
      \ | e -> raise e\n" header call_str rec_call

  let gen_try_cls a : unit t =
    let* st = get in
    if a <= st.max_args then return ()
    else
      let new_clauses =
        String.concat "\n"
          (List.init (a - st.max_args) (fun i -> gen_try_cl (st.max_args + 1 + i)))
      in
      let* () = tell new_clauses in
      modify (fun st -> { st with max_args = max st.max_args a })
  let gen_unzip_cl i =
    if i = 1 then "let unzip1 lst = lst\n" else
    let vars = List.init i (fun j -> Printf.sprintf "%c" (Char.chr (97 + j))) in
    let tup_type = String.concat " * " (List.map (fun v -> Printf.sprintf "'%s" v) vars) in
    let ret_type = String.concat " * " (List.map (fun v -> Printf.sprintf "'%s list" v) vars) in
    let pat = String.concat ", " vars in
    let accs = List.init i (fun j -> Printf.sprintf "acc%d" j) in
    let acc_args = String.concat " " accs in
    let acc_init = String.concat " " (List.map (fun _ -> "[]") accs) in
    let acc_updates = String.concat " " (List.mapi (fun j v -> Printf.sprintf "(%s :: acc%d)" v j) vars) in
    let rev_result = String.concat ", " (List.map (fun a -> Printf.sprintf "List.rev %s" a) accs) in
    Printf.sprintf
      "let unzip%d (lst : (%s) list) : (%s) =\n\
      \  let rec aux %s = function\n\
      \    | [] -> (%s)\n\
      \    | (%s) :: rest -> aux %s rest\n\
      \  in\n\
      \  aux %s lst\n"
      i tup_type ret_type acc_args rev_result pat acc_updates acc_init

  let gen_unzip_cls a : unit t =
    let* st = get in
    if a <= st.max_zip then return ()
    else
    let new_unzips =
      String.concat "\n"
        (List.init (a - st.max_zip) (fun i -> gen_unzip_cl (st.max_zip + 1 + i)))
    in
    let* () = tell new_unzips in
    modify (fun st -> { st with max_zip = max st.max_zip a })

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

  (* major refactor needed *)
  let concat_mapM2' seps f xs =
    let* parts = mapM f xs in
    let (lefts, rights) = List.split parts in
    let (lefts, rights) = List.flatten lefts, List.flatten rights in
    let rec rmv_duplicates seen acc lst = 
      match lst with 
      | [] -> List.rev acc
      | l :: ls -> 
      if Set.mem l seen then rmv_duplicates seen acc ls else
      rmv_duplicates (Set.add l seen) (l :: acc) ls
    in
    let lefts', rights' = rmv_duplicates Set.empty [] lefts, rmv_duplicates Set.empty [] rights in
    return (concat_nonempty (List.nth seps 0) lefts', concat_nonempty (List.nth seps 1) rights')

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
      max_args = -1;
      max_zip = 0;
      builtins = [];
      } in 
    let (a, st1, w, p) = m st0 in (a, w, p) 

end

(* ====== outdated now probably ====== *)
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
(* ====== ====== ====== *)

(* a clause may fail when
   * an expression does not match a pattern, i.e. in `let pattern = exp` (Match_failure)
   * subtyping/supertyping failure (SubtypingFailed)
   * an `-- if premise` is not satisfied (CondFailed)
   * a nested function call fails (NoMatchingClause) 
   * an option type is none (Invalid_argument) (not sure if this can happen)
   * a +++ b where both a and b are of the form Some _  *)

exception SubtypingFailed
exception NoMatchingClause of string
exception CondFailed
exception UnanimatedArg of string
exception CompositionFailed

let compose_opt x y = match x, y with
  | None  , None   -> None
  | None  , Some y -> Some y
  | Some x, None   -> Some x
  | Some _, Some _ -> raise CompositionFailed
  
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
  | IterPr (prem, _) -> prem_calls prem
  | _ -> Set.empty

let f_calls (fdef : func_def) : Set.t =
  let (_, _, _, _, clauses, _) = fdef.it in
  List.fold_left Set.union Set.empty (List.map (fun (fclause : func_clause) ->
    let _, clause = fclause in
    let DefD (_, _, e, prems) = clause.it in
    let from_e = exp_calls e in
    let from_prems = List.fold_left Set.union Set.empty (List.map prem_calls prems) in
    Set.union from_e from_prems
  ) clauses)

(* using a list for now *)
let rec find_fdef (flist : dl_def list) (name : string) : func_def =
  match flist with 
  | [] -> raise Not_found
  | FuncDef fdef :: rest -> 
    let (id, _, _, _, _, _) = fdef.it in 
    if id.it = name then fdef else 
    find_fdef rest name
  | (RecDef defs) :: rest -> 
    begin try 
      find_fdef defs name
    with Not_found -> 
      find_fdef rest name
    end
  | _ :: rest -> find_fdef rest name

let ( let* ) = TypeM.bind

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
    print_all_occurrences rest vars*)

let atom_to_ocaml_str (a : Atom.atom) : string =
  let it_str = match a.it with
    | Atom.Atom s      -> Printf.sprintf "Xl.Atom.Atom \"%s\"" s
    | Atom.Infinity    -> "Xl.Atom.Infinity"
    | Atom.Bot         -> "Xl.Atom.Bot"
    | Atom.Top         -> "Xl.Atom.Top"
    | Atom.Dot         -> "Xl.Atom.Dot"
    | Atom.Dot2        -> "Xl.Atom.Dot2"
    | Atom.Dot3        -> "Xl.Atom.Dot3"
    | Atom.Semicolon   -> "Xl.Atom.Semicolon"
    | Atom.Backslash   -> "Xl.Atom.Backslash"
    | Atom.Mem         -> "Xl.Atom.Mem"
    | Atom.NotMem      -> "Xl.Atom.NotMem"
    | Atom.Arrow       -> "Xl.Atom.Arrow"
    | Atom.Arrow2      -> "Xl.Atom.Arrow2"
    | Atom.ArrowSub    -> "Xl.Atom.ArrowSub"
    | Atom.Arrow2Sub   -> "Xl.Atom.Arrow2Sub"
    | Atom.Colon       -> "Xl.Atom.Colon"
    | Atom.ColonSub    -> "Xl.Atom.ColonSub"
    | Atom.Sub         -> "Xl.Atom.Sub"
    | Atom.Sup         -> "Xl.Atom.Sup"
    | Atom.Assign      -> "Xl.Atom.Assign"
    | Atom.Equal       -> "Xl.Atom.Equal"
    | Atom.EqualSub    -> "Xl.Atom.EqualSub"
    | Atom.NotEqual    -> "Xl.Atom.NotEqual"
    | Atom.Less        -> "Xl.Atom.Less"
    | Atom.Greater     -> "Xl.Atom.Greater"
    | Atom.LessEqual   -> "Xl.Atom.LessEqual"
    | Atom.GreaterEqual-> "Xl.Atom.GreaterEqual"
    | Atom.Equiv       -> "Xl.Atom.Equiv"
    | Atom.EquivSub    -> "Xl.Atom.EquivSub"
    | Atom.Approx      -> "Xl.Atom.Approx"
    | Atom.ApproxSub   -> "Xl.Atom.ApproxSub"
    | Atom.SqArrow     -> "Xl.Atom.SqArrow"
    | Atom.SqArrowSub  -> "Xl.Atom.SqArrowSub"
    | Atom.SqArrowStar -> "Xl.Atom.SqArrowStar"
    | Atom.SqArrowStarSub -> "Xl.Atom.SqArrowStarSub"
    | Atom.Prec        -> "Xl.Atom.Prec"
    | Atom.Succ        -> "Xl.Atom.Succ"
    | Atom.Turnstile   -> "Xl.Atom.Turnstile"
    | Atom.TurnstileSub-> "Xl.Atom.TurnstileSub"
    | Atom.Tilesturn   -> "Xl.Atom.Tilesturn"
    | Atom.TilesturnSub-> "Xl.Atom.TilesturnSub"
    | Atom.Quest       -> "Xl.Atom.Quest"
    | Atom.Plus        -> "Xl.Atom.Plus"
    | Atom.Star        -> "Xl.Atom.Star"
    | Atom.Comma       -> "Xl.Atom.Comma"
    | Atom.Cat         -> "Xl.Atom.Cat"
    | Atom.Bar         -> "Xl.Atom.Bar"
    | Atom.BigAnd      -> "Xl.Atom.BigAnd"
    | Atom.BigOr       -> "Xl.Atom.BigOr"
    | Atom.BigAdd      -> "Xl.Atom.BigAdd"
    | Atom.BigMul      -> "Xl.Atom.BigMul"
    | Atom.BigCat      -> "Xl.Atom.BigCat"
    | Atom.LParen      -> "Xl.Atom.LParen"
    | Atom.RParen      -> "Xl.Atom.RParen"
    | Atom.LBrack      -> "Xl.Atom.LBrack"
    | Atom.RBrack      -> "Xl.Atom.RBrack"
    | Atom.LBrace      -> "Xl.Atom.LBrace"
    | Atom.RBrace      -> "Xl.Atom.RBrace"
  in
  Printf.sprintf "{it=%s; at=no; note={Xl.Atom.def=\"\"; case=\"\"}; mark=false}" it_str

(* let mixop_to_ocaml_str (mixop : 'a Mixop.mixop) : string =
  "[" ^
  String.concat "; "
    (List.map (fun atoms ->
      "[" ^ String.concat "; " (List.map atom_to_ocaml_str atoms) ^ "]"
    ) mixop) ^
  "]"*)
(* just temporary till i reconcile IL changes *)
let mixop_to_ocaml_str (mixop : 'a Mixop.mixop) : string =
  Mixop.to_string mixop

