open Xl
open Il.Ast

(* FIXME: we project on ocaml lists/tuples not DL lists *)
let projE lst n =
  match lst with
  | ListE es -> (match List.nth_opt es n with
    | Some v -> v
    | None -> failwith "list too short")
  | _ -> failwith "projE: expected ListE"

let is_letter c = ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
let is_capital c = 'A' <= c && c <= 'Z'

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

(* OCaml convention:
   typenames and record fields are lowercased
   constructors have their first letter uppercased
   constructors cannot begin with non-letter chars
   type arguments are prefixed with a quote (') *)
let sanitize_name ?(typename=true) ?(typecons=false) ?(typearg=false) ?(recordfield = false) id =
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
  let lowercase name = sanitize_name ~typename:false ~recordfield name in
  match mixop with
  | [{it = Atom.Atom a; _}]::tail when List.for_all ((=) []) tail -> (*"Atom " ^*) lowercase a
  | mixop ->
    let s =
      String.concat "_pct_" (List.map (
        fun atoms -> String.concat "" (List.map (fun x -> x |> Atom.to_string |> lowercase) atoms)) mixop
      )
    in
    (*"Atom " ^*) s

(* let slice (lst : 'a list) (start : int) (len : int) : 'a list option =
  if start < 0 || len < 0 then None else
  let rec drop n l =
    match n, l with
    | 0, l -> Some l
    | _, [] -> None
    | n, _ :: tl -> drop (n-1) tl
  in
  let rec take n l =
    match n, l with
    | 0, _ -> Some []
    | _, [] -> None
    | n, x :: tl ->
        match take (n-1) tl with
        | Some rest -> Some (x :: rest)
        | None -> None
  in
  match drop start lst with
  | None -> None
  | Some after_drop -> take len after_drop

let rec lookup (x : id) (pairs : (id * 'b) list) : 'b option =
  match pairs with
  | [] -> None
  | (k,v) :: rest ->
      if k.it = x.it then Some v else lookup x rest*)

let rec update_at i v = function
  | _ :: xs when i = 0 -> v :: xs
  | x :: xs            -> x :: update_at (i - 1) v xs
  | [] -> failwith "update_at: index out of bounds" (* todo this is also a codegen error *)

(* todo: does update also take start and len or start and end?*)
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

let unzip_opt1 opt_a = Some opt_a

let unzip1M lst = lst 

let unzip2M (lst : ('a * 'b) list option) : (('a list * 'b list) option) =
  match lst with
  | None -> None
  | Some pairs -> Some (unzip2 pairs)

let unzip3M (lst : ('a * 'b * 'c) list option) : (('a list * 'b list * 'c list) option) =
  match lst with
  | None -> None
  | Some pairs -> Some (unzip3 pairs)

let map1 = List.map

let rec map2 f xs ys =
  match xs, ys with
  | x::xt, y::yt -> (f x y) :: map2 f xt yt
  | _ -> []

let rec map3 f xs ys zs =
  match xs, ys, zs with
  | x::xt, y::yt, z::zt -> (f x y z) :: map3 f xt yt zt
  | _ -> []

let rec map1M (f : 'a -> 'b option) (lst : 'a list) : ('b list option) =
  match lst with 
  | [] -> Some []
  | x :: rest -> 
    match f x with 
    | None -> None 
    | Some y -> 
      match map1M f rest with 
      | None -> None 
      | Some ys -> Some (y :: ys)

let rec map2M (f : 'a -> 'b -> 'c option) (lst1 : 'a list) (lst2 : 'b list) : (('a * 'b) list option) =
  match lst1, lst2 with 
  | [], [] -> Some []
  | x :: rest1, y :: rest2 -> 
    match f x y with 
    | None -> None 
    | Some y -> 
      match map2M f rest1 rest2 with 
      | None -> None 
      | Some ys -> Some (y :: ys)

let map_opt1 (f : 'a -> 'b) (opt_a : 'a option) : 'b =
  match opt_a with
  | Some a -> f a 
  | None -> failwith "TODO: optional iterator with None"

(* monadic (optional) maps for generated code *)

module TypeMap = Map.Make(String) 
module Set = Set.Make(String) 

(* A State+Writer monad: 
   The State keeps track of type definitions, known/bound/type/fresh
   variables, the Writer accumulates type-casting functions *)
module TypeM = struct

  type state = {
    mutable typemap : Def.dl_def TypeMap.t; (* maps types to their definitions *)
    mutable typeconvfuncs : Set.t; (* keeps track of type-conversion functions *)
    mutable knowns : Set.t; (* need this to determine inflow/outflow *)
    mutable typecasts : string; (* type-casted function arguments to be moved to the body *)
    mutable freshvaridx : int;
    mutable typevars : Set.t (* type variables currently in scope *)
  }

  type 'a t = state -> 'a * state * string  

  let return x : 'a t = fun st -> (x, st, "")

  let append_sep a b sep =
    if a = "" then b else if b = "" then a else a ^ sep ^ b
  let append a b = append_sep a b "\n"

  let bind (m : 'a t) (f : 'a -> 'b t) : 'b t =
    fun st0 ->
      let (a, st1, w1) = m st0 in
      let (b, st2, w2) = f a st1 in
      (b, st2, append w1 w2)

  let ( let* ) = bind

  let tell (w : string) : unit t = fun st -> ((), st, w)
  let tell_if_nonempty (w : string) : unit t =
    if w = "" then return () else tell w

  let get : state t = fun st -> (st, st, "")
  let put (st' : state) : unit t = fun _ -> ((), st', "")
  let modify f : unit t = fun st -> ((), f st, "")
  let get_knowns : Set.t t = fun st -> st.knowns, st, ""

  let add_typedef (name : string) (typedef : Def.dl_def) : unit t =
    modify (fun st -> { st with typemap = TypeMap.add name typedef st.typemap })

  let get_typedef (typename : string) : Def.dl_def option t = fun st -> ((TypeMap.find_opt typename st.typemap), st, "")

  let get_freshvar () : string t = fun st ->
      let var = Printf.sprintf "v%d" st.freshvaridx in
      st.freshvaridx <- st.freshvaridx + 1;
      (var, st, "")

  let get_typecasts () : string t =
    fun st -> (st.typecasts, st, "")

  let set_typecasts (xs : string) : unit t =
    modify (fun st -> { st with typecasts = xs })

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
    fun st -> (Set.mem x st.knowns, st, "")

  let are_knowns (xs: Set.t) : bool t = fun st -> 
    (Set.subset xs st.knowns, st, "")
  let is_defined (x : string) : bool t =
    fun st -> (Set.mem x st.typeconvfuncs, st, "")

  let add_func (x : string) : unit t =
    modify (fun st -> { st with typeconvfuncs = Set.add x st.typeconvfuncs })

  let add_typevar (x : string) : unit t =
    modify (fun st -> { st with typevars = Set.add x st.typevars })

  let get_typevars () : Set.t t =
    fun st -> (st.typevars, st, "")

  let set_typevars (s : Set.t) : unit t =
    modify (fun st -> { st with typevars = s })

  let is_typevar (x : string) : bool t =
    fun st -> (Set.mem x st.typevars, st, "")

  let concat_nonempty sep xs =
  xs |> List.filter (fun s -> s <> "") |> String.concat sep

  let rec mapM (f : 'a -> 'b t) (xs : 'a list) : 'b list t =
    match xs with
    | []      -> return []
    | x :: xs ->
      let* y  = f x in
      let* ys = mapM f xs in
      return (y :: ys)

  let concat_mapM sep f xs =
    let* parts = mapM f xs in
    return (concat_nonempty sep parts)

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
    let st0 = { typemap = TypeMap.empty; 
    typeconvfuncs = Set.empty;
    knowns = Set.empty;
    typecasts = "";
    freshvaridx = 0;
    typevars = Set.empty
    } in 
    let (a, _, w) = m st0 in (a, w) 

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

let val_or_fail = function 
  | Some v -> v
  | None -> failwith "No matching clause"

(* Using the standard mplus operator defined as :
    Some v <|> RHS -> Some v
    does not work because the RHS is evaluated eagerly. So if the RHS throws an error, it will be raised immediately. To delay the evaluation we pass a thunk instead. *)
let mplus (a : 'a option) (b : unit -> 'a option) : 'a option =
  match a with
  | Some _ -> a 
  | None -> b ()
