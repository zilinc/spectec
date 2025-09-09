open Xl
open Il.Ast

(* this is wrong, need a case statement for every possible type *)
let uncaseE (e : exp) op =
  match e.it with
  | CaseE (o, e) when (Mixop.eq o op) ->
    (match e.it with
    | TupE tupe -> ListE tupe (* convert tuple to list in case we need to index *)
    | e' -> e')
  | _ -> failwith "uncase: expected UncaseE"

(* maybe we don't need to throw error and just return None *)
let projE lst n =
  match lst with
  | ListE es -> (match List.nth_opt es n with
    | Some v -> v
    | None -> failwith "list too short")
  | _ -> failwith "projE: expected ListE"

let mixop_to_atom_str ?(recordfield = false) (mixop : Mixop.mixop) =
  let lowercase name =
      if recordfield then String.lowercase_ascii name
      else name
  in
  match mixop with
  | [{it = Atom.Atom a; _}]::tail when List.for_all ((=) []) tail -> (*"Atom " ^*) lowercase a
  | mixop ->
    let s =
      String.concat "_pct_" (List.map (
        fun atoms -> String.concat "" (List.map (fun x -> x |> Atom.to_string |> lowercase) atoms)) mixop
      )
    in
    (*"Atom " ^*) s

let slice (lst : 'a list) (start : int) (end_ : int) : 'a list option =
  if start < 0 || end_ < start then None else
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
  | Some after_drop -> take (end_ - start) after_drop

let rec lookup (x : id) (pairs : (id * 'b) list) : 'b option =
  match pairs with
  | [] -> None
  | (k,v) :: rest ->
      if k.it = x.it then Some v else lookup x rest

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

let map1 = List.map
let rec map2 (f : 'a -> 'b -> 'c) (lst : ('a * 'b) list) : ('c list) =
  match lst with 
  | [] -> []
  | (x, y) :: rest -> (f x y) :: (map2 f rest)
let rec map3 (f : 'a -> 'b -> 'c -> 'd) (lst : ('a * 'b * 'c) list) : ('d list) =
  match lst with
  | [] -> []
  | (x, y, z) :: rest -> (f x y z) :: (map3 f rest)

module TypeMap = Map.Make(String) 
module Set = Set.Make(String) 

(* A State+Writer monad: 
   The State keeps track of type definitions and known 
   variables, the Writer accumulates type-casting functions *)
module TypeM = struct

  type state = {
    mutable typemap : Def.dl_def TypeMap.t; (* maps types to their definitions*)
    mutable typeconvfuncs : Set.t; (* keeps track of type-conversion functions *)
    mutable knowns : Set.t; (* need this to determine inflow/outflow *)
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

  (* maybe dont need this? *)
  let are_knowns (xs: Set.t) : bool t =
    fun st -> (Set.subset xs st.knowns, st, "")

  let is_defined (x : string) : bool t =
    fun st -> (Set.mem x st.typeconvfuncs, st, "")

  let add_func (x : string) : unit t =
    modify (fun st -> { st with typeconvfuncs = Set.add x st.typeconvfuncs })

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

  let concat_mapMi sep f xs =
    let* parts = mapMi f xs in
    return (concat_nonempty sep parts)

  let lift_pair1 (m1 : string t) : (string * string) t =
    fun st0 ->
      let (a, st1, w1) = m1 st0 in
      ((a, ""), st1, w1)

  let lift_pair2 (m2 : string t) : (string * string) t =
    fun st0 ->
      let (a, st1, w1) = m2 st0 in
      (("", a), st1, w1)

  (*let run m st0  = m st0*)              
  let eval m = 
    let st0 = { typemap = TypeMap.empty; 
    typeconvfuncs = Set.empty;
    knowns = Set.empty
    } in 
    let (a, _, w) = m st0 in (a, w) 

end

