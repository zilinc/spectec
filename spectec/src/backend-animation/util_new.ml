open Xl
open Il.Ast 

let uncaseE (e : exp) op =
  match e.it with
  | CaseE (o, e) when (Mixop.eq o op) -> 
    (match e.it with 
    | TupE tupe -> ListE tupe (* convert tuple to list in case we need to index *)
    | e' -> e')
  | _ -> failwith "uncase: expected UncaseE"

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

(* this is a bad way of doing it but works for now *)
module TypeMap = Map.Make(String) 
module TypeSet = Set.Make(String) 

(* A state+writer monad *)
module TypeM = struct

  type types = {
    mutable typemap : Def.dl_def TypeMap.t; (* maps types to their definitions*)
    mutable typeconvfuncs : TypeSet.t; (* keeps track of type-conversion functions *)
  }

  type 'a t = types -> 'a * types * string  

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

  let get : types t = fun st -> (st, st, "")
  let put (st' : types) : unit t = fun _ -> ((), st', "")
  let modify f : unit t = fun st -> ((), f st, "")

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

  (* runners *)
  let run m st0  = m st0               (* -> (a, st1, log) *)
  let eval m st0 = let (a, _, w) = m st0 in (a, w)  (* -> (result_string, accumulated_string) *)
end

