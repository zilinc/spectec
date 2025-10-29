module List =
struct
  include List

  let rec take n xs =
    match n, xs with
    | 0, _ -> []
    | n, x::xs' when n > 0 -> x :: take (n - 1) xs'
    | _ -> failwith "take"

  let rec drop n xs =
    match n, xs with
    | 0, _ -> xs
    | n, _::xs' when n > 0 -> drop (n - 1) xs'
    | _ -> failwith "drop"


  let take_from_back n xs =
    List.rev xs |> take n |> List.rev

  let rec split n xs =
    match n, xs with
    | 0, _ -> [], xs
    | n, x::xs' when n > 0 ->
      let xs1', xs2' = split (n - 1) xs' in x::xs1', xs2'
    | _ -> failwith "split"

  let split_hd = function
    | x::xs -> x, xs
    | _ -> failwith "split_hd"

  let rec split_last_opt' ys = function
    | x::[] -> Some (List.rev ys, x)
    | x::xs -> split_last_opt' (x::ys) xs
    | [] -> None
  let split_last_opt xs = split_last_opt' [] xs
  let split_last l = Option.get (split_last_opt l)

  let last_opt l = Option.map snd (split_last_opt l)
  let last l = snd (split_last l)

  let rec nub pred = function
    | [] -> []
    | x::xs -> x :: nub pred (List.filter (fun y -> not (pred x y)) xs)

  let filter_not pred = List.filter (fun x -> not (pred x))

  let rec flatten_opt = function
    | [] -> Some []
    | None::_ -> None
    | (Some x)::xos ->
      match flatten_opt xos with
      | Some xs -> Some (x::xs)
      | None -> None

  let fold_lefti f init xs =
    let rec aux i acc xs =
      match xs with
      | [] -> acc
      | hd :: tl -> aux (i+1) (f i acc hd) tl
    in
    aux 0 init xs

  let group_by eq xs =
    let rec aux acc xs =
      match xs with
      | [] -> acc
      | hd :: tl ->
        let same, diff = List.partition (fun g ->
          eq hd (List.hd g)
        ) acc in
        match same with
        | [group] -> aux (diff @ [group @ [hd]]) tl
        | _ -> aux (acc @ [[hd]]) tl
    in
    aux [] xs

  let rec combinations xss =
    let (let*) ma f = List.concat_map f ma in
    let return x = [x] in
    match xss with
    | [] -> return []
    | xs :: xss' ->
        let* x = xs in
        let* rest = combinations xss' in
        return (x :: rest)

  let find_indices p xs : int list =
    let indices = ref [] in
    List.iteri (fun i x -> if p x then indices := i :: !indices else ()) xs;
    List.rev !indices

  let fold_left1 f = function
    | []    -> assert false
    | x::xs -> List.fold_left f x xs

  let rec assoc_with f y = function
    | []    -> raise Not_found
    | (k,v)::xs -> if f k y then v else assoc_with f y xs

  let assoc_with_opt f y xs = match assoc_with f y xs with
    | exception Not_found -> None
    | v -> Some v

  let unzip = List.split

  let rec unzip3 = function
    | [] -> ([], [], [])
    | (x, y, z)::xyzs -> let (xs, ys, zs) = unzip3 xyzs in (x::xs, y::ys, z::zs)

  let rec unzip4 = function
    | [] -> ([], [], [], [])
    | (x, y, z, w)::xyzws -> let (xs, ys, zs, ws) = unzip4 xyzws in (x::xs, y::ys, z::zs, w::ws)

  let[@tail_mod_cons] rec mapi2' i f l1 l2 =
    match (l1, l2) with
    | ([], []) -> []
    | ([a1], [b1]) ->
        let r1 = f i a1 b1 in
        [r1]
    | (a1::a2::l1, b1::b2::l2) ->
        let r1 = f i a1 b1 in
        let r2 = f (i+1) a2 b2 in
        r1::r2::mapi2' (i+2) f l1 l2
    | (_, _) -> invalid_arg "Lib.List.mapi2"
  let mapi2 f l1 l2 = mapi2' 0 f l1 l2
end

module Char =
struct
  let is_digit_ascii c = '0' <= c && c <= '9'
  let is_uppercase_ascii c = 'A' <= c && c <= 'Z'
  let is_lowercase_ascii c = 'a' <= c && c <= 'z'
  let is_letter_ascii c = is_uppercase_ascii c || is_lowercase_ascii c
end

module String =
struct
  include String

  let implode cs =
    let buf = Buffer.create 80 in
    List.iter (Buffer.add_char buf) cs;
    Buffer.contents buf

  let explode s =
    let cs = ref [] in
    for i = String.length s - 1 downto 0 do cs := s.[i] :: !cs done;
    !cs

  let replace pattern replacement s =
    Str.global_replace (Str.regexp_string pattern) replacement s

  let shorten ?(cap=100) s =
    let l = String.length s in
    if l > cap then String.sub s 0 cap ^ "..." ^ String.sub s (l-cap) cap else s
end

module Fun =
struct
  let curry f a b = f (a, b)
  let uncurry f (a, b) = f a b
  let curry3 f a b c = f (a, b, c)
  let uncurry3 f (a, b, c) = f a b c
  let both f (a1, a2) = (f a1, f a2)
  let (>>>) f g = fun x -> x |> f |> g
  let (<***>) f g (a, b) = (f a, g b)
end

module Option =
struct
  let mplus oa ob = match oa, ob with
  | Some a, _      -> Some a
  | None  , None   -> None
  | None  , Some b -> Some b
  let mconcat oxs = List.fold_left mplus None oxs
  let mconcat_map f xs = List.map f xs |> mconcat
  let cat_opts_opt oxs =
    let f acc ox = match acc, ox with
    | None, None -> None
    | None, Some x -> Some [x]
    | Some ys, None -> Some ys
    | Some ys, Some x -> Some (x::ys)
    in
    List.fold_left f None oxs
  let opt_list = function
    | None -> []
    | Some ls -> ls
end

module Time =
struct
  let time msg f a =
    let start = Sys.time () in
    let b = f a in
    let lapsed = Sys.time () -. start in
    print_endline (msg ^ ": " ^ Printf.sprintf "%.5fs." lapsed);
    b
end


module type Monad =
sig
  type 'a m
  val return : 'a -> 'a m
  val fail : unit -> 'a m
  val ( >>= ) : 'a m -> ('a -> 'b m) -> 'b m
  val ( let* ) : 'a m -> ('a -> 'b m) -> 'b m
  val ( >=> ) : ('a -> 'b m) -> ('b -> 'c m) -> 'a -> 'c m
  val ( >> ) : 'a m -> 'b m -> 'b m
  val ( <$> ) : ('a -> 'b) -> 'a m -> 'b m
  val ( <&> ) : 'a m -> ('a -> 'b) -> 'b m
  val mapM : ('a -> 'b m) -> 'a list -> 'b list m
  val iterM : ('a -> 'b m) -> 'a list -> unit m
  val mapiM : (int -> 'a -> 'b m) -> 'a list -> 'b list m
  val opt_mapM : ('a -> 'b m) -> 'a option -> 'b option m
  val forM : 'a list -> ('a -> 'b m) -> 'b list m
  val foldlM : ('b -> 'a -> 'b m) -> 'b -> 'a list -> 'b m
  val foldlM1 : ('a -> 'a -> 'a m) -> 'a list -> 'a m
end

module type MonadState =
sig
  include Monad
  type s
  val get : unit -> s m
  val put : s -> unit m
  val update : (s -> s) -> unit m
  val update_get_old : (s -> s) -> s m
  val update_get_new : (s -> s) -> s m
  val state : (s -> ('a * s)) -> 'a m
  val run_state : 'a m -> s -> ('a * s)
end

module type MonadTrans = functor (M : Monad) ->
sig
  include Monad
  val lift : 'a M.m -> 'a m
end
