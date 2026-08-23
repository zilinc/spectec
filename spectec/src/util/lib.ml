let fst3 (x, _, _) = x
let snd3 (_, y, _) = y
let thd3 (_, _, z) = z

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
  let (<.>) g f = fun x -> g (f x)
  let (>.>) f g = fun x -> f x |> g
end

module Option =
struct
  let mplus oa ob = match oa, ob with
  | Some a, _      -> Some a
  | None  , None   -> None
  | None  , Some b -> Some b
  let mconcat oxs = List.fold_left mplus None oxs
  let mconcat_map f xs = List.map f xs |> mconcat
  let cat_opts oxs = List.filter_map Stdlib.Fun.id oxs
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
  let timer : bool ref = ref true
  let timer_off () = timer := false
  let time msg f a =
    if !timer then
      let start = Sys.time () in
      let b = f a in
      let lapsed = Sys.time () -. start in
      print_endline (msg ^ ": " ^ Printf.sprintf "%.5fs." lapsed);
      b
    else
      f a
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

module type MonadLogger =
sig
  include Monad
  type w
  val push     : w -> unit m
  val pop      : unit -> w m
  val drop     : unit -> unit m
  val clear    : unit -> unit m
  val new_with : w -> unit m
  val run_logger : 'a m -> 'a * w list
end

module State (S : sig type t end) : MonadState with type s = S.t = struct
  type s = S.t
  type 'a m = State of (s -> ('a * s))
  let state f = State f
  let run_state (State m) s = m s
  let get () = state (fun s -> (s, s))
  let put s = state (fun _ -> ((), s))
  let return a = state (fun s -> (a, s))
  let fail () = raise (Failure "State")
  let ( >>= ) ma f = state (fun s -> let (a, s') = run_state ma s in
                                     run_state (f a) s')
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let ( <$> ) f (State r) = State (fun s -> let (a, s') = r s in (f a, s'))
  let ( <&> ) ma f = f <$> ma
  let rec mapM f = function
    | [] -> return []
    | x::xs -> let* x'  = f x in
               let* xs' = mapM f xs in
               return (x'::xs')
  let mapiM f xs =
    let rec mapiM' f i = function
    | [] -> return []
    | x::xs -> let* x'  = f i x in
               let* xs' = mapiM' f (i+1) xs in
               return (x'::xs')
    in
    mapiM' f 0 xs
  let iterM f xs = mapM f xs >> return ()
  let opt_mapM f = function
    | None -> return None
    | Some a -> let* b = f a in return (Some b)
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> raise (Invalid_argument "empty list is invalid")
    | x::xs -> foldlM f x xs
  let update f = let* s = get () in put (f s)
  let update_get_old f = let* s = get () in put (f s) >> return s
  let update_get_new f = let* s = get () in let s' = f s in put s' >> return s'
end

module type MonadTrans = functor (M : Monad) ->
sig
  include Monad
  val lift : 'a M.m -> 'a m
end

module type Error = sig
  type t
  val string_of_error : t -> string
end

module StringError : Error with type t = string = struct
  type t = string
  let string_of_error s = s
end

module type MonadError = functor (E : Error) ->
sig
  include Monad
  val throw : E.t -> 'a m
end

module Except : functor (E : Error) ->
sig
  include Monad
  val throw : E.t -> 'a m
  val run_except : 'a m -> ('a, E.t) result
end = functor (E : Error) ->
struct
  type 'a m = ('a, E.t) result
  let return x = Ok x
  let throw e = Error e
  let run_except m = m
  let fail () = failwith "Except"
  let ( >>= ) m f = match m with Ok x -> f x | Error e -> Error e
  let ( let* ) = ( >>= )
  let ( >=> ) f g x = f x >>= g
  let ( >> ) ma mb = ma >>= fun _ -> mb
  let ( <$> ) f = function Ok x -> Ok (f x) | Error e -> Error e
  let ( <&> ) ma f = f <$> ma
  let rec mapM f = function
    | [] -> return []
    | x :: xs -> let* x' = f x in let* xs' = mapM f xs in return (x' :: xs')
  let iterM f xs = mapM f xs >> return ()
  let mapiM f xs =
    let rec go i = function
      | [] -> return []
      | x :: xs -> let* x' = f i x in let* xs' = go (i+1) xs in return (x' :: xs')
    in go 0 xs
  let opt_mapM f = function
    | None   -> return None
    | Some x -> let* y = f x in return (Some y)
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []      -> return b
    | x :: xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | []      -> invalid_arg "empty list"
    | x :: xs -> foldlM f x xs
end


module type MonadErrorTrans = functor (E : Error) (M : Monad) ->
sig
  include Monad
  val throw : E.t -> 'a m
  val lift : 'a M.m -> 'a m
end


module ExceptT = functor (E : Error) (M : Monad) ->
struct
  open Result
  type 'a m = ExceptT of (('a, E.t) result) M.m
  let run_exceptT (ExceptT m) = m
  let exceptT m = ExceptT m
  let return x = ExceptT (Ok x |> M.return)
  let fail x = ExceptT (M.fail x)
  let ( >>= ) ma f = ExceptT (
    let open M in
    run_exceptT ma >>= function
    | Error e -> return (Error e)
    | Ok    a -> run_exceptT (f a))
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let ( <$> ) f (ExceptT m) = ExceptT (
    let open M in
    let* r = m in
    (match r with
    | Ok a -> Ok (f a)
    | Error e -> Error e
    ) |> return
  )
  let ( <&> ) ma f = f <$> ma
  let rec mapM f = function
    | [] -> return []
    | x::xs -> let* x'  = f x in
               let* xs' = mapM f xs in
               return (x'::xs')
  let mapiM f xs =
    let rec mapiM' f i = function
    | [] -> return []
    | x::xs -> let* x'  = f i x in
               let* xs' = mapiM' f (i+1) xs in
               return (x'::xs')
    in
    mapiM' f 0 xs
  let iterM f xs = mapM f xs >> return ()
  let opt_mapM f = function
    | None -> return None
    | Some a -> let* b = f a in return (Some b)
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> invalid_arg "empty list is invalid"
    | x::xs -> foldlM f x xs
  let lift m = ExceptT (let open M in let* x = m in return (Ok x))
  let throw e = ExceptT (M.return (Error e))
end

module type LogEntry = sig type t end

module Logger (LE : LogEntry) =
struct
  type w = LE.t
  type 'a m = Logger of (w list -> ('a * w list))
  let unlogger (Logger x) w = x w
  let run_logger m = unlogger m []

  let push w = Logger (fun ws -> ((), w::ws))
  let pop () = Logger (function
  | [] -> invalid_arg "Cannot pop empty logger."
  | w::ws -> w, ws
  )
  let drop () = Logger (function
  | []    -> (), []
  | _::ws -> (), ws
  )
  let clear () = Logger (fun _ -> (), [])
  let new_with w = Logger (fun _ -> (), [w])

  let return a = Logger (fun w -> (a, w))
  let fail () = failwith "Logger"
  let ( >>= ) (Logger f) g = Logger (fun w ->
    let (a, w') = f w in unlogger (g a) w'
  )
  let ( let* ) = ( >>= )
  let ( >=> ) f g = fun x -> (f x >>= fun y -> g y)
  let ( >> ) ma f = ma >>= fun _ -> f
  let ( <$> ) f (Logger r) = Logger (fun w -> let (a, w') = r w in (f a, w'))
  let ( <&> ) ma f = f <$> ma
  let rec mapM f = function
    | [] -> return []
    | x::xs -> let* x'  = f x in
               let* xs' = mapM f xs in
               return (x'::xs')
  let mapiM f xs =
    let rec mapiM' f i = function
    | [] -> return []
    | x::xs -> let* x'  = f i x in
               let* xs' = mapiM' f (i+1) xs in
               return (x'::xs')
    in
    mapiM' f 0 xs
  let iterM f xs = mapM f xs >> return ()
  let opt_mapM f = function
    | None -> return None
    | Some a -> let* b = f a in return (Some b)
  let forM xs f = mapM f xs
  let rec foldlM f b = function
    | []    -> return b
    | x::xs -> f b x >>= fun x' -> foldlM f x' xs
  let foldlM1 f = function
    | [] -> raise (Invalid_argument "empty list is invalid")
    | x::xs -> foldlM f x xs
end

module ExceptLogger (E : Error)(LE : LogEntry) = struct
  module L = Logger(LE)
  module X = ExceptT(E)(L)
  include X
  type w = LE.t
  let push w = X.lift (L.push w)
  let pop () = X.lift (L.pop ())
  let drop () = X.lift (L.drop ())
  let clear () = X.lift (L.clear ())
  let new_with w = X.lift (L.new_with w)
  let run_logger m = L.run_logger (X.run_exceptT m)
end
