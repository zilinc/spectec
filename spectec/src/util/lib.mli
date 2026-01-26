(* Things that should be in the OCaml library... *)

module List :
sig
  val take : int -> 'a list -> 'a list (* raises Failure *)
  val drop : int -> 'a list -> 'a list (* raises Failure *)
  val take_from_back : int -> 'a list -> 'a list (* raises Failure *)
  val split : int -> 'a list -> 'a list * 'a list (* raises Failure *)
  val split_hd : 'a list -> 'a * 'a list (* raises Failure *)
  val split_last_opt : 'a list -> ('a list * 'a) option
  val split_last : 'a list -> 'a list * 'a (* raises Failure *)
  val last_opt : 'a list -> 'a option
  val last : 'a list -> 'a (* raises Failure *)
  val nub : ('a -> 'a -> bool) -> 'a list -> 'a list
  val filter_not : ('a -> bool) -> 'a list -> 'a list
  val flatten_opt : 'a option list -> 'a list option
  val fold_lefti : (int -> 'acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc
  val group_by : ('a -> 'a -> bool) -> 'a list -> 'a list list

  (**
  `combination xss`: Construct all the combinations of picking one element from each
  element in `xss`.
  Example:
    input : [["p11"; "p12"]; ["p21"; "p22"; "p23"]; ["p31"]]
    output: [["p11"; "p21"; "p31"]; ["p12"; "p21"; "p31"]; ["p11"; "p22"; "p31"];
             ["p12"; "p22"; "p31"]; ["p11"; "p23"; "p31"]; ["p12"; "p23"; "p31"]]
  *)
  val combinations : 'a list list -> 'a list list
  val find_indices : ('a -> bool) -> 'a list -> int list
  val fold_left1 : ('a -> 'a -> 'a) -> 'a list -> 'a
  val assoc_with : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b
  val assoc_with_opt : ('a -> 'a -> bool) -> 'a -> ('a * 'b) list -> 'b option

  (** Same as [List.split]. *)
  val unzip : ('a * 'b) list -> 'a list * 'b list
  val unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
  val unzip4 : ('a * 'b * 'c * 'd) list -> 'a list * 'b list * 'c list * 'd list
  val mapi2 : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
end

module Char :
sig
  val is_digit_ascii : char -> bool
  val is_uppercase_ascii : char -> bool
  val is_lowercase_ascii : char -> bool
  val is_letter_ascii : char -> bool
end

module String :
sig
  val implode : char list -> string
  val explode : string -> char list
  val replace : string -> string -> string -> string
  val shorten : ?cap:int -> string -> string
end

module Fun :
sig
  val curry : (('a * 'b) -> 'c) -> 'a -> 'b -> 'c
  val uncurry :  ('a -> 'b -> 'c) -> ('a * 'b) -> 'c
  val curry3 : (('a * 'b * 'c) -> 'd) -> 'a -> 'b -> 'c -> 'd
  val uncurry3 :  ('a -> 'b -> 'c -> 'd) -> ('a * 'b * 'c) -> 'd
  val both : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)
  val (>>>) : ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c)
  val (<***>) : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val (<.>) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c  (* Function composition *)
  val (>.>)  : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c (* Forward function composition *)
end

module Option:
sig
  val mplus : 'a option -> 'a option -> 'a option
  (* Note that `mconcat` has different semantics to `flatten_opt`: The former biases
     towards `Some`, whereas the latter biases towards `None`. `cat_opts_opt` is yet
     different: it collects all the `Some`s.
  *)
  val mconcat : 'a option list -> 'a option
  val mconcat_map : ('a -> 'b option) -> 'a list -> 'b option
  val cat_opts_opt : 'a option list -> 'a list option
  val opt_list : 'a list option -> 'a list
end

module Time:
sig
  val timer_off : unit -> unit
  val time : string -> ('a -> 'b) -> 'a -> 'b
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

module State (S : sig type t end) : MonadState with type s = S.t


module type MonadTrans = functor (M : Monad) ->
sig
  include Monad
  val lift : 'a M.m -> 'a m
end

module type Error =
sig
  type t
  val string_of_error : t -> string
end


module type MonadError = functor (E : Error) ->
sig
  include Monad
  val throw : E.t -> 'a m
end

module type MonadErrorTrans = functor (E : Error) (M : Monad) ->
sig
  include Monad
  val throw : E.t -> 'a m
  val lift : 'a M.m -> 'a m
end

module ExceptT (E : Error) (M : Monad) : sig
  include Monad
  val run_exceptT : 'a m -> ('a, E.t) result M.m
  val exceptT : ('a, E.t) result M.m -> 'a m
  val throw : E.t -> 'a m
  val lift : 'a M.m -> 'a m
end
