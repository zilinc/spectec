open Ast

type env = Env.t
type subst = Subst.t

val is_normal_exp : exp -> bool
val is_head_normal_exp : exp -> bool
val is_cnf : exp -> bool

val cnf_if_prim : exp -> exp


type 'a result = ('a, 'a) Result.t
  (* For errors, term is the last one before taking the failing step. *)

val (let*) : 'a option -> ('a -> 'a option) -> 'a option
val (let**) : 'a result -> ('a -> 'a result) -> 'a result
val (let***) : 'a option result -> ('a -> 'a option result) -> 'a option result

val reduce_exp : env -> exp -> exp result
val reduce_typ : env -> typ -> typ result
val reduce_typdef : env -> typ -> deftyp result
val reduce_arg : env -> arg -> arg result
val reduce_fncall_hook : (env -> Util.Source.region -> typ -> id -> arg list -> exp) ref
val reduce_prems : env -> Subst.subst -> prem list -> [`True of Subst.t | `False | `None]
val reduce_exp_call : env -> id -> arg list -> Util.Source.region -> clause list -> exp option

val equiv_functyp : env -> param list * typ -> param list * typ -> bool
val equiv_typ : env -> typ -> typ -> bool
val sub_typ : env -> typ -> typ -> bool

val match_iter : env -> subst -> iter -> iter -> subst option result
val match_exp : env -> subst -> exp -> exp -> subst option result
val match_typ : env -> subst -> typ -> typ -> subst option result
val match_arg : env -> subst -> arg -> arg -> subst option result

val match_list :
  (env -> subst -> 'a -> 'a -> subst option result) ->
  env -> subst -> 'a list -> 'a list -> subst option result
