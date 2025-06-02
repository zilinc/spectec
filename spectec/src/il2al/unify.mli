open Il.Ast
open Def

type env

val rename : bool ref

val init_env : Free.Set.t -> env

(** [unify r h]: [r] toggle rule unification; [h] toggle helper unification *)
val unify : bool -> bool -> dl_def list -> dl_def list

val unify_rules : env -> rule list -> rule list
