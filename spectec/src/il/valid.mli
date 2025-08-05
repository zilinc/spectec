val valid : Ast.script -> unit (* raises Error.Error *)

val local_env : Env.t ref -> Env.t ref

val valid_param : Env.t ref -> Ast.param -> unit
val valid_inst : Env.t ref -> Ast.param list -> Ast.inst -> unit
val valid_typ : Env.t -> Ast.typ -> unit
val valid_clause : Env.t ref -> Ast.param list -> Ast.typ -> Ast.clause -> unit
