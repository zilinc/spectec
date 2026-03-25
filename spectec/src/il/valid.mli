val valid : Ast.script -> unit (* raises Error.Error *)
val valid_binders : (Env.t -> 'a -> Env.t) -> Env.t -> 'a list -> Env.t

val valid_param : Env.t -> Ast.param -> Env.t
val valid_inst : Env.t -> Ast.quant list -> Ast.inst -> unit
val valid_typ : Env.t -> Ast.typ -> unit
val valid_clause : Env.t -> Ast.id -> Ast.param list -> Ast.typ -> Ast.clause -> unit

val valid_params : Env.t -> Ast.param list -> Env.t
