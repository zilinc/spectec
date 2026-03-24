val allow_partial_animation : bool ref
val animate : (Def.dl_def list * Il.Ast.script) -> Il.Env.t * Def.dl_def list
val env_of_quants : Il.Ast.quant list -> Il.Env.t ref -> Il.Env.t ref