val allow_partial_animation : bool ref
val animate : Il.Env.t -> Def.dl_def list -> Il.Env.t * Def.dl_def list
val env_of_quants : Il.Ast.quant list -> Il.Env.t ref -> Il.Env.t ref