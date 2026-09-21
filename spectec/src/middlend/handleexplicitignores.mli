(* Strips any def tagged hint(nobackendrender), and its own HintD entry, from
   the script -- see handleexplicitignores.ml for the full explanation. This
   is expected to run before every other pass, so that nothing downstream
   (undep's well-formedness lemmas, typefamilyremoval's projections,
   totalize's catch-alls, deftorel's relation conversion, ...) ever sees the
   ignored def and generates a companion for it.

   Errors (via Error.error) if an ignored def is still referenced -- as a
   call, a higher-order argument, a relation premise, a type use, or a
   grammar use -- anywhere else in the script, rather than silently leaving
   a dangling reference for some later pass to fail on more confusingly. *)
val transform : Il.Ast.script -> Il.Ast.script
