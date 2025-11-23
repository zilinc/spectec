let () =
  let results = [ Interpreter_ocaml.Dl_codegen.run_tests2 (); Interpreter_ocaml.Dl_codegen.run_tests3 (); Interpreter_ocaml.Dl_codegen.run_tests4 (); Interpreter_ocaml.Dl_codegen.run_tests5 () ] in
  if List.for_all ((=) 1) results then (print_endline "ALL TESTS PASSED")
  else (print_endline "SOME TESTS FAILED"; exit 1)

let () = 
  Backend_animation.Runner.run ()