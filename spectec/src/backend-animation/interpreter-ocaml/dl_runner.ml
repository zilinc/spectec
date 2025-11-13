open Backend_interpreter
open Reference_interpreter

let test_file = "./test-ocaml/sample.wat"
let parser = Parse.Script.parse_file

let run_wasm file = 
  let commands = parser file in
  Backend_animation.Temp_print.pp_script commands

let () =
  run_wasm test_file;
  let results = [ Interpreter_ocaml.Dl_codegen.run_tests2 (); Interpreter_ocaml.Dl_codegen.run_tests3 (); Interpreter_ocaml.Dl_codegen.run_tests4 (); Interpreter_ocaml.Dl_codegen.run_tests5 () ] in
  if List.for_all ((=) 1) results then (print_endline "ALL TESTS PASSED"; exit 0)
  else (print_endline "SOME TESTS FAILED"; exit 1)

