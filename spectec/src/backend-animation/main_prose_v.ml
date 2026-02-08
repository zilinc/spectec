open Prose_v

let text_prose dl ofile =
  let prose = text_prose_script dl in
  let oc = open_out ofile in
  Printf.fprintf oc "%s\n" prose;
  close_out oc;
  ()
