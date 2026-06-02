open Il.Ast
open Util.Source
open Il.Walk


let preamble = "" (* TODO *)

let convert_def (target : Il.Ast.def) : string = failwith ""


let convert_script (il : script) : string =
  preamble ^
  "(* Generated Code *)\n" ^
  String.concat "" (List.map (convert_def true false))