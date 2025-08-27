(* The .wast stuff *)

open Il.Ast
open Util.Error
open Util.Source


(* Register *)

module Map = Map.Make (String)

module Register = struct
  let _register : Il.Ast.exp Map.t ref = ref Map.empty
  let _latest = ""

  let add name moduleinst = _register := Map.add name moduleinst !_register

  let add_with_var var moduleinst =
    let open Reference_interpreter.Source in
    add _latest moduleinst;
    match var with
    | Some name -> add name.it moduleinst
    | _ -> ()

  exception ModuleNotFound of string

  let find name =
    match Map.find_opt name !_register with
    | Some x -> x
    | None -> raise (ModuleNotFound name)

  let get_module_name var =
    let open Reference_interpreter.Source in
    match var with
    | Some name -> name.it
    | None -> _latest
end



(* Host *)

let il_of_spectest () : exp = todo "spectest"

