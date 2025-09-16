open Il.Ast
open Il.Print
open Util
open Error
open Source
open Il_util
module Ds = Backend_interpreter.Ds
module RI = Reference_interpreter

(* TODO(zilinc): Properly convert Il expression to RI type and run the checker,
   and get back the result expression.
*)
let dummy : exp = varE ~note:(t_var "dummyT") "dummyE"

(* Errors *)

let verbose : string list ref =
  ref []

let error at msg = Error.error at "Animate/Relation" msg
let error_np msg = error no_region msg

let info v at msg = if List.mem v !verbose || v = "" then
                      print_endline (string_of_region at ^ " Animate/Relation info[" ^ v ^ "]:\n" ^ msg)
                    else
                      ()


(* $Ref_ok : store -> ref -> reftype *)
let ref_ok s ref : exp = todo "$Ref_ok"
(*
  (* TODO: some / none *)
  let null = some "NULL" in
  let nonull = none "NULL" in
  let none = nullary "NONE" in
  let nofunc = nullary "NOFUNC" in
  let noexn = nullary "NOEXN" in
  let noextern = nullary "NOEXTERN" in

  let match_heaptype v1 v2 =
    let ht1 = Construct.al_to_heaptype v1 in
    let ht2 = Construct.al_to_heaptype v2 in
    Match.match_reftype [] (Types.Null, ht1) (Types.Null, ht2)
  in

  match ref with
  (* null *)
  | [CaseV ("REF.NULL", [ ht ]) as v] ->
    if match_heaptype none ht then
      CaseV ("REF", [ null; none])
    else if match_heaptype nofunc ht then
      CaseV ("REF", [ null; nofunc])
    else if match_heaptype noexn ht then
      CaseV ("REF", [ null; noexn])
    else if match_heaptype noextern ht then
      CaseV ("REF", [ null; noextern])
    else
      Numerics.error_typ_value "$Reftype" "null reference" v
  (* i31 *)
  | [CaseV ("REF.I31_NUM", [ _ ])] -> CaseV ("REF", [ nonull; nullary "I31"])
  (* host *)
  | [CaseV ("REF.HOST_ADDR", [ _ ])] -> CaseV ("REF", [ nonull; nullary "ANY"])
  (* exception *)
  | [CaseV ("REF.EXN_ADDR", [ _ ])] -> CaseV ("REF", [ nonull; nullary "EXN"])
  (* array/func/struct addr *)
  | [CaseV (name, [ NumV (`Nat i) ])]
  when String.starts_with ~prefix:"REF." name && String.ends_with ~suffix:"_ADDR" name ->
    let field_name = String.sub name 4 (String.length name - 9) in
    let object_ = listv_nth (Ds.Store.access (field_name ^ "S")) (Z.to_int i) in
    let dt = strv_access "TYPE" object_ in
    CaseV ("REF", [ nonull; dt])
  (* extern *)
  (* TODO: check null *)
  | [CaseV ("REF.EXTERN", [ _ ])] -> CaseV ("REF", [ nonull; nullary "EXTERN"])
  | vs -> Numerics.error_values "$Reftype" vs
*)

(* $Module_ok : module -> moduletype *)
let module_ok (module_: arg) : exp =
  match module_.it with
  | ExpA module_' -> dummy
  | _ -> error module_.at ("Wrong argument sort to function $Module_ok. Got: " ^ string_of_arg module_)
(*
  match module_ with
  | [ m ] ->
    (try
      let module_ = Construct.al_to_module m in
      let ModuleT (its, ets) = Reference_interpreter.Valid.check_module module_ in
      let importtypes = List.map (fun (Types.ImportT (_, _, xt)) -> Construct.al_of_externtype xt) its in
      let exporttypes = List.map (fun (Types.ExportT (_, xt)) -> Construct.al_of_externtype xt) ets in
      CaseV ("->", [ listV_of_list importtypes; listV_of_list exporttypes ])
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ()))
    )

  | vs -> Numerics.error_values "$Module_ok" vs
*)

(* $Externaddr_ok : store -> externaddr -> externtype *)
let externaddr_ok s eaddr =
  match s.it, eaddr.it with
  | ExpA s', ExpA eaddr' -> dummy
  | _ , ExpA _ -> error s.at     ("1st argument to function $Externaddr_ok has wrong sort. Got: " ^ string_of_arg s    )
  | ExpA _ , _ -> error eaddr.at ("2nd argument to function $Externaddr_ok has wrong sort. Got: " ^ string_of_arg eaddr)
(* match eaddr with
  | [ CaseV (name, [ NumV (`Nat z) ]); t ] ->
    (try
      let addr = Z.to_int z in
      let externaddr_type =
        name^"S"
        |> Store.access
        |> unwrap_listv_to_array
        |> fun arr -> Array.get arr addr
        |> strv_access "TYPE"
        |> fun type_ -> CaseV (name, [type_])
        |> Construct.al_to_externtype
      in
      let externtype = Construct.al_to_externtype t in
      boolV (Match.match_externtype [] externaddr_type externtype)
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Externaddr_ok" vs
*)

(* $Val_ok : store -> val -> valtype *)
let val_ok s val_ = todo "$Val_ok"
(*
function
  | [ v; t ] ->
    let value = Construct.al_to_value v in
    let valtype = Construct.al_to_valtype t in
    (try
      boolV (Match.match_valtype [] (Value.type_of_value value) valtype)
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Val_ok" vs
*)

(*
(* Rule `Expand` has been compiled to `$expanddt` in animation.ml *)
let expand = function
  | [ v ] ->
    (try
      v
      |> Construct.al_to_deftype
      |> Types.expand_deftype
      |> Construct.al_of_comptype
    with exn -> raise (Exception.Invalid (exn, Printexc.get_raw_backtrace ())))
  | vs -> Numerics.error_values "$Expand" vs
*)

(* $Eval_expr : state -> expr -> (state * exp) *)
let eval_expr st exp : exp = todo "$Eval_expr"

let mem name =
  List.mem name ["Ref_ok"; "Module_ok"; "Externaddr_ok"; "Val_ok"; "Eval_expr"]

let call_func name (args: arg list) : exp =
  let nargs = List.length args in
  match name with
  | "Ref_ok"        when nargs = 2 -> ref_ok        (List.nth args 0) (List.nth args 1)
  | "Module_ok"     when nargs = 1 -> module_ok     (List.nth args 0)
  | "Externaddr_ok" when nargs = 2 -> externaddr_ok (List.nth args 0) (List.nth args 1)
  | "Val_ok"        when nargs = 2 -> val_ok        (List.nth args 0) (List.nth args 1)
  | "Eval_expr"     when nargs = 2 -> eval_expr     (List.nth args 0) (List.nth args 1)
  | _ -> assert false
