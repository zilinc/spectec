open Util.Error
open Util.Source
open Value
open State_v
open Construct_v
module RI = Reference_interpreter


(* Host *)

let il_of_spectest () : value =

  (* Helper functions *)
  let i32_to_const i = caseV [["CONST"];[]] [ nullary "I32"; vl_of_uN_32   i ] in
  let i64_to_const i = caseV [["CONST"];[]] [ nullary "I64"; vl_of_uN_64   i ] in
  let f32_to_const f = caseV [["CONST"];[]] [ nullary "F32"; vl_of_float32 f ] in
  let f64_to_const f = caseV [["CONST"];[]] [ nullary "F64"; vl_of_float64 f ] in


  (* TODO: Change this into host function instance, instead of current normal function instance.
     TODO(zilinc): what does it mean?
  *)
  let create_funcinst name ptypes =
    let code = nullary (String.uppercase_ascii name) in  (* instr *)
    let param_types = List.map nullary ptypes  (* list(valtype) *) in
    let comptype = caseV [["FUNC"];["->"];[]] [
      vl_of_list' param_types;
      vl_of_list' []
    ] in
    let subtype = caseV [["SUB"];[];[];[]] [
      optV (Some (nullary "FINAL"));
      listV [||];
      comptype
    ] in
    let rectype = caseV [["REC"];[]] [
      vl_of_list' [subtype]
    ] in
    let deftype = caseV [["_DEF"];[];[]] [
      rectype; vl_of_nat 0
    ] in
    let funccode = caseV [["FUNC"];[];[];[]] [
      vl_of_nat 0;
      listV_of_list [];
      listV_of_list [code]
    ] in
    name, strV [
      "TYPE"  , deftype;
      "MODULE", (strV []); (* dummy module *)
      "CODE"  , funccode
    ] in

  let create_globalinst t v =
    let valtype = nullary t in
    let globaltype = caseV [[];[]] [ none; valtype ] in
    strV [ ("TYPE", globaltype); ("VALUE" , v ) ]
  in

  let create_tableinst t =
    let addrtype = nullary t in
    let limits   = caseV [["["];[".."];["]"]] [
      vl_of_nat 10; vl_of_nat 20
    ] in
    let reftype  = caseV [["REF"];[];[]] [
      some (nullary "NULL");
      nullary "FUNC"
    ] in
    let tabletype = caseV [[];[];[];[]] [
      addrtype; limits; reftype
    ] in
    let func = nullary "FUNC" in
    let nulls = listV (Array.init 10 (Fun.const (caseV [["REF.NULL"];[]] [func]))) in
    strV [ ("TYPE", tabletype); ("REFS", nulls) ]
  in

  let create_meminst t =
    let addrtype = nullary t in
    let limits   = caseV [["["];[".."];["]"]] [
      vl_of_nat 1; vl_of_nat 2
    ] in
    let memtype = caseV [[];[];["PAGE"]] [
      addrtype; limits
    ] in
    let zeros = listV (Array.init 0x20 (Fun.const (vl_of_nat 0))) in  (* 0x10000 *)
    strV [ ("TYPE", memtype); ("BYTES", zeros) ] in

  (* Builtin functions *)
  let funcs = [
    create_funcinst "print"         [            ];
    create_funcinst "print_i32"     ["I32"       ];
    create_funcinst "print_i64"     ["I64"       ];
    create_funcinst "print_f32"     ["F32"       ];
    create_funcinst "print_f64"     ["F64"       ];
    create_funcinst "print_i32_f32" ["I32"; "F32"];
    create_funcinst "print_f64_f64" ["F64"; "F64"];
  ] in

  (* Builtin globals *)
  let globals = [
    "global_i32", 666   |> RI.I32.of_int_u |> i32_to_const |> create_globalinst "I32";
    "global_i64", 666   |> RI.I64.of_int_u |> i64_to_const |> create_globalinst "I64";
    "global_f32", 666.6 |> RI.F32.of_float |> f32_to_const |> create_globalinst "F32";
    "global_f64", 666.6 |> RI.F64.of_float |> f64_to_const |> create_globalinst "F64";
  ] in

  (* Builtin tables *)
  let tables = [
    "table"  , create_tableinst "I32";
    "table64", create_tableinst "I64";
  ] in

  (* Builtin memories *)
  let memories = [
    "memory"  , create_meminst "I32";
    "memory64", create_meminst "I64";
  ] in

  let tags = [] in

  let append kind (name, inst) exinsts =

    let kinds = kind ^ "S" in

    (* Generate exportinst *)

    let addr =
      match Store.access kinds with
      | ListV a -> Array.length !a
      | _ -> assert false
    in
    let new_inst =
      strV [ ("NAME", textV name); ("ADDR", caseV [[kind];[]] [ vl_of_nat addr ]) ]
    in

    (* Update Store *)

    Store.update kinds (function
    | ListV vs -> listV (Array.append !vs [|inst|])
    | _ -> assert false
    );

    new_inst :: exinsts in

  (* extern -> new_extern *)
  let append_func_extern   = List.fold_right (append "FUNC"  ) funcs    in
  let append_global_extern = List.fold_right (append "GLOBAL") globals  in
  let append_table_extern  = List.fold_right (append "TABLE" ) tables   in
  let append_memory_extern = List.fold_right (append "MEM"   ) memories in
  let append_tag_extern    = List.fold_right (append "TAG"   ) tags     in

  let exportinsts =
    []
    |> append_func_extern
    |> append_global_extern
    |> append_table_extern
    |> append_memory_extern
    |> append_tag_extern
    |> listV_of_list
  in

  let moduleinst = strV
                          [ ("TYPES"  , listV [||])
                          ; ("TAGS"   , listV [||])
                          ; ("GLOBALS", listV [||])
                          ; ("MEMS"   , listV [||])
                          ; ("TABLES" , listV [||])
                          ; ("FUNCS"  , listV [||])
                          ; ("ELEMS"  , listV [||])
                          ; ("DATAS"  , listV [||])
                          ; ("EXPORTS", exportinsts)
                          ]
  in
  moduleinst


(* Host instructions *)

let is_host = function
  | "PRINT" | "PRINT_I32" | "PRINT_I64" | "PRINT_F32" | "PRINT_F64" | "PRINT_I32_F32" | "PRINT_F64_F64" -> true
  | _ -> false

(*
let call name =
  let local =
    WasmContext.get_current_context "FRAME_"
    |> unwrap_framev
    |> strv_access "LOCALS"
    |> listv_nth
  in
  let as_const ty = function
  | CaseV ("CONST", [ CaseV (ty', []) ; n ])
  | OptV (Some (CaseV ("CONST", [ CaseV (ty', []) ; n ]))) when ty = ty' -> n
  | v -> raise (Exception.ArgMismatch ("Not " ^ ty ^ ".CONST: " ^ string_of_value v)) in

  match name with
  | "PRINT" -> print_endline "- print: ()"
  | "PRINT_I32" ->
    local 0
    |> as_const "I32"
    |> al_to_nat32
    |> I32.to_string_s
    |> Printf.printf "- print_i32: %s\n"
  | "PRINT_I64" ->
    local 0
    |> as_const "I64"
    |> al_to_nat64
    |> I64.to_string_s
    |> Printf.printf "- print_i64: %s\n"
  | "PRINT_F32" ->
    local 0
    |> as_const "F32"
    |> al_to_float32
    |> F32.to_string
    |> Printf.printf "- print_f32: %s\n"
  | "PRINT_F64" ->
    local 0
    |> as_const "F64"
    |> al_to_float64
    |> F64.to_string
    |> Printf.printf "- print_f64: %s\n"
  | "PRINT_I32_F32" ->
    let i32 = local 0 |> as_const "I32" |> al_to_nat32 |> I32.to_string_s in
    let f32 = local 1 |> as_const "F32" |> al_to_float32 |> F32.to_string in
    Printf.printf "- print_i32_f32: %s %s\n" i32 f32
  | "PRINT_F64_F64" ->
    let f64 = local 0 |> as_const "F64" |> al_to_float64 |> F64.to_string in
    let f64' = local 1 |> as_const "F64" |> al_to_float64 |> F64.to_string in
    Printf.printf "- print_f64_f64: %s %s\n" f64 f64'
  | name -> raise (Exception.UnknownFunc ("No spectest function: " ^ name))

*)

