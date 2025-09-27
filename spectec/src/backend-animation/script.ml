open Il.Ast
open Util.Error
open Util.Source
open Il_util
open State
module RI = Reference_interpreter


(* Host *)

let il_of_spectest () : exp =

  (* Helper functions *)
  let i32_to_const i = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "I32"; Construct.il_of_uN_32   i ] in
  let i64_to_const i = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "I64"; Construct.il_of_uN_64   i ] in
  let f32_to_const f = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "F32"; Construct.il_of_float32 f ] in
  let f64_to_const f = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "F64"; Construct.il_of_float64 f ] in


  (* TODO: Change this into host function instance, instead of current normal function instance.
     TODO(zilinc): what does it mean?
  *)
  let create_funcinst name ptypes =
    let code = mk_nullary' "instr" (String.uppercase_ascii name) in  (* instr *)
    let param_types = List.map (mk_nullary' "numtype") ptypes  (* list(valtype) *) in
    let comptype = mk_case' "comptype" [["FUNC"];["->"];[]] [
      listE (t_var "resulttype") param_types;
      listE (t_var "resulttype") []
    ] in
    let subtype = mk_case' "subtype" [["SUB"];[];[];[]] [
      optE (t_var "fin") (Some (mk_nullary' "" "FINAL"));
      listE (t_star "typeuse") [];
      comptype
    ] in
    let rectype = mk_case' "rectype" [["REC"];[]] [
      listE (t_app "list" [typA (t_var "subtype")]) [subtype]
    ] in
    let deftype = mk_case' "deftype" [["_DEF"];[];[]] [
      rectype; mk_nat 0
    ] in
    let func = mk_case' "func" [["FUNC"];[];[];[]] [

    ] in
    let funccode = mk_case' "funccode" [["FUNC"];[];[];[]] [
      mk_nat 0;
      listE (t_star "local") [];
      listE (t_var "expr") [code]
    ] in
    name, mk_str "funcinst" [
      "TYPE"  , deftype;
      "MODULE", (mk_str "moduleinst" []); (* dummy module *)
      "CODE"  , funccode
    ] in

  let create_globalinst t v =
    let valtype = mk_nullary' "valtype" t in
    let globaltype = mk_case' "globaltype" [[];[]] [ 
      mk_none (t_var "mut");
      valtype
    ] in
    mk_str "globalinst" [ ("TYPE", globaltype); ("VALUE" , v ) ]
  in

  let create_tableinst t =
    let addrtype = mk_nullary' "addrtype" t in
    let limits   = mk_case' "limits" [["["];[".."];["]"]] [
      mk_nat 10; mk_nat 20
    ] in
    let reftype  = mk_case' "reftype" [["REF"];[];[]] [
      mk_some (t_var "nul") (mk_nullary' "" "NULL");
      mk_nullary' "heaptype" "FUNC"
    ] in
    let tabletype = mk_case' "tabletype" [[];[];[];[]] [
      addrtype; limits; reftype
    ] in
    let func = mk_nullary' "heaptype" "FUNC" in
    let nulls = listE (t_star "ref") (List.init 10 (Fun.const (mk_case' "ref" [["REF.NULL"];[]] [func]))) in
    mk_str "tableinst" [ ("TYPE", tabletype); ("REFS", nulls) ]
  in

  let create_meminst t =
    let addrtype = mk_nullary' "addrtype" t in
    let limits   = mk_case' "limits" [["["];[".."];["]"]] [
      mk_nat 1; mk_nat 2
    ] in
    let memtype = mk_case' "memtype" [[];[];["PAGE"]] [
      addrtype; limits
    ] in
    let zeros = listE (t_star "byte") (List.init 0x10000 (Fun.const (mk_nat 0))) in
    mk_str "meminst" [ ("TYPE", memtype); ("BYTES", zeros) ] in

  (* Builtin functions *)
  let funcs = [
    create_funcinst "print"         [            ];
    create_funcinst "print_i32"     ["I32"       ];
    (*
    create_funcinst "print_i64"     ["I64"       ];
    create_funcinst "print_f32"     ["F32"       ];
    create_funcinst "print_f64"     ["F64"       ];
    create_funcinst "print_i32_f32" ["I32"; "F32"];
    create_funcinst "print_f64_f64" ["F64"; "F64"]; *)
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
      match (Store.access kinds).it with
      | ListE a -> List.length a
      | _ -> assert false
    in
    let new_inst =
      mk_str "exportinst" [ ("NAME", textE name); ("ADDR", mk_case' "externaddr" [[kind];[]] [ mk_nat addr ]) ]
    in

    (* Update Store *)

    Store.update kinds (fun e -> match e.it with
    | ListE es -> ListE (es @ [inst]) $> e
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
    |> listE (t_star "exportinst")
  in

  let moduleinst = mk_str "moduleinst"
                          [ ("TYPES"  , listE (t_star "deftype") [])
                          ; ("TAGS"   , listE (t_star "tagaddr") [])
                          ; ("GLOBALS", listE (t_star "globaladdr") [])
                          ; ("MEMS"   , listE (t_star "memaddr") [])
                          ; ("TABLES" , listE (t_star "tableaddr") [])
                          ; ("FUNCS"  , listE (t_star "funcaddr") [])
                          ; ("ELEMS"  , listE (t_star "elemaddr") [])
                          ; ("DATAS"  , listE (t_star "dataaddr") [])
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

