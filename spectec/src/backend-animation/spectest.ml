open Il.Ast
open Util
open Util.Source
open Il_util
open State
module RI = Reference_interpreter


let error at msg = Error.error at "animation/script" msg

(* Host *)

let il_of_spectest () : exp =

  (* Helper functions *)
  let i32_to_const i = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "I32"; Construct.il_of_uN_32   i ] in
  let i64_to_const i = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "I64"; Construct.il_of_uN_64   i ] in
  let f32_to_const f = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "F32"; Construct.il_of_float32 f ] in
  let f64_to_const f = mk_case' "instr" [["CONST"];[]] [ mk_nullary' "numtype" "F64"; Construct.il_of_float64 f ] in


  let create_funcinst name ptypes =
    let code = mk_nullary' "instr" (String.uppercase_ascii name) in  (* instr *)
    let param_types = List.map (mk_nullary' "numtype") ptypes  (* list(valtype) *) in
    let comptype = mk_case' "comptype" [["FUNC"];["->"];[]] [
      Construct.il_of_list' (t_var "resulttype") param_types;
      Construct.il_of_list' (t_var "resulttype") []
    ] in
    let subtype = mk_case' "subtype" [["SUB"];[];[];[]] [
      optE (t_var "fin") (Some (mk_nullary' "" "FINAL"));
      listE (t_star "typeuse") [];
      comptype
    ] in
    let rectype = mk_case' "rectype" [["REC"];[]] [
      Construct.il_of_list' (t_app "list" [typA (t_var "subtype")]) [subtype]
    ] in
    let deftype = mk_case' "deftype" [["_DEF"];[];[]] [
      rectype; mk_nat 0
    ] in
    let funccode = mk_case' "funccode" [["_HOSTFUNC"];[]] [
      textE name
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
    let zeros = listE (t_star "byte") (List.init 0x10 (Fun.const (mk_nat 0))) in  (* 0x10000 *)
    mk_str "meminst" [ ("TYPE", memtype); ("BYTES", zeros) ] in

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

