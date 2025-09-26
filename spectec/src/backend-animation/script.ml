open Il.Ast
open Util.Error
open Util.Source
open Il_util
module Ds = Backend_interpreter.Ds
module RI = Reference_interpreter

(* Register, Modules *)

module Register = Ds.Register(struct type t = exp end)
module Modules  = Ds.Modules

(* Record *)

module Record   = Util.Record


(* Store *)

module Store = struct
  type t = exp

  let store = ref Record.empty

  let init () =
    store := Record.empty
      |> Record.add "TAGS"    (listE (t_star "taginst"    ) [])
      |> Record.add "GLOBALS" (listE (t_star "globalinst" ) [])
      |> Record.add "MEMS"    (listE (t_star "meminst"    ) [])
      |> Record.add "TABLES"  (listE (t_star "tableinst"  ) [])
      |> Record.add "FUNCS"   (listE (t_star "funcinst"   ) [])
      |> Record.add "DATAS"   (listE (t_star "datainst"   ) [])
      |> Record.add "ELEMS"   (listE (t_star "eleminst"   ) [])
      |> Record.add "STRUCTS" (listE (t_star "structinst" ) [])
      |> Record.add "ARRAYS"  (listE (t_star "arrayinst"  ) [])
      |> Record.add "EXNS"    (listE (t_star "exninst"    ) [])
    ;
    Ds.Store.init ()


  let get () = mk_str "store" (List.map (fun (f, er) -> (f, !er)) !store)

  let access field = Record.find field !store
  let update field f = let v = access field in
                       store := Record.add field (f v) !store

  let put s =
    let tags    = find_str_field "TAGS"    s in
    let globals = find_str_field "GLOBALS" s in
    let mems    = find_str_field "MEMS"    s in
    let tables  = find_str_field "TABLES"  s in
    let funcs   = find_str_field "FUNCS"   s in
    let datas   = find_str_field "DATAS"   s in
    let elems   = find_str_field "ELEMS"   s in
    let structs = find_str_field "STRUCTS" s in
    let arrays  = find_str_field "ARRAYS"  s in
    let exns    = find_str_field "EXNS"    s in
    update "TAGS"    (Fun.const tags   );
    update "GLOBALS" (Fun.const globals);
    update "MEMS"    (Fun.const mems   );
    update "TABLES"  (Fun.const tables );
    update "FUNCS"   (Fun.const funcs  );
    update "DATAS"   (Fun.const datas  );
    update "ELEMS"   (Fun.const elems  );
    update "STRUCTS" (Fun.const structs);
    update "ARRAYS"  (Fun.const arrays );
    update "EXNS"    (Fun.const exns   );

    (* Update Ds.Store as well, because AL -> Value relies on it. Yikes! *)
    let als_tags    = Il_util.elts_of_list tags    |> List.map Construct.exp_to_val in
    let als_globals = Il_util.elts_of_list globals |> List.map Construct.exp_to_val in
    let als_mems    = Il_util.elts_of_list mems    |> List.map Construct.exp_to_val in
    let als_tables  = Il_util.elts_of_list tables  |> List.map Construct.exp_to_val in
    let als_funcs   = Il_util.elts_of_list funcs   |> List.map Construct.exp_to_val in
    let als_datas   = Il_util.elts_of_list datas   |> List.map Construct.exp_to_val in
    let als_elems   = Il_util.elts_of_list elems   |> List.map Construct.exp_to_val in
    let als_structs = Il_util.elts_of_list structs |> List.map Construct.exp_to_val in
    let als_arrays  = Il_util.elts_of_list arrays  |> List.map Construct.exp_to_val in
    let als_exns    = Il_util.elts_of_list exns    |> List.map Construct.exp_to_val in

    (match Ds.Store.access "TAGS" with
    | ListV a -> a := Array.of_list als_tags
    | _ -> assert false);
    (match Ds.Store.access "GLOBALS" with
    | ListV a -> a := Array.of_list als_globals
    | _ -> assert false);
    (match Ds.Store.access "MEMS" with
    | ListV a -> a := Array.of_list als_mems
    | _ -> assert false);
    (match Ds.Store.access "TABLES" with
    | ListV a -> a := Array.of_list als_tables
    | _ -> assert false);
    (match Ds.Store.access "FUNCS" with
    | ListV a -> a := Array.of_list als_funcs
    | _ -> assert false);
    (match Ds.Store.access "DATAS" with
    | ListV a -> a := Array.of_list als_datas
    | _ -> assert false);
    (match Ds.Store.access "ELEMS" with
    | ListV a -> a := Array.of_list als_elems
    | _ -> assert false);
    (match Ds.Store.access "STRUCTS" with
    | ListV a -> a := Array.of_list als_structs
    | _ -> assert false);
    (match Ds.Store.access "ARRAYS" with
    | ListV a -> a := Array.of_list als_arrays
    | _ -> assert false);
    (match Ds.Store.access "EXNS" with
    | ListV a -> a := Array.of_list als_exns
    | _ -> assert false);

end


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

