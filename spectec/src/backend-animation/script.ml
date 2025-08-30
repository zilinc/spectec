(* The .wast stuff *)

open Il.Ast
open Util.Error
open Util.Source
open Il_util

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

(* Store *)

module Store = struct
  let _init_store : exp =
    mk_str "store" [ ("TAGS"   , listE (t_star "taginst"    ) [])
                   ; ("GLOBALS", listE (t_star "globalinst" ) [])
                   ; ("MEMS"   , listE (t_star "meminst"    ) [])
                   ; ("TABLES" , listE (t_star "tableinst"  ) [])
                   ; ("FUNCS"  , listE (t_star "funcinst"   ) [])
                   ; ("DATAS"  , listE (t_star "datainst"   ) [])
                   ; ("ELEMS"  , listE (t_star "eleminst"   ) [])
                   ; ("STRUCTS", listE (t_star "structinst" ) [])
                   ; ("ARRAYS" , listE (t_star "arrayinst"  ) [])
                   ; ("EXNS"   , listE (t_star "exninst"    ) [])
                   ]

  let _store : exp ref = ref _init_store

  let get_store () : exp = !_store
  let set_store s : unit = _store := s



end


(* Host *)

let il_of_spectest () : exp =
  todo "il_to_spectest"
(*
  (* TODO : Change this into host function instance, instead of current normal function instance *)
  let create_funcinst (name, type_tags) =
    let winstr_tag = String.uppercase_ascii name in
    let code = nullary winstr_tag in
    let ptype = Array.map nullary type_tags in
    let arrow = CaseV ("->", [ listV ptype; listV [||] ]) in
    let ftype = CaseV ("FUNC", [ listV ptype; listV [||] ]) in
    let dtype =
      CaseV ("_DEF", [
        CaseV ("REC", [
          [| CaseV ("SUB", [some "FINAL"; listV [||]; ftype]) |] |> listV
        ]); natV Z.zero
      ]) in
    let tidx = CaseV ("", [ natV Z.zero ]) in
    name, StrV [
      "TYPE", ref (if !Construct.version <= 2 then arrow else dtype);
      "MODULE", ref (StrV Record.empty); (* dummy module *)
      "CODE", ref (CaseV ("FUNC", [ tidx; listV [||]; listV [| code |] ]))
    ] in

  let create_globalinst t v = StrV [
    "TYPE", t |> ref;
    "VALUE", v |> ref
  ] in

  let create_tableinst t elems = StrV [
    "TYPE", t |> ref;
    "REFS", elems |> ref
  ] in

  let create_meminst t bytes_ = StrV [
    "TYPE", t |> ref;
    "BYTES", bytes_ |> ref
  ] in

  (* Builtin functions *)
  let funcs = List.rev [
    ("print", [||]) |> create_funcinst;
    ("print_i32", [| "I32" |]) |> create_funcinst;
    ("print_i64", [| "I64" |]) |> create_funcinst;
    ("print_f32", [| "F32" |]) |> create_funcinst;
    ("print_f64", [| "F64" |]) |> create_funcinst;
    ("print_i32_f32", [| "I32"; "F32" |]) |> create_funcinst;
    ("print_f64_f64", [| "F64"; "F64" |]) |> create_funcinst
  ] in
  (* Builtin globals *)
  let globals = List.rev [
    "global_i32", 666   |> I32.of_int_u |> i32_to_const |> create_globalinst (TupV [none "MUT"; nullary "I32"]);
    "global_i64", 666   |> I64.of_int_u |> i64_to_const |> create_globalinst (TupV [none "MUT"; nullary "I64"]);
    "global_f32", 666.6 |> F32.of_float |> f32_to_const |> create_globalinst (TupV [none "MUT"; nullary "F32"]);
    "global_f64", 666.6 |> F64.of_float |> f64_to_const |> create_globalinst (TupV [none "MUT"; nullary "F64"]);
  ] in
  (* Builtin tables *)
  let nulls = CaseV ("REF.NULL", [ nullary "FUNC" ]) |> Array.make 10 in
  let funcref =
    if !Construct.version <= 2 then
      nullary "FUNCREF"
    else
      CaseV ("REF", [some "NULL"; nullary "FUNC"])
  in
  let mk_ttype nt =
    let args = [ CaseV ("[", [ natV (Z.of_int 10); natV (Z.of_int 20) ]); funcref ] in
    if !Construct.version <= 2 then
      TupV args
    else
      TupV (CaseV (nt, []) :: args)
  in
  let tables = [
    "table",
    listV nulls |> create_tableinst (mk_ttype "I32");
    "table64",
    listV nulls |> create_tableinst (mk_ttype "I64");
  ] in
  (* Builtin memories *)
  let zeros = natV Z.zero |> Array.make 0x10000 in
  let mk_mtype nt =
    let arg = CaseV ("[", [ natV Z.one; natV (Z.of_int 2) ]) in
    if !Construct.version <= 2 then
      CaseV ("PAGE", [ arg ])
    else
      CaseV ("PAGE", [ CaseV (nt, []); arg ])
  in
  let memories = [
    "memory",
    listV zeros |> create_meminst (mk_mtype "I32");
    "memory64",
    listV zeros |> create_meminst (mk_mtype "I64");
  ] in
  let tags = [] in

  let append kind (name, inst) extern =

    let kinds = kind ^ "S" in

    (* Generate ExternFunc *)

    let addr =
      match Store.access kinds with
      | ListV a -> Array.length !a |> Z.of_int
      | _ -> assert false
    in
    let new_extern =
      StrV [ "NAME", ref (TextV name); "ADDR", ref (CaseV (kind, [ natV addr ])) ]
    in

    (* Update Store *)

    (match Store.access kinds with
    | ListV a -> a := Array.append !a [|inst|]
    | _ -> assert false);

    new_extern :: extern in

  (* extern -> new_extern *)
  let func_extern = List.fold_right (append "FUNC") funcs in
  let global_extern = List.fold_right (append "GLOBAL") globals in
  let table_extern = List.fold_right (append "TABLE") tables in
  let memory_extern = List.fold_right (append "MEM") memories in
  let tag_extern = List.fold_right (append "TAG") tags in

  let extern =
    []
    |> func_extern
    |> global_extern
    |> table_extern
    |> memory_extern
    |> tag_extern
    |> Array.of_list in

  let moduleinst = mk_str "moduleinst"
                          [ ("TYPES"  , listE (t_star "deftype") [])
                          ; ("TAGS"   , listE (t_star "tagaddr") [])
                          ; ("GLOBALS", listE (t_star "globaladdr") [])
                          ; ("MEMS"   , listE (t_star "memaddr") [])
                          ; ("TABLES" , listE (t_star "tableaddr") [])
                          ; ("FUNCS"  , listE (t_star "funcaddr") [])
                          ; ("ELEMS"  , listE (t_star "elemaddr") [])
                          ; ("DATAS"  , listE (t_star "dataaddr") [])
                          ; ("EXPORTS", extern)
                          ]
  in
  moduleinst, store
*)

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

