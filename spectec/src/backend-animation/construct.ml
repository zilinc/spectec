open Il.Ast
open Util
open Error
open Source
open Il_util
module RI = Reference_interpreter
module RT = RI.Types

let error at msg = Util.Error.error at "ani.../int.../construct" msg


(* Constant *)

let default_table_max = 4294967295L
let default_memory_max = 65536L

(* Currently support only version 3. *)
let version = ref 3



(* Construct minor *)

let il_of_z_nat z : exp = natE z
let il_of_z_int z : exp = intE z


(*
let al_of_fmagN layout i =
  let n = Z.logand i (mask_exp layout) in
  let m = Z.logand i (mask_mant layout) in
  if n = Z.zero then
    CaseV ("SUBNORM", [ al_of_z_nat m ])
  else if n <> mask_exp layout then
    CaseV ("NORM", [ al_of_z_nat m; al_of_z_int Z.(shift_right n layout.mantissa - bias layout) ])
  else if m = Z.zero then
    CaseV ("INF", [])
  else
    CaseV ("NAN", [ al_of_z_nat m ])

let al_of_floatN layout i =
  let i' = Z.logand i (mask_mag layout) in
  let mag = al_of_fmagN layout i in
  CaseV ((if i' = i then "POS" else "NEG"), [ mag ])

let vec128_to_z vec =
  match V128.I64x2.to_lanes vec with
  | [ v1; v2 ] -> Z.(of_int64_unsigned v1 + e64 * of_int64_unsigned v2)
  | _ -> assert false
*)

let il_of_nat i = Z.of_int i |> il_of_z_nat
let il_of_nat8  i8  = Z.of_int (RI.I8.to_int_u  i8 ) |> il_of_z_nat
let il_of_nat16 i16 = Z.of_int (RI.I16.to_int_u i16) |> il_of_z_nat
let il_of_nat32 i32 = Z.of_int32_unsigned i32 |> il_of_z_nat
let il_of_nat64 i64 = Z.of_int64_unsigned i64 |> il_of_z_nat

let il_of_idx (idx: RI.Ast.idx) = il_of_nat32 idx.it

let il_of_name name = textE (Utf8.encode name)
let il_of_byte byte = Char.code byte |> il_of_nat
let il_of_bytes bytes = String.to_seq bytes |> il_of_seq il_of_byte (t_star "byte")

(*
let al_of_float32 f32 = F32.to_bits f32 |> Z.of_int32_unsigned |> al_of_floatN layout32
let al_of_float64 f64 = F64.to_bits f64 |> Z.of_int64_unsigned |> al_of_floatN layout64
let al_of_vec128 vec = vec128_to_z vec |> al_of_z_nat
let al_of_bool b = Stdlib.Bool.to_int b |> al_of_nat
let al_of_memidx idx = if !version <= 2 then [] else [al_of_idx idx]
*)


(* Construct instruction *)

(*
let al_of_catch catch =
  match catch.it with
  | Catch (idx1, idx2) -> CaseV ("CATCH", [ al_of_idx idx1; al_of_idx idx2 ])
  | CatchRef (idx1, idx2) -> CaseV ("CATCH_REF", [ al_of_idx idx1; al_of_idx idx2 ])
  | CatchAll idx -> CaseV ("CATCH_ALL", [ al_of_idx idx ])
  | CatchAllRef idx -> CaseV ("CATCH_ALL_REF", [ al_of_idx idx ])
*)

let il_of_instr (instr: RI.Ast.instr) = Error.todo "il_of_instr"
(*
  match instr.it with
  (* wasm values *)
  | Const num -> il_of_num num.it
  | VecConst vec -> il_of_vec vec.it
  | RefNull ht -> CaseV ("REF.NULL", [ al_of_heaptype ht ])
  (* wasm instructions *)
  | Unreachable -> mk_nullary "UNREACHABLE"
  | Nop -> nullary "NOP"
  | Drop -> nullary "DROP"
  | Unary op -> CaseV ("UNOP", al_of_unop op)
  | Binary op -> CaseV ("BINOP", al_of_binop op)
  | Test op -> CaseV ("TESTOP", al_of_testop op)
  | Compare op -> CaseV ("RELOP", al_of_relop op)
  | Convert op -> CaseV ("CVTOP", al_of_cvtop op)
  | VecTest vop -> CaseV ("VTESTOP", al_of_vtestop vop)
  | VecCompare vop -> CaseV ("VRELOP", al_of_vrelop vop)
  | VecUnary vop -> CaseV ("VUNOP", al_of_vunop vop)
  | VecBinary vop -> (match al_of_vbinop_opt vop with Some l -> CaseV ("VBINOP", l) | None -> al_of_special_vbinop vop)
  | VecTernary vop -> (match al_of_vternop_opt vop with Some l -> CaseV ("VTERNOP", l) | None -> al_of_special_vternop vop)
  | VecConvert vop -> (match al_of_vcvtop_opt vop with Some l -> CaseV ("VCVTOP", l) | None -> al_of_special_vcvtop vop)
  | VecShift vop -> CaseV ("VSHIFTOP", al_of_vshiftop vop)
  | VecBitmask vop -> CaseV ("VBITMASK", al_of_vbitmaskop vop)
  | VecTestBits vop -> CaseV ("VVTESTOP", al_of_vvtestop vop)
  | VecUnaryBits vop -> CaseV ("VVUNOP", al_of_vvunop vop)
  | VecBinaryBits vop -> CaseV ("VVBINOP", al_of_vvbinop vop)
  | VecTernaryBits vop -> CaseV ("VVTERNOP", al_of_vvternop vop)
  | VecSplat vop -> CaseV ("VSPLAT", al_of_vsplatop vop)
  | VecExtract vop -> CaseV ("VEXTRACT_LANE", al_of_vextractop vop)
  | VecReplace vop -> CaseV ("VREPLACE_LANE", al_of_vreplaceop vop)
  | RefIsNull -> nullary "REF.IS_NULL"
  | RefFunc idx -> CaseV ("REF.FUNC", [ al_of_idx idx ])
  | Select vtl_opt when !version = 1 -> assert (vtl_opt = None); nullary "SELECT"
  | Select vtl_opt -> CaseV ("SELECT", [ al_of_opt (al_of_list al_of_valtype) vtl_opt ])
  | LocalGet idx -> CaseV ("LOCAL.GET", [ al_of_idx idx ])
  | LocalSet idx -> CaseV ("LOCAL.SET", [ al_of_idx idx ])
  | LocalTee idx -> CaseV ("LOCAL.TEE", [ al_of_idx idx ])
  | GlobalGet idx -> CaseV ("GLOBAL.GET", [ al_of_idx idx ])
  | GlobalSet idx -> CaseV ("GLOBAL.SET", [ al_of_idx idx ])
  | TableGet idx -> CaseV ("TABLE.GET", [ al_of_idx idx ])
  | TableSet idx -> CaseV ("TABLE.SET", [ al_of_idx idx ])
  | TableSize idx -> CaseV ("TABLE.SIZE", [ al_of_idx idx ])
  | TableGrow idx -> CaseV ("TABLE.GROW", [ al_of_idx idx ])
  | TableFill idx -> CaseV ("TABLE.FILL", [ al_of_idx idx ])
  | TableCopy (idx1, idx2) -> CaseV ("TABLE.COPY", [ al_of_idx idx1; al_of_idx idx2 ])
  | TableInit (idx1, idx2) -> CaseV ("TABLE.INIT", [ al_of_idx idx1; al_of_idx idx2 ])
  | ElemDrop idx -> CaseV ("ELEM.DROP", [ al_of_idx idx ])
  | Block (bt, instrs) ->
    CaseV ("BLOCK", [ al_of_blocktype bt; al_of_list al_of_instr instrs ])
  | Loop (bt, instrs) ->
    CaseV ("LOOP", [ al_of_blocktype bt; al_of_list al_of_instr instrs ])
  | If (bt, instrs1, instrs2) ->
    CaseV ("IF", [
      al_of_blocktype bt;
      al_of_list al_of_instr instrs1;
      al_of_list al_of_instr instrs2;
    ])
  | Br idx -> CaseV ("BR", [ al_of_idx idx ])
  | BrIf idx -> CaseV ("BR_IF", [ al_of_idx idx ])
  | BrTable (idxs, idx) ->
    CaseV ("BR_TABLE", [ al_of_list al_of_idx idxs; al_of_idx idx ])
  | BrOnNull idx -> CaseV ("BR_ON_NULL", [ al_of_idx idx ])
  | BrOnNonNull idx -> CaseV ("BR_ON_NON_NULL", [ al_of_idx idx ])
  | BrOnCast (idx, rt1, rt2) ->
    CaseV ("BR_ON_CAST", [ al_of_idx idx; al_of_reftype rt1; al_of_reftype rt2 ])
  | BrOnCastFail (idx, rt1, rt2) ->
    CaseV ("BR_ON_CAST_FAIL", [ al_of_idx idx; al_of_reftype rt1; al_of_reftype rt2 ])
  | Return -> nullary "RETURN"
  | Call idx -> CaseV ("CALL", [ al_of_idx idx ])
  | CallRef idx -> CaseV ("CALL_REF", [ optV (Some (al_of_typeuse_of_idx idx)) ])
  | CallIndirect (idx1, idx2) ->
    let args = (if !version = 1 then [] else [ al_of_idx idx1 ]) @ [ al_of_typeuse_of_idx idx2 ] in
    CaseV ("CALL_INDIRECT", args)
  | ReturnCall idx -> CaseV ("RETURN_CALL", [ al_of_idx idx ])
  | ReturnCallRef idx -> CaseV ("RETURN_CALL_REF", [ optV (Some (al_of_idx idx)) ])
  | ReturnCallIndirect (idx1, idx2) ->
    CaseV ("RETURN_CALL_INDIRECT", [ al_of_idx idx1; al_of_typeuse_of_idx idx2 ])
  | Throw idx -> CaseV ("THROW", [ al_of_idx idx ])
  | ThrowRef -> nullary "THROW_REF"
  | TryTable (bt, catches, instrs) ->
    CaseV ("TRY_TABLE", [
      al_of_blocktype bt;
      al_of_list al_of_catch catches;
      al_of_list al_of_instr instrs
    ])
  | Load (idx, loadop) -> CaseV ("LOAD", al_of_loadop idx loadop)
  | Store (idx, storeop) -> CaseV ("STORE", al_of_storeop idx storeop)
  | VecLoad (idx, vloadop) -> CaseV ("VLOAD", al_of_vloadop idx vloadop)
  | VecLoadLane (idx, vlaneop, i) -> CaseV ("VLOAD_LANE", al_of_vlaneop idx vlaneop i)
  | VecStore (idx, vstoreop) -> CaseV ("VSTORE", al_of_vstoreop idx vstoreop)
  | VecStoreLane (idx, vlaneop, i) -> CaseV ("VSTORE_LANE", al_of_vlaneop idx vlaneop i)
  | MemorySize idx -> CaseV ("MEMORY.SIZE", al_of_memidx idx)
  | MemoryGrow idx -> CaseV ("MEMORY.GROW", al_of_memidx idx)
  | MemoryFill idx -> CaseV ("MEMORY.FILL", al_of_memidx idx)
  | MemoryCopy (idx1, idx2) -> CaseV ("MEMORY.COPY", al_of_memidx idx1 @ al_of_memidx idx2)
  | MemoryInit (idx1, idx2) -> CaseV ("MEMORY.INIT", al_of_memidx idx1 @ [ al_of_idx idx2 ])
  | DataDrop idx -> CaseV ("DATA.DROP", [ al_of_idx idx ])
  | RefAsNonNull -> nullary "REF.AS_NON_NULL"
  | RefTest rt -> CaseV ("REF.TEST", [ al_of_reftype rt ])
  | RefCast rt -> CaseV ("REF.CAST", [ al_of_reftype rt ])
  | RefEq -> nullary "REF.EQ"
  | RefI31 -> nullary "REF.I31"
  | I31Get sx -> CaseV ("I31.GET", [ al_of_sx sx ])
  | StructNew (idx, Explicit) -> CaseV ("STRUCT.NEW", [ al_of_idx idx ])
  | StructNew (idx, Implicit) -> CaseV ("STRUCT.NEW_DEFAULT", [ al_of_idx idx ])
  | StructGet (idx1, idx2, sx_opt) ->
    CaseV ("STRUCT.GET", [
      al_of_opt al_of_sx sx_opt;
      al_of_idx idx1;
      al_of_nat32 idx2;
    ])
  | StructSet (idx1, idx2) -> CaseV ("STRUCT.SET", [ al_of_idx idx1; al_of_nat32 idx2 ])
  | ArrayNew (idx, Explicit) -> CaseV ("ARRAY.NEW", [ al_of_idx idx ])
  | ArrayNew (idx, Implicit) -> CaseV ("ARRAY.NEW_DEFAULT", [ al_of_idx idx ])
  | ArrayNewFixed (idx, i32) ->
    CaseV ("ARRAY.NEW_FIXED", [ al_of_idx idx; al_of_nat32 i32 ])
  | ArrayNewElem (idx1, idx2) ->
    CaseV ("ARRAY.NEW_ELEM", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayNewData (idx1, idx2) ->
    CaseV ("ARRAY.NEW_DATA", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayGet (idx, sx_opt) ->
    CaseV ("ARRAY.GET", [ al_of_opt al_of_sx sx_opt; al_of_idx idx ])
  | ArraySet idx -> CaseV ("ARRAY.SET", [ al_of_idx idx ])
  | ArrayLen -> nullary "ARRAY.LEN"
  | ArrayCopy (idx1, idx2) -> CaseV ("ARRAY.COPY", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayFill idx -> CaseV ("ARRAY.FILL", [ al_of_idx idx ])
  | ArrayInitData (idx1, idx2) ->
    CaseV ("ARRAY.INIT_DATA", [ al_of_idx idx1; al_of_idx idx2 ])
  | ArrayInitElem (idx1, idx2) ->
    CaseV ("ARRAY.INIT_ELEM", [ al_of_idx idx1; al_of_idx idx2 ])
  | ExternConvert Internalize -> nullary "ANY.CONVERT_EXTERN"
  | ExternConvert Externalize -> nullary "EXTERN.CONVERT_ANY"
  (* | _ -> CaseV ("TODO: Unconstructed Wasm instruction (al_of_instr)", []) *)
*)

let il_of_const (const: RI.Ast.const) = il_of_list (t_star "instr") il_of_instr const.it

(* Construct module *)


let rec il_of_null = function
  | RT.NoNull -> mk_none (varT "nul")
  | RT.Null   -> mk_some (varT "nul") (mk_nullary "nul" "NULL")

and il_of_final = function
  | RT.NoFinal -> mk_none (varT "fin")
  | RT.Final   -> mk_some (varT "fin") (mk_nullary "fin" "FINAL")

and il_of_mut = function
  | RT.Cons -> mk_none (varT "mut")
  | RT.Var  -> mk_some (varT "mut") (mk_nullary "mut" "MUT")

and il_of_packtype = function
  | RT.I8T  -> mk_nullary "storagetype" "I8"
  | RT.I16T -> mk_nullary "storagetype" "I16"

and il_of_storagetype = function
  | RT.ValStorageT  vt -> il_of_valtype  vt
  | RT.PackStorageT pt -> il_of_packtype pt

and il_of_fieldtype = function
  | RT.FieldT (mut, st) -> mk_case "fieldtype" [[];[];[]] [ il_of_mut mut; il_of_storagetype st ]

and il_of_resulttype rt = il_of_list (t_star "valtype") il_of_valtype rt

and il_of_comptype = function
  | RT.StructT ftl      -> mk_case "comptype" [["STRUCT"];[]]      [ il_of_list (t_list "fieldtype") il_of_fieldtype ftl ]
  | RT.ArrayT  ft       -> mk_case "comptype" [["ARRAY"];[]]       [ il_of_fieldtype ft ]
  | RT.FuncT (rt1, rt2) -> mk_case "comptype" [["FUNC"];["->"];[]] [ il_of_resulttype rt1; il_of_resulttype rt2 ]

and il_of_subtype = function
  | RT.SubT (fin, tul, st) ->
    mk_case "subtype" [["SUB"];[];[];[]] [ il_of_final fin; il_of_list (t_star "typeuse") il_of_typeuse tul; il_of_comptype st ]

and il_of_rectype = function
  | RT.RecT stl -> mk_case "rectype" [["REC"];[]] [ il_of_list (t_list "subtype") il_of_subtype stl ]

and il_of_deftype = function
  | RT.DefT (rt, i) -> mk_case "deftype" [["_DEF"];[];[]] [il_of_rectype rt; il_of_nat32 i]

and il_of_typeuse = function
  | RT.Idx idx -> mk_case "typeuse" [["_IDX"];[]] [ il_of_nat32 idx ]
  | RT.Rec n   -> mk_case "typeuse" [["REC" ];[]] [ il_of_nat32 n ]
  | RT.Def dt  -> il_of_deftype dt

and il_of_heaptype = function
  | RT.UseHT tu -> il_of_typeuse tu
  | RT.BotHT    -> mk_nullary "absheaptype" "BOT"
  | ht -> RT.string_of_heaptype ht |> mk_nullary "absheaptype"

and il_of_reftype (null, ht) =
  mk_case "reftype" [["REF"];[];[]] [ il_of_null null; il_of_heaptype ht ]

and il_of_addrtype at = RT.string_of_addrtype at |> mk_nullary "addrtype"

and il_of_numtype nt = RT.string_of_numtype nt |> mk_nullary "numtype"

and il_of_vectype vt = RT.string_of_vectype vt |> mk_nullary "vectype"

and il_of_valtype = function
  | RT.RefT rt -> il_of_reftype rt
  | RT.NumT nt -> il_of_numtype nt
  | RT.VecT vt -> il_of_vectype vt
  | RT.BotT    -> mk_nullary "valtype" "BOT"

let il_of_blocktype = function
  | RI.Ast.VarBlockType idx    -> mk_case "blocktype" [["_IDX"   ];[]] [ il_of_idx idx ]
  | RI.Ast.ValBlockType vt_opt -> mk_case "blocktype" [["_RESULT"];[]] [ il_of_opt (t_opt "valtype") il_of_valtype vt_opt ]

let il_of_limits default (limits: RT.limits) =
  let max =
    match limits.max with
    | Some v -> il_of_nat64 v
    | None   -> il_of_nat64 default
  in
  mk_case "limits" [["["];[".."];["]"]] [ il_of_nat64 limits.min; max ]

let il_of_tagtype = function
  | RT.TagT tu -> il_of_typeuse tu

let il_of_globaltype = function
  | RT.GlobalT (mut, vt) -> mk_case "globaltype" [[];[];[]] [ il_of_mut mut; il_of_valtype vt ]

let il_of_tabletype = function
  | RT.TableT (at, limits, rt) ->
    mk_case "tabletype" [[];[];[];[]] [ il_of_addrtype at; il_of_limits default_table_max limits; il_of_reftype rt ]

let il_of_memorytype = function
  | RT.MemoryT (at, limits) ->
    mk_case "memtype" [[];[];["PAGE"]] [ il_of_addrtype at; il_of_limits default_memory_max limits ]



(* Construct value *)

(*
let al_of_num = function
  | I32 i32 -> CaseV ("CONST", [ nullary "I32"; al_of_nat32 i32 ])
  | I64 i64 -> CaseV ("CONST", [ nullary "I64"; al_of_nat64 i64 ])
  | F32 f32 -> CaseV ("CONST", [ nullary "F32"; al_of_float32 f32 ])
  | F64 f64 -> CaseV ("CONST", [ nullary "F64"; al_of_float64 f64 ])

let al_of_vec = function
  | V128 v128 -> CaseV ("VCONST", [ nullary "V128"; al_of_vec128 v128 ])

let al_of_vec_shape shape (lanes: int64 list) =
  al_of_vec (V128  (
    match shape with
    | V128.I8x16() -> V128.I8x16.of_lanes (List.map I8.of_int_s (List.map Int64.to_int lanes))
    | V128.I16x8() -> V128.I16x8.of_lanes (List.map I16.of_int_s (List.map Int64.to_int lanes))
    | V128.I32x4() -> V128.I32x4.of_lanes (List.map Int64.to_int32 lanes)
    | V128.I64x2() -> V128.I64x2.of_lanes lanes
    | V128.F32x4() -> V128.F32x4.of_lanes (List.map (fun i -> i |> Int64.to_int32 |> F32.of_bits) lanes)
    | V128.F64x2() -> V128.F64x2.of_lanes (List.map F64.of_bits lanes)
  ))

let rec al_of_ref = function
  | NullRef ht -> CaseV ("REF.NULL", [ al_of_heaptype ht ])
  (*
  | I31.I31Ref i ->
    CaseV ("REF.I31_NUM", [ NumV (Int64.of_int i) ])
  | Aggr.StructRef a ->
    CaseV ("REF.STRUCT_ADDR", [ NumV (int64_of_int32_u a) ])
  | Aggr.ArrayRef a ->
    CaseV ("REF.ARRAY_ADDR", [ NumV (int64_of_int32_u a) ])
  | Instance.FuncRef a ->
    CaseV ("REF.FUNC_ADDR", [ NumV (int64_of_int32_u a) ])
  *)
  | Script.HostRef i32 -> CaseV ("REF.HOST_ADDR", [ al_of_nat32 i32 ])
  | Extern.ExternRef r -> CaseV ("REF.EXTERN", [ al_of_ref r ])
  | r -> string_of_ref r |> error "al_of_ref"
*)

let il_of_num n = todo "il_of_value"
let il_of_vec v = todo "il_of_value"
let il_of_ref r = todo "il_of_value"

let il_of_value (v: RI.Value.value) = match v with
  | Num n -> il_of_num n
  | Vec v -> il_of_vec v
  | Ref r -> il_of_ref r


let il_of_type (ty: RI.Ast.type_) =
  mk_case "type" [["TYPE"];[]] [ il_of_rectype ty.it ]

let il_of_local (local: RI.Ast.local) =
  let Local t = local.it in
  mk_case "local" [["LOCAL"];[]] [ il_of_valtype t ]

let il_of_func (func: RI.Ast.func) =
  let Func (idx, locals, body) = func.it in
  mk_case "func" [["FUNC"];[];[];[]] [
    il_of_idx idx;
    il_of_list (t_star "local") il_of_local locals;
    il_of_list (varT "expr") il_of_instr body;
  ]

let il_of_global (global: RI.Ast.global) =
  let Global (gt, expr) = global.it in
  mk_case "global" [["GLOBAL"];[];[]] [ il_of_globaltype gt; il_of_const expr ]

let il_of_table (table: RI.Ast.table) =
  let Table (tt, expr) = table.it in
  mk_case "table" [["TABLE"];[];[]] [ il_of_tabletype tt; il_of_const expr ]

let il_of_memory (memory: RI.Ast.memory) =
  let Memory mt = memory.it in
  mk_case "mem" [["MEMORY"];[]] [ il_of_memorytype mt ]

let il_of_tag (tag: RI.Ast.tag) =
  let Tag tt = tag.it in
  mk_case "tag" [["TAG"];[]] [ il_of_tagtype tt ]

let il_of_segmentmode (segmentmode: RI.Ast.segmentmode) =
  match segmentmode.it with
  | Passive -> mk_nullary "datamode" "PASSIVE"
  | Active (index, offset) ->
    mk_case "datamode" [["ACTIVE"];[];[]] [ il_of_idx index; il_of_const offset ]
  | Declarative -> error no "datamode: no Declarative constructor"

let il_of_elem (elem: RI.Ast.elem) =
  let Elem (rt, consts, mode) = elem.it in
  mk_case "elem" [["ELEM"];[];[];[]] [
    il_of_reftype rt;
    il_of_list (t_star "expr") il_of_const consts;
    il_of_segmentmode mode;
  ]

let il_of_data (data: RI.Ast.data) =
  let Data (bytes, mode) = data.it in
  mk_case "data" [["DATA"];[];[]] [ il_of_bytes bytes; il_of_segmentmode mode ]

let il_of_externtype = function
  | RT.ExternFuncT   (typeuse   ) -> mk_case "externtype" [["FUNC"  ];[]] [il_of_typeuse    typeuse   ]
  | RT.ExternGlobalT (globaltype) -> mk_case "externtype" [["GLOBAL"];[]] [il_of_globaltype globaltype]
  | RT.ExternTableT  (tabletype ) -> mk_case "externtype" [["TABLE" ];[]] [il_of_tabletype  tabletype ]
  | RT.ExternMemoryT (memtype   ) -> mk_case "externtype" [["MEM"   ];[]] [il_of_memorytype memtype   ]
  | RT.ExternTagT    (tagtype   ) -> mk_case "externtype" [["TAG"   ];[]] [il_of_tagtype    tagtype   ]

let il_of_import (import: RI.Ast.import)=
  let Import (module_name, item_name, xt) = import.it in
  mk_case "import" [["IMPORT"];[];[];[]] [ il_of_name module_name; il_of_name item_name; il_of_externtype xt ]

let il_of_externidx (xt: RI.Ast.externidx) = match xt.it with
  | FuncX   idx -> mk_case "externidx" [["FUNC"  ];[]] [ il_of_idx idx ]
  | TableX  idx -> mk_case "externidx" [["TABLE" ];[]] [ il_of_idx idx ]
  | MemoryX idx -> mk_case "externidx" [["MEM"   ];[]] [ il_of_idx idx ]
  | GlobalX idx -> mk_case "externidx" [["GLOBAL"];[]] [ il_of_idx idx ]
  | TagX    idx -> mk_case "externidx" [["TAG"   ];[]] [ il_of_idx idx ]

let il_of_start (start: RI.Ast.start) =
  let Start idx = start.it in
  mk_case "start" [["START"];[]] [ il_of_idx idx ]

let il_of_export (export: RI.Ast.export) =
  let Export (name, exix) = export.it in
  mk_case "export" [["EXPORT"];[];[]] [ il_of_name name; il_of_externidx exix ]


(* Wasm-3: MODULE type* import* tag* global* mem* table* func* data* elem* start? export* *)
let il_of_module (module_: RI.Ast.module_) =
  let es = [
            il_of_list (t_star "type"  ) il_of_type module_.it.types;
            il_of_list (t_star "import") il_of_import module_.it.imports;
            il_of_list (t_star "tag"   ) il_of_tag module_.it.tags;
            il_of_list (t_star "global") il_of_global module_.it.globals;
            il_of_list (t_star "mem"   ) il_of_memory module_.it.memories;
            il_of_list (t_star "table" ) il_of_table module_.it.tables;
            il_of_list (t_star "func"  ) il_of_func module_.it.funcs;
            il_of_list (t_star "data"  ) il_of_data module_.it.datas;
            il_of_list (t_star "elem"  ) il_of_elem module_.it.elems;
            il_of_opt  (t_opt  "start" ) il_of_start module_.it.start;
            il_of_list (t_star "export") il_of_export module_.it.exports;
          ]
  in
  mk_case "module" [["MODULE"];[];[];[];[];[];[];[];[];[];[];[]] es

