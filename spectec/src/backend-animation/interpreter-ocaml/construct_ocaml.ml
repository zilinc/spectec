module RI = Reference_interpreter
module RT = RI.Types
module DL = Dl_codegen_types

(* TEMPORARY only for debugging *)
let string_of_dlinstr = function
  | DL.NOP_instr -> "NOP_instr"
  | DL.UNREACHABLE_instr -> "UNREACHABLE_instr"
  | DL.DROP_instr -> "DROP_instr"
  | DL.SELECT_instr _ -> "SELECT_instr"
  | DL.CALL_instr _ -> "CALL_instr"
  | DL.CALL_REF_instr _ -> "CALL_REF_instr"
  | DL.RETURN_instr -> "RETURN_instr"
  | DL.RETURN_CALL_REF_instr _ -> "RETURN_CALL_REF_instr"
  | DL.THROW_REF_instr -> "THROW_REF_instr"
  | DL.CONST_instr _ -> "CONST_instr"
  | DL.BINOP_instr _ -> "BINOP_instr"
  | DL.REF_dot_NULL_instr _ -> "REF_dot_NULL_instr"
  | DL.LOCAL_dot_GET_instr _ -> "LOCAL_dot_GET_instr"
  | DL.TABLE_dot_INIT_instr _ -> "TABLE_dot_INIT_instr"
  | DL.ELEM_dot_DROP_instr _ -> "ELEM_dot_DROP_instr"
  | DL.MEMORY_dot_INIT_instr _ -> "MEMORY_dot_INIT_instr"
  | DL.DATA_dot_DROP_instr _ -> "DATA_dot_DROP_instr"
  | DL.REF_dot_I31_NUM_instr _ -> "REF_dot_I31_NUM_instr"
  | DL.REF_dot_STRUCT_ADDR_instr _ -> "REF_dot_STRUCT_ADDR_instr"
  | DL.REF_dot_ARRAY_ADDR_instr _ -> "REF_dot_ARRAY_ADDR_instr"
  | DL.REF_dot_FUNC_ADDR_instr _ -> "REF_dot_FUNC_ADDR_instr"
  | DL.REF_dot_EXN_ADDR_instr _ -> "REF_dot_EXN_ADDR_instr"
  | DL.REF_dot_HOST_ADDR_instr _ -> "REF_dot_HOST_ADDR_instr"
  | DL.REF_dot_EXTERN_instr _ -> "REF_dot_EXTERN_instr"
  | DL.TRAP_instr -> "TRAP_instr"
  | DL.BR_instr _ -> "BR_instr"
  | DL.LABEL__pct__lbrackcu_pct__rbrackcu_pct__instr _ -> "LABEL"
  | DL.FRAME__pct__lbrackcu_pct__rbrackcu_pct__instr _ -> "FRAME"

(* ======== *)

let ocaml_of_list f lst = DL.C_pct__list_ (List.map f lst)

let ocaml_of_codepoint (cp: RI.Utf8.codepoint) : DL.char = DL.C_pct__char cp
let ocaml_of_name (name : RI.Ast.name) : DL.name =
  DL.C_pct__name (List.map ocaml_of_codepoint name)

(* int32 translates to nat for now but probably should not *)
let ocaml_of_typeidx (n : RT.typeidx) : DL.typeidx = C_pct__uc_un (Int32.to_int n)

let ocaml_of_idx (n : RI.Ast.idx) : DL.idx = C_pct__uc_un (Int32.to_int n.it)
let ocaml_of_ast_typeidx (n : RI.Ast.typeidx) : DL.typeidx = ocaml_of_idx n
let ocaml_of_funcidx (n : RI.Ast.funcidx) : DL.funcidx = ocaml_of_idx n
let ocaml_of_tableidx (n : RI.Ast.tableidx) : DL.tableidx = ocaml_of_idx n
let ocaml_of_elemidx (n : RI.Ast.elemidx) : DL.elemidx = ocaml_of_idx n
let ocaml_of_dataidx (n : RI.Ast.dataidx) : DL.dataidx = ocaml_of_idx n
let ocaml_of_memoryidx (n : RI.Ast.memoryidx) : DL.memidx = ocaml_of_idx n
let ocaml_of_localidx (n : RI.Ast.localidx) : DL.localidx = ocaml_of_idx n
let ocaml_of_tagidx (n : RI.Ast.tagidx) : DL.tagidx = ocaml_of_idx n
let ocaml_of_globalidx (n : RI.Ast.globalidx) : DL.globalidx = ocaml_of_idx n

let ocaml_of_labelidx (n : RI.Ast.labelidx) : DL.labelidx = ocaml_of_idx n

let ocaml_typeuse_of_typeidx (n : DL.typeidx) = DL.C_IDX_typeuse n
let ocaml_of_int32 (n : int32) : DL.nat = Int32.to_int n
let ocaml_of_int64 (n : int64) : DL.uc_un = DL.C_pct__uc_un (Int64.to_int n)

let ocaml_unsigned_of_int (n : int) : DL.uc_un = DL.C_pct__uc_un n
let ocaml_unsigned_of_int64 (n : int64) : DL.uc_un = DL.C_pct__uc_un (Int64.to_int n)
let ocaml_of_mut mut = match mut with
  | RT.Cons -> None
  | RT.Var  -> Some DL.MUT_mut

let ocaml_of_null = function
  | RT.Null    -> Some DL.NULL_null
  | RT.NoNull -> None

let ocaml_of_numtype = function
  | RT.I32T -> DL.I32_numtype
  | RT.I64T -> DL.I64_numtype
  | RT.F32T -> DL.F32_numtype
  | RT.F64T -> DL.F64_numtype

let ocaml_of_numtype_storage = function
  | RT.I32T -> DL.I32_storagetype
  | RT.I64T -> DL.I64_storagetype
  | RT.F32T -> DL.F32_storagetype
  | RT.F64T -> DL.F64_storagetype

let ocaml_of_numtype_val = function
  | RT.I32T -> DL.I32_valtype
  | RT.I64T -> DL.I64_valtype
  | RT.F32T -> DL.F32_valtype
  | RT.F64T -> DL.F64_valtype

let ocaml_of_vectype _ = DL.V128_vectype
let ocaml_of_vectype_storage _ = DL.V128_storagetype

let ocaml_of_final = function
  | RT.NoFinal -> None
  | RT.Final   -> Some DL.FINAL_final

(* not used i think; remove *)
let ocaml_of_packtype s vt =
  if s = "storagetype" then match vt with
    | RT.I8T  -> DL.I8_storagetype
    | RT.I16T -> DL.I16_storagetype
  else failwith "ocaml_of_packtype: type not implemented"

let rec ocaml_of_valtype vt = match vt with
  | RT.RefT (null, ht) -> DL.REF_valtype (ocaml_of_null null, ocaml_of_heaptype ht)
  | RT.NumT nt -> ocaml_of_numtype_val nt
  | RT.VecT _  -> DL.V128_valtype
  | RT.BotT    -> DL.BOT_valtype

and ocaml_of_storagetype = function
  | RT.ValStorageT  vt -> begin match vt with
    | RT.NumT nt         -> ocaml_of_numtype_storage nt
    | RT.VecT _          -> DL.V128_storagetype
    | RT.RefT (null, ht) -> DL.REF_storagetype (ocaml_of_null null, ocaml_of_heaptype ht)
    | RT.BotT            -> DL.BOT_storagetype
    end
  | RT.PackStorageT pt -> begin match pt with
    | RT.I8T  -> DL.I8_storagetype
    | RT.I16T -> DL.I16_storagetype
    end

and ocaml_of_resulttype rt = ocaml_of_list ocaml_of_valtype rt

and ocaml_of_fieldtype = function
  | RT.FieldT (mut, st) -> DL.C_pct__pct__fieldtype (ocaml_of_mut mut, ocaml_of_storagetype st)

and ocaml_of_typeuse = function
  | RT.Idx idx -> DL.C_IDX_typeuse (ocaml_of_typeidx idx)
  | RT.Rec n   -> DL.REC_typeuse (ocaml_of_int32 n)
  | RT.Def (DefT (rt, n))  -> DL.C_DEF_typeuse (ocaml_of_rectype rt, ocaml_of_int32 n)

and ocaml_of_comptype = function
  | RT.StructT ftl      -> DL.STRUCT_comptype (ocaml_of_list ocaml_of_fieldtype ftl)
  | RT.ArrayT  ft       -> DL.ARRAY_comptype (ocaml_of_fieldtype ft)
  | RT.FuncT (rt1, rt2) -> DL.FUNC_pct__dash_right_pct__comptype (ocaml_of_resulttype rt1, ocaml_of_resulttype rt2)

and ocaml_of_subtype = function
  | RT.SubT (fin, tul, st) -> DL.SUB_subtype (ocaml_of_final fin, List.map ocaml_of_typeuse tul, ocaml_of_comptype st)

and ocaml_of_rectype = function
  | RT.RecT stl -> REC_rectype (ocaml_of_list ocaml_of_subtype stl)

and ocaml_of_heaptype = function
  | RT.AnyHT ->  DL.ANY_heaptype
  | RT.NoneHT -> DL.NONE_heaptype
  | RT.EqHT -> DL.EQ_heaptype
  | RT.I31HT -> DL.I31_heaptype
  | RT.StructHT -> DL.STRUCT_heaptype
  | RT.ArrayHT -> DL.ARRAY_heaptype
  | RT.FuncHT -> DL.FUNC_heaptype
  | RT.NoFuncHT -> DL.NOFUNC_heaptype
  | RT.ExnHT -> DL.EXN_heaptype
  | RT.NoExnHT -> DL.NOEXN_heaptype
  | RT.ExternHT -> DL.EXTERN_heaptype
  | RT.NoExternHT -> DL.NOEXTERN_heaptype
  | RT.UseHT tu -> begin match tu with
    | RT.Idx ti -> DL.C_IDX_heaptype (ocaml_of_typeidx ti)
    | RT.Rec n -> DL.REC_heaptype (ocaml_of_int32 n)
    | RT.Def (DefT (rt, n)) -> DL.C_DEF_heaptype (ocaml_of_rectype rt, ocaml_of_int32 n)
  end
  | RT.BotHT -> DL.BOT_heaptype

let ocaml_of_type (ty: RI.Ast.type_) =
  (*Printf.printf "Generating OCaml for type...\n";*)
  DL.TYPE_type_ (ocaml_of_rectype ty.it)

let ocaml_of_local (local: RI.Ast.local) =
  let RI.Ast.Local vt = local.it in
  DL.LOCAL_local (ocaml_of_valtype vt)

(* not sure if this is correct *)
let ocaml_of_packsize (packsize : RI.Pack.packsize) =
  match packsize with
  | RI.Pack.Pack8  -> DL.C_pct__sz 8
  | RI.Pack.Pack16 -> DL.C_pct__sz 16
  | RI.Pack.Pack32 -> DL.C_pct__sz 32
  | RI.Pack.Pack64 -> DL.C_pct__sz 64

let ocaml_of_sx (sx : RI.Pack.sx) =
  match sx with
  | RI.Pack.S -> DL.S_sx
  | RI.Pack.U -> DL.U_sx

let ocaml_of_loadop (loadop : RI.Ast.loadop) =
  match loadop.pack with
  | Some (packsize, sx) -> Some (DL.C_pct___pct__loadop_ (ocaml_of_packsize packsize, ocaml_of_sx sx))
  | None -> None

let ocaml_mem_of_loadop (loadop : RI.Ast.loadop) : DL.memarg =
  let align = loadop.align in
  let offset = loadop.offset in
  { uc_align_memarg = ocaml_unsigned_of_int align; uc_offset_memarg = ocaml_unsigned_of_int64 offset }

let ocaml_of_blocktype (bt : RI.Ast.blocktype) : DL.blocktype =
  match bt with
  | RI.Ast.VarBlockType typeidx -> DL.C_IDX_blocktype (ocaml_of_ast_typeidx typeidx)
  | ValBlockType vt_opt         -> DL.C_RESULT_blocktype (Option.map ocaml_of_valtype vt_opt)

let rec ocaml_of_instr (instr: RI.Ast.instr) =
  match instr.it with
  | RI.Ast.Unreachable       -> DL.UNREACHABLE_instr
  | RI.Ast.Nop               -> DL.NOP_instr
  | RI.Ast.Drop              -> DL.DROP_instr
  | RI.Ast.Select None       -> DL.SELECT_instr None
  | RI.Ast.Select (Some vt)  -> DL.SELECT_instr (Some (List.map ocaml_of_valtype vt))
  | RI.Ast.Block (blocktype, instrs)
                             -> DL.BLOCK_instr (ocaml_of_blocktype blocktype, List.map ocaml_of_instr instrs)
  | RI.Ast.Loop (blocktype, instrs)
                             -> DL.LOOP_instr (ocaml_of_blocktype blocktype, List.map ocaml_of_instr instrs)
  | RI.Ast.If (blocktype, instrs, instrs')
                             -> IF_pct__pct_ELSE_pct__instr (ocaml_of_blocktype blocktype, List.map ocaml_of_instr instrs, List.map ocaml_of_instr instrs')
  | RI.Ast.Br labelidx       -> DL.BR_instr (ocaml_of_labelidx labelidx)
  | RI.Ast.BrIf _            -> failwith "BrIf instruction not implemented yet"
  | RI.Ast.BrTable _         -> failwith "BrTable instruction not implemented yet"
  | RI.Ast.BrOnNull _        -> failwith "BrOnNull instruction not implemented yet"
  | RI.Ast.BrOnNonNull _     -> failwith "BrOnNonNull instruction not implemented yet"
  | RI.Ast.BrOnCast _        -> failwith "BrOnCast instruction not implemented yet"
  | RI.Ast.BrOnCastFail _    -> failwith "BrOnCastFail instruction not implemented yet"
  | RI.Ast.Return            -> DL.RETURN_instr
  | RI.Ast.Call funcidx      -> DL.CALL_instr (ocaml_of_funcidx funcidx)
  | RI.Ast.CallRef typeidx   -> DL.CALL_REF_instr (ocaml_typeuse_of_typeidx (ocaml_of_ast_typeidx typeidx))
  | RI.Ast.CallIndirect _    -> failwith "CallIndirect instruction not implemented yet"
  | RI.Ast.ReturnCall _      -> failwith "ReturnCall instruction not implemented yet"
  | RI.Ast.ReturnCallRef _   -> failwith "ReturnCallRef instruction not implemented yet"
  | RI.Ast.ReturnCallIndirect _
                             -> failwith "ReturnCallIndirect instruction not implemented yet"
  | RI.Ast.Throw _           -> failwith "Throw instruction not implemented yet"
  | RI.Ast.ThrowRef          -> failwith "ThrowRef instruction not implemented yet"
  | RI.Ast.TryTable _        -> failwith "TryTable instruction not implemented yet"
  | RI.Ast.LocalGet localidx -> DL.LOCAL_dot_GET_instr (ocaml_of_localidx localidx)
  | RI.Ast.LocalSet localidx -> DL.LOCAL_dot_SET_instr (ocaml_of_localidx localidx)
  | RI.Ast.LocalTee localidx -> DL.LOCAL_dot_TEE_instr (ocaml_of_localidx localidx)
  | RI.Ast.GlobalGet globalidx
                             -> DL.GLOBAL_dot_GET_instr (ocaml_of_globalidx globalidx)
  | RI.Ast.GlobalSet globalidx
                             -> DL.GLOBAL_dot_SET_instr (ocaml_of_globalidx globalidx)
  | RI.Ast.TableGet _        -> failwith "TableGet instruction not implemented yet"
  | RI.Ast.TableSet _        -> failwith "TableSet instruction not implemented yet"
  | RI.Ast.TableSize _       -> failwith "TableSize instruction not implemented yet"
  | RI.Ast.TableGrow _       -> failwith "TableGrow instruction not implemented yet"
  | RI.Ast.TableFill _       -> failwith "TableFill instruction not implemented yet"
  | RI.Ast.TableCopy _       -> failwith "TableCopy instruction not implemented yet"
  | RI.Ast.TableInit
    (tableidx, elemidx)      -> DL.TABLE_dot_INIT_instr (ocaml_of_tableidx tableidx, ocaml_of_elemidx elemidx)
  | RI.Ast.ElemDrop elemidx  -> DL.ELEM_dot_DROP_instr (ocaml_of_elemidx elemidx)
  | RI.Ast.Load (memidx, loadop)
                             -> DL.LOAD_instr (ocaml_of_numtype loadop.ty, ocaml_of_loadop loadop, ocaml_of_memoryidx memidx, ocaml_mem_of_loadop loadop)
  | RI.Ast.Store _           -> failwith "Store instruction not implemented yet"
  | RI.Ast.VecLoad _         -> failwith "VecLoad instruction not implemented yet"
  | RI.Ast.VecStore _        -> failwith "VecStore instruction not implemented yet"
  | RI.Ast.VecLoadLane _     -> failwith "VecLoadLane instruction not implemented yet"
  | RI.Ast.VecStoreLane _    -> failwith "VecStoreLane instruction not implemented yet"
  | RI.Ast.MemorySize _      -> failwith "MemorySize instruction not implemented yet"
  | RI.Ast.MemoryGrow _      -> failwith "MemoryGrow instruction not implemented yet"
  | RI.Ast.MemoryFill _      -> failwith "MemoryFill instruction not implemented yet"
  | RI.Ast.MemoryCopy _      -> failwith "MemoryCopy instruction not implemented yet"
  | RI.Ast.MemoryInit
    (memoryidx, dataidx)     -> DL.MEMORY_dot_INIT_instr (ocaml_of_memoryidx memoryidx, ocaml_of_dataidx dataidx)
  | RI.Ast.DataDrop dataidx  -> DL.DATA_dot_DROP_instr (ocaml_of_dataidx dataidx)
  | RI.Ast.RefNull heaptype  -> DL.REF_dot_NULL_instr (ocaml_of_heaptype heaptype)
  | RI.Ast.RefFunc _         -> failwith "RefFunc instruction not implemented yet"
  | RI.Ast.RefIsNull         -> failwith "RefIsNull instruction not implemented yet"
  | RI.Ast.RefAsNonNull      -> failwith "RefAsNonNull instruction not implemented yet"
  | RI.Ast.RefTest _         -> failwith "RefTest instruction not implemented yet"
  | RI.Ast.RefCast _         -> failwith "RefCast instruction not implemented yet"
  | RI.Ast.RefEq             -> failwith "RefEq instruction not implemented yet"
  | RI.Ast.RefI31            -> failwith "RefI31 instruction not implemented yet"
  | RI.Ast.I31Get _          -> failwith "I31Get instruction not implemented yet"
  | RI.Ast.StructNew _       -> failwith "StructNew instruction not implemented yet"
  | RI.Ast.StructGet _       -> failwith "StructGet instruction not implemented yet"
  | RI.Ast.StructSet _       -> failwith "StructSet instruction not implemented yet"
  | RI.Ast.ArrayNew _        -> failwith "ArrayNew instruction not implemented yet"
  | RI.Ast.ArrayNewFixed _   -> failwith "ArrayNewFixed instruction not implemented yet"
  | RI.Ast.ArrayNewData _    -> failwith "ArrayNewData instruction not implemented yet"
  | RI.Ast.ArrayNewElem _    -> failwith "ArrayNewElem instruction not implemented yet"
  | RI.Ast.ArrayGet _        -> failwith "ArrayGet instruction not implemented yet"
  | RI.Ast.ArraySet _        -> failwith "ArraySet instruction not implemented yet"
  | RI.Ast.ArrayLen          -> failwith "ArrayLen instruction not implemented yet"
  | RI.Ast.ArrayCopy _       -> failwith "ArrayCopy instruction not implemented yet"
  | RI.Ast.ArrayFill _       -> failwith "ArrayFill instruction not implemented yet"
  | RI.Ast.ArrayInitData _   -> failwith "ArrayInitData instruction not implemented yet"
  | RI.Ast.ArrayInitElem _   -> failwith "ArrayInitElem instruction not implemented yet"
  | RI.Ast.ExternConvert _   -> failwith "ExternConvert instruction not implemented yet"
  | RI.Ast.Const num         -> begin match num.it with
    | RI.Value.I32 n         -> DL.CONST_instr (DL.I32_numtype, DL.C_pct__uc_un (Int32.to_int n))
    | RI.Value.I64 n         -> failwith "I64 not implemented yet"
    | RI.Value.F32 n         -> failwith "F32 not implemented yet"
    | RI.Value.F64 n         -> failwith "F64 not implemented yet"
    end
  | RI.Ast.Test testop       -> begin match testop with
    | RI.Value.I32 RI.Ast.IntOp.Eqz -> DL.TESTOP_instr (DL.I32_numtype, DL.EQZ_testop_)
    | _ -> failwith "non-i32 testop not implemented yet"
    end
  | RI.Ast.Compare relop     -> begin match relop with
    | RI.Value.I32 RI.Ast.IntOp.Eq     -> DL.RELOP_instr (DL.I32_numtype, DL.EQ_relop_)
    | RI.Value.I32 RI.Ast.IntOp.Ne     -> DL.RELOP_instr (DL.I32_numtype, DL.NE_relop_)
    | RI.Value.I32 RI.Ast.IntOp.Lt sx  -> DL.RELOP_instr (DL.I32_numtype, DL.LT_relop_ (ocaml_of_sx sx))
    | RI.Value.I32 RI.Ast.IntOp.Le sx  -> DL.RELOP_instr (DL.I32_numtype, DL.LE_relop_ (ocaml_of_sx sx))
    | RI.Value.I32 RI.Ast.IntOp.Ge sx  -> DL.RELOP_instr (DL.I32_numtype, DL.GE_relop_ (ocaml_of_sx sx))
    | RI.Value.I32 RI.Ast.IntOp.Gt sx  -> DL.RELOP_instr (DL.I32_numtype, DL.GT_relop_ (ocaml_of_sx sx))
    | _                                -> failwith "non-i32 relop not implemented yet"
    end
  | RI.Ast.Unary _           -> failwith "Unary instruction not implemented yet"
  | RI.Ast.Binary binop      -> begin match binop with
    | RI.Value.I32 RI.Ast.IntOp.Add    -> DL.BINOP_instr (DL.I32_numtype, DL.ADD_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Sub    -> DL.BINOP_instr (DL.I32_numtype, DL.SUB_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Mul    -> DL.BINOP_instr (DL.I32_numtype, DL.MUL_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Div sx -> DL.BINOP_instr (DL.I32_numtype, DL.DIV_binop_ (ocaml_of_sx sx))
    | RI.Value.I32 RI.Ast.IntOp.Rem sx -> DL.BINOP_instr (DL.I32_numtype, DL.REM_binop_ (ocaml_of_sx sx))
    | RI.Value.I32 RI.Ast.IntOp.Or     -> DL.BINOP_instr (DL.I32_numtype, DL.OR_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Xor    -> DL.BINOP_instr (DL.I32_numtype, DL.XOR_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Shl    -> DL.BINOP_instr (DL.I32_numtype, DL.SHL_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Shr sx -> DL.BINOP_instr (DL.I32_numtype, DL.SHR_binop_ (ocaml_of_sx sx))
    | RI.Value.I32 RI.Ast.IntOp.Rotl   -> DL.BINOP_instr (DL.I32_numtype, DL.ROTL_binop_)
    | RI.Value.I32 RI.Ast.IntOp.Rotr   -> DL.BINOP_instr (DL.I32_numtype, DL.ROTR_binop_)
    | _ -> failwith "non-i32 binary op not implemented yet"
    end
  | RI.Ast.Convert _         -> failwith "Convert instruction not implemented yet"
  | RI.Ast.VecConst _        -> failwith "VecConst instruction not implemented yet"
  | RI.Ast.VecTest _         -> failwith "VecTest instruction not implemented yet"
  | RI.Ast.VecCompare _      -> failwith "VecCompare instruction not implemented yet"
  | RI.Ast.VecUnary _        -> failwith "VecUnary instruction not implemented yet"
  | RI.Ast.VecBinary _       -> failwith "VecBinary instruction not implemented yet"
  | RI.Ast.VecTernary _      -> failwith "VecTernary instruction not implemented yet"
  | RI.Ast.VecConvert _      -> failwith "VecConvert instruction not implemented yet"
  | RI.Ast.VecShift _        -> failwith "VecShift instruction not implemented yet"
  | RI.Ast.VecBitmask _      -> failwith "VecBitmask instruction not implemented yet"
  | RI.Ast.VecTestBits _     -> failwith "VecTestBits instruction not implemented yet"
  | RI.Ast.VecUnaryBits _    -> failwith "VecUnaryBits instruction not implemented yet"
  | RI.Ast.VecBinaryBits _   -> failwith "VecBinaryBits instruction not implemented yet"
  | RI.Ast.VecTernaryBits _  -> failwith "VecTernaryBits instruction not implemented yet"
  | RI.Ast.VecSplat _        -> failwith "VecSplat instruction not implemented yet"
  | RI.Ast.VecExtract _      -> failwith "VecExtract instruction not implemented yet"
  | RI.Ast.VecReplace _      -> failwith "VecReplace instruction not implemented yet"
  let ocaml_of_func (func: RI.Ast.func) =
    (*Printf.printf "Generating OCaml for function...\n";*)
    let RI.Ast.Func (idx, locals, instrs) = func.it in
    DL.FUNC_func (
      ocaml_of_ast_typeidx idx,
      List.map ocaml_of_local locals,
      List.map ocaml_of_instr instrs
    )

let ocaml_of_externidx exix =
  match exix with
  | RI.Ast.TagX tagidx       -> DL.TAG_externidx (ocaml_of_tagidx tagidx)
  | RI.Ast.GlobalX globalidx -> DL.GLOBAL_externidx (ocaml_of_globalidx globalidx)
  | RI.Ast.MemoryX memoryidx -> DL.MEM_externidx (ocaml_of_memoryidx memoryidx)
  | RI.Ast.TableX tableidx   -> DL.TABLE_externidx (ocaml_of_tableidx tableidx)
  | RI.Ast.FuncX funcidx     -> DL.FUNC_externidx (ocaml_of_funcidx funcidx)
let ocaml_of_export (export : RI.Ast.export) : DL.export =
  let Export (name, exix) = export.it in
  EXPORT_export (ocaml_of_name name, ocaml_of_externidx exix.it)

let ocaml_of_globaltype (globaltype : RT.globaltype) : DL.globaltype =
  let RT.GlobalT (mut, vt) = globaltype in
  DL.C_pct__pct__globaltype (ocaml_of_mut mut, ocaml_of_valtype vt)

let ocaml_of_global (global : RI.Ast.global) : DL.global =
  let RI.Ast.Global (globaltype, const) = global.it in
  DL.GLOBAL_global (ocaml_of_globaltype globaltype, (List.map ocaml_of_instr const.it))

let ocaml_of_addrtype (addrtype : RT.addrtype) : DL.addrtype =
  match addrtype with
  | RT.I32AT -> DL.I32_addrtype
  | RT.I64AT -> DL.I64_addrtype

let ocaml_of_limits (limits : RT.limits) : DL.limits =
  DL.C_lbracksq_pct__dot__dot__pct__rbracksq_limits (ocaml_of_int64 limits.min, Option.map ocaml_of_int64 limits.max)

let ocaml_of_reftype ((null, ht) : RT.reftype) : DL.reftype =
  DL.REF_reftype (ocaml_of_null null, ocaml_of_heaptype ht)

let ocaml_of_tabletype (tabletype : RT.tabletype) : DL.tabletype =
  let RT.TableT (addrtype, lim, rt) = tabletype in
  DL.C_pct__pct__pct__tabletype (ocaml_of_addrtype addrtype, ocaml_of_limits lim, ocaml_of_reftype rt)

let ocaml_of_table (table : RI.Ast.table) : DL.table =
  let RI.Ast.Table (tabletype, consts) = table.it in
  DL.TABLE_table (ocaml_of_tabletype tabletype, List.map ocaml_of_instr consts.it)

let ocaml_of_module (module_: RI.Ast.module_) : DL.module_ = DL.MODULE_module_ (
  List.map ocaml_of_type module_.it.types,
  [], (* imports *)
  [], (* tags *)
  List.map ocaml_of_global module_.it.globals,
  [], (* mems *)
  List.map ocaml_of_table module_.it.tables,
  List.map ocaml_of_func module_.it.funcs,
  [], (* data *)
  [], (* elems *)
  None,
  List.map ocaml_of_export module_.it.exports
)

let ocaml_of_value (v : RI.Value.value) : DL.val_ =
  match v with
  | RI.Value.Num (RI.Value.I32 n) -> DL.CONST_val_ (DL.I32_numtype, DL.C_pct__uc_un (Int32.to_int n))
  | _ -> failwith "TODO: implement non-I32 values"

let ocaml_of_literal (lit : RI.Script.literal) : DL.val_ =
  ocaml_of_value lit.it

(* convert OCaml values to RI values again to check assertions *)
let phrase_of_ocaml (x : 'a) : 'a RI.Source.phrase = RI.Source.(x @@ no_region)
let instr_of_ocaml (instr: DL.instr) : RI.Ast.instr' =
  match instr with
  | DL.UNREACHABLE_instr      -> RI.Ast.Unreachable
  | DL.NOP_instr              -> RI.Ast.Nop
  | DL.DROP_instr             -> RI.Ast.Drop
  | DL.SELECT_instr None      -> RI.Ast.Select None
  | DL.CONST_instr (nt, num)    ->
    let C_pct__uc_un n = num in
    begin match nt with
    | DL.I32_numtype          -> RI.Ast.Const (phrase_of_ocaml (RI.Value.I32 (Int32.of_int n)))
    | _ -> failwith "non-I32 const not implemented yet"
    end
  | _ -> failwith "instruction not implemented yet"

let val_of_ocaml (instr: DL.instr) : RI.Value.value =
  match instr with
  | DL.CONST_instr (nt, num) ->
    let C_pct__uc_un n = num in
    begin match nt with
    | DL.I32_numtype -> RI.Value.Num (RI.Value.I32 (Int32.of_int n))
    | _              -> failwith "TODO: non-I32 const"
    end
  | _ ->
    let instr_str = string_of_dlinstr instr in
    failwith ("TODO: non-CONST instruction: " ^ instr_str)
