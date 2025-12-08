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

(* todo: possibly a better way of doing this since we want a way to express dependent types anyway,, also int32 translates to nat for now but probably should not *)
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

let ocaml_typeuse_of_typeidx (n : DL.typeidx) = DL.C_IDX_typeuse n 
let ocaml_of_int32 (n : int32) : DL.nat = Int32.to_int n
let ocaml_of_mut mut = match mut with 
  | RT.Cons -> None
  | RT.Var  -> Some DL.MUT_uc_mut

let ocaml_of_null = function
  | RT.Null    -> Some DL.NULL_uc_null
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
  | RT.Final   -> Some DL.FINAL_uc_final

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
  Printf.printf "Generating OCaml for type...\n";
  DL.TYPE_type_ (ocaml_of_rectype ty.it)

let ocaml_of_local (local: RI.Ast.local) =
  let RI.Ast.Local vt = local.it in
  DL.LOCAL_local (ocaml_of_valtype vt)

let ocaml_of_instr (instr: RI.Ast.instr) =
  match instr.it with
  | RI.Ast.Unreachable      -> DL.UNREACHABLE_instr
  | RI.Ast.Nop              -> DL.NOP_instr
  | RI.Ast.Drop             -> DL.DROP_instr
  | RI.Ast.Select None      -> DL.SELECT_instr None
  | RI.Ast.Select (Some vt) -> DL.SELECT_instr (Some (List.map ocaml_of_valtype vt))
  | RI.Ast.Const num        -> begin match num.it with 
    | RI.Value.I32 n        -> DL.CONST_instr (DL.I32_numtype, DL.C_pct__uc_un (Int32.to_int n))
    | RI.Value.I64 n        -> failwith "I64 not implemented yet"
    | RI.Value.F32 n        -> failwith "F32 not implemented yet"
    | RI.Value.F64 n        -> failwith "F64 not implemented yet"
    end
  | RI.Ast.Binary binop     -> begin match binop with 
    | RI.Value.I32 RI.Ast.IntOp.Add -> DL.BINOP_instr (DL.I32_numtype, DL.ADD_binop_)
    | _ -> failwith "non-addition binary op not implemented yet"
    end
  | RI.Ast.Call funcidx     -> DL.CALL_instr (ocaml_of_funcidx funcidx)
  | RI.Ast.CallRef typeidx  -> DL.CALL_REF_instr (ocaml_typeuse_of_typeidx (ocaml_of_ast_typeidx typeidx))
  | RI.Ast.RefNull heaptype -> DL.REF_dot_NULL_instr (ocaml_of_heaptype heaptype)
  | RI.Ast.TableInit 
    (tableidx, elemidx)     -> DL.TABLE_dot_INIT_instr (ocaml_of_tableidx tableidx, ocaml_of_elemidx elemidx)
  | RI.Ast.ElemDrop elemidx -> DL.ELEM_dot_DROP_instr (ocaml_of_elemidx elemidx)
  | RI.Ast.MemoryInit 
    (memoryidx, dataidx)    -> DL.MEMORY_dot_INIT_instr (ocaml_of_memoryidx memoryidx, ocaml_of_dataidx dataidx)
  | RI.Ast.DataDrop dataidx -> DL.DATA_dot_DROP_instr (ocaml_of_dataidx dataidx)  
  | RI.Ast.LocalGet localidx -> DL.LOCAL_dot_GET_instr (ocaml_of_localidx localidx)   
  | _                       -> 
    let instr_str = Backend_animation.Temp_print.string_of_instr instr in
    failwith ("instruction not implemented yet: " ^ instr_str)

  let ocaml_of_func (func: RI.Ast.func) =
    Printf.printf "Generating OCaml for function...\n";
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
let ocaml_of_export (export: RI.Ast.export) : DL.export =
  let Export (name, exix) = export.it in
  EXPORT_export (ocaml_of_name name, ocaml_of_externidx exix.it)

(* only do types, funcs and exports for now *)
let ocaml_of_module (module_: RI.Ast.module_) : DL.module_ = DL.MODULE_module_ (
  List.map ocaml_of_type module_.it.types,
  [],
  [],
  [],
  [],
  [],
  List.map ocaml_of_func module_.it.funcs,
  [],
  [],
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
