module RI = Reference_interpreter
module RT = RI.Types 
module DL = Dl_codegen_types

let ocaml_of_list f lst = DL.C_pct__list_ (List.map f lst)

(* todo: possibly a better way of doing this since we want a way to express dependent types anyway,, also int32 translates to nat for now but probably should not *)
let ocaml_of_typeidx (n : RT.typeidx) : DL.typeidx = C_pct__uc_un (Int32.to_int n)

let ocaml_of_ast_typeidx (n : RI.Ast.typeidx) : DL.typeidx = C_pct__uc_un (Int32.to_int n.it)
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
  | _                       -> failwith "instruction not implemented yet"

  let ocaml_of_func (func: RI.Ast.func) =
  let RI.Ast.Func (idx, locals, instrs) = func.it in
  DL.FUNC_func (
    ocaml_of_ast_typeidx idx,
    List.map ocaml_of_local locals,
    List.map ocaml_of_instr instrs
  )

(* let ocaml_of_export (export: Ast.export) =
  let Export (name, exix) = export in
  caseV [["EXPORT"];[];[]] [ocaml_of_name name; ocaml_of_externidx exix]*)

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
  [] (* do this *)
)