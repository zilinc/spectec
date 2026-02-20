open Dl_codegen_types

let use_step_pure = function 
  | NOP_instr
  | UNREACHABLE_instr
  | DROP_instr 
  | SELECT_instr _
  | IF_pct__pct_ELSE_pct__instr _
  | BR_instr _
  | BR_IF_instr _
  | BR_TABLE_instr _
  | BR_ON_NULL_instr _
  (*| BR_ON_NON_NULL _
  | CALL_INDIRECT
  | RETURN_CALL_INDIRECT*)
  | RETURN_instr
  (* | UNOP *)
  | RETURN_CALL_REF_instr _
  | BINOP_instr _ 
  | TESTOP_instr _
  | RELOP_instr _
  (*| CVTOP_instr 
  | REF_dot_IS_NULL_instr
  | REF_dot_AS_NON_NULL_instr
  | REF_dot_EQ_instr
  | I31_dot_GET_instr
  | ARRAY_dot_NEW_instr
  | EXTERN_dot_CONVERT_ANY_instr
  | ANY_dot_CONVERT_EXTERN_instr
  | VVUNOP_instr
  | VVBINOP_instr
  | VVTERNOP_instr
  | VVTESTOP_instr
  | VUNOP_instr 
  | VBINOP_instr
  | VTERNOP_instr
  | VTESTOP_instr
  | VRELOP_instr
  | VSHIFTOP_instr
  | VBITMASK_instr
  | VSWIZZLOP_instr
  | VSHUFFLE_instr
  | VSPLAT_instr
  | VEXTRACT_LANE_instr
  | VREPLACE_LANE_instr
  | VEXTUNOP_instr
  | VEXTBINOP_instr
  | VEXTTERNOP_instr
  | VNARROW_instr
  | VCVTOP_instr *)
  | LOCAL_dot_TEE_instr _
  | REF_dot_I31_NUM_instr _ 
  | TRAP_instr               -> true 
  | _                        -> false

let use_step_read = function
  | BLOCK_instr _
  | LOOP_instr _
  (* | BR_ON_CAST_instr
  | BR_ON_CAST_FAIL_instr *)
  | CALL_instr _
  (* | RETURN_CALL_instr *)
  | RETURN_CALL_REF_instr _
  | THROW_REF_instr
  (* | TRY_TABLE_instr *)
  | REF_dot_NULL_instr _
  | REF_dot_FUNC_ADDR_instr _ (* not sure if this is the same *)
  (* | REF_dot_TEST_instr
  | REF_dot_CAST_instr
  | STRUCT_dot_NEW_DEFAULT_instr
  | STRUCT_dot_GET_instr
  | ARRAY_dot_NEW_DEFAULT_instr
  | ARRAY_dot_NEW_ELEM_instr
  | ARRAY_dot_NEW_DATA_instr
  | ARRAY_dot_GET_instr
  | ARRAY_dot_LEN_instr
  | ARRAY_dot_FILL_instr
  | ARRAY_dot_COPY_instr
  | ARRAY_dot_INIT_DATA_instr
  | ARRAY_dot_INIT_ELEM_instr *)
  | LOCAL_dot_GET_instr _
  | GLOBAL_dot_GET_instr _
  | TABLE_dot_GET_instr _
  | TABLE_dot_SIZE_instr _
  (*| TABLE_dot_FILL_instr
  | TABLE_dot_COPY_instr *)
  | TABLE_dot_INIT_instr _
  | LOAD_instr _
  (* | VLOAD_instr
  | VLOAD_LANE_instr
  | MEMORY_dot_SIZE_instr
  | MEMORY_dot_FILL_instr
  | MEMORY_dot_COPY_instr *)
  | MEMORY_dot_INIT_instr _ -> true 
  | _ -> false 

let use_step = function
  | CALL_REF_instr _
  | ELEM_dot_DROP_instr _
  | LOCAL_dot_SET_instr _
  | GLOBAL_dot_SET_instr _
  | DATA_dot_DROP_instr _ -> true 
  | _ -> false

let use_step_ctxt = function 
  | LABEL__pct__lbrackcu_pct__rbrackcu_pct__instr _
  | FRAME__pct__lbrackcu_pct__rbrackcu_pct__instr _ -> true
  | _ -> false

let inv_concat_ a0 = failwith "TODO: implement Built-in function inv_concat_"
let inv_concatn_ a0 a1 = failwith "TODO: implement Built-in function inv_concatn_"

let uc_nd () = failwith "TODO: implement Built-in function inv_concatn_"
let utf8 a0 = failwith "TODO: implement Built-in function utf8"
let dispatch_step a0 a1 = failwith "TODO: implement Built-in function dispatch_step"
let dispatch_step_read a0 a1 = failwith "TODO: implement Built-in function dispatch_step_pure"
let step_ctxt a0 = failwith "TODO: implement Built-in function step_ctxt"

let hostcall a0 a1 a2 = failwith "TODO: implement Built-in function hostcall"

let nbytes_ a0 = failwith "TODO: implement Built-in function nbytes"

let inv_nbytes_ a0 a1 = failwith "TODO: implement Built-in function nbytes"

let idiv_ a0 a1 = failwith "TODO: implement Built-in function idiv_"
let irem_ a0 a1 = failwith "TODO: implement Built-in function irem_"
let imin_ a0 a1 = failwith "TODO: implement Built-in function imin_"

let uc_r_fmadd = failwith "TODO: implement Built-in function uc_r_fmadd"
let uc_r_fmin = failwith "TODO: implement Built-in function uc_r_fmin"
let uc_r_fmax = failwith "TODO: implement Built-in function uc_r_fmax"
let uc_r_idot = failwith "TODO: implement Built-in function uc_r_idot"
let uc_r_iq15mulr = failwith "TODO: implement Built-in function uc_r_iq15mulr"
let uc_r_trunc_u = failwith "TODO: implement Built-in function uc_r_trunc_u"
let uc_r_trunc_s = failwith "TODO: implement Built-in function uc_r_trunc_s"
let uc_r_swizzle = failwith "TODO: implement Built-in function uc_r_swizzle"
let uc_r_laneselect = failwith "TODO: implement Built-in function uc_r_laneselect"
let s33_to_u32 = failwith "TODO: implement Built-in function s33_to_u32"
let ibits_ = failwith "TODO: implement Built-in function ibits_"
let fbits_ = failwith "TODO: implement Built-in function fbits_"
let ibytes_ = failwith "TODO: implement Built-in function ibytes_"
let fbytes_ = failwith "TODO: implement Built-in function fbytes_"
let nbytes_ = failwith "TODO: implement Built-in function nbytes_"
let vbytes_ = failwith "TODO: implement Built-in function vbytes_"
let zbytes_ = failwith "TODO: implement Built-in function zbytes_"
let cbytes_ = failwith "TODO: implement Built-in function cbytes_"
let inv_ibits_ = failwith "TODO: implement Built-in function inv_ibits_"
let inv_fbits_ = failwith "TODO: implement Built-in function inv_fbits_"
let inv_ibytes_ = failwith "TODO: implement Built-in function uc_r_fmadd"
let inv_fbytes_ = failwith "TODO: implement Built-in function inv_ibytes_"
let inv_nbytes_ = failwith "TODO: implement Built-in function inv_nbytes_"
let inv_vbytes_ = failwith "TODO: implement Built-in function inv_vbytes_"
let inv_zbytes_ = failwith "TODO: implement Built-in function inv_zbytes_"
let inv_cbytes_ = failwith "TODO: implement Built-in function inv_cbytes_"
