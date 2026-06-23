open Dl_codegen_types

let use_step_pure = function 
  | NOP_instr
  | UNREACHABLE_instr
  | DROP_instr 
  | SELECT_instr _
  | IFPctPctELSEPct_instr _
  | BR_IF_instr _
  | BR_TABLE_instr _
  | BR_ON_NULL_instr _
  | BR_ON_NON_NULL_instr _
  | CALL_INDIRECT_instr _
  | RETURN_CALL_INDIRECT_instr _
  | UNOP_instr _
  | BINOP_instr _ 
  | TESTOP_instr _
  | RELOP_instr _
  | CVTOP_instr _
  | REF_dot_IS_NULL_instr
  | REF_dot_AS_NON_NULL_instr
  | REF_dot_EQ_instr
  | I31_dot_GET_instr _
  | ARRAY_dot_NEW_instr _
  | EXTERN_dot_CONVERT_ANY_instr
  | ANY_dot_CONVERT_EXTERN_instr
  | VVUNOP_instr _
  | VVBINOP_instr _
  | VVTERNOP_instr _
  | VVTESTOP_instr _
  | VUNOP_instr _ 
  | VBINOP_instr _
  | VTERNOP_instr _
  | VTESTOP_instr _
  | VRELOP_instr _
  | VSHIFTOP_instr _
  | VBITMASK_instr _
  | VSWIZZLOP_instr _
  | VSHUFFLE_instr _
  | VSPLAT_instr _
  | VEXTRACT_LANE_instr _
  | VREPLACE_LANE_instr _
  | VEXTUNOP_instr _
  | VEXTBINOP_instr _
  | VEXTTERNOP_instr _
  | VNARROW_instr _
  | VCVTOP_instr _
  | LOCAL_dot_TEE_instr _
  | REF_dot_I31_instr (* not sure *) -> true
  | _                        -> false

let use_step_read = function
  | BLOCK_instr _
  | LOOP_instr _
  | BR_ON_CAST_instr _
  | BR_ON_CAST_FAIL_instr _
  | CALL_instr _
  | RETURN_CALL_instr _
  | THROW_REF_instr
  | TRY_TABLE_instr _
  | REF_dot_NULL_instr _
  | REF_dot_FUNC_instr _ 
  | REF_dot_TEST_instr _
  | REF_dot_CAST_instr _
  | STRUCT_dot_NEW_DEFAULT_instr _
  | STRUCT_dot_GET_instr _
  | ARRAY_dot_NEW_DEFAULT_instr _
  | ARRAY_dot_NEW_ELEM_instr _
  | ARRAY_dot_NEW_DATA_instr _
  | ARRAY_dot_GET_instr _
  | ARRAY_dot_LEN_instr
  | ARRAY_dot_FILL_instr _
  | ARRAY_dot_COPY_instr _
  | ARRAY_dot_INIT_DATA_instr _
  | ARRAY_dot_INIT_ELEM_instr _
  | LOCAL_dot_GET_instr _
  | GLOBAL_dot_GET_instr _
  | TABLE_dot_GET_instr _
  | TABLE_dot_SIZE_instr _
  | TABLE_dot_FILL_instr _
  | TABLE_dot_COPY_instr _
  | TABLE_dot_INIT_instr _
  | LOAD_instr _
  | VLOAD_instr _
  | VLOAD_LANE_instr _
  | MEMORY_dot_SIZE_instr _
  | MEMORY_dot_FILL_instr _
  | MEMORY_dot_COPY_instr _
  | MEMORY_dot_INIT_instr _ -> true 
  | _ -> false 

let use_step = function
  | CALL_REF_instr _
  | THROW_instr _
  | STRUCT_dot_NEW_instr _
  | STRUCT_dot_SET_instr _
  | ARRAY_dot_NEW_FIXED_instr _
  | ARRAY_dot_SET_instr _
  | LOCAL_dot_SET_instr _
  | GLOBAL_dot_SET_instr _
  | TABLE_dot_SET_instr _
  | TABLE_dot_GROW_instr _
  | ELEM_dot_DROP_instr _
  | STORE_instr _
  | VSTORE_instr _
  | VSTORE_LANE_instr _
  | MEMORY_dot_GROW_instr _
  | DATA_dot_DROP_instr _  -> true 
  | _ -> false

let use_step_ctxt = function 
  | LABEL_Pct_lbrackcuPct_rbrackcuPct_instr _
  | FRAME_Pct_lbrackcuPct_rbrackcuPct_instr _ 
  | HANDLER_Pct_lbrackcuPct_rbrackcuPct_instr _ -> true
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
let uc_r_fmadd () = failwith "TODO: implement Built-in function uc_r_fmadd"
let uc_r_fmin () = failwith "TODO: implement Built-in function uc_r_fmin"
let uc_r_fmax () = failwith "TODO: implement Built-in function uc_r_fmax"
let uc_r_idot () = failwith "TODO: implement Built-in function uc_r_idot"
let uc_r_iq15mulr () = failwith "TODO: implement Built-in function uc_r_iq15mulr"
let uc_r_trunc_u () = failwith "TODO: implement Built-in function uc_r_trunc_u"
let uc_r_trunc_s () = failwith "TODO: implement Built-in function uc_r_trunc_s"
let uc_r_swizzle () = failwith "TODO: implement Built-in function uc_r_swizzle"
let uc_r_laneselect () = failwith "TODO: implement Built-in function uc_r_laneselect"
let s33_to_u32 a0 = failwith "TODO: implement Built-in function s33_to_u32"
let ibits_ a0 a1 = failwith "TODO: implement Built-in function ibits_"
let fbits_ a0 a1 = failwith "TODO: implement Built-in function fbits_"
let ibytes_ a0 a1 = failwith "TODO: implement Built-in function ibytes_"
let fbytes_ a0 a1 = failwith "TODO: implement Built-in function fbytes_"
let nbytes_ a0 a1 = failwith "TODO: implement Built-in function nbytes_"
let vbytes_ a0 a1 = failwith "TODO: implement Built-in function vbytes_"
let zbytes_ a0 a1 = failwith "TODO: implement Built-in function zbytes_"
let cbytes_ a0 a1 = failwith "TODO: implement Built-in function cbytes_"
let inv_ibits_ a0 a1 = failwith "TODO: implement Built-in function inv_ibits_"
let inv_fbits_ a0 a1 = failwith "TODO: implement Built-in function inv_fbits_"
let inv_ibytes_ a0 a1 = failwith "TODO: implement Built-in function uc_r_fmadd"
let inv_fbytes_ a0 a1 = failwith "TODO: implement Built-in function inv_ibytes_"
let inv_nbytes_ a0 a1 = failwith "TODO: implement Built-in function inv_nbytes_"
let inv_vbytes_ a0 a1 = failwith "TODO: implement Built-in function inv_vbytes_"
let inv_zbytes_ a0 a1 = failwith "TODO: implement Built-in function inv_zbytes_"
let inv_cbytes_ a0 a1 = failwith "TODO: implement Built-in function inv_cbytes_"
let truncz a0 = failwith "TODO: implement Built-in function truncz"
let ceilz a0 = failwith "TODO: implement Built-in function ceilz"
let iclz_ a0 a1 = failwith "TODO: implement Built-in function iclz_"
let ictz_ a0 a1 = failwith "TODO: implement Built-in function ictz_"
let ipopcnt_ a0 a1 = failwith "TODO: implement Built-in function ipopcnt_"
let iq15mulr_sat_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function iq15mulr_sat_"
let irelaxed_q15mulr_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function irelaxed_q15mulr_"
let inot_ a0 a1 = failwith "TODO: implement Built-in function inot_"
let irev_ a0 a1 = failwith "TODO: implement Built-in function irev_"
let iand_ a0 a1 a2 = failwith "TODO: implement Built-in function iand_"
let iandnot_ a0 a1 a2 = failwith "TODO: implement Built-in function iandnot_"
let ior_ a0 a1 a2 = failwith "TODO: implement Built-in function ior_"
let ixor_ a0 a1 a2 = failwith "TODO: implement Built-in function ixor_"
let ishl_ a0 a1 a2 = failwith "TODO: implement Built-in function ishl_"
let ishr_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function ishr_"
let irotl_ a0 a1 a2 = failwith "TODO: implement Built-in function irotl_"
let irotr_ a0 a1 a2 = failwith "TODO: implement Built-in function irotr_"
let ibitselect_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function ibitselect_"
let iavgr_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function iavgr_"
let irelaxed_laneselect_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function irelaxed_laneselect_"
let irelaxed_laneselect_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function irelaxed_laneselect_"
let fabs_ a0 a1 = failwith "TODO: implement Built-in function fabs_"
let fneg_ a0 a1 = failwith "TODO: implement Built-in function fneg_"
let fsqrt_ a0 a1 = failwith "TODO: implement Built-in function fsqrt_"
let fceil_ a0 a1 = failwith "TODO: implement Built-in function fceil_"
let ffloor_ a0 a1 = failwith "TODO: implement Built-in function ffloor_"
let ftrunc_ a0 a1 = failwith "TODO: implement Built-in function ftrunc_"
let fnearest_ a0 a1 = failwith "TODO: implement Built-in function fnearest_"
let fadd_ a0 a1 a2 = failwith "TODO: implement Built-in function fadd_"
let fsub_ a0 a1 a2 = failwith "TODO: implement Built-in function fsub_"
let fmul_ a0 a1 a2 = failwith "TODO: implement Built-in function fmul_"
let fdiv_ a0 a1 a2 = failwith "TODO: implement Built-in function fdiv_"
let fmin_ a0 a1 a2 = failwith "TODO: implement Built-in function fmin_"
let fmax_ a0 a1 a2 = failwith "TODO: implement Built-in function fmax_"
let fpmin_ a0 a1 a2 = failwith "TODO: implement Built-in function fpmin_"
let fpmax_ a0 a1 a2 = failwith "TODO: implement Built-in function fpmax_"
let frelaxed_min_ a0 a1 a2 = failwith "TODO: implement Built-in function frelaxed_min_"
let frelaxed_max_ a0 a1 a2 = failwith "TODO: implement Built-in function frelaxed_max_"
let fcopysign_ a0 a1 a2 = failwith "TODO: implement Built-in function fcopysign_"
let feq_ a0 a1 a2 = failwith "TODO: implement Built-in function feq_"
let fne_ a0 a1 a2 = failwith "TODO: implement Built-in function fne_"
let flt_ a0 a1 a2 = failwith "TODO: implement Built-in function flt_"
let fgt_ a0 a1 a2 = failwith "TODO: implement Built-in function fgt_"
let fle_ a0 a1 a2 = failwith "TODO: implement Built-in function fle_"
let fge_ a0 a1 a2 = failwith "TODO: implement Built-in function fge_"
let frelaxed_madd_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function frelaxed_madd_"
let frelaxed_nmadd_ a0 a1 a2 a3 = failwith "TODO: implement Built-in function frelaxed_nmadd_"
let wrap__ a0 a1 a2 = failwith "TODO: implement Built-in function wrap__"
let extend__ a0 a1 a2 a3 = failwith "TODO: implement Built-in function extend__"
let trunc__ a0 a1 a2 a3 = failwith "TODO: implement Built-in function trunc__"
let trunc_sat__ a0 a1 a2 a3 = failwith "TODO: implement Built-in function trunc_sat__"
let relaxed_trunc__ a0 a1 a2 a3 = failwith "TODO: implement Built-in function relaxed_trunc__"
let demote__ a0 a1 a2 = failwith "TODO: implement Built-in function demote__"
let promote__ a0 a1 a2 = failwith "TODO: implement Built-in function promote__"
let convert__ a0 a1 a2 a3 = failwith "TODO: implement Built-in function convert__"
let narrow__ a0 a1 a2 a3 = failwith "TODO: implement Built-in function narrow__"
let reinterpret__ a0 a1 a2 = failwith "TODO: implement Built-in function reinterpret__"
let lanes_ a0 a1 = failwith "TODO: implement Built-in function lanes_"
let inv_lanes_ a0 a1 = failwith "TODO: implement Built-in function inv_lanes_"

let step a0 a1 = failwith "TODO: implement Built-in function inv_lanes_"

let uc_step_pure_slashbr a0 = failwith "TODO: implement Built-in function uc_step_pure_slashbr"

let uc_step_pure_slashreturn a0 = failwith "TODO: implement Built-in function uc_step_pure_slashbr"

let uc_module_ok_fn a0 = failwith "TODO: implement Built-in function uc_module_ok_fn"

let uc_externaddr_ok_fn a0 a1 a2 = failwith "TODO: implement Built-in function uc_externaddr_ok_fn"

let uc_step_read_slashreturn_call_ref a0 = failwith "TODO: implement Built-in function uc_step_read_slashreturn_call_ref"

let uc_step_slashctxt a0 = failwith "TODO: implement Built-in function uc_step_slashctxt"

let uc_heaptype_sub_fn a0 a1 a2 = failwith "TODO: implement Built-in function uc_heaptype_sub_fn"
let ieee_ a0 a1 = failwith "TODO: implement Built-in function ieee_"

let dots = ()
let ordered a0 = failwith "TODO: implement Built-in function ordered"

let instrdots () = failwith "TODO: implement Built-in function instrdots"
let uc_allocx a0 a1 a2 = failwith "TODO: implement Built-in function uc_allocx"