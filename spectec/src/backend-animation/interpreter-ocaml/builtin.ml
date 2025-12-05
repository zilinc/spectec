open Dl_codegen_types

(* for now, do the very inefficient thing - actually it might not be that bad, the compiler may optimise constructor-matching since we ignore the arguments *)
let use_step_pure = function 
  | NOP_instr
  | UNREACHABLE_instr
  | DROP_instr 
  | SELECT_instr _
  | BINOP_instr _ 
  | REF_dot_I31_NUM_instr _ 
  | TRAP_instr               -> true 
  | _                        -> false 

let use_step_read = function
  | CALL_instr _ | CALL_REF_instr _ | REF_dot_NULL_instr _ 
  | LOCAL_dot_GET_instr _ | TABLE_dot_INIT_instr _
  | MEMORY_dot_INIT_instr _ -> true 
  | _ -> false

let use_step = function 
  | ELEM_dot_DROP_instr _
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