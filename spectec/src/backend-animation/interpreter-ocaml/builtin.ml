open Dl_codegen_types

(* for now, do the very inefficient thing - actually it might not be that bad, the compiler may optimise constructor-matching since we ignore the arguments *)
let use_step_pure = function 
  | NOP_instr
  | UNREACHABLE_instr
  | DROP_instr 
  | SELECT_instr _
  | CONST_instr _
  | BINOP_instr _ 
  | REF_dot_I31_NUM_instr _ 
  | TRAP_instr               -> true 
  | _                        -> false 

let use_step_read = function
  | CALL_instr _ | CALL_REF_instr _ | REF_dot_NULL_instr _ 
  | LOCAL_dot_GET_instr _ | TABLE_dot_INIT_instr _
  | MEMORY_dot_INIT_instr _ -> true 
  | _ -> false

let use_step_table = function 
  | ELEM_dot_DROP_instr _
  | DATA_dot_DROP_instr _ -> true 
  | _ -> false

let use_idk = function 
  | REF_dot_STRUCT_ADDR_instr _
  | REF_dot_ARRAY_ADDR_instr _
  | REF_dot_FUNC_ADDR_instr _
  | REF_dot_EXN_ADDR_instr _
  | REF_dot_HOST_ADDR_instr _
  | REF_dot_EXTERN_instr _ -> true 
  | _ -> false

(*let dispatch_step_pure = function
  | [instr; arg] ->
    let mixop, _ = match_caseE "instr" instr in
    (match Common.Map.find_opt (List.hd (List.hd mixop)) !Common.step_table with
    | Some (rel_name, rule_name, _) when rel_name = "Step_pure" -> call_func (rel_name ^ "/" ^ rule_name) [expA arg]
    | _ -> error instr.at ("No $Step_pure rule for instr" ^ string_of_exp instr)
    )
  | es -> error_values ("Args to $dispatch_step_pure") es*)

let inv_concat_ a0 = failwith "TODO: implement Built-in function inv_concat_"
let inv_concatn_ a0 a1 = failwith "TODO: implement Built-in function inv_concatn_"

let uc_nd () = failwith "TODO: implement Built-in function inv_concatn_"
let utf8 a0 = failwith "TODO: implement Built-in function utf8"
let use_step a0 = failwith "TODO: implement Built-in function use_step"
let use_step_ctxt a0 = failwith "TODO: implement Built-in function use_step_ctxt"
let dispatch_step a0 a1 = failwith "TODO: implement Built-in function dispatch_step"
let dispatch_step_read a0 a1 = failwith "TODO: implement Built-in function dispatch_step_pure"
let step_ctxt a0 = failwith "TODO: implement Built-in function step_ctxt"