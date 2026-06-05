theory Base_Defs
	imports Main reference_isabelle_output_wasm2 Properties_Aux Subtyping Subtyping_Properties
begin

(* 
instr is always a basic instruction; 
admininstr wraps around instr.
admininstr includes REF.FUNC_ADDR REF.HOST_ADDR. REF.NULL is dual purpose, which is both an instr and also an admin instr. 

*)
definition is_const :: "admininstr \<Rightarrow> bool" where
  "is_const e = (case e of admininstr_subcase_7 (admininstr_subtype_7_TRAP) \<Rightarrow> False
                         | admininstr_subcase_7 (CALL_ADDR _)               \<Rightarrow> False
                         | _ \<Rightarrow> True)"

(*
  | Invoke i
  | Label nat "e list" "e list"
  | Frame nat f "e list"
  | Ref v_ref

*)
 
	(*
	| admininstr_subtype_7_REF_HOST_ADDR "hostaddr"
	| admininstr_subtype_7_REF_FUNC_ADDR "funcaddr"
	| admininstr_subtype_7_DATA_DROP "dataidx"
	| admininstr_subtype_7_MEMORY_INIT "dataidx"
	| admininstr_subtype_7_MEMORY_COPY
	| admininstr_subtype_7_MEMORY_FILL
	| admininstr_subtype_7_MEMORY_GROW

definition const_list :: "e list \<Rightarrow> bool" where
  "const_list xs = list_all is_const xs"
*)
(*
7.5.4 Administrative Instructions
Typing rules for administrative instructions are specified as follows. In addition to the context C, typing of these
instructions is defined under a given store S. To that end, all previous typing judgements C \<turnstile> prop are generalized
to include the store, as in S;C \<turnstile> prop, by implicitly adding S to all rules– S is never modified by the pre-existing
rules, but it is accessed in the extra rules for administrative instructions given below.
*)
end