theory Base_Defs
	imports Main reference_isabelle_output_wasm2 Properties_Aux Subtyping Subtyping_Properties
	  admininstr
begin

(* 
instr is always a basic instruction; 
admininstr repeats instr and more.
admininstr includes REF.FUNC_ADDR REF.HOST_ADDR.
NB: REF.NULL is dual purpose, which is both an instr and also an admin instr. 


definition is_const :: "admininstr \<Rightarrow> bool" where
  "is_const e = (case e of admininstr_subcase_7 (admininstr_subtype_7_TRAP)) \<Rightarrow> False
 ...
is replaced by
*)

definition const_list :: "admininstr list \<Rightarrow> bool" where
  "const_list xs = list_all is_instr xs"

(*
7.5.4 Administrative Instructions
Typing rules for administrative instructions are specified as follows. In addition to the context C, typing of these
instructions is defined under a given store S. To that end, all previous typing judgements C \<turnstile> prop are generalized
to include the store, as in S;C \<turnstile> prop, by implicitly adding S to all rules– S is never modified by the pre-existing
rules, but it is accessed in the extra rules for administrative instructions given below.
*)
end