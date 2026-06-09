section \<open>Subtyping\<close>

theory Subtyping imports reference_isabelle_output_wasm2 begin

(*This might be auto-generated*)
definition instr_subtyping :: "[functype, functype] \<Rightarrow> bool" ("_ '<ti: _" 60) where
  "instr_subtyping tf1 tf2  \<equiv>
(case (tf1, tf2) of
 (mk_functype (mk_list dom1) (mk_list ran1), mk_functype (mk_list dom2) (mk_list ran2)) \<Rightarrow> \<exists> ts ts' tf1_dom_sub tf1_ran_sub.
    dom2 = ts@tf1_dom_sub
  \<and> ran2 = ts'@tf1_ran_sub
  \<and> Resulttype_sub (mk_list ts) (mk_list ts')
  \<and> Resulttype_sub (mk_list tf1_dom_sub)  (mk_list dom1)
  \<and> Resulttype_sub (mk_list ran1) (mk_list tf1_ran_sub)
)"

end