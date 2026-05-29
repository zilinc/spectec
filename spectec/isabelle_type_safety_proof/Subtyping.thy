section \<open>Subtyping\<close>

theory Subtyping imports reference_isabelle_output_wasm2 begin

definition t_subtyping :: "[valtype, valtype] \<Rightarrow> bool" ("_ '<t: _" 60) where
  "t_subtyping t1 t2 = (t1 = BOT \<or> t1 = t2)"

definition t_list_subtyping :: "[resulttype, resulttype] \<Rightarrow> bool" ("_ '<ts: _" 60) where
  "t_list_subtyping t1 t2 =
    (case (t1, t2) of
      (mk_list t1s, mk_list t2s) \<Rightarrow> list_all2 t_subtyping t1s t2s)"

definition instr_subtyping :: "[functype, functype] \<Rightarrow> bool" ("_ '<ti: _" 60) where
  "instr_subtyping tf1 tf2  \<equiv> 
(case (tf1, tf2) of
 (mk_functype (mk_list dom1) (mk_list ran1), mk_functype (mk_list dom2) (mk_list ran2)) \<Rightarrow> \<exists> ts ts' tf1_dom_sub tf1_ran_sub.
    dom2 = ts@tf1_dom_sub
  \<and> ran2 = ts'@tf1_ran_sub
  \<and> t_list_subtyping (mk_list ts) (mk_list ts')
  \<and> t_list_subtyping (mk_list tf1_dom_sub)  (mk_list dom1)
  \<and> t_list_subtyping (mk_list ran1) (mk_list tf1_ran_sub)
)"

end