section \<open>Subtyping\<close>

theory Subtyping imports reference_isabelle_output_wasm2 begin

(*
this is 7187 Valtype_sub:

definition t_subtyping :: "[valtype, valtype] \<Rightarrow> bool" ("_ '<t: _" 60) where
  "t_subtyping t1 t2 = (t1 = BOT \<or> t1 = t2)"
*)

definition t_list_subtyping :: "[resulttype, resulttype] \<Rightarrow> bool" ("_ '<ts: _" 60) where
  "t_list_subtyping t1 t2 =
    (case (t1, t2) of
      (mk_list t1s, mk_list t2s) \<Rightarrow> list_all2 Valtype_sub t1s t2s)"

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

lemma Resulttype_sub_t_list_subtyping:
  "Resulttype_sub rt1 rt2 \<longleftrightarrow> t_list_subtyping rt1 rt2"
  apply auto
  subgoal
    apply (induction rule: Resulttype_sub.induct)
    using t_list_subtyping_def by auto
  subgoal
    unfolding t_list_subtyping_def
    apply (auto split: prod.splits)
    by (metis list_all2_lengthD mk_Resulttype_sub res_list.case res_list.exhaust)
  done

lemma Resulttype_sub_empty:
  "Resulttype_sub (mk_list []) (mk_list [])"
  by (auto simp add: Resulttype_sub.simps)

lemma instr_subtyping_sub_rule:
  assumes
    "Resulttype_sub ts1' ts1"
    "Resulttype_sub ts2 ts2'"
  shows
    "(mk_functype ts1 ts2) <ti: (mk_functype ts1' ts2')"
  using assms Resulttype_sub_t_list_subtyping unfolding instr_subtyping_def
  apply (auto split: res_list.splits)
  sorry

lemma instr_subtyping_frame_rule:
    "(mk_functype (mk_list ts1) (mk_list ts2)) <ti: (mk_functype (mk_list (ts@ts1)) (mk_list (ts@ts2)))"
  using assms Resulttype_sub_t_list_subtyping unfolding instr_subtyping_def
  apply (auto split: res_list.splits)
  sorry


lemma instr_subtyping_trans:
  assumes
    "tf1 <ti: tf2"
    "tf2 <ti: tf3"
  shows
    "tf1 <ti: tf3"
  sorry





end