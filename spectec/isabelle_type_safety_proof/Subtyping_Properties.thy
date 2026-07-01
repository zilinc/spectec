section \<open>Subtyping Properties\<close>

theory Subtyping_Properties imports Subtyping isabelle_reference_output_wasm2 begin

lemma Valtype_sub_refl:
  "Valtype_sub t t"
  by (metis Valtype_sub.refl)

lemma Resulttype_sub_refl:
  "Resulttype_sub ts ts"
  apply (auto simp add: Resulttype_sub.simps)
  by (metis Valtype_sub_refl list.rel_refl res_list.exhaust)

lemma instr_subtyping_refl:
  "tf <ti: tf"
  unfolding instr_subtyping_def using Resulttype_sub_refl
  apply (auto split: functype.splits prod.splits res_list.splits)
  by blast

(*for Seq*)
lemma Resulttype_sub_empty:
  "Resulttype_sub (mk_list []) (mk_list [])"
  by (auto simp add: Resulttype_sub.simps)

lemma Resulttype_sub_append:
assumes "Resulttype_sub (mk_list ts1') (mk_list ts)"
        "Resulttype_sub (mk_list ts2') (mk_list tf1_ran_sub)"
shows   "Resulttype_sub (mk_list (ts1' @ ts2')) (mk_list (ts @ tf1_ran_sub))"
by (cases rule: Resulttype_sub.cases[OF assms(1)];
    cases rule: Resulttype_sub.cases[OF assms(2)];
    auto intro: Resulttype_sub.mk_Resulttype_sub
                 list_all2_appendI)

lemma Resulttype_sub_split_left:
  assumes "Resulttype_sub (mk_list ts) (mk_list (ts1@ts2))"
  shows "\<exists> ts1' ts2'. Resulttype_sub (mk_list ts1') (mk_list ts1) \<and> Resulttype_sub (mk_list ts2') (mk_list ts2) \<and> ts = ts1'@ts2'"
  using assms
  apply (auto simp add: Resulttype_sub.simps)
  by (metis list_all2_append2)

lemma instr_subtyping_sub_rule:
  assumes
    "Resulttype_sub ts1' ts1"
    "Resulttype_sub ts2 ts2'"
  shows
    "(mk_functype ts1 ts2) <ti: (mk_functype ts1' ts2')"
proof -
  obtain ts1_l ts2_l ts1'_l ts2'_l where defs:
    "ts1 = mk_list ts1_l"
    "ts2 = mk_list ts2_l"
    "ts1' = mk_list ts1'_l"
    "ts2' = mk_list ts2'_l"
    by (metis proj_list_0.cases)

  have "ts1'_l = [] @ ts1'_l \<and>
        ts2'_l = [] @ ts2'_l \<and>
        Resulttype_sub (mk_list []) (mk_list []) \<and>
        Resulttype_sub (mk_list ts1'_l) (mk_list ts1_l) \<and>
        Resulttype_sub (mk_list ts2_l) (mk_list ts2'_l)"
    using assms defs Resulttype_sub_empty
    by auto

  then show ?thesis using defs unfolding instr_subtyping_def
    by fastforce
qed

lemma func_sub_app_single_l:
  assumes "(mk_functype (mk_list []) (mk_list [])) <ti: (mk_functype (mk_list ts2) (mk_list ts3))"
  shows "(mk_functype (mk_list ts1) (mk_list ts2)) <ti: (mk_functype (mk_list ts1) (mk_list ts3))"
proof -
  have "Resulttype_sub (mk_list ts2) (mk_list ts3)"
    using assms instr_subtyping_def Resulttype_sub.simps Resulttype_sub_split_left Resulttype_sub_refl Resulttype_sub_append
      by simp
  then show ?thesis
    using Resulttype_sub_refl instr_subtyping_sub_rule
      by force
qed


lemma func_sub_app_single_r:
  assumes "(mk_functype (mk_list []) (mk_list [])) <ti: (mk_functype (mk_list ts1) (mk_list ts2))"
  shows "(mk_functype (mk_list ts2) (mk_list ts3)) <ti: (mk_functype (mk_list ts1) (mk_list ts3))"
proof -
  have "Resulttype_sub (mk_list ts1) (mk_list ts2)"
    using assms instr_subtyping_def Resulttype_sub.simps Resulttype_sub_split_left Resulttype_sub_refl Resulttype_sub_append
      by simp
  then show ?thesis
    using Resulttype_sub_refl instr_subtyping_sub_rule
      by force
qed


(*for sub*)
lemma Resulttype_sub_split_right:
  assumes "Resulttype_sub (mk_list (ts1@ts2)) (mk_list ts)"
  shows "\<exists> ts1' ts2'. Resulttype_sub (mk_list ts1) (mk_list ts1') \<and> Resulttype_sub (mk_list ts2) (mk_list ts2') \<and> ts = ts1'@ts2'"
  using assms
  apply (auto simp add: Resulttype_sub.simps)
  by (metis list_all2_append1)

lemma Valtype_sub_trans:
  assumes
    "Valtype_sub t1 t2"
    "Valtype_sub t2 t3"
  shows
    "Valtype_sub t1 t3"
  using assms Valtype_sub.simps
  by auto

lemma Resulttype_sub_trans:
  assumes
    "Resulttype_sub ts1 ts2"
    "Resulttype_sub ts2 ts3"
  shows
    "Resulttype_sub ts1 ts3"
  using Valtype_sub_trans assms
  apply (auto simp add:  Resulttype_sub.simps)
  using list_all2_trans by blast

lemma instr_subtyping_trans:
  assumes
    "tf1 <ti: tf2"
    "tf2 <ti: tf3"
  shows
    "tf1 <ti: tf3"
proof - 
  obtain tf1_d tf1_r tf2_d tf2_r tf3_d tf3_r where defs:
    "tf1 = mk_functype (mk_list tf1_d) (mk_list tf1_r)"
    "tf2 = mk_functype (mk_list tf2_d) (mk_list tf2_r)"
    "tf3 = mk_functype (mk_list tf3_d) (mk_list tf3_r)"
    by (metis functype.exhaust res_list.exhaust)

  obtain ts_12 ts'_12 tf1_dom_sub_12 tf1_ran_sub_12 where defs12:
    "tf2_d = ts_12 @ tf1_dom_sub_12"
    "tf2_r = ts'_12 @ tf1_ran_sub_12"
    "Resulttype_sub (mk_list ts_12) (mk_list ts'_12)"
    "Resulttype_sub (mk_list tf1_dom_sub_12) (mk_list tf1_d)"
    "Resulttype_sub (mk_list tf1_r) (mk_list tf1_ran_sub_12)"
    using assms(1) defs unfolding instr_subtyping_def by auto

  obtain ts_23 ts'_23 tf1_dom_sub_23 tf1_ran_sub_23 where defs23:
    "tf3_d = ts_23 @ tf1_dom_sub_23"
    "tf3_r = ts'_23 @ tf1_ran_sub_23"
    "Resulttype_sub (mk_list ts_23) (mk_list ts'_23)"
    "Resulttype_sub (mk_list tf1_dom_sub_23) (mk_list tf2_d)"
    "Resulttype_sub (mk_list tf2_r) (mk_list tf1_ran_sub_23)"
    using assms(2) defs unfolding instr_subtyping_def by auto

  obtain tf1_ts_12 tf1_tf_dom_sub_12  where defs_split_12:
    "Resulttype_sub (mk_list tf1_ts_12) (mk_list ts_12)"
    "Resulttype_sub (mk_list tf1_tf_dom_sub_12) (mk_list tf1_dom_sub_12)"  
    "tf1_ts_12@tf1_tf_dom_sub_12 = tf1_dom_sub_23"
    using defs12(1) defs23(4)
    using Resulttype_sub_split_left by blast

  obtain tf1_ts'_12 tf1_tf_ran_sub_12 where  defs_split_23:
    "Resulttype_sub (mk_list ts'_12) (mk_list tf1_ts'_12)"
    "Resulttype_sub (mk_list tf1_ran_sub_12) (mk_list tf1_tf_ran_sub_12)"  
    "tf1_ran_sub_23 = tf1_ts'_12@tf1_tf_ran_sub_12"
    using defs12(2) defs23(5)
    using Resulttype_sub_split_right by blast

  let ?ts = "ts_23@tf1_ts_12"
  let ?ts' = "ts'_23@tf1_ts'_12"
  let ?tf1_dom_sub = "tf1_tf_dom_sub_12"
  let ?tf1_ran_sub = "tf1_tf_ran_sub_12"
  have a: "tf3_d = ?ts @ ?tf1_dom_sub"
    by (simp add: defs_split_12(3) defs23(1))
  have b: "Resulttype_sub (mk_list ?tf1_dom_sub) (mk_list tf1_d)"
    using defs12(4) defs_split_12(2) Resulttype_sub_trans by blast
  have c: "Resulttype_sub (mk_list ?ts) (mk_list ?ts')"
    using Resulttype_sub_trans
      defs12(3) defs23(3)
      list_all2_appendI[of Valtype_sub ts_23 ts'_23 tf1_ts_12 tf1_ts'_12]
    unfolding Resulttype_sub.simps 
    apply simp
    by (metis res_list.inject Resulttype_sub.simps defs_split_12(1) defs12(3) defs_split_23(1) Resulttype_sub_trans)
  have d: "tf3_r = ?ts' @ ?tf1_ran_sub" using defs23(2) defs_split_23(3)
    by auto
  have e: "Resulttype_sub (mk_list tf1_r) (mk_list ?tf1_ran_sub)"
    using defs12(5) defs_split_23(2) Resulttype_sub_trans by blast
  show ?thesis
    using a b c d e defs unfolding instr_subtyping_def
    apply (auto split: functype.splits)
    by (metis append_assoc)
qed

(*For frame*)
lemma instr_subtyping_frame_rule:
    "(mk_functype (mk_list ts1) (mk_list ts2)) <ti: (mk_functype (mk_list (ts@ts1)) (mk_list (ts@ts2)))"
proof -
  have "ts @ ts1 = ts @ ts1 \<and>
        ts @ ts2 = ts @ ts2 \<and>
        Resulttype_sub (mk_list ts) (mk_list ts) \<and>
        Resulttype_sub (mk_list ts1) (mk_list ts1) \<and>
        Resulttype_sub (mk_list ts2) (mk_list ts2)"
    by (metis Resulttype_sub_refl)

  then show ?thesis
    unfolding instr_subtyping_def
    by fastforce
qed

definition t_list_subtyping :: "[resulttype, resulttype] \<Rightarrow> bool" ("_ '<ts: _" 60) where
  "t_list_subtyping t1 t2 =
    (case (t1, t2) of
      (mk_list t1s, mk_list t2s) \<Rightarrow> list_all2 Valtype_sub t1s t2s)"

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

end