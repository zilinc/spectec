theory Properties_Aux
	imports Main reference_isabelle_output_wasm2 Subtyping Subtyping_Properties
begin

lemma b_e_type_empty1[dest]:
  assumes "Instrs_ok C [] ft"
          "ft = (mk_functype (mk_list ts) (mk_list ts'))"
  shows   "instr_subtyping (mk_functype (mk_list []) (mk_list [])) (mk_functype (mk_list ts) (mk_list ts'))"
  using assms
  apply (induction "[] :: (instr list)" "ft" arbitrary: ts ts' rule: Instr_ok_Instrs_ok.inducts(2))
                      apply auto
  subgoal
    unfolding instr_subtyping_def
    using Resulttype_sub_empty
    by (auto split: res_list.splits)
  subgoal for C t_1_lst t_2_lst t'_2_lst ts
    using instr_subtyping_trans instr_subtyping_sub_rule
    by auto
  subgoal
    using instr_subtyping_trans instr_subtyping_frame_rule
    by auto
  done

lemma instr_inversion_helper:
  assumes "Instrs_ok C [e] ft"
  shows "\<exists> ft_principal. (Instr_ok C e ft_principal) \<and> (ft_principal <ti: ft)"
  using assms
proof (induction C "[e]" "ft" arbitrary:  rule: Instr_ok_Instrs_ok.inducts(2)[where ?P1.0 = "\<lambda> C e ft. \<exists> ft_principal. Instr_ok C e ft_principal  \<and> ft_principal <ti: ft"])
  case (block t_2_lst C bt t_1_lst append_context instr_lst)
  then show ?case
    by (metis Instr_ok_Instrs_ok.block instr_subtyping_refl)
next
  case (loop t_1_lst C bt t_2_lst append_context instr_lst)
  then show ?case
    by (metis Instr_ok_Instrs_ok.loop instr_subtyping_refl)
next
  case (res_if t_2_lst C bt t_1_lst append_context instr_1_lst instr_2_lst)
  then show ?case
    by (metis Instr_ok_Instrs_ok.res_if instr_subtyping_refl)
next
  case (br_table C l_lst t_lst l' t_1_lst t_2_lst)
  then show ?case
    by (metis Instr_ok_Instrs_ok.br_table instr_subtyping_refl)
next
  case (vstore mt C v_memarg)
  then show ?case
    using Instr_ok_Instrs_ok.vstore[OF vstore] instr_subtyping_refl
    by auto
next
  case (vstore_lane mt C v_memarg v_n v_laneidx)
  then show ?case
    using Instr_ok_Instrs_ok.vstore_lane[OF vstore_lane] instr_subtyping_refl
    by auto
next
  case (seq C instr_1 t_1_lst t_2_lst instr_2_lst t_3_lst)
  then have "instr_2_lst = []" "instr_1 = e" by auto
  then have "(mk_functype (mk_list []) (mk_list [])) <ti: (mk_functype (mk_list t_2_lst) (mk_list t_3_lst))"
    using seq.hyps(3) by blast
  then show ?case
    using \<open>instr_1 = e\<close> functype_weakening seq.hyps(1)
      by blast
next
  case (sub C t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case
    by (metis instr_subtyping_sub_rule instr_subtyping_trans)
next
  case (Instrs_ok__frame C t_1_lst t_2_lst t_lst)
  then show ?case
    by (metis instr_subtyping_frame_rule instr_subtyping_trans)
qed (metis Instr_ok_Instrs_ok.intros instr_subtyping_refl)+

lemma instr_inversion:
  assumes "Instrs_ok C [e] ft"
  shows
    inv_nop: "e = instr_subcase_0 NOP \<Longrightarrow>(mk_functype (mk_list []) (mk_list [])) <ti: ft" and
    inv_unreachable: "e = instr_subcase_0 UNREACHABLE \<Longrightarrow> True" and
    inv_drop: "e = instr_subcase_0 DROP \<Longrightarrow> (\<exists> t. ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_select_expl: "e = instr_subcase_0 (SELECT (Some [t])) \<Longrightarrow> ((mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: ft)" and
    inv_select_impl: "e = instr_subcase_0 (SELECT (None)) \<Longrightarrow> (\<exists> t v_numtype v_vectype t'. (Valtype_sub t t') \<and> ((t' = (valtype_numtype v_numtype)) \<or> (t' = (valtype_vectype v_vectype))) \<and> ((mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: ft))" and
    (*TODO: this should break once a fix for append_res_context is implemented *)
    inv_block: "e = (instr_subcase_7 (BLOCK bt instr_lst)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst append_context.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<and>
      (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
      ((Instrs_ok (append_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<and>
      ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))"
  using instr_inversion_helper[OF assms]
  apply auto
  by (cases rule: Instr_ok.cases, auto)+

lemma inversion_nop:
  assumes "Instrs_ok C [e] ft"
    "e = (instr_subcase_0 NOP)"
  shows "(mk_functype (mk_list []) (mk_list []) <ti: ft)"
  using inv_nop assms by auto

lemma inversion_drop:
  assumes "Instrs_ok C [e] ft"
    "e = (instr_subcase_0 DROP)"
  shows "\<exists> t. (mk_functype (mk_list [t]) (mk_list []) <ti: ft)"
  using instr_inversion_helper[OF assms(1)] assms(2)
  apply auto
    apply(cases rule: Instr_ok.cases)
  by auto

lemma b_e_type_cnum:
  assumes "Instrs_ok C [e] ft"
          "e = instr_subcase_1 (res_CONST v_numtype var_0)"
          "ft = (mk_functype (mk_list ts) (mk_list ts'))"
  shows   "instr_subtyping (mk_functype (mk_list []) (mk_list [(valtype_numtype v_numtype)])) (mk_functype (mk_list ts) (mk_list ts'))"
  using instr_inversion_helper[OF assms(1)] assms(2,3)
  apply auto
    apply(cases rule: Instr_ok.cases)
  by auto

end