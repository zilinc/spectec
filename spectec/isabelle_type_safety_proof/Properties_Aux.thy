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

lemma main_inversion_lemma:
  assumes "Instrs_ok C [e] ft"
  shows "\<exists> ft_principal. (Instr_ok C e ft_principal) \<and> (ft_principal <ti: ft)"
  using assms
  apply (induction "[e]" "ft" arbitrary:  rule: Instr_ok_Instrs_ok.inducts(2)[where ?P1.0 = "\<lambda> _ _ _. True"])
                      apply auto
  subgoal for C t_1_lst t_2_lst t_3_lst
    sorry
  subgoal
    by (metis instr_subtyping_sub_rule instr_subtyping_trans)
  subgoal
    by (metis instr_subtyping_trans instr_subtyping_frame_rule)
  done

lemma inversion_nop:
  assumes "Instrs_ok C [e] ft"
    "e = (instr_subcase_0 NOP)"
  shows "(mk_functype (mk_list []) (mk_list []) <ti: ft)"
  using main_inversion_lemma[OF assms(1)] assms(2)
  apply auto
    apply(cases rule: Instr_ok.cases)
  by auto

lemma inversion_drop:
  assumes "Instrs_ok C [e] ft"
    "e = (instr_subcase_0 DROP)"
  shows "\<exists> t. (mk_functype (mk_list [t]) (mk_list []) <ti: ft)"
  using main_inversion_lemma[OF assms(1)] assms(2)
  apply auto
    apply(cases rule: Instr_ok.cases)
  by auto

lemma b_e_type_cnum:
  assumes "Instrs_ok C [e] ft"
          "e = instr_subcase_1 (res_CONST v_numtype var_0)"
          "ft = (mk_functype (mk_list ts) (mk_list ts'))"
  shows   "instr_subtyping (mk_functype (mk_list []) (mk_list [(valtype_numtype v_numtype)])) (mk_functype (mk_list ts) (mk_list ts'))"
  using main_inversion_lemma[OF assms(1)] assms(2,3)
  apply auto
    apply(cases rule: Instr_ok.cases)
  by auto

end