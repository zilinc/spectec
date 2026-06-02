theory Properties_Aux
	imports Main reference_isabelle_output_wasm2 Subtyping
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

end