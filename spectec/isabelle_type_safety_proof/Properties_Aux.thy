theory Properties_Aux
	imports Main reference_isabelle_output_wasm2 Subtyping Subtyping_Properties
begin

lemma b_e_type_empty1:
  assumes "Instrs_ok C [] ft"
          "ft = (mk_functype (mk_list ts) (mk_list ts'))"
  shows   "(mk_functype (mk_list []) (mk_list [])) <ti: (mk_functype (mk_list ts) (mk_list ts'))"
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
  case (block C bt t_1_lst t_2_lst instr_lst)
  then show ?case
    by (metis Instr_ok_Instrs_ok.block instr_subtyping_refl)
next
  case (loop C bt t_1_lst t_2_lst instr_lst)
  then show ?case
    by (metis Instr_ok_Instrs_ok.loop instr_subtyping_refl)
next
  case (res_if C bt t_1_lst t_2_lst instr_1_lst instr_2_lst)
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
    using seq.hyps(3) b_e_type_empty1 by blast
  then show ?case
    using \<open>instr_1 = e\<close> func_sub_app_single seq.hyps(1)
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

lemma instr_inversion_1:
  assumes "Instrs_ok C [e] ft"
  shows
    inv_nop: "e = instr_subcase_0 NOP \<Longrightarrow> (mk_functype (mk_list []) (mk_list [])) <ti: ft" and
    inv_unreachable: "e = instr_subcase_0 UNREACHABLE \<Longrightarrow> True" and
    inv_drop: "e = instr_subcase_0 DROP \<Longrightarrow> (\<exists> t. ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_select_expl: "e = instr_subcase_0 (SELECT (Some [t])) \<Longrightarrow> ((mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: ft)" and
    inv_select_impl: "e = instr_subcase_0 (SELECT (None)) \<Longrightarrow> (\<exists> t v_numtype v_vectype t'. (Valtype_sub t t') \<and> ((t' = (valtype_numtype v_numtype)) \<or> (t' = (valtype_vectype v_vectype))) \<and> ((mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: ft))" and
    inv_block: "e = (instr_subcase_7 (BLOCK bt instr_lst)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<and>
      (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
      ((Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<and>
      ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))" and
    inv_loop: "e =  (instr_subcase_7 (LOOP bt instr_lst)) \<Longrightarrow>
	    (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None \<rparr>) \<and>
		  (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  True)" and
    inv_res_if: "e = (instr_subcase_7 (IFELSE bt instr_1_lst instr_2_lst)) \<Longrightarrow>
		  (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<and>
		  (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_2_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  ((mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst)) <ti: ft))" and
	  inv_br: "e = (instr_subcase_0 (BR l)) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst t_2_lst.
		  ((proj_uN_0 l) < (length (LABELS C))) \<and>
		  ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<and>
		  ((mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst)) <ti: ft))" and
    inv_br_if: "e = (instr_subcase_0 (BR_IF l)) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst.
		  ((proj_uN_0 l) < (length (LABELS C))) \<and>
		  ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<and>
		  ((mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_lst)) <ti: ft))" and
    inv_br_table:  "e = (instr_subcase_0 (BR_TABLE l_lst l')) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst t_2_lst.
      (list_all (\<lambda> (l :: labelidx). ((proj_uN_0 l) < (length (LABELS C)))) l_lst) \<and>
		  (list_all (\<lambda> (l :: labelidx). (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l)))) l_lst) \<and>
		  ((proj_uN_0 l') < (length (LABELS C))) \<and>
		  (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l'))) \<and>
      ((mk_functype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) (mk_list t_2_lst)) <ti: ft))" and
    inv_call: "e = (instr_subcase_0 (CALL x)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
		  ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
		  (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))" and
    inv_call_indirect: "e = (instr_subcase_0 (CALL_INDIRECT x y)) \<Longrightarrow>
      (\<exists> lim t_1_lst t_2_lst.
		  ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim FUNCREF)) \<and>
		  ((proj_uN_0 y) < (length (context_TYPES C))) \<and>
		  (((context_TYPES C) ! (proj_uN_0 y)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (wf_tabletype (mk_tabletype lim FUNCREF)) \<and>
      ((mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst)) <ti: ft))" and
    inv_return: "e = (instr_subcase_1 RETURN) \<Longrightarrow>
      (\<exists> t_lst t_1_lst t_2_lst.
      ((context_RETURN C) = (Some (mk_list t_lst))) \<and>
		  ((mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst)) <ti: ft))" and
    inv_const: "e = (instr_subcase_1 (res_CONST nt c_nt)) \<Longrightarrow> (mk_functype (mk_list []) (mk_list [(valtype_numtype nt)])) <ti: ft" and
    inv_unop: "e = (instr_subcase_1 (UNOP nt unop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [(valtype_numtype nt)])) <ti: ft" and
    inv_binop: "e = (instr_subcase_1 (BINOP nt binop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [(valtype_numtype nt)])) <ti: ft" and
    inv_testop: "e = (instr_subcase_1 (TESTOP nt testop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [valtype_I32])) <ti: ft" and
    inv_relop: "e = (instr_subcase_1 (RELOP nt relop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [valtype_I32])) <ti: ft" and
    inv_cvtop_convert: "e = (instr_subcase_1 (CVTOP nt_1 nt_2 v_cvtop)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: ft" and
    inv_ref_null: "e = (instr_subcase_4 (REF_NULL rt)) \<Longrightarrow> (mk_functype (mk_list []) (mk_list [(valtype_reftype rt)])) <ti: ft" and
    inv_ref_is_null: "e = (instr_subcase_4 REF_IS_NULL) \<Longrightarrow> (\<exists> rt. (mk_functype (mk_list [(valtype_reftype rt)]) (mk_list [valtype_I32])) <ti: ft)" and
    inv_vconst: "e = (instr_subcase_1 (VCONST V128 c)) \<Longrightarrow> (mk_functype (mk_list []) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok_vvunop: "e = (instr_subcase_2 (VVUNOP V128 v_vvunop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vvbinop: "e = (instr_subcase_2 (VVBINOP V128 v_vvbinop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vvternop: "e = (instr_subcase_2 (VVTERNOP V128 v_vvternop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vvtestop: "e = (instr_subcase_2 (VVTESTOP V128 v_vvtestop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: ft" and
    inv_vunop: "e = (instr_subcase_2 (VUNOP sh vunop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vbinop: "e = (instr_subcase_2 (VBINOP sh vbinop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vtestop: "e = (instr_subcase_2 (VTESTOP sh vtestop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: ft" and
    inv_vrelop: "e = (instr_subcase_2 (VRELOP sh vrelop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vshiftop: "e = (instr_subcase_2 (VSHIFTOP ish vshiftop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vbitmask: "e = (instr_subcase_3 (VBITMASK ish)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: ft" and
    inv_vswizzle: "e = (instr_subcase_3 (VSWIZZLE ish)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vshuffle: "e = (instr_subcase_3 (VSHUFFLE ish i_lst)) \<Longrightarrow>
      (\<exists> i.
      (list_all (\<lambda> (i :: laneidx). ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (shape_ishape ish)))))) i_lst) \<and>
		  ((wf_dim (fun_dim (shape_ishape ish)))) \<and>
      ((mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft))" and
    inv_vsplat: "e = (instr_subcase_3 (VSPLAT sh)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype (shunpack sh))]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vextract_lane: "e = (instr_subcase_3 (VEXTRACT_LANE sh sx_opt i)) \<Longrightarrow>
      ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<and>
		  (wf_dim (fun_dim sh)) \<and>
      ((mk_functype (mk_list [valtype_V128]) (mk_list [(valtype_numtype (shunpack sh))])) <ti: ft)" and
    inv_vreplace_lane: "e = (instr_subcase_3 (VREPLACE_LANE sh i)) \<Longrightarrow>
      ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<and>
		  (wf_dim (fun_dim sh)) \<and>
      ((mk_functype (mk_list [valtype_V128, (valtype_numtype (shunpack sh))]) (mk_list [valtype_V128])) <ti: ft)" and
    inv_vextunop: "e = (instr_subcase_3 (VEXTUNOP sh_1 sh_2 vextunop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) <ti: ft)" and
    inv_vextbinop: "e = (instr_subcase_3 (VEXTBINOP sh_1 sh_2 vextbinop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) <ti: ft)" and
    inv_vnarrow: "e = (instr_subcase_3 (VNARROW sh_1 sh_2 v_sx)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vcvtop: "e = (instr_subcase_4 (VCVTOP sh sh2 v_vcvtop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_local_get: "e = (instr_subcase_4 (LOCAL_GET x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_functype (mk_list []) (mk_list [t])) <ti: ft))" and
    inv_local_set: "e = (instr_subcase_4 (LOCAL_SET x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_local_tee: "e = (instr_subcase_4 (LOCAL_TEE x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_functype (mk_list [t]) (mk_list [t])) <ti: ft))" and
    inv_global_get: "e = (instr_subcase_4 (GLOBAL_GET x)) \<Longrightarrow>
      (\<exists> v_mut t.
      ((proj_uN_0 x) < (length (context_GLOBALS C))) \<and>
		  (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype v_mut t)) \<and>
      ((mk_functype (mk_list []) (mk_list [t])) <ti: ft))" and
    inv_global_set: "e = (instr_subcase_4 (GLOBAL_SET x)) \<Longrightarrow>
      (\<exists> MUT t.
      ((proj_uN_0 x) < (length (context_GLOBALS C))) \<and>
		  (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT) t)) \<and>
      ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_table_get: "e = (instr_subcase_5 (TABLE_GET x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_reftype rt)])) <ti: ft))" and
    inv_table_set: "e =  (instr_subcase_5 (TABLE_SET x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [valtype_I32, (valtype_reftype rt)]) (mk_list [])) <ti: ft))" and
    inv_table_size: "e = (instr_subcase_5 (TABLE_SIZE x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list []) (mk_list [valtype_I32])) <ti: ft))" and
    inv_table_grow: "e = (instr_subcase_5 (TABLE_GROW x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [(valtype_reftype rt), valtype_I32]) (mk_list [valtype_I32])) <ti: ft))" and
    inv_table_fill: "e = (instr_subcase_5 (TABLE_FILL x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [valtype_I32, (valtype_reftype rt), valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_table_copy: "e = (instr_subcase_5 (TABLE_COPY x_1 x_2)) \<Longrightarrow>
      (\<exists> lim_1 rt lim_2.
      ((proj_uN_0 x_1) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim_1 rt)) \<and>
		  ((proj_uN_0 x_2) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_2)) = (mk_tabletype lim_2 rt)) \<and>
		  (wf_tabletype (mk_tabletype lim_1 rt)) \<and>
		  (wf_tabletype (mk_tabletype lim_2 rt)) \<and>
		  ((mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: ft))"


  using instr_inversion_helper[OF assms]
  apply auto
  by (cases rule: Instr_ok.cases, auto)+

lemma instr_inversion_2:
  assumes "Instrs_ok C [e] ft"
  shows
    inv_cvtop_reinterpret: "e = (instr_subcase_1 (CVTOP nt_1 nt_2 REINTERPRET)) \<Longrightarrow>
      ((size (valtype_numtype nt_1)) \<noteq> None) \<and>
      ((size (valtype_numtype nt_2)) \<noteq> None) \<and>
      ((the ((size (valtype_numtype nt_1)))) = (the ((size (valtype_numtype nt_2))))) \<and>
      ((mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: ft)" and
    inv_ref_func: "e = (instr_subcase_4 (REF_FUNC x)) \<Longrightarrow>
      ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
      (((context_FUNCS C) ! (proj_uN_0 x)) = ft) \<and>
      ((mk_functype (mk_list []) (mk_list [valtype_FUNCREF])) <ti: ft)"
  using instr_inversion_helper[OF assms]
  apply auto
  apply (cases rule: Instr_ok.cases, auto)
sorry

lemma all_wf:
  assumes "Instrs_ok C [e] ft"
  shows   "(wf_context C)"
		      "(wf_instr e)"
  sorry


(*Testing the inversion lemma*)
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

end