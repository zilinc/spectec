theory Properties_Aux
	imports Main isabelle_reference_output_wasm2 Subtyping Subtyping_Properties
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
  subgoal for C t_1_lst t_2_lst t'_2_lst
    using instr_subtyping_trans instr_subtyping_sub_rule func_sub_app_single_l
    by blast
  subgoal
    using instr_subtyping_trans instr_subtyping_frame_rule instr_subtyping_sub_rule
    by blast
  subgoal
    using instr_subtyping_frame_rule instr_subtyping_trans
    by blast
  done

lemma instr_inversion_helper:
  assumes "Instrs_ok C [e] ft"
  shows "\<exists> ft_principal. (Instr_ok C e ft_principal) \<and> (ft_principal <ti: ft)"
  using assms
proof (induction C "[e]" "ft" arbitrary:  
       rule: Instr_ok_Instrs_ok.inducts(2)[where ?P1.0 = 
          "\<lambda> C e ft. \<exists> ft_principal. Instr_ok C e ft_principal \<and> ft_principal <ti: ft"])
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
  then show ?case 
  proof (cases instr_1)
    case Nil
    then have e2: "instr_2_lst = [e]" using seq by simp
    then have "(mk_functype (mk_list []) (mk_list [])) <ti: 
               (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))" 
      using seq.hyps b_e_type_empty1 by blast
    then show ?thesis 
      using  \<open>instr_2_lst = [e]\<close> func_sub_app_single_r 
              instr_subtyping_trans seq.hyps(3,4) by blast
  next
    case (Cons a list)
    then have "instr_2_lst = []" "instr_1 = [e]" 
      using seq.hyps(8) by auto
      then have "(mk_functype (mk_list []) (mk_list [])) <ti: 
                  (mk_functype (mk_list t_2_lst) (mk_list t_3_lst))"
    using seq.hyps(3) b_e_type_empty1 by blast
  then show ?thesis
    using \<open>instr_1 = [e]\<close> func_sub_app_single_l seq.hyps(1) 
  using instr_subtyping_trans seq.hyps(2) by blast
qed
next
  case (sub C t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case
    by (metis instr_subtyping_sub_rule instr_subtyping_trans)
next
  case (Instrs_ok__frame C t_1_lst t_2_lst t_lst)
  then show ?case
    by (metis instr_subtyping_frame_rule instr_subtyping_trans)
(* This next line takes a while *)
qed (metis Instr_ok_Instrs_ok.intros instr_subtyping_refl)+

termination numtype_Inn
  by lexicographic_order

lemma instr_ok_inv_store_pack:
  assumes "Instrs_ok C [e] ft"
          "e = (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg))"
  shows
       "(\<exists> mt.
        (0 < (length (context_MEMS C))) \<and>
        (((context_MEMS C) ! 0) = mt) \<and>
        (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat))) \<and>
        (wf_memtype mt) \<and>
        ((mk_functype (mk_list [valtype_I32, (valtype_Inn v_Inn)]) (mk_list [])) <ti: ft))"
proof -
  obtain pt where
     "Instr_ok C (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) pt" and
		 "(pt <ti: ft)"
  by (metis assms(1) assms(2) instr_inversion_helper)
  then show ?thesis using assms(1)
    proof (induction "C" "(instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg))" "pt" arbitrary: v_Inn rule: Instr_ok_Instrs_ok.inducts(1))
      case (store_pack C mt v_Innsa)
      have "v_Inn = v_Innsa" 
        by (metis store_pack.hyps(7) numtype_Inn.elims numtype.distinct(1))
      then have "mk_functype (mk_list [valtype_I32, valtype_Inn v_Inn]) (mk_list []) <ti: ft" using store_pack(7,8)
        by simp
      then show ?case
        using store_pack.hyps(1,2,3,5) by auto
    qed
qed

lemma instr_ok_inv_ref_func:
  assumes "Instrs_ok C [e] ft"
          "e = (instr_sc4 (REF_FUNC x))"
  shows"(\<exists> fta.
        ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
        (((context_FUNCS C) ! (proj_uN_0 x)) = fta) \<and>
        ((mk_functype (mk_list []) (mk_list [valtype_FUNCREF])) <ti: ft))"
proof -
obtain pt where
  "Instr_ok C (instr_sc4 (REF_FUNC x)) pt" and
  "pt <ti: ft" by (metis assms(2) assms(1) instr_inversion_helper)
  then show ?thesis
    by (cases rule: Instr_ok.cases, auto)
qed

termination isabelle_reference_output_wasm2.size
  by lexicographic_order

termination isabelle_reference_output_wasm2.valtype_numtype
  by lexicographic_order

lemma instr_ok_inv_cvtop_reinterpret:
  assumes "Instrs_ok C [e] ft"
          "e = (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET))"
  shows "
      ((size (valtype_numtype nt_1)) \<noteq> None) \<and>
      ((size (valtype_numtype nt_2)) \<noteq> None) \<and>
      ((the ((size (valtype_numtype nt_1)))) = (the ((size (valtype_numtype nt_2))))) \<and>
      ((mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: ft)"
proof -
obtain pt where
  a: "Instr_ok C (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET)) pt" and
  b: "pt <ti: ft" by (metis assms(2) assms(1) instr_inversion_helper)
  show ?thesis using a b
  apply (induction "C" "(instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET))" "pt" arbitrary: nt_1 nt_2 rule: Instr_ok_Instrs_ok.inducts(1))
  apply auto+
  subgoal for C nt_1 nt_2
    apply (induction nt_1) by simp+
  subgoal for C nt_1 nt_2
    apply (induction nt_2) by simp+
  subgoal for C nt_1 nt_2
    proof -
      have "nt_1 = nt_2" sorry
      then show ?thesis
        by simp
    qed
  sorry
qed

lemma instr_ok_inversion:
  assumes "Instrs_ok C [e] ft"
  shows
    inv_store_pack: "e = (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) \<Longrightarrow>
        (\<exists> mt.
        (0 < (length (context_MEMS C))) \<and>
        (((context_MEMS C) ! 0) = mt) \<and>
        (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat))) \<and>
        (wf_memtype mt) \<and>
        ((mk_functype (mk_list [valtype_I32, (valtype_Inn v_Inn)]) (mk_list [])) <ti: ft))" and
    inv_ref_func: "e = (instr_sc4 (REF_FUNC x)) \<Longrightarrow>
        (\<exists> fta.
        ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
        (((context_FUNCS C) ! (proj_uN_0 x)) = fta) \<and>
        ((mk_functype (mk_list []) (mk_list [valtype_FUNCREF])) <ti: ft))" and
    inv_cvtop_reinterpret: "e = (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET)) \<Longrightarrow>
        ((size (valtype_numtype nt_1)) \<noteq> None) \<and>
        ((size (valtype_numtype nt_2)) \<noteq> None) \<and>
        ((the ((size (valtype_numtype nt_1)))) = (the ((size (valtype_numtype nt_2))))) \<and>
        ((mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: ft)" and
    inv_nop: "e = instr_sc0 NOP \<Longrightarrow> (mk_functype (mk_list []) (mk_list [])) <ti: ft" and
    inv_unreachable: "e = instr_sc0 UNREACHABLE \<Longrightarrow> True" and
    inv_drop: "e = instr_sc0 DROP \<Longrightarrow> (\<exists> t. ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_select_expl: "e = instr_sc0 (SELECT (Some [t])) \<Longrightarrow> ((mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: ft)" and
    inv_select_impl: "e = instr_sc0 (SELECT (None)) \<Longrightarrow> (\<exists> t v_numtype v_vectype t'. (Valtype_sub t t') \<and> ((t' = (valtype_numtype v_numtype)) \<or> (t' = (valtype_vectype v_vectype))) \<and> ((mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: ft))" and
    inv_block: "e = (instr_sc7 (BLOCK bt instr_lst)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<and>
      (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
      ((Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<and>
      ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))" and
    inv_loop: "e =  (instr_sc7 (LOOP bt instr_lst)) \<Longrightarrow>
	    (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None \<rparr>) \<and>
		  (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_1_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  True)" and
    inv_res_if: "e = (instr_sc7 (IFELSE bt instr_1_lst instr_2_lst)) \<Longrightarrow>
		  (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<and>
		  (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_1_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_2_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  ((mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst)) <ti: ft))" and
	  inv_br: "e = (instr_sc0 (BR l)) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst t_2_lst.
		  ((proj_uN_0 l) < (length (LABELS C))) \<and>
		  ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<and>
		  ((mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst)) <ti: ft))" and
    inv_br_if: "e = (instr_sc0 (BR_IF l)) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst.
		  ((proj_uN_0 l) < (length (LABELS C))) \<and>
		  ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<and>
		  ((mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_lst)) <ti: ft))" and
    inv_br_table:  "e = (instr_sc0 (BR_TABLE l_lst l')) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst t_2_lst.
      (list_all (\<lambda> (l :: labelidx). ((proj_uN_0 l) < (length (LABELS C)))) l_lst) \<and>
		  (list_all (\<lambda> (l :: labelidx). (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l)))) l_lst) \<and>
		  ((proj_uN_0 l') < (length (LABELS C))) \<and>
		  (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l'))) \<and>
      ((mk_functype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) (mk_list t_2_lst)) <ti: ft))" and
    inv_call: "e = (instr_sc0 (CALL x)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
		  ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
		  (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))" and
    inv_call_indirect: "e = (instr_sc0 (CALL_INDIRECT x y)) \<Longrightarrow>
      (\<exists> lim t_1_lst t_2_lst.
		  ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim FUNCREF)) \<and>
		  ((proj_uN_0 y) < (length (context_TYPES C))) \<and>
		  (((context_TYPES C) ! (proj_uN_0 y)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (wf_tabletype (mk_tabletype lim FUNCREF)) \<and>
      ((mk_functype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst)) <ti: ft))" and
    inv_return: "e = (instr_sc1 RETURN) \<Longrightarrow>
      (\<exists> t_lst t_1_lst t_2_lst.
      ((context_RETURN C) = (Some (mk_list t_lst))) \<and>
		  ((mk_functype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst)) <ti: ft))" and
    inv_const: "e = (instr_sc1 (res_CONST nt c_nt)) \<Longrightarrow> (mk_functype (mk_list []) (mk_list [(valtype_numtype nt)])) <ti: ft" and
    inv_unop: "e = (instr_sc1 (UNOP nt unop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [(valtype_numtype nt)])) <ti: ft" and
    inv_binop: "e = (instr_sc1 (BINOP nt binop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [(valtype_numtype nt)])) <ti: ft" and
    inv_testop: "e = (instr_sc1 (TESTOP nt testop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt)]) (mk_list [valtype_I32])) <ti: ft" and
    inv_relop: "e = (instr_sc1 (RELOP nt relop_nt)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [valtype_I32])) <ti: ft" and
    inv_cvtop_convert: "e = (instr_sc1 (CVTOP nt_1 nt_2 v_cvtop)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: ft" and
    inv_ref_null: "e = (instr_sc4 (REF_NULL rt)) \<Longrightarrow> (mk_functype (mk_list []) (mk_list [(valtype_reftype rt)])) <ti: ft" and
    inv_ref_is_null: "e = (instr_sc4 REF_IS_NULL) \<Longrightarrow> (\<exists> rt. (mk_functype (mk_list [(valtype_reftype rt)]) (mk_list [valtype_I32])) <ti: ft)" and
    inv_vconst: "e = (instr_sc1 (VCONST V128 c)) \<Longrightarrow> (mk_functype (mk_list []) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok_vvunop: "e = (instr_sc2 (VVUNOP V128 v_vvunop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vvbinop: "e = (instr_sc2 (VVBINOP V128 v_vvbinop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vvternop: "e = (instr_sc2 (VVTERNOP V128 v_vvternop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vvtestop: "e = (instr_sc2 (VVTESTOP V128 v_vvtestop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: ft" and
    inv_vunop: "e = (instr_sc2 (VUNOP sh vunop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vbinop: "e = (instr_sc2 (VBINOP sh vbinop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vtestop: "e = (instr_sc2 (VTESTOP sh vtestop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: ft" and
    inv_vrelop: "e = (instr_sc2 (VRELOP sh vrelop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vshiftop: "e = (instr_sc2 (VSHIFTOP ish vshiftop_sh)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vbitmask: "e = (instr_sc3 (VBITMASK ish)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: ft" and
    inv_vswizzle: "e = (instr_sc3 (VSWIZZLE ish)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vshuffle: "e = (instr_sc3 (VSHUFFLE ish i_lst)) \<Longrightarrow>
      (\<exists> i.
      (list_all (\<lambda> (i :: laneidx). ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (shape_ishape ish)))))) i_lst) \<and>
		  ((wf_dim (fun_dim (shape_ishape ish)))) \<and>
      ((mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft))" and
    inv_vsplat: "e = (instr_sc3 (VSPLAT sh)) \<Longrightarrow> (mk_functype (mk_list [(valtype_numtype (shunpack sh))]) (mk_list [valtype_V128])) <ti: ft" and
    inv_vextract_lane: "e = (instr_sc3 (VEXTRACT_LANE sh sx_opt i)) \<Longrightarrow>
      ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<and>
		  (wf_dim (fun_dim sh)) \<and>
      ((mk_functype (mk_list [valtype_V128]) (mk_list [(valtype_numtype (shunpack sh))])) <ti: ft)" and
    inv_vreplace_lane: "e = (instr_sc3 (VREPLACE_LANE sh i)) \<Longrightarrow>
      ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<and>
		  (wf_dim (fun_dim sh)) \<and>
      ((mk_functype (mk_list [valtype_V128, (valtype_numtype (shunpack sh))]) (mk_list [valtype_V128])) <ti: ft)" and
    inv_vextunop: "e = (instr_sc3 (VEXTUNOP sh_1 sh_2 vextunop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128]) <ti: ft)" and
    inv_vextbinop: "e = (instr_sc3 (VEXTBINOP sh_1 sh_2 vextbinop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) <ti: ft)" and
    inv_vnarrow: "e = (instr_sc3 (VNARROW sh_1 sh_2 v_sx)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_Instr_ok__vcvtop: "e = (instr_sc4 (VCVTOP sh sh2 v_vcvtop)) \<Longrightarrow> (mk_functype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: ft" and
    inv_local_get: "e = (instr_sc4 (LOCAL_GET x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_functype (mk_list []) (mk_list [t])) <ti: ft))" and
    inv_local_set: "e = (instr_sc4 (LOCAL_SET x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_local_tee: "e = (instr_sc4 (LOCAL_TEE x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_functype (mk_list [t]) (mk_list [t])) <ti: ft))" and
    inv_global_get: "e = (instr_sc4 (GLOBAL_GET x)) \<Longrightarrow>
      (\<exists> v_mut t.
      ((proj_uN_0 x) < (length (context_GLOBALS C))) \<and>
		  (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype v_mut t)) \<and>
      ((mk_functype (mk_list []) (mk_list [t])) <ti: ft))" and
    inv_global_set: "e = (instr_sc4 (GLOBAL_SET x)) \<Longrightarrow>
      (\<exists> MUT t.
      ((proj_uN_0 x) < (length (context_GLOBALS C))) \<and>
		  (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT) t)) \<and>
      ((mk_functype (mk_list [t]) (mk_list [])) <ti: ft))" and
    inv_table_get: "e = (instr_sc5 (TABLE_GET x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_reftype rt)])) <ti: ft))" and
    inv_table_set: "e =  (instr_sc5 (TABLE_SET x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [valtype_I32, (valtype_reftype rt)]) (mk_list [])) <ti: ft))" and
    inv_table_size: "e = (instr_sc5 (TABLE_SIZE x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list []) (mk_list [valtype_I32])) <ti: ft))" and
    inv_table_grow: "e = (instr_sc5 (TABLE_GROW x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [(valtype_reftype rt), valtype_I32]) (mk_list [valtype_I32])) <ti: ft))" and
    inv_table_fill: "e = (instr_sc5 (TABLE_FILL x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_functype (mk_list [valtype_I32, (valtype_reftype rt), valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_table_copy: "e = (instr_sc5 (TABLE_COPY x_1 x_2)) \<Longrightarrow>
      (\<exists> lim_1 rt lim_2.
      ((proj_uN_0 x_1) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim_1 rt)) \<and>
		  ((proj_uN_0 x_2) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_2)) = (mk_tabletype lim_2 rt)) \<and>
		  (wf_tabletype (mk_tabletype lim_1 rt)) \<and>
		  (wf_tabletype (mk_tabletype lim_2 rt)) \<and>
		  ((mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_table_init: "e = (instr_sc5 (TABLE_INIT x_1 x_2)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x_1) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim rt)) \<and>
		  ((proj_uN_0 x_2) < (length (context_ELEMS C))) \<and>
		  (((context_ELEMS C) ! (proj_uN_0 x_2)) = rt) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
		  ((mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_elem_drop: "e = (instr_sc5 (ELEM_DROP x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_ELEMS C))) \<and>
		  (((context_ELEMS C) ! (proj_uN_0 x)) = rt) \<and>
      ((mk_functype (mk_list []) (mk_list [])) <ti: ft))" and
    inv_memory_size: "e = (instr_sc6 MEMORY_SIZE) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (wf_memtype mt) \<and>
      ((mk_functype (mk_list []) (mk_list [valtype_I32])) <ti: ft))" and
    inv_memory_grow: "e = (instr_sc6 MEMORY_GROW) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      (wf_memtype mt) \<and>
      ((mk_functype (mk_list [valtype_I32]) (mk_list [valtype_I32])) <ti: ft))" and
    inv_memory_fill: "e = (instr_sc6 MEMORY_FILL) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      (wf_memtype mt) \<and>
      ((mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_memory_copy: "e = (instr_sc6 MEMORY_COPY) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      (wf_memtype mt) \<and>
      ((mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_memory_init: "e = (instr_sc7 (MEMORY_INIT x)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      ((proj_uN_0 x) < (length (context_DATAS C))) \<and>
		  (((context_DATAS C) ! (proj_uN_0 x)) = OK) \<and>
      (wf_memtype mt) \<and>
      ((mk_functype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: ft))" and
    inv_data_drop: "e = (instr_sc7 (DATA_DROP x)) \<Longrightarrow>
      ((proj_uN_0 x) < (length (context_DATAS C))) \<and>
		  (((context_DATAS C) ! (proj_uN_0 x)) = OK) \<and>
      ((mk_functype (mk_list []) (mk_list [])) <ti: ft)" and
    inv_load_val: "e = (instr_sc5 (LOAD nt None v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  ((size (valtype_numtype nt)) \<noteq> None) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_numtype nt)])) <ti: ft))" and
    inv_load_pack: "e = (instr_sc5 (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat)))  \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32]) (mk_list [(valtype_Inn v_Inn)])) <ti: ft))" and
    inv_store_val: "e = (instr_sc6 (STORE nt None v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  ((size (valtype_numtype nt)) \<noteq> None) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32, (valtype_numtype nt)]) (mk_list [])) <ti: ft))" and
    inv_vload: "e = (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat)) * (v_N :: nat)) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128])) <ti: ft))" and
    inv_vload_splat: "e = (instr_sc6 (VLOAD V128 (Some (SPLAT v_n)) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128])) <ti: ft))" and
    inv_vload_zero: "e = (instr_sc6 (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32]) (mk_list [valtype_V128])) <ti: ft))" and
    inv_vload_lane: "e = (instr_sc6 (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
      (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list [valtype_V128])) <ti: ft))" and
    inv_vstore: "e = (instr_sc6 (VSTORE V128 v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
      ((size valtype_V128) \<noteq> None) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size valtype_V128))) :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list [])) <ti: ft))" and
    inv_vstore_lane: "e = (instr_sc6 (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
      (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_functype (mk_list [valtype_I32, valtype_V128]) (mk_list [])) <ti: ft))"

  using assms instr_ok_inv_store_pack apply blast
  using assms instr_ok_inv_ref_func apply blast
  using assms instr_ok_inv_cvtop_reinterpret apply blast

  using instr_inversion_helper[OF assms]


  apply auto                   
(* This next line takes a full two minutes *) 
  apply (cases rule: Instr_ok.cases, auto)+
  done          





lemma instr_ok_wf:
  assumes "Instrs_ok C [e] ft"
  shows   "(wf_context C)"
		      "(wf_instr e)"
	using instr_inversion_helper[OF assms]
	 apply auto
	apply (cases rule:Instr_ok.cases, auto)+
	done


(*Instrs_ok2*)
lemma e_type_empty1:
  assumes "Instrs_ok2 s C [] ft"
          "ft = (mk_functype (mk_list ts) (mk_list ts'))"
  shows   "(mk_functype (mk_list []) (mk_list [])) <ti: ft"
using assms
apply (induction "[] :: (admininstr list)" "ft" arbitrary: ts ts' rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2))
apply simp+
apply (metis instr_subtyping_refl)
   apply simp
  sorry
(*
using instr_subtyping_sub_rule instr_subtyping_trans apply force
using instr_subtyping_frame_rule instr_subtyping_trans apply force
by simp
*)

lemma instr_ok2_inversion_helper:
  assumes "Instrs_ok2 s C [a_e] ft"
  shows "\<exists> ft_principal. (Instr_ok2 s C a_e ft_principal) \<and> (ft_principal <ti: ft)"
  using assms
proof (induction s C "[a_e]" "ft" arbitrary:  rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where ?P1.0 = "\<lambda> s C e ft. \<exists> ft_principal. Instr_ok2 s C e ft_principal \<and> ft_principal <ti: ft" and ?P3.0 = "\<lambda> s C e rt. True"])
  case (plain C v_instr t_1_lst t_2_lst s)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.plain instr_subtyping_refl
    by blast
next
  case (label s C instr'_lst t'_lst t_lst admininstr_lst v_n)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.label instr_subtyping_refl
    by blast
next
  case (Instr_ok2__frame  s_s f_f C'_c admininstr_lst_l t_lst_r C_r v_n_r)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__frame instr_subtyping_refl
    by blast
next
  case (Instr_ok2__call_addr s v_funcaddr t_1_lst t_2_lst C)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__call_addr instr_subtyping_refl
    by blast
next
  case (Instr_ok2__ref s v_ref rt C)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__ref instr_subtyping_refl by blast
next
  case (Instr_ok2__trap s C t_1_lst t_2_lst)
  show ?case using admininstr_case_73 Instr_ok2__trap.hyps(1,2) Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__trap instr_subtyping_refl
    by (metis)
next
  case Instrs_ok2__empty
  then show ?case
    by simp
next
  case (Instrs_ok2__seq s C admininstr_1 t_1_lst t_2_lst admininstr_2_lst t_3_lst)
  then show ?case 
  proof (cases admininstr_1)
    case Nil
    then have "admininstr_2_lst = [a_e]" using Instrs_ok2__seq by force
    then have "(mk_functype (mk_list []) (mk_list [])) <ti: 
               (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))" 
      using Instrs_ok2__seq.hyps e_type_empty1 by auto
    then show ?thesis using func_sub_app_single_r 
      using Instrs_ok2__seq.hyps(4) \<open>admininstr_2_lst = [a_e]\<close> instr_subtyping_trans
      by blast
  next
    case (Cons a list)
    then have "admininstr_2_lst = []" using Instrs_ok2__seq by force
    then have "(mk_functype (mk_list []) (mk_list [])) <ti: 
               (mk_functype (mk_list t_2_lst) (mk_list t_3_lst))" 
      using Instrs_ok2__seq.hyps(3) e_type_empty1
      by auto
      then show ?thesis using func_sub_app_single_l 
        by (metis \<open>mk_functype (mk_list [])
             (mk_list []) <ti: mk_functype (mk_list t_2_lst) (mk_list t_3_lst)\<close> 
              Instrs_ok2__seq.hyps(2) func_sub_app_single_l 
              Instrs_ok2__seq.hyps(9)  
              \<open>admininstr_2_lst = []\<close> instr_subtyping_trans append.right_neutral)
  qed


 
next
  case (Instrs_ok2__sub s C t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case
    by (metis Instrs_ok2__sub.hyps(4) Instrs_ok2__sub.hyps(3) Instrs_ok2__sub.hyps(2) 
        instr_subtyping_trans instr_subtyping_sub_rule)
next
  case (Instrs_ok2__frame s C t_1_lst t_2_lst t_lst)
  then show ?case
    by (metis Instrs_ok2__frame.hyps(2) instr_subtyping_frame_rule instr_subtyping_trans)
qed

lemma instr_ok2_inversion:
  assumes "Instrs_ok2 s C [a_e] ft"
  shows
    inv_plain: "a_e = (admininstr_instr v_instr) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))" and
    inv_call_addr: "a_e = (admininstr_sc7 (CALL_ADDR v_funcaddr)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      ((mk_functype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: ft))"
  using instr_ok2_inversion_helper[OF assms]
  apply auto
  apply (cases rule: Instrs_ok2.cases, auto)
  using assms instr_subtyping_refl instr_subtyping_sub_rule instr_subtyping_frame_rule
(*  apply blast+
  apply (metis functype.exhaust res_list.exhaust) *)
  
sorry

lemma inv_ref: "a_e = (admininstr_ref v_ref) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst rt.
      (Ref_ok s v_ref rt) \<and>
      ((mk_functype (mk_list []) (mk_list [valtype_reftype rt])) <ti: ft))"
sorry

lemma inv_label:
  assumes "Instrs_ok2 s C [a_e] ft"
  shows "a_e = (admininstr_sc8 (LABEL_underscore v_n instr'_lst admininstr_lst)) \<Longrightarrow>
      (\<exists> t'_lst t_lst.
      (Instrs_ok2 s C (map (\<lambda> (instr' :: instr). (admininstr_instr instr')) instr'_lst) (mk_functype (mk_list t'_lst) (mk_list t_lst))) \<and>
      (Instrs_ok2 s (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t'_lst)], context_RETURN = None \<rparr> C) admininstr_lst (mk_functype (mk_list []) (mk_list t_lst))) \<and>
		  (wf_admininstr (admininstr_sc8 (LABEL_underscore v_n instr'_lst admininstr_lst))) \<Longrightarrow>
		  (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t'_lst)], context_RETURN = None \<rparr>) \<Longrightarrow>
		  (v_n = (length t'_lst)) \<Longrightarrow>
      ((mk_functype (mk_list []) (mk_list t_lst)) <ti: ft))"
  sorry



lemma instr_ok2_wf:
  assumes "Instrs_ok2 s C [e] ft"
  shows   "(wf_context C)"
		     (* "(wf_admininstr e)" *)
          "wf_store s"
	using instr_ok2_inversion_helper[OF assms]
	 apply auto
	  apply (cases rule:Instr_ok2.cases, auto)
	apply (cases rule:Instr_ok2.cases, auto)
	done

end