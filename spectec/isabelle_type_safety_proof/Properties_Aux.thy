theory Properties_Aux
	imports Main isabelle_reference_output_wasm2 Subtyping Subtyping_Properties
begin

 
lemma Instrs_ok_empty:
  assumes "Instrs_ok C [] ft"
          "ft = (mk_functype (mk_list ts) (mk_list ts'))"
  shows   "(mk_instrtype (mk_list []) (mk_list [])) <ti: (mk_instrtype (mk_list ts) (mk_list ts'))"
  using assms
  apply (induction "[] :: (instr list)" "ft" arbitrary: ts ts' rule: Instr_ok_Instrs_ok.inducts(2))
  apply auto
  subgoal
    unfolding Instrtype_sub.simps
    using Resulttype_sub_empty
    by (auto split: res_list.splits)
  subgoal for C t_1_lst t_2_lst t'_2_lst
    using Instrtype_sub_trans Instrtype_sub_sub_rule func_sub_app_single_l
    by blast
  subgoal
    using Instrtype_sub_trans Instrtype_sub_frame_rule Instrtype_sub_sub_rule
    by blast
  subgoal
    using Instrtype_sub_frame_rule Instrtype_sub_trans
    by blast
  done

lemma Instrs_ok_inversion_helper:
  assumes "Instrs_ok C [e] (mk_functype t1 t2)"
  shows "\<exists> tp1 tp2. ((Instr_ok C e (mk_functype tp1 tp2)) \<and>
        (mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2))"
  using assms
proof (induction C "[e]" "mk_functype t1 t2" arbitrary: t1 t2
       rule: Instr_ok_Instrs_ok.inducts(2)[where ?P1.0 =
          "\<lambda> C e ft.
        (case ft of (mk_functype t1 t2) \<Rightarrow>
        \<exists> tp1 tp2. Instr_ok C e (mk_functype tp1 tp2) \<and>
        (mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2))"])
  case (block C bt t_1_lst t_2_lst instr_lst)
  then show ?case
    using Instr_ok_Instrs_ok.block Instrtype_sub_refl
    by fastforce
next
  case (loop C bt t_1_lst t_2_lst instr_lst)
  then show ?case
    using Instr_ok_Instrs_ok.loop Instrtype_sub_refl by fastforce
next
  case (res_if C bt t_1_lst t_2_lst instr_1_lst instr_2_lst)
  then show ?case
    using Instr_ok_Instrs_ok.res_if Instrtype_sub_refl by fastforce
next
  case (br_table C l_lst t_lst l' t_1_lst t_2_lst)
  then show ?case
    using Instr_ok_Instrs_ok.br_table Instrtype_sub_refl by fastforce
next
  case (vstore mt C v_memarg)
  then show ?case
    using Instr_ok_Instrs_ok.vstore[OF vstore] Instrtype_sub_refl
    by auto
next
  case (vstore_lane mt C v_memarg v_n v_laneidx)
  then show ?case
    using Instr_ok_Instrs_ok.vstore_lane[OF vstore_lane] Instrtype_sub_refl
    by auto
next
  case (seq C instr_1 t_1_lst t_2_lst instr_2_lst t_3_lst)
  then show ?case
  proof (cases instr_1)
    case Nil
    then have e2: "instr_2_lst = [e]" using seq by simp
    then have "(mk_instrtype (mk_list []) (mk_list [])) <ti:
               (mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst))"
      using seq.hyps Instrs_ok_empty by blast
    then show ?thesis
      using  \<open>instr_2_lst = [e]\<close> func_sub_app_single_r
              Instrtype_sub_trans seq.hyps(3,4) by blast
  next
    case (Cons a list)
    then have "instr_2_lst = []" "instr_1 = [e]"
      using seq.hyps(8) by auto
      then have "(mk_instrtype (mk_list []) (mk_list [])) <ti:
                  (mk_instrtype (mk_list t_2_lst) (mk_list t_3_lst))"
    using seq.hyps(3) Instrs_ok_empty by blast
  then show ?thesis
    using \<open>instr_1 = [e]\<close> func_sub_app_single_l seq.hyps(1,2)
        Instrtype_sub_trans by blast
qed
next
  case (sub C t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case
    by (metis Instrtype_sub_sub_rule Instrtype_sub_trans)
next
  case (Instrs_ok__frame C t_1_lst t_2_lst t_lst)
  then show ?case
    by (metis Instrtype_sub_frame_rule Instrtype_sub_trans)

(* This next line used to take a while *)
qed (fastforce intro: Instr_ok_Instrs_ok.intros Instrtype_sub_refl)+

termination numtype_Inn
  by lexicographic_order

lemma Instrs_ok_inv_store_pack:
  assumes "Instrs_ok C [e] (mk_functype t1 t2)"
          "e = (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg))"
  shows
       "(\<exists> mt.
        (0 < (length (context_MEMS C))) \<and>
        (((context_MEMS C) ! 0) = mt) \<and>
        (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat))) \<and>
        (wf_memtype mt) \<and>
        ((mk_instrtype (mk_list [valtype_I32, (valtype_Inn v_Inn)]) (mk_list [])) <ti:
        mk_instrtype t1 t2))"
proof -
  obtain tp1 tp2 where
     "Instr_ok C (instr_sc6 (STORE (numtype_Inn v_Inn)
      (Some (mk_sz v_M)) v_memarg)) (mk_functype tp1 tp2)" and
		 "(mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2)"
  by (metis assms(1) assms(2) Instrs_ok_inversion_helper)
  then show ?thesis using assms(1)
  proof (induction "C" "(instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg))"
        "mk_functype tp1 tp2"
        arbitrary: v_Inn rule: Instr_ok_Instrs_ok.inducts(1))
      case (store_pack C mt v_Innsa)
      have "v_Inn = v_Innsa"
        by (metis store_pack.hyps(7) numtype_Inn.elims numtype.distinct(1))
      then have "mk_instrtype (mk_list [valtype_I32, valtype_Inn v_Inn]) (mk_list []) <ti:
                mk_instrtype t1 t2" using store_pack(8,9,10)
        by simp
      then show ?case
        using store_pack.hyps(1,2,3,5) by auto
    qed
qed

lemma Instrs_ok_inv_ref_func:
  assumes "Instrs_ok C [e] (mk_functype t1 t2)"
          "e = (instr_sc4 (REF_FUNC x))"
  shows"(\<exists> fta.
        ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
        (((context_FUNCS C) ! (proj_uN_0 x)) = fta) \<and>
        ((mk_instrtype (mk_list []) (mk_list [valtype_FUNCREF])) <ti: mk_instrtype t1 t2))"
proof -
obtain tp1 tp2 where
  "Instr_ok C (instr_sc4 (REF_FUNC x)) (mk_functype tp1 tp2)" and
  "mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2" 
  by (metis assms(2) assms(1) Instrs_ok_inversion_helper)
  then show ?thesis
    by (cases rule: Instr_ok.cases, auto)
qed

termination isabelle_reference_output_wasm2.size
  by lexicographic_order

termination isabelle_reference_output_wasm2.valtype_numtype
  by lexicographic_order

lemma Instrs_ok_inv_cvtop_reinterpret:
  assumes "Instrs_ok C [e] (mk_functype t1 t2)"
          "e = (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET))"
  shows "
      ((size (valtype_numtype nt_1)) \<noteq> None) \<and>
      ((size (valtype_numtype nt_2)) \<noteq> None) \<and>
      ((the ((size (valtype_numtype nt_1)))) = (the ((size (valtype_numtype nt_2))))) \<and>
      ((mk_instrtype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: mk_instrtype t1 t2)"
proof -
obtain tp1 tp2 where
  a: "Instr_ok C (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET)) (mk_functype tp1 tp2)" and
  b: "mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2"
  by (metis assms(2) assms(1) Instrs_ok_inversion_helper)
  show ?thesis using a b
    apply (induction "C" "(instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET))" 
          "mk_functype tp1 tp2" arbitrary: nt_1 nt_2 rule: Instr_ok_Instrs_ok.inducts(1))
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

lemma Instrs_ok_inversion:
  assumes "Instrs_ok C [e] (mk_functype t1 t2)"
  shows 
    inv_store_pack: "e = (instr_sc6 (STORE (numtype_Inn v_Inn) (Some (mk_sz v_M)) v_memarg)) \<Longrightarrow>
        (\<exists> mt.
        (0 < (length (context_MEMS C))) \<and>
        (((context_MEMS C) ! 0) = mt) \<and>
        (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat))) \<and>
        (wf_memtype mt) \<and>
        ((mk_instrtype (mk_list [valtype_I32, (valtype_Inn v_Inn)]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_ref_func: "e = (instr_sc4 (REF_FUNC x)) \<Longrightarrow>
        (\<exists> fta.
        ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
        (((context_FUNCS C) ! (proj_uN_0 x)) = fta) \<and>
        ((mk_instrtype (mk_list []) (mk_list [valtype_FUNCREF])) <ti: mk_instrtype t1 t2))" and
    inv_cvtop_reinterpret: "e = (instr_sc1 (CVTOP nt_1 nt_2 REINTERPRET)) \<Longrightarrow>
        ((size (valtype_numtype nt_1)) \<noteq> None) \<and>
        ((size (valtype_numtype nt_2)) \<noteq> None) \<and>
        ((the ((size (valtype_numtype nt_1)))) = (the ((size (valtype_numtype nt_2))))) \<and>
        ((mk_instrtype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: mk_instrtype t1 t2)" and
    inv_nop: "e = instr_sc0 NOP \<Longrightarrow> (mk_instrtype (mk_list []) (mk_list [])) <ti: mk_instrtype t1 t2" and
    inv_unreachable: "e = instr_sc0 UNREACHABLE \<Longrightarrow> True" and
    inv_drop: "e = instr_sc0 DROP \<Longrightarrow> (\<exists> t. ((mk_instrtype (mk_list [t]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_select_expl: "e = instr_sc0 (SELECT (Some ts)) \<Longrightarrow> \<exists> t. ts = [t] \<and> (mk_instrtype (mk_list [t, t, valtype_I32]) (mk_list [t]) <ti: mk_instrtype t1 t2)" and
     inv_select_impl: "e = instr_sc0 (SELECT (None)) \<Longrightarrow> (\<exists> t v_numtype v_vectype t'. (Valtype_sub t t') \<and> ((t' = (valtype_numtype v_numtype)) \<or> (t' = (valtype_vectype v_vectype))) \<and> ((mk_instrtype (mk_list [t, t, valtype_I32]) (mk_list [t])) <ti: mk_instrtype t1 t2))" and
    inv_block: "e = (instr_sc7 (BLOCK bt instr_lst)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr>) \<and>
      (Blocktype_ok C bt (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
      ((Instrs_ok (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t_2_lst)], context_RETURN = None \<rparr> C) instr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<and>
      ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
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
		  ((mk_instrtype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
	  inv_br: "e = (instr_sc0 (BR l)) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst t_2_lst.
		  ((proj_uN_0 l) < (length (LABELS C))) \<and>
		  ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<and>
		  ((mk_instrtype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_br_if: "e = (instr_sc0 (BR_IF l)) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst.
		  ((proj_uN_0 l) < (length (LABELS C))) \<and>
		  ((proj_list_0  ((LABELS C) ! (proj_uN_0 l))) = t_lst) \<and>
		  ((mk_instrtype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_lst)) <ti: mk_instrtype t1 t2))" and
    inv_br_table:  "e = (instr_sc0 (BR_TABLE l_lst l')) \<Longrightarrow>
      (\<exists> l t_lst t_1_lst t_2_lst.
      (list_all (\<lambda> (l :: labelidx). ((proj_uN_0 l) < (length (LABELS C)))) l_lst) \<and>
		  (list_all (\<lambda> (l :: labelidx). (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l)))) l_lst) \<and>
		  ((proj_uN_0 l') < (length (LABELS C))) \<and>
		  (Resulttype_sub (mk_list t_lst) ((LABELS C) ! (proj_uN_0 l'))) \<and>
      ((mk_instrtype (mk_list (t_1_lst @ (t_lst @ [valtype_I32]))) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_call: "e = (instr_sc0 (CALL x)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
		  ((proj_uN_0 x) < (length (context_FUNCS C))) \<and>
		  (((context_FUNCS C) ! (proj_uN_0 x)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_call_indirect: "e = (instr_sc0 (CALL_INDIRECT x y)) \<Longrightarrow>
      (\<exists> lim t_1_lst t_2_lst.
		  ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim FUNCREF)) \<and>
		  ((proj_uN_0 y) < (length (context_TYPES C))) \<and>
		  (((context_TYPES C) ! (proj_uN_0 y)) = (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		  (wf_tabletype (mk_tabletype lim FUNCREF)) \<and>
      ((mk_instrtype (mk_list (t_1_lst @ [valtype_I32])) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_return: "e = (instr_sc1 RETURN) \<Longrightarrow>
      (\<exists> t_lst t_1_lst t_2_lst.
      ((context_RETURN C) = (Some (mk_list t_lst))) \<and>
		  ((mk_instrtype (mk_list (t_1_lst @ t_lst)) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_const: "e = (instr_sc1 (res_CONST nt c_nt)) \<Longrightarrow> (mk_instrtype (mk_list []) (mk_list [(valtype_numtype nt)])) <ti: mk_instrtype t1 t2" and
    inv_unop: "e = (instr_sc1 (UNOP nt unop_nt)) \<Longrightarrow> (mk_instrtype (mk_list [(valtype_numtype nt)]) (mk_list [(valtype_numtype nt)])) <ti: mk_instrtype t1 t2" and
    inv_binop: "e = (instr_sc1 (BINOP nt binop_nt)) \<Longrightarrow> (mk_instrtype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [(valtype_numtype nt)])) <ti: mk_instrtype t1 t2" and
    inv_testop: "e = (instr_sc1 (TESTOP nt testop_nt)) \<Longrightarrow> (mk_instrtype (mk_list [(valtype_numtype nt)]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2" and
    inv_relop: "e = (instr_sc1 (RELOP nt relop_nt)) \<Longrightarrow> (mk_instrtype (mk_list [(valtype_numtype nt), (valtype_numtype nt)]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2" and
    inv_cvtop_convert: "e = (instr_sc1 (CVTOP nt_1 nt_2 v_cvtop)) \<Longrightarrow> (mk_instrtype (mk_list [(valtype_numtype nt_2)]) (mk_list [(valtype_numtype nt_1)])) <ti: mk_instrtype t1 t2" and
    inv_ref_null: "e = (instr_sc4 (REF_NULL rt)) \<Longrightarrow> (mk_instrtype (mk_list []) (mk_list [(valtype_reftype rt)])) <ti: mk_instrtype t1 t2" and
    inv_ref_is_null: "e = (instr_sc4 REF_IS_NULL) \<Longrightarrow> (\<exists> rt. ((mk_instrtype (mk_list [(valtype_reftype rt)]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2))" and
    inv_vconst: "e = (instr_sc1 (VCONST V128 c)) \<Longrightarrow> (mk_instrtype (mk_list []) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vvunop: "e = (instr_sc2 (VVUNOP V128 v_vvunop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vvbinop: "e = (instr_sc2 (VVBINOP V128 v_vvbinop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vvternop: "e = (instr_sc2 (VVTERNOP V128 v_vvternop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vvtestop: "e = (instr_sc2 (VVTESTOP V128 v_vvtestop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2" and
    inv_vunop: "e = (instr_sc2 (VUNOP sh vunop_sh)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vbinop: "e = (instr_sc2 (VBINOP sh vbinop_sh)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vtestop: "e = (instr_sc2 (VTESTOP sh vtestop_sh)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2" and
    inv_vrelop: "e = (instr_sc2 (VRELOP sh vrelop_sh)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vshiftop: "e = (instr_sc2 (VSHIFTOP ish vshiftop_sh)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_I32]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vbitmask: "e = (instr_sc3 (VBITMASK ish)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2" and
    inv_vswizzle: "e = (instr_sc3 (VSWIZZLE ish)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vshuffle: "e = (instr_sc3 (VSHUFFLE ish i_lst)) \<Longrightarrow>
      (\<exists> i.
      (list_all (\<lambda> (i :: laneidx). ((proj_uN_0 i) < (2 * (proj_dim_0 (fun_dim (shape_ishape ish)))))) i_lst) \<and>
		  ((wf_dim (fun_dim (shape_ishape ish)))) \<and>
      ((mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2))" and
    inv_vsplat: "e = (instr_sc3 (VSPLAT sh)) \<Longrightarrow> (mk_instrtype (mk_list [(valtype_numtype (shunpack sh))]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vextract_lane: "e = (instr_sc3 (VEXTRACT_LANE sh sx_opt i)) \<Longrightarrow>
      ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<and>
		  (wf_dim (fun_dim sh)) \<and>
      ((mk_instrtype (mk_list [valtype_V128]) (mk_list [(valtype_numtype (shunpack sh))])) <ti: mk_instrtype t1 t2)" and
    inv_vreplace_lane: "e = (instr_sc3 (VREPLACE_LANE sh i)) \<Longrightarrow>
      ((proj_uN_0 i) < (proj_dim_0 (fun_dim sh))) \<and>
		  (wf_dim (fun_dim sh)) \<and>
      ((mk_instrtype (mk_list [valtype_V128, (valtype_numtype (shunpack sh))]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2)" and
    inv_vextunop: "e = (instr_sc3 (VEXTUNOP sh_1 sh_2 vextunop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_V128]) <ti: mk_instrtype t1 t2)" and
    inv_vextbinop: "e = (instr_sc3 (VEXTBINOP sh_1 sh_2 vextbinop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128]) <ti: mk_instrtype t1 t2)" and
    inv_vnarrow: "e = (instr_sc3 (VNARROW sh_1 sh_2 v_sx)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_vcvtop: "e = (instr_sc4 (VCVTOP sh sh2 v_vcvtop)) \<Longrightarrow> (mk_instrtype (mk_list [valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2" and
    inv_local_get: "e = (instr_sc4 (LOCAL_GET x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_instrtype (mk_list []) (mk_list [t])) <ti: mk_instrtype t1 t2))" and
    inv_local_set: "e = (instr_sc4 (LOCAL_SET x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_instrtype (mk_list [t]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_local_tee: "e = (instr_sc4 (LOCAL_TEE x)) \<Longrightarrow>
      (\<exists> t.
      ((proj_uN_0 x) < (length (context_LOCALS C))) \<and>
		  (((context_LOCALS C) ! (proj_uN_0 x)) = t) \<and>
      ((mk_instrtype (mk_list [t]) (mk_list [t])) <ti: mk_instrtype t1 t2))" and
    inv_global_get: "e = (instr_sc4 (GLOBAL_GET x)) \<Longrightarrow>
      (\<exists> v_mut t.
      ((proj_uN_0 x) < (length (context_GLOBALS C))) \<and>
		  (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype v_mut t)) \<and>
      ((mk_instrtype (mk_list []) (mk_list [t])) <ti: mk_instrtype t1 t2))" and
    inv_global_set: "e = (instr_sc4 (GLOBAL_SET x)) \<Longrightarrow>
      (\<exists> MUT t.
      ((proj_uN_0 x) < (length (context_GLOBALS C))) \<and>
		  (((context_GLOBALS C) ! (proj_uN_0 x)) = (mk_globaltype (Some MUT) t)) \<and>
      ((mk_instrtype (mk_list [t]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_table_get: "e = (instr_sc5 (TABLE_GET x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_instrtype (mk_list [valtype_I32]) (mk_list [(valtype_reftype rt)])) <ti: mk_instrtype t1 t2))" and
    inv_table_set: "e =  (instr_sc5 (TABLE_SET x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_instrtype (mk_list [valtype_I32, (valtype_reftype rt)]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_table_size: "e = (instr_sc5 (TABLE_SIZE x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_instrtype (mk_list []) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2))" and
    inv_table_grow: "e = (instr_sc5 (TABLE_GROW x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_instrtype (mk_list [(valtype_reftype rt), valtype_I32]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2))" and
    inv_table_fill: "e = (instr_sc5 (TABLE_FILL x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x)) = (mk_tabletype lim rt)) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
      ((mk_instrtype (mk_list [valtype_I32, (valtype_reftype rt), valtype_I32]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_table_copy: "e = (instr_sc5 (TABLE_COPY x_1 x_2)) \<Longrightarrow>
      (\<exists> lim_1 rt lim_2.
      ((proj_uN_0 x_1) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim_1 rt)) \<and>
		  ((proj_uN_0 x_2) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_2)) = (mk_tabletype lim_2 rt)) \<and>
		  (wf_tabletype (mk_tabletype lim_1 rt)) \<and>
		  (wf_tabletype (mk_tabletype lim_2 rt)) \<and>
		  ((mk_instrtype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_table_init: "e = (instr_sc5 (TABLE_INIT x_1 x_2)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x_1) < (length (context_TABLES C))) \<and>
		  (((context_TABLES C) ! (proj_uN_0 x_1)) = (mk_tabletype lim rt)) \<and>
		  ((proj_uN_0 x_2) < (length (context_ELEMS C))) \<and>
		  (((context_ELEMS C) ! (proj_uN_0 x_2)) = rt) \<and>
		  (wf_tabletype (mk_tabletype lim rt)) \<and>
		  ((mk_instrtype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_elem_drop: "e = (instr_sc5 (ELEM_DROP x)) \<Longrightarrow>
      (\<exists> lim rt.
      ((proj_uN_0 x) < (length (context_ELEMS C))) \<and>
		  (((context_ELEMS C) ! (proj_uN_0 x)) = rt) \<and>
      ((mk_instrtype (mk_list []) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_memory_size: "e = (instr_sc6 MEMORY_SIZE) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (wf_memtype mt) \<and>
      ((mk_instrtype (mk_list []) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2))" and
    inv_memory_grow: "e = (instr_sc6 MEMORY_GROW) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      (wf_memtype mt) \<and>
      ((mk_instrtype (mk_list [valtype_I32]) (mk_list [valtype_I32])) <ti: mk_instrtype t1 t2))" and
    inv_memory_fill: "e = (instr_sc6 MEMORY_FILL) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      (wf_memtype mt) \<and>
      ((mk_instrtype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_memory_copy: "e = (instr_sc6 MEMORY_COPY) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      (wf_memtype mt) \<and>
      ((mk_instrtype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_memory_init: "e = (instr_sc7 (MEMORY_INIT x)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
      (((context_MEMS C) ! 0) = mt) \<and>
      ((proj_uN_0 x) < (length (context_DATAS C))) \<and>
		  (((context_DATAS C) ! (proj_uN_0 x)) = OK) \<and>
      (wf_memtype mt) \<and>
      ((mk_instrtype (mk_list [valtype_I32, valtype_I32, valtype_I32]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_data_drop: "e = (instr_sc7 (DATA_DROP x)) \<Longrightarrow>
      ((proj_uN_0 x) < (length (context_DATAS C))) \<and>
		  (((context_DATAS C) ! (proj_uN_0 x)) = OK) \<and>
      ((mk_instrtype (mk_list []) (mk_list [])) <ti: mk_instrtype t1 t2)" and
    inv_load_val: "e = (instr_sc5 (LOAD nt None v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  ((size (valtype_numtype nt)) \<noteq> None) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32]) (mk_list [(valtype_numtype nt)])) <ti: mk_instrtype t1 t2))" and
    inv_load_pack: "e = (instr_sc5 (LOAD (numtype_Inn v_Inn) (Some (mk_loadop__0 v_Inn (mk_loadop_Inn (mk_sz v_M) v_sx))) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat)))  \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32]) (mk_list [(valtype_Inn v_Inn)])) <ti: mk_instrtype t1 t2))" and
    inv_store_val: "e = (instr_sc6 (STORE nt None v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  ((size (valtype_numtype nt)) \<noteq> None) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size (valtype_numtype nt)))) :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32, (valtype_numtype nt)]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_vload: "e = (instr_sc6 (VLOAD V128 (Some (SHAPEX_underscore v_M v_N v_sx)) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_M :: nat) div (8 :: nat)) * (v_N :: nat)) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2))" and
    inv_vload_splat: "e = (instr_sc6 (VLOAD V128 (Some (SPLAT v_n)) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2))" and
    inv_vload_zero: "e = (instr_sc6 (VLOAD V128 (Some (vloadop_ZERO v_n)) v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2))" and
    inv_vload_lane: "e = (instr_sc6 (VLOAD_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
      (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32, valtype_V128]) (mk_list [valtype_V128])) <ti: mk_instrtype t1 t2))" and
    inv_vstore: "e = (instr_sc6 (VSTORE V128 v_memarg)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
      ((size valtype_V128) \<noteq> None) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> (((the ((size valtype_V128))) :: nat) div (8 :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32, valtype_V128]) (mk_list [])) <ti: mk_instrtype t1 t2))" and
    inv_vstore_lane: "e = (instr_sc6 (VSTORE_LANE V128 (mk_sz v_n) v_memarg v_laneidx)) \<Longrightarrow>
      (\<exists> mt.
      (0 < (length (context_MEMS C))) \<and>
		  (((context_MEMS C) ! 0) = mt) \<and>
		  (((2 ^ (proj_uN_0 (ALIGN v_memarg))) :: nat) \<le> ((v_n :: nat) div (8 :: nat))) \<and>
      (((proj_uN_0 v_laneidx) :: nat) < ((128 :: nat) div (v_n :: nat))) \<and>
		  (wf_memtype mt) \<and>
		  ((mk_instrtype (mk_list [valtype_I32, valtype_V128]) (mk_list [])) <ti: mk_instrtype t1 t2))"

  using assms Instrs_ok_inv_store_pack apply blast
  using assms Instrs_ok_inv_ref_func apply blast
  using assms Instrs_ok_inv_cvtop_reinterpret apply blast

  using Instrs_ok_inversion_helper[OF assms]


  apply auto
(* This next line takes a full two minutes *)
  apply (cases rule: Instr_ok.cases, auto)+
  done



lemma Instr_ok_wf:
  assumes "Instr_ok C e ft"
  shows   "(wf_context C)"
		      "(wf_instr e)"
	using assms
proof (induction)
qed(simp)+

lemma Instrs_ok_wf:
  assumes "Instrs_ok C e ft"
  shows   "(wf_context C)"
		      "(list_all wf_instr e)"
	using assms
proof (induction)
qed(simp)+


(*Instrs_ok2*)
lemma Instrs_ok2_empty:
  assumes "Instrs_ok2 s C [] ft"
          "ft = (mk_functype (mk_list t1) (mk_list t2))"
  shows   "(mk_instrtype (mk_list []) (mk_list [])) <ti: (mk_instrtype (mk_list t1) (mk_list t2))"
using assms
apply (induction "[] :: (admininstr list)" "ft" arbitrary: t1 t2 rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2))
apply simp+
apply (metis Instrtype_sub_refl)
apply simp
apply (meson Instrtype_sub_trans func_sub_app_single_r)
using Instrtype_sub_sub_rule Instrtype_sub_trans apply force
using Instrtype_sub_frame_rule Instrtype_sub_trans apply force
apply simp
done

lemma Instrs_ok2_inversion_helper:
  assumes "Instrs_ok2 s C [a_e] (mk_functype t1 t2)"
  shows "\<exists> tp1 tp2. (Instr_ok2 s C a_e (mk_functype tp1 tp2)) \<and>
        (mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2)"
  using assms
proof (induction s C "[a_e]" "mk_functype t1 t2" arbitrary:  t1 t2
      rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where ?P1.0 =
        "\<lambda> s C e ft. (case ft of (mk_functype t1 t2) \<Rightarrow>
        \<exists> tp1 tp2. Instr_ok2 s C e (mk_functype tp1 tp2) \<and>
          (mk_instrtype tp1 tp2 <ti: mk_instrtype t1 t2))" and ?P3.0 = "\<lambda> s C e rt. True"])
  case (plain C v_instr t_1_lst t_2_lst s)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.plain Instrtype_sub_refl
    by fastforce
next
  case (label s C instr'_lst t'_lst t_lst admininstr_lst v_n)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.label Instrtype_sub_refl
    by fastforce
next
  case (Instr_ok2__frame  s_s f_f C'_c admininstr_lst_l t_lst_r C_r v_n_r)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__frame Instrtype_sub_refl
    by fastforce
next
  case (Instr_ok2__call_addr s v_funcaddr t_1_lst t_2_lst C)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__call_addr Instrtype_sub_refl
    by fastforce
next
  case (Instr_ok2__ref s v_ref rt C)
  then show ?case using Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__ref Instrtype_sub_refl
    by fastforce
next
  case (Instr_ok2__trap s C t_1_lst t_2_lst)
  show ?case using admininstr_case_73 Instr_ok2__trap.hyps(1,2) Instr_ok2_Instrs_ok2_Expr_ok2.Instr_ok2__trap Instrtype_sub_refl
    by fastforce
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
    then have "(mk_instrtype (mk_list []) (mk_list [])) <ti:
               (mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst))"
      using Instrs_ok2__seq.hyps Instrs_ok2_empty by auto
    then show ?thesis using func_sub_app_single_r
      using Instrs_ok2__seq.hyps(4) \<open>admininstr_2_lst = [a_e]\<close> Instrtype_sub_trans
      by fastforce
  next
    case (Cons a list)
    then have "admininstr_2_lst = []" using Instrs_ok2__seq by force
    then have "(mk_instrtype (mk_list []) (mk_list [])) <ti:
               (mk_instrtype (mk_list t_2_lst) (mk_list t_3_lst))"
      using Instrs_ok2__seq.hyps(3) Instrs_ok2_empty
      by auto
      then show ?thesis using func_sub_app_single_l
        by (metis \<open>mk_instrtype (mk_list [])
             (mk_list []) <ti: mk_instrtype (mk_list t_2_lst) (mk_list t_3_lst)\<close>
              Instrs_ok2__seq.hyps(2) func_sub_app_single_l
              Instrs_ok2__seq.hyps(9)
              \<open>admininstr_2_lst = []\<close> Instrtype_sub_trans append.right_neutral)
  qed



next
  case (Instrs_ok2__sub s C t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case
    by (metis Instrs_ok2__sub.hyps(4) Instrs_ok2__sub.hyps(3)
        Instrtype_sub_trans Instrtype_sub_sub_rule)
next
  case (Instrs_ok2__frame s C t_1_lst t_2_lst t_lst)
  then show ?case
    by (metis Instrtype_sub_frame_rule Instrtype_sub_trans)
qed(fastforce)+

lemma Instrs_ok2_inversion:
  assumes "Instrs_ok2 s C [a_e] (mk_functype t1 t2)"
  shows
    inv_plain: "a_e = (admininstr_instr v_instr) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2) \<and> 
       Instr_ok C v_instr (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))" and
    inv_label: "a_e = (admininstr_sc8 (LABEL_underscore v_n instr'_lst admininstr_lst)) \<Longrightarrow>
      (\<exists> t'_lst t_lst.
      (Instrs_ok2 s C (map (\<lambda> (instr' :: instr). (admininstr_instr instr')) instr'_lst) (mk_functype (mk_list t'_lst) (mk_list t_lst))) \<and>
      (Instrs_ok2 s (append_res_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t'_lst)], context_RETURN = None \<rparr> C) admininstr_lst (mk_functype (mk_list []) (mk_list t_lst))) \<and>
		  (wf_context \<lparr> context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [], LABELS = [(mk_list t'_lst)], context_RETURN = None \<rparr>) \<Longrightarrow>
		  (v_n = (length t'_lst)) \<Longrightarrow>
      ((mk_instrtype (mk_list []) (mk_list t_lst)) <ti: mk_instrtype t1 t2))" and
   (*  inv_call_addr: "a_e = (admininstr_sc7 (CALL_ADDR v_funcaddr)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and *)
    inv_frame: "a_e = (admininstr_sc8 (FRAME_underscore v_n f admininstr_lst)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst C' t_lst.
		  (Frame_ok s f C') \<and>
		  (Expr_ok2 s C' admininstr_lst (mk_list t_lst)) \<and>
		  (wf_context C') \<and>
		  (v_n = (length t_lst)) \<and>
      ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_call_addr: "a_e = (admininstr_sc7 (CALL_ADDR v_funcaddr)) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      (Externaddr_ok s (externaddr_FUNC v_funcaddr) (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<and>
		  (wf_externtype (FUNC (mk_functype (mk_list t_1_lst) (mk_list t_2_lst)))) \<and>
      ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" and
    inv_ref: "a_e = (admininstr_ref v_ref) \<Longrightarrow>
      (\<exists> rt.
      (Ref_ok s v_ref rt) \<and>
      ((mk_instrtype (mk_list []) (mk_list [valtype_reftype rt])) <ti: mk_instrtype t1 t2))" (* and *)
  (*  inv_trap: "a_e = (admininstr_sc7 admininstr_st7_TRAP) \<Longrightarrow>
      (\<exists> t_1_lst t_2_lst.
      ((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst)) <ti: mk_instrtype t1 t2))" *)

  using Instrs_ok2_inversion_helper[OF assms]
  apply auto
  apply (cases rule: Instrs_ok2.cases, auto)
  using assms Instrtype_sub_refl Instrtype_sub_sub_rule Instrtype_sub_frame_rule
(*  apply blast+
  apply (metis instrtype.exhaust res_list.exhaust) *)

  sorry

lemma map_is_app :
  assumes "map f l = res1 @ res2"
  shows "\<exists> l1 l2. l1 @ l2 = l \<and> map f l1 = res1 \<and> map f l2 = res2"
  using assms
proof (induction l arbitrary: res1 res2)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by (metis map_eq_append_conv)
qed

(*
fun is_const :: "instr \<Rightarrow> bool" where
"is_const (instr_sc1 (res_CONST _ _)) = True"
| "is_const (instr_sc1 (VCONST _ _)) = True"
| "is_const (instr_sc4 (REF_NULL _)) = True"
| "is_const _ = False" 
*)

lemma inv_const_list :
  assumes "Instrs_ok2 s C e (mk_functype t1 t2)"
          "e = map (\<lambda> v. admininstr_val v) vs" 
        shows "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: mk_instrtype t1 t2" 
  using assms
proof (induction s C e "mk_functype t1 t2" arbitrary: vs t1 t2
      rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where ?P1.0 =
        "(\<lambda> s C e ft. (case ft of (mk_functype t1 t2) \<Rightarrow> 
         (\<forall> v. (e = admininstr_val v \<longrightarrow>
         (mk_instrtype (mk_list []) (mk_list [typeofval v]) <ti: mk_instrtype t1 t2)))))
        " and ?P3.0 = "\<lambda> s C e rt. True" ])
  case (plain C v_instr t1l t2l s)
  then show ?case
    apply (auto)
    subgoal for v
    proof -
      assume newassms: "Instr_ok C v_instr (mk_functype (mk_list t1l) (mk_list t2l))"
        "wf_context C"
        "wf_instr v_instr"
        "admininstr_instr v_instr = admininstr_val v"
      then show "mk_instrtype (mk_list []) (mk_list [typeofval v]) <ti: 
                 mk_instrtype (mk_list t1l) (mk_list t2l)"
      proof (cases rule: Instr_ok.cases)
        case (const nt c_nt)
      then show ?thesis using newassms(4)
      proof (cases v)
        case (val_CONST tval vval)
        then show ?thesis using const admininstr_val.domintros admininstr_val.psimps
          admininstr_instr.domintros admininstr_instr.psimps newassms(4)
          by (metis Instrtype_sub_refl admininstr.inject(2) admininstr_st1.inject(5) 
              typeofval.domintros(1)
              typeofval.psimps(1))
      qed (simp add: admininstr_val.domintros admininstr_val.psimps
                   admininstr_instr.domintros admininstr_instr.psimps)+ 
    next
      case (vconst c)
      then show ?thesis using newassms(4)
      proof (cases v) 
        case (val_VCONST tval vval)
        then show ?thesis using vconst admininstr_val.domintros(2) admininstr_val.psimps(2)
          admininstr_instr.domintros(21) admininstr_instr.psimps(21) typeofval.domintros(2)
          typeofval.psimps(2) Instrtype_sub_refl valtype_vectype.domintros valtype_vectype.psimps
          newassms(4)
          by simp
      qed(simp add:admininstr_val.domintros admininstr_val.psimps
                   admininstr_instr.domintros admininstr_instr.psimps)+ 
    next
      case (ref_null rt)
      then show ?thesis using newassms(4)
      proof (cases v) 
        case (val_REF_NULL rt')
        then show ?thesis using ref_null admininstr_val.domintros admininstr_val.psimps
          admininstr_instr.domintros admininstr_instr.psimps newassms(4) 
          by (metis Instrtype_sub_refl admininstr.inject(5) admininstr_st4.inject(4) 
              typeofval.domintros(3)
              typeofval.psimps(3))
       qed(simp add:admininstr_val.domintros admininstr_val.psimps
                   admininstr_instr.domintros admininstr_instr.psimps)+ 
  qed(cases v, simp_all add:admininstr_val.domintros admininstr_val.psimps
                   admininstr_instr.domintros admininstr_instr.psimps)+ 
qed done
  
next
  case (label s C instr'_lst t'_lst t_lst admininstr_lst v_n)
  show ?case
    apply (auto)
    subgoal for v
    proof (cases v)
    qed(simp add:admininstr_val.domintros admininstr_val.psimps)+
    done
next
  case (Instr_ok2__frame s f C' admininstr_lst t_lst C v_n)
  show ?case
    apply (auto)
    subgoal for v
    proof (cases v)
    qed(simp add:admininstr_val.domintros admininstr_val.psimps)+
    done
next
  case (Instr_ok2__call_addr s v_funcaddr t_1_lst t_2_lst C)
  show ?case
    apply (auto)
    subgoal for v
    proof (cases v)
    qed(simp add:admininstr_val.domintros admininstr_val.psimps)+
    done
next
  case (Instr_ok2__ref s v_ref rt C)
    show ?case
    apply (auto)
    subgoal for v
    proof (cases v)
      case (val_CONST x11 x12)
      assume "admininstr_ref v_ref = admininstr_val v" 
      then show ?thesis using val_CONST 
      proof (cases v_ref)
      qed(simp add:admininstr_val.domintros admininstr_val.psimps admininstr_ref.domintros
          admininstr_ref.psimps)+
    next
      case (val_VCONST x21 x22)
      assume "admininstr_ref v_ref = admininstr_val v" 
      then show ?thesis using val_VCONST 
      proof (cases v_ref)
      qed(simp add:admininstr_val.domintros admininstr_val.psimps admininstr_ref.domintros
          admininstr_ref.psimps)+
    next
      case (val_REF_NULL x3)
      assume eq: "admininstr_ref v_ref = admininstr_val v"
      show ?thesis using Instr_ok2__ref eq val_REF_NULL
      proof (induction rule:Ref_ok.cases)
        case (null s rt)
        then show ?case 
          using Instrtype_sub_refl admininstr_val.domintros(3) 
                admininstr_val.psimps(3) admininstr_ref.domintros(1) 
                admininstr_ref.psimps(1)
          by (simp add: typeofval.domintros(3) typeofval.psimps(3))
      qed(simp add:admininstr_val.domintros admininstr_val.psimps admininstr_ref.domintros
          admininstr_ref.psimps)+
    next
      case (val_REF_FUNC_ADDR x4)
      assume eq: "admininstr_ref v_ref = admininstr_val v"
      show ?thesis using Instr_ok2__ref eq val_REF_FUNC_ADDR
      proof (induction rule:Ref_ok.cases)
        case (Ref_ok__func s a ext)
        then show ?case
          using Instrtype_sub_refl admininstr_val.domintros admininstr_val.psimps
            admininstr_ref.domintros admininstr_ref.psimps typeofval.domintros 
          typeofval.psimps
          using valtype_reftype.domintros(1) valtype_reftype.psimps(1) by presburger
      qed(simp add:admininstr_val.domintros admininstr_val.psimps admininstr_ref.domintros
          admininstr_ref.psimps)+
    next
      case (val_REF_HOST_ADDR x5)
       assume eq: "admininstr_ref v_ref = admininstr_val v"
      show ?thesis using Instr_ok2__ref eq val_REF_HOST_ADDR
      proof (induction rule:Ref_ok.cases)
        case (extern s a)
        then show ?case
          using Instrtype_sub_refl admininstr_val.domintros admininstr_val.psimps
            admininstr_ref.domintros admininstr_ref.psimps typeofval.domintros 
          typeofval.psimps valtype_reftype.domintros valtype_reftype.psimps by simp
      qed(simp add:admininstr_val.domintros admininstr_val.psimps admininstr_ref.domintros
          admininstr_ref.psimps)+
    qed
    done
next
  case (Instr_ok2__trap s C t_1_lst t_2_lst)
  show ?case
    apply (auto)
    subgoal for v
    proof (cases v)
    qed(simp add:admininstr_val.domintros admininstr_val.psimps)+
    done
next
  case (Instrs_ok2__empty s C)
  then show ?case using Instrtype_sub_refl by simp
next
  case (Instrs_ok2__instr s C v_admininstr t_1_lst t_2_lst)
  then show ?case 
  proof (cases vs)
    case Nil
    then show ?thesis using Instrs_ok2__instr by simp
  next
    case (Cons a list)
    then show ?thesis 
    proof (cases list)
      case Nil
      then show ?thesis using Cons Instrs_ok2__instr
        by simp
    next
      case (Cons a' list')
      then show ?thesis using Instrs_ok2__instr
        by auto
    qed
  qed 
next
  case (Instrs_ok2__seq s C es1 t1l t2l es2 t3l)
  then show ?case 
  proof -
    obtain vs1 vs2 where "vs1 @ vs2 = vs" "es1 = map admininstr_val vs1" "es2 = map admininstr_val vs2"
      using map_is_app Instrs_ok2__seq(9)
      by metis
    then show ?thesis using Instrs_ok2__seq Instrtype_sub_emptyl
      by fastforce
  qed
next
  case (Instrs_ok2__sub s C admininstr_lst t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case using Instrtype_sub_trans
    using Instrtype_sub_sub_rule by blast
next
  case (Instrs_ok2__frame s C admininstr_lst t_1_lst t_2_lst t_lst)
  then show ?case using Instrtype_sub_trans
    using Instrtype_sub_frame_rule by blast
next
  case (mk_Expr_ok2 s C admininstr_lst t_lst)
  then show ?case by simp
qed 

lemma app_app:
  assumes "l1 @ l2 = m1 @ m2"
  shows "\<exists> n1 n2 n3. (n1 = l1 \<and> n2 @ n3 = l2 \<and> n1 @ n2 = m1 \<and> n3 = m2) \<or>
(n1 @ n2 = l1 \<and> n3 = l2 \<and> n1 = m1 \<and> n2 @ n3 = m2)"
  using assms
proof(induction l1 arbitrary: l2 m1 m2)
  case Nil
  then have "[] = [] \<and> m1 @ m2 = l2 \<and> [] @ m1 = m1 \<and> m2 = m2" by simp
  then show ?case by blast
next
  case (Cons a l1)
  note outer = Cons
  then show ?case
  proof (cases m1)
    case Nil
    then show ?thesis
      by (metis local.Nil append_Nil Cons.prems)
  next
    case (Cons b m1')
    then have "a = b" "l1 @ l2 = m1' @ m2" using outer by auto
    then show ?thesis using outer(1)
      by (metis \<open>a = b\<close> \<open>l1 @ l2 = m1' @ m2\<close> local.Cons append_Cons)
  qed
qed


lemma inv_seq:
  assumes "Instrs_ok2 s C es (mk_functype t1 t3)"
          "es = (es1 @ es2)"
  shows "(\<exists> t1' t2' t3'.
    (Instrs_ok2 s C es1 (mk_functype t1' t2')) \<and>
		(Instrs_ok2 s C es2 (mk_functype t2' t3')) \<and>
    Resulttype_sub t1 t1' \<and> Resulttype_sub t3' t3)"
  using assms
proof(induction s C es "mk_functype t1 t3" arbitrary: t1 t3 es1 es2
rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where ?P1.0 =
"\<lambda> s C e ft. True" 
and ?P3.0 = "\<lambda> s C e rt. True" 
])
  case (Instrs_ok2__empty s C)
  then show ?case
    using Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__empty Resulttype_sub_empty by blast
next
  case (Instrs_ok2__instr s C v_admininstr t1l t3l)
  then show ?case 
  proof(cases es1)
    case Nil
    then have okes1: "Instrs_ok2 s C es1 (mk_functype (mk_list t1l) (mk_list t1l))"
      using Instrs_ok2__empty Instrs_ok2__frame Instrs_ok2__instr.hyps(3,4) by fastforce
    have "Instrs_ok2 s C es2 (mk_functype (mk_list t1l) (mk_list t3l))" 
      using Nil Instrs_ok2__instr
      using Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__instr by auto
    then show ?thesis using okes1 
      using Resulttype_sub_refl by blast
  next
    case (Cons a list)
    then have okes1: "Instrs_ok2 s C es1 (mk_functype (mk_list t1l) (mk_list t3l))" 
      using Instrs_ok2__instr Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__instr by force
    have "es2 = []" using Cons Instrs_ok2__instr
      by simp
    then have "Instrs_ok2 s C es2 (mk_functype (mk_list t3l) (mk_list t3l))" 
      using Instrs_ok2__empty Instrs_ok2__frame
      using Instrs_ok2__instr.hyps(3,4) by fastforce
    then show ?thesis using okes1 Resulttype_sub_refl by blast
  qed
next
  case (Instrs_ok2__seq s C es1' t1l t2l es2' t3l)
  obtain l1 l2 l3 where
    "(l1 = es1' \<and> l2 @ l3 = es2' \<and> l1 @ l2 = es1 \<and> l3 = es2) \<or>
      (l1 @ l2 = es1' \<and> l3 = es2' \<and> l1 = es1 \<and> l2 @ l3 = es2)"
    using app_app[OF Instrs_ok2__seq(9)] by force
  then show ?case 
  proof
    assume els: "l1 = es1' \<and> l2 @ l3 = es2' \<and> l1 @ l2 = es1 \<and> l3 = es2"
    then obtain t1' t2' t3' where
      ih: "Instrs_ok2 s C l2 (mk_functype t1' t2')"
      "Instrs_ok2 s C l3 (mk_functype t2' t3')"
      "Resulttype_sub (mk_list t2l) t1'" "Resulttype_sub t3' (mk_list t3l)"
      using Instrs_ok2__seq(4) by blast
    then show "\<exists>t1' t2' t3'.
       Instrs_ok2 s C es1 (mk_functype t1' t2') \<and>
       Instrs_ok2 s C es2 (mk_functype t2' t3') \<and> Resulttype_sub (mk_list t1l) t1' \<and> 
       Resulttype_sub t3' (mk_list t3l)"
    proof (cases t1')
      case (mk_list t1l')
      then have okes1': "Instrs_ok2 s C es1' (mk_functype (mk_list t1l) t1')"
        using Instrs_ok2__sub[OF Instrs_ok2__seq(1) Resulttype_sub_refl[of "mk_list t1l"]] 
            ih(3) Instrs_ok2__seq by blast
      then show ?thesis
      proof (cases t2')
        case (mk_list t2l')
        then have "Instrs_ok2 s C es1 (mk_functype (mk_list t1l) t2')" 
        using ih(1) els Instrs_ok2__seq Resulttype_sub.simps okes1'
        using Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__seq ih(3) by auto
      then show ?thesis using ih els
        using Resulttype_sub_refl by blast
    qed
  qed
next
    assume els: "l1 @ l2 = es1' \<and> l3 = es2' \<and> l1 = es1 \<and> l2 @ l3 = es2"
    then obtain t1' t2' t3' where
      ih: "Instrs_ok2 s C l1 (mk_functype t1' t2')"
      "Instrs_ok2 s C l2 (mk_functype t2' t3')"
      "Resulttype_sub (mk_list t1l) t1'" "Resulttype_sub t3' (mk_list t2l)"
      using Instrs_ok2__seq(2) by blast
    then show "\<exists>t1' t2' t3'.
       Instrs_ok2 s C es1 (mk_functype t1' t2') \<and>
       Instrs_ok2 s C es2 (mk_functype t2' t3') \<and> Resulttype_sub (mk_list t1l) t1' \<and> 
       Resulttype_sub t3' (mk_list t3l)"
    proof (cases t3')
      case (mk_list t3l')
      then have okes1': "Instrs_ok2 s C es2' (mk_functype t3' (mk_list t3l))"
        using Instrs_ok2__sub[OF Instrs_ok2__seq(3)]
            Resulttype_sub_refl[of "mk_list t3l"]
            ih(4) Instrs_ok2__seq by blast
      then show ?thesis
      proof (cases t2')
        case (mk_list t2l')
        then have "Instrs_ok2 s C es2 (mk_functype t2' (mk_list t3l))" 
        using ih(2) els Instrs_ok2__seq Resulttype_sub.simps okes1'
        using Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__seq ih(4) by auto
      then show ?thesis using ih els
        using Resulttype_sub_refl by blast
    qed
  qed
qed
next
  case (Instrs_ok2__sub s C es t1l t2l t1l' t2l')
  then show ?case
    by (metis Resulttype_sub_trans)
next
  case (Instrs_ok2__frame s C es t1l t2l tl)
  then obtain t1' t2' t3' where ih:
    "Instrs_ok2 s C es1 (mk_functype t1' t2')"
    "Instrs_ok2 s C es2 (mk_functype t2' t3')"
    "Resulttype_sub (mk_list t1l) t1'"
    "Resulttype_sub t3' (mk_list t2l)" 
    by blast
  then show ?case
  proof (cases t1')
    case (mk_list t1l')
    note t1eq = mk_list
    then show ?thesis
    proof (cases t2')
      case (mk_list t2l')
      note t2eq = mk_list
      then show ?thesis 
      proof (cases t3')
        case (mk_list t3l')
        then have ok1: "Instrs_ok2 s C es1 (mk_functype (mk_list (tl @ t1l')) (mk_list (tl @ t2l')))"
          using ih(1) t1eq t2eq
          using Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__frame Instrs_ok2__frame.hyps(3,4,5)
            Instrs_ok2__frame.prems list_all_append by blast
        have "Instrs_ok2 s C es2 (mk_functype (mk_list (tl @ t2l')) (mk_list (tl @ t3l')))"
          using ih(2) t2eq mk_list
          using Instr_ok2_Instrs_ok2_Expr_ok2.Instrs_ok2__frame Instrs_ok2__frame.hyps(3,4,5)
            Instrs_ok2__frame.prems list_all_append by blast
        then show ?thesis using ok1 ih(3,4)
          using Resulttype_sub_append Resulttype_sub_refl mk_list t1eq by blast
      qed qed qed
    qed (simp)+

(*
lemma inv_cons:
  assumes "Instrs_ok2 s C es (mk_functype t1 t4)"
          "es = (e # es2)"
  shows "(\<exists> t1' t2' t3' t4'.
    (Instr_ok2 s C e (mk_functype t1' t2')) \<and>
		(Instrs_ok2 s C es2 (mk_functype t3' t4')) \<and>
    Resulttype_sub t1 t1' \<and> Resulttype_sub t2' t3' \<and> Resulttype_sub t4' t4)"
proof -
  obtain t1' t2' t3' where split:
    "Instrs_ok2 s C [e] (mk_functype t1' t2')"
    "Instrs_ok2 s C es2 (mk_functype t2' t3')"
    "Resulttype_sub t1 t1'" "Resulttype_sub t3' t4"
    using assms inv_seq[of s C es t1 t4 "[e]" es2] by auto
  then obtain t1'' t2'' where one:
    "Instr_ok2 s C e (mk_functype t1'' t2'')" 
    "mk_instrtype t1'' t2'' <ti: mk_instrtype t1' t2'" 
    using Instrs_ok2_inversion_helper by blast
  show ?thesis using one(2)
  proof (induction "mk_instrtype t1'' t2''" "mk_instrtype t1' t2'"
        rule:Instrtype_sub.induct)
    case (mk_Instrtype_sub t_21_lst t_lst t_11'_lst t_22_lst t'_lst t_12'_lst t_11_lst t_12_lst)
    then show ?case using split one 
  qed

qed
*)

(* Not convinced these ones will ever be necessary: the sub and frame cases are
   an inconvenience that appears
   in every other case, not cases we want to specifically invert on *)
(*
lemma inv_Instrs_ok2__sub:
  assumes "Instrs_ok2 s C admininstr_lst (mk_functype t1 t2)"
  shows "(\<exists> t_1_lst t_2_lst t2.
		(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		(Resulttype_sub t1 (mk_list t_1_lst)) \<and>
		(Resulttype_sub (mk_list t_2_lst) t2) \<and>
		(list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst) \<and>
		((mk_instrtype (mk_list t_1_lst) (mk_list t_2_lst) <ti: mk_instrtype t1 t2)))"

sorry 

lemma inv_Instrs_ok2__frame:
  assumes "Instrs_ok2 s C admininstr_lst (mk_functype t1 t2)"
  shows "(\<exists> t_lst t_1_lst t_2_lst.
		(Instrs_ok2 s C admininstr_lst (mk_functype (mk_list t_1_lst) (mk_list t_2_lst))) \<and>
		(list_all (\<lambda> (v_admininstr :: admininstr). (wf_admininstr v_admininstr)) admininstr_lst) \<and>
		((mk_instrtype (mk_list (t_lst @ t_1_lst)) (mk_list (t_lst @ t_2_lst)) <ti: mk_instrtype t1 t2)))"

sorry *)



lemma Instr_ok2_wf:
  assumes "Instr_ok2 s C e ft"
  shows   "(wf_context C)"
          "wf_store s"
  using assms
proof(induction)
qed(simp)+

lemma Instrs_ok2_wf:
  assumes "Instrs_ok2 s C e ft"
  shows   "(wf_context C)"
          "wf_store s"
  using assms
proof(induction)
qed(simp)+

lemma list_all_drop:
  assumes "list_all (\<lambda> x. P x \<and> Q x) l"
  shows "list_all P l"
  using assms
proof(induction l)
qed(auto)


lemma wf_admininstr_instr:
  assumes "wf_instr e"
  shows "wf_admininstr (admininstr_instr e)"
  using assms
proof(induction e rule:wf_instr.induct)
  case (instr_case_4 v_blocktype instr_lst)
  then show ?case using admininstr_case_4 list_all_drop 
    by (metis admininstr_instr.domintros(5) admininstr_instr.psimps(5))
next
  case (instr_case_5 v_blocktype instr_lst)
  then show ?case  using admininstr_case_5 list_all_drop 
    by (metis admininstr_instr.domintros(6) admininstr_instr.psimps(6))
next
  case (instr_case_6 v_blocktype instr_lst instr_lst_0_lst)
  then show ?case  using admininstr_case_6 list_all_drop 
    by (metis admininstr_instr.domintros(7) admininstr_instr.psimps(7))
qed(simp_all add: wf_admininstr.intros admininstr_instr.domintros admininstr_instr.psimps)+



lemma admininstr_instr_inj:
  assumes "admininstr_instr e1 = admininstr_instr e2"
  shows "e1 = e2"
  using assms
proof (cases e1 rule:admininstr_instr.cases)
(* This next line can take many seconds *)
 qed(cases e2 rule:admininstr_instr.cases, 
     simp_all add:admininstr_instr.domintros admininstr_instr.psimps)+


lemma wf_admininstr_instr_inv:
  assumes "wf_admininstr (admininstr_instr e)"
  shows "wf_instr e"
  using assms

   apply(induction "admininstr_instr e" rule:wf_admininstr.induct;
                      cases e rule:admininstr_instr.cases)
(* This next line can take a little while *)
  apply(simp_all add:admininstr_instr.domintros admininstr_instr.psimps wf_instr.intros)
  done

  

lemma Instr_ok2_wf_instr:
  assumes "Instr_ok2 s C e ft"
  shows "wf_admininstr e"
  using assms
proof(induction s C e ft rule:Instr_ok2_Instrs_ok2_Expr_ok2.inducts(1)[where ?P2.0 =
    "\<lambda> s C e ft. list_all wf_admininstr e" and ?P3.0 = "\<lambda> s C e rt. True"])
  case (plain C v_instr t_1_lst t_2_lst s)
  then show ?case using wf_admininstr_instr by simp 
next
  case (Instr_ok2__ref s v_ref rt C)
  then show ?case
  proof (induction rule:Ref_ok.induct)
    case (null s rt)
    then show ?case
      by (simp add: admininstr_case_40 admininstr_ref.domintros(1) admininstr_ref.psimps(1))
  next
    case (Ref_ok__func s a ext)
    then show ?case 
      using admininstr_case_68 admininstr_ref.domintros(2) admininstr_ref.psimps(2) by presburger
  next
    case (extern s a)
    then show ?case
      using admininstr_case_69 admininstr_ref.domintros(3) admininstr_ref.psimps(3) by presburger
  qed
qed(simp)+


lemma Instrs_ok2_wf_instr:
  assumes "Instrs_ok2 s C e ft"
  shows "list_all wf_admininstr e"
  using assms
proof(induction s C e ft rule:Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where ?P1.0 =
    "\<lambda> s C e ft. wf_admininstr e" and ?P3.0 = "\<lambda> s C e rt. True"])
  case (plain C v_instr t_1_lst t_2_lst s)
  then show ?case using wf_admininstr_instr by simp 
next
  case (Instr_ok2__ref s v_ref rt C)
  then show ?case
  proof (induction rule:Ref_ok.induct)
    case (null s rt)
    then show ?case
      by (simp add: admininstr_case_40 admininstr_ref.domintros(1) admininstr_ref.psimps(1))
  next
    case (Ref_ok__func s a ext)
    then show ?case 
      using admininstr_case_68 admininstr_ref.domintros(2) admininstr_ref.psimps(2) by presburger
  next
    case (extern s a)
    then show ?case
      using admininstr_case_69 admininstr_ref.domintros(3) admininstr_ref.psimps(3) by presburger
  qed
qed(simp)+

(*
lemma Instr_ok2_const:
  assumes "wf_context C" "wf_store s" "wf_admininstr (admininstr_val v)"
  shows "Instr_ok2 s C (admininstr_val v) (mk_functype (mk_list []) (mk_list [typeofval v]))"
proof (cases v)
  case (val_CONST x11 x12)
  then show ?thesis using plain const assms sledgehammer
next
  case (val_VCONST x21 x22)
  then show ?thesis sorry
next
  case (val_REF_NULL x3)
  then show ?thesis sorry
next
  case (val_REF_FUNC_ADDR x4)
  then show ?thesis sorry
next
  case (val_REF_HOST_ADDR x5)
  then show ?thesis sorry
qed

lemma Instrs_ok2_const:
  assumes "wf_context C" "wf_store s" "list_all wf_admininstr (map admininstr_val vs)"
  shows "Instrs_ok2 s C (map administr_val vs) 
      (mk_functype (mk_list []) (mk_list (map typeofval vs)))"
  using assms
proof (induction vs)
  case Nil
  then show ?case using Instrs_ok2__empty by simp 
next
  case (Cons a vs)
  then show ?case using Instrs_ok2__seq Instrs_ok2__instr 
qed

*)
 
lemma Instr_ok2_const_replace:
  assumes "Instr_ok2 s C (admininstr_val v) tf" 
  shows "Instr_ok2 s C (admininstr_val v) (mk_functype (mk_list []) (mk_list [typeofval v]))"
proof (cases v)
  case (val_CONST x11 x12)
  then show ?thesis using Instr_ok2_wf Instr_ok2_wf_instr assms 
    plain wf_admininstr_instr_inv const
    by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14) admininstr_val.domintros(1)
        admininstr_val.psimps(1) typeofval.domintros(1) typeofval.psimps(1))
next
  case (val_VCONST x21 x22)
  then show ?thesis
  proof (cases x21)
    case V128
    then have "wf_instr (instr_sc1 (VCONST V128 x22))" using 
        val_VCONST Instr_ok2_wf_instr wf_admininstr_instr_inv
      using admininstr_instr.domintros(21) admininstr_instr.psimps(21) admininstr_val.domintros(2)
        admininstr_val.psimps(2) assms by auto
      then show ?thesis using val_VCONST Instr_ok2_wf assms 
          plain V128
          vconst
          admininstr_instr.domintros(21) admininstr_instr.psimps(21)
          admininstr_val.domintros(2) admininstr_val.psimps(2) typeofval.domintros(2) 
          typeofval.psimps(2)
        by (metis valtype_vectype.domintros valtype_vectype.psimps)
    qed
next
  case (val_REF_NULL x3)
  then have "wf_instr (instr_sc4 (REF_NULL x3))" using 
    Instr_ok2_wf_instr assms wf_admininstr_instr_inv
    using instr_case_40 by presburger
  then show ?thesis using Instr_ok2_wf assms 
    plain ref_null
    by (metis admininstr_instr.domintros(41) admininstr_instr.psimps(41) admininstr_val.domintros(3)
        admininstr_val.psimps(3) typeofval.domintros(3) typeofval.psimps(3) val_REF_NULL)
next
  case (val_REF_FUNC_ADDR x4)
  then have eq: "admininstr_val v = admininstr_ref (REF_FUNC_ADDR x4)"
    by (simp add: admininstr_ref.domintros(2) admininstr_ref.psimps(2)
        admininstr_val.domintros(4) admininstr_val.psimps(4))
  then show ?thesis 
  proof(cases tf)
    case (mk_functype t1l t2l)
    then have 
      "Instrs_ok2 s C [admininstr_ref (REF_FUNC_ADDR x4)] (mk_functype t1l t2l)"
      using assms val_REF_FUNC_ADDR 
        Instrs_ok2__instr[of s C "admininstr_val v"]
        Instr_ok2_wf_instr eq
        Instr_ok2_wf
      by (metis res_list.exhaust) 
    then obtain rt where 
      "Ref_ok s (REF_FUNC_ADDR x4) rt"
      "mk_instrtype (mk_list [])
          (mk_list [valtype_reftype rt]) <ti: mk_instrtype t1l t2l" 
      using inv_ref
        admininstr_val.psimps admininstr_val.domintros admininstr_ref.psimps
        admininstr_ref.domintros Instrs_ok2.simps Instrs_ok2_wf_instr
      by metis
    then show ?thesis using Instr_ok2__ref assms Instr_ok2_wf 
      val_REF_FUNC_ADDR admininstr_val.domintros admininstr_val.psimps 
      valtype_reftype.domintros valtype_reftype.psimps
      admininstr_ref.domintros admininstr_ref.psimps 
      by (metis Ref_ok.simps ref.distinct(1,5) typeofval.domintros(4)
          typeofval.psimps(4))
  qed
next
  case (val_REF_HOST_ADDR x5)
  then have eq: "admininstr_val v = admininstr_ref (REF_HOST_ADDR x5)"
    by (simp add: admininstr_ref.domintros(3) admininstr_ref.psimps(3)
        admininstr_val.domintros(5) admininstr_val.psimps(5))
  then show ?thesis 
  proof(cases tf)
    case (mk_functype t1l t2l)
    then have 
      "Instrs_ok2 s C [admininstr_ref (REF_HOST_ADDR x5)] (mk_functype t1l t2l)"
      using assms val_REF_HOST_ADDR 
        Instrs_ok2__instr[of s C "admininstr_val v"]
        Instr_ok2_wf_instr eq
        Instr_ok2_wf
      by (metis res_list.exhaust) 
    then obtain rt where 
      "Ref_ok s (REF_HOST_ADDR x5) rt"
      "mk_instrtype (mk_list [])
          (mk_list [valtype_reftype rt]) <ti: mk_instrtype t1l t2l" 
      using inv_ref
        admininstr_val.psimps admininstr_val.domintros admininstr_ref.psimps
        admininstr_ref.domintros Instrs_ok2.simps Instrs_ok2_wf_instr
      by metis
    then show ?thesis using Instr_ok2__ref assms Instr_ok2_wf 
      val_REF_HOST_ADDR admininstr_val.domintros admininstr_val.psimps 
      valtype_reftype.domintros valtype_reftype.psimps
      admininstr_ref.domintros admininstr_ref.psimps 
      by (metis Ref_ok.simps typeofval.domintros(5)
          typeofval.psimps(5))
  qed
qed

(*
lemma Instrs_ok2_one_const_replace:
  assumes "Instrs_ok2 s C [admininstr_val v] tf" 
  shows "Instrs_ok2 s C [admininstr_val v] (mk_functype (mk_list []) (mk_list [typeofval v]))"
  using assms
proof (induction s C "[admininstr_val v]" tf
    rule: Instr_ok2_Instrs_ok2_Expr_ok2.inducts(2)[where
      ?P1.0 = "\<lambda> s C e tf. True" and ?P3.0 = "\<lambda> s C e tf. True"])
  case (Instrs_ok2__instr s C t_1_lst t_2_lst)
  then show ?case 
    using Instr_ok2_const_replace isabelle_reference_output_wasm2.Instrs_ok2__instr
    by simp
next
  case (Instrs_ok2__seq s C admininstr_1_lst t_1_lst t_2_lst admininstr_2_lst t_3_lst)
  then show ?case sorry
next
  case (Instrs_ok2__sub s C t_1_lst t_2_lst t'_1_lst t'_2_lst)
  then show ?case sorry
next
  case (Instrs_ok2__frame s C t_1_lst t_2_lst t_lst)
  then show ?case sorry
qed(auto)*)

lemma Instrs_ok2_const_replace:
  assumes "Instrs_ok2 s C (map admininstr_val vs) tf" 
  shows "Instrs_ok2 s C (map admininstr_val vs) 
          (mk_functype (mk_list []) (mk_list (map typeofval vs)))"
  using assms
proof (induction vs arbitrary:tf)
  case Nil
  then show ?case using Instrs_ok2__empty Instrs_ok2_wf by simp
next
  case (Cons a vs)
  then show ?case
  proof (cases tf)
    case (mk_functype t1 t2)
    then obtain t1' t2' t3' where split:
       "Instrs_ok2 s C [admininstr_val a] (mk_functype t1' t2')"
       "Instrs_ok2 s C (map admininstr_val vs) (mk_functype t2' t3')"
       "Resulttype_sub t1 t1'" "Resulttype_sub t3' t2" 
      using Cons inv_seq[of s C "map admininstr_val (a # vs)" t1 t2 
                          "[admininstr_val a]" "map admininstr_val vs"]
      by auto
    then obtain t1'' t2'' where 
      "Instr_ok2 s C (admininstr_val a) (mk_functype t1'' t2'')" 
      using Instrs_ok2_inversion_helper by fast
    then have "Instr_ok2 s C (admininstr_val a) (mk_functype (mk_list [])
                (mk_list [typeofval a]))" using Instr_ok2_const_replace by fast
    then have a: "Instrs_ok2 s C [admininstr_val a] (mk_functype (mk_list [])
                (mk_list [typeofval a]))" using Instrs_ok2__instr 
                Instr_ok2_wf Instr_ok2_wf_instr by simp
    have "Instrs_ok2 s C (map admininstr_val vs) 
               (mk_functype (mk_list []) (mk_list (map typeofval vs)))" 
      using Cons split by fast
    then have "Instrs_ok2 s C (map admininstr_val vs) 
              (mk_functype (mk_list [typeofval a]) (mk_list (map typeofval (a # vs))))"
      using Instrs_ok2__frame[of s C "map admininstr_val vs" "[]" "map typeofval vs"
              "[typeofval a]"] Instrs_ok2_wf Instrs_ok2_wf_instr by auto
    then show ?thesis using a 
      Instrs_ok2__seq[of s C "[admininstr_val a]" "[]" "[typeofval a]" 
            "map admininstr_val vs" "map typeofval (a # vs)"]
      Instrs_ok2_wf Instrs_ok2_wf_instr by fastforce
  qed

qed


end