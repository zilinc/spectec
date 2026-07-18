theory Wasm2_Type_Soundness
(* Imported Code *)
	imports isabelle_reference_output_wasm2 store_extension_typing Properties Type_Inversion Subtyping_Theorem
begin

definition t_inst_match :: "res_context \<Rightarrow> res_context \<Rightarrow> bool" where
  "t_inst_match C C' \<equiv> context_TYPES C = context_TYPES C' \<and>
                       context_FUNCS C = context_FUNCS C' \<and>
                       context_GLOBALS C = context_GLOBALS C' \<and>
                       context_TABLES C = context_TABLES C' \<and>
                       context_MEMS C = context_MEMS C' \<and>
                       context_ELEMS C = context_ELEMS C' \<and>
                       context_DATAS C = context_DATAS C'"

lemma t_inst_match_is:
  assumes "t_inst_match C1 C2"
  shows "\<exists>a b c. C2 = \<lparr> context_TYPES = context_TYPES C1,
                       context_FUNCS = context_FUNCS C1,
                       context_GLOBALS = context_GLOBALS C1,
                       context_TABLES = context_TABLES C1,
                       context_MEMS = context_MEMS C1,
                       context_ELEMS = context_ELEMS C1,
                       context_DATAS = context_DATAS C1,
                       context_LOCALS = a,
                       LABELS = b,
                       context_RETURN = c \<rparr>"
  by (metis (full_types) assms unit.exhaust res_context.surjective t_inst_match_def)

lemma step_wf: "(wf_config var_0) \<Longrightarrow>
		 (Step var_0 var_1) \<Longrightarrow>
		 (wf_config var_1)"
  sorry


lemma list_update_func_length:
  assumes "list_update_func l k f = l'"
  shows "length l = length l'"
  using assms
proof (induction l arbitrary: k l')
  case Nil
  then show ?case
  by simp 
next
  case (Cons a l)
  then show ?case 
  proof (cases k)
    case 0
    then show ?thesis
    using Cons.prems by force
  next
    case (Suc nat)
    then show ?thesis using Cons by auto
  qed 
qed

lemma list_all2_list_update_func_r :
  assumes "list_all2 f l1 l2"
          "list_update_func l2 k g = l2'" 
          "f (l1 ! k) (g (l2 ! k))"
        shows "list_all2 f l1 l2'"
  using assms
proof (induction l2 arbitrary: k l2')
  case Nil
  then show ?case
  by simp 
next
  case (Cons a l2)
  then show ?case 
  proof (cases k)
    case 0
    then show ?thesis using Cons by auto
  next
    case (Suc nat)
    then show ?thesis using Cons by auto
  qed
qed


lemma e_preservation_locals:
  assumes "Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
          "Store_ok s"
          "Store_ok s'"
	        "Extend_store s s'"
          "Moduleinst_ok s (frame_MODULE f) C"
          "Moduleinst_ok s' (frame_MODULE f) C"
          "t_inst_match C C'"
          "list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s v t)) (context_LOCALS C') (LOCALS f)"
          "Instrs_ok2 s C' es tf"

shows
          "length (LOCALS f) = length (LOCALS f')"
          "frame_MODULE f = frame_MODULE f'"
          "list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s' v t)) (context_LOCALS C') (LOCALS f')"
  using assms
proof (induction "mk_config (mk_state s f) es" "mk_config (mk_state s' f') es'" 
       arbitrary: es es' s s' f f' tf rule: Step.induct)
  case pure 
  {
    case 1
    then show ?case using pure by simp
  next
    case 2
    then show ?case using pure by simp
  next
    case 3
    then show ?case using pure by simp
  }
next
  case read
  {
    case 1
    then show ?case using read by simp
  next
    case 2
    then show ?case using read by simp
  next
    case 3
    then show ?case using read by simp
  }
next
  case (ctxt_label es0 es1 v_n instr_0_lst)
  {
    case 1 
  then have ok: "Instrs_ok2 s C' es0 tf" 
    sorry (* inversion lemma on labels *) 
    then show ?case using ok ctxt_label 1 by simp
  next
    case 2
  have ok: "Instrs_ok2 s C' es0 tf" 
    using assms(9)
    sorry (* inversion lemma on labels *) 
    then show ?case using ok ctxt_label 2 by simp
  next
    case 3
  have ok: "Instrs_ok2 s C' es0 tf" 
    using assms(9)
    sorry (* inversion lemma on labels *) 
    then show ?case using ok ctxt_label 3 by simp
  }
next
  case (ctxt_frame f' es0 f'' es1 v_n)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (ctxt_instrs es0 es1 es2)
  then have ok: "Instrs_ok2 s C' es0 tf" sorry (* inversion lemma on concatenation *)
  {
    case 1
    then show ?case using ok ctxt_instrs by simp
  next
    case 2
    then show ?case using ok ctxt_instrs by simp
  next
    case 3
    then show ?case using ok ctxt_instrs by simp
  }
next
  case (Step__local_set v_val x)
  {
    case 1
    have "list_update_func (LOCALS f) (proj_uN_0 x) (\<lambda> _. v_val) = LOCALS f'" 
      using Step__local_set 
      by (metis local.Step__local_set with_local.psimps state.inject 
          with_local.domintros frame.update_convs(1) frame.ext_inject frame.surjective)
    then show ?case using list_update_func_length
      by blast
  next
    case 2
    then show ?case using Step__local_set using with_local.domintros with_local.psimps by auto 
  next
    case 3
    have localsupd: "list_update_func (LOCALS f) (proj_uN_0 x) (\<lambda> _. v_val) = LOCALS f'" 
      using Step__local_set 
      by (metis local.Step__local_set with_local.psimps state.inject 
          with_local.domintros frame.update_convs(1) frame.ext_inject frame.surjective)
    have types': "list_all2 (\<lambda> t v. Val_ok s' v t) (context_LOCALS C') (LOCALS f)" 
      using 3 store_extension_valok list_all2_mono
      by (metis (mono_tags, lifting) Extend_store.simps)
    have "Val_ok s' v_val (context_LOCALS C' ! proj_uN_0 x)" 
      using 3(8)
      sorry (* figure out t, use inversion for concat, inversion for value v_val, for local_set *) 
    then show ?case using localsupd types' list_all2_list_update_func_r
      by blast
  }
next
  case (Step__global_set v_val x)
  then have samef: "f = f'" by (simp add: with_global.domintros with_global.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps) 
  }
next
  case (table_set_trap i x v_ref)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using table_set_trap by simp
  }
next
  case (table_set_val i x v_ref)
  then have samef: "f = f'" by (simp add: with_table.domintros with_table.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (table_grow_succeed x v_n v_ref var_0 ti)
  then have samef: "f = f'" by (simp add: with_tableinst.domintros with_tableinst.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (table_grow_fail var_0 v_ref v_n x)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using table_grow_fail by simp
  }
next
  case (Step__elem_drop x)
  then have samef: "f = f'" using with_elem.domintros with_elem.psimps by force
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (store_num_trap i nt ao c)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using store_num_trap by simp
  }
next
  case (store_num_val i nt b_lst c ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (store_pack_trap i ao v_n v_Inn c)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using store_pack_trap by simp
  }
next
  case (store_pack_val i v_Inn c b_lst v_n ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (vstore_oob i ao c)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using vstore_oob by simp
  }
next
  case (vstore_val i b_lst c ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (vstore_lane_oob i ao v_N c j)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using vstore_lane_oob by simp
  }
next
  case (vstore_lane_val i v_N v_Jnn v_M c j b_lst ao)
  then have samef: "f = f'" by (simp add: with_mem.domintros with_mem.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (memory_grow_succeed v_n var_0 mi)
  then have samef: "f = f'" by (simp add: with_meminst.domintros with_meminst.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
next
  case (memory_grow_fail var_0 v_n)
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case using memory_grow_fail by simp
  }
next
  case (Step__data_drop x)
  then have samef: "f = f'" by (simp add: with_data.domintros with_data.psimps)
  {
    case 1
    then show ?case using samef by simp
  next
    case 2
    then show ?case using samef by simp
  next
    case 3
    then show ?case using samef store_extension_valok list_all2_mono 
      by (metis (mono_tags, lifting) Extend_store.simps)
  }
qed

lemma mk_uN_proj_uN_0:
  shows "mk_uN (proj_uN_0 k) = k" 
proof (cases k)
  case (mk_uN x)
  then show ?thesis using proj_uN_0.domintros proj_uN_0.psimps by simp
qed

lemma mk_list_proj_list_0:
  shows "mk_list (proj_list_0 l) = l"
proof (cases l)
  case (mk_list x)
  then show ?thesis using proj_list_0.domintros proj_list_0.psimps by blast
qed

(*
lemma Instrs_ok2_seq_sub:
  assumes 
      "Instrs_ok2 s C es1 (mk_functype t1a t1b)" 
      "Instrs_ok2 s C es2 (mk_functype t2a t2b)" 
      "mk_instrtype t1a t1b <ti: mk_instrtype tstart tmid" 
      "mk_instrtype t2a t2b <ti: mk_instrtype tmid tend" 
    shows "Instrs_ok2 s C (es1 @ es2) (mk_functype tstart tend)"
*)

lemma e_preservation:
  assumes "Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
          "Store_ok s"
          "Store_ok s'"
	        "Extend_store s s'"
          "Moduleinst_ok s (frame_MODULE f) C"
          "Moduleinst_ok s' (frame_MODULE f) C"
          "t_inst_match C C'"
          "list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s v t)) (context_LOCALS C') (LOCALS f)"
          "Instrs_ok2 s C' es tf"

shows
          "Instrs_ok2 s' C' es' tf"
proof (cases tf)
  case (mk_functype t1 t3)
  show ?thesis 
  using assms mk_functype
proof (induction "mk_config (mk_state s f) es" "mk_config (mk_state s' f') es'" 
    arbitrary: s f es s' f' es' tf t1 t3 rule:Step.induct)
  case (pure es0 es1)
  then show ?case 
  proof (induction rule:Step_pure.induct)
    case Step_pure__unreachable
    then have wfs: "wf_store s" "wf_context C'" using Instrs_ok2_wf by auto
    then show ?case 
         using Instrs_ok2__instr admininstr_case_73 mk_functype Instr_ok2__trap res_list.exhaust
         by (metis wfs(1) Instrs_ok2__instr admininstr_case_73 wfs(2) Instr_ok2__trap 
             res_list.exhaust pure.prems(9))
  next
    case Step_pure__nop
    obtain t1' t2' where 
      "Instr_ok2 s C' (admininstr_sc0 admininstr_st0_NOP) (mk_functype t1' t2')" 
      and sub: "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using Step_pure__nop(8,9) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc0 NOP) (mk_functype t1' t2')"            
      using inv_plain[where ?v_instr = "instr_sc0 NOP"]
      using admininstr_instr.domintros(1) admininstr_instr.psimps(1) 
      by simp
    then show ?case 
      using Instrs_ok2_subtyping
            Instrs_ok2__empty Instrs_ok2_wf(1,2) pure.prems(8,9)
            inv_nop instr_ok_instrs_ok instr_case_0
            sub by blast
  next
    case (Step_pure__drop v_val)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_val v_val] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 admininstr_st0_DROP] (mk_functype t2 t3)"
      using inv_seq[of s C' "[admininstr_val v_val, admininstr_sc0 admininstr_st0_DROP]"
              t1 t3 "[admininstr_val v_val]" "[admininstr_sc0 admininstr_st0_DROP]"] by fastforce
    have tv: "mk_instrtype (mk_list []) (mk_list [typeofval v_val]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[v_val]"] by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
      and "Instr_ok2 s C' (admininstr_sc0 admininstr_st0_DROP) (mk_functype t2'' t3'')" 
      using Step_pure__drop(9) splitih(2)
         inv_one_admininstr 
      by blast
    then have "Instr_ok C' (instr_sc0 DROP) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc0 DROP"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain t where 
      "mk_functype (mk_list [t]) (mk_list []) = mk_functype t2'' t3''"
      using inv_drop by blast
    then have "mk_instrtype (mk_list []) (mk_list []) <ti: mk_instrtype t1 t3" 
      using td tv Instrtype_sub_trans produce_consume[of 
           "[typeofval v_val]" t1 t2 "[]" "[t]" "[]"] 
      by fastforce
    then show ?case 
      using Instrs_ok2_subtyping 
            Instrs_ok2__empty Instrs_ok2_wf(1,2) pure.prems(8,9) 
      by fast
  next
    case (select_true c val_1 val_2 t_lst_opt)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_val val_1, admininstr_val val_2, 
                        admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_, admininstr_sc0 _]"
              t1 t3 "[admininstr_val _,_,_]" "[admininstr_sc0 _]"] by fastforce
    obtain t2v where splitval1:
      "Instrs_ok2 s C' [admininstr_val val_1] (mk_functype t1 t2v)"
      "Instrs_ok2 s C' [admininstr_val val_2, admininstr_sc1 (admininstr_st1_CONST I32 c)] 
              (mk_functype t2v t2)" 
      using inv_seq[OF splitih(1), of "[_]" "[_,_]"] by fastforce
   
    have tv: "mk_instrtype (mk_list []) 
              (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_1,val_2,val_CONST I32 c]"] 
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps 
       by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
        "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)) 
              (mk_functype t2'' t3'')"
      using select_true(9) splitih(2) inv_one_admininstr by blast
    then have
       td': "Instr_ok C' (instr_sc0 (SELECT t_lst_opt)) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc0 _"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then show ?case 
    proof (cases t_lst_opt)
      case None
      then obtain t v_numtype v_vectype t' where
       "Valtype_sub t t'"
       "(t' = valtype_numtype v_numtype \<or> t' = valtype_vectype v_vectype)"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) = 
        mk_functype t2'' t3''"
        using td' inv_select_impl by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2 "[]"  
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by force
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_1) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_1]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_1]) <ti:
              mk_instrtype t1 t3" 
        using subs 
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval1(1) 
            Instrs_ok2_const_replace[of s C' "[val_1]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    next
      case (Some ts)
       then obtain t where "ts = [t]"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) = 
        mk_functype t2'' t3''"
        using td' inv_select_expl by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2  "[]" 
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by force
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_1) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_1]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_1]) <ti:
              mk_instrtype t1 t3" 
        using subs
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval1(1) 
            Instrs_ok2_const_replace[of s C' "[val_1]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    qed
  next
    case (select_false c val_1 val_2 t_lst_opt)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_val val_1, admininstr_val val_2, 
                        admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_,_, admininstr_sc0 _]"
              t1 t3 "[admininstr_val _,_,_]" "[admininstr_sc0 _]"] by fastforce
    obtain t2v where splitval1:
      "Instrs_ok2 s C' [admininstr_val val_1] (mk_functype t1 t2v)"
      "Instrs_ok2 s C' [admininstr_val val_2, admininstr_sc1 (admininstr_st1_CONST I32 c)] 
              (mk_functype t2v t2)" 
      using inv_seq[OF splitih(1), of "[_]" "[_,_]"] by fastforce
    then obtain t1v' t2v' where splitval2:
      "Instrs_ok2 s C' [admininstr_val val_2] (mk_functype t1v' t2v')"
      using inv_seq[OF splitval1(2), of "[_]" "[_]"] by fastforce
    have tv: "mk_instrtype (mk_list []) 
              (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) <ti: mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_1,val_2,val_CONST I32 c]"] 
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps 
       by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
       "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_SELECT t_lst_opt)) (mk_functype t2'' t3'')" 
      using inv_one_admininstr select_false(9) splitih(2) by blast
    then have
      td': "Instr_ok C' (instr_sc0 (SELECT t_lst_opt)) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc0 _"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then show ?case 
    proof (cases t_lst_opt)
      case None
      then obtain t v_numtype v_vectype t' where
       "Valtype_sub t t'"
       "(t' = valtype_numtype v_numtype \<or> t' = valtype_vectype v_vectype)"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) =
        mk_functype t2'' t3''"
        using td' inv_select_impl
        by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2 "[]" 
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by force
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_2) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_2]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_2]) <ti:
              mk_instrtype t1 t3" 
        using subs 
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval2(1) 
            Instrs_ok2_const_replace[of s C' "[val_2]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    next
      case (Some ts)
       then obtain t where "ts = [t]"
       "mk_functype (mk_list [t, t, valtype_I32]) (mk_list [t]) =
        mk_functype t2'' t3''"
        using td' inv_select_expl
        by blast
      then have "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3) \<and>
            Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])"
        using td(1) tv produce_consume[of 
              "[typeofval val_1 , typeofval val_2 , valtype_I32]" t1 t2 "[]" 
              "[t,t,valtype_I32]" "[t]" t3]
              Instrtype_sub_trans by fastforce
      then have 
        subs: "(mk_instrtype (mk_list []) (mk_list [t]) <ti: mk_instrtype t1 t3)"
            "Resulttype_sub (mk_list [typeofval val_1, typeofval val_2, valtype_I32]) 
                    (mk_list [t,t,valtype_I32])" by auto
      have "Valtype_sub (typeofval val_2) t" 
        using subs(2) 
      proof(induction "mk_list [typeofval val_1, typeofval val_2, valtype_I32]" 
              "mk_list [t,t,valtype_I32]" rule: Resulttype_sub.induct)
        case mk_Resulttype_sub
        then show ?case by simp 
      qed
      then have "Resulttype_sub (mk_list [typeofval val_2]) (mk_list [t])" 
        using mk_Resulttype_sub by simp
      then have "mk_instrtype (mk_list []) (mk_list [typeofval val_2]) <ti:
              mk_instrtype t1 t3" 
        using subs
        by (meson Instrtype_sub_sub_rule Instrtype_sub_trans Resulttype_sub_refl)
      then show ?thesis 
        using pure.prems(9) splitval2(1) 
            Instrs_ok2_const_replace[of s C' "[val_2]" _ C'] Instrs_ok2_subtyping Instrs_ok2_wf by auto
    qed
  next
    case (if_true c bt es1 es2)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]"
              t1 t3 "[_]" "[_]"] by fastforce
    have tv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
          mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_CONST I32 c]"] typeofval.domintros
          typeofval.psimps admininstr_val.domintros admininstr_val.psimps 
         by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
      and "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)) (mk_functype t2'' t3'')"
      using if_true(9) splitih(2) inv_one_admininstr by blast
    then have
      td': "Instr_ok C' (instr_sc7 (IFELSE bt es1 es2)) (mk_functype t2'' t3'')" 
      using inv_plain[where ?v_instr = "instr_sc7 (IFELSE bt es1 es2)"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain t1l t2l where blockhyps:
      "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
           context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
           context_LOCALS = [], LABELS = [mk_list t2l], context_RETURN = None\<rparr>"
       "Blocktype_ok C' bt (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es1 (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es2 (mk_functype (mk_list t1l) (mk_list t2l))"
       "mk_functype (mk_list (t1l @ [valtype_I32]))
        (mk_list t2l) = mk_functype  t2'' t3''"
      using inv_res_if instr_ok_instrs_ok by metis
    have sub: "mk_instrtype (mk_list t1l) (mk_list t2l) <ti: mk_instrtype t1 t3"
      using tv td blockhyps(5)
        produce_consume[of "[valtype_I32]" t1 t2 t1l "[valtype_I32]" t2l t3]
      using Instrtype_sub_sub_rule Instrtype_sub_trans by blast
    have "Instr_ok C' (instr_sc7 (BLOCK bt es1)) 
      (mk_functype (mk_list t1l) (mk_list t2l))" 
      using blockhyps block[OF blockhyps(2) blockhyps(3)] pure.prems(8)
          Instrs_ok2_wf Instrs_ok_wf instr_case_4
      by (metis Blocktype_ok.simps)
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BLOCK bt es1)]
          (mk_functype (mk_list t1l) (mk_list t2l))"
      using instr_ok2_instrs_ok2 instr_ok_instr_ok2 
          admininstr_instr.domintros admininstr_instr.psimps
        pure.prems(8) Instrs_ok2_wf by metis
    then show ?case using sub Instrs_ok2_subtyping pure.prems(9) by auto
  next
    case (if_false c bt es1 es2)
    then obtain t2 where splitih:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)] (mk_functype t2 t3)" 
      using inv_seq[of s C' "[_,_]"
              t1 t3 "[_]" "[_]"] by fastforce
    have tv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: 
          mk_instrtype t1 t2" 
      using inv_const_list[OF splitih(1), of "[val_CONST I32 c]"] typeofval.domintros
          typeofval.psimps admininstr_val.domintros admininstr_val.psimps 
         by simp
    obtain t2'' t3'' where 
      td: "mk_instrtype t2'' t3'' <ti: mk_instrtype t2 t3"
      and "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_IFELSE bt es1 es2)) (mk_functype t2'' t3'')" 
      using if_false(9) splitih(2) inv_one_admininstr by blast
      then have "Instr_ok C' (instr_sc7 (IFELSE bt es1 es2)) (mk_functype t2'' t3'')"
      using inv_plain[where ?v_instr = "instr_sc7 (IFELSE bt es1 es2)"]
      using admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain t1l t2l where blockhyps:
      "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
           context_TABLES = [], context_MEMS = [], context_ELEMS = [], context_DATAS = [],
           context_LOCALS = [], LABELS = [mk_list t2l], context_RETURN = None\<rparr>"
       "Blocktype_ok C' bt (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es1 (mk_functype (mk_list t1l) (mk_list t2l))"
       "Instrs_ok
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [],
             context_TABLES = [], context_MEMS = [], context_ELEMS = [],
             context_DATAS = [], context_LOCALS = [], LABELS = [mk_list t2l],
             context_RETURN = None\<rparr>
          C')
        es2 (mk_functype (mk_list t1l) (mk_list t2l))"
       "mk_functype (mk_list (t1l @ [valtype_I32]))
        (mk_list t2l) = mk_functype t2'' t3''"
      using inv_res_if instr_ok_instrs_ok by metis
    have sub: "mk_instrtype (mk_list t1l) (mk_list t2l) <ti: mk_instrtype t1 t3"
      using tv td blockhyps(5) 
        produce_consume[of "[valtype_I32]" t1 t2 t1l "[valtype_I32]" t2l t3]
      using Instrtype_sub_sub_rule Instrtype_sub_trans by blast
    have "Instr_ok C' (instr_sc7 (BLOCK bt es2)) 
      (mk_functype (mk_list t1l) (mk_list t2l))" 
      using blockhyps block[OF blockhyps(2) blockhyps(4)] pure.prems(8)
          Instrs_ok2_wf Instrs_ok_wf instr_case_4
      by (metis Blocktype_ok.simps)
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BLOCK bt es2)]
          (mk_functype (mk_list t1l) (mk_list t2l))"
      using instr_ok2_instrs_ok2 instr_ok_instr_ok2
        admininstr_instr.domintros admininstr_instr.psimps
        pure.prems(8) Instrs_ok2_wf
      by metis
    then show ?case using sub Instrs_ok2_subtyping pure.prems(9) by auto
  next
    case (label_vals n es vs)
    then obtain t1' t2' where 
      td: "Instr_ok2 s C' (admininstr_sc8 (LABEL_underscore n es (map admininstr_val vs)))
        (mk_functype t1' t2')"
      "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih: 
        "Instrs_ok2 s C' (map admininstr_instr es)
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
        (map admininstr_val vs) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'" 
      using inv_label by blast
    then show ?case using Instrs_ok2_const_replace td 
      by (metis Instrs_ok2_subtyping Instrs_ok2_wf(1) inv_const_list pure.prems(9))
  next
    case (br_zero n vs es' vs' es)
    then obtain t1' t2' where td:
      "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore n es'
         (((map admininstr_val vs' @ map admininstr_val vs) @
           [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
     "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih0: 
        "Instrs_ok2 s C' (map admininstr_instr es')
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
         (((map admininstr_val vs' @ map admininstr_val vs) @
           [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_instrtype (mk_list []) (mk_list ts) <ti: mk_instrtype t1 t3" 
      using inv_label by blast
    then obtain ts2 where splitih:
       "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ((map admininstr_val vs' @ map admininstr_val vs) @ 
              [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_instr es) (mk_functype ts2 (mk_list ts))"
      using inv_seq by blast 
    then obtain ts2' where splitih': 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs' @ map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') [admininstr_sc0 (admininstr_st0_BR (mk_uN 0))] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where splitih'': 
       "Instr_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (admininstr_sc0 (admininstr_st0_BR (mk_uN 0))) (mk_functype ts2'' ts3'')" 
        "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
      then have "Instr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (instr_sc0 (BR (mk_uN 0))) (mk_functype ts2'' ts3'')"
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tsbr ts1br ts2br where splitihbr:
      "proj_uN_0 (mk_uN 0) < length (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C'))"
      "proj_list_0 (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ! proj_uN_0 (mk_uN 0)) = tsbr"
      "mk_functype (mk_list (ts1br @ tsbr)) (mk_list ts2br) = mk_functype ts2'' ts3''" 
      using inv_br by presburger
    obtain t2v where splitihv:
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs') (mk_functype (mk_list []) t2v)" 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs) (mk_functype t2v ts2')"
      using inv_seq[OF splitih'(1)] by blast
    then have subvs': "mk_instrtype (mk_list []) (mk_list (map typeofval vs')) <ti: 
        mk_instrtype (mk_list []) t2v" using inv_const_list by blast
    have subvs: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti:
        mk_instrtype t2v ts2'" using inv_const_list splitihv by blast
    have typevs: "Instrs_ok2 s C' (map admininstr_val vs) 
            (mk_functype (mk_list []) (mk_list (map typeofval vs)))"
      using splitihv Instrs_ok2_const_replace splitih0 Instrs_ok2_wf by blast
    have zeq: "proj_uN_0 (mk_uN 0) = 0" using proj_uN_0.domintros proj_uN_0.psimps by simp
    have "ts' = tsbr" proof(cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
              context_ELEMS context_DATAS context_LOCALS LABELS context_RETURN)
      then have "res_context.LABELS
       (append_res_context
         \<lparr>res_context.context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
            context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
            LABELS = [mk_list ts'], context_RETURN = None\<rparr>
         C') = (mk_list ts') # LABELS" using append_res_context_def by simp
      then show ?thesis 
        using splitihbr(2) zeq 
          proj_list_0.domintros proj_list_0.psimps
        by (metis nth_Cons_0)
    qed  
    then have "Resulttype_sub (mk_list (map typeofval vs)) (mk_list ts')"
      using splitihbr(3) splitih''(2)
        Instrtype_sub_emptyl[OF subvs' subvs] 
        produce_consume_waste[of "map typeofval vs'" "map typeofval vs" "mk_list []" ts2' ts1br tsbr 
            ts2br ts2] 
        br_zero(1) splitih0(4) Instrtype_sub_trans length_map map_append 
      by (metis functype.inject inv_const_list splitih'(1)) 
    then show ?case using typevs splitih0(1,5) pure(10) Instrs_ok2__seq Instrs_ok2_subtyping
      by (meson Instrs_ok2__sub Instrs_ok2_wf(1,2) Instrs_ok2_wf_instr Resulttype_sub_empty)
  next
    case (br_succ n es' vs l es)
    then obtain t1' t2' where td:
      "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore n es'
         ((map admininstr_val vs @ [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
      "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih0: 
        "Instrs_ok2 s C' (map admininstr_instr es')
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
         (((map admininstr_val vs) @
           [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'" 
      using inv_label by blast
    then obtain ts2 where splitih:
       "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ((map admininstr_val vs) @ 
              [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_instr es) (mk_functype ts2 (mk_list ts))"
      using inv_seq by blast 
    then obtain ts2' where splitih': 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') [admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where splitih'': 
       "Instr_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (admininstr_sc0 (admininstr_st0_BR (mk_uN (proj_uN_0 l + 1)))) (mk_functype ts2'' ts3'')" 
        "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
    then have brok: "Instr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (instr_sc0 (BR (mk_uN (proj_uN_0 l + 1)))) (mk_functype ts2'' ts3'')" 
using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tsbr ts1br ts2br where splitihbr:
      "proj_uN_0 (mk_uN (proj_uN_0 l + 1)) < length (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C'))"
      "proj_list_0 (LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ! proj_uN_0 (mk_uN (proj_uN_0 l + 1))) = tsbr"
      "mk_functype (mk_list (ts1br @ tsbr)) (mk_list ts2br) = mk_functype ts2'' ts3''" 
      using inv_br by presburger
    then have proj1: "proj_uN_0 l < length (LABELS C')" 
    proof (cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
            context_ELEMS context_DATAS context_LOCALS context_LABELS context_RETURN)
      then have "LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = (mk_list ts') # context_LABELS" using append_res_context_def by simp
      then show ?thesis using splitihbr proj_uN_0.domintros proj_uN_0.psimps fields by force
    qed
    have proj2: "proj_list_0 (LABELS C' ! proj_uN_0 l) = tsbr" 
    proof (cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
            context_ELEMS context_DATAS context_LOCALS context_LABELS context_RETURN)
      then have "LABELS (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = (mk_list ts') # context_LABELS" using append_res_context_def by simp
      then show ?thesis using splitihbr proj_uN_0.domintros proj_uN_0.psimps fields by force
    qed
    have wfbr: "wf_instr (instr_sc0 (BR l))" 
      using Instr_ok_wf(2)[OF brok]
    proof (induction "instr_sc0 (BR (mk_uN (proj_uN_0 l + 1)))" rule:wf_instr.induct)
      case instr_case_7
      then show ?case
      proof(induction "mk_uN (proj_uN_0 l + 1)" rule:wf_uN.induct)
        case (uN_case_0 v_N)
        then show ?case using isabelle_reference_output_wasm2.instr_case_7[of l]
          isabelle_reference_output_wasm2.uN_case_0[of "proj_uN_0 l" "32"]
          mk_uN_proj_uN_0[of l]
          by (metis bot_nat_0.extremum le_add1 le_trans local.instr_case_7 uN.inject wf_uN.cases)
      qed
    qed
    have subvs: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
          mk_instrtype (mk_list []) ts2'" using splitih' inv_const_list by blast
    have vsok: "Instrs_ok2 s C' (map admininstr_val vs) 
          (mk_functype (mk_list []) (mk_list (map typeofval vs)))" 
      using splitih' Instrs_ok2_const_replace splitih0 Instrs_ok2_wf by blast
    have sucl: "proj_uN_0 l + 1 = Suc (proj_uN_0 l)" by auto
    have "LABELS C' ! proj_uN_0 l = mk_list tsbr"
      proof (cases "LABELS C' ! proj_uN_0 l")
      case (mk_list x)
      then show ?thesis using proj2 proj_list_0.domintros proj_list_0.psimps by metis
    qed
    then obtain vs1 vs2 where 
      "vs = vs1 @ vs2" 
      "Resulttype_sub (mk_list (map typeofval vs2)) (mk_list tsbr)"
      using inv_label_const_list_br td(1) sucl
      by metis 
    then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti:
                 mk_instrtype (mk_list []) (mk_list (map typeofval vs1 @ tsbr))" 
      using mk_Instrtype_sub Resulttype_sub_refl 
      using Instrtype_sub_sub_rule Resulttype_sub_append by simp
    then have "Instrs_ok2 s C' (map admininstr_val vs @ 
              [admininstr_sc0 (admininstr_st0_BR l)])
              (mk_functype (mk_list []) (mk_list ts)) "  
      using 
        vsok
        instr_ok2_instrs_ok2[OF
        instr_ok_instr_ok2[OF 
          br[OF proj1 proj2 Instrs_ok2_wf(1)[OF splitih0(1)] wfbr, of "map typeofval vs1" ts]
           Instrs_ok2_wf(2)[OF splitih0(1)]]]
        instrs_ok2_seq[of s C' "map admininstr_val vs" "mk_list []" 
              "mk_list (map typeofval vs1 @ tsbr)" "[_]" "mk_list ts"]
        Instrs_ok2_subtyping
      by (simp add: admininstr_instr.domintros(8) admininstr_instr.psimps(8))
    then show ?case using splitihbr(3) splitih''(2) subvs 
         br_succ(9) splitih0(5) td(2)
      using Instrs_ok2_subtyping by blast
  next
    case (br_if_true c l)
    then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR_IF l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_BR_IF l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_IF l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts where brhyps:
      "proj_uN_0 l < length (LABELS C')"
      "proj_list_0 (LABELS C' ! proj_uN_0 l) = ts"
      "mk_functype (mk_list (ts @ [valtype_I32])) (mk_list ts) = mk_functype ts2' ts3'"
      using inv_br_if by blast
    then have sub: "mk_instrtype (mk_list ts) (mk_list ts) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 ts "[valtype_I32]" ts t3]
        subv subt by fastforce
    have wfbr: "wf_instr (instr_sc0 (BR l))" 
      using Instr_ok_wf(2)[OF brifok]
    proof (induction "instr_sc0 (BR_IF l)" rule:wf_instr.induct)
      case instr_case_8
      then show ?case using instr_case_7 by simp
    qed
    show ?case using subv 
        br[OF brhyps(1) brhyps(2) Instrs_ok2_wf(1)[OF split(1)] wfbr, of "[]" ts] 
        instr_ok_instr_ok2 instr_ok2_instrs_ok2 
        Instrs_ok2_wf(2)[OF split(1)] br_if_true(11)
        Instrs_ok2_subtyping sub 
      by (metis admininstr_instr.domintros(8) admininstr_instr.psimps(8) append_Nil)
  next
    case (br_if_false c l)
 then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR_IF l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc0 (admininstr_st0_BR_IF l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_IF l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts where brhyps:
      "proj_uN_0 l < length (LABELS C')"
      "proj_list_0 (LABELS C' ! proj_uN_0 l) = ts"
      "mk_functype (mk_list (ts @ [valtype_I32])) (mk_list ts) = mk_functype ts2' ts3'"
      using inv_br_if by blast
    then have sub: "mk_instrtype (mk_list ts) (mk_list ts) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 ts "[valtype_I32]" ts t3]
        subv subt by fastforce
    have "mk_instrtype (mk_list []) (mk_list []) <ti: mk_instrtype (mk_list ts) (mk_list ts)" 
      by (metis Instrtype_sub_frame_rule append.right_neutral)
    then show ?case using Instrs_ok2__empty Instrs_ok2_wf[OF split(1)] 
      br_if_false(11) sub Instrs_ok2_subtyping by auto
  next
    case (br_table_lt c ls l)
    then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_BR_TABLE ls l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts tbef taft where brhyps:
      "list_all (\<lambda>l. proj_uN_0 l < length (LABELS C')) ls"
      "list_all (\<lambda>l. Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)) ls"
      "proj_uN_0 l < length (LABELS C')"
      "Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)"
      "mk_functype (mk_list (tbef @ ts @ [valtype_I32])) (mk_list taft) = mk_functype ts2' ts3'"
      using inv_br_table by blast  
    then have sub: "mk_instrtype (mk_list (tbef @ ts)) (mk_list taft) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 "tbef @ ts" "[valtype_I32]" taft t3]
        subv subt by fastforce
    have wfbr: "wf_instr (instr_sc0 (BR (ls ! proj_uN_0 (the (proj_num__0 c)))))" 
      using Instr_ok_wf(2)[OF brifok]
    proof (induction "instr_sc0 (BR_TABLE ls l)" rule:wf_instr.induct)
      case instr_case_9
      then show ?case using instr_case_7 
        by (simp add: br_table_lt.hyps(1) list_all_length) 
    qed
    then have brok: "Instr_ok C' (instr_sc0 (BR (ls ! proj_uN_0 (the (proj_num__0 c))))) 
                (mk_functype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c)))))) 
              (mk_list taft))" 
      using br brhyps br_table_lt(1) list_all_length Instrs_ok2_wf(1)[OF split(1)]
      by meson
    have "mk_instrtype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c)))))) 
              (mk_list taft) <ti: mk_instrtype (mk_list (tbef @ ts)) (mk_list taft)" 
      using 
        Instrtype_sub_sub_rule[of "mk_list (tbef @ ts)" "mk_list (tbef @ proj_list_0 
            (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c)))))" "mk_list taft" 
            "mk_list taft"]
        Resulttype_sub_append[OF Resulttype_sub_refl[of "mk_list tbef"], of ts 
            "proj_list_0 (LABELS C' ! proj_uN_0 (ls ! proj_uN_0 (the (proj_num__0 c))))"] 
        brhyps(2) br_table_lt(1) list_all_length Resulttype_sub_refl[of "mk_list taft"]
        mk_list_proj_list_0 by metis
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR 
              (ls ! proj_uN_0 (the (proj_num__0 c))))]
                (mk_functype (mk_list (tbef @ ts)) (mk_list taft))"
      using instr_ok_instr_ok2 instr_ok2_instrs_ok2 Instrs_ok2_subtyping brok 
        Instrs_ok2_wf(2)[OF split(1)]
      by (metis admininstr_instr.domintros(8) admininstr_instr.psimps(8))
    then show ?case using sub Instrs_ok2_subtyping br_table_lt(11)
      Instrtype_sub_sub_rule by meson
  next
    case (br_table_ge c ls l)
    then obtain t2 where split:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST I32 c)] (mk_functype t1 t2)" 
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_BR_TABLE ls l)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce 
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_I32]) <ti: mk_instrtype t1 t2"
      using inv_const_list[OF split(1), of "[val_CONST I32 c]"]
        admininstr_val.domintros admininstr_val.psimps typeofval.domintros typeofval.psimps
      by simp
    obtain ts2' ts3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      and subt: "mk_instrtype ts2' ts3' <ti: mk_instrtype t2 t3" 
      using split inv_one_admininstr by blast
    then have brifok: "Instr_ok C' (instr_sc0 (BR_TABLE ls l)) (mk_functype ts2' ts3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by simp
    then obtain ts tbef taft where brhyps:
      "list_all (\<lambda>l. proj_uN_0 l < length (LABELS C')) ls"
      "list_all (\<lambda>l. Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)) ls"
      "proj_uN_0 l < length (LABELS C')"
      "Resulttype_sub (mk_list ts) (LABELS C' ! proj_uN_0 l)"
      "mk_functype (mk_list (tbef @ ts @ [valtype_I32])) (mk_list taft) = mk_functype ts2' ts3'"
      using inv_br_table by blast  
    then have sub: "mk_instrtype (mk_list (tbef @ ts)) (mk_list taft) <ti: mk_instrtype t1 t3"
      using produce_consume[of "[valtype_I32]" t1 t2 "tbef @ ts" "[valtype_I32]" taft t3]
        subv subt by fastforce
    have wfbr: "wf_instr (instr_sc0 (BR l))" 
      using Instr_ok_wf(2)[OF brifok]
    proof (induction "instr_sc0 (BR_TABLE ls l)" rule:wf_instr.induct)
      case instr_case_9
      then show ?case using instr_case_7 by simp
    qed
    then have brok: "Instr_ok C' (instr_sc0 (BR l)) 
                (mk_functype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 l))) 
              (mk_list taft))" 
      using br brhyps Instrs_ok2_wf(1)[OF split(1)]
      by meson
    have "mk_instrtype (mk_list (tbef @  
                  proj_list_0 (LABELS C' ! proj_uN_0 l))) 
              (mk_list taft) <ti: mk_instrtype (mk_list (tbef @ ts)) (mk_list taft)" 
      using 
        Instrtype_sub_sub_rule[of "mk_list (tbef @ ts)" "mk_list (tbef @ proj_list_0 
            (LABELS C' ! proj_uN_0 l))" "mk_list taft" 
            "mk_list taft"]
        Resulttype_sub_append[OF Resulttype_sub_refl[of "mk_list tbef"], of ts 
            "proj_list_0 (LABELS C' ! proj_uN_0 l)"] 
        brhyps(4) Resulttype_sub_refl[of "mk_list taft"]
        mk_list_proj_list_0 by metis
    then have "Instrs_ok2 s C' [admininstr_sc0 (admininstr_st0_BR 
              l)]
                (mk_functype (mk_list (tbef @ ts)) (mk_list taft))"
      using instr_ok_instr_ok2 instr_ok2_instrs_ok2 Instrs_ok2_subtyping brok 
        Instrs_ok2_wf(2)[OF split(1)]
      by (metis admininstr_instr.domintros(8) admininstr_instr.psimps(8))
    then show ?case using sub Instrs_ok2_subtyping br_table_ge(11)
      Instrtype_sub_sub_rule by meson
  next
    case (frame_vals n vs f)
    then obtain ts1 ts2 where 
      "Instr_ok2 s C' (admininstr_sc8 (FRAME_underscore n f (map admininstr_val vs)))
          (mk_functype ts1 ts2)" 
      and sub: "mk_instrtype ts1 ts2 <ti: mk_instrtype t1 t3" 
      using inv_one_admininstr by blast
    then obtain Cf ts where invframe:
        "Frame_ok s f Cf" 
        "Expr_ok2 s Cf (map admininstr_val vs) (mk_list ts)"
        "wf_context Cf" "n = length ts" 
        "mk_functype (mk_list []) (mk_list ts) = mk_functype ts1 ts2"
      using inv_frame by blast
    then have inv:
        "Instrs_ok2 s Cf (map admininstr_val vs) (mk_functype (mk_list []) (mk_list ts))"
      using inv_expr by blast
    then show ?case using sub frame_vals(10) invframe(5) Instrs_ok2_subtyping
      by (metis Instrs_ok2_subtyping invframe(5) pure.prems(9) inv local.sub 
          inv_const_list pure.prems(8) Instrs_ok2_wf(1) Instrs_ok2_const_replace)
  next
    case (return_frame n vs f vs' es)
    then obtain t1' t2' where
      "Instr_ok2 s C' (admininstr_sc8
       (FRAME_underscore n f
         (((map admininstr_val vs' @ map admininstr_val vs) @ [admininstr_sc1 admininstr_st1_RETURN]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
      and subt: "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3" 
      using inv_one_admininstr by blast
    then obtain Cf ts where framehyps:
      "Frame_ok s f Cf"
      "Expr_ok2 s Cf (((map admininstr_val vs' @ map admininstr_val vs) @ [admininstr_sc1 admininstr_st1_RETURN]) @
          map admininstr_instr es) (mk_list ts)"
      "wf_context Cf" "n = length ts" "context_RETURN Cf = Some (mk_list ts)"
      "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'"
      using inv_frame by blast
    then have "Instrs_ok2 s Cf (((map admininstr_val vs' @ map admininstr_val vs) @ 
            [admininstr_sc1 admininstr_st1_RETURN]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))" 
      using inv_expr by blast
    then obtain ts2 where splites:
      "Instrs_ok2 s Cf ((map admininstr_val vs' @ map admininstr_val vs) @ 
            [admininstr_sc1 admininstr_st1_RETURN]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s Cf (map admininstr_instr es) (mk_functype ts2 (mk_list ts))" 
      using inv_seq by blast
    then obtain ts2' where splitret:
      "Instrs_ok2 s Cf (map admininstr_val vs' @ map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s Cf [admininstr_sc1 admininstr_st1_RETURN] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where 
      "Instr_ok2 s Cf (admininstr_sc1 admininstr_st1_RETURN) (mk_functype ts2'' ts3'')"
      and subt': "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
    then have "Instr_ok Cf (instr_sc1 RETURN) (mk_functype ts2'' ts3'')"
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tret tbef taft where rethyps:
      "context_RETURN Cf = Some (mk_list tret)"
      "mk_functype (mk_list (tbef @ tret)) (mk_list taft) = mk_functype ts2'' ts3''"
      using inv_return by blast
    then obtain tv2 where splitvs:
      "Instrs_ok2 s Cf (map admininstr_val vs') (mk_functype (mk_list []) tv2)"
      "Instrs_ok2 s Cf (map admininstr_val vs) (mk_functype tv2 ts2')" 
      using splitret inv_seq by blast
    then have subv1: "mk_instrtype (mk_list []) (mk_list (map typeofval vs')) <ti: mk_instrtype (mk_list []) tv2"
      using inv_const_list by blast
    have subv2: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: mk_instrtype tv2 ts2'"
      using splitvs inv_const_list by blast
    have subv: "mk_instrtype (mk_list []) (mk_list (map typeofval vs' @ map typeofval vs)) <ti:
      mk_instrtype (mk_list []) ts2'" using splitret(1) inv_const_list
      by (metis inv_const_list splitret(1) map_append)
    have "Resulttype_sub (mk_list (map typeofval vs)) (mk_list ts)"
      using produce_consume_waste[OF subv] rethyps subt' return_frame(1) framehyps(4,5)
      by force
    then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: mk_instrtype t1 t3" 
      using return_frame(10) subt framehyps(6) Instrtype_sub_sub_rule Resulttype_sub_refl
      using Instrtype_sub_trans by blast
    then show ?case 
      using splitvs(1) Instrs_ok2_const_replace Instrs_ok2_wf(1)[OF return_frame(9)]
      Instrs_ok2_subtyping
      using return_frame.prems(9) splitvs(2) by force
  next
    case (return_label n es' vs es)
 then obtain t1' t2' where td:
      "Instr_ok2 s C'
     (admininstr_sc8
       (LABEL_underscore n es'
         ((map admininstr_val vs @ [admininstr_sc1 (admininstr_st1_RETURN)]) @
          map admininstr_instr es))) (mk_functype t1' t2')"
      "mk_instrtype t1' t2' <ti: mk_instrtype t1 t3"
      using inv_one_admininstr by blast
    then obtain ts ts' where splitih0: 
        "Instrs_ok2 s C' (map admininstr_instr es')
        (mk_functype (mk_list ts') (mk_list ts))"
       "Instrs_ok2 s
        (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C')
         (((map admininstr_val vs) @
           [admininstr_sc1 (admininstr_st1_RETURN)]) @
          map admininstr_instr es) (mk_functype (mk_list []) (mk_list ts))"
       "wf_context
        \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
           context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
           LABELS = [mk_list ts'], context_RETURN = None\<rparr>"
       "n = length ts'" 
       "mk_functype (mk_list []) (mk_list ts) = mk_functype t1' t2'" 
      using inv_label by blast
    then obtain ts2 where splitih:
       "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') ((map admininstr_val vs) @ 
              [admininstr_sc1 (admininstr_st1_RETURN)]) (mk_functype (mk_list []) ts2)"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_instr es) (mk_functype ts2 (mk_list ts))"
      using inv_seq by blast 
    then obtain ts2' where splitih': 
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (map admininstr_val vs) (mk_functype (mk_list []) ts2')"
      "Instrs_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') [admininstr_sc1 (admininstr_st1_RETURN)] (mk_functype ts2' ts2)" 
      using inv_seq by blast
    then obtain ts2'' ts3'' where splitih'': 
       "Instr_ok2 s (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (admininstr_sc1 admininstr_st1_RETURN) (mk_functype ts2'' ts3'')" 
        "mk_instrtype ts2'' ts3'' <ti: mk_instrtype ts2' ts2"
      using inv_one_admininstr by blast
    then have brok: "Instr_ok (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') (instr_sc1 RETURN) (mk_functype ts2'' ts3'')" 
using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then obtain tsbr ts1br ts2br where splitihbr:
      "context_RETURN (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = Some (mk_list tsbr)"
      "mk_functype (mk_list (ts1br @ tsbr)) (mk_list ts2br) = mk_functype ts2'' ts3''" 
      using inv_return by blast
    have proj2: "context_RETURN C' = Some (mk_list tsbr)" 
    proof (cases C')
      case (fields context_TYPES context_FUNCS context_GLOBALS context_TABLES context_MEMS 
            context_ELEMS context_DATAS context_LOCALS context_LABELS context_RETURN)
      then have "res_context.context_RETURN (append_res_context
          \<lparr>context_TYPES = [], context_FUNCS = [], context_GLOBALS = [], context_TABLES = [],
             context_MEMS = [], context_ELEMS = [], context_DATAS = [], context_LOCALS = [],
             LABELS = [mk_list ts'], context_RETURN = None\<rparr>
          C') = res_context.context_RETURN C'" using append_res_context_def by simp
      then show ?thesis using splitihbr fields by force
    qed
    have wfbr: "wf_instr (instr_sc1 RETURN)" 
      using Instr_ok_wf(2)[OF brok] by simp
    have subvs: "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti: 
          mk_instrtype (mk_list []) ts2'" using splitih' inv_const_list by blast
    have vsok: "Instrs_ok2 s C' (map admininstr_val vs) 
          (mk_functype (mk_list []) (mk_list (map typeofval vs)))" 
      using splitih' Instrs_ok2_const_replace splitih0 Instrs_ok2_wf by blast
    then obtain vs1 vs2 where 
      "vs = vs1 @ vs2" 
      "Resulttype_sub (mk_list (map typeofval vs2)) (mk_list tsbr)"
      using inv_label_const_list_return td(1) proj2
      by metis 
    then have "mk_instrtype (mk_list []) (mk_list (map typeofval vs)) <ti:
                 mk_instrtype (mk_list []) (mk_list (map typeofval vs1 @ tsbr))" 
      using mk_Instrtype_sub Resulttype_sub_refl 
      using Instrtype_sub_sub_rule Resulttype_sub_append by simp
    then have "Instrs_ok2 s C' (map admininstr_val vs @ 
              [admininstr_sc1 (admininstr_st1_RETURN)])
              (mk_functype (mk_list []) (mk_list ts)) "  
      using 
        vsok
        instr_ok2_instrs_ok2[OF
        instr_ok_instr_ok2[OF 
          return[OF proj2 Instrs_ok2_wf(1)[OF splitih0(1)] wfbr, of "map typeofval vs1" ts]
           Instrs_ok2_wf(2)[OF splitih0(1)]]]
        instrs_ok2_seq[of s C' "map admininstr_val vs" "mk_list []" 
              "mk_list (map typeofval vs1 @ tsbr)" "[_]" "mk_list ts"]
        Instrs_ok2_subtyping
      by (simp add: admininstr_instr.domintros admininstr_instr.psimps)
    then show ?case using splitihbr(2) splitih''(2) subvs 
        return_label(9) splitih0(5) td(2)
      using Instrs_ok2_subtyping by blast
  next
    case (trap_vals val_lst instr_lst)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (trap_label v_n instr'_lst)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (trap_frame v_n f)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (unop_val nt unop c_1 c)
    then obtain t2 where splitunop:
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_CONST nt c_1)] (mk_functype t1 t2)"
      "Instrs_ok2 s C' [admininstr_sc1 (admininstr_st1_UNOP nt unop)] (mk_functype t2 t3)"
      using inv_seq[of s C' "[_,_]" t1 t3 "[_]" "[_]"] by fastforce
    have subv: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt]) <ti:
                mk_instrtype t1 t2" 
      using inv_const_list[OF splitunop(1), of "[val_CONST _ _]"] admininstr_val.domintros
        admininstr_val.psimps typeofval.domintros typeofval.psimps by simp
    obtain t2' t3' where 
      "Instr_ok2 s C' (admininstr_sc1 (admininstr_st1_UNOP nt unop)) (mk_functype t2' t3')" 
      and subt: "mk_instrtype t2' t3' <ti: mk_instrtype t2 t3" 
      using splitunop(2) inv_one_admininstr by blast
    then have "Instr_ok C' (instr_sc1 (UNOP nt unop)) (mk_functype t2' t3')" 
      using inv_plain admininstr_instr.domintros admininstr_instr.psimps by metis
    then have "mk_functype (mk_list [valtype_numtype nt]) (mk_list [valtype_numtype nt]) =
        mk_functype t2' t3'" using inv_unop by blast
    then have subt: "mk_instrtype (mk_list []) (mk_list [valtype_numtype nt]) <ti: 
                mk_instrtype t1 t3" using subv subt produce_consume by auto
    have "wf_instr (instr_sc1 (res_CONST nt c))" 
      using unop__is_wf unop_val(2) Instrs_ok2_wf_instr[OF unop_val(10)]
      by (metis Step_pure.unop_val Step_pure_is_wf admininstr_instr.domintros(14) 
          admininstr_instr.psimps(14)
          list.pred_inject(2) unop_val.hyps(1) wf_admininstr_instr_inv)
    then show ?case using unop_val(11) const instr_ok_instr_ok2 instr_ok2_instrs_ok2
      Instrs_ok2_subtyping Instrs_ok2_wf[OF unop_val(10)] subt
      by (metis admininstr_instr.domintros(14) admininstr_instr.psimps(14))
  next
    case (unop_trap nt unop c_1)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (binop_val nt binop c_1 c_2 var_0 c)
    then show ?case sorry
  next
    case (binop_trap nt binop c_1 c_2 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (Step_pure__testop c nt testop c_1)
    then show ?case sorry
  next
    case (Step_pure__relop nt relop c_1 c_2 var_0 c)
    then show ?case sorry
  next
    case (cvtop_val nt_1 nt_2 v_cvtop c_1 var_0 c)
    then show ?case sorry
  next
    case (cvtop_trap nt_1 nt_2 v_cvtop c_1 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (ref_is_null_true v_ref rt)
    then show ?case sorry
  next
    case (ref_is_null_false v_ref)
    then show ?case sorry
  next
    case (Step_pure__vvunop c v_vvunop c_1)
    then show ?case sorry
  next
    case (Step_pure__vvbinop c v_vvbinop c_1 c_2)
    then show ?case sorry
  next
    case (Step_pure__vvternop c v_vvternop c_1 c_2 c_3)
    then show ?case sorry
  next
    case (Step_pure__vvtestop c c_1)
    then show ?case sorry
  next
    case (Step_pure__vunop sh vunop c_1 var_0 c)
    then show ?case sorry
  next
    case (vunop_trap sh vunop c_1 var_0)
    then show ?case sorry
  next
    case (vbinop_val sh vbinop c_1 c_2 var_0 c)
    then show ?case sorry
  next
    case (vbinop_trap sh vbinop c_1 c_2 var_0)
    then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
  next
    case (vtestop_true ci_1_lst v_Jnn v_N c)
    then show ?case sorry
  next
    case (vtestop_false c v_Jnn v_N)
    then show ?case sorry
  next
    case (Step_pure__vrelop sh vrelop c_1 c_2 var_0 c)
    then show ?case sorry
  next
    case (Step_pure__vshiftop var_0_lst c'_lst v_Jnn v_N vshiftop v_n c_1 c)
    then show ?case sorry
  next
    case (Step_pure__vbitmask var_0_lst ci_1_lst v_Jnn v_N c ci)
    then show ?case sorry
  next
    case (Step_pure__vswizzle ci_lst v_Pnn v_M c_2 c_1 c'_lst c)
    then show ?case sorry
  next
    case (Step_pure__vshuffle v_Pnn c'_lst v_N c_1 c_2 i_lst c)
    then show ?case sorry
  next
    case (Step_pure__vsplat c v_Lnn v_N c_1)
    then show ?case sorry
  next
    case (vextract_lane_num i nt v_N c_1 c_2)
    then show ?case sorry
  next
    case (vextract_lane_pack c_2 pt v_N c_1 i v_sx)
    then show ?case sorry
  next
    case (Step_pure__vreplace_lane c v_Lnn v_N c_1 i c_2)
    then show ?case sorry
  next
    case (Step_pure__vextunop sh_1 sh_2 vextunop c_1 var_0 c)
    then show ?case sorry
  next
    case (Step_pure__vextbinop sh_1 sh_2 vextbinop c_1 c_2 var_0 c)
    then show ?case sorry
  next
    case (Step_pure__vnarrow ci_1_lst Jnn_1 N_1 c_1 ci_2_lst c_2 cj_1_lst Jnn_2 v_sx cj_2_lst c N_2)
    then show ?case sorry
  next
    case (vcvtop_full v_vcvtop ci_lst Lnn_1 v_M c_1 cj_lst_lst Lnn_2 c)
    then show ?case sorry
  next
    case (vcvtop_half v_vcvtop v_half ci_lst Lnn_1 M_1 c_1 M_2 cj_lst_lst Lnn_2 c)
    then show ?case sorry
  next
    case (vcvtop_zero v_vcvtop ci_lst nt_1 M_1 c_1 cj_lst_lst nt_2 M_2 c)
    then show ?case sorry
  next
    case (Step_pure__local_tee v_val x)
    then show ?case sorry
  qed

next
  case (read admininstr_lst admininstr'_lst)
  then show ?case sorry
next
  case (ctxt_label admininstr_lst admininstr'_lst v_n instr_0_lst)
  then show ?case sorry
next
  case (ctxt_frame s f' admininstr_lst s' f'' admininstr'_lst f v_n)
  then show ?case sorry
next
  case (ctxt_instrs admininstr_lst admininstr'_lst val_lst admininstr_1_lst)
  then show ?case sorry
next
  case (Step__local_set v_val x)
  then show ?case sorry
next
  case (Step__global_set v_val x)
  then show ?case sorry
next
  case (table_set_trap i x v_ref)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
next
  case (table_set_val i x v_ref)
  then show ?case sorry
next
  case (table_grow_succeed x v_n v_ref var_0 ti)
  then show ?case sorry
next
  case (table_grow_fail var_0 v_ref v_n x)
  then show ?case sorry
next
  case (Step__elem_drop x)
  then show ?case sorry
next
  case (store_num_trap i nt ao c)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
next
  case (store_num_val i nt b_lst c ao)
  then show ?case sorry
next
  case (store_pack_trap i ao v_n v_Inn c)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
next
  case (store_pack_val i v_Inn c b_lst v_n ao)
  then show ?case sorry
next
  case (vstore_oob i ao c)
  then show ?case sorry
next
  case (vstore_val i b_lst c ao)
  then show ?case sorry
next
  case (vstore_lane_oob i ao v_N c j)
  then show ?case using Instr_ok2__trap Instrs_ok2_wf admininstr_case_73 instr_ok2_instrs_ok2
      res_list.exhaust by metis
next
  case (vstore_lane_val i v_N v_Jnn v_M c j b_lst ao)
  then show ?case sorry
next
  case (memory_grow_succeed v_n var_0 mi)
  then show ?case sorry
next
  case (memory_grow_fail var_0 v_n)
  then show ?case sorry
next
  case (Step__data_drop x)
  then show ?case sorry
qed
qed 



theorem preservation:
  assumes "Config_ok cfg ts"
          "Step cfg cfg'"
  shows "Config_ok cfg' ts"
proof -

  obtain s s' f f' es es' C where cfg_is:"cfg = mk_config (mk_state s f) es"
                                         "cfg' = mk_config (mk_state s' f') es'"
                                         "State_ok (mk_state s f) C"
                                         "(Expr_ok2 s C es ts)"
                                         "(wf_context C)"
                                         "(wf_config (mk_config (mk_state s f) es))"
                                         "(wf_state (mk_state s f))"
    using assms(1) Config_ok.simps
    by (metis config.exhaust state.exhaust)

  have 7:"Store_ok s"
    using State_ok.cases cfg_is(3)
    by blast

  have "Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
    by (metis assms(2) cfg_is(1) cfg_is(2))

	have 1:"Frame_ok s f C"
	  using State_ok.cases cfg_is(3)
	  by blast

  obtain C' t_lst where C'_is:"Moduleinst_ok s (frame_MODULE f) C'"
                  "C =
        append_res_context C'
         \<lparr>context_TYPES = [],
            context_FUNCS = [],
            context_GLOBALS = [],
            context_TABLES = [],
            context_MEMS = [],
            context_ELEMS = [],
            context_DATAS = [],
            context_LOCALS = t_lst,
            LABELS = [],
            context_RETURN =
              None\<rparr>"
        "length t_lst = length (LOCALS f)"
        "list_all2 (\<lambda>t v_val. Val_ok s v_val t) t_lst (LOCALS f)"
    using Frame_ok.cases[OF 1]
    by (metis frame.select_convs(1,2))

  have 0:"Store_ok s'"
         "Extend_store s s'"
         "Moduleinst_ok s' (frame_MODULE f) C'"
    sorry
    (* should come from A's proof *)

  have 2:"context_LOCALS C = t_lst"
    using C'_is(1,2)
    unfolding Moduleinst_ok.simps append_res_context_def
    apply simp
    apply (metis res_context.select_convs(8))
    done

    have 4:"list_all2 (\<lambda>(t :: valtype) (v :: val). (Val_ok s v t)) (context_LOCALS C) (LOCALS f)"
      by (simp add: "2" C'_is(4))

    have 3:"Instrs_ok2 s C es (mk_functype (mk_list []) ts)"
      by (metis Expr_ok2.cases cfg_is(4))

    have 5:"Step (mk_config (mk_state s f) es) (mk_config (mk_state s' f') es')"
      using assms(2) cfg_is(1,2)
      by auto

    have 6:"t_inst_match C' C"
      using C'_is(2)
      unfolding append_res_context_def t_inst_match_def
      by simp

    have a:"Instrs_ok2 s' C es' (mk_functype (mk_list []) ts)"
         "list_all2 (\<lambda>t v. Val_ok s' v t) (context_LOCALS C) (LOCALS f')"
         "length (LOCALS f) = length (LOCALS f')"
         "frame_MODULE f = frame_MODULE f'"
      using e_preservation[OF 5 7 0(1) 0(2) C'_is(1) 0(3) 6 4 3]
            e_preservation_locals[OF 5 7 0(1) 0(2) C'_is(1) 0(3) 6 4 3]
      by simp_all

		have bc:"(wf_state (mk_state s' f'))"
  by (metis "5" cfg_is(6) config.inject step_wf wf_config.cases)
		  

    have c:"wf_store s'"
      by (metis bc state.inject wf_state.cases)

    have cc:"wf_context C'"
      by (fastforce intro: C'_is Moduleinst_ok.cases)

    have ccc:"length (context_LOCALS C) = length (LOCALS f')"
      by (simp add: "2" C'_is(3) a(3))

    have ccccc:"wf_frame \<lparr>LOCALS = LOCALS f', frame_MODULE = frame_MODULE f\<rparr>"
      by (metis (full_types) a(4) bc frame.surjective old.unit.exhaust state.inject
          wf_state.cases)

    have cccc:"wf_context
   \<lparr>context_TYPES = [],
      context_FUNCS = [],
      context_GLOBALS = [],
      context_TABLES = [],
      context_MEMS = [],
      context_ELEMS = [],
      context_DATAS = [],
      context_LOCALS =
        context_LOCALS C,
      LABELS = [],
      context_RETURN = None\<rparr>"
      unfolding wf_context.simps
      by auto

    have bb:"(Frame_ok s' f' C)"
      using Frame_ok.intros[OF 0(3) ccc a(2) c cc ccccc cccc]
      by (metis "2" C'_is(2) a(4) frame.surjective old.unit.exhaust)

    have b:"(State_ok (mk_state s' f') C)"
      by (simp add: "0"(1) bb bc cfg_is(5)
          mk_State_ok)


    have d:"(Expr_ok2 s' C es' ts)"
      using a(1) cfg_is(5) b
      unfolding Expr_ok2.simps
      apply simp
      using Config_ok.simps assms(1) c Instrs_ok2_wf_instr by auto

    show ?thesis
      using "5" Config_ok.simps assms(1) b bc cfg_is(1,2,5) d step_wf by auto
qed

theorem progress:
  assumes "Config_ok (mk_config s es) ts"
  shows "\<exists>cfg'. Step (mk_config s es) cfg' \<or> es = [admininstr_subcase_7 admininstr_subtype_7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)"
  sorry


end