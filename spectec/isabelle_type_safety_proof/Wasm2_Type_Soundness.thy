theory Wasm2_Type_Soundness
(* Imported Code *)
	imports isabelle_reference_output_wasm2 store_extension_typing Properties_Aux
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

lemma step_wf: "Step_is_wf cfg cfg'"
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
    using instr_ok_inversion
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
  using assms
proof (induction "mk_config (mk_state s f) es" "mk_config (mk_state s' f') es'" 
    arbitrary: s f es s' f' es' tf rule:Step.induct)
  case (pure es0 es1)
  then show ?case 
  proof (induction rule:Step_pure.induct)
    case Step_pure__unreachable
    then show ?case 
      using Instrs_ok2__instr Instr_ok2__trap pure inv_unreachable
      sorry
  next
    case Step_pure__nop
    then show ?case 
      using inv_nop Instrs_ok2__instr plain nop
      sorry
  next
    case (Step_pure__drop v_val)
    then show ?case sorry
  next
    case (select_true c val_1 val_2 t_lst_opt)
    then show ?case sorry
  next
    case (select_false c val_1 val_2 t_lst_opt)
    then show ?case sorry
  next
    case (if_true c bt instr_1_lst instr_2_lst)
    then show ?case sorry
  next
    case (if_false c bt instr_1_lst instr_2_lst)
    then show ?case sorry
  next
    case (label_vals v_n instr_lst val_lst)
    then show ?case sorry
  next
    case (br_zero v_n val_lst instr'_lst val'_lst instr_lst)
    then show ?case sorry
  next
    case (br_succ v_n instr'_lst val_lst l instr_lst)
    then show ?case sorry
  next
    case (br_if_true c l)
    then show ?case sorry
  next
    case (br_if_false c l)
    then show ?case sorry
  next
    case (br_table_lt i l_lst l')
    then show ?case sorry
  next
    case (br_table_ge i l_lst l')
    then show ?case sorry
  next
    case (frame_vals v_n val_lst f)
    then show ?case sorry
  next
    case (return_frame v_n val_lst f val'_lst instr_lst)
    then show ?case sorry
  next
    case (return_label v_n instr'_lst val_lst instr_lst)
    then show ?case sorry
  next
    case (trap_vals val_lst instr_lst)
    then show ?case sorry
  next
    case (trap_label v_n instr'_lst)
    then show ?case sorry
  next
    case (trap_frame v_n f)
    then show ?case sorry
  next
    case (unop_val nt unop c_1 c)
    then show ?case sorry
  next
    case (unop_trap nt unop c_1)
    then show ?case sorry
  next
    case (binop_val nt binop c_1 c_2 var_0 c)
    then show ?case sorry
  next
    case (binop_trap nt binop c_1 c_2 var_0)
    then show ?case sorry
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
    then show ?case sorry
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
    then show ?case sorry
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
  then show ?case sorry
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
  then show ?case sorry
next
  case (store_num_val i nt b_lst c ao)
  then show ?case sorry
next
  case (store_pack_trap i ao v_n v_Inn c)
  then show ?case sorry
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
  then show ?case sorry
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
    by (metis Step_is_wf.cases step_wf)

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
		  by (metis Step_is_wf.cases config.inject step_wf wf_config.cases)

    have c:"wf_store s'"
      by (metis bc state.inject wf_state.cases)

(* UH OH! *)
(* Derived "False" from these facts alone: "0"(1) "0"(2) "0"(3) "2" "3" "6" "7" C'_is(1) C'_is(3) C'_is(4) Ex_list_of_length Step_is_wf.cases a(4) admininstr_subtype_8.size_neq e_preservation_locals(1) frame.cases frame.ext_inject frame.surjective list_all2_mono step_wf *)
    have cc:"wf_context C'"
      by (fastforce intro: C'_is  Moduleinst_ok.cases)

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
      by (metis Step_is_wf.cases c config.inject proj_list_0.cases step_wf
          wf_config.simps)

    show ?thesis
      by (metis State_ok.cases Step_is_wf.cases d b cfg_is(2)
          mk_Config_ok proj_list_0.cases step_wf)
qed

theorem progress:
  assumes "Config_ok (mk_config s es) ts"
  shows "\<exists>cfg'. Step (mk_config s es) cfg' \<or> es = [admininstr_subcase_7 admininstr_subtype_7_TRAP] \<or> (\<exists>vs. es = map admininstr_val vs)"
  sorry


end