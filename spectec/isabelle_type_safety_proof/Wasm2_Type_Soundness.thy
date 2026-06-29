theory Wasm2_Type_Soundness
(* Imported Code *)
	imports isabelle_reference_output_wasm2 store_extension_typing
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
proof (induction "mk_config (mk_state s f) es" "mk_config (mk_state s' f') es'" arbitrary: es es' f f' tf rule: Step.induct)
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
  then have ok: "Instrs_ok2 s C' es0 tf" sorry (* inversion lemma on labels *)
  {
    case 1 
    then show ?case using ok ctxt_label by simp
  next
    case 2
    then show ?case using ok ctxt_label by simp
  next
    case 3
    then show ?case using ok ctxt_label by simp
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
    then show ?case using Step__local_set sorry (* with_local implies same length *)
  next
    case 2
    then show ?case using Step__local_set using with_local.domintros with_local.psimps by auto 
  next
    case 3
    then show ?case using Step__local_set sorry (* with_local and typechecks implies all typecheck *)
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
  sorry

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