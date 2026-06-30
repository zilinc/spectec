theory Properties
	imports Main isabelle_reference_output_wasm2

begin

lemma func_extension_refl:
 shows "wf_funcinst g \<Longrightarrow> Extend_funcinst g g"
  apply (induction rule: wf_funcinst.induct)
  by (simp add: funcinst_case_underscore mk_Extend_funcinst)

lemma global_extension_refl:
  shows "wf_globalinst g \<Longrightarrow> Extend_globalinst g g"
  apply (induction rule: wf_globalinst.induct)
  by (metis globalinst_case_underscore globaltype.exhaust
      mk_Extend_globalinst)

lemma mem_extension_refl:
assumes "wf_meminst m"
shows "Extend_meminst m m"
proof -
obtain min maxOpt bs where m_is:"m = \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr>"
  by (metis meminst.cases memtype.exhaust limits.exhaust uN.exhaust)
have "Extend_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr> \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr>"
  proof (cases maxOpt)
    case (Some maxSize)
      then obtain max where "maxSize = mk_uN max" by (cases maxSize)
      moreover have "wf_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) maxOpt), BYTES = bs\<rparr>"
        using assms m_is by simp
      ultimately show ?thesis using Some Extend_meminst.intros[of "min" "min" "bs" "bs" "Some max"]
        by simp
  next
    case None
      have "wf_meminst \<lparr>meminst_TYPE = PAGE (mk_limits (mk_uN min) (map_option mk_uN None)), BYTES = bs\<rparr>"
        using None assms m_is by auto
      then show ?thesis using Extend_meminst.intros[of "min" "min" "bs" "bs" "None"] None
        by simp
  qed
  then show ?thesis using m_is by simp
qed

lemma tab_extension_refl:
  assumes "wf_tableinst m"
  shows   "Extend_tableinst m m"
proof -
obtain min maxOpt ref_t ref_lst where m_is: "m = \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr>"
  by (metis limits.exhaust tableinst.cases tabletype.exhaust uN.exhaust)
have "Extend_tableinst \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr> \<lparr> tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr>"
  proof (cases maxOpt)
    case (Some maxSize)
      then obtain max where "maxSize = mk_uN max" by (cases maxSize)
      moreover have "wf_tableinst \<lparr>tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) maxOpt) ref_t), REFS = ref_lst \<rparr>"
        using assms m_is by auto
      ultimately show ?thesis using Extend_tableinst.intros[of "min" "min" "ref_lst" "ref_lst" "Some max" "ref_t"]
        using Some by simp
  next
    case None
      have "wf_tableinst \<lparr>tableinst_TYPE = (mk_tabletype (mk_limits (mk_uN min) None) ref_t), REFS = ref_lst \<rparr>"
        using None assms m_is by auto
      then show ?thesis using Extend_tableinst.intros[of "min" "min" "ref_lst" "ref_lst" "None"] None
        by simp
  qed
  then show ?thesis using m_is by simp
qed

lemma elem_extension_refl:
  shows "Extend_eleminst el el"
  by (metis Extend_eleminst.simps eleminst.cases)

lemma data_extension_refl:
  shows "wf_datainst d \<Longrightarrow> Extend_datainst d d"
  by (metis Extend_datainst.simps datainst.cases)

lemma store_extension_refl:
  assumes "wf_store s"
  shows   "Extend_store s s"
  using assms func_extension_refl global_extension_refl mem_extension_refl tab_extension_refl elem_extension_refl data_extension_refl
  apply(simp add: Extend_store.simps)
  apply(induction rule: wf_store.induct)
  unfolding holds_upto_def
  apply simp+
  by (metis list_all_length)

end