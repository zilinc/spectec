 theory Context_Store_Agreement
	imports Main isabelle_reference_output_wasm2 
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



lemma blocktype_ok_agree:
  assumes "Blocktype_ok C' bt tf"
    "Moduleinst_ok s (frame_MODULE f) C"
    "t_inst_match C C'"
  shows "fun_blocktype (mk_state s f) bt = tf"
  using assms
proof(induction C' bt tf rule:Blocktype_ok.induct)
  case (Blocktype_ok__valtype C valtype_opt)
  then show ?case 
  proof (cases valtype_opt)
    case None
    then show ?thesis using Blocktype_ok__valtype fun_blocktype.domintros 
       fun_blocktype.psimps by auto
  next
    case (Some a)
    then show ?thesis using Blocktype_ok__valtype fun_blocktype.domintros
fun_blocktype.psimps by auto
  qed
next
  case (Blocktype_ok__typeidx v_typeidx C' t_1_lst t_2_lst)
  then have sametypes: "context_TYPES C' = context_TYPES C" using t_inst_match_def by simp
  show ?case using Blocktype_ok__typeidx(5,1,2,3,4,6) fun_blocktype.domintros(3) fun_blocktype.psimps(3)
      fun_type.domintros fun_type.psimps sametypes
  proof (induction s "frame_MODULE f" C rule:Moduleinst_ok.induct)
    case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
          functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
          dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
    then have "TYPES (frame_MODULE f) ! proj_uN_0 v_typeidx = context_TYPES C' ! proj_uN_0 v_typeidx"
      by (metis moduleinst.select_convs(1) res_context.select_convs(1))
    then show ?case using mk_Moduleinst_ok by metis
  qed
qed

lemma list_all2_nth:
  assumes "list_all2 P l1 l2" "l1 ! k = x1" "l2 ! k = x2" "k < length l1"
  shows "P x1 x2" 
  using assms 
proof (induction l1 arbitrary: l2 k)
  case Nil 
  then show ?case
    by simp
  note outer = Nil
next
  case (Cons a l1)
  note outer = Cons
  then show ?case 
  proof (cases l2)
    case Nil
    then show ?thesis using outer by simp
  next
    case (Cons b list)
    then show ?thesis 
    proof (cases k)
      case 0
      then show ?thesis using outer Cons by simp
    next
      case (Suc nat)
      then show ?thesis using outer Cons by auto
    qed
  qed
qed

lemma context_types_agree:
  assumes "Moduleinst_ok s (frame_MODULE f) C" 
          "t_inst_match C C'"
        shows "context_TYPES C' ! proj_uN_0 x = fun_type (mk_state s f) x"
  using assms proof(induction s "frame_MODULE f" C rule:Moduleinst_ok.induct)
  case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
          functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
          dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
  then show ?case using t_inst_match_def fun_type.psimps fun_type.domintros 
    by (metis moduleinst.select_convs(1) res_context.select_convs(1))
qed

lemma context_funcs_agree:
  assumes "context_FUNCS C' ! x = tf" 
          "x < length (context_FUNCS C')"
          "fun_funcaddr (mk_state s f) ! x = y"
          "wf_store s" 
          "Moduleinst_ok s (frame_MODULE f) C" 
          "t_inst_match C C'"
        shows "Externaddr_ok s (externaddr_FUNC y) (FUNC tf)"
proof - 
  have eqfuncs: "context_FUNCS C' = context_FUNCS C" using assms t_inst_match_def by simp
  show ?thesis using assms(5,1,2,3,4,6) eqfuncs
    proof (induction s "frame_MODULE f" C rule:Moduleinst_ok.induct)
      case (mk_Moduleinst_ok functype_lst globaladdr_lst globaltype_lst s funcaddr_lst 
              functype_F_lst memaddr_lst memtype_lst tableaddr_lst tabletype_lst exportinst_lst 
              dataaddr_lst datatype_lst elemaddr_lst elemtype_lst)
      show ?case using mk_Moduleinst_ok(30,27,28,29,33) fun_funcaddr.psimps fun_funcaddr.domintros
        list_all2_nth[OF mk_Moduleinst_ok(5)]
        by (metis mk_Moduleinst_ok.hyps(4) moduleinst.select_convs(2) res_context.select_convs(2))
    qed
  qed

end