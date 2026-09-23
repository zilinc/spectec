import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas

/-!
# TypePreservationPure

Lean port of `spectec/test-rocq/theories/type_preservation_pure.v`. Full
digest: `claude-logging/for-claude/digest_typing_lemmas_and_type_preservation_pure.md`.

Scope: type preservation ONLY for `Step_pure` (WASM's deterministic,
store-independent reduction rules — constant folding, control-flow
bookkeeping, select/if/local.tee desugaring, ref.is_null). Excludes
store-mutating instructions (→ `type_preservation.v`) and SIMD.

**Two proof obligations are genuinely incomplete in the Rocq source**
(`Admitted`, not `Qed`) and are mirrored here as `sorry` deliberately, not
as a placeholder to later fill in from first principles:
- `Step_pure__return_frame_preserves` — Rocq's proof script is entirely
  commented out, never attempted.
- `t_pure_preservation` (the master theorem) — Rocq handles all non-SIMD
  cases and stops at `(* The rest are all simd instructions *) Admitted.`

Every other lemma below has a complete Rocq proof (`Qed`) and is a
genuine target for a real Lean proof in a later pass.

Phase 1 (this file, first pass): every signature stated, proofs `sorry`.
-/

namespace TLC

/-- Rocq `type_preservation_pure.v:41` `Step_pure__nop_preserves`. -/
theorem Step_pure__nop_preserves (v_S : store) (v_C : context) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.NOP] v_ft → Step_pure [admininstr.NOP] [] →
    Instrs_ok2 v_S v_C [] v_ft := sorry

/-- Rocq `type_preservation_pure.v:55` `Step_pure__drop_preserves`. -/
theorem Step_pure__drop_preserves (v_S : store) (v_C : context) (v_val : val) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr.DROP] v_ft →
    Step_pure [admininstr_val v_val, admininstr.DROP] [] →
    Instrs_ok2 v_S v_C [] v_ft := sorry

/-- Rocq `type_preservation_pure.v:72` `Step_pure__select_preserves_helper`. -/
theorem Step_pure__select_preserves_helper (v_S : store) (v_C : context)
    (v_val_1 v_val_2 : val) (v_c : num_) (v_t : Option (List valtype)) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] v_ft →
    Instrs_ok2 v_S v_C [admininstr_val v_val_1] v_ft ∧ Instrs_ok2 v_S v_C [admininstr_val v_val_2] v_ft := sorry

/-- Rocq `type_preservation_pure.v:130` `Step_pure__select_true_preserves`. -/
theorem Step_pure__select_true_preserves (v_S : store) (v_C : context)
    (v_val_1 v_val_2 : val) (v_c : num_) (v_t : Option (List valtype)) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] v_ft →
    Step_pure [admininstr_val v_val_1, admininstr_val v_val_2, admininstr.CONST numtype.I32 v_c,
      admininstr.SELECT v_t] [admininstr_val v_val_1] →
    Instrs_ok2 v_S v_C [admininstr_val v_val_1] v_ft := sorry

/-- Rocq `type_preservation_pure.v:140` `Step_pure__select_false_preserves`. -/
theorem Step_pure__select_false_preserves (v_S : store) (v_C : context)
    (v_val_1 v_val_2 : val) (v_c : num_) (v_t : Option (List valtype)) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] v_ft →
    Step_pure [admininstr_val v_val_1, admininstr_val v_val_2, admininstr.CONST numtype.I32 v_c,
      admininstr.SELECT v_t] [admininstr_val v_val_2] →
    Instrs_ok2 v_S v_C [admininstr_val v_val_2] v_ft := sorry

/-- Rocq `type_preservation_pure.v:150` `Step_pure__if_preserves_helper`. -/
theorem Step_pure__if_preserves_helper (v_S : store) (v_C : context) (v_c : num_) (v_bt : blocktype)
    (v_instrs_1 v_instrs_2 : List instr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] v_ft →
    Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_1] v_ft ∧
      Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_2] v_ft := sorry

/-- Rocq `type_preservation_pure.v:170` `Step_pure__if_true_preserves`. -/
theorem Step_pure__if_true_preserves (v_S : store) (v_C : context) (v_c : num_) (v_bt : blocktype)
    (v_instrs_1 v_instrs_2 : List instr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2]
      [admininstr.BLOCK v_bt v_instrs_1] →
    Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_1] v_ft := sorry

/-- Rocq `type_preservation_pure.v:180` `Step_pure__if_false_preserves`. -/
theorem Step_pure__if_false_preserves (v_S : store) (v_C : context) (v_c : num_) (v_bt : blocktype)
    (v_instrs_1 v_instrs_2 : List instr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2]
      [admininstr.BLOCK v_bt v_instrs_2] →
    Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_2] v_ft := sorry

/-- Rocq `type_preservation_pure.v:190` `Step_pure__label_vals_preserves`. -/
theorem Step_pure__label_vals_preserves (v_S : store) (v_C : context) (v_n : n) (v_instrs : List instr)
    (v_val : List val) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.LABEL_ v_n v_instrs (v_val.map admininstr_val)] v_ft →
    Step_pure [admininstr.LABEL_ v_n v_instrs (v_val.map admininstr_val)] (v_val.map admininstr_val) →
    Instrs_ok2 v_S v_C (v_val.map admininstr_val) v_ft := sorry

/-- Rocq `type_preservation_pure.v:210` `Step_pure__br_zero_preserves`. NOTE: Rocq's
    statement takes only the typing hypothesis + length side-condition, not an explicit
    `Step_pure` premise — the reduction fact itself isn't needed for the proof. -/
theorem Step_pure__br_zero_preserves (v_S : store) (v_C : context) (v_n : n) (v_instr' : List instr)
    (v_val' v_val : List val) (v_admininstr : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.LABEL_ v_n v_instr'
      ((((v_val'.map admininstr_val) ++ (v_val.map admininstr_val)) ++ [admininstr.BR (uN.mk_uN 0)]) ++ v_admininstr)] v_ft →
    v_val.length = v_n →
    Instrs_ok2 v_S v_C ((v_val.map admininstr_val) ++ (v_instr'.map admininstr_instr)) v_ft := sorry

/-- Rocq `type_preservation_pure.v:241` `Step_pure__br_succ_preserves`. Longest/most
    involved lemma in the Rocq file (~80 lines). -/
theorem Step_pure__br_succ_preserves (v_S : store) (v_C : context) (v_n : n) (v_instr' : List instr)
    (v_val : List val) (v_l : labelidx) (v_admininstr : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.LABEL_ v_n v_instr'
      (((v_val.map admininstr_val) ++ [admininstr.BR (uN.mk_uN ((proj_uN_0 v_l) + 1))]) ++ v_admininstr)] v_ft →
    Step_pure [admininstr.LABEL_ v_n v_instr'
      (((v_val.map admininstr_val) ++ [admininstr.BR (uN.mk_uN ((proj_uN_0 v_l) + 1))]) ++ v_admininstr)]
      ((v_val.map admininstr_val) ++ [admininstr.BR v_l]) →
    Instrs_ok2 v_S v_C ((v_val.map admininstr_val) ++ [admininstr.BR v_l]) v_ft := sorry

/-- Rocq `type_preservation_pure.v:322` `Step_pure__br_if_true_preserves`. -/
theorem Step_pure__br_if_true_preserves (v_S : store) (v_C : context) (v_c : num_) (v_l : labelidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l] [admininstr.BR v_l] →
    Instrs_ok2 v_S v_C [admininstr.BR v_l] v_ft := sorry

/-- Rocq `type_preservation_pure.v:355` `Step_pure__br_if_false_preserves`. -/
theorem Step_pure__br_if_false_preserves (v_S : store) (v_C : context) (v_c : num_) (v_l : labelidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l] [] →
    Instrs_ok2 v_S v_C [] v_ft := sorry

/-- Rocq `type_preservation_pure.v:383` `proj_identity`. Small helper (round-trip through
    the `list` wrapper constructor). -/
theorem proj_identity (a : resulttype) : list.mk_list (proj_list_0 valtype a) = a := sorry

/-- Rocq `type_preservation_pure.v:389` `Step_pure__br_table_lt_preserves`. One of the
    longest lemmas (~70 lines): `Forall_nth`, manual `instrtype_sub_trans` chaining. -/
theorem Step_pure__br_table_lt_preserves (v_S : store) (v_C : context) (v_i : num_)
    (v_l : List labelidx) (v_l' : labelidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_i, admininstr.BR_TABLE v_l v_l'] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_i, admininstr.BR_TABLE v_l v_l']
      [admininstr.BR (v_l[(proj_uN_0 (Option.get! (proj_num__0 v_i)))]!)] →
    (proj_uN_0 (Option.get! (proj_num__0 v_i))) < v_l.length →
    Instrs_ok2 v_S v_C [admininstr.BR (v_l[(proj_uN_0 (Option.get! (proj_num__0 v_i)))]!)] v_ft := sorry

/-- Rocq `type_preservation_pure.v:458` `Step_pure__br_table_ge_preserves`. Dual/default-
    target case. -/
theorem Step_pure__br_table_ge_preserves (v_S : store) (v_C : context) (v_i : num_)
    (v_l : List labelidx) (v_l' : labelidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_i, admininstr.BR_TABLE v_l v_l'] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_i, admininstr.BR_TABLE v_l v_l'] [admininstr.BR v_l'] →
    v_l.length ≤ (proj_uN_0 (Option.get! (proj_num__0 v_i))) →
    Instrs_ok2 v_S v_C [admininstr.BR v_l'] v_ft := sorry

/-- Rocq `type_preservation_pure.v:501` `Step_pure__frame_vals_preserves`. Uses
    `construct_ais_vals'` (context-irrelevance) to cross the frame boundary. -/
theorem Step_pure__frame_vals_preserves (v_S : store) (v_C : context) (v_n : n) (v_f : frame)
    (v_val : List val) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.FRAME_ v_n v_f (v_val.map admininstr_val)] v_ft →
    Step_pure [admininstr.FRAME_ v_n v_f (v_val.map admininstr_val)] (v_val.map admininstr_val) →
    Instrs_ok2 v_S v_C (v_val.map admininstr_val) v_ft := sorry

/-- Rocq `type_preservation_pure.v:517` `Step_pure__return_frame_preserves`. **`Admitted`
    in Rocq — proof script entirely commented out, genuinely never attempted.** Kept as
    `sorry` deliberately, mirroring the Rocq gap rather than inventing a proof. -/
theorem Step_pure__return_frame_preserves (v_S : store) (v_C : context) (v_n : n) (v_f : frame)
    (v_val' v_val : List val) (v_admininstr : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.FRAME_ v_n v_f
      ((((v_val'.map admininstr_val) ++ (v_val.map admininstr_val)) ++ [admininstr.RETURN]) ++ v_admininstr)] v_ft →
    Step_pure [admininstr.FRAME_ v_n v_f
      ((((v_val'.map admininstr_val) ++ (v_val.map admininstr_val)) ++ [admininstr.RETURN]) ++ v_admininstr)]
      (v_val.map admininstr_val) →
    v_val.length = v_n →
    Instrs_ok2 v_S v_C (v_val.map admininstr_val) v_ft := sorry

/-- Rocq `type_preservation_pure.v:577` `Step_pure__return_label_preserves`. Fully proved
    in Rocq (unlike the `_frame_` sibling above). RETURN propagates outward through an
    enclosing label unchanged. -/
theorem Step_pure__return_label_preserves (v_S : store) (v_C : context) (v_n : n) (v_instr' : List instr)
    (v_val : List val) (v_admininstr : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.LABEL_ v_n v_instr'
      (((v_val.map admininstr_val) ++ [admininstr.RETURN]) ++ v_admininstr)] v_ft →
    Step_pure [admininstr.LABEL_ v_n v_instr' (((v_val.map admininstr_val) ++ [admininstr.RETURN]) ++ v_admininstr)]
      ((v_val.map admininstr_val) ++ [admininstr.RETURN]) →
    Instrs_ok2 v_S v_C ((v_val.map admininstr_val) ++ [admininstr.RETURN]) v_ft := sorry

/-- Rocq `type_preservation_pure.v:619` `Step_pure__unop_val_preserves`. NOTE: takes
    `wf_admininstr` of the *result* constant as an extra hypothesis (not derived —
    presumably from a `Step_pure_is_wf`-style companion fact). -/
theorem Step_pure__unop_val_preserves (v_S : store) (v_C : context) (v_t : numtype) (v_c_1 : num_)
    (v_unop : unop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.UNOP v_t v_unop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.UNOP v_t v_unop] [admininstr.CONST v_t v_c] →
    wf_admininstr (admininstr.CONST v_t v_c) →
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c] v_ft := sorry

/-- Rocq `type_preservation_pure.v:646` `Step_pure__binop_val_preserves`. -/
theorem Step_pure__binop_val_preserves (v_S : store) (v_C : context) (v_t : numtype)
    (v_c_1 v_c_2 : num_) (v_binop : binop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.BINOP v_t v_binop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.BINOP v_t v_binop]
      [admininstr.CONST v_t v_c] →
    wf_admininstr (admininstr.CONST v_t v_c) →
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c] v_ft := sorry

/-- Rocq `type_preservation_pure.v:680` `Step_pure__testop_preserves`. -/
theorem Step_pure__testop_preserves (v_S : store) (v_C : context) (v_t : numtype) (v_c_1 : num_)
    (v_testop : testop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.TESTOP v_t v_testop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.TESTOP v_t v_testop] [admininstr.CONST numtype.I32 v_c] →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c] v_ft := sorry

/-- Rocq `type_preservation_pure.v:708` `Step_pure__relop_preserves`. -/
theorem Step_pure__relop_preserves (v_S : store) (v_C : context) (v_t : numtype) (v_c_1 v_c_2 : num_)
    (v_relop : relop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.RELOP v_t v_relop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.RELOP v_t v_relop]
      [admininstr.CONST numtype.I32 v_c] →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c] v_ft := sorry

/-- Rocq `type_preservation_pure.v:742` `Step_pure__cvtop_val_preserves`. -/
theorem Step_pure__cvtop_val_preserves (v_S : store) (v_C : context) (v_t_1 v_t_2 : numtype) (v_c_1 : num_)
    (v_cvtop : cvtop__) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t_1 v_c_1, admininstr.CVTOP v_t_2 v_t_1 v_cvtop] v_ft →
    Step_pure [admininstr.CONST v_t_1 v_c_1, admininstr.CVTOP v_t_2 v_t_1 v_cvtop] [admininstr.CONST v_t_2 v_c] →
    Instrs_ok2 v_S v_C [admininstr.CONST v_t_2 v_c] v_ft := sorry

/-- Rocq `type_preservation_pure.v:770` `Step_pure__local_tee_preserves`. -/
theorem Step_pure__local_tee_preserves (v_S : store) (v_C : context) (v_val : val) (v_x : localidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr.LOCAL_TEE v_x] v_ft →
    Step_pure [admininstr_val v_val, admininstr.LOCAL_TEE v_x]
      [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET v_x] →
    Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET v_x] v_ft := sorry

/-- Rocq `type_preservation_pure.v:816` `Step_pure__ref_is_null_helper`. Generic over the
    Boolean result (works for either 0 or 1). -/
theorem Step_pure__ref_is_null_helper (v_S : store) (v_C : context) (v_rt : reftype) (v_ft : functype) (v_n : Nat) :
    Instrs_ok2 v_S v_C [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL] v_ft →
    Step_pure [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL]
      [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))] →
    (v_n = 1 ∨ v_n = 0) →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))] v_ft := sorry

/-- Rocq `type_preservation_pure.v:848` `Step_pure__ref_is_null_true_preserves`.
    Specializes the helper above with `v_n := 1`. -/
theorem Step_pure__ref_is_null_true_preserves (v_S : store) (v_C : context) (v_rt : reftype) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL] v_ft →
    Step_pure [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL]
      [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))] →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))] v_ft := sorry

/-- Rocq `type_preservation_pure.v:857` `Step_pure__ref_is_null_false_preserves`.
    Case-splits on the 3 `ref` constructors (REF_NULL delegates to the helper above;
    REF_FUNC_ADDR/REF_HOST_ADDR each get their own hand proof in Rocq). -/
theorem Step_pure__ref_is_null_false_preserves (v_S : store) (v_C : context) (v_ref : ref) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_ref v_ref, admininstr.REF_IS_NULL] v_ft →
    Step_pure [admininstr_ref v_ref, admininstr.REF_IS_NULL]
      [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))] →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))] v_ft := sorry

/-- Rocq `type_preservation_pure.v:913` `t_pure_preservation` — the master theorem for
    this file. **`Admitted` in Rocq**: every non-SIMD `Step_pure` case is dispatched to one
    of the 26 non-admitted lemmas above (`local_tee` included); the SIMD cases (`(* The
    rest are all simd instructions *)`) are never handled. Kept as `sorry` here,
    deliberately mirroring the Rocq gap. -/
theorem t_pure_preservation (v_s : store) (v_ais v_ais' : List admininstr) (v_C : context) (tf : functype) :
    Instrs_ok2 v_s v_C v_ais tf → Step_pure v_ais v_ais' → Instrs_ok2 v_s v_C v_ais' tf := sorry

end TLC
