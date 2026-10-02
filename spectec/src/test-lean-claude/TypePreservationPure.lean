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

/-- Rocq `type_preservation_pure.v:41` `Step_pure__nop_preserves`. Rocq's proof is a
    5-tactic-macro pipeline (`resolve_wfness`/`invert_ais_typing`/`resolve_all_pt`/
    `resolve_subtyping`/`construct_ais_typing`, all pure Ltac automation from
    `helper_tactics.v`, not ported per project convention); the underlying content is:
    `[NOP]`'s only principal type is `[]->[]` (`ai_principal_typing`'s `NOP` case), so the
    typing hypothesis reduces to `instrtype_sub([]->[])v_ft`, and `[]` types at any such
    `v_ft` via `ais_empty_typing` + `instrtype_sub_empty`. -/
theorem Step_pure__nop_preserves (v_S : store) (v_C : context) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.NOP] v_ft → Step_pure [admininstr.NOP] [] →
    Instrs_ok2 v_S v_C [] v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨t1s_sup, t2s_sub, hprincipal, hsub⟩ := ais_single_typing_inversion v_S v_C admininstr.NOP t1s t2s h
  unfold ai_principal_typing at hprincipal
  unfold mkFunctype at hprincipal
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hprincipal
  obtain ⟨e1, e2⟩ := hprincipal
  subst e1; subst e2
  have hrsub : ResulttypeSub t1s t2s := instrtype_sub_empty t1s t2s hsub
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C [admininstr.NOP] (mkFunctype t1s t2s) h
  exact (ais_empty_typing v_S v_C t1s t2s).mpr ⟨hwfC, hwfS, hrsub⟩

/-- Rocq `type_preservation_pure.v:55` `Step_pure__drop_preserves`. Rocq's `join_subtyping_eq`
    tactic step is `instrtype_sub_compose_eq` applied to the value's `[]->[t]` principal
    typing and `DROP`'s `[t']->[]` principal typing (both singleton lists, so the length
    hypothesis `[t].length=[t'].length` is `rfl`), collapsing the pipeline to `[]->[]`. -/
theorem Step_pure__drop_preserves (v_S : store) (v_C : context) (v_val : val) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr.DROP] v_ft →
    Step_pure [admininstr_val v_val, admininstr.DROP] [] →
    Instrs_ok2 v_S v_C [] v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr_val v_val, admininstr.DROP] = [admininstr_val v_val] ++ [admininstr.DROP] := rfl
  rw [heq] at h
  obtain ⟨t3s, htail, hhead⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.DROP] (admininstr_val v_val) t1s t2s h
  obtain ⟨t, hhead_sub, _⟩ := ais_single_val_typing_inversion v_S v_C v_val t1s t3s hhead
  obtain ⟨t1s_sup, t2s_sub, hdrop_principal, hdrop_sub⟩ :=
    ais_single_typing_inversion v_S v_C admininstr.DROP t3s t2s htail
  unfold ai_principal_typing at hdrop_principal
  obtain ⟨t', hdrop_eq⟩ := hdrop_principal
  unfold mkFunctype at hdrop_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hdrop_eq
  obtain ⟨e1, e2⟩ := hdrop_eq
  subst e1; subst e2
  obtain ⟨hfinal, _⟩ := instrtype_sub_compose_eq [] [t] [t'] [] t1s t3s t2s hhead_sub hdrop_sub rfl
  have hrsub : ResulttypeSub t1s t2s := instrtype_sub_empty t1s t2s hfinal
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C _ (mkFunctype t1s t2s) h
  exact (ais_empty_typing v_S v_C t1s t2s).mpr ⟨hwfC, hwfS, hrsub⟩

/-- Rocq `type_preservation_pure.v:72` `Step_pure__select_preserves_helper`. -/
theorem Step_pure__select_preserves_helper (v_S : store) (v_C : context)
    (v_val_1 v_val_2 : val) (v_c : num_) (v_t : Option (List valtype)) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] v_ft →
    Instrs_ok2 v_S v_C [admininstr_val v_val_1] v_ft ∧ Instrs_ok2 v_S v_C [admininstr_val v_val_2] v_ft := by
  intro h
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C _ (mkFunctype t1s t2s) h
  -- peel the four-instruction sequence apart
  have heq1 : [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t]
      = [admininstr_val v_val_1] ++ [admininstr_val v_val_2,
        admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] := rfl
  rw [heq1] at h
  obtain ⟨ta, h_r1, h_v1⟩ :=
    ais_seq_typing_inversion v_S v_C _ (admininstr_val v_val_1) t1s t2s h
  have heq2 : [admininstr_val v_val_2, admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t]
      = [admininstr_val v_val_2] ++ [admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] := rfl
  rw [heq2] at h_r1
  obtain ⟨tb, h_r2, h_v2⟩ :=
    ais_seq_typing_inversion v_S v_C _ (admininstr_val v_val_2) ta t2s h_r1
  have heq3 : [admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t]
      = [admininstr.CONST numtype.I32 v_c] ++ [admininstr.SELECT v_t] := rfl
  rw [heq3] at h_r2
  obtain ⟨tc, h_sel, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C _ (admininstr.CONST numtype.I32 v_c) tb t2s h_r2
  obtain ⟨tv1, hsub_v1, hvok1⟩ := ais_single_val_typing_inversion v_S v_C v_val_1 t1s ta h_v1
  obtain ⟨tv2, hsub_v2, hvok2⟩ := ais_single_val_typing_inversion v_S v_C v_val_2 ta tb h_v2
  obtain ⟨_, _, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST numtype.I32 v_c) tb tc h_const
  unfold ai_principal_typing at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  unfold mkFunctype at hconst_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tsel1, tsel2, hsel_pt, hsub_sel⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.SELECT v_t) tc t2s h_sel
  -- `SELECT`'s principal type is `[t,t,I32] -> [t]` in both the annotated and the
  -- unannotated case (the remaining annotation shapes are ruled out as `False`)
  have hsel : ∃ tt : valtype, tsel1 = [tt, tt, valtype.I32] ∧ tsel2 = [tt] := by
    rcases v_t with _ | lst
    · simp only [ai_principal_typing] at hsel_pt
      obtain ⟨tt, _, he, _, _⟩ := hsel_pt
      unfold mkFunctype at he
      simp only [functype.mk_functype.injEq, list.mk_list.injEq] at he
      exact ⟨tt, he.1, he.2⟩
    · rcases lst with _ | ⟨tt, rest⟩
      · simp only [ai_principal_typing] at hsel_pt
      · rcases rest with _ | ⟨x, rest'⟩
        · simp only [ai_principal_typing] at hsel_pt
          unfold mkFunctype at hsel_pt
          simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hsel_pt
          exact ⟨tt, hsel_pt.1, hsel_pt.2⟩
        · simp only [ai_principal_typing] at hsel_pt
  obtain ⟨tt, es1, es2⟩ := hsel
  subst es1; subst es2
  -- compose the four subtyping steps
  have hc1 : instrtype_sub (mkFunctype [] ([tv1] ++ [tv2])) (mkFunctype t1s tb) :=
    (instrtype_sub_compose_ge [] [tv1] [] [] [tv2] t1s ta tb (by simpa using hsub_v1) hsub_v2 rfl).1
  have hc2 : instrtype_sub (mkFunctype [] ([tv1, tv2] ++ [valtype_numtype numtype.I32]))
      (mkFunctype t1s tc) :=
    (instrtype_sub_compose_ge [] [tv1, tv2] [] [] [valtype_numtype numtype.I32] t1s tb tc
      (by simpa using hc1) hsub_const rfl).1
  obtain ⟨hfinal, hrsub⟩ :=
    instrtype_sub_compose_eq [] [tv1, tv2, valtype.I32] [tt, tt, valtype.I32] [tt] t1s tc t2s
      (by simpa [valtype_numtype] using hc2) hsub_sel rfl
  -- neither value's type can be BOT, so the select's `t` *is* both of them
  have hnb : Forall (fun v_t => v_t ≠ valtype.BOT) [tv1, tv2, valtype.I32] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact Val_ok_non_bot v_S v_val_1 tv1 hvok1
    · rw [hx]; exact Val_ok_non_bot v_S v_val_2 tv2 hvok2
    · rw [hx]; simp
  have heqts := resulttype_sub_non_bot [tv1, tv2, valtype.I32] [tt, tt, valtype.I32] hnb hrsub
  injection heqts with e1 r1
  injection r1 with e2 _
  rw [e1] at hvok1
  rw [e2] at hvok2
  exact ⟨construct_ais_subtyping v_S v_C [admininstr_val v_val_1] [] [tt] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr_val v_val_1) [] [tt]
        (construct_ai_val v_S v_C v_val_1 tt hvok1 hwfC hwfS)) hfinal,
    construct_ais_subtyping v_S v_C [admininstr_val v_val_2] [] [tt] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr_val v_val_2) [] [tt]
        (construct_ai_val v_S v_C v_val_2 tt hvok2 hwfC hwfS)) hfinal⟩

/-- Rocq `type_preservation_pure.v:130` `Step_pure__select_true_preserves`. -/
theorem Step_pure__select_true_preserves (v_S : store) (v_C : context)
    (v_val_1 v_val_2 : val) (v_c : num_) (v_t : Option (List valtype)) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] v_ft →
    Step_pure [admininstr_val v_val_1, admininstr_val v_val_2, admininstr.CONST numtype.I32 v_c,
      admininstr.SELECT v_t] [admininstr_val v_val_1] →
    Instrs_ok2 v_S v_C [admininstr_val v_val_1] v_ft := fun h _ =>
  (Step_pure__select_preserves_helper v_S v_C v_val_1 v_val_2 v_c v_t v_ft h).1

/-- Rocq `type_preservation_pure.v:140` `Step_pure__select_false_preserves`. -/
theorem Step_pure__select_false_preserves (v_S : store) (v_C : context)
    (v_val_1 v_val_2 : val) (v_c : num_) (v_t : Option (List valtype)) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val_1, admininstr_val v_val_2,
      admininstr.CONST numtype.I32 v_c, admininstr.SELECT v_t] v_ft →
    Step_pure [admininstr_val v_val_1, admininstr_val v_val_2, admininstr.CONST numtype.I32 v_c,
      admininstr.SELECT v_t] [admininstr_val v_val_2] →
    Instrs_ok2 v_S v_C [admininstr_val v_val_2] v_ft := fun h _ =>
  (Step_pure__select_preserves_helper v_S v_C v_val_1 v_val_2 v_c v_t v_ft h).2

/-- Rocq `type_preservation_pure.v:150` `Step_pure__if_preserves_helper`. Rocq's
    `join_subtyping_le Hsub0 Hsub` step is `instrtype_sub_compose_le` applied to `CONST`'s
    `[]->[I32]` principal typing and `IFELSE`'s `(ift1s++[I32])->ift2s` principal typing
    (length hyp `[I32].length=[I32].length` is `rfl`), collapsing to `ift1s->ift2s ≤
    t1s->t2s` directly — the same widening then applies to both `v_instrs_1`/`v_instrs_2`
    since `IFELSE`'s principal typing packages both blocks' `Instrs_ok` facts together at
    the identical `ift1s->ift2s`. -/
theorem Step_pure__if_preserves_helper (v_S : store) (v_C : context) (v_c : num_) (v_bt : blocktype)
    (v_instrs_1 v_instrs_2 : List instr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] v_ft →
    Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_1] v_ft ∧
      Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_2] v_ft := by
  intro h
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2]
      = [admininstr.CONST numtype.I32 v_c] ++ [admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_ifelse, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.IFELSE v_bt v_instrs_1 v_instrs_2]
      (admininstr.CONST numtype.I32 v_c) t1s t2s h
  obtain ⟨tc1, tc2, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST numtype.I32 v_c) t1s t3s h_const
  unfold ai_principal_typing at hconst_pt
  unfold mkFunctype at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tf1, tf2, hif_pt, hsub_if⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.IFELSE v_bt v_instrs_1 v_instrs_2) t3s t2s h_ifelse
  unfold ai_principal_typing at hif_pt
  obtain ⟨ift1s, ift2s, hif_eq, hblockty, hinstrs1, hinstrs2⟩ := hif_pt
  unfold mkFunctype at hif_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hif_eq
  obtain ⟨ef1, ef2⟩ := hif_eq
  rw [ef1, ef2] at hsub_if
  obtain ⟨hwidened, _⟩ := instrtype_sub_compose_le [] [valtype.I32] [valtype.I32] ift1s ift2s t1s t3s t2s
    hsub_const hsub_if rfl
  have hwidened' : instrtype_sub (mkFunctype ift1s ift2s) (mkFunctype t1s t2s) := by
    simpa using hwidened
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C _ (mkFunctype t1s t2s) h
  obtain ⟨_, _, hwf_ifelse_all⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] (mkFunctype t3s t2s) h_ifelse
  have hwfai : wf_admininstr (admininstr.IFELSE v_bt v_instrs_1 v_instrs_2) := hwf_ifelse_all _ (by simp)
  cases hwfai with
  | admininstr_case_6 _ _ _ hbt hf1 hf2 =>
    have hwfCinner : wf_context ({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
        LOCALS := [], LABELS := [.mk_list ift2s], RETURN := none : context }) :=
      wf_context.context_case_ _ _ _ [] [] _ _ _ _ _ (by intro x hx; simp at hx) (by intro x hx; simp at hx)
    have hblock1 : Instr_ok v_C (instr.BLOCK v_bt v_instrs_1) (mkFunctype ift1s ift2s) :=
      Instr_ok.block v_C v_bt v_instrs_1 ift1s ift2s hblockty hinstrs1 hwfC
        (wf_instr.instr_case_4 v_bt v_instrs_1 hbt hf1) hwfCinner
    have hblock2 : Instr_ok v_C (instr.BLOCK v_bt v_instrs_2) (mkFunctype ift1s ift2s) :=
      Instr_ok.block v_C v_bt v_instrs_2 ift1s ift2s hblockty hinstrs2 hwfC
        (wf_instr.instr_case_4 v_bt v_instrs_2 hbt hf2) hwfCinner
    have hinstr2_1 : Instr_ok2 v_S v_C (admininstr.BLOCK v_bt v_instrs_1) (mkFunctype ift1s ift2s) :=
      Instr_ok2.plain v_S v_C (instr.BLOCK v_bt v_instrs_1) ift1s ift2s hblock1 hwfS hwfC
        (wf_instr.instr_case_4 v_bt v_instrs_1 hbt hf1)
    have hinstr2_2 : Instr_ok2 v_S v_C (admininstr.BLOCK v_bt v_instrs_2) (mkFunctype ift1s ift2s) :=
      Instr_ok2.plain v_S v_C (instr.BLOCK v_bt v_instrs_2) ift1s ift2s hblock2 hwfS hwfC
        (wf_instr.instr_case_4 v_bt v_instrs_2 hbt hf2)
    exact ⟨construct_ais_subtyping v_S v_C [admininstr.BLOCK v_bt v_instrs_1] ift1s ift2s t1s t2s
        (construct_ais_typing_single v_S v_C (admininstr.BLOCK v_bt v_instrs_1) ift1s ift2s hinstr2_1) hwidened',
      construct_ais_subtyping v_S v_C [admininstr.BLOCK v_bt v_instrs_2] ift1s ift2s t1s t2s
        (construct_ais_typing_single v_S v_C (admininstr.BLOCK v_bt v_instrs_2) ift1s ift2s hinstr2_2) hwidened'⟩

/-- Rocq `type_preservation_pure.v:170` `Step_pure__if_true_preserves`. -/
theorem Step_pure__if_true_preserves (v_S : store) (v_C : context) (v_c : num_) (v_bt : blocktype)
    (v_instrs_1 v_instrs_2 : List instr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2]
      [admininstr.BLOCK v_bt v_instrs_1] →
    Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_1] v_ft := fun h _ =>
  (Step_pure__if_preserves_helper v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft h).1

/-- Rocq `type_preservation_pure.v:180` `Step_pure__if_false_preserves`. -/
theorem Step_pure__if_false_preserves (v_S : store) (v_C : context) (v_c : num_) (v_bt : blocktype)
    (v_instrs_1 v_instrs_2 : List instr) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.IFELSE v_bt v_instrs_1 v_instrs_2]
      [admininstr.BLOCK v_bt v_instrs_2] →
    Instrs_ok2 v_S v_C [admininstr.BLOCK v_bt v_instrs_2] v_ft := fun h _ =>
  (Step_pure__if_preserves_helper v_S v_C v_c v_bt v_instrs_1 v_instrs_2 v_ft h).2

/-- Rocq `type_preservation_pure.v:190` `Step_pure__label_vals_preserves`. Diverges from
    Rocq's `join_subtyping_trans` (a second `invert_ais_typing` decomposing the value-list
    body further): once `LABEL_`'s principal typing hands over
    `Instrs_ok2{...LABELS:=t's::v_C.LABELS}(v_val.map admininstr_val)([]->ts)`, this project's
    `construct_ais_vals'` (context-irrelevance for value lists, already proved) switches the
    context back to `v_C` directly in one step, since value lists never reference
    `LABELS`/`RETURN` — no need to re-decompose the value list itself. -/
theorem Step_pure__label_vals_preserves (v_S : store) (v_C : context) (v_n : n) (v_instrs : List instr)
    (v_val : List val) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.LABEL_ v_n v_instrs (v_val.map admininstr_val)] v_ft →
    Step_pure [admininstr.LABEL_ v_n v_instrs (v_val.map admininstr_val)] (v_val.map admininstr_val) →
    Instrs_ok2 v_S v_C (v_val.map admininstr_val) v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨t1s_sup, t2s_sub, hprincipal, hsub⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.LABEL_ v_n v_instrs (v_val.map admininstr_val)) t1s t2s h
  unfold ai_principal_typing at hprincipal
  obtain ⟨ts, t's, heq, hlen, hinstrs, hbody⟩ := hprincipal
  unfold mkFunctype at heq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  rw [e1, e2] at hsub
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.LABEL_ v_n v_instrs (v_val.map admininstr_val)]
      (mkFunctype t1s t2s) h
  have hbody' : Instrs_ok2 v_S v_C (v_val.map admininstr_val) (mkFunctype [] ts) :=
    construct_ais_vals' v_S { v_C with LABELS := (list.mk_list t's) :: v_C.LABELS } v_C v_val
      (mkFunctype [] ts) hbody hwfC
  exact construct_ais_subtyping v_S v_C (v_val.map admininstr_val) [] ts t1s t2s hbody' hsub

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
    Instrs_ok2 v_S v_C [admininstr.BR v_l] v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l]
      = [admininstr.CONST numtype.I32 v_c] ++ [admininstr.BR_IF v_l] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_brif, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.BR_IF v_l] (admininstr.CONST numtype.I32 v_c) t1s t2s h
  obtain ⟨tc1, tc2, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST numtype.I32 v_c) t1s t3s h_const
  unfold ai_principal_typing at hconst_pt
  unfold mkFunctype at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tb1, tb2, hbrif_pt, hsub_brif⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.BR_IF v_l) t3s t2s h_brif
  unfold ai_principal_typing at hbrif_pt
  obtain ⟨ts, hbrif_eq, hget⟩ := hbrif_pt
  unfold mkFunctype at hbrif_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hbrif_eq
  obtain ⟨eb1, eb2⟩ := hbrif_eq
  rw [eb1, eb2] at hsub_brif
  have hwidened := instrtype_sub_compose1 [] [valtype.I32] ts ts t1s t3s t2s hsub_const hsub_brif
  simp only [List.append_nil] at hwidened
  obtain ⟨hwfC, hwfS, hwfai⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l]
      (mkFunctype t1s t2s) h
  have hwfbrif : wf_admininstr (admininstr.BR_IF v_l) := hwfai _ (by simp)
  obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hget
  cases hwfbrif with
  | admininstr_case_8 _ hwfl =>
    have hidxeq' : proj_list_0 valtype (v_C.LABELS[proj_uN_0 v_l]!) = ts := by
      have hbang : v_C.LABELS[proj_uN_0 v_l]! = list.mk_list ts := by
        rw [getElem!_pos v_C.LABELS (proj_uN_0 v_l) hlt]; exact hidxeq
      rw [hbang]; rfl
    have hbr_instrok : Instr_ok v_C (instr.BR v_l) (mkFunctype ts ts) :=
      Instr_ok.br v_C v_l [] ts ts hlt hidxeq' hwfC (wf_instr.instr_case_7 v_l hwfl)
    have hbr2 : Instr_ok2 v_S v_C (admininstr.BR v_l) (mkFunctype ts ts) :=
      Instr_ok2.plain v_S v_C (instr.BR v_l) ts ts hbr_instrok hwfS hwfC (wf_instr.instr_case_7 v_l hwfl)
    exact construct_ais_subtyping v_S v_C [admininstr.BR v_l] ts ts t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr.BR v_l) ts ts hbr2) hwidened

/-- Rocq `type_preservation_pure.v:355` `Step_pure__br_if_false_preserves`. -/
theorem Step_pure__br_if_false_preserves (v_S : store) (v_C : context) (v_c : num_) (v_l : labelidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l] v_ft →
    Step_pure [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l] [] →
    Instrs_ok2 v_S v_C [] v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l]
      = [admininstr.CONST numtype.I32 v_c] ++ [admininstr.BR_IF v_l] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_brif, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.BR_IF v_l] (admininstr.CONST numtype.I32 v_c) t1s t2s h
  obtain ⟨tc1, tc2, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST numtype.I32 v_c) t1s t3s h_const
  unfold ai_principal_typing at hconst_pt
  unfold mkFunctype at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tb1, tb2, hbrif_pt, hsub_brif⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.BR_IF v_l) t3s t2s h_brif
  unfold ai_principal_typing at hbrif_pt
  obtain ⟨ts, hbrif_eq, hget⟩ := hbrif_pt
  unfold mkFunctype at hbrif_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hbrif_eq
  obtain ⟨eb1, eb2⟩ := hbrif_eq
  rw [eb1, eb2] at hsub_brif
  have hwidened := instrtype_sub_compose1 [] [valtype.I32] ts ts t1s t3s t2s hsub_const hsub_brif
  simp only [List.append_nil] at hwidened
  obtain ⟨tp1', tp1, ts1', ts2'', h1e1, h1e2, h1s1, h1s2, h1s3⟩ := hwidened
  have hrsub : ResulttypeSub t1s t2s := by
    rw [h1e1, h1e2]
    exact resulttype_sub_app tp1' ts1' tp1 ts2'' h1s1 (resulttype_sub_trans _ _ _ h1s2 h1s3)
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.CONST numtype.I32 v_c, admininstr.BR_IF v_l]
      (mkFunctype t1s t2s) h
  exact (ais_empty_typing v_S v_C t1s t2s).mpr ⟨hwfC, hwfS, hrsub⟩

/-- Rocq `type_preservation_pure.v:383` `proj_identity`. Small helper (round-trip through
    the `list` wrapper constructor). -/
theorem proj_identity (a : resulttype) : list.mk_list (proj_list_0 valtype a) = a := by
  cases a; rfl

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
    `construct_ais_vals'` (context-irrelevance) to cross the frame boundary — same shape as
    `Step_pure__label_vals_preserves` above, except `FRAME_`'s principal typing wraps its
    body in `Expr_ok2` (one extra inversion step to reach the underlying `Instrs_ok2`) and
    the crossed context is `{c' with RETURN := ...}` for the `Frame_ok`-supplied `c'`, not a
    `LABELS`-extension of `v_C` itself; `Frame_ok v_S v_f c'` itself is never inverted since
    nothing about `v_f`'s actual identity is needed. -/
theorem Step_pure__frame_vals_preserves (v_S : store) (v_C : context) (v_n : n) (v_f : frame)
    (v_val : List val) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.FRAME_ v_n v_f (v_val.map admininstr_val)] v_ft →
    Step_pure [admininstr.FRAME_ v_n v_f (v_val.map admininstr_val)] (v_val.map admininstr_val) →
    Instrs_ok2 v_S v_C (v_val.map admininstr_val) v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  obtain ⟨t1s_sup, t2s_sub, hprincipal, hsub⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.FRAME_ v_n v_f (v_val.map admininstr_val)) t1s t2s h
  unfold ai_principal_typing at hprincipal
  obtain ⟨ts, c', heq, hframe, hexpr, _hlen⟩ := hprincipal
  unfold mkFunctype at heq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  rw [e1, e2] at hsub
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.FRAME_ v_n v_f (v_val.map admininstr_val)]
      (mkFunctype t1s t2s) h
  cases hexpr with
  | mk_Expr_ok2 _ _ _ hinstrs _ _ _ =>
    have hbody' : Instrs_ok2 v_S v_C (v_val.map admininstr_val) (mkFunctype [] ts) :=
      construct_ais_vals' v_S { c' with RETURN := some (list.mk_list ts) } v_C v_val
        (mkFunctype [] ts) hinstrs hwfC
    exact construct_ais_subtyping v_S v_C (v_val.map admininstr_val) [] ts t1s t2s hbody' hsub

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
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c] v_ft := by
  intro h _ hwfc
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST v_t v_c_1, admininstr.UNOP v_t v_unop]
      = [admininstr.CONST v_t v_c_1] ++ [admininstr.UNOP v_t v_unop] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_unop, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.UNOP v_t v_unop] (admininstr.CONST v_t v_c_1) t1s t2s h
  obtain ⟨tc1, tc2, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t v_c_1) t1s t3s h_const
  unfold ai_principal_typing at hconst_pt
  unfold mkFunctype at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tu1, tu2, hunop_pt, hsub_unop⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.UNOP v_t v_unop) t3s t2s h_unop
  unfold ai_principal_typing at hunop_pt
  unfold mkFunctype at hunop_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hunop_pt
  obtain ⟨eu1, eu2⟩ := hunop_pt
  rw [eu1, eu2] at hsub_unop
  have hwidened :=
    instrtype_sub_compose [] [valtype_numtype v_t] [valtype_numtype v_t] t1s t3s t2s hsub_const hsub_unop
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.CONST v_t v_c_1, admininstr.UNOP v_t v_unop]
      (mkFunctype t1s t2s) h
  cases hwfc with
  | admininstr_case_13 _ _ hwfnum =>
    have hcinstrok : Instr_ok v_C (instr.CONST v_t v_c) (mkFunctype [] [valtype_numtype v_t]) :=
      Instr_ok.const v_C v_t v_c hwfC (wf_instr.instr_case_13 v_t v_c hwfnum)
    have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST v_t v_c) (mkFunctype [] [valtype_numtype v_t]) :=
      Instr_ok2.plain v_S v_C (instr.CONST v_t v_c) [] [valtype_numtype v_t] hcinstrok hwfS hwfC
        (wf_instr.instr_case_13 v_t v_c hwfnum)
    exact construct_ais_subtyping v_S v_C [admininstr.CONST v_t v_c] [] [valtype_numtype v_t] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr.CONST v_t v_c) [] [valtype_numtype v_t] hcinstr2) hwidened

/-- Rocq `type_preservation_pure.v:646` `Step_pure__binop_val_preserves`. -/
theorem Step_pure__binop_val_preserves (v_S : store) (v_C : context) (v_t : numtype)
    (v_c_1 v_c_2 : num_) (v_binop : binop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.BINOP v_t v_binop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.BINOP v_t v_binop]
      [admininstr.CONST v_t v_c] →
    wf_admininstr (admininstr.CONST v_t v_c) →
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c] v_ft := by
  intro h _ hwfc
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.BINOP v_t v_binop]
      = [admininstr.CONST v_t v_c_1] ++ ([admininstr.CONST v_t v_c_2] ++ [admininstr.BINOP v_t v_binop]) := rfl
  rw [heq] at h
  obtain ⟨t3s, h_rest1, h1⟩ :=
    ais_seq_typing_inversion v_S v_C ([admininstr.CONST v_t v_c_2] ++ [admininstr.BINOP v_t v_binop])
      (admininstr.CONST v_t v_c_1) t1s t2s h
  obtain ⟨t4s, h_binop, h2⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.BINOP v_t v_binop] (admininstr.CONST v_t v_c_2) t3s t2s h_rest1
  obtain ⟨tc1a, tc1b, hc1_pt, hsub_c1⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t v_c_1) t1s t3s h1
  unfold ai_principal_typing at hc1_pt
  unfold mkFunctype at hc1_pt
  obtain ⟨hc1_eq, _⟩ := hc1_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hc1_eq
  obtain ⟨e1a, e1b⟩ := hc1_eq
  subst e1a; subst e1b
  obtain ⟨tc2a, tc2b, hc2_pt, hsub_c2⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t v_c_2) t3s t4s h2
  unfold ai_principal_typing at hc2_pt
  unfold mkFunctype at hc2_pt
  obtain ⟨hc2_eq, _⟩ := hc2_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hc2_eq
  obtain ⟨e2a, e2b⟩ := hc2_eq
  subst e2a; subst e2b
  obtain ⟨tb1, tb2, hbinop_pt, hsub_binop⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.BINOP v_t v_binop) t4s t2s h_binop
  unfold ai_principal_typing at hbinop_pt
  unfold mkFunctype at hbinop_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hbinop_pt
  obtain ⟨ebA, ebB⟩ := hbinop_pt
  have hsub_binop' : instrtype_sub (mkFunctype ([valtype_numtype v_t] ++ [valtype_numtype v_t]) [valtype_numtype v_t])
      (mkFunctype t4s t2s) := by rw [ebA, ebB] at hsub_binop; exact hsub_binop
  have hmid :=
    instrtype_sub_compose1 [] [valtype_numtype v_t] [valtype_numtype v_t] [valtype_numtype v_t] t3s t4s t2s
      hsub_c2 hsub_binop'
  simp only [List.append_nil] at hmid
  have hwidened :=
    instrtype_sub_compose [] [valtype_numtype v_t] [valtype_numtype v_t] t1s t3s t2s hsub_c1 hmid
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C
      [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.BINOP v_t v_binop]
      (mkFunctype t1s t2s) h
  cases hwfc with
  | admininstr_case_13 _ _ hwfnum =>
    have hcinstrok : Instr_ok v_C (instr.CONST v_t v_c) (mkFunctype [] [valtype_numtype v_t]) :=
      Instr_ok.const v_C v_t v_c hwfC (wf_instr.instr_case_13 v_t v_c hwfnum)
    have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST v_t v_c) (mkFunctype [] [valtype_numtype v_t]) :=
      Instr_ok2.plain v_S v_C (instr.CONST v_t v_c) [] [valtype_numtype v_t] hcinstrok hwfS hwfC
        (wf_instr.instr_case_13 v_t v_c hwfnum)
    exact construct_ais_subtyping v_S v_C [admininstr.CONST v_t v_c] [] [valtype_numtype v_t] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr.CONST v_t v_c) [] [valtype_numtype v_t] hcinstr2) hwidened

/-- Rocq `type_preservation_pure.v:680` `Step_pure__testop_preserves`. -/
theorem Step_pure__testop_preserves (v_S : store) (v_C : context) (v_t : numtype) (v_c_1 : num_)
    (v_testop : testop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.TESTOP v_t v_testop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.TESTOP v_t v_testop] [admininstr.CONST numtype.I32 v_c] →
    wf_admininstr (admininstr.CONST numtype.I32 v_c) →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c] v_ft := by
  intro h _ hwfc
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST v_t v_c_1, admininstr.TESTOP v_t v_testop]
      = [admininstr.CONST v_t v_c_1] ++ [admininstr.TESTOP v_t v_testop] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_testop, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.TESTOP v_t v_testop] (admininstr.CONST v_t v_c_1) t1s t2s h
  obtain ⟨tc1, tc2, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t v_c_1) t1s t3s h_const
  unfold ai_principal_typing at hconst_pt
  unfold mkFunctype at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tu1, tu2, htestop_pt, hsub_testop⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.TESTOP v_t v_testop) t3s t2s h_testop
  unfold ai_principal_typing at htestop_pt
  unfold mkFunctype at htestop_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at htestop_pt
  obtain ⟨eu1, eu2⟩ := htestop_pt
  rw [eu1, eu2] at hsub_testop
  have hwidened :=
    instrtype_sub_compose [] [valtype_numtype v_t] [valtype.I32] t1s t3s t2s hsub_const hsub_testop
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.CONST v_t v_c_1, admininstr.TESTOP v_t v_testop]
      (mkFunctype t1s t2s) h
  cases hwfc with
  | admininstr_case_13 _ _ hwfnum =>
    have hcinstrok : Instr_ok v_C (instr.CONST numtype.I32 v_c) (mkFunctype [] [valtype.I32]) :=
      Instr_ok.const v_C numtype.I32 v_c hwfC (wf_instr.instr_case_13 numtype.I32 v_c hwfnum)
    have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST numtype.I32 v_c) (mkFunctype [] [valtype.I32]) :=
      Instr_ok2.plain v_S v_C (instr.CONST numtype.I32 v_c) [] [valtype.I32] hcinstrok hwfS hwfC
        (wf_instr.instr_case_13 numtype.I32 v_c hwfnum)
    exact construct_ais_subtyping v_S v_C [admininstr.CONST numtype.I32 v_c] [] [valtype.I32] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr.CONST numtype.I32 v_c) [] [valtype.I32] hcinstr2) hwidened

/-- Rocq `type_preservation_pure.v:708` `Step_pure__relop_preserves`. -/
theorem Step_pure__relop_preserves (v_S : store) (v_C : context) (v_t : numtype) (v_c_1 v_c_2 : num_)
    (v_relop : relop_) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.RELOP v_t v_relop] v_ft →
    Step_pure [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.RELOP v_t v_relop]
      [admininstr.CONST numtype.I32 v_c] →
    wf_admininstr (admininstr.CONST numtype.I32 v_c) →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 v_c] v_ft := by
  intro h _ hwfc
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.RELOP v_t v_relop]
      = [admininstr.CONST v_t v_c_1] ++ ([admininstr.CONST v_t v_c_2] ++ [admininstr.RELOP v_t v_relop]) := rfl
  rw [heq] at h
  obtain ⟨t3s, h_rest1, h1⟩ :=
    ais_seq_typing_inversion v_S v_C ([admininstr.CONST v_t v_c_2] ++ [admininstr.RELOP v_t v_relop])
      (admininstr.CONST v_t v_c_1) t1s t2s h
  obtain ⟨t4s, h_relop, h2⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.RELOP v_t v_relop] (admininstr.CONST v_t v_c_2) t3s t2s h_rest1
  obtain ⟨tc1a, tc1b, hc1_pt, hsub_c1⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t v_c_1) t1s t3s h1
  unfold ai_principal_typing at hc1_pt
  unfold mkFunctype at hc1_pt
  obtain ⟨hc1_eq, _⟩ := hc1_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hc1_eq
  obtain ⟨e1a, e1b⟩ := hc1_eq
  subst e1a; subst e1b
  obtain ⟨tc2a, tc2b, hc2_pt, hsub_c2⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t v_c_2) t3s t4s h2
  unfold ai_principal_typing at hc2_pt
  unfold mkFunctype at hc2_pt
  obtain ⟨hc2_eq, _⟩ := hc2_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hc2_eq
  obtain ⟨e2a, e2b⟩ := hc2_eq
  subst e2a; subst e2b
  obtain ⟨tr1, tr2, hrelop_pt, hsub_relop⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.RELOP v_t v_relop) t4s t2s h_relop
  unfold ai_principal_typing at hrelop_pt
  unfold mkFunctype at hrelop_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hrelop_pt
  obtain ⟨erA, erB⟩ := hrelop_pt
  have hsub_relop' : instrtype_sub (mkFunctype ([valtype_numtype v_t] ++ [valtype_numtype v_t]) [valtype.I32])
      (mkFunctype t4s t2s) := by rw [erA, erB] at hsub_relop; exact hsub_relop
  have hmid :=
    instrtype_sub_compose1 [] [valtype_numtype v_t] [valtype_numtype v_t] [valtype.I32] t3s t4s t2s
      hsub_c2 hsub_relop'
  simp only [List.append_nil] at hmid
  have hwidened :=
    instrtype_sub_compose [] [valtype_numtype v_t] [valtype.I32] t1s t3s t2s hsub_c1 hmid
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C
      [admininstr.CONST v_t v_c_1, admininstr.CONST v_t v_c_2, admininstr.RELOP v_t v_relop]
      (mkFunctype t1s t2s) h
  cases hwfc with
  | admininstr_case_13 _ _ hwfnum =>
    have hcinstrok : Instr_ok v_C (instr.CONST numtype.I32 v_c) (mkFunctype [] [valtype.I32]) :=
      Instr_ok.const v_C numtype.I32 v_c hwfC (wf_instr.instr_case_13 numtype.I32 v_c hwfnum)
    have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST numtype.I32 v_c) (mkFunctype [] [valtype.I32]) :=
      Instr_ok2.plain v_S v_C (instr.CONST numtype.I32 v_c) [] [valtype.I32] hcinstrok hwfS hwfC
        (wf_instr.instr_case_13 numtype.I32 v_c hwfnum)
    exact construct_ais_subtyping v_S v_C [admininstr.CONST numtype.I32 v_c] [] [valtype.I32] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr.CONST numtype.I32 v_c) [] [valtype.I32] hcinstr2) hwidened

/-- Rocq `type_preservation_pure.v:742` `Step_pure__cvtop_val_preserves`. -/
theorem Step_pure__cvtop_val_preserves (v_S : store) (v_C : context) (v_t_1 v_t_2 : numtype) (v_c_1 : num_)
    (v_cvtop : cvtop__) (v_c : num_) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr.CONST v_t_1 v_c_1, admininstr.CVTOP v_t_2 v_t_1 v_cvtop] v_ft →
    Step_pure [admininstr.CONST v_t_1 v_c_1, admininstr.CVTOP v_t_2 v_t_1 v_cvtop] [admininstr.CONST v_t_2 v_c] →
    wf_admininstr (admininstr.CONST v_t_2 v_c) →
    Instrs_ok2 v_S v_C [admininstr.CONST v_t_2 v_c] v_ft := by
  intro h _ hwfc
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr.CONST v_t_1 v_c_1, admininstr.CVTOP v_t_2 v_t_1 v_cvtop]
      = [admininstr.CONST v_t_1 v_c_1] ++ [admininstr.CVTOP v_t_2 v_t_1 v_cvtop] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_cvtop, h_const⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.CVTOP v_t_2 v_t_1 v_cvtop] (admininstr.CONST v_t_1 v_c_1) t1s t2s h
  obtain ⟨tc1, tc2, hconst_pt, hsub_const⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CONST v_t_1 v_c_1) t1s t3s h_const
  unfold ai_principal_typing at hconst_pt
  unfold mkFunctype at hconst_pt
  obtain ⟨hconst_eq, _⟩ := hconst_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hconst_eq
  obtain ⟨ec1, ec2⟩ := hconst_eq
  subst ec1; subst ec2
  obtain ⟨tu1, tu2, hcvtop_pt, hsub_cvtop⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.CVTOP v_t_2 v_t_1 v_cvtop) t3s t2s h_cvtop
  unfold ai_principal_typing at hcvtop_pt
  unfold mkFunctype at hcvtop_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hcvtop_pt
  obtain ⟨eu1, eu2⟩ := hcvtop_pt
  rw [eu1, eu2] at hsub_cvtop
  have hwidened :=
    instrtype_sub_compose [] [valtype_numtype v_t_1] [valtype_numtype v_t_2] t1s t3s t2s hsub_const hsub_cvtop
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr.CONST v_t_1 v_c_1, admininstr.CVTOP v_t_2 v_t_1 v_cvtop]
      (mkFunctype t1s t2s) h
  cases hwfc with
  | admininstr_case_13 _ _ hwfnum =>
    have hcinstrok : Instr_ok v_C (instr.CONST v_t_2 v_c) (mkFunctype [] [valtype_numtype v_t_2]) :=
      Instr_ok.const v_C v_t_2 v_c hwfC (wf_instr.instr_case_13 v_t_2 v_c hwfnum)
    have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST v_t_2 v_c) (mkFunctype [] [valtype_numtype v_t_2]) :=
      Instr_ok2.plain v_S v_C (instr.CONST v_t_2 v_c) [] [valtype_numtype v_t_2] hcinstrok hwfS hwfC
        (wf_instr.instr_case_13 v_t_2 v_c hwfnum)
    exact construct_ais_subtyping v_S v_C [admininstr.CONST v_t_2 v_c] [] [valtype_numtype v_t_2] t1s t2s
      (construct_ais_typing_single v_S v_C (admininstr.CONST v_t_2 v_c) [] [valtype_numtype v_t_2] hcinstr2) hwidened

/-- Rocq `type_preservation_pure.v:770` `Step_pure__local_tee_preserves`. Diverges from
    Rocq's `Val_ok_non_bot`/`valtype_sub_non_bot` pinning: rather than proving the two
    values' type is *exactly* the local's declared type `t`, this port just widens the
    value's own principal type `[]->[ta]` directly to `[]->[t]` using the `ResulttypeSub
    [ta] [t]` fact `instrtype_sub_compose_eq` already hands back as its second component —
    shorter, since the exact-equality pinning turns out not to be needed once the widening
    is done at the `Instrs_ok2` level instead of value-by-value. -/
theorem Step_pure__local_tee_preserves (v_S : store) (v_C : context) (v_val : val) (v_x : localidx) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr.LOCAL_TEE v_x] v_ft →
    Step_pure [admininstr_val v_val, admininstr.LOCAL_TEE v_x]
      [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET v_x] →
    Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET v_x] v_ft := by
  intro h _
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr_val v_val, admininstr.LOCAL_TEE v_x]
      = [admininstr_val v_val] ++ [admininstr.LOCAL_TEE v_x] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_tee, h_val⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.LOCAL_TEE v_x] (admininstr_val v_val) t1s t2s h
  obtain ⟨ta, hsub_val, hval_ok⟩ := ais_single_val_typing_inversion v_S v_C v_val t1s t3s h_val
  obtain ⟨t4a, t4b, htee_pt, hsub_tee⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr.LOCAL_TEE v_x) t3s t2s h_tee
  unfold ai_principal_typing at htee_pt
  obtain ⟨t, htee_eq, hget⟩ := htee_pt
  unfold mkFunctype at htee_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at htee_eq
  obtain ⟨et1, et2⟩ := htee_eq
  rw [et1, et2] at hsub_tee
  obtain ⟨hfinal, hResulttypeSub_ta_t⟩ :=
    instrtype_sub_compose_eq [] [ta] [t] [t] t1s t3s t2s hsub_val hsub_tee rfl
  obtain ⟨hwfC, hwfS, hwfai⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr_val v_val, admininstr.LOCAL_TEE v_x] (mkFunctype t1s t2s) h
  have hwftee : wf_admininstr (admininstr.LOCAL_TEE v_x) := hwfai _ (by simp)
  obtain ⟨hlt, hidxeq⟩ := List.getElem?_eq_some_iff.mp hget
  have hidxeq' : v_C.LOCALS[proj_uN_0 v_x]! = t := by rw [getElem!_pos v_C.LOCALS (proj_uN_0 v_x) hlt]; exact hidxeq
  cases hwftee with
  | admininstr_case_45 _ hwfl =>
    have hwidenwitness : instrtype_sub (mkFunctype [] [ta]) (mkFunctype [] [t]) :=
      ⟨[], [], [], [t], rfl, rfl, resulttype_sub_refl [], resulttype_sub_refl [], hResulttypeSub_ta_t⟩
    have hval1 : Instrs_ok2 v_S v_C [admininstr_val v_val] (mkFunctype [] [t]) :=
      construct_ais_subtyping v_S v_C [admininstr_val v_val] [] [ta] [] [t]
        (construct_ais_typing_single v_S v_C (admininstr_val v_val) [] [ta]
          (construct_ai_val v_S v_C v_val ta hval_ok hwfC hwfS)) hwidenwitness
    have hval2 : Instrs_ok2 v_S v_C [admininstr_val v_val] (mkFunctype [t] [t, t]) :=
      construct_ais_subtyping v_S v_C [admininstr_val v_val] [] [t] [t] [t, t]
        hval1 (instrtype_sub_add_same [] [t] [t])
    have hvals : Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr_val v_val] (mkFunctype [] [t, t]) := by
      have := construct_ais_compose v_S v_C [admininstr_val v_val] [admininstr_val v_val] [] [t] [t, t] hval1 hval2
      simpa using this
    have hwfinstr_set : wf_instr (instr.LOCAL_SET v_x) := wf_instr.instr_case_44 v_x hwfl
    have hlocalset_instrok : Instr_ok v_C (instr.LOCAL_SET v_x) (mkFunctype [t] []) :=
      Instr_ok.local_set v_C v_x t hlt hidxeq' hwfC hwfinstr_set
    have hlocalset2 : Instr_ok2 v_S v_C (admininstr.LOCAL_SET v_x) (mkFunctype [t] []) :=
      Instr_ok2.plain v_S v_C (instr.LOCAL_SET v_x) [t] [] hlocalset_instrok hwfS hwfC hwfinstr_set
    have hlocalset3 : Instrs_ok2 v_S v_C [admininstr.LOCAL_SET v_x] (mkFunctype [t, t] [t]) :=
      construct_ais_subtyping v_S v_C [admininstr.LOCAL_SET v_x] [t] [] [t, t] [t]
        (construct_ais_typing_single v_S v_C (admininstr.LOCAL_SET v_x) [t] [] hlocalset2)
        (instrtype_sub_add_same [t] [] [t])
    have hcombined :
        Instrs_ok2 v_S v_C [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET v_x]
          (mkFunctype [] [t]) := by
      have := construct_ais_compose v_S v_C [admininstr_val v_val, admininstr_val v_val]
        [admininstr.LOCAL_SET v_x] [] [t, t] [t] hvals hlocalset3
      simpa using this
    exact construct_ais_subtyping v_S v_C
      [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET v_x] [] [t] t1s t2s hcombined hfinal

/-- Rocq `type_preservation_pure.v:816` `Step_pure__ref_is_null_helper`. Generic over the
    Boolean result (works for either 0 or 1). -/
theorem Step_pure__ref_is_null_helper (v_S : store) (v_C : context) (v_rt : reftype) (v_ft : functype) (v_n : Nat) :
    Instrs_ok2 v_S v_C [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL] v_ft →
    Step_pure [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL]
      [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))] →
    (v_n = 1 ∨ v_n = 0) →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))] v_ft := by
  intro h _ hdisj
  obtain ⟨t1, t2⟩ := v_ft
  obtain ⟨t1s⟩ := t1
  obtain ⟨t2s⟩ := t2
  have heq : [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL]
      = [admininstr_instr (instr.REF_NULL v_rt)] ++ [admininstr.REF_IS_NULL] := rfl
  rw [heq] at h
  obtain ⟨t3s, h_isnull, h_refnull⟩ :=
    ais_seq_typing_inversion v_S v_C [admininstr.REF_IS_NULL] (admininstr_instr (instr.REF_NULL v_rt)) t1s t2s h
  obtain ⟨trn1, trn2, hrefnull_pt, hsub_refnull⟩ :=
    ais_single_typing_inversion v_S v_C (admininstr_instr (instr.REF_NULL v_rt)) t1s t3s h_refnull
  unfold ai_principal_typing at hrefnull_pt
  simp only [admininstr_instr] at hrefnull_pt
  unfold mkFunctype at hrefnull_pt
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hrefnull_pt
  obtain ⟨ern1, ern2⟩ := hrefnull_pt
  rw [ern1, ern2] at hsub_refnull
  obtain ⟨ti1, ti2, hisnull_pt, hsub_isnull⟩ :=
    ais_single_typing_inversion v_S v_C admininstr.REF_IS_NULL t3s t2s h_isnull
  unfold ai_principal_typing at hisnull_pt
  obtain ⟨rt', hisnull_eq⟩ := hisnull_pt
  unfold mkFunctype at hisnull_eq
  simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hisnull_eq
  obtain ⟨ei1, ei2⟩ := hisnull_eq
  rw [ei1, ei2] at hsub_isnull
  obtain ⟨hfinal, _⟩ :=
    instrtype_sub_compose_eq [] [valtype_reftype v_rt] [valtype_reftype rt'] [valtype.I32] t1s t3s t2s
      hsub_refnull hsub_isnull rfl
  have hwfnum : wf_num_ numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)) := by
    refine wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN v_n) ?_ ?_ rfl
    · simp [size, valtype_Inn]
    · simp only [size, valtype_Inn]
      exact wf_uN.uN_case_0 32 v_n (by rcases hdisj with h | h <;> subst h <;> decide)
  obtain ⟨hwfC, hwfS, _⟩ :=
    ainstrs_ok_context_store_wf v_S v_C [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL]
      (mkFunctype t1s t2s) h
  have hwfinstr : wf_instr (instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) :=
    wf_instr.instr_case_13 numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)) hwfnum
  have hcinstrok : Instr_ok v_C (instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (mkFunctype [] [valtype.I32]) :=
    Instr_ok.const v_C numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)) hwfC hwfinstr
  have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) (mkFunctype [] [valtype.I32]) :=
    Instr_ok2.plain v_S v_C (instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))) [] [valtype.I32]
      hcinstrok hwfS hwfC hwfinstr
  exact construct_ais_subtyping v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n))]
    [] [valtype.I32] t1s t2s
    (construct_ais_typing_single v_S v_C (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN v_n)))
      [] [valtype.I32] hcinstr2) hfinal

/-- Rocq `type_preservation_pure.v:848` `Step_pure__ref_is_null_true_preserves`.
    Specializes the helper above with `v_n := 1`. -/
theorem Step_pure__ref_is_null_true_preserves (v_S : store) (v_C : context) (v_rt : reftype) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL] v_ft →
    Step_pure [admininstr_instr (instr.REF_NULL v_rt), admininstr.REF_IS_NULL]
      [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))] →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 1))] v_ft := fun h hred =>
  Step_pure__ref_is_null_helper v_S v_C v_rt v_ft 1 h hred (Or.inl rfl)

/-- Shared final step for `Step_pure__ref_is_null_false_preserves`'s
    `REF_FUNC_ADDR`/`REF_HOST_ADDR` cases (not a Rocq lemma — factored out here purely to
    avoid duplicating the `CONST I32 0` construction, since `wf_num_ I32 0` is trivially
    true regardless of which `ref` case produced the `[]->[I32]` widening fact). -/
theorem ref_is_null_zero_construct {v_ais : List admininstr} (v_S : store) (v_C : context)
    (t1s t2s : List valtype) (hfinal : instrtype_sub (mkFunctype [] [valtype.I32]) (mkFunctype t1s t2s))
    (h : Instrs_ok2 v_S v_C v_ais (mkFunctype t1s t2s)) :
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))] (mkFunctype t1s t2s) := by
  obtain ⟨hwfC, hwfS, _⟩ := ainstrs_ok_context_store_wf v_S v_C v_ais (mkFunctype t1s t2s) h
  have hwfnum : wf_num_ numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)) := by
    refine wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN 0) ?_ ?_ rfl
    · simp [size, valtype_Inn]
    · simp only [size, valtype_Inn]
      exact wf_uN.uN_case_0 32 0 (by decide)
  have hwfinstr : wf_instr (instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))) :=
    wf_instr.instr_case_13 numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)) hwfnum
  have hcinstrok : Instr_ok v_C (instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))) (mkFunctype [] [valtype.I32]) :=
    Instr_ok.const v_C numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)) hwfC hwfinstr
  have hcinstr2 : Instr_ok2 v_S v_C (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))) (mkFunctype [] [valtype.I32]) :=
    Instr_ok2.plain v_S v_C (instr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))) [] [valtype.I32]
      hcinstrok hwfS hwfC hwfinstr
  exact construct_ais_subtyping v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))]
    [] [valtype.I32] t1s t2s
    (construct_ais_typing_single v_S v_C (admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)))
      [] [valtype.I32] hcinstr2) hfinal

/-- Rocq `type_preservation_pure.v:857` `Step_pure__ref_is_null_false_preserves`.
    Case-splits on the 3 `ref` constructors (REF_NULL delegates to the helper above;
    REF_FUNC_ADDR/REF_HOST_ADDR each get their own hand proof in Rocq). -/
theorem Step_pure__ref_is_null_false_preserves (v_S : store) (v_C : context) (v_ref : ref) (v_ft : functype) :
    Instrs_ok2 v_S v_C [admininstr_ref v_ref, admininstr.REF_IS_NULL] v_ft →
    Step_pure [admininstr_ref v_ref, admininstr.REF_IS_NULL]
      [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))] →
    Instrs_ok2 v_S v_C [admininstr.CONST numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0))] v_ft := by
  intro h hred
  cases v_ref with
  | REF_NULL rt => exact Step_pure__ref_is_null_helper v_S v_C rt v_ft 0 h hred (Or.inr rfl)
  | REF_FUNC_ADDR faddr =>
    obtain ⟨t1, t2⟩ := v_ft
    obtain ⟨t1s⟩ := t1
    obtain ⟨t2s⟩ := t2
    have heq : [admininstr_ref (ref.REF_FUNC_ADDR faddr), admininstr.REF_IS_NULL]
        = [admininstr_ref (ref.REF_FUNC_ADDR faddr)] ++ [admininstr.REF_IS_NULL] := rfl
    rw [heq] at h
    obtain ⟨t3s, h_isnull, h_ref⟩ :=
      ais_seq_typing_inversion v_S v_C [admininstr.REF_IS_NULL] (admininstr_ref (ref.REF_FUNC_ADDR faddr)) t1s t2s h
    obtain ⟨tr1, tr2, href_pt, hsub_ref⟩ :=
      ais_single_typing_inversion v_S v_C (admininstr_ref (ref.REF_FUNC_ADDR faddr)) t1s t3s h_ref
    unfold ai_principal_typing at href_pt
    obtain ⟨ft, href_eq, _⟩ := href_pt
    unfold mkFunctype at href_eq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at href_eq
    obtain ⟨er1, er2⟩ := href_eq
    rw [er1, er2] at hsub_ref
    obtain ⟨ti1, ti2, hisnull_pt, hsub_isnull⟩ :=
      ais_single_typing_inversion v_S v_C admininstr.REF_IS_NULL t3s t2s h_isnull
    unfold ai_principal_typing at hisnull_pt
    obtain ⟨rt', hisnull_eq⟩ := hisnull_pt
    unfold mkFunctype at hisnull_eq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hisnull_eq
    obtain ⟨ei1, ei2⟩ := hisnull_eq
    rw [ei1, ei2] at hsub_isnull
    obtain ⟨hfinal, _⟩ :=
      instrtype_sub_compose_eq [] [valtype_reftype reftype.FUNCREF] [valtype_reftype rt'] [valtype.I32] t1s t3s t2s
        hsub_ref hsub_isnull rfl
    exact ref_is_null_zero_construct v_S v_C t1s t2s hfinal h
  | REF_HOST_ADDR haddr =>
    obtain ⟨t1, t2⟩ := v_ft
    obtain ⟨t1s⟩ := t1
    obtain ⟨t2s⟩ := t2
    have heq : [admininstr_ref (ref.REF_HOST_ADDR haddr), admininstr.REF_IS_NULL]
        = [admininstr_ref (ref.REF_HOST_ADDR haddr)] ++ [admininstr.REF_IS_NULL] := rfl
    rw [heq] at h
    obtain ⟨t3s, h_isnull, h_ref⟩ :=
      ais_seq_typing_inversion v_S v_C [admininstr.REF_IS_NULL] (admininstr_ref (ref.REF_HOST_ADDR haddr)) t1s t2s h
    obtain ⟨tr1, tr2, href_pt, hsub_ref⟩ :=
      ais_single_typing_inversion v_S v_C (admininstr_ref (ref.REF_HOST_ADDR haddr)) t1s t3s h_ref
    unfold ai_principal_typing at href_pt
    unfold mkFunctype at href_pt
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at href_pt
    obtain ⟨er1, er2⟩ := href_pt
    rw [er1, er2] at hsub_ref
    obtain ⟨ti1, ti2, hisnull_pt, hsub_isnull⟩ :=
      ais_single_typing_inversion v_S v_C admininstr.REF_IS_NULL t3s t2s h_isnull
    unfold ai_principal_typing at hisnull_pt
    obtain ⟨rt', hisnull_eq⟩ := hisnull_pt
    unfold mkFunctype at hisnull_eq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hisnull_eq
    obtain ⟨ei1, ei2⟩ := hisnull_eq
    rw [ei1, ei2] at hsub_isnull
    obtain ⟨hfinal, _⟩ :=
      instrtype_sub_compose_eq [] [valtype_reftype reftype.EXTERNREF] [valtype_reftype rt'] [valtype.I32] t1s t3s t2s
        hsub_ref hsub_isnull rfl
    exact ref_is_null_zero_construct v_S v_C t1s t2s hfinal h

/-- Rocq `type_preservation_pure.v:913` `t_pure_preservation` — the master theorem for
    this file. **`Admitted` in Rocq**: every non-SIMD `Step_pure` case is dispatched to one
    of the 26 non-admitted lemmas above (`local_tee` included); the SIMD cases (`(* The
    rest are all simd instructions *)`) are never handled. Kept as `sorry` here,
    deliberately mirroring the Rocq gap. -/
theorem t_pure_preservation (v_s : store) (v_ais v_ais' : List admininstr) (v_C : context) (tf : functype) :
    Instrs_ok2 v_s v_C v_ais tf → Step_pure v_ais v_ais' → Instrs_ok2 v_s v_C v_ais' tf := sorry

end TLC
