import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas
import TypePreservationPure
import ExtensionLemmas

/-!
# TypePreservation

Lean port of `spectec/test-rocq/theories/type_preservation.v` — the
capstone file containing the main preservation theorem. Full digest:
`claude-logging/for-claude/digest_type_preservation.md`.

Rocq proof-completeness summary (mirror faithfully): of the 13
declarations, 3 lemmas are `Admitted` (`store_extension_reduce`,
`t_read_preservation`, `t_preservation_type`), and in **every case the
gap is exclusively the SIMD/vector-instruction cases** — everything else,
including the final top-level theorem `t_preservation` itself, is fully
`Qed`-proved in Rocq (though `t_preservation`'s `Qed` is only complete
*modulo* the 3 transitively-Admitted lemmas, which Coq's kernel treats as
axioms once accepted). The 10 non-Admitted declarations are genuine
targets for real Lean proofs in a later pass; the 3 Admitted ones are
`sorry`'d here deliberately, mirroring Rocq exactly rather than inventing
proofs Rocq itself doesn't have. **Correction (2026-09-30, bundle13
signature audit)**: `num_default_is_well_formed` is a 14th case the above
paragraph doesn't cover cleanly — its cited Rocq declaration
(`type_preservation.v:28`) is not `Admitted` but **entirely commented
out** in current Rocq (not stated at all), so it's neither one of the "3
Admitted" nor one of the "10 `Qed`'d." Kept `sorry`'d here regardless
(same deliberate-gap treatment as the 3 Admitted ones — inventing a proof
Rocq itself doesn't currently state isn't this project's job), but the
"of the 13 declarations" framing above should be read as 13 signatures
transcribed, not 13 declarations all still live in current Rocq.

Phase 1 (this file, first pass): every signature stated, proofs `sorry`.
-/

namespace TLC

/-- Rocq `type_preservation.v:13` `zero_is_well_formed`. -/
theorem zero_is_well_formed : wf_num_ numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)) := by
  refine wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN 0) ?_ ?_ rfl
  · simp [size, valtype_Inn]
  · simp only [size, valtype_Inn]
    exact wf_uN.uN_case_0 32 0 (by decide)

/-- Rocq `type_preservation.v:19` `num_default`. Default/zero value per numtype; used to
    build default locals in `t_read_preservation`'s Call_addr/frame-invocation case. -/
def num_default (nt : numtype) : num_ :=
  match nt with
  | .I32 => .mk_num__0 Inn.I32 (uN.mk_uN 0)
  | .I64 => .mk_num__0 Inn.I64 (uN.mk_uN 0)
  | .F32 => .mk_num__1 Fnn.F32 (fzero 32)
  | .F64 => .mk_num__1 Fnn.F64 (fzero 64)

/-- Rocq `type_preservation.v:28` `num_default_is_well_formed`. -/
theorem num_default_is_well_formed (nt : numtype) : wf_num_ nt (num_default nt) := by
  cases nt with
  | I32 =>
    refine wf_num_.num__case_0 numtype.I32 Inn.I32 (uN.mk_uN 0) ?_ ?_ rfl
    · simp [size, valtype_Inn]
    · simp only [size, valtype_Inn]
      exact wf_uN.uN_case_0 32 0 (by decide)
  | I64 =>
    refine wf_num_.num__case_0 numtype.I64 Inn.I64 (uN.mk_uN 0) ?_ ?_ rfl
    · simp [size, valtype_Inn]
    · simp only [size, valtype_Inn]
      exact wf_uN.uN_case_0 64 0 (by decide)
  | F32 =>
    refine wf_num_.num__case_1 numtype.F32 Fnn.F32 (fzero 32) ?_ rfl
    simp only [fzero, sizenn, numtype_Fnn, sizenn1]
    exact wf_fN.fN_case_0 32 (fNmag.SUBNORM 0)
      (wf_fNmag.fNmag_case_1 32 (2 - 2 ^ (((E 32 : Int) - 1).toNat)) 0 ⟨by decide, rfl⟩)
  | F64 =>
    refine wf_num_.num__case_1 numtype.F64 Fnn.F64 (fzero 64) ?_ rfl
    simp only [fzero, sizenn, numtype_Fnn, sizenn1]
    exact wf_fN.fN_case_0 64 (fNmag.SUBNORM 0)
      (wf_fNmag.fNmag_case_1 64 (2 - 2 ^ (((E 64 : Int) - 1).toNat)) 0 ⟨by decide, rfl⟩)

/-- Rocq `type_preservation.v:39` `inst_t_context_local_empty`. -/
theorem inst_t_context_local_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LOCALS = [] := by
  intro h; cases h; rfl

/-- Rocq `type_preservation.v:46` `inst_t_context_labels_empty`. -/
theorem inst_t_context_labels_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LABELS = [] := by
  intro h; cases h; rfl

/-- Generalized form of `t_preservation_vs_type'` below (same `remember`/
    `generalize dependent` encoding as `reduce_inst_unchanged_aux`). Of `Step`'s
    23 rules, 20 leave the frame alone outright — only `local_set` touches
    `LOCALS`, and only the two congruence rules (`ctxt_label`, `ctxt_instrs`)
    need the induction hypothesis; `ctxt_frame` changes only the *inner* frame.
    Rocq compresses the same case split into one `induction ...; try (...)`
    script backed by its `invert_ais_typing`/`resolve_all_pt` tactics. -/
private theorem t_preservation_vs_type'_aux (c1 c2 : config) (h : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' →
      Store_ok s → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS → inst_match C C' →
      Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s f'.LOCALS C'.LOCALS := by
  induction h
  case ctxt_label z vn i0 al z' al' _ _ _ ih =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 hsok hmi hvals him htype
    injection h1 with hz1 hais
    injection h2 with hz2 _
    subst hz1
    rw [← hais] at htype
    obtain ⟨_, _, hpt, _⟩ :=
      ais_single_typing_inversion s C' (admininstr.LABEL_ vn i0 al) t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, ts', _, _, _, hbody⟩ := hpt
    exact ih s f al s' f' al' C (prepend_label C' (list.mk_list ts')) [] ts rfl (by rw [hz2])
      hsok hmi hvals (construct_inst_prepend_label C C' (list.mk_list ts') him) hbody
  case ctxt_instrs z vl al al1 z' al' _ _ _ _ ih =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 hsok hmi hvals him htype
    injection h1 with hz1 hais
    injection h2 with hz2 _
    subst hz1
    rw [← hais] at htype
    obtain ⟨tm, _, hrest⟩ := ais_composition_typing s C' _ (al ++ al1) t1s t2s htype
    obtain ⟨tm2, hal, _⟩ := ais_composition_typing s C' al al1 tm t2s hrest
    exact ih s f al s' f' al' C C' tm tm2 rfl (by rw [hz2]) hsok hmi hvals him hal
  case ctxt_frame =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 _ _ hvals _ _
    injection h1 with hz1 _
    injection h2 with hz2 _
    injection hz1 with _ e1
    injection hz2 with _ e2
    subst e1
    subst e2
    exact hvals
  case local_set z v x =>
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 _ _ hvals _ htype
    injection h1 with hz1 hais
    injection h2 with hz2 _
    subst hz1
    simp only [with_local] at hz2
    injection hz2 with _ hf
    subst hf
    rw [← hais] at htype
    -- the value being written has exactly the local's declared type
    have heqs : [admininstr_val v, admininstr.LOCAL_SET x]
        = [admininstr_val v] ++ [admininstr.LOCAL_SET x] := rfl
    rw [heqs] at htype
    obtain ⟨t3s, h_ls, h_v⟩ :=
      ais_seq_typing_inversion s C' _ (admininstr_val v) t1s t2s htype
    obtain ⟨tv, hsub_v, hvok⟩ := ais_single_val_typing_inversion s C' v t1s t3s h_v
    obtain ⟨_, _, hls_pt, hsub_ls⟩ :=
      ais_single_typing_inversion s C' (admininstr.LOCAL_SET x) t3s t2s h_ls
    unfold ai_principal_typing at hls_pt
    obtain ⟨t, hls_eq, hlookup⟩ := hls_pt
    unfold mkFunctype at hls_eq
    simp only [functype.mk_functype.injEq, list.mk_list.injEq] at hls_eq
    obtain ⟨el1, el2⟩ := hls_eq
    subst el1; subst el2
    obtain ⟨_, hrsub⟩ := instrtype_sub_compose_eq [] [tv] [t] [] t1s t3s t2s hsub_v hsub_ls rfl
    have hnb : Forall (fun u => u ≠ valtype.BOT) [tv] := by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rw [hu]
      exact Val_ok_non_bot s v tv hvok
    have heqt := resulttype_sub_non_bot [tv] [t] hnb hrsub
    injection heqt with et _
    have hget : C'.LOCALS[proj_uN_0 x]! = t := by
      rw [List.getElem!_eq_getElem?_getD, hlookup]; rfl
    -- now transport the locals typing across the single-slot update
    obtain ⟨hlen, hall⟩ := hvals
    refine ⟨?_, ?_⟩
    · show C'.LOCALS.length = (f.LOCALS.modify (proj_uN_0 x) (fun _ => v)).length
      rw [List.length_modify]
      exact hlen
    · intro p hp
      rcases mem_zip_modify_right _ C'.LOCALS f.LOCALS (proj_uN_0 x) p hp with hp' | ⟨h1', h2', _⟩
      · exact hall p hp'
      · show Val_ok s p.2 p.1
        rw [h1', h2', hget, ← et]
        exact hvok
  all_goals (
    intro s f ais s' f' ais' C C' t1s t2s h1 h2 _ _ hvals _ _
    injection h1 with hz1 _
    injection h2 with hz2 _
    subst hz1
    try simp only [with_global, with_table, with_tableinst, with_elem, with_mem,
      with_meminst, with_data] at hz2
    injection hz2 with _ hf
    subst hf
    exact hvals)

/-- Rocq `type_preservation.v:53` `t_preservation_vs_type'`. Locals stay well-typed under
    one `Step` (store held fixed / pre-store-extension). -/
theorem t_preservation_vs_type' (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS → inst_match C C' →
    Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s f'.LOCALS C'.LOCALS :=
  fun hstep hsok hmi hvals him htype =>
    t_preservation_vs_type'_aux _ _ hstep s f ais s' f' ais' C C' t1s t2s rfl rfl hsok hmi hvals him htype

/-- Rocq `type_preservation.v:107` `t_preservation_vs_type`. Composition:
    `t_preservation_vs_type'` then `store_extension_vals` to transport across store
    extension. -/
theorem t_preservation_vs_type (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Extend_store s s' → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS →
    inst_match C C' → Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s' f'.LOCALS C'.LOCALS := by
  intro hstep hsok hext hmi hvals him htype
  exact Extend_store_vals s s' C'.LOCALS f'.LOCALS hext
    (t_preservation_vs_type' s f ais s' f' ais' C C' t1s t2s hstep hsok hmi hvals him htype)

/-- Rocq `type_preservation.v:123` `store_extension_reduce`. **`Admitted` in Rocq** — a
    massive induction on `Step`, complete for every case except 2 SIMD-instruction
    store-mutation cases (`(* SIMD instructions *) 1-2: admit.`). Establishes store-
    extension monotonicity + preservation of `Store_ok` across one reduction step. Kept as
    `sorry` here, mirroring the Rocq gap. -/
theorem store_extension_reduce (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (tf : functype) :
    wf_config (config.mk_config (state.mk_state s f) ais) →
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Moduleinst_ok s f.MODULE C → Instrs_ok2 s C' ais tf → inst_match C C' → Store_ok s →
    Extend_store s s' ∧ Store_ok s' := sorry

/-- Generalized form of `reduce_inst_unchanged` below. Rocq does the same
    thing with `remember ... as c1`/`remember ... as c2` plus `generalize
    dependent` before `induction HReduce`; Lean's `induction` needs the
    indices to be variables, so the two `config`s are generalized and the
    shapes recovered from equational premises instead. Every `Step`
    constructor either leaves the state alone, rewrites it with one of the
    `with_*` functions (all of which preserve `frame.MODULE` — `with_local`
    touches only `LOCALS`, the rest only the store), or is one of the two
    congruence rules that need the induction hypothesis; `ctxt_frame` is in
    the first group, since it changes only the *inner* frame. -/
private theorem reduce_inst_unchanged_aux (c1 c2 : config) (h : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' → f.MODULE = f'.MODULE := by
  induction h
  case ctxt_label z v_n i0 L z' L' _ _ _ ih =>
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    injection h2 with hz' _
    exact ih s f L s' f' L' (by rw [hz]) (by rw [hz'])
  case ctxt_instrs z vl L L1 z' L' _ _ _ _ ih =>
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    injection h2 with hz' _
    exact ih s f L s' f' L' (by rw [hz]) (by rw [hz'])
  case local_set z v_val x =>
    -- the only rule that touches the frame at all: `with_local` rewrites
    -- `LOCALS` and leaves `MODULE` alone.
    intro s f ais s' f' ais' h1 h2
    injection h1 with hz _
    subst hz
    injection h2 with hz' _
    simp only [with_local] at hz'
    injection hz' with _ hf
    subst hf
    rfl
  all_goals (
    intro s f ais s' f' ais' h1 h2
    simp_all [with_global, with_table, with_tableinst, with_elem, with_mem,
      with_meminst, with_data])

/-- Rocq `type_preservation.v:997` `reduce_inst_unchanged`. The module-instance component
    of the frame is invariant under `Step`. -/
theorem reduce_inst_unchanged (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    f.MODULE = f'.MODULE :=
  fun h => reduce_inst_unchanged_aux _ _ h s f ais s' f' ais' rfl rfl

/-- Rocq `type_preservation.v:1011` `t_read_preservation`. **`Admitted` in Rocq** — huge
    case-by-case induction on `Step_read`, complete except 5 SIMD-instruction read-
    reduction cases (`(* SIMD instructions *) 1-5: admit.`). Preservation under the
    read-only reduction relation (no store mutation). Kept as `sorry` here, mirroring the
    Rocq gap. -/
theorem t_read_preservation (v_s : store) (v_f : frame) (v_ais : List admininstr)
    (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step_read (config.mk_config (state.mk_state v_s v_f) v_ais) v_ais' →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C →
    Forall₂ (fun v_t v_val => Val_ok v_s v_val v_t) v_C'.LOCALS v_f.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s v_C' v_ais' (mkFunctype t1s t2s) := sorry

/-- Rocq `type_preservation.v:2409` `step_moduleinst`. Composition:
    `reduce_inst_unchanged` + `store_extension_moduleinst` + `store_extension_reduce`
    (transitively inherits `store_extension_reduce`'s SIMD gap). -/
theorem step_moduleinst (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store)
    (v_f' : frame) (v_ais' : List admininstr) (v_C v_C' : context) (v_tf : functype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step (config.mk_config (state.mk_state v_s v_f) v_ais) (config.mk_config (state.mk_state v_s' v_f') v_ais') →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais v_tf → Moduleinst_ok v_s' v_f'.MODULE v_C := by
  intro hwfc hstep hsok hmi him htype
  rw [← reduce_inst_unchanged v_s v_f v_ais v_s' v_f' v_ais' hstep]
  exact Extend_store_moduleinst v_s v_s' v_f.MODULE v_C
    (store_extension_reduce v_s v_f v_ais v_s' v_f' v_ais' v_C v_C' v_tf hwfc hstep hmi htype him hsok).1
    hmi

/-- Rocq `type_preservation.v:2425` `t_preservation_type`. **The central preservation
    lemma for the whole `Step` relation** (subsumes `t_read_preservation`). **`Admitted` in
    Rocq** — complete except 2 SIMD-instruction cases in the `Context Frame`/mutation
    dispatch (`(* The rest are all SIMD instructions *) 1-2: admit.`). Dispatches
    `Step_pure` to `t_pure_preservation` (`TypePreservationPure.lean`) and `Step_read` to
    `t_read_preservation` above — both of which have their own SIMD gaps, so this
    theorem's gap is a strict superset. Kept as `sorry` here, mirroring the Rocq gap. -/
theorem t_preservation_type (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store)
    (v_f' : frame) (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    wf_config (config.mk_config (state.mk_state v_s v_f) v_ais) →
    Step (config.mk_config (state.mk_state v_s v_f) v_ais) (config.mk_config (state.mk_state v_s' v_f') v_ais') →
    Store_ok v_s → Store_ok v_s' → Extend_store v_s v_s' →
    Moduleinst_ok v_s v_f.MODULE v_C → Moduleinst_ok v_s' v_f.MODULE v_C →
    Vals_ok v_s v_f.LOCALS v_C'.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s' v_C' v_ais' (mkFunctype t1s t2s) := sorry

/-! ### Plumbing for `t_preservation`

    `Frame_ok`'s conclusion types a frame at `<locals-only context> ++ C`
    (`wasm2.0.lean`), and `Config_ok`/`State_ok` carry that same appended
    context. These two small lemmas isolate the only two facts the top-level
    proof needs about that shape, so the (long) context literal appears in
    exactly one place. Rocq gets both for free from `resolve_inst_match` and
    its `_append`/`cats0` rewriting. -/

/-- Prefixing a context with a locals-only context leaves every component
    `inst_match` looks at untouched. -/
theorem inst_match_locals_append (tl : List valtype) (C : context) :
    inst_match C (({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [],
        ELEMS := [], DATAS := [], LOCALS := tl, LABELS := [], RETURN := none } : context) ++ C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- …and its `LOCALS` are exactly the prefix, since `Moduleinst_ok` forces the
    module context's own `LOCALS` to be empty (`inst_t_context_local_empty`). -/
theorem locals_append_eq (tl : List valtype) (C : context) (h : C.LOCALS = []) :
    ((({
        TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [],
        ELEMS := [], DATAS := [], LOCALS := tl, LABELS := [], RETURN := none } : context)
      ++ C) : context).LOCALS = tl := by
  show tl ++ C.LOCALS = tl
  rw [h, List.append_nil]

/-- Rocq `type_preservation.v:2668` `t_preservation`. **THE top-level theorem** — Rocq
    source comment: `(* Ultimate goal of project *)`. Whole-program preservation: reduction
    (`Step`) on a full `config` preserves well-typedness at the same fixed result type.
    Fully `Qed`-proved in Rocq (assembled from `store_extension_reduce`,
    `t_preservation_vs_type`, `t_preservation_type`, `reduce_inst_unchanged`,
    `store_extension_moduleinst`), but only complete *modulo* the 3 transitively-Admitted
    lemmas above. A genuine target for a real Lean proof once its dependencies are filled
    in (the proof itself, per Rocq, needs no case analysis beyond what those dependencies
    already provide — it is pure composition). -/
theorem t_preservation (c1 : config) (ts : resulttype) (c2 : config) :
    Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts := by
  intro hstep hcfg
  obtain ⟨⟨s1, f1⟩, ais1⟩ := c1
  obtain ⟨⟨s2, f2⟩, ais2⟩ := c2
  cases hcfg with
  | mk_Config_ok _ _ _ t_lst C hstate hexpr hwfC hwfcfg _ =>
    cases hstate with
    | mk_State_ok _ _ _ hsok hframe _ _ =>
      cases hframe with
      | mk_Frame_ok val_lst v_minst t_lst0 C0 hminst hlen hvals _ hwfC0 _ hwflocC =>
        cases hexpr with
        | mk_Expr_ok2 _ _ _ hinstrs _ _ _ =>
          -- well-formedness of the post-state, from the generated `Step_is_wf`
          have hwfcfg2 : wf_config (config.mk_config (state.mk_state s2 f2) ais2) :=
            Step_is_wf _ _ hwfcfg hstep
          have hwfais2 : Forall wf_admininstr ais2 := by
            cases hwfcfg2 with | config_case_0 _ _ _ h => exact h
          have hwfst2 : wf_state (state.mk_state s2 f2) := by
            cases hwfcfg2 with | config_case_0 _ _ h _ => exact h
          have hwfs2 : wf_store s2 := by
            cases hwfst2 with | state_case_0 _ _ h _ => exact h
          have hwff2 : wf_frame f2 := by
            cases hwfst2 with | state_case_0 _ _ _ h => exact h
          -- the module context's own LOCALS are empty, so the appended context's
          -- LOCALS are exactly the frame's local types
          have hloc : C0.LOCALS = [] := inst_t_context_local_empty s1 v_minst C0 hminst
          have him := inst_match_locals_append t_lst0 C0
          -- store extension + store typedness across the step
          obtain ⟨hext, hsok2⟩ := store_extension_reduce s1 _ ais1 s2 f2 ais2 C0 _ _
            hwfcfg hstep hminst hinstrs him hsok
          have hmod := reduce_inst_unchanged s1 _ ais1 s2 f2 ais2 hstep
          have hminst2 : Moduleinst_ok s2 v_minst C0 :=
            Extend_store_moduleinst s1 s2 v_minst C0 hext hminst
          -- locals stay well-typed
          have hvals2 := t_preservation_vs_type s1 _ ais1 s2 f2 ais2 C0 _ [] t_lst hstep hsok
            hext hminst (by rw [locals_append_eq t_lst0 C0 hloc]; exact ⟨hlen, hvals⟩) him hinstrs
          rw [locals_append_eq t_lst0 C0 hloc] at hvals2
          obtain ⟨hlen2, hvals2'⟩ := hvals2
          -- and so does the instruction sequence
          have hinstrs2 := t_preservation_type s1 _ ais1 s2 f2 ais2 C0 _ [] t_lst hwfcfg hstep
            hsok hsok2 hext hminst hminst2
            (by rw [locals_append_eq t_lst0 C0 hloc]; exact ⟨hlen, hvals⟩) him hinstrs
          -- reassemble
          exact Config_ok.mk_Config_ok s2 f2 ais2 t_lst _
            (State_ok.mk_State_ok s2 f2 _ hsok2
              (Frame_ok.mk_Frame_ok s2 f2.LOCALS f2.MODULE t_lst0 C0
                (by rw [← hmod]; exact hminst2) hlen2 hvals2' hwfs2 hwfC0 hwff2 hwflocC)
              hwfC hwfst2)
            (Expr_ok2.mk_Expr_ok2 s2 _ ais2 t_lst hinstrs2 hwfs2 hwfC hwfais2)
            hwfC hwfcfg2 hwfst2

end TLC
