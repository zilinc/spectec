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
declarations, only 3 lemmas are `Admitted` (`store_extension_reduce`,
`t_read_preservation`, `t_preservation_type`), and in **every case the
gap is exclusively the SIMD/vector-instruction cases** — everything else,
including the final top-level theorem `t_preservation` itself, is fully
`Qed`-proved in Rocq (though `t_preservation`'s `Qed` is only complete
*modulo* the 3 transitively-Admitted lemmas, which Coq's kernel treats as
axioms once accepted). The 10 non-Admitted declarations are genuine
targets for real Lean proofs in a later pass; the 3 Admitted ones are
`sorry`'d here deliberately, mirroring Rocq exactly rather than inventing
proofs Rocq itself doesn't have.

Phase 1 (this file, first pass): every signature stated, proofs `sorry`.
-/

namespace TLC

/-- Rocq `type_preservation.v:13` `zero_is_well_formed`. -/
theorem zero_is_well_formed : wf_num_ numtype.I32 (num_.mk_num__0 Inn.I32 (uN.mk_uN 0)) := sorry

/-- Rocq `type_preservation.v:19` `num_default`. Default/zero value per numtype; used to
    build default locals in `t_read_preservation`'s Call_addr/frame-invocation case. -/
def num_default (nt : numtype) : num_ :=
  match nt with
  | .I32 => .mk_num__0 Inn.I32 (uN.mk_uN 0)
  | .I64 => .mk_num__0 Inn.I64 (uN.mk_uN 0)
  | .F32 => .mk_num__1 Fnn.F32 (fzero 32)
  | .F64 => .mk_num__1 Fnn.F64 (fzero 64)

/-- Rocq `type_preservation.v:28` `num_default_is_well_formed`. -/
theorem num_default_is_well_formed (nt : numtype) : wf_num_ nt (num_default nt) := sorry

/-- Rocq `type_preservation.v:39` `inst_t_context_local_empty`. -/
theorem inst_t_context_local_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LOCALS = [] := sorry

/-- Rocq `type_preservation.v:46` `inst_t_context_labels_empty`. -/
theorem inst_t_context_labels_empty (s : store) (i : moduleinst) (C : context) :
    Moduleinst_ok s i C → C.LABELS = [] := sorry

/-- Rocq `type_preservation.v:53` `t_preservation_vs_type'`. Locals stay well-typed under
    one `Step` (store held fixed / pre-store-extension). -/
theorem t_preservation_vs_type' (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS → inst_match C C' →
    Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s f'.LOCALS C'.LOCALS := sorry

/-- Rocq `type_preservation.v:107` `t_preservation_vs_type`. Composition:
    `t_preservation_vs_type'` then `store_extension_vals` to transport across store
    extension. -/
theorem t_preservation_vs_type (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Store_ok s → Extend_store s s' → Moduleinst_ok s f.MODULE C → Vals_ok s f.LOCALS C'.LOCALS →
    inst_match C C' → Instrs_ok2 s C' ais (mkFunctype t1s t2s) → Vals_ok s' f'.LOCALS C'.LOCALS := sorry

/-- Rocq `type_preservation.v:123` `store_extension_reduce`. **`Admitted` in Rocq** — a
    massive induction on `Step`, complete for every case except 2 SIMD-instruction
    store-mutation cases (`(* SIMD instructions *) 1-2: admit.`). Establishes store-
    extension monotonicity + preservation of `Store_ok` across one reduction step. Kept as
    `sorry` here, mirroring the Rocq gap. -/
theorem store_extension_reduce (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (tf : functype) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Moduleinst_ok s f.MODULE C → Instrs_ok2 s C' ais tf → inst_match C C' → Store_ok s →
    Extend_store s s' ∧ Store_ok s' := sorry

/-- Rocq `type_preservation.v:997` `reduce_inst_unchanged`. The module-instance component
    of the frame is invariant under `Step`. -/
theorem reduce_inst_unchanged (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) :
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    f.MODULE = f'.MODULE := sorry

/-- Rocq `type_preservation.v:1011` `t_read_preservation`. **`Admitted` in Rocq** — huge
    case-by-case induction on `Step_read`, complete except 5 SIMD-instruction read-
    reduction cases (`(* SIMD instructions *) 1-5: admit.`). Preservation under the
    read-only reduction relation (no store mutation). Kept as `sorry` here, mirroring the
    Rocq gap. -/
theorem t_read_preservation (v_s : store) (v_f : frame) (v_ais : List admininstr)
    (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    Step_read (config.mk_config (state.mk_state v_s v_f) v_ais) v_ais' →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C →
    Forall₂ (fun v_t v_val => Val_ok v_s v_val v_t) v_C'.LOCALS v_f.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s v_C' v_ais' (mkFunctype t1s t2s) := sorry

/-- Rocq `type_preservation.v:2409` `step_moduleinst`. Composition:
    `reduce_inst_unchanged` + `store_extension_moduleinst` + `store_extension_reduce`
    (transitively inherits `store_extension_reduce`'s SIMD gap). -/
theorem step_moduleinst (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store)
    (v_f' : frame) (v_ais' : List admininstr) (v_C v_C' : context) (v_tf : functype) :
    Step (config.mk_config (state.mk_state v_s v_f) v_ais) (config.mk_config (state.mk_state v_s' v_f') v_ais') →
    Store_ok v_s → Moduleinst_ok v_s v_f.MODULE v_C → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais v_tf → Moduleinst_ok v_s' v_f'.MODULE v_C := sorry

/-- Rocq `type_preservation.v:2425` `t_preservation_type`. **The central preservation
    lemma for the whole `Step` relation** (subsumes `t_read_preservation`). **`Admitted` in
    Rocq** — complete except 2 SIMD-instruction cases in the `Context Frame`/mutation
    dispatch (`(* The rest are all SIMD instructions *) 1-2: admit.`). Dispatches
    `Step_pure` to `t_pure_preservation` (`TypePreservationPure.lean`) and `Step_read` to
    `t_read_preservation` above — both of which have their own SIMD gaps, so this
    theorem's gap is a strict superset. Kept as `sorry` here, mirroring the Rocq gap. -/
theorem t_preservation_type (v_s : store) (v_f : frame) (v_ais : List admininstr) (v_s' : store)
    (v_f' : frame) (v_ais' : List admininstr) (v_C v_C' : context) (t1s t2s : List valtype) :
    Step (config.mk_config (state.mk_state v_s v_f) v_ais) (config.mk_config (state.mk_state v_s' v_f') v_ais') →
    Store_ok v_s → Store_ok v_s' → Extend_store v_s v_s' →
    Moduleinst_ok v_s v_f.MODULE v_C → Moduleinst_ok v_s' v_f.MODULE v_C →
    Vals_ok v_s v_f.LOCALS v_C'.LOCALS → inst_match v_C v_C' →
    Instrs_ok2 v_s v_C' v_ais (mkFunctype t1s t2s) → Instrs_ok2 v_s' v_C' v_ais' (mkFunctype t1s t2s) := sorry

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
    Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts := sorry

end TLC
