import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas
import TypePreservationPure

/-!
# ExtensionLemmas

Lean port of `spectec/test-rocq/theories/extension_lemmas.v`. Full
digest: `claude-logging/for-claude/digest_subtyping_and_extension_lemmas.md`.

**Naming note (RESOLVED, session 1 continuation)**: Rocq's
`Store_extension`/`Func_extension`/`Table_extension`/`Mem_extension`/
`Global_extension`/`Elem_extension`/`Data_extension` are used pervasively
throughout `extension_lemmas.v` and `type_preservation.v`, but a direct
`grep -rn "Inductive Func_extension\|Definition Func_extension\|Notation
Func_extension"` (and the same for every other name in that list) across
**every** `.v` file in `test-rocq/theories/` returns **zero hits** — these
names are not declared *anywhere* in the current Rocq sources, under any
declaration form. The only store-extension-shaped relations that actually
exist (confirmed both in `wasm.v` and in `wasm2.0.lean`, both generated
from the same EL spec) are `Extend_store`/`Extend_funcinst`/
`Extend_tableinst`/`Extend_meminst`/`Extend_globalinst`/`Extend_eleminst`/
`Extend_datainst`. Best explanation, strongly supported by the evidence:
`extension_lemmas.v` (and `type_preservation.v`) were written against an
**earlier generation of the SpecTec Rocq backend** that named these
relations `Store_extension`/`Func_extension`/etc.; the backend was later
regenerated with the `Extend_*` naming convention (matching `wasm2.0.lean`'s
convention, which never used the old names at all), and the hand-written
lemma files were never updated to match. Under this theory, **Rocq's
`extension_lemmas.v` and `type_preservation.v` likely do not currently
compile against the current `wasm.v`** — consistent with this session's
earlier failed attempt to get `dune build` to run at all (blocked on a
missing `mathcomp` findlib package, so this couldn't be confirmed
directly; worth another attempt in a future session, ideally by fixing
the opam switch rather than assuming). This file uses the confirmed
`Extend_*` names throughout (`Store_extension s s'` → `Extend_store s s'`,
etc.) — the semantic content of each relation (checked field-by-field
against `extension_lemmas.v`'s usage) lines up with the corresponding
`Extend_*` relation, so this is very likely the intended 1:1
correspondence, not a coincidence. **Consequence for lemma signatures**:
the `Extend_*` relations' constructors (confirmed by reading
`wasm2.0.lean` directly) bake in `wf_*` well-formedness premises for
`Extend_funcinst`/`Extend_globalinst`/`Extend_tableinst`/`Extend_meminst`/
`Extend_datainst` (but NOT `Extend_eleminst`, which has none) — Rocq's own
`func_extension_refl0`/etc. (about the now-undefined `Func_extension`)
apparently did NOT need such premises (one-line `econstructor.` proofs),
which is further evidence those Rocq lemmas are stale/were written
against a `Func_extension` with a laxer constructor. The lemma
*signatures* below have been corrected to add the `wf_*` hypotheses the
*current*, real `Extend_*` relations actually require — this is a
deliberate deviation from a literal reading of the (now-inapplicable)
Rocq statement, in service of the same underlying mathematical fact
(reflexivity of the extension order) stated against the relation that
actually exists in this project's target. A prior Lean session's
`Extension.lean` (see `digest_prior_lean_attempts.md`) independently
arrived at the same corrected signatures (it read `wasm2.0.lean`'s
`Extend_*` definitions directly rather than trusting the Rocq lemma
signature) — its proofs are reused below.

Similarly, `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` (cited by the
digest for the custom `Scheme`-based mutual induction backing
`store_extension_ais`) do not exist under those names either — the
matching argument shapes correspond to `Instrs_ok2`/`Instr_ok2`, used
below.

Phase 1 (this file, first pass): every signature stated, proofs `sorry`.
-/

namespace TLC

/-! ## `Store_ok` inversion (extension_lemmas.v:20-209) -/

/-- Rocq `extension_lemmas.v:20` `Val_ok_store`. `Val_ok` for a value at a valtype depends
    only on `store.FUNCS`; stated here as swap-invariance across the other 5 fields. -/
theorem Val_ok_store (f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 : _) (v : val) (t : valtype) :
    Val_ok (store.MKstore f1 g1 t1 m1 e1 d1) v t ↔ Val_ok (store.MKstore f1 g2 t2 m2 e2 d2) v t := sorry

/-- Rocq `extension_lemmas.v:57` `s_invert_funcs`. -/
theorem s_invert_funcs (s : store) : Store_ok s →
    ∃ fts, Forall₂ (fun f t => ∃ minst v_func, f = funcinst.MKfuncinst t minst v_func) s.FUNCS fts := sorry

/-- Rocq `extension_lemmas.v:89` `s_invert_globals`. -/
theorem s_invert_globals (s : store) : Store_ok s →
    ∃ gts, Forall₂ (fun g t => ∃ v_mut v_vt v_v, g = globalinst.MKglobalinst t v_v ∧
      t = globaltype.mk_globaltype v_mut v_vt ∧ Val_ok s v_v v_vt) s.GLOBALS gts := sorry

/-- Rocq `extension_lemmas.v:121` `s_invert_mems`. Encodes the memory page-count invariant
    (`v_n = byte-length / 64KiB`) and the hard cap `v_m ≤ 2^16` pages. -/
theorem s_invert_mems (s : store) : Store_ok s →
    ∃ mts, Forall₂ (fun m t => ∃ b_lst v_n v_m, m = meminst.MKmeminst t b_lst ∧
      t = memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (some (uN.mk_uN v_m))) ∧
      v_n = b_lst.length / (64 * Ki) ∧ v_n ≤ v_m ∧ v_m ≤ 2 ^ 16) s.MEMS mts := sorry

/-- Rocq `extension_lemmas.v:172` `s_invert_tables`. -/
theorem s_invert_tables (s : store) : Store_ok s →
    ∃ tbts, Forall₂ (fun tb tbt => ∃ ref_lst v_m rt, tb = tableinst.MKtableinst tbt ref_lst ∧
      tbt = tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN ref_lst.length) (some (uN.mk_uN v_m))) rt ∧
      Tabletype_ok tbt ∧ Forall (fun r => Ref_ok s r rt) ref_lst) s.TABLES tbts := sorry

/-! ## `Extend_store` component-wise inversion — the central structural pattern
    (extension_lemmas.v:211-289) -/

/-- Rocq `extension_lemmas.v:211` `se_invert_funcs`. -/
theorem se_invert_funcs (s s' : store) : Extend_store s s' →
    ∃ fs' fs2, Forall₂ Extend_funcinst s.FUNCS fs' ∧ s'.FUNCS = fs' ++ fs2 := sorry

/-- Rocq `extension_lemmas.v:224` `se_invert_tables`. -/
theorem se_invert_tables (s s' : store) : Extend_store s s' →
    ∃ tbs' tbs2, Forall₂ Extend_tableinst s.TABLES tbs' ∧ s'.TABLES = tbs' ++ tbs2 := sorry

/-- Rocq `extension_lemmas.v:238` `se_invert_mems`. -/
theorem se_invert_mems (s s' : store) : Extend_store s s' →
    ∃ ms' ms2, Forall₂ Extend_meminst s.MEMS ms' ∧ s'.MEMS = ms' ++ ms2 := sorry

/-- Rocq `extension_lemmas.v:252` `se_invert_store_globals`. -/
theorem se_invert_store_globals (s s' : store) : Extend_store s s' →
    ∃ gs' gs2, Forall₂ Extend_globalinst s.GLOBALS gs' ∧ s'.GLOBALS = gs' ++ gs2 := sorry

/-- Rocq `extension_lemmas.v:266` `se_invert_elems`. -/
theorem se_invert_elems (s s' : store) : Extend_store s s' →
    ∃ es' es2, Forall₂ Extend_eleminst s.ELEMS es' ∧ s'.ELEMS = es' ++ es2 := sorry

/-- Rocq `extension_lemmas.v:280` `se_invert_datas`. -/
theorem se_invert_datas (s s' : store) : Extend_store s s' →
    ∃ ds' ds2, Forall₂ Extend_datainst s.DATAS ds' ∧ s'.DATAS = ds' ++ ds2 := sorry

/-! ## `Moduleinst_ok`/`inst_match` interaction with store contents (extension_lemmas.v:294-431) -/

/-- Rocq `extension_lemmas.v:294` `minst_invert_functypes`. -/
theorem minst_invert_functypes (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' → C'.TYPES = minst.TYPES := sorry

/-- Rocq `extension_lemmas.v:303` `minst_invert_funcs`. -/
theorem minst_invert_funcs (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun fa ft => ∃ minst1 v_func, fa < v_S.FUNCS.length ∧
      lookup_total v_S.FUNCS fa = funcinst.MKfuncinst ft minst1 v_func) minst.FUNCS C'.FUNCS := sorry

/-- Rocq `extension_lemmas.v:325` `minst_invert_tables`. Involves `Limits_sub`: the
    context may present widened limits relative to the concrete table instance. -/
theorem minst_invert_tables (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun tba tbt => ∃ rt lim lim' tbr, tba < v_S.TABLES.length ∧
      tbt = tabletype.mk_tabletype lim' rt ∧ Limits_sub lim lim' ∧
      lookup_total v_S.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype lim rt) tbr)
      minst.TABLES C'.TABLES := sorry

/-- Rocq `extension_lemmas.v:350` `minst_invert_globals`. -/
theorem minst_invert_globals (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ga gt => ∃ v_mut v_valtype v_val, gt = globaltype.mk_globaltype v_mut v_valtype ∧
      lookup_total v_S.GLOBALS ga = globalinst.MKglobalinst (globaltype.mk_globaltype v_mut v_valtype) v_val)
      minst.GLOBALS C'.GLOBALS := sorry

/-- Rocq `extension_lemmas.v:373` `minst_invert_mems`. Involves `Memtype_sub`. -/
theorem minst_invert_mems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ma mt => ∃ v_mt b_lst, ma < v_S.MEMS.length ∧ Memtype_sub v_mt mt ∧
      lookup_total v_S.MEMS ma = meminst.MKmeminst v_mt b_lst) minst.MEMS C'.MEMS := sorry

/-- Rocq `extension_lemmas.v:395` `minst_invert_elems`. -/
theorem minst_invert_elems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ea et => ∃ ref_lst, ea < v_S.ELEMS.length ∧ Forall (fun r => Ref_ok v_S r et) ref_lst ∧
      lookup_total v_S.ELEMS ea = eleminst.MKeleminst et ref_lst) minst.ELEMS C'.ELEMS := sorry

/-- Rocq `extension_lemmas.v:426` `minst_invert_datas`. -/
theorem minst_invert_datas (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    minst.DATAS.length = C'.DATAS.length ∧
      Forall (fun da => ∃ b_lst, da < v_S.DATAS.length ∧ lookup_total v_S.DATAS da = datainst.MKdatainst b_lst)
        minst.DATAS := sorry

/-! ## Misc lookup/inversion lemmas (extension_lemmas.v:532-627) -/

/-- Rocq `extension_lemmas.v:532` `lookup_global`. -/
theorem lookup_global (v_a : Nat) (v_C v_C' : context) (v_mut : «mut») (v_vt : valtype) (v_S : store) (minst : moduleinst) :
    v_a < v_C'.GLOBALS.length → lookup_total v_C'.GLOBALS v_a = globaltype.mk_globaltype v_mut v_vt →
    Moduleinst_ok v_S minst v_C → inst_match v_C v_C' → Store_ok v_S →
    Val_ok v_S (lookup_total v_S.GLOBALS (lookup_total minst.GLOBALS v_a)).VALUE v_vt := sorry

/-- Rocq `extension_lemmas.v:572` `bt_inversion`. The computable elaboration function
    `fun_blocktype` agrees with the declarative `Blocktype_ok` relation's chosen functype. -/
theorem bt_inversion (v_S : store) (v_C v_C' : context) (r_v_f : frame) (b_lstt : blocktype)
    (ts1 ts2 bt1 bt2 : List valtype) :
    Moduleinst_ok v_S r_v_f.MODULE v_C → Blocktype_ok v_C' b_lstt (mkFunctype ts1 ts2) →
    fun_blocktype (state.mk_state v_S r_v_f) b_lstt = mkFunctype bt1 bt2 → inst_match v_C v_C' →
    ts1 = bt1 ∧ ts2 = bt2 := sorry

/-- Rocq `extension_lemmas.v:600` `tc_func_reference2`. -/
theorem tc_func_reference2 (v_S : store) (v_C : context) (minst : moduleinst) (idx : Nat) (tf : functype) (v_type : funcinst) :
    lookup_total minst.TYPES idx = v_type.TYPE → Moduleinst_ok v_S minst v_C →
    lookup_total v_C.TYPES idx = tf → tf = v_type.TYPE := sorry

/-- Rocq `extension_lemmas.v:611` `store_typed_exterval_types`. -/
theorem store_typed_exterval_types (v_S : store) (v_f : funcinst) (v_a : Nat) :
    v_a < v_S.FUNCS.length → lookup_total v_S.FUNCS v_a = v_f → Store_ok v_S →
    Externaddr_ok v_S (externaddr.FUNC v_a) (externtype.FUNC v_f.TYPE) := sorry

/-! ## Extension relations are reflexive per store-component kind (extension_lemmas.v:629-793) -/

/-- Rocq `extension_lemmas.v:629` `func_extension_refl0` (about the now-stale
    `Func_extension`; corrected here to the real `Extend_funcinst`, which — unlike Rocq's
    `Func_extension` — bakes in a `wf_funcinst` premise; see the naming note above). Proof
    reused from a prior Lean session's `Extension.lean` (`extend_funcinst_refl`), which
    independently derived this same corrected signature. -/
theorem func_extension_refl0 {f : funcinst} (h : wf_funcinst f) : Extend_funcinst f f := by
  obtain ⟨ft, mm, fc⟩ := f
  exact Extend_funcinst.mk_Extend_funcinst ft mm fc h

theorem func_extension_refl {f : List funcinst} (h : Forall wf_funcinst f) :
    Forall₂ Extend_funcinst f f := by
  induction f with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    have hx : wf_funcinst x := h x (by simp)
    have hxs : Forall wf_funcinst xs := fun a ha => h a (by simp [ha])
    rcases hp with hp | hp
    · rw [hp]; exact func_extension_refl0 hx
    · exact ih hxs p hp

/-- Rocq `extension_lemmas.v:646` `table_extension_refl0`, corrected to `Extend_tableinst`
    (see naming note). Proof reused from `Extension.lean` (`extend_tableinst_refl`). -/
theorem table_extension_refl0 {t : tableinst} (h : wf_tableinst t) : Extend_tableinst t t := by
  obtain ⟨ty, refs⟩ := t
  obtain ⟨lim, rt⟩ := ty
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | u32opt
  · exact Extend_tableinst.mk_Extend_tableinst v_n none rt refs v_n refs
      (Nat.le_refl v_n) (Nat.le_refl refs.length) h h
  · obtain ⟨n'⟩ := u32opt
    exact Extend_tableinst.mk_Extend_tableinst v_n (some n') rt refs v_n refs
      (Nat.le_refl v_n) (Nat.le_refl refs.length) h h

theorem table_extension_refl {t : List tableinst} (h : Forall wf_tableinst t) :
    Forall₂ Extend_tableinst t t := by
  induction t with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    have hx : wf_tableinst x := h x (by simp)
    have hxs : Forall wf_tableinst xs := fun a ha => h a (by simp [ha])
    rcases hp with hp | hp
    · rw [hp]; exact table_extension_refl0 hx
    · exact ih hxs p hp

/-- Rocq `extension_lemmas.v:673` `mem_extension_refl0`, corrected to `Extend_meminst`
    (see naming note). Proof reused from `Extension.lean` (`extend_meminst_refl`). -/
theorem mem_extension_refl0 {m : meminst} (h : wf_meminst m) : Extend_meminst m m := by
  obtain ⟨ty, bs⟩ := m
  obtain ⟨lim⟩ := ty
  obtain ⟨v_u32, u32_opt⟩ := lim
  obtain ⟨v_n⟩ := v_u32
  rcases u32_opt with _ | u32opt
  · exact Extend_meminst.mk_Extend_meminst v_n none bs v_n bs
      (Nat.le_refl v_n) (Nat.le_refl bs.length) h h
  · obtain ⟨n'⟩ := u32opt
    exact Extend_meminst.mk_Extend_meminst v_n (some n') bs v_n bs
      (Nat.le_refl v_n) (Nat.le_refl bs.length) h h

theorem mem_extension_refl {m : List meminst} (h : Forall wf_meminst m) :
    Forall₂ Extend_meminst m m := by
  induction m with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    have hx : wf_meminst x := h x (by simp)
    have hxs : Forall wf_meminst xs := fun a ha => h a (by simp [ha])
    rcases hp with hp | hp
    · rw [hp]; exact mem_extension_refl0 hx
    · exact ih hxs p hp

/-- Rocq `extension_lemmas.v:699` `global_extension_refl_0`, corrected to
    `Extend_globalinst` (see naming note). Proof reused from `Extension.lean`
    (`extend_globalinst_refl`). -/
theorem global_extension_refl_0 {g : globalinst} (h : wf_globalinst g) : Extend_globalinst g g := by
  obtain ⟨ty, v⟩ := g
  obtain ⟨v_mut, t⟩ := ty
  exact Extend_globalinst.mk_Extend_globalinst v_mut t v v (Or.inr rfl) h h

theorem global_extension_refl {g : List globalinst} (h : Forall wf_globalinst g) :
    Forall₂ Extend_globalinst g g := by
  induction g with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    have hx : wf_globalinst x := h x (by simp)
    have hxs : Forall wf_globalinst xs := fun a ha => h a (by simp [ha])
    rcases hp with hp | hp
    · rw [hp]; exact global_extension_refl_0 hx
    · exact ih hxs p hp

/-- Rocq `extension_lemmas.v:725` `elem_extension_refl0`. `Extend_eleminst` has no `wf_*`
    premise (matches Rocq — no `wf_eleminst` exists on either side), so this one needs no
    correction. Proof reused from `Extension.lean` (`extend_eleminst_refl`). -/
theorem elem_extension_refl0 (e : eleminst) : Extend_eleminst e e := by
  obtain ⟨rt, refs⟩ := e
  exact Extend_eleminst.mk_Extend_eleminst rt refs refs (Or.inl rfl)

theorem elem_extension_refl (e : List eleminst) : Forall₂ Extend_eleminst e e := by
  induction e with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with hp | hp
    · rw [hp]; exact elem_extension_refl0 x
    · exact ih p hp

/-- Rocq `extension_lemmas.v:746` `data_extension_refl0`, corrected to `Extend_datainst`
    (see naming note). Proof reused from `Extension.lean` (`extend_datainst_refl`). -/
theorem data_extension_refl0 {d : datainst} (h : wf_datainst d) : Extend_datainst d d := by
  obtain ⟨bs⟩ := d
  exact Extend_datainst.mk_Extend_datainst bs bs (Or.inl rfl) h h

theorem data_extension_refl {d : List datainst} (h : Forall wf_datainst d) :
    Forall₂ Extend_datainst d d := by
  induction d with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    have hx : wf_datainst x := h x (by simp)
    have hxs : Forall wf_datainst xs := fun a ha => h a (by simp [ha])
    rcases hp with hp | hp
    · rw [hp]; exact data_extension_refl0 hx
    · exact ih hxs p hp

/-- Bounds side-condition needed by `Extend_store`'s constructor: every index into
    `List.range l.length` is `< l.length`. No Rocq counterpart (new plumbing needed only
    because `wasm2.0.lean` represents `Extend_store` via `Forall _ (List.range n)` index
    bounds rather than Rocq's `holds_upto` predicate). Reused from a prior Lean session's
    `Extension.lean` (`forall_range_lt`). -/
theorem forall_range_lt {α : Type} (l : List α) :
    Forall (fun a => a < l.length) (List.range l.length) := by
  intro a ha
  exact List.mem_range.mp ha

/-- Lifts a single-instance reflexivity fact, plus a well-formedness `Forall` over a list,
    to the index-`Forall`-over-`List.range` shape `Extend_store` needs. New plumbing, no
    Rocq counterpart (see `forall_range_lt`). Reused from `Extension.lean`
    (`forall_range_refl`). -/
theorem forall_range_refl {α : Type} [Inhabited α] (l : List α) (P : α → Prop)
    (R : α → α → Prop) (hP : Forall P l) (hR : ∀ x, P x → R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a ha
  have ha' : a < l.length := List.mem_range.mp ha
  have hmem : l[a]! ∈ l := by
    rw [getElem!_pos l a ha']
    exact List.getElem_mem ha'
  exact hR _ (hP _ hmem)

/-- As `forall_range_refl`, but for `Extend_eleminst`, which has no well-formedness side
    condition. Reused from `Extension.lean` (`forall_range_refl_noWf`). -/
theorem forall_range_refl_noWf {α : Type} [Inhabited α] (l : List α) (R : α → α → Prop)
    (hR : ∀ x, R x x) : Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a _
  exact hR _

/-- Rocq `extension_lemmas.v:767` `store_extension_refl`, corrected to `Extend_store` (see
    naming note). **No explicit `store_extension_trans` (transitivity) lemma exists
    anywhere in the Rocq file** — downstream preservation proofs re-derive extension facts
    per reduction step rather than composing two `Extend_store` proofs. Not ported here
    either, matching the Rocq gap. Proof reused from a prior Lean session's
    `Extension.lean` (`extend_store_refl`). -/
theorem store_extension_refl {s : store} (h : wf_store s) : Extend_store s s := by
  cases h with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    have hwf : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    exact Extend_store.mk_Extend_store _ _
      (forall_range_lt globals) (forall_range_lt globals)
      (forall_range_refl globals wf_globalinst Extend_globalinst hglobals
        (fun x hx => global_extension_refl_0 hx))
      (forall_range_lt mems) (forall_range_lt mems)
      (forall_range_refl mems wf_meminst Extend_meminst hmems
        (fun x hx => mem_extension_refl0 hx))
      (forall_range_lt tables) (forall_range_lt tables)
      (forall_range_refl tables wf_tableinst Extend_tableinst htables
        (fun x hx => table_extension_refl0 hx))
      (forall_range_lt funcs) (forall_range_lt funcs)
      (forall_range_refl funcs wf_funcinst Extend_funcinst hfuncs
        (fun x hx => func_extension_refl0 hx))
      (forall_range_lt datas) (forall_range_lt datas)
      (forall_range_refl datas wf_datainst Extend_datainst hdatas
        (fun x hx => data_extension_refl0 hx))
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst elem_extension_refl0)
      hwf hwf

/-- Rocq `extension_lemmas.v:787` `funcinst_same`. `Extend_funcinst` forces literal
    equality (funcs are immutable once allocated) — used pervasively downstream to erase
    func-extension side conditions.

    **CAVEAT (not present in Rocq)**: `wasm2.0.lean`'s `Forall₂` is a zip-based `def`
    (`∀ t ∈ xs.zip ys, P t.1 t.2`, see `ExtendedDeriveDecEq.lean`), which does NOT force
    `f1.length = f2.length` the way Rocq's inductive `Forall2` does — so `Forall₂
    Extend_funcinst f1 f2` alone is satisfiable even when `f1`/`f2` have different lengths
    (e.g. `f1` longer, with the extra tail elements simply never constrained). This lemma
    is therefore NOT provable as literally stated below without an extra length hypothesis;
    every actual call site in `extension_lemmas.v` applies it to a `Forall₂` fact that
    arose alongside a separate length-equality fact (e.g. from `se_invert_funcs`'s
    `Forall₂ Extend_funcinst s.FUNCS fs'` together with knowing `fs'` came from splitting
    `s'.FUNCS`). Left as `sorry` deliberately — needs either restating with an explicit
    `f1.length = f2.length` hypothesis, or a case-by-case fix at each call site once this
    file's later lemmas (`store_extension_ref` etc.) are actually proved. Flagged here
    rather than silently adding a hypothesis that would make this lemma's signature
    diverge from how it may be invoked positionally elsewhere. -/
theorem funcinst_same (f1 f2 : List funcinst) : Forall₂ Extend_funcinst f1 f2 → f1 = f2 := sorry

/-! ## `Extend_store` preserves `Ref_ok`/`Val_ok` (extension_lemmas.v:796-877) -/

theorem store_extension_ref (v_S v_S' : store) (v_t : reftype) (v_val : ref) :
    Extend_store v_S v_S' → Ref_ok v_S v_val v_t → Ref_ok v_S' v_val v_t := sorry

theorem store_extension_refs (v_S v_S' : store) (v_ts : List reftype) (v_vals : List ref) :
    Extend_store v_S v_S' → Forall₂ (fun t v => Ref_ok v_S v t) v_ts v_vals →
    Forall₂ (fun t v => Ref_ok v_S' v t) v_ts v_vals := sorry

theorem store_extension_val (v_S v_S' : store) (v_t : valtype) (v_val : val) :
    Extend_store v_S v_S' → Val_ok v_S v_val v_t → Val_ok v_S' v_val v_t := sorry

theorem store_extension_vals (v_S v_S' : store) (v_t : List valtype) (v_val : List val) :
    Extend_store v_S v_S' → Vals_ok v_S v_val v_t → Vals_ok v_S' v_val v_t := sorry

theorem config_same (s s' : store) (f f' : frame) (ais ais' : List admininstr) :
    config.mk_config (state.mk_state s f) ais = config.mk_config (state.mk_state s' f') ais' →
    s = s' ∧ f = f' ∧ ais = ais' := sorry

theorem config_same2 (s s' : store) (f f' : frame) (ais ais' : List admininstr) :
    s = s' ∧ f = f' ∧ ais = ais' →
    config.mk_config (state.mk_state s f) ais = config.mk_config (state.mk_state s' f') ais' := sorry

/-! ## Extension facts produced by specific store-mutating operations
    (extension_lemmas.v:885-1134) -/

/-- Rocq `extension_lemmas.v:885` `global_set_global_extension`. `global.set` on a
    `MUT_MUT` slot satisfies `Extend_globalinst` pointwise. -/
theorem global_set_global_extension (v_g : List globalinst) (v_idx : Nat) (v_valtype : valtype)
    (v_val_0 v_val_1 : val) :
    v_idx < v_g.length → lookup_total v_g v_idx = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) v_valtype) v_val_0 →
    Forall₂ Extend_globalinst v_g (list_update_func v_g v_idx (fun g => { g with VALUE := v_val_1 })) := sorry

/-- Rocq `extension_lemmas.v:916` `store_none_mem_extension`. `memory.store` (in-place
    byte-slice overwrite, memtype unchanged). -/
theorem store_none_mem_extension (v_ms : List meminst) (v_idx : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_l v_n_len : Nat) (v_nb : List byte) :
    v_idx < v_ms.length → lookup_total v_ms v_idx = meminst.MKmeminst v_mt b_lst →
    Forall₂ Extend_meminst v_ms
      (list_update_func v_ms v_idx (fun m => { m with BYTES := list_slice_update m.BYTES v_l v_n_len v_nb })) := sorry

/-- Rocq `extension_lemmas.v:950` `memory_grow_mem_extension`. `memory.grow` (append
    `v_n` zero-pages, bump min-limit, checked against max `v_j`). -/
theorem memory_grow_mem_extension (v_ms : List meminst) (v_idx : Nat) (b_lst : List byte) (v_i v_n v_j : Nat) :
    v_idx < v_ms.length →
    lookup_total v_ms v_idx = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN v_i) (some (uN.mk_uN v_j)))) b_lst →
    v_i + v_n ≤ v_j →
    Forall₂ Extend_meminst v_ms (list_update_func v_ms v_idx (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (v_i + v_n)) (some (uN.mk_uN v_j))))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)))) := sorry

/-- Rocq `extension_lemmas.v:990` `table_set_table_extension`. `table.set` (single-slot
    ref update). -/
theorem table_set_table_extension (v_tbs : List tableinst) (v_idx : Nat) (tbt : tabletype) (tbr : List ref)
    (v_i : Nat) (v_tbr : ref) :
    v_idx < v_tbs.length → lookup_total v_tbs v_idx = tableinst.MKtableinst tbt tbr →
    Forall₂ Extend_tableinst v_tbs
      (list_update_func v_tbs v_idx (fun tb => { tb with REFS := list_update_func tb.REFS v_i (fun _ => v_tbr) })) := sorry

/-- Rocq `extension_lemmas.v:1030` `table_grow_table_extension`. `table.grow` (append `n`
    copies of `ref`, bump min-limit). -/
theorem table_grow_table_extension (v_tbs : List tableinst) (v_idx : Nat) (j : Option uN) (r : ref)
    (rt : reftype) (nn : Nat) (tbr : List ref) :
    v_idx < v_tbs.length →
    lookup_total v_tbs v_idx = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN tbr.length) j) rt) tbr →
    Forall₂ Extend_tableinst v_tbs (list_update_func v_tbs v_idx (fun _ =>
      tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (tbr.length + nn)) j) rt)
        (tbr ++ List.replicate nn r))) := sorry

/-- Rocq `extension_lemmas.v:1075` `elem_drop_elem_extension`. `elem.drop` clears an elem
    segment's REFS to `[]`. -/
theorem elem_drop_elem_extension (es : List eleminst) (idx : Nat) :
    idx < es.length → Forall₂ Extend_eleminst es (list_update_func es idx (fun e => { e with REFS := [] })) := sorry

/-- Rocq `extension_lemmas.v:1098` `data_drop_data_extension`. `data.drop` analogue. -/
theorem data_drop_data_extension (ds : List datainst) (idx : Nat) :
    idx < ds.length → Forall₂ Extend_datainst ds (list_update_func ds idx (fun _ => datainst.MKdatainst [])) := sorry

/-- Rocq `extension_lemmas.v:1121` `update_global_unchanged`. Frame lemma: updating only
    `store.GLOBALS` leaves every other component (and globals-length) unchanged. -/
theorem update_global_unchanged (v_S v_S' : store) (func : globalinst → globalinst) (v_idx : Nat) :
    v_S' = { v_S with GLOBALS := list_update_func v_S.GLOBALS v_idx func } →
    v_S.FUNCS = v_S'.FUNCS ∧ v_S.TABLES = v_S'.TABLES ∧ v_S.GLOBALS.length = v_S'.GLOBALS.length ∧
      v_S.MEMS = v_S'.MEMS ∧ v_S.ELEMS = v_S'.ELEMS ∧ v_S.DATAS = v_S'.DATAS := sorry

/-! ## `Externaddr_ok` preserved by store extension (extension_lemmas.v:1137-1389) -/

theorem addrs_store_funcs_extension (v_S v_S' : store) (v_funcaddr : Nat) (fs1' fs2 : List funcinst) (v_ft : functype) :
    Externaddr_ok v_S (externaddr.FUNC v_funcaddr) (externtype.FUNC v_ft) →
    v_S'.FUNCS = fs1' ++ fs2 → Forall₂ Extend_funcinst v_S.FUNCS fs1' →
    Externaddr_ok v_S' (externaddr.FUNC v_funcaddr) (externtype.FUNC v_ft) := sorry

theorem addrs_tables_extension (v_S v_S' : store) (v_tableaddr : Nat) (tbs1' tbs2 : List tableinst) (tt : tabletype) :
    Externaddr_ok v_S (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) →
    v_S'.TABLES = tbs1' ++ tbs2 → Forall₂ Extend_tableinst v_S.TABLES tbs1' →
    Externaddr_ok v_S' (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) := sorry

theorem addrs_store_globals_extension (v_S v_S' : store) (v_globaladdr : Nat) (gs1' gs2 : List globalinst) (gt : globaltype) :
    Externaddr_ok v_S (externaddr.GLOBAL v_globaladdr) (externtype.GLOBAL gt) →
    v_S'.GLOBALS = gs1' ++ gs2 → Forall₂ Extend_globalinst v_S.GLOBALS gs1' →
    Externaddr_ok v_S' (externaddr.GLOBAL v_globaladdr) (externtype.GLOBAL gt) := sorry

theorem addrs_mems_extension (v_S v_S' : store) (v_memaddr : Nat) (ms1' ms2 : List meminst) (mt : memtype) :
    Externaddr_ok v_S (externaddr.MEM v_memaddr) (externtype.MEM mt) →
    v_S'.MEMS = ms1' ++ ms2 → Forall₂ Extend_meminst v_S.MEMS ms1' →
    Externaddr_ok v_S' (externaddr.MEM v_memaddr) (externtype.MEM mt) := sorry

theorem addrss_store_funcs_extension (v_S v_S' : store) (v_funcaddrs : List Nat) (fs1' fs2 : List funcinst) (tcf : List functype) :
    Forall₂ (fun a t => Externaddr_ok v_S (externaddr.FUNC a) (externtype.FUNC t)) v_funcaddrs tcf →
    v_S.FUNCS.length = fs1'.length → v_S'.FUNCS = fs1' ++ fs2 → Forall₂ Extend_funcinst v_S.FUNCS fs1' →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.FUNC a) (externtype.FUNC t)) v_funcaddrs tcf := sorry

theorem addrss_tables_extension (v_S v_S' : store) (v_addrs : List Nat) (tbs1' tbs2 : List tableinst) (tcs : List tabletype) :
    Forall₂ (fun a t => Externaddr_ok v_S (externaddr.TABLE a) (externtype.TABLE t)) v_addrs tcs →
    v_S.TABLES.length = tbs1'.length → v_S'.TABLES = tbs1' ++ tbs2 → Forall₂ Extend_tableinst v_S.TABLES tbs1' →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.TABLE a) (externtype.TABLE t)) v_addrs tcs := sorry

theorem addrss_store_globals_extension (v_S v_S' : store) (v_addrs : List Nat) (gs1' gs2 : List globalinst) (tcs : List globaltype) :
    Forall₂ (fun a t => Externaddr_ok v_S (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs →
    v_S.GLOBALS.length = gs1'.length → v_S'.GLOBALS = gs1' ++ gs2 → Forall₂ Extend_globalinst v_S.GLOBALS gs1' →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs := sorry

theorem addrss_mems_extension (v_S v_S' : store) (v_addrs : List Nat) (ms1' ms2 : List meminst) (tcs : List memtype) :
    Forall₂ (fun a t => Externaddr_ok v_S (externaddr.MEM a) (externtype.MEM t)) v_addrs tcs →
    v_S.MEMS.length = ms1'.length → v_S'.MEMS = ms1' ++ ms2 → Forall₂ Extend_meminst v_S.MEMS ms1' →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.MEM a) (externtype.MEM t)) v_addrs tcs := sorry

/-! ## `Extend_store` preserves `Exportinst_ok`/`Eleminst_ok`(store-addressed)/`Datainst_ok`
    (store-addressed)/`Moduleinst_ok` (extension_lemmas.v:1391-1588) -/

theorem store_extension_exts (v_S v_S' : store) (v_exportinst : List exportinst) :
    Extend_store v_S v_S' → Forall (Exportinst_ok v_S) v_exportinst → Forall (Exportinst_ok v_S') v_exportinst := sorry

theorem store_extension_eleminst (v_S v_S' : store) (a : eleminst) (t : elemtype) :
    Extend_store v_S v_S' → Eleminst_ok v_S a t → Eleminst_ok v_S' a t := sorry

/-- Rocq `extension_lemmas.v:1436` `store_extension_eleminsts'`. Address-based version, for
    module-instance `ELEMS` fields addressed by index. -/
theorem store_extension_eleminsts' (v_S v_S' : store) (aa : List Nat) (ts : List elemtype) :
    Extend_store v_S v_S' → Forall (fun a => a < v_S.ELEMS.length) aa →
    Forall₂ (fun a t => Eleminst_ok v_S (lookup_total v_S.ELEMS a) t) aa ts →
    Forall (fun a => a < v_S'.ELEMS.length) aa ∧
      Forall₂ (fun a t => Eleminst_ok v_S' (lookup_total v_S'.ELEMS a) t) aa ts := sorry

theorem store_extension_eleminsts (v_S v_S' : store) (aa : List eleminst) (ts : List elemtype) :
    Extend_store v_S v_S' → Forall₂ (fun a t => Eleminst_ok v_S a t) aa ts →
    Forall₂ (fun a t => Eleminst_ok v_S' a t) aa ts := sorry

/-- Rocq `extension_lemmas.v:1513` `store_extension_datainsts'`. Note `Datainst_ok`'s
    proof is content-independent/always-true in Rocq. -/
theorem store_extension_datainsts' (v_S v_S' : store) (aa : List Nat) :
    Extend_store v_S v_S' → Forall (fun a => a < v_S.DATAS.length) aa →
    Forall (fun a => Datainst_ok v_S (lookup_total v_S.DATAS a) datatype.OK) aa →
    Forall (fun a => a < v_S'.DATAS.length) aa ∧ Forall (fun a => Datainst_ok v_S' (lookup_total v_S'.DATAS a) datatype.OK) aa := sorry

theorem store_extension_datainsts (v_S v_S' : store) (aa : List datainst) :
    Extend_store v_S v_S' → Forall (fun a => Datainst_ok v_S a datatype.OK) aa →
    Forall (fun a => Datainst_ok v_S' a datatype.OK) aa := sorry

/-- Rocq `extension_lemmas.v:1560` `store_extension_moduleinst`. **The key assembly
    lemma**, reused by `type_preservation.v`'s `step_moduleinst`. -/
theorem store_extension_moduleinst (v_S v_S' : store) (v_i : moduleinst) (v_C : context) :
    Extend_store v_S v_S' → Moduleinst_ok v_S v_i v_C → Moduleinst_ok v_S' v_i v_C := sorry

/-! ## `Extend_store` preserves `*_instance_ok` (extension_lemmas.v:1590-1717) -/

theorem store_extension_funcinst (s s' : store) (v : funcinst) (t : functype) :
    Extend_store s s' → Funcinst_ok s v t → Funcinst_ok s' v t := sorry

theorem store_extension_funcinsts (s s' : store) (vs : List funcinst) (ts : List functype) :
    Extend_store s s' → Forall₂ (fun v t => Funcinst_ok s v t) vs ts →
    Forall₂ (fun v t => Funcinst_ok s' v t) vs ts := sorry

theorem store_extension_globalinst (s s' : store) (v : globalinst) (t : globaltype) :
    Extend_store s s' → Globalinst_ok s v t → Globalinst_ok s' v t := sorry

theorem store_extension_globalinsts (s s' : store) (vs : List globalinst) (ts : List globaltype) :
    Extend_store s s' → Forall₂ (fun v t => Globalinst_ok s v t) vs ts →
    Forall₂ (fun v t => Globalinst_ok s' v t) vs ts := sorry

theorem store_extension_tableinst (s s' : store) (v : tableinst) (t : tabletype) :
    Extend_store s s' → Tableinst_ok s v t → Tableinst_ok s' v t := sorry

theorem store_extension_tableinsts (s s' : store) (vs : List tableinst) (ts : List tabletype) :
    Extend_store s s' → Forall₂ (fun v t => Tableinst_ok s v t) vs ts →
    Forall₂ (fun v t => Tableinst_ok s' v t) vs ts := sorry

theorem store_extension_meminst (s s' : store) (v : meminst) (t : memtype) :
    Extend_store s s' → Meminst_ok s v t → Meminst_ok s' v t := sorry

theorem store_extension_meminsts (s s' : store) (vs : List meminst) (ts : List memtype) :
    Extend_store s s' → Forall₂ (fun v t => Meminst_ok s v t) vs ts →
    Forall₂ (fun v t => Meminst_ok s' v t) vs ts := sorry

/-- Rocq `extension_lemmas.v:1697` `store_extension_externaddrs_func`. A second,
    ergonomically-restated proof of essentially `addrs_store_funcs_extension`'s func case
    (no explicit `++` witnesses needed); the preferred form downstream. -/
theorem store_extension_externaddrs_func (s s' : store) (fa : Nat) (ft : functype) :
    Extend_store s s' → Externaddr_ok s (externaddr.FUNC fa) (externtype.FUNC ft) →
    Externaddr_ok s' (externaddr.FUNC fa) (externtype.FUNC ft) := sorry

/-! ## The big `Instrs_ok2`/`Instr_ok2` monotonicity theorem (extension_lemmas.v:1718-1776) -/

/-- Rocq `extension_lemmas.v:1724` `store_extension_ais`. **THE big monotonicity
    theorem**: admin-instruction-sequence typing is preserved under store extension (given
    both stores well-formed). Rocq proves this via a custom mutual induction principle
    (`Scheme ais_ok_ind'`) over what this digest calls `Admin_instrs_ok`/`Thread_ok`/
    `Admin_instr_ok` — see the naming note at the top of this file; stated here in terms of
    the confirmed `Instrs_ok2` judgment. Directly reused by `type_preservation.v`'s
    `t_preservation_type` ("Context Instrs" congruence case) and `step_moduleinst`. -/
theorem store_extension_ais (s s' : store) (c : context) (ais : List admininstr) (ft : functype) :
    Extend_store s s' → Store_ok s → Store_ok s' → Instrs_ok2 s c ais ft → Instrs_ok2 s' c ais ft := sorry

/-! ## "construct_*" lemmas — complementary direction: pre-mutation typing witness + fresh
    `Ref_ok`/`Val_ok` for new payload → post-mutation typing witness (extension_lemmas.v:1776-2045).
    These are exactly the ingredients `type_preservation.v`'s `store_extension_reduce`
    needs per store-mutating reduction rule. -/

/-- Rocq `extension_lemmas.v:1776` `construct_tableinsts`. `table.set` preserves table
    typedness at unchanged type list `ts`. -/
theorem construct_tableinsts (s : store) (ts : List tabletype) (t : reftype) (tba : Nat) (lim : limits)
    (tbr : List ref) (i : Nat) (ref_lst : ref) :
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype lim t) tbr →
    Forall₂ (fun v ty => Tableinst_ok s v ty)
      (list_update_func s.TABLES tba (fun v1 => { v1 with REFS := list_update_func v1.REFS i (fun _ => ref_lst) })) ts := sorry

/-- Rocq `extension_lemmas.v:1817` `construct_tableinsts_grow`. `table.grow` preserves
    typedness, updates the type list too (min bumped by `v_n`, checked against max). -/
theorem construct_tableinsts_grow (s : store) (ts : List tabletype) (ref_lst : ref) (t : reftype)
    (tba : Nat) (v_r : List ref) (j_opt : Option uN) (v_n : Nat) :
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    Forall (fun v_j => v_r.length + v_n ≤ (proj_uN_0 v_j)) (Option.toList j_opt) →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_r.length) j_opt) t) v_r →
    Forall₂ (fun v ty => Tableinst_ok s v ty)
      (list_update_func s.TABLES tba (fun _ => tableinst.MKtableinst
        (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t) (v_r ++ List.replicate v_n ref_lst)))
      (list_update_func ts tba (fun _ => tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t)) := sorry

/-- Rocq `extension_lemmas.v:1893` `construct_globalinsts`. `global.set` preserves global
    typedness (type list unchanged, mutable globals don't change globaltype). -/
theorem construct_globalinsts (s : store) (ts : List globaltype) (ga : Nat) (v : val) (t : valtype) (v_old : val) :
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) s.GLOBALS ts →
    lookup_total s.GLOBALS ga = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) t) v_old →
    Val_ok s v t →
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) (list_update_func s.GLOBALS ga (fun g => { g with VALUE := v })) ts := sorry

/-- Rocq `extension_lemmas.v:1919` `construct_meminsts`. `memory.store` preserves
    typedness (memtype unchanged). -/
theorem construct_meminsts (s : store) (ts : List memtype) (ma : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_i v_len : Nat) (v_nb : List byte) :
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst v_mt b_lst →
    Forall₂ (fun v ty => Meminst_ok s v ty)
      (list_update_func s.MEMS ma (fun m => { m with BYTES := list_slice_update m.BYTES v_i v_len v_nb })) ts := sorry

/-- Rocq `extension_lemmas.v:1946` `construct_meminsts_grow`. `memory.grow` preserves
    typedness, updates the type list too. -/
theorem construct_meminsts_grow (s : store) (ts : List memtype) (ma : Nat) (b_lst : List byte)
    (lim_old v_n v_j : Nat) :
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN lim_old) (some (uN.mk_uN v_j)))) b_lst →
    lim_old = b_lst.length / (64 * Ki) → lim_old + v_n ≤ v_j →
    Forall₂ (fun v ty => Meminst_ok s v ty) (list_update_func s.MEMS ma (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) (some (uN.mk_uN v_j))))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))))
      (list_update_func ts ma (fun _ => memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) (some (uN.mk_uN v_j))))) := sorry

/-- Rocq `extension_lemmas.v:2002` `construct_datainsts`. `data.drop` preserves data
    typedness trivially. -/
theorem construct_datainsts (s : store) (da : Nat) (b_lst : List byte) :
    Forall (fun a => Datainst_ok s a datatype.OK) s.DATAS → lookup_total s.DATAS da = datainst.MKdatainst b_lst →
    Forall (fun a => Datainst_ok s a datatype.OK) (list_update_func s.DATAS da (fun _ => datainst.MKdatainst [])) := sorry

/-- Rocq `extension_lemmas.v:2025` (last declaration in file) `construct_eleminsts`.
    `elem.drop` preserves element typedness trivially. -/
theorem construct_eleminsts (s : store) (ts : List elemtype) (ea : Nat) (t : elemtype) (ref_lst : List ref) :
    Forall₂ (fun v ty => Eleminst_ok s v ty) s.ELEMS ts →
    lookup_total s.ELEMS ea = eleminst.MKeleminst t ref_lst →
    Forall₂ (fun v ty => Eleminst_ok s v ty) (list_update_func s.ELEMS ea (fun e => { e with REFS := [] })) ts := sorry

end TLC
