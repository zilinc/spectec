import «wasm2.0»
import HelperLemmas
import Subtyping
import TypingLemmas
import TypePreservationPure

/-!
# ExtensionLemmas

Lean port of `spectec/test-rocq/theories/extension_lemmas.v`. Full
digest: `claude-logging/for-claude/digest_subtyping_and_extension_lemmas.md`.

**2026-09-24 update (post-resync rename/reshape pass)**: the user re-synced
the local `spectec/test-rocq/theories/` checkout to upstream HEAD (`a8b585cdb`,
was `5b03ae067`) on 2026-09-23; see
`claude-logging/verbatim_dialogue_log/bundle3/updated_documents/resync_impact_report.md`
for full detail. `extension_lemmas.v` was renamed wholesale in that update:
every `store_extension_*`/`*_extension_refl*` name below has been renamed to
`Extend_store_*`/`extend_*_refl*` (converging on the same naming convention
`wasm2.0.lean`'s own `Extend_store`/`Extend_funcinst` etc. already use — see
the now-historical naming note immediately below, which explains why the
*previous* names were themselves already a correction of an even older
Rocq naming). Several list-lifted lemmas (`extend_func_refl` etc.,
`se_invert_*`, `global_set_global_extension` and its sibling
per-instruction extension facts, `addrs_*_extension`/`addrss_*_extension`)
were also **reshaped**: their conclusions moved from a `Forall₂`/existential-
split idiom to an explicit `holds_upto P n` ("P holds at every index below
n") idiom, matching a new `holds_upto` definition upstream in `wasm.v`
itself (`holds_upto P n := Forall P (iotaN 0 n)`, i.e. exactly
`Forall P (List.range n)` here — see the `holds_upto` definition below,
which is now itself a direct 1:1 port). Several lemmas also gained new
well-formedness (`wf_*`) premises they lacked before. This file has been
updated to match the **current** Rocq names/shapes throughout; every
already-proved lemma's underlying math is unaffected (same facts, just
renamed/reshaped), and every still-`sorry` lemma has been restated against
the current signature rather than the stale one. `minst_invert_funcs`/
`_globals`/`_tables`/`_mems` were also generalized from exact-equality/
bespoke-subtyping premises to the unified `Externtype_sub` relation (already
present in `wasm2.0.lean`, confirmed field-for-field below) — a genuine
semantic generalization upstream, not just a rename.

**Naming note (RESOLVED, session 1 continuation; superseded in *name* by the
2026-09-24 update above, but the underlying reasoning is unchanged and this
history is kept for context)**: Rocq's `Store_extension`/`Func_extension`/
`Table_extension`/`Mem_extension`/`Global_extension`/`Elem_extension`/
`Data_extension` were used pervasively throughout `extension_lemmas.v` and
`type_preservation.v` at the *original* (pre-2026-07) Rocq revision this
project first read, but a direct grep across every `.v` file in
`test-rocq/theories/` at that revision returned zero hits for those exact
names — they were not declared anywhere under any declaration form. The
only store-extension-shaped relations that actually existed (confirmed both
in `wasm.v` and in `wasm2.0.lean`, both generated from the same EL spec)
were `Extend_store`/`Extend_funcinst`/`Extend_tableinst`/`Extend_meminst`/
`Extend_globalinst`/`Extend_eleminst`/`Extend_datainst`. The 2026-09-24
resync confirms this theory directly: the upstream author's later revision
(`a8b585cdb`) renamed `extension_lemmas.v`'s lemmas to converge on exactly
this `Extend_*` family (`store_extension_refl` → `Extend_store_refl`,
`func_extension_refl0` → `extend_funcinst_refl_0`, etc.) — i.e. the
"corrected" names this file already used turned out to anticipate the
direction upstream itself moved in. **Consequence for lemma signatures**:
the `Extend_*` relations' constructors (confirmed by reading `wasm2.0.lean`
directly) bake in `wf_*` well-formedness premises for `Extend_funcinst`/
`Extend_globalinst`/`Extend_tableinst`/`Extend_meminst`/`Extend_datainst`
(but NOT `Extend_eleminst`, which has none) — and the current upstream
Rocq's `extend_funcinst_refl_0`/etc. now also carry exactly these `wf_*`
premises (confirmed in the signatures above), matching what this file
already required. A prior Lean session's `Extension.lean` (see
`digest_prior_lean_attempts.md`) independently arrived at the same
corrected signatures early on; its proofs are reused below.

Similarly, `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` (cited by the
digest for the custom `Scheme`-based mutual induction backing
`Extend_store_ais`, née `store_extension_ais`) do not exist under those
names either — the matching argument shapes correspond to
`Instrs_ok2`/`Instr_ok2`, used below.

Phase 1 (first pass): every signature stated, proofs `sorry` except where
noted as reused/proved.
-/

namespace TLC

/-- Rocq `wasm.v:107` `holds_upto`. `holds_upto P n := Forall P (iotaN 0 n)`
    in Rocq — i.e. "P holds at every index strictly below `n`" — which is
    exactly `Forall P (List.range n)` here (`iotaN 0 n` ≈ `List.range n`).
    An `abbrev` (not `def`) so it unfolds transparently wherever a bare
    `Forall _ (List.range _)` fact (e.g. from `forall_range_lt`/
    `forall_range_refl` below) is needed in its place. -/
abbrev holds_upto (P : Nat → Prop) (n : Nat) : Prop := Forall P (List.range n)

/-- Bounds side-condition needed by `Extend_store`'s constructor: every index
    into `List.range l.length` is `< l.length`. No direct Rocq counterpart
    by name, but is exactly what Rocq's `holds_upto_lt_refl` states (not
    ported by name — pure proof-engineering plumbing, skipped per the same
    rationale as `helper_tactics.v`; the *fact* is used here via this
    equivalent). Reused from a prior Lean session's `Extension.lean`
    (`forall_range_lt`). -/
theorem forall_range_lt {α : Type} (l : List α) :
    Forall (fun a => a < l.length) (List.range l.length) := by
  intro a ha
  exact List.mem_range.mp ha

/-- Lifts a single-instance reflexivity fact, plus a well-formedness `Forall`
    over a list, to the `holds_upto` shape the `extend_*_refl` lemmas below
    (and `Extend_store`'s constructor) need. New plumbing, no Rocq
    counterpart by name. Reused from `Extension.lean` (`forall_range_refl`). -/
theorem forall_range_refl {α : Type} [Inhabited α] (l : List α) (P : α → Prop)
    (R : α → α → Prop) (hP : Forall P l) (hR : ∀ x, P x → R x x) :
    Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a ha
  have ha' : a < l.length := List.mem_range.mp ha
  have hmem : l[a]! ∈ l := by
    rw [getElem!_pos l a ha']
    exact List.getElem_mem ha'
  exact hR _ (hP _ hmem)

/-- As `forall_range_refl`, but for `Extend_eleminst`, which has no
    well-formedness side condition. Reused from `Extension.lean`
    (`forall_range_refl_noWf`). -/
theorem forall_range_refl_noWf {α : Type} [Inhabited α] (l : List α) (R : α → α → Prop)
    (hR : ∀ x, R x x) : Forall (fun a => R (l[a]!) (l[a]!)) (List.range l.length) := by
  intro a _
  exact hR _

/-! ## `Store_ok` inversion (extension_lemmas.v:20-209 old numbering; unchanged
    by the 2026-09-24 resync) -/

/-- Rocq `extension_lemmas.v` `Val_ok_store` at the pre-resync revision. **Not
    found under this name (or an obvious renaming) in the current upstream
    source** — flagged, not removed, since nothing else in this project
    depends on it and the underlying fact (swap-invariance of `Val_ok` across
    non-`FUNCS` store fields) is plausible and may still be needed later; if
    a future session finds the current Rocq equivalent, update this comment
    and the signature to match. -/
theorem Val_ok_store (f1 g1 t1 m1 e1 d1 g2 t2 m2 e2 d2 : _) (v : val) (t : valtype) :
    Val_ok (store.MKstore f1 g1 t1 m1 e1 d1) v t ↔ Val_ok (store.MKstore f1 g2 t2 m2 e2 d2) v t := sorry

/-- Rocq `extension_lemmas.v:57` `s_invert_funcs`. Unaffected by the
    2026-09-24 resync (signature confirmed identical against the current
    source). -/
theorem s_invert_funcs (s : store) : Store_ok s →
    ∃ fts, Forall₂ (fun f t => ∃ minst v_func, f = funcinst.MKfuncinst t minst v_func) s.FUNCS fts := sorry

/-- Rocq `extension_lemmas.v:89` `s_invert_globals`. Unaffected by the resync. -/
theorem s_invert_globals (s : store) : Store_ok s →
    ∃ gts, Forall₂ (fun g t => ∃ v_mut v_vt v_v, g = globalinst.MKglobalinst t v_v ∧
      t = globaltype.mk_globaltype v_mut v_vt ∧ Val_ok s v_v v_vt) s.GLOBALS gts := sorry

/-- Rocq `extension_lemmas.v:121` `s_invert_mems`. Unaffected by the resync
    (the current source names the page-count computation `pagediv`, a
    `Definition` we don't need a Lean counterpart for since it's pure sugar
    for the same `b_lst.length / (64 * Ki)` computation already inlined
    here). Encodes the memory page-count invariant and the hard cap
    `v_m ≤ 2^16` pages. -/
theorem s_invert_mems (s : store) : Store_ok s →
    ∃ mts, Forall₂ (fun m t => ∃ b_lst v_n v_m, m = meminst.MKmeminst t b_lst ∧
      t = memtype.PAGE (limits.mk_limits (uN.mk_uN v_n) (some (uN.mk_uN v_m))) ∧
      v_n = b_lst.length / (64 * Ki) ∧ v_n ≤ v_m ∧ v_m ≤ 2 ^ 16) s.MEMS mts := sorry

/-- Rocq `extension_lemmas.v:172` `s_invert_tables`. Unaffected by the resync. -/
theorem s_invert_tables (s : store) : Store_ok s →
    ∃ tbts, Forall₂ (fun tb tbt => ∃ ref_lst v_m rt, tb = tableinst.MKtableinst tbt ref_lst ∧
      tbt = tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN ref_lst.length) (some (uN.mk_uN v_m))) rt ∧
      Tabletype_ok tbt ∧ Forall (fun r => Ref_ok s r rt) ref_lst) s.TABLES tbts := sorry

/-! ## `Extend_store` component-wise inversion (2026-09-24: RESHAPED from an
    existential-split idiom to `holds_upto`, matching the current source) -/

/-- Rocq `se_invert_funcs` (current source). Old shape (pre-resync) was
    `∃ fs' fs2, Forall₂ Extend_funcinst s.FUNCS fs' ∧ s'.FUNCS = fs' ++ fs2`;
    current shape takes two `holds_upto` bound-hypotheses directly and
    concludes with a `holds_upto`-indexed pointwise fact instead. -/
theorem se_invert_funcs (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.FUNCS.length) s.FUNCS.length →
    holds_upto (fun a => a < s'.FUNCS.length) s.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (s.FUNCS[a]!) (s'.FUNCS[a]!)) s.FUNCS.length := sorry

/-- Rocq `se_invert_tables` (current source), reshaped as `se_invert_funcs`. -/
theorem se_invert_tables (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.TABLES.length) s.TABLES.length →
    holds_upto (fun a => a < s'.TABLES.length) s.TABLES.length →
    holds_upto (fun a => Extend_tableinst (s.TABLES[a]!) (s'.TABLES[a]!)) s.TABLES.length := sorry

/-- Rocq `se_invert_mems` (current source), reshaped as `se_invert_funcs`. -/
theorem se_invert_mems (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.MEMS.length) s.MEMS.length →
    holds_upto (fun a => a < s'.MEMS.length) s.MEMS.length →
    holds_upto (fun a => Extend_meminst (s.MEMS[a]!) (s'.MEMS[a]!)) s.MEMS.length := sorry

/-- Rocq `se_invert_store_globals` (current source), reshaped as `se_invert_funcs`. -/
theorem se_invert_store_globals (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.GLOBALS.length) s.GLOBALS.length →
    holds_upto (fun a => a < s'.GLOBALS.length) s.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (s.GLOBALS[a]!) (s'.GLOBALS[a]!)) s.GLOBALS.length := sorry

/-- Rocq `se_invert_elems` (current source), reshaped as `se_invert_funcs`. -/
theorem se_invert_elems (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.ELEMS.length) s.ELEMS.length →
    holds_upto (fun a => a < s'.ELEMS.length) s.ELEMS.length →
    holds_upto (fun a => Extend_eleminst (s.ELEMS[a]!) (s'.ELEMS[a]!)) s.ELEMS.length := sorry

/-- Rocq `se_invert_datas` (current source), reshaped as `se_invert_funcs`. -/
theorem se_invert_datas (s s' : store) : Extend_store s s' →
    holds_upto (fun a => a < s.DATAS.length) s.DATAS.length →
    holds_upto (fun a => a < s'.DATAS.length) s.DATAS.length →
    holds_upto (fun a => Extend_datainst (s.DATAS[a]!) (s'.DATAS[a]!)) s.DATAS.length := sorry

/-! ## Subtyping-of-externtypes cluster (2026-09-24: NEW in the current
    source — previously only available via a prior Lean session's reuse-only
    proofs, per `proof_prioritization.md` Tier F #20; now has real Rocq
    statements to port against. `Limits_sub`/`Externtype_sub` etc. already
    exist as inductives in `wasm2.0.lean`, confirmed field-for-field.) -/

/-- Rocq `limits_sub_refl` (current source, new). -/
theorem limits_sub_refl (lim : limits) : wf_limits lim → Limits_sub lim lim := sorry

/-- Rocq `limits_sub_trans` (current source, new). -/
theorem limits_sub_trans (lim lim' lim'' : limits) :
    Limits_sub lim lim' → Limits_sub lim' lim'' → Limits_sub lim lim'' := sorry

/-- Rocq `externtype_sub_refl` (current source, new). -/
theorem externtype_sub_refl (xt : externtype) : wf_externtype xt → Externtype_sub xt xt := sorry

/-- Rocq `externtype_sub_trans` (current source, new). -/
theorem externtype_sub_trans (xt xt' xt'' : externtype) :
    Externtype_sub xt xt' → Externtype_sub xt' xt'' → Externtype_sub xt xt'' := sorry

/-- Rocq `externtype_global_eq` (current source, new). `Globaltype_sub` in
    `wasm2.0.lean` is trivial (`Globaltype_sub gt gt` only), so
    `Externtype_sub (GLOBAL gt) (GLOBAL gt')` collapses to `gt = gt'`. -/
theorem externtype_global_eq (gt gt' : globaltype) :
    Externtype_sub (externtype.GLOBAL gt) (externtype.GLOBAL gt') → gt = gt' := sorry

/-- Rocq `externtype_func_eq` (current source, new). `Functype_sub` in
    `wasm2.0.lean` is likewise trivial, so this collapses to `ft = ft'`. -/
theorem externtype_func_eq (ft ft' : functype) :
    Externtype_sub (externtype.FUNC ft) (externtype.FUNC ft') → ft = ft' := sorry

/-! ## `Moduleinst_ok`/`inst_match` interaction with store contents
    (2026-09-24: `minst_invert_funcs`/`_tables`/`_globals`/`_mems` RESHAPED
    to use the unified `Externtype_sub` relation instead of exact equality
    (funcs/globals) or a bespoke per-kind `_sub` relation (tables/mems) — a
    genuine semantic generalization upstream, not just cosmetic.
    `minst_invert_functypes`/`_elems`/`_datas` unaffected.) -/

/-- Rocq `minst_invert_functypes`. Unaffected by the resync. -/
theorem minst_invert_functypes (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' → C'.TYPES = minst.TYPES := sorry

/-- Rocq `minst_invert_funcs` (current source). Was exact-equality on `ft`
    before the resync; now uses `Externtype_sub (FUNC ft') (FUNC ft)`. -/
theorem minst_invert_funcs (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun fa ft => ∃ minst1 v_func ft', fa < v_S.FUNCS.length ∧
      lookup_total v_S.FUNCS fa = funcinst.MKfuncinst ft' minst1 v_func ∧
      Externtype_sub (externtype.FUNC ft') (externtype.FUNC ft)) minst.FUNCS C'.FUNCS := sorry

/-- Rocq `minst_invert_tables` (current source). Was stated via a bespoke
    `Limits_sub`-on-the-limits-only premise before the resync; now uses
    `Externtype_sub (TABLE tbt') (TABLE tbt)` uniformly (which itself
    unfolds to a `Limits_sub` premise plus matching `wf_tabletype` facts,
    per `wasm2.0.lean`'s `Tabletype_sub`/`Externtype_sub` definitions). -/
theorem minst_invert_tables (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun tba tbt => ∃ tbr tbt', tba < v_S.TABLES.length ∧
      lookup_total v_S.TABLES tba = tableinst.MKtableinst tbt' tbr ∧
      Externtype_sub (externtype.TABLE tbt') (externtype.TABLE tbt)) minst.TABLES C'.TABLES := sorry

/-- Rocq `minst_invert_globals` (current source). Was exact-equality on
    `v_mut`/`v_valtype` before the resync; now uses
    `Externtype_sub (GLOBAL gt') (GLOBAL gt)`. -/
theorem minst_invert_globals (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ga gt => ∃ gt' v_val, ga < v_S.GLOBALS.length ∧
      lookup_total v_S.GLOBALS ga = globalinst.MKglobalinst gt' v_val ∧
      Externtype_sub (externtype.GLOBAL gt') (externtype.GLOBAL gt)) minst.GLOBALS C'.GLOBALS := sorry

/-- Rocq `minst_invert_mems` (current source). Was stated via a bespoke
    `Memtype_sub` premise before the resync; now uses
    `Externtype_sub (MEM v_mt) (MEM mt)` uniformly. -/
theorem minst_invert_mems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ma mt => ∃ v_mt b_lst, ma < v_S.MEMS.length ∧
      lookup_total v_S.MEMS ma = meminst.MKmeminst v_mt b_lst ∧
      Externtype_sub (externtype.MEM v_mt) (externtype.MEM mt)) minst.MEMS C'.MEMS := sorry

/-- Rocq `minst_invert_elems`. Unaffected by the resync. -/
theorem minst_invert_elems (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    Forall₂ (fun ea et => ∃ ref_lst, ea < v_S.ELEMS.length ∧ Forall (fun r => Ref_ok v_S r et) ref_lst ∧
      lookup_total v_S.ELEMS ea = eleminst.MKeleminst et ref_lst) minst.ELEMS C'.ELEMS := sorry

/-- Rocq `minst_invert_datas`. Unaffected by the resync. -/
theorem minst_invert_datas (v_S : store) (minst : moduleinst) (C C' : context) :
    Moduleinst_ok v_S minst C → inst_match C C' →
    minst.DATAS.length = C'.DATAS.length ∧
      Forall (fun da => ∃ b_lst, da < v_S.DATAS.length ∧ lookup_total v_S.DATAS da = datainst.MKdatainst b_lst)
        minst.DATAS := sorry

/-! ## Misc lookup/inversion lemmas (unaffected by the 2026-09-24 resync) -/

/-- Rocq `lookup_global`. Unaffected by the resync. -/
theorem lookup_global (v_a : Nat) (v_C v_C' : context) (v_mut : «mut») (v_vt : valtype) (v_S : store) (minst : moduleinst) :
    v_a < v_C'.GLOBALS.length → lookup_total v_C'.GLOBALS v_a = globaltype.mk_globaltype v_mut v_vt →
    Moduleinst_ok v_S minst v_C → inst_match v_C v_C' → Store_ok v_S →
    Val_ok v_S (lookup_total v_S.GLOBALS (lookup_total minst.GLOBALS v_a)).VALUE v_vt := sorry

/-- Rocq `bt_inversion`. Unaffected by the resync. The computable elaboration
    function `fun_blocktype` agrees with the declarative `Blocktype_ok`
    relation's chosen functype. -/
theorem bt_inversion (v_S : store) (v_C v_C' : context) (r_v_f : frame) (b_lstt : blocktype)
    (ts1 ts2 bt1 bt2 : List valtype) :
    Moduleinst_ok v_S r_v_f.MODULE v_C → Blocktype_ok v_C' b_lstt (mkFunctype ts1 ts2) →
    fun_blocktype (state.mk_state v_S r_v_f) b_lstt = mkFunctype bt1 bt2 → inst_match v_C v_C' →
    ts1 = bt1 ∧ ts2 = bt2 := sorry

/-- Rocq `tc_func_reference2`. Unaffected by the resync. -/
theorem tc_func_reference2 (v_S : store) (v_C : context) (minst : moduleinst) (idx : Nat) (tf : functype) (v_type : funcinst) :
    lookup_total minst.TYPES idx = v_type.TYPE → Moduleinst_ok v_S minst v_C →
    lookup_total v_C.TYPES idx = tf → tf = v_type.TYPE := sorry

/-- Rocq `store_typed_exterval_types`. Unaffected by the resync. -/
theorem store_typed_exterval_types (v_S : store) (v_f : funcinst) (v_a : Nat) :
    v_a < v_S.FUNCS.length → lookup_total v_S.FUNCS v_a = v_f → Store_ok v_S →
    Externaddr_ok v_S (externaddr.FUNC v_a) (externtype.FUNC v_f.TYPE) := sorry

/-! ## Extension relations are reflexive per store-component kind
    (2026-09-24: single-instance `_refl0` lemmas RENAMED only, same shape;
    list-lifted `_refl` lemmas RENAMED **and RESHAPED** — now stated
    store-specifically with a `holds_upto` conclusion instead of generically
    over any list with a `Forall₂` conclusion.) -/

/-- Rocq `extend_funcinst_refl_0` (was `func_extension_refl0`; RENAMED only,
    same shape, since `Extend_funcinst`'s `wf_funcinst` premise requirement
    was already anticipated pre-resync — see the naming note above). Proof
    reused from a prior Lean session's `Extension.lean` (`extend_funcinst_refl`). -/
theorem extend_funcinst_refl_0 {f : funcinst} (h : wf_funcinst f) : Extend_funcinst f f := by
  obtain ⟨ft, mm, fc⟩ := f
  exact Extend_funcinst.mk_Extend_funcinst ft mm fc h

/-- Rocq `extend_func_refl` (was `func_extension_refl`; RENAMED and RESHAPED:
    now store-specific with a `holds_upto` conclusion rather than generic
    over any list with a `Forall₂` conclusion). Proved directly from
    `forall_range_refl` below, which already produces exactly this
    `holds_upto`-shaped fact (`holds_upto` unfolds to `Forall _ (List.range _)`). -/
theorem extend_func_refl (s : store) (h : Forall wf_funcinst s.FUNCS) :
    holds_upto (fun n => Extend_funcinst (s.FUNCS[n]!) (s.FUNCS[n]!)) s.FUNCS.length :=
  forall_range_refl s.FUNCS wf_funcinst Extend_funcinst h (fun x hx => extend_funcinst_refl_0 hx)

/-- Rocq `extend_tableinst_refl_0` (was `table_extension_refl0`; RENAMED
    only, same shape). Proof reused from `Extension.lean`
    (`extend_tableinst_refl`). -/
theorem extend_tableinst_refl_0 {t : tableinst} (h : wf_tableinst t) : Extend_tableinst t t := by
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

/-- Rocq `extend_table_refl` (was `table_extension_refl`; RENAMED and
    RESHAPED, as `extend_func_refl`). -/
theorem extend_table_refl (s : store) (h : Forall wf_tableinst s.TABLES) :
    holds_upto (fun n => Extend_tableinst (s.TABLES[n]!) (s.TABLES[n]!)) s.TABLES.length :=
  forall_range_refl s.TABLES wf_tableinst Extend_tableinst h (fun x hx => extend_tableinst_refl_0 hx)

/-- Rocq `extend_meminst_refl_0` (was `mem_extension_refl0`; RENAMED only,
    same shape). Proof reused from `Extension.lean` (`extend_meminst_refl`). -/
theorem extend_meminst_refl_0 {m : meminst} (h : wf_meminst m) : Extend_meminst m m := by
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

/-- Rocq `extend_mem_refl` (was `mem_extension_refl`; RENAMED and RESHAPED,
    as `extend_func_refl`). -/
theorem extend_mem_refl (s : store) (h : Forall wf_meminst s.MEMS) :
    holds_upto (fun n => Extend_meminst (s.MEMS[n]!) (s.MEMS[n]!)) s.MEMS.length :=
  forall_range_refl s.MEMS wf_meminst Extend_meminst h (fun x hx => extend_meminst_refl_0 hx)

/-- Rocq `extend_globalinst_refl_0` (was `global_extension_refl_0`; RENAMED
    only, same shape). Proof reused from `Extension.lean`
    (`extend_globalinst_refl`). -/
theorem extend_globalinst_refl_0 {g : globalinst} (h : wf_globalinst g) : Extend_globalinst g g := by
  obtain ⟨ty, v⟩ := g
  obtain ⟨v_mut, t⟩ := ty
  exact Extend_globalinst.mk_Extend_globalinst v_mut t v v (Or.inr rfl) h h

/-- Rocq `extend_global_refl` (was `global_extension_refl`; RENAMED and
    RESHAPED, as `extend_func_refl`). -/
theorem extend_global_refl (s : store) (h : Forall wf_globalinst s.GLOBALS) :
    holds_upto (fun n => Extend_globalinst (s.GLOBALS[n]!) (s.GLOBALS[n]!)) s.GLOBALS.length :=
  forall_range_refl s.GLOBALS wf_globalinst Extend_globalinst h (fun x hx => extend_globalinst_refl_0 hx)

/-- Rocq `extend_eleminst_refl_0` (was `elem_extension_refl0`; RENAMED only,
    same shape — `Extend_eleminst` has no `wf_*` premise, matches Rocq).
    Proof reused from `Extension.lean` (`extend_eleminst_refl`). -/
theorem extend_eleminst_refl_0 (e : eleminst) : Extend_eleminst e e := by
  obtain ⟨rt, refs⟩ := e
  exact Extend_eleminst.mk_Extend_eleminst rt refs refs (Or.inl rfl)

/-- Rocq `extend_elem_refl` (was `elem_extension_refl`; RENAMED and RESHAPED,
    as `extend_func_refl`; no `wf_*` premise, as in Rocq). -/
theorem extend_elem_refl (s : store) :
    holds_upto (fun n => Extend_eleminst (s.ELEMS[n]!) (s.ELEMS[n]!)) s.ELEMS.length :=
  forall_range_refl_noWf s.ELEMS Extend_eleminst extend_eleminst_refl_0

/-- Rocq `extend_datainst_refl_0` (was `data_extension_refl0`; RENAMED only,
    same shape). Proof reused from `Extension.lean` (`extend_datainst_refl`). -/
theorem extend_datainst_refl_0 {d : datainst} (h : wf_datainst d) : Extend_datainst d d := by
  obtain ⟨bs⟩ := d
  exact Extend_datainst.mk_Extend_datainst bs bs (Or.inl rfl) h h

/-- Rocq `extend_data_refl` (was `data_extension_refl`; RENAMED and
    RESHAPED, as `extend_func_refl`). -/
theorem extend_data_refl (s : store) (h : Forall wf_datainst s.DATAS) :
    holds_upto (fun n => Extend_datainst (s.DATAS[n]!) (s.DATAS[n]!)) s.DATAS.length :=
  forall_range_refl s.DATAS wf_datainst Extend_datainst h (fun x hx => extend_datainst_refl_0 hx)

/-- Rocq `Extend_store_refl` (was `store_extension_refl`; RENAMED only —
    the underlying `Extend_store` constructor lives in `wasm2.0.lean`,
    which was **not** touched by the 2026-09-24 resync, so this lemma's
    actual shape and proof are unaffected; only its Rocq-side name changed).
    **No explicit `Extend_store_trans` (transitivity) lemma exists anywhere
    in the current Rocq file either** — downstream preservation proofs
    re-derive extension facts per reduction step rather than composing two
    `Extend_store` proofs. Not ported here either, matching the Rocq gap.
    Proof reused from a prior Lean session's `Extension.lean`
    (`extend_store_refl`); note it calls the single-instance `_refl0` lemmas
    and `forall_range_refl` directly rather than routing through the
    store-specific `extend_func_refl`-family lemmas above — a legitimate
    proof-method divergence (Lean has proof irrelevance), not a
    signature divergence. -/
theorem Extend_store_refl {s : store} (h : wf_store s) : Extend_store s s := by
  cases h with
  | store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas =>
    have hwf : wf_store { FUNCS := funcs, GLOBALS := globals, TABLES := tables, MEMS := mems, ELEMS := elems, DATAS := datas } :=
      wf_store.store_case_ funcs globals tables mems elems datas hfuncs hglobals htables hmems hdatas
    exact Extend_store.mk_Extend_store _ _
      (forall_range_lt globals) (forall_range_lt globals)
      (forall_range_refl globals wf_globalinst Extend_globalinst hglobals
        (fun x hx => extend_globalinst_refl_0 hx))
      (forall_range_lt mems) (forall_range_lt mems)
      (forall_range_refl mems wf_meminst Extend_meminst hmems
        (fun x hx => extend_meminst_refl_0 hx))
      (forall_range_lt tables) (forall_range_lt tables)
      (forall_range_refl tables wf_tableinst Extend_tableinst htables
        (fun x hx => extend_tableinst_refl_0 hx))
      (forall_range_lt funcs) (forall_range_lt funcs)
      (forall_range_refl funcs wf_funcinst Extend_funcinst hfuncs
        (fun x hx => extend_funcinst_refl_0 hx))
      (forall_range_lt datas) (forall_range_lt datas)
      (forall_range_refl datas wf_datainst Extend_datainst hdatas
        (fun x hx => extend_datainst_refl_0 hx))
      (forall_range_lt elems) (forall_range_lt elems)
      (forall_range_refl_noWf elems Extend_eleminst extend_eleminst_refl_0)
      hwf hwf

/-- Rocq `funcinst_same` at the pre-resync revision. **Not found under this
    name (or an obvious renaming) in the current upstream source** —
    flagged, not removed; the representational-gap caveat below (about
    `Forall₂`'s zip-based definition not forcing equal length) may have
    been resolved differently upstream (e.g. inside the new proofs of
    `Extend_store_funcinst`/`Extend_store_ref`) — worth checking those
    proofs directly before re-deriving a fix here.

    **CAVEAT (not present in Rocq)**: `wasm2.0.lean`'s `Forall₂` is a
    zip-based `def` (`∀ t ∈ xs.zip ys, P t.1 t.2`, see
    `ExtendedDeriveDecEq.lean`), which does NOT force `f1.length = f2.length`
    the way Rocq's inductive `Forall2` does — so `Forall₂ Extend_funcinst f1
    f2` alone is satisfiable even when `f1`/`f2` have different lengths.
    This lemma is therefore NOT provable as literally stated below without
    an extra length hypothesis; left as `sorry` deliberately. -/
theorem funcinst_same (f1 f2 : List funcinst) : Forall₂ Extend_funcinst f1 f2 → f1 = f2 := sorry

/-! ## `Extend_store` preserves `Ref_ok`/`Val_ok` (2026-09-24: RENAMED only,
    `store_extension_*` → `Extend_store_*`; one new lemma `Extend_store_refs'`
    added upstream) -/

theorem Extend_store_ref (v_S v_S' : store) (v_t : reftype) (v_val : ref) :
    Extend_store v_S v_S' → Ref_ok v_S v_val v_t → Ref_ok v_S' v_val v_t := sorry

theorem Extend_store_refs (v_S v_S' : store) (v_ts : List reftype) (v_vals : List ref) :
    Extend_store v_S v_S' → Forall₂ (fun t v => Ref_ok v_S v t) v_ts v_vals →
    Forall₂ (fun t v => Ref_ok v_S' v t) v_ts v_vals := sorry

/-- Rocq `Extend_store_refs'` (current source, new). Single-type version of
    `Extend_store_refs` (a `Forall` over one `reftype`, not a `Forall₂`
    across two parallel lists). -/
theorem Extend_store_refs' (v_S v_S' : store) (v_t : reftype) (v_refs : List ref) :
    Extend_store v_S v_S' → Forall (fun v_ref => Ref_ok v_S v_ref v_t) v_refs →
    Forall (fun v_ref => Ref_ok v_S' v_ref v_t) v_refs := sorry

theorem Extend_store_val (v_S v_S' : store) (v_t : valtype) (v_val : val) :
    Extend_store v_S v_S' → Val_ok v_S v_val v_t → Val_ok v_S' v_val v_t := sorry

theorem Extend_store_vals (v_S v_S' : store) (v_t : List valtype) (v_val : List val) :
    Extend_store v_S v_S' → Vals_ok v_S v_val v_t → Vals_ok v_S' v_val v_t := sorry

theorem config_same (s s' : store) (f f' : frame) (ais ais' : List admininstr) :
    config.mk_config (state.mk_state s f) ais = config.mk_config (state.mk_state s' f') ais' →
    s = s' ∧ f = f' ∧ ais = ais' := sorry

theorem config_same2 (s s' : store) (f f' : frame) (ais ais' : List admininstr) :
    s = s' ∧ f = f' ∧ ais = ais' →
    config.mk_config (state.mk_state s f) ais = config.mk_config (state.mk_state s' f') ais' := sorry

/-! ## Extension facts produced by specific store-mutating operations
    (2026-09-24: names UNCHANGED, but every lemma here RESHAPED — added
    `wf_*` premises, and conclusions moved from `Forall₂` to `holds_upto`) -/

/-- Rocq `global_set_global_extension` (current source). Gained `Forall
    wf_globalinst v_g` and `wf_val v_val_1` premises; conclusion now
    `holds_upto`-shaped and takes the post-update list `v_g'` as an explicit
    hypothesis-bound parameter rather than writing `list_update_func` inline
    in the conclusion. -/
theorem global_set_global_extension (v_g v_g' : List globalinst) (v_idx : Nat) (v_valtype : valtype)
    (v_val_0 v_val_1 : val) :
    Forall wf_globalinst v_g → wf_val v_val_1 →
    v_idx < v_g.length → lookup_total v_g v_idx = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) v_valtype) v_val_0 →
    v_g' = list_update_func v_g v_idx (fun g => { g with VALUE := v_val_1 }) →
    holds_upto (fun a => Extend_globalinst (v_g[a]!) (v_g'[a]!)) v_g.length := sorry

/-- Rocq `store_none_mem_extension` (current source). Gained `Forall wf_byte
    v_nb` and `Forall wf_meminst v_ms` premises; conclusion now
    `holds_upto`-shaped with `v_ms'` explicit. -/
theorem store_none_mem_extension (v_ms v_ms' : List meminst) (v_idx : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_l v_n_len : Nat) (v_nb : List byte) :
    Forall wf_byte v_nb → Forall wf_meminst v_ms →
    v_idx < v_ms.length → lookup_total v_ms v_idx = meminst.MKmeminst v_mt b_lst →
    v_ms' = list_update_func v_ms v_idx (fun m => { m with BYTES := list_slice_update m.BYTES v_l v_n_len v_nb }) →
    holds_upto (fun a => Extend_meminst (v_ms[a]!) (v_ms'[a]!)) v_ms.length := sorry

/-- Rocq `memory_grow_mem_extension` (current source). Gained `Forall
    wf_meminst v_ms`/`Forall wf_meminst v_ms'` premises; conclusion now
    `holds_upto`-shaped with `v_ms'` explicit. -/
theorem memory_grow_mem_extension (v_ms v_ms' : List meminst) (v_idx : Nat) (b_lst : List byte) (v_i v_n v_j : Nat) :
    Forall wf_meminst v_ms → Forall wf_meminst v_ms' →
    v_idx < v_ms.length →
    lookup_total v_ms v_idx = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN v_i) (some (uN.mk_uN v_j)))) b_lst →
    v_i + v_n ≤ v_j →
    v_ms' = list_update_func v_ms v_idx (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (v_i + v_n)) (some (uN.mk_uN v_j))))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) →
    holds_upto (fun a => Extend_meminst (v_ms[a]!) (v_ms'[a]!)) v_ms.length := sorry

/-- Rocq `table_set_table_extension` (current source). Gained `Forall
    wf_tableinst v_tbs` premise; conclusion now `holds_upto`-shaped with
    `v_tbs'` explicit. -/
theorem table_set_table_extension (v_tbs v_tbs' : List tableinst) (v_idx : Nat) (tbt : tabletype) (tbr : List ref)
    (v_i : Nat) (v_tbr : ref) :
    Forall wf_tableinst v_tbs →
    v_idx < v_tbs.length → lookup_total v_tbs v_idx = tableinst.MKtableinst tbt tbr →
    v_tbs' = list_update_func v_tbs v_idx (fun tb => { tb with REFS := list_update_func tb.REFS v_i (fun _ => v_tbr) }) →
    holds_upto (fun a => Extend_tableinst (v_tbs[a]!) (v_tbs'[a]!)) v_tbs.length := sorry

/-- Rocq `table_grow_table_extension` (current source). Gained `Forall
    wf_tableinst v_tbs`/`Forall wf_tableinst v_tbs'` premises; conclusion now
    `holds_upto`-shaped with `v_tbs'` explicit. -/
theorem table_grow_table_extension (v_tbs v_tbs' : List tableinst) (v_idx : Nat) (j : Option uN) (r : ref)
    (rt : reftype) (nn : Nat) (tbr : List ref) :
    Forall wf_tableinst v_tbs → Forall wf_tableinst v_tbs' →
    v_idx < v_tbs.length →
    lookup_total v_tbs v_idx = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN tbr.length) j) rt) tbr →
    v_tbs' = list_update_func v_tbs v_idx (fun _ =>
      tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (tbr.length + nn)) j) rt)
        (tbr ++ List.replicate nn r)) →
    holds_upto (fun a => Extend_tableinst (v_tbs[a]!) (v_tbs'[a]!)) v_tbs.length := sorry

/-- Rocq `elem_drop_elem_extension` (current source). Conclusion now
    `holds_upto`-shaped with `es'` explicit (no `wf_*` premise, as before —
    `Extend_eleminst` has none). -/
theorem elem_drop_elem_extension (es es' : List eleminst) (idx : Nat) :
    idx < es.length → es' = list_update_func es idx (fun e => { e with REFS := [] }) →
    holds_upto (fun a => Extend_eleminst (es[a]!) (es'[a]!)) es.length := sorry

/-- Rocq `data_drop_data_extension` (current source). Gained `Forall
    wf_datainst ds` premise; conclusion now `holds_upto`-shaped with `ds'`
    explicit. -/
theorem data_drop_data_extension (ds ds' : List datainst) (idx : Nat) :
    Forall wf_datainst ds → idx < ds.length → ds' = list_update_func ds idx (fun _ => datainst.MKdatainst []) →
    holds_upto (fun a => Extend_datainst (ds[a]!) (ds'[a]!)) ds.length := sorry

/-- Rocq `update_global_unchanged`. Unaffected by the resync. Frame lemma:
    updating only `store.GLOBALS` leaves every other component (and
    globals-length) unchanged. -/
theorem update_global_unchanged (v_S v_S' : store) (func : globalinst → globalinst) (v_idx : Nat) :
    v_S' = { v_S with GLOBALS := list_update_func v_S.GLOBALS v_idx func } →
    v_S.FUNCS = v_S'.FUNCS ∧ v_S.TABLES = v_S'.TABLES ∧ v_S.GLOBALS.length = v_S'.GLOBALS.length ∧
      v_S.MEMS = v_S'.MEMS ∧ v_S.ELEMS = v_S'.ELEMS ∧ v_S.DATAS = v_S'.DATAS := sorry

/-! ## `Externaddr_ok` preserved by store extension (2026-09-24: names
    UNCHANGED, but every lemma RESHAPED — gained a `wf_store v_S'` premise
    and the `++`-split witness + `Forall₂ Extend_*` premises were replaced
    by two `holds_upto` premises) -/

theorem addrs_store_funcs_extension (v_S v_S' : store) (v_funcaddr : Nat) (v_ft : functype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.FUNC v_funcaddr) (externtype.FUNC v_ft) →
    holds_upto (fun a => a < v_S'.FUNCS.length) v_S.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (v_S.FUNCS[a]!) (v_S'.FUNCS[a]!)) v_S.FUNCS.length →
    Externaddr_ok v_S' (externaddr.FUNC v_funcaddr) (externtype.FUNC v_ft) := sorry

theorem addrs_tables_extension (v_S v_S' : store) (v_tableaddr : Nat) (tt : tabletype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) →
    holds_upto (fun a => a < v_S'.TABLES.length) v_S.TABLES.length →
    holds_upto (fun a => Extend_tableinst (v_S.TABLES[a]!) (v_S'.TABLES[a]!)) v_S.TABLES.length →
    Externaddr_ok v_S' (externaddr.TABLE v_tableaddr) (externtype.TABLE tt) := sorry

theorem addrs_store_globals_extension (v_S v_S' : store) (v_globaladdr : Nat) (gt : globaltype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.GLOBAL v_globaladdr) (externtype.GLOBAL gt) →
    holds_upto (fun a => a < v_S'.GLOBALS.length) v_S.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (v_S.GLOBALS[a]!) (v_S'.GLOBALS[a]!)) v_S.GLOBALS.length →
    Externaddr_ok v_S' (externaddr.GLOBAL v_globaladdr) (externtype.GLOBAL gt) := sorry

theorem addrs_mems_extension (v_S v_S' : store) (v_memaddr : Nat) (mt : memtype) :
    wf_store v_S' → Externaddr_ok v_S (externaddr.MEM v_memaddr) (externtype.MEM mt) →
    holds_upto (fun a => a < v_S'.MEMS.length) v_S.MEMS.length →
    holds_upto (fun a => Extend_meminst (v_S.MEMS[a]!) (v_S'.MEMS[a]!)) v_S.MEMS.length →
    Externaddr_ok v_S' (externaddr.MEM v_memaddr) (externtype.MEM mt) := sorry

theorem addrss_store_funcs_extension (v_S v_S' : store) (v_funcaddrs : List Nat) (tcf : List functype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.FUNC a) (externtype.FUNC t)) v_funcaddrs tcf →
    holds_upto (fun a => a < v_S'.FUNCS.length) v_S.FUNCS.length →
    holds_upto (fun a => Extend_funcinst (v_S.FUNCS[a]!) (v_S'.FUNCS[a]!)) v_S.FUNCS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.FUNC a) (externtype.FUNC t)) v_funcaddrs tcf := sorry

theorem addrss_tables_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List tabletype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.TABLE a) (externtype.TABLE t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.TABLES.length) v_S.TABLES.length →
    holds_upto (fun a => Extend_tableinst (v_S.TABLES[a]!) (v_S'.TABLES[a]!)) v_S.TABLES.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.TABLE a) (externtype.TABLE t)) v_addrs tcs := sorry

theorem addrss_store_globals_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List globaltype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.GLOBALS.length) v_S.GLOBALS.length →
    holds_upto (fun a => Extend_globalinst (v_S.GLOBALS[a]!) (v_S'.GLOBALS[a]!)) v_S.GLOBALS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.GLOBAL a) (externtype.GLOBAL t)) v_addrs tcs := sorry

theorem addrss_mems_extension (v_S v_S' : store) (v_addrs : List Nat) (tcs : List memtype) :
    wf_store v_S' → Forall₂ (fun a t => Externaddr_ok v_S (externaddr.MEM a) (externtype.MEM t)) v_addrs tcs →
    holds_upto (fun a => a < v_S'.MEMS.length) v_S.MEMS.length →
    holds_upto (fun a => Extend_meminst (v_S.MEMS[a]!) (v_S'.MEMS[a]!)) v_S.MEMS.length →
    Forall₂ (fun a t => Externaddr_ok v_S' (externaddr.MEM a) (externtype.MEM t)) v_addrs tcs := sorry

/-! ## `Extend_store` preserves `Exportinst_ok`/`Eleminst_ok`(store-addressed)/
    `Datainst_ok`(store-addressed)/`Moduleinst_ok` (2026-09-24: RENAMED only,
    `store_extension_*` → `Extend_store_*`, shapes unchanged) -/

theorem Extend_store_exts (v_S v_S' : store) (v_exportinst : List exportinst) :
    Extend_store v_S v_S' → Forall (Exportinst_ok v_S) v_exportinst → Forall (Exportinst_ok v_S') v_exportinst := sorry

theorem Extend_store_eleminst (v_S v_S' : store) (a : eleminst) (t : elemtype) :
    Extend_store v_S v_S' → Eleminst_ok v_S a t → Eleminst_ok v_S' a t := sorry

/-- Rocq `Extend_store_eleminsts'` (was `store_extension_eleminsts'`).
    Address-based version, for module-instance `ELEMS` fields addressed by
    index. -/
theorem Extend_store_eleminsts' (v_S v_S' : store) (aa : List Nat) (ts : List elemtype) :
    Extend_store v_S v_S' → Forall (fun a => a < v_S.ELEMS.length) aa →
    Forall₂ (fun a t => Eleminst_ok v_S (lookup_total v_S.ELEMS a) t) aa ts →
    Forall (fun a => a < v_S'.ELEMS.length) aa ∧
      Forall₂ (fun a t => Eleminst_ok v_S' (lookup_total v_S'.ELEMS a) t) aa ts := sorry

theorem Extend_store_eleminsts (v_S v_S' : store) (aa : List eleminst) (ts : List elemtype) :
    Extend_store v_S v_S' → Forall₂ (fun a t => Eleminst_ok v_S a t) aa ts →
    Forall₂ (fun a t => Eleminst_ok v_S' a t) aa ts := sorry

/-- Rocq `Extend_store_datainsts'` (was `store_extension_datainsts'`). Note
    `Datainst_ok`'s proof is content-independent/always-true in Rocq. -/
theorem Extend_store_datainsts' (v_S v_S' : store) (aa : List Nat) :
    Extend_store v_S v_S' → Forall (fun a => a < v_S.DATAS.length) aa →
    Forall (fun a => Datainst_ok v_S (lookup_total v_S.DATAS a) datatype.OK) aa →
    Forall (fun a => a < v_S'.DATAS.length) aa ∧ Forall (fun a => Datainst_ok v_S' (lookup_total v_S'.DATAS a) datatype.OK) aa := sorry

theorem Extend_store_datainsts (v_S v_S' : store) (aa : List datainst) :
    Extend_store v_S v_S' → Forall (fun a => Datainst_ok v_S a datatype.OK) aa →
    Forall (fun a => Datainst_ok v_S' a datatype.OK) aa := sorry

/-- Rocq `Extend_store_moduleinst` (was `store_extension_moduleinst`). **The
    key assembly lemma**, reused by `type_preservation.v`'s
    `step_moduleinst`. -/
theorem Extend_store_moduleinst (v_S v_S' : store) (v_i : moduleinst) (v_C : context) :
    Extend_store v_S v_S' → Moduleinst_ok v_S v_i v_C → Moduleinst_ok v_S' v_i v_C := sorry

/-! ## `Extend_store` preserves `*_instance_ok` (2026-09-24: RENAMED only,
    `store_extension_*` → `Extend_store_*`, shapes unchanged) -/

theorem Extend_store_funcinst (s s' : store) (v : funcinst) (t : functype) :
    Extend_store s s' → Funcinst_ok s v t → Funcinst_ok s' v t := sorry

theorem Extend_store_funcinsts (s s' : store) (vs : List funcinst) (ts : List functype) :
    Extend_store s s' → Forall₂ (fun v t => Funcinst_ok s v t) vs ts →
    Forall₂ (fun v t => Funcinst_ok s' v t) vs ts := sorry

theorem Extend_store_globalinst (s s' : store) (v : globalinst) (t : globaltype) :
    Extend_store s s' → Globalinst_ok s v t → Globalinst_ok s' v t := sorry

theorem Extend_store_globalinsts (s s' : store) (vs : List globalinst) (ts : List globaltype) :
    Extend_store s s' → Forall₂ (fun v t => Globalinst_ok s v t) vs ts →
    Forall₂ (fun v t => Globalinst_ok s' v t) vs ts := sorry

theorem Extend_store_tableinst (s s' : store) (v : tableinst) (t : tabletype) :
    Extend_store s s' → Tableinst_ok s v t → Tableinst_ok s' v t := sorry

theorem Extend_store_tableinsts (s s' : store) (vs : List tableinst) (ts : List tabletype) :
    Extend_store s s' → Forall₂ (fun v t => Tableinst_ok s v t) vs ts →
    Forall₂ (fun v t => Tableinst_ok s' v t) vs ts := sorry

theorem Extend_store_meminst (s s' : store) (v : meminst) (t : memtype) :
    Extend_store s s' → Meminst_ok s v t → Meminst_ok s' v t := sorry

theorem Extend_store_meminsts (s s' : store) (vs : List meminst) (ts : List memtype) :
    Extend_store s s' → Forall₂ (fun v t => Meminst_ok s v t) vs ts →
    Forall₂ (fun v t => Meminst_ok s' v t) vs ts := sorry

/-- Rocq `Extend_store_externaddrs_func` (was `store_extension_externaddrs_func`).
    A second, ergonomically-restated proof of essentially
    `addrs_store_funcs_extension`'s func case (no explicit `holds_upto`
    bound-witness needed); the preferred form downstream. -/
theorem Extend_store_externaddrs_func (s s' : store) (fa : Nat) (ft : functype) :
    Extend_store s s' → Externaddr_ok s (externaddr.FUNC fa) (externtype.FUNC ft) →
    Externaddr_ok s' (externaddr.FUNC fa) (externtype.FUNC ft) := sorry

/-! ## The big `Instrs_ok2`/`Instr_ok2` monotonicity theorem (2026-09-24:
    RENAMED only, `store_extension_ais` → `Extend_store_ais`, shape unchanged) -/

/-- Rocq `Extend_store_ais` (was `store_extension_ais`). **THE big
    monotonicity theorem**: admin-instruction-sequence typing is preserved
    under store extension (given both stores well-formed). Rocq proves this
    via a custom mutual induction principle (`Scheme ais_ok_ind'`) over what
    this digest calls `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` — see
    the naming note at the top of this file; stated here in terms of the
    confirmed `Instrs_ok2` judgment. Directly reused by
    `type_preservation.v`'s `t_preservation_type` ("Context Instrs"
    congruence case) and `step_moduleinst`. -/
theorem Extend_store_ais (s s' : store) (c : context) (ais : List admininstr) (ft : functype) :
    Extend_store s s' → Store_ok s → Store_ok s' → Instrs_ok2 s c ais ft → Instrs_ok2 s' c ais ft := sorry

/-! ## "construct_*" lemmas — complementary direction: pre-mutation typing
    witness + fresh `Ref_ok`/`Val_ok` for new payload → post-mutation typing
    witness. (2026-09-24: names unchanged throughout; `construct_tableinsts`/
    `construct_globalinsts`/`construct_datainsts`/`construct_eleminsts`
    unaffected; `construct_tableinsts_grow`/`construct_meminsts`/
    `construct_meminsts_grow` gained `wf_*` premises and/or restructured to
    bind their post-mutation list via an explicit hypothesis.) These are
    exactly the ingredients `type_preservation.v`'s `store_extension_reduce`
    needs per store-mutating reduction rule. -/

/-- Rocq `construct_tableinsts`. Unaffected by the resync. `table.set`
    preserves table typedness at unchanged type list `ts`. -/
theorem construct_tableinsts (s : store) (ts : List tabletype) (t : reftype) (tba : Nat) (lim : limits)
    (tbr : List ref) (i : Nat) (ref_lst : ref) :
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype lim t) tbr →
    Forall₂ (fun v ty => Tableinst_ok s v ty)
      (list_update_func s.TABLES tba (fun v1 => { v1 with REFS := list_update_func v1.REFS i (fun _ => ref_lst) })) ts := sorry

/-- Rocq `construct_tableinsts_grow` (current source). Gained a `Forall
    wf_tableinst tbinsts` premise; the post-`table.grow` table list is now
    bound via an explicit `tbinsts = ...` hypothesis rather than written
    inline in the conclusion. -/
theorem construct_tableinsts_grow (s : store) (ts : List tabletype) (ref_lst : ref) (t : reftype)
    (tba : Nat) (v_r : List ref) (j_opt : Option uN) (v_n : Nat) (tbinsts : List tableinst) :
    Forall wf_tableinst tbinsts →
    Forall₂ (fun v ty => Tableinst_ok s v ty) s.TABLES ts → Ref_ok s ref_lst t →
    Forall (fun v_j => v_r.length + v_n ≤ (proj_uN_0 v_j)) (Option.toList j_opt) →
    lookup_total s.TABLES tba = tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN v_r.length) j_opt) t) v_r →
    tbinsts = list_update_func s.TABLES tba (fun _ => tableinst.MKtableinst
        (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t) (v_r ++ List.replicate v_n ref_lst)) →
    Forall₂ (fun v ty => Tableinst_ok s v ty) tbinsts
      (list_update_func ts tba (fun _ => tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (v_r.length + v_n)) j_opt) t)) := sorry

/-- Rocq `construct_globalinsts`. Unaffected by the resync. `global.set`
    preserves global typedness (type list unchanged, mutable globals don't
    change globaltype). -/
theorem construct_globalinsts (s : store) (ts : List globaltype) (ga : Nat) (v : val) (t : valtype) (v_old : val) :
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) s.GLOBALS ts →
    lookup_total s.GLOBALS ga = globalinst.MKglobalinst (globaltype.mk_globaltype (some r_MUT.MUT) t) v_old →
    Val_ok s v t →
    Forall₂ (fun v0 ty => Globalinst_ok s v0 ty) (list_update_func s.GLOBALS ga (fun g => { g with VALUE := v })) ts := sorry

/-- Rocq `construct_meminsts` (current source). Gained a `Forall wf_byte
    v_nb` premise; also collapses the old separate `v_len` parameter into
    `v_nb.length` directly (Rocq now writes `(|v_nb|)` inline rather than a
    free variable — an "obvious optimization" already reflected here since
    it removes a redundant parameter without changing the fact proved). -/
theorem construct_meminsts (s : store) (ts : List memtype) (ma : Nat) (v_mt : memtype) (b_lst : List byte)
    (v_i : Nat) (v_nb : List byte) :
    Forall wf_byte v_nb →
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst v_mt b_lst →
    Forall₂ (fun v ty => Meminst_ok s v ty)
      (list_update_func s.MEMS ma (fun m => { m with BYTES := list_slice_update m.BYTES v_i v_nb.length v_nb })) ts := sorry

/-- Rocq `construct_meminsts_grow` (2026-09-30 `rocq-backend-proof-final`
    resync). **No longer `Admitted` upstream** — the prior gap (`lim_old +
    v_n ≤ 2^16`, the hard page-count cap baked into `Memtype_ok` via
    `Limits_ok _ (2^16)`; see `Limits_ok`/`Memtype_ok` in `wasm2.0.lean`)
    is now closed because `$growmemory` itself gained a matching
    `-- if i' <= $(2^16)` side condition (`5-runtime-aux.spectec`), which
    Rocq's proof consumes directly instead of deriving it. Mirrored here as
    a new `lim_old + v_n ≤ 2 ^ 16` hypothesis (added last among the
    Nat-valued premises, matching Rocq's new `HBound` position just before
    the `minsts = ...` binder). Still `Nat`-based rather than Rocq's `Q`,
    per the pre-existing representational note (unaffected by this resync).
    **Now a genuine target** (previously permanently blocked) — not yet
    attempted for real: the Rocq proof's own route is pure `Q`/`Z`
    rational-conversion bookkeeping that has no Lean counterpart to mirror,
    and this codebase's zip-based `Forall₂` (unlike Rocq's inductive
    `Forall2`) doesn't support the same structural induction Rocq's proof
    uses without first separately establishing `s.MEMS.length = ts.length`
    (the same class of gap as `Vals_ok`/`Vals_ok_non_bot`, see
    `HelperLemmas.lean`'s `Forall₂` bridge) — flagged for a focused future
    pass rather than rushed here. (Separately, pre-existing and unrelated to
    this resync: this signature hard-codes the declared-max limit as always
    present (`some (uN.mk_uN v_j)`) where Rocq's `v_j_opt` is a genuine
    `Option`; not fixed here, flagged in the audit notes.) -/
theorem construct_meminsts_grow (s : store) (ts : List memtype) (ma : Nat) (b_lst : List byte)
    (lim_old v_n v_j : Nat) (minsts : List meminst) :
    Forall wf_meminst minsts →
    Forall₂ (fun v ty => Meminst_ok s v ty) s.MEMS ts →
    lookup_total s.MEMS ma = meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN lim_old) (some (uN.mk_uN v_j)))) b_lst →
    lim_old = b_lst.length / (64 * Ki) → lim_old + v_n ≤ v_j → lim_old + v_n ≤ 2 ^ 16 →
    minsts = list_update_func s.MEMS ma (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) (some (uN.mk_uN v_j))))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) →
    Forall₂ (fun v ty => Meminst_ok s v ty) minsts
      (list_update_func ts ma (fun _ => memtype.PAGE (limits.mk_limits (uN.mk_uN (lim_old + v_n)) (some (uN.mk_uN v_j))))) := sorry

/-- Rocq `construct_datainsts`. Unaffected by the resync. `data.drop`
    preserves data typedness trivially. -/
theorem construct_datainsts (s : store) (da : Nat) (b_lst : List byte) :
    Forall (fun a => Datainst_ok s a datatype.OK) s.DATAS → lookup_total s.DATAS da = datainst.MKdatainst b_lst →
    Forall (fun a => Datainst_ok s a datatype.OK) (list_update_func s.DATAS da (fun _ => datainst.MKdatainst [])) := sorry

/-- Rocq (last declaration in file) `construct_eleminsts`. Unaffected by the
    resync. `elem.drop` preserves element typedness trivially. -/
theorem construct_eleminsts (s : store) (ts : List elemtype) (ea : Nat) (t : elemtype) (ref_lst : List ref) :
    Forall₂ (fun v ty => Eleminst_ok s v ty) s.ELEMS ts →
    lookup_total s.ELEMS ea = eleminst.MKeleminst t ref_lst →
    Forall₂ (fun v ty => Eleminst_ok s v ty) (list_update_func s.ELEMS ea (fun e => { e with REFS := [] })) ts := sorry

end TLC
