# 2. `store_extension_reduce` and its engine, `store_extension_reduce_aux`

*(Previous: [01-t-preservation.md](01-t-preservation.md). Next: [03-reduce-inst-unchanged.md](03-reduce-inst-unchanged.md).)*

**Plain-English summary.** One step of execution turns the store into a *growth* of itself (§0.6 of the primer) and the new store is still well-typed. This is the half of preservation about the store component specifically, independent of whatever instructions are left to execute.

**Code (`store_extension_reduce`)** — [TypePreservation.lean:1614-1622](../../spectec/src/test-lean-claude/TypePreservation.lean#L1614-L1622):
```lean
theorem store_extension_reduce (s : store) (f : frame) (ais : List admininstr) (s' : store)
    (f' : frame) (ais' : List admininstr) (C C' : context) (tf : functype) :
    wf_config (config.mk_config (state.mk_state s f) ais) →
    Step (config.mk_config (state.mk_state s f) ais) (config.mk_config (state.mk_state s' f') ais') →
    Moduleinst_ok s f.MODULE C → Instrs_ok2 s C' ais tf → inst_match C C' → Store_ok s →
    Extend_store s s' ∧ Store_ok s' := by
  intro hwfc hstep hmi htype him hsok
  obtain ⟨⟨t1s⟩, ⟨t2s⟩⟩ := tf
  exact store_extension_reduce_aux _ _ hstep s f ais s' f' ais' C C' t1s t2s rfl rfl hwfc hmi htype him hsok
```

**Signature.** Takes a well-formed pre-config, a `Step` between the two full configs, the usual `Moduleinst_ok`/`Instrs_ok2`/`inst_match` typing package for the *pre*-state, and `Store_ok s`. Concludes `Extend_store s s' ∧ Store_ok s'` — both halves of the store invariant, for the *post*-store, in one shot. This is a thin wrapper: it just unwraps the `functype tf` into its two bare `List valtype` components (the primer's §0.3 `list` quirk) and hands everything to the `_aux` induction (primer's §0.8 pattern).

**Code (`store_extension_reduce_aux`, the actual induction)** — [TypePreservation.lean:1441-1609](../../spectec/src/test-lean-claude/TypePreservation.lean#L1441-L1609):
```lean
private theorem store_extension_reduce_aux (c1 c2 : config) (hstep : Step c1 c2) :
    ∀ (s : store) (f : frame) (ais : List admininstr) (s' : store) (f' : frame)
      (ais' : List admininstr) (C C' : context) (t1s t2s : List valtype),
      c1 = config.mk_config (state.mk_state s f) ais →
      c2 = config.mk_config (state.mk_state s' f') ais' →
      wf_config c1 → Moduleinst_ok s f.MODULE C → Instrs_ok2 s C' ais (mkFunctype t1s t2s) →
      inst_match C C' → Store_ok s → Extend_store s s' ∧ Store_ok s' := by
  induction hstep
  case pure z ais ais' _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _; injection h2 with hz2 _
    rw [hz1] at hz2; injection hz2 with hs _; subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
  case read z ais ais' _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _; injection h2 with hz2 _
    rw [hz1] at hz2; injection hz2 with hs _; subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
  case ctxt_label z n instrs0 ais z' ais' _ hwf1 _ ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 hais2
    subst hz1 hz2 hais1 hais2
    obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion _ _ _ t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, t's, _, _, _, hbody⟩ := hpt
    exact ih s f ais s' f' ais' C { C' with LABELS := (list.mk_list t's) :: C'.LABELS } [] ts rfl rfl
      hwf1 hmi hbody (construct_inst_prepend_label C C' _ him) hsok
  case ctxt_frame s0 f0 n fi ais s0' fi' ais' _ hwf1 _ ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ htype _ hsok
    injection h1 with hz1 hais1; injection h2 with hz2 hais2
    injection hz1 with hs1 hf1; injection hz2 with hs2 hf2
    subst hs1 hf1 hs2 hf2 hais1 hais2
    obtain ⟨_, _, hpt, _⟩ := ais_single_typing_inversion _ _ _ t1s t2s htype
    unfold ai_principal_typing at hpt
    obtain ⟨ts, _, _, hframe, hexpr, _⟩ := hpt
    cases hframe with
    | mk_Frame_ok vals minst tl C0 hminst _ _ _ _ _ _ =>
      cases hexpr with
      | mk_Expr_ok2 _ _ _ hbody _ _ _ =>
        have him_in : inst_match C0 ({ ({ …, LOCALS := tl, LABELS := [], RETURN := none } ++ C0)
            with RETURN := some (list.mk_list ts) }) := inst_match_locals_append tl C0
        exact ih s0 _ ais s0' fi' ais' C0 _ [] ts rfl rfl hwf1 hminst hbody him_in hsok
  case ctxt_instrs z vals ais ais1 z' ais' _ _ hwf1 _ ih =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 hais2
    subst hz1 hz2 hais1 hais2
    obtain ⟨x1, _, hrest⟩ := ais_composition_typing s C' _ _ t1s t2s htype
    obtain ⟨x2, hA, _⟩ := ais_composition_typing s C' ais ais1 x1 t2s hrest
    exact ih s f ais s' f' ais' C C' x1 x2 rfl rfl hwf1 hmi hA him hsok
  case local_set z v x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _; injection h2 with hz2 _; subst hz1
    simp only [with_local] at hz2; injection hz2 with hs _; subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
  case global_set z v x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    simp only [with_global] at hz2; injection hz2 with hs _; subst hs
    exact global_set_store_ok s f C C' v x t1s t2s hsok hmi him htype
  case table_set_val z i r x _ _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    simp only [with_table] at hz2; injection hz2 with hs _; subst hs
    exact table_set_store_ok s f C C' i r x _ t1s t2s hsok hmi him htype
  case table_grow_succeed z r k x ti var_0 hgrow hne hget =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    simp only [with_tableinst] at hz2; injection hz2 with hs _; subst hs
    exact table_grow_store_ok s f C C' r k _ x ti var_0 t1s t2s hsok hmi him htype hgrow hne hget
  case elem_drop z x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    simp only [with_elem] at hz2; injection hz2 with hs _; subst hs
    exact elem_drop_store_ok s f C C' x t1s t2s hsok hmi him htype
  case store_num_val z i nt c ao b_lst _ _ hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    have hwfn : wf_num_ nt c := wf_const_num (wf_config_ais hwfc _ (by simp))
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_store_mems_inv _ _ _ _ _ _ _ t1s t2s htype) (nbytes__is_wf nt c b_lst hwfn hb)
  case store_pack_val z i v_Inn c k ao b_lst _ _ hc hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    have hwfn : wf_num_ (numtype_Inn v_Inn) c := wf_const_num (wf_config_ais hwfc _ (by simp))
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_store_mems_inv _ _ _ _ _ _ _ t1s t2s htype)
      (ibytes__is_wf k _ b_lst (wrap___is_wf _ k _ _ (wf_num_Inn_proj v_Inn c hwfn hc) rfl) hb)
  case vstore_val z i c ao b_lst _ _ hb =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 hwfc hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing _ _ _ _ _ _ htype
    have hwfv : wf_admininstr (admininstr.VCONST vectype.V128 c) := wf_config_ais hwfc _ (by simp)
    obtain ⟨hsz, hwfu⟩ := wf_vconst_parts hwfv
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_vstore_mems_inversion _ _ ao u1 u2 hop) (vbytes__is_wf vectype.V128 c b_lst hsz hwfu hb)
  case vstore_lane_val z i c v_N ao j b_lst v_Jnn v_M _ _ _ _ _ hb hwfl =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    obtain ⟨u1, u2, hop⟩ := ais_seq3_last_typing _ _ _ _ _ _ htype
    exact with_mem_store_ok s f s' f' C C' _ _ b_lst hz2 hsok hmi him
      (ais_vstore_lane_mems_inversion _ _ v_N ao j u1 u2 hop) (ibytes__is_wf v_N _ b_lst hwfl hb)
  case memory_grow_succeed z v_n mi var_0 hgrow hne hget _ =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    simp only [with_meminst] at hz2; injection hz2 with hs _; subst hs
    exact memory_grow_store_ok s f C C' _ v_n mi var_0 t1s t2s hsok hmi him htype hgrow hne hget
  case data_drop z x =>
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ hmi htype him hsok
    injection h1 with hz1 hais1; injection h2 with hz2 _; subst hz1 hais1
    simp only [with_data] at hz2; injection hz2 with hs _; subst hs
    exact data_drop_store_ok s f C C' x t1s t2s hsok hmi him htype
  -- the remaining rules (traps and failed grows) leave the state unchanged
  all_goals
    intro s f ais0 s' f' ais0' C C' t1s t2s h1 h2 _ _ _ _ hsok
    injection h1 with hz1 _; injection h2 with hz2 _
    rw [hz1] at hz2; injection hz2 with hs _; subst hs
    exact ⟨Extend_store_refl (Store_ok_wf_store _ hsok), hsok⟩
```

**Signature** (of the `_aux`). Same shape as `store_extension_reduce`, but phrased over fully general `c1 c2 : config` plus the two equality premises (`c1 = ...`, `c2 = ...`) that let `induction hstep` work — see primer §0.8.

**Proof sketch.** Induct on the 23 `Step` constructors. `pure`/`read` and every "trap"/"failed grow" rule change nothing about the store (`all_goals` catches these), so they're `Extend_store_refl` — reflexive, trivially a (degenerate) growth of itself. The three congruence rules (`ctxt_label`/`ctxt_frame`/`ctxt_instrs`) peel off one layer of typing structure (via `ais_single_typing_inversion`/`ais_composition_typing`, which read off the *principal type* of the wrapped sub-instruction) and recurse via the induction hypothesis `ih`. Every genuinely store-writing rule (`global_set`, `table_set_val`, `table_grow_succeed`, `elem_drop`, the four memory-write rules, `memory_grow_succeed`, `data_drop`) is dispatched to exactly one of the per-rule lemmas below, after `simp only [with_global, ...]` unfolds the operational `with_*` state-update function enough to match that lemma's conclusion.

## 2a. The seven store-writing lemmas

Each of these proves one `Step` rule's write respects `Extend_store` (primer §0.6) and keeps `Store_ok`. They all share one shape: invert the instruction-sequence typing to learn the store address being written is in-bounds and of the right static type, pull the store apart into its six typed components (`Store_ok_parts`), rebuild the one written component via the matching `Extend_*` fact, and reassemble (`Store_ok_of_parts`).

**`global_set_store_ok`** — *`global.set` writes one value into a global instance, which is sound exactly when that global is declared mutable.*

Code — [TypePreservation.lean:1082-1120](../../spectec/src/test-lean-claude/TypePreservation.lean#L1082-L1120):
```lean
theorem global_set_store_ok (s : store) (f : frame) (C C' : context) (v : val) (x : globalidx)
    (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr_val v, admininstr.GLOBAL_SET x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      GLOBALS := list_update_func s.GLOBALS (f.MODULE.GLOBALS[proj_uN_0 x]!)
        (fun g => { g with VALUE := v }) } ∧
    Store_ok { s with
      GLOBALS := list_update_func s.GLOBALS (f.MODULE.GLOBALS[proj_uN_0 x]!)
        (fun g => { g with VALUE := v }) } := by
  intro hsok hmi him htype
  set gs' := list_update_func s.GLOBALS (f.MODULE.GLOBALS[proj_uN_0 x]!) (fun g => { g with VALUE := v })
    with hgs'
  obtain ⟨t, hlkC, hvok⟩ := ais_global_set_inv s C' v x t1s t2s htype
  obtain ⟨hx, hgt⟩ := getElem?_eq_some_bang hlkC
  have hlenG : f.MODULE.GLOBALS.length = C'.GLOBALS.length := by
    rw [← him.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).1
  obtain ⟨gt', v_old, hga, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.GLOBALS C'.GLOBALS
    (minst_invert_globals s f.MODULE C C' hmi him) hlenG (proj_uN_0 x) (by omega)
  rw [hgt] at hsub
  rw [externtype_global_eq _ _ hsub] at hlk
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfv := Val_ok_wf_val s v t hvok
  have hwfgs' : Forall wf_globalinst gs' := Forall_list_update_func _ s.GLOBALS _ _ hwfG
    (fun g hg => by cases hg with | globalinst_case_ gt0 _ _ => exact wf_globalinst.globalinst_case_ gt0 v hwfv)
  have hwfS' : wf_store { s with GLOBALS := gs' } := wf_store_with_globals s gs' hwfS hwfgs'
  have hext : Extend_store s { s with GLOBALS := gs' } := Extend_store_of_parts _ _
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (global_set_global_extension s.GLOBALS gs' _ t v_old v hwfG hwfv hga hlk hgs')
    (Nat.le_refl _) (extend_mem_refl s hwfM) (Nat.le_refl _) (extend_table_refl s hwfT)
    (Nat.le_refl _) (extend_func_refl s hwfF) (Nat.le_refl _) (extend_data_refl s hwfD)
    (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl ((list_update_length_func _ _ _).trans h1)
    (Extend_store_globalinsts _ _ _ _ hext (construct_globalinsts s gtl _ v t v_old h2 hlk hvok))
    h3 (Extend_store_meminsts _ _ _ _ hext h4) h5 (Extend_store_tableinsts _ _ _ _ hext h6)
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
    h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt htt⟩
```
*Signature:* takes `Store_ok s`, the module-instance/context typing package, and a typing derivation for literally `[v, GLOBAL_SET x]` at any `t1s → t2s`. Concludes the specific updated store (`list_update_func` modifying just slot `f.MODULE.GLOBALS[x]`) is both an `Extend_store` of `s` and itself `Store_ok`.
*Proof sketch:* `ais_global_set_inv` inverts the instruction typing to learn `v`'s type `t` and that `C'` claims a global of that type at slot `x`. `inst_match`/`Moduleinst_ok_lengths` transport that into a concrete store address, and `minst_invert_globals` fetches the old value's `Val_ok` fact. Split the store via `Store_ok_parts`, rebuild only the `GLOBALS` component (`global_set_global_extension` proves the new/old pair satisfies `Extend_globalinst` — it's the mutable-global branch of the primer's §0.6 disjunction, since typing only allows `global.set` on declared-mutable globals), leave the other five components at reflexive extension, and reassemble with `Store_ok_of_parts`.

**`table_set_store_ok`** — *`table.set` writes one reference into one table slot.* Code — [TypePreservation.lean:1123-1161](../../spectec/src/test-lean-claude/TypePreservation.lean#L1123-L1161):
```lean
theorem table_set_store_ok (s : store) (f : frame) (C C' : context) (i : num_) (r : ref) (x : tableidx)
    (k : Nat) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr.CONST numtype.I32 i, admininstr_ref r, admininstr.TABLE_SET x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)
        (fun tb => { tb with REFS := list_update_func tb.REFS k (fun _ => r) }) } ∧
    Store_ok { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)
        (fun tb => { tb with REFS := list_update_func tb.REFS k (fun _ => r) }) } := by
  intro hsok hmi him htype
  set ts' := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!)
    (fun tb => { tb with REFS := list_update_func tb.REFS k (fun _ => r) }) with hts'
  obtain ⟨rt, lim, hlkC, hrok⟩ := ais_table_set_inv s C' i r x t1s t2s htype
  obtain ⟨hx, htt⟩ := getElem?_eq_some_bang hlkC
  have hlenT : f.MODULE.TABLES.length = C'.TABLES.length := by
    rw [← him.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.1
  obtain ⟨tbr, tbt', hta, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.TABLES C'.TABLES
    (minst_invert_tables s f.MODULE C C' hmi him) hlenT (proj_uN_0 x) (by omega)
  rw [htt] at hsub
  obtain ⟨lim', hlim'⟩ := externtype_table_sub_inv _ _ _ hsub
  rw [hlim'] at hlk
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt'⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfts' : Forall wf_tableinst ts' := Forall_list_update_func _ s.TABLES _ _ hwfT
    (fun tb htb => by cases htb with | tableinst_case_ tt0 _ h => exact wf_tableinst.tableinst_case_ tt0 _ h)
  have hwfS' : wf_store { s with TABLES := ts' } := wf_store_with_tables s ts' hwfS hwfts'
  have hext : Extend_store s { s with TABLES := ts' } := Extend_store_of_parts _ _
    (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (table_set_table_extension s.TABLES ts' _ _ tbr k r hwfT hta hlk hts')
    (Nat.le_refl _) (extend_func_refl s hwfF) (Nat.le_refl _) (extend_data_refl s hwfD)
    (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
    h3 (Extend_store_meminsts _ _ _ _ hext h4) ((list_update_length_func _ _ _).trans h5)
    (Extend_store_tableinsts _ _ _ _ hext (construct_tableinsts s ttl rt _ lim' tbr k r h6 hrok hlk))
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
    h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt htt'⟩
```
*Signature/proof sketch:* identical shape to `global_set_store_ok`, just rebuilding `TABLES[x].REFS[k]` instead of `GLOBALS[x].VALUE` — `Extend_tableinst`'s premise `ref_lst.length ≤ ref'_lst.length` is satisfied with equality (`table.set` never changes a table's *size*, only one existing slot's content), proved by `table_set_table_extension`.

**`table_grow_store_ok`** — *`table.grow` appends `v_n` copies of a reference, actually changing the table's length.* Code — [TypePreservation.lean:1164-1232](../../spectec/src/test-lean-claude/TypePreservation.lean#L1164-L1232):
```lean
theorem table_grow_store_ok (s : store) (f : frame) (C C' : context) (r : ref) (v_n : Nat) (k : num_)
    (x : tableidx) (ti : tableinst) (var_0 : Option tableinst) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr_ref r, admininstr.CONST numtype.I32 k, admininstr.TABLE_GROW x] (mkFunctype t1s t2s) →
    fun_growtable (fun_table (state.mk_state s f) x) v_n r var_0 → var_0 ≠ none → Option.get! var_0 = ti →
    Extend_store s { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ => ti) } ∧
    Store_ok { s with
      TABLES := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ => ti) } := by
  intro hsok hmi him htype hgrow hne hget
  cases hgrow with
  | fun_growtable_case_1 _ => exact absurd rfl hne
  | fun_growtable_case_0 ti' i j_opt rt r'_lst i' hold hi' hj hti' _ hwfnew =>
    have hteq : ti' = ti := hget
    subst hteq hti' hi'
    obtain ⟨rt0, lim0, hlkC, hrok⟩ := ais_table_grow_inv s C' r k x t1s t2s htype
    obtain ⟨hx, htt⟩ := getElem?_eq_some_bang hlkC
    have hlenT : f.MODULE.TABLES.length = C'.TABLES.length := by
      rw [← him.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.1
    obtain ⟨tbr, tbt', hta, hlk, hsub⟩ := Forall2_nth_of_length f.MODULE.TABLES C'.TABLES
      (minst_invert_tables s f.MODULE C C' hmi him) hlenT (proj_uN_0 x) (by omega)
    rw [htt] at hsub
    obtain ⟨lim', hlim'⟩ := externtype_table_sub_inv _ _ _ hsub
    rw [hlim'] at hlk
    have hold' := hold.trans hlk
    injection hold' with hT hR
    injection hT with hL hrt
    subst hL hrt hR
    obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt'⟩ :=
      Store_ok_parts s hsok
    obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
    have htok := Forall2_nth_of_length s.TABLES ttl h6 h5 _ hta
    rw [show (s.TABLES[f.MODULE.TABLES[proj_uN_0 x]!]! : tableinst) = lookup_total s.TABLES _ from rfl,
      hlk] at htok
    obtain ⟨rl0, v_m, rt'', he1, he2, _, _⟩ := tableinst_ok_invert s _ _ htok
    injection he1 with hA hB
    rw [← hA] at he2
    injection he2 with hC _
    injection hC with hD _
    subst hB; subst hD
    have hwfnewtt : wf_tabletype (tabletype.mk_tabletype
        (limits.mk_limits (uN.mk_uN (r'_lst.length + v_n)) j_opt) rt) := by
      cases hwfnew with | tableinst_case_ _ _ h => exact h
    set ts' := list_update_func s.TABLES (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ =>
      tableinst.MKtableinst (tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (r'_lst.length + v_n)) j_opt) rt)
        (r'_lst ++ List.replicate v_n r)) with hts'
    have hwfts' : Forall wf_tableinst ts' := Forall_list_update_func _ s.TABLES _ _ hwfT (fun _ _ => hwfnew)
    have hwfS' : wf_store { s with TABLES := ts' } := wf_store_with_tables s ts' hwfS hwfts'
    have hext : Extend_store s { s with TABLES := ts' } := Extend_store_of_parts _ _
      (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
      (Nat.le_of_eq (list_update_length_func _ _ _).symm)
      (table_grow_table_extension s.TABLES ts' _ j_opt r rt v_n r'_lst hwfT hwfts' hta hlk hts')
      (Nat.le_refl _) (extend_func_refl s hwfF) (Nat.le_refl _) (extend_data_refl s hwfD)
      (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
    refine ⟨hext, Store_ok_of_parts _ gtl mtl
      (list_update_func ttl (f.MODULE.TABLES[proj_uN_0 x]!) (fun _ =>
        tabletype.mk_tabletype (limits.mk_limits (uN.mk_uN (r'_lst.length + v_n)) j_opt) rt))
      ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
      h3 (Extend_store_meminsts _ _ _ _ hext h4)
      ((list_update_length_func _ _ _).trans (h5.trans (list_update_length_func _ _ _).symm))
      (Extend_store_tableinsts _ _ _ _ hext
        (construct_tableinsts_grow s ttl r rt _ r'_lst j_opt v_n ts' hwfts' h6 hrok hj hlk hts'))
      h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
      h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt
      (Forall_list_update_func _ ttl _ _ htt' (fun _ _ => hwfnewtt))⟩
```
*Signature:* additionally threads `fun_growtable (fun_table ... x) v_n r var_0` — the *operational* "does growing table `x` by `v_n` elements filled with `r` succeed" relation — plus `var_0 ≠ none`/`Option.get! var_0 = ti` pinning the result to the concrete `ti` the `Step.table_grow_succeed` rule actually produced.
*Proof sketch:* case on `fun_growtable`'s own two constructors (`_case_1` is the failure case — impossible here since `hne : var_0 ≠ none`, dismissed by `absurd`). In the success case, chase down the *old* table's shape from `Store_ok`/`Tableinst_ok` (`tableinst_ok_invert`), confirm the new table literally is `old_refs ++ replicate v_n r` at a bumped minimum size, and feed that to `table_grow_table_extension` to get `Extend_tableinst` (satisfying `n ≤ n'`/`ref_lst.length ≤ ref'_lst.length` by construction, since growing only appends).

**`elem_drop_store_ok`** — *`elem.drop` zeroes out one element segment's contents.* Code — [TypePreservation.lean:1235-1267](../../spectec/src/test-lean-claude/TypePreservation.lean#L1235-L1267):
```lean
theorem elem_drop_store_ok (s : store) (f : frame) (C C' : context) (x : elemidx) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr.ELEM_DROP x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      ELEMS := list_update_func s.ELEMS (f.MODULE.ELEMS[proj_uN_0 x]!)
        (fun e => { e with REFS := [] }) } ∧
    Store_ok { s with
      ELEMS := list_update_func s.ELEMS (f.MODULE.ELEMS[proj_uN_0 x]!)
        (fun e => { e with REFS := [] }) } := by
  intro hsok hmi him htype
  set es' := list_update_func s.ELEMS (f.MODULE.ELEMS[proj_uN_0 x]!) (fun e => { e with REFS := [] })
    with hes'
  obtain ⟨rt, hlkC⟩ := ais_elem_drop_inv s C' x t1s t2s htype
  obtain ⟨hx, _⟩ := getElem?_eq_some_bang hlkC
  have hlenE : f.MODULE.ELEMS.length = C'.ELEMS.length := by
    rw [← him.2.2.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.2.2.2
  obtain ⟨ref_lst, hea, _, hlk⟩ := Forall2_nth_of_length f.MODULE.ELEMS C'.ELEMS
    (minst_invert_elems s f.MODULE C C' hmi him) hlenE (proj_uN_0 x) (by omega)
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfS' : wf_store { s with ELEMS := es' } := wf_store_with_elems s es' hwfS
  have hext : Extend_store s { s with ELEMS := es' } := Extend_store_of_parts _ _
    (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
    (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
    (Nat.le_refl _) (extend_data_refl s hwfD)
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (elem_drop_elem_extension s.ELEMS es' _ hea hes') hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
    h3 (Extend_store_meminsts _ _ _ _ hext h4) h5 (Extend_store_tableinsts _ _ _ _ hext h6)
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) h9 (Extend_store_datainsts₂ _ _ _ _ hext h10)
    ((list_update_length_func _ _ _).trans h11)
    (Extend_store_eleminsts _ _ _ _ hext (construct_eleminsts s etl _ _ ref_lst h12 hlk)) hwfS' hmt htt⟩
```
*Proof sketch:* the simplest of the seven — no operational side-relation to case on, since `elem.drop` unconditionally sets `REFS := []`, which is exactly `Extend_eleminst`'s *right* disjunct (`ref'_lst = []`), proved directly by `elem_drop_elem_extension`.

**`data_drop_store_ok`** — *`data.drop`'s exact mirror image for data segments,* same shape, `Extend_datainst`'s `b'_lst = []` disjunct. Code — [TypePreservation.lean:1270-1306](../../spectec/src/test-lean-claude/TypePreservation.lean#L1270-L1306):
```lean
theorem data_drop_store_ok (s : store) (f : frame) (C C' : context) (x : dataidx) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [admininstr.DATA_DROP x] (mkFunctype t1s t2s) →
    Extend_store s { s with
      DATAS := list_update_func s.DATAS (f.MODULE.DATAS[proj_uN_0 x]!)
        (fun _ => datainst.MKdatainst []) } ∧
    Store_ok { s with
      DATAS := list_update_func s.DATAS (f.MODULE.DATAS[proj_uN_0 x]!)
        (fun _ => datainst.MKdatainst []) } := by
  intro hsok hmi him htype
  set ds' := list_update_func s.DATAS (f.MODULE.DATAS[proj_uN_0 x]!) (fun _ => datainst.MKdatainst [])
    with hds'
  have hlkC := ais_data_drop_inv s C' x t1s t2s htype
  obtain ⟨hx, _⟩ := getElem?_eq_some_bang hlkC
  obtain ⟨hlenD, hdas⟩ := minst_invert_datas s f.MODULE C C' hmi him
  have hxm : proj_uN_0 x < f.MODULE.DATAS.length := by omega
  have hmem : f.MODULE.DATAS[proj_uN_0 x]! ∈ f.MODULE.DATAS := by
    rw [getElem!_pos f.MODULE.DATAS _ hxm]; exact List.getElem_mem hxm
  obtain ⟨b_lst, hda, hlk⟩ := hdas _ hmem
  obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
    Store_ok_parts s hsok
  obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
  have hwfds' : Forall wf_datainst ds' := Forall_list_update_func _ s.DATAS _ _ hwfD
    (fun _ _ => wf_datainst.datainst_case_ [] (by intro _ h; simp at h))
  have hwfS' : wf_store { s with DATAS := ds' } := wf_store_with_datas s ds' hwfS hwfds'
  have hext : Extend_store s { s with DATAS := ds' } := Extend_store_of_parts _ _
    (Nat.le_refl _) (extend_global_refl s hwfG) (Nat.le_refl _) (extend_mem_refl s hwfM)
    (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
    (Nat.le_of_eq (list_update_length_func _ _ _).symm)
    (data_drop_data_extension s.DATAS ds' _ hwfD hda hds')
    (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
  refine ⟨hext, Store_ok_of_parts _ gtl mtl ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
    h3 (Extend_store_meminsts _ _ _ _ hext h4) h5 (Extend_store_tableinsts _ _ _ _ hext h6)
    h7 (Extend_store_funcinsts _ _ _ _ hext h8) ((list_update_length_func _ _ _).trans h9)
    (datainsts_Forall₂_of_Forall _ _ dtl (Extend_store_datainsts _ _ _ hext
      (construct_datainsts s _ b_lst (datainsts_Forall_of_Forall₂ s s.DATAS dtl h9 h10) hlk)))
    h11 (Extend_store_eleminsts _ _ _ _ hext h12) hwfS' hmt htt⟩
```

**`with_mem_store_ok`** — *the shared engine behind all four memory-write rules* (`store_num_val`, `store_pack_val`, `vstore_val`, `vstore_lane_val`): they all ultimately call the same operational `with_mem` state-update, so one lemma covers all four. Code — [TypePreservation.lean:1344-1354](../../spectec/src/test-lean-claude/TypePreservation.lean#L1344-L1354):
```lean
theorem with_mem_store_ok (s : store) (f : frame) (s' : store) (f' : frame) (C C' : context)
    (off len : Nat) (b_lst : List byte) :
    with_mem (state.mk_state s f) (uN.mk_uN 0) off len b_lst = state.mk_state s' f' →
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' → 0 < C'.MEMS.length →
    Forall wf_byte b_lst → Extend_store s s' ∧ Store_ok s' := by
  intro heq hsok hmi him hmem hwfb
  simp only [with_mem, splice_eq_list_slice_update] at heq
  injection heq with hs _
  subst hs
  exact mem_store_extension s f C C' off b_lst b_lst.length hsok (Store_ok_wf_store s hsok) hmi him hmem
    hwfb rfl
```
*Signature:* rather than naming the instruction at all, this is phrased purely operationally — "if `with_mem` (write `b_lst` at byte-offset `off` into memory 0) takes `(s,f)` to `(s',f')`, and the usual typing package holds plus `0 < C'.MEMS.length` (memory 0 exists) and the bytes are well-formed, you get the store invariant." That genericity is exactly why it's reusable for four different `Step` rules (which differ only in *how* `b_lst` was computed — raw bytes, packed/wrapped integer bytes, vector bytes, or one lane's bytes — not in what happens to the store). It just delegates to `mem_store_extension`, which does the real `Store_ok_parts`/`Extend_meminst` work in one place.

**`memory_grow_store_ok`** — *`memory.grow`'s structural twin of `table_grow_store_ok`*, appending `v_n` pages of zero bytes. Code — [TypePreservation.lean:1358-1435](../../spectec/src/test-lean-claude/TypePreservation.lean#L1358-L1435):
```lean
theorem memory_grow_store_ok (s : store) (f : frame) (C C' : context) (a : admininstr) (v_n : Nat)
    (mi : meminst) (var_0 : Option meminst) (t1s t2s : List valtype) :
    Store_ok s → Moduleinst_ok s f.MODULE C → inst_match C C' →
    Instrs_ok2 s C' [a, admininstr.MEMORY_GROW] (mkFunctype t1s t2s) →
    fun_growmemory (fun_mem (state.mk_state s f) (uN.mk_uN 0)) v_n var_0 → var_0 ≠ none →
    Option.get! var_0 = mi →
    Extend_store s { s with
      MEMS := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ => mi) } ∧
    Store_ok { s with
      MEMS := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ => mi) } := by
  intro hsok hmi him htype hgrow hne hget
  cases hgrow with
  | fun_growmemory_case_1 _ => exact absurd rfl hne
  | fun_growmemory_case_0 mi' i j_opt b_lst i' hold hi' hj h216 hmi' _ hwfnew =>
    have hmeq : mi' = mi := hget
    subst hmeq hmi'
    have hmems := ais_memory_grow_inv s C' a t1s t2s htype
    have hlenM : f.MODULE.MEMS.length = C'.MEMS.length := by
      rw [← him.2.2.2.2.1]; exact (Moduleinst_ok_lengths s _ C hmi).2.2.1
    obtain ⟨_, _, hma, _, _⟩ := Forall2_nth_of_length f.MODULE.MEMS C'.MEMS
      (minst_invert_mems s f.MODULE C C' hmi him) hlenM 0 (by omega)
    obtain ⟨gtl, mtl, ttl, ftl, dtl, etl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hwfS, hmt, htt⟩ :=
      Store_ok_parts s hsok
    obtain ⟨hwfF, hwfG, hwfT, hwfM, hwfD⟩ := wf_store_parts s hwfS
    have hmok := Forall2_nth_of_length s.MEMS mtl h4 h3 _ hma
    obtain ⟨vn0, m_opt, bs0, he1, _, hblen, _, _⟩ := meminst_ok_raw s _ _ hmok
    have hold' : meminst.MKmeminst (memtype.PAGE (limits.mk_limits i j_opt)) b_lst =
        meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN vn0) (m_opt.map uN.mk_uN))) bs0 :=
      hold.trans he1
    injection hold' with hA hB
    injection hA with hA'
    injection hA' with hC hjo
    subst hC hjo hB
    have hi'' : i' = ((vn0 + v_n : Nat) : Rat) := by
      rw [hi', hblen]; unfold Ki; push_cast; ring
    subst hi''
    rw [rat_to_nat_natCast] at hwfnew ⊢
    have h216' : vn0 + v_n ≤ 2 ^ 16 := by exact_mod_cast h216
    have hjn : Forall (fun v_j => vn0 + v_n ≤ proj_uN_0 v_j) (Option.toList (m_opt.map uN.mk_uN)) := by
      intro v_j hv; have := hj v_j hv; exact_mod_cast this
    have hjn' : Forall (fun j => vn0 + v_n ≤ j) m_opt.toList := by
      intro j hjm
      have hmem : uN.mk_uN j ∈ Option.toList (m_opt.map uN.mk_uN) := by
        rcases m_opt with _ | m0
        · simp at hjm
        · simp only [Option.toList_some, List.mem_singleton] at hjm; subst hjm; simp
      exact hjn _ hmem
    have hlim : vn0 = b_lst.length / (64 * Ki) := by
      rw [hblen, Nat.mul_div_cancel _ (by unfold Ki; norm_num)]
    have hwfmt : wf_memtype (memtype.PAGE (limits.mk_limits (uN.mk_uN (vn0 + v_n)) (m_opt.map uN.mk_uN))) := by
      cases hwfnew with | meminst_case_ _ _ h _ => exact h
    set ms' := list_update_func s.MEMS (f.MODULE.MEMS[0]!) (fun _ =>
      meminst.MKmeminst (memtype.PAGE (limits.mk_limits (uN.mk_uN (vn0 + v_n)) (m_opt.map uN.mk_uN)))
        (b_lst ++ List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0))) with hms'
    have hwfms' : Forall wf_meminst ms' := Forall_list_update_func _ s.MEMS _ _ hwfM (fun _ _ => hwfnew)
    have hwfS' : wf_store { s with MEMS := ms' } := wf_store_with_mems s ms' hwfS hwfms'
    have hext : Extend_store s { s with MEMS := ms' } := Extend_store_of_parts _ _
      (Nat.le_refl _) (extend_global_refl s hwfG)
      (Nat.le_of_eq (list_update_length_func _ _ _).symm)
      (memory_grow_mem_extension s.MEMS ms' _ b_lst vn0 v_n m_opt hwfM hwfms' hma he1 hjn' hms')
      (Nat.le_refl _) (extend_table_refl s hwfT) (Nat.le_refl _) (extend_func_refl s hwfF)
      (Nat.le_refl _) (extend_data_refl s hwfD) (Nat.le_refl _) (extend_elem_refl s) hwfS hwfS'
    refine ⟨hext, Store_ok_of_parts _ gtl
      (list_update_func mtl (f.MODULE.MEMS[0]!) (fun _ =>
        memtype.PAGE (limits.mk_limits (uN.mk_uN (vn0 + v_n)) (m_opt.map uN.mk_uN))))
      ttl ftl dtl etl h1 (Extend_store_globalinsts _ _ _ _ hext h2)
      ((list_update_length_func _ _ _).trans (h3.trans (list_update_length_func _ _ _).symm))
      (Extend_store_meminsts _ _ _ _ hext
        (construct_meminsts_grow s mtl _ b_lst vn0 v_n _ ms' hwfms' h4 he1 hlim hjn h216' hms'))
      h5 (Extend_store_tableinsts _ _ _ _ hext h6) h7 (Extend_store_funcinsts _ _ _ _ hext h8)
      h9 (Extend_store_datainsts₂ _ _ _ _ hext h10) h11 (Extend_store_eleminsts _ _ _ _ hext h12)
      hwfS' (Forall_list_update_func _ mtl _ _ hmt (fun _ _ => hwfmt)) htt⟩
```
*The one genuinely interesting arithmetic step* is `rat_to_nat_natCast`: the spec computes the new page count as a *rational* expression `⌊|bytes|/64Ki⌋ + n` (`rat_to_nat` of a `Rat`), because the generated code is mechanically translating the spec's generic arithmetic; this lemma — [TypePreservation.lean:1318-1319](../../spectec/src/test-lean-claude/TypePreservation.lean#L1318-L1319), `theorem rat_to_nat_natCast (n : Nat) : rat_to_nat (n : Rat) = n := by simp [rat_to_nat]` — confirms that for any store satisfying `Store_ok` (where the old page count is provably a genuine natural number, not a weird fraction), that rational expression is *actually* just `vn0 + v_n : Nat`, letting the rest of the proof work with ordinary `Nat` arithmetic.

## 2b. `Extend_store_refl`

**Plain-English summary.** Reflexivity: a store trivially "extends" itself (every component is unchanged, which satisfies every `Extend_*` relation's "stayed the same or only grew" clause). Used by every `Step` case that doesn't touch the store at all (`pure`, `read`, `local_set`, and every trap/failed-grow rule).

**Code** — [ExtensionLemmas.lean:1051-1074](../../spectec/src/test-lean-claude/ExtensionLemmas.lean#L1051-L1074):
```lean
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
```
**Signature:** just `wf_store s → Extend_store s s` — note it needs `wf_store`, not `Store_ok`; reflexivity of "growth" only needs syntactic sanity, not typing. **Proof sketch:** destructure `wf_store`'s one constructor to get each component's well-formedness, then build `Extend_store.mk_Extend_store` field by field: "every address below the length is in range" (`forall_range_lt`) is trivially true against itself, and "each old/new pair at that address satisfies `Extend_<thing>inst`" reduces, when old=new, to each `Extend_<thing>inst`'s own dedicated reflexivity fact (`extend_globalinst_refl_0`, etc. — one tiny lemma per component, applying the "or equal" side of each disjunction from primer §0.6).

## Bonus: `step_moduleinst` — the pre-packaged composition

Not separately named in the diagram, but worth flagging since it exists in the source and *is* exactly "`store_extension_reduce` + `reduce_inst_unchanged` + `Extend_store_moduleinst`, composed" — [TypePreservation.lean:1626-1636](../../spectec/src/test-lean-claude/TypePreservation.lean#L1626-L1636):
```lean
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
```
Interesting detail from reading `t_preservation`'s actual proof term (file `01`): it does *not* call `step_moduleinst`. It inlines the same three-lemma composition directly instead (you can see `reduce_inst_unchanged`, `Extend_store_moduleinst`, and `.1` of `store_extension_reduce`'s pair, called separately). `step_moduleinst` is available — ported 1:1 from the Rocq lemma of the same name — but this particular caller just didn't route through it.

---
*Next: [03-reduce-inst-unchanged.md](03-reduce-inst-unchanged.md).*
