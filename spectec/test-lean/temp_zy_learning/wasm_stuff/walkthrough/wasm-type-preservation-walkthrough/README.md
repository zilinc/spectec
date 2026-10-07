# WASM 2.0 type-preservation walkthrough

A function-by-function walkthrough of the `t_preservation` theorem tree in this repo's
Lean port of WASM 2.0 type soundness, written up from a chat conversation. It follows
this dependency diagram (from `claude-logging/for-claude/verbatim_dialogue_log/bundle20/user_requested_documents/preservation_audit_report.md`):

```
t_preservation  (TypePreservation.lean:2699)          Step c1 c2 → Config_ok c1 ts → Config_ok c2 ts
│  Unpacks Config_ok → State_ok → Store_ok + Frame_ok (Moduleinst_ok, locals typed) + Expr_ok2 (Instrs_ok2),
│  then re-packs the same structure for c2 from:
├─ store_extension_reduce   (TP:1611)   Step ⇒ Extend_store s s' ∧ Store_ok s'
│   └─ store_extension_reduce_aux (TP:1438): induction on the Step derivation
│        (equational premises c1 = …, c2 = … encode Rocq's `dependent induction`)
│        ├─ congruence rules (label/frame/instrs context): the IH
│        ├─ store-writing rules → one lemma each: global_set_store_ok, table_set_store_ok,
│        │   table_grow_store_ok, elem_drop_store_ok, data_drop_store_ok,
│        │   with_mem_store_ok (TP:1341, the 4 store rules), memory_grow_store_ok (TP:1355)
│        └─ every other rule: store unchanged ⇒ Extend_store_refl
├─ reduce_inst_unchanged    (TP:536)    a step never changes the frame's MODULE
├─ Extend_store_moduleinst  (ExtensionLemmas.lean:1724)  Moduleinst_ok survives store extension
├─ t_preservation_vs_type   (TP:227)    the locals stay well-typed (Vals_ok) across a step
└─ t_preservation_type      (TP:2679)   the instruction sequence keeps its type
    └─ t_preservation_type_aux (TP:2422): induction on Step
         ├─ Step.pure  → t_pure_preservation (TypePreservationPure.lean:1858): case split over the
         │               54 Step_pure rules, one Step_pure__*_preserves lemma per rule
         ├─ Step.read  → t_read_preservation (TP:2028): case split over the 47 Step_read rules
         ├─ congruence rules (ctxt_label / ctxt_frame / ctxt_instrs): IH + typing decomposition
         └─ store-writing rules: the reduct is [] or a constant, typed directly
```

(Line numbers above are the diagram's own, from an earlier snapshot; the file links in
each section below use the actual current line numbers, verified against the source
at write time.)

## Status

Covers **Part 0** (the WASM 2.0 primer) and **Part 1, sections 1 through 7a** in full —
i.e. everything in the diagram except the `t_read_preservation` leaf. That section
(the 47-case `Step_read` dispatcher) is the one piece not written up yet; ask to have
it added as `09-t-read-preservation.md` when wanted.

## Files

- [`00-primer.md`](00-primer.md) — WASM 2.0 background: the execution model, runtime
  state, static types, the `wf_*` vs `*_ok` judgment families, the typing judgments,
  store growth (`Extend_store`), the `Step`/`Step_pure`/`Step_read` split, and the
  Rocq→Lean `_aux` porting pattern used throughout.
- [`01-t-preservation.md`](01-t-preservation.md) — the top-level theorem.
- [`02-store-extension-reduce.md`](02-store-extension-reduce.md) — `store_extension_reduce`
  / `store_extension_reduce_aux`, the seven store-writing lemmas, `Extend_store_refl`,
  and the bonus `step_moduleinst` composition.
- [`03-reduce-inst-unchanged.md`](03-reduce-inst-unchanged.md)
- [`04-extend-store-moduleinst.md`](04-extend-store-moduleinst.md)
- [`05-t-preservation-vs-type.md`](05-t-preservation-vs-type.md)
- [`06-t-preservation-type.md`](06-t-preservation-type.md)
- [`07-t-preservation-type-aux.md`](07-t-preservation-type-aux.md) — the 23-case `Step`
  dispatcher, including the `t_pure_preservation` hand-off (§7a, full 54-case proof).

All source citations are relative links from this folder back into `spectec/src/test-lean-claude/`.
