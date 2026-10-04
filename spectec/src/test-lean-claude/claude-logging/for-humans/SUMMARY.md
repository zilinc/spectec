# Progress summary (human-readable)

**Last updated:** 2026-10-04 (bundle19). The sections below the first one are the
original session-1 summary, kept for history; for the step-by-step record see each
`verbatim_dialogue_log/bundleN/response_N.md`.

## Latest (2026-10-04, bundle19)

- **Preservation is proved**, apart from generated well-formedness facts that the Rocq
  proof also leaves unproved. The last real proof, `t_read_preservation` (all 47 read-only
  reduction rules), is done, and the main preservation file has no `sorry` left.
- **The generated file `wasm2.0.lean`:** all 89 well-formedness theorems that Rocq proves
  are now proved in Lean too. The 63 still open are exactly the ones Rocq leaves
  `Admitted`.
- **What preservation still rests on:** 33 generated theorems, all unproved in Rocq as well.
  - `Step_read_is_wf`: false in the known 4 GiB-memory corner case (spec fix pending).
  - 32 facts that numeric operations (`iand`, `fabs`, `lanes`, ...) return valid values.
    The generated Lean leaves those operations undefined (`opaque`), so the facts can't be
    proved there, but none of them is false.
- **The user's fixes worked.** `rat_to_nat` now has a real definition. The locals
  hypothesis now uses `Vals_ok`, which adds the length fact.
- **One maintenance cost:** the proofs sit inside the generated file, so regenerating it
  erases them. `bundle19/user_requested_documents/wasm2.0_hand_edits.patch` puts them back
  (tested).

## Previous (2026-10-03, bundle18)

- **Preservation is nearly done.** 18 `sorry`s remain (was 26). 16 are dead helpers nobody
  uses. Of the other two, `t_read_preservation` is real work (47 small cases, plan written),
  and `rat_to_nat_natCast` can't be proved until the backend gives `rat_to_nat` a real
  definition.
- **Newly proved:** `store_extension_reduce` (a step extends the store and keeps it valid),
  `t_pure_preservation`, `t_preservation_type`, and all the SIMD lemmas.
- **The user's two changes were correct**: the `br_table_ge` premise was redundant, and the
  `splice`-based regeneration fixed the store bug found in bundle17.
- **Known limit**: `memory.fill`/`memory.copy`/`memory.init` on a full 4 GiB memory can push
  the out-of-range constant `2^32`. In that corner case preservation is false, in Rocq too.
  This is a spec issue.

## Previous (2026-10-02, bundle17)

- **Where the port stands**: the helper, subtyping and typing-lemma files are complete;
  the store-extension file has one leftover `sorry` (a lemma upstream deleted); the
  pure-preservation file has 7 and the main preservation file 3; plus 15 dead helper
  lemmas. The top-level preservation theorem typechecks, but on top of `sorry`s.
- **Correction**: earlier reports said 5 of the remaining preservation lemmas were
  deliberately left open because the Rocq proof left them open. That was out of date:
  upstream Rocq has proved all of them, including every SIMD (vector) case, since
  2026-09-22. So the Lean port has more to do than reported: about 70 Rocq
  declarations are not yet in Lean, mostly the SIMD preservation lemmas.
- **Problem found, needs a decision**: the Lean code generator writes "overwrite
  bytes i..i+j of memory" in a way that makes memory *grow* if the write is out of
  bounds. Rocq's generator writes it in a way that never changes the length. Because the
  spec's store rule doesn't itself check bounds, in the Lean model an out-of-bounds store
  can produce a memory of an invalid size, so **the preservation theorem is actually
  false in the Lean model as generated.** Proposed fixes are in
  `verbatim_dialogue_log/bundle17/user_requested_documents/with_mem_slice_update_issue.md`.
- Upstream itself documents a small spec corner case (an address overflow in the bulk
  memory instructions) that also breaks preservation, in both Rocq and Lean.
- Work stopped at that point to report, per the standing instructions. No Lean files
  were changed this turn.


## What this is

Porting the Rocq (Coq) mechanized proof of WASM 2.0 type safety
(`spectec/test-rocq/theories/`, ~27,000 lines across 9 files) into Lean 4,
lemma-by-lemma, inside `spectec/src/test-lean-claude/`.

## Where things stand

- **Project scaffolding is done and builds.** Copied the mathlib toolchain
  setup from the sibling `test-lean` project (saved re-downloading several
  GB), wrote a `lakefile.lean`, and confirmed `lake build` succeeds on the
  backend-generated base file (`wasm2.0.lean`) as-is.
- **Good news on scope:** most of what Rocq's `wasm.v` hand-defines (types,
  store, typing judgments, reduction rules) is *already auto-generated* in
  `wasm2.0.lean` by the same SpecTec pipeline, just targeting Lean instead
  of Rocq. So the real porting work is just the **lemma files** — the
  hand-written Rocq proofs about those definitions — not the definitions
  themselves.
- **Reconnaissance phase:** dispatched parallel research passes over the
  whole Rocq proof and over a previous (separate) Lean-porting attempt left
  behind in `spectec/test-lean/`, to build an accurate map before writing
  any Lean. Two of these have reported back so far:
  - `helper_lemmas.v` (general list/arithmetic helper lemmas, ~45 lemmas) —
    fully digested. Mostly small, mechanically portable facts; several are
    pure artifacts of Rocq using two different list libraries at once
    (mathcomp vs stdlib) and won't need a Lean counterpart at all.
  - `type_preservation.v` (2802 lines) — the **capstone file** containing
    the main preservation theorem. Fully digested. Key finding: the file is
    essentially complete — only 3 lemmas are `Admitted` (left incomplete)
    in the original Rocq proof, and in every case the *only* gap is the
    SIMD/vector-instruction cases, which don't otherwise affect the
    argument. Everything else, including the final top-level theorem
    `t_preservation`, is fully proved in Rocq. That's a strong, concrete
    target for the Lean side: mirror the same gaps, aim to close everything
    else for real.
  - Remaining files (the core `wasm.v`, `subtyping.v`, `extension_lemmas.v`,
    `typing_lemmas.v`, `type_preservation_pure.v`, and the old Lean attempt)
    are still being digested.
- Nothing outside `spectec/src/test-lean-claude/` has been touched — verified
  by a repeatable safety-check script that's run periodically and logged.

## Major update: full skeleton in place and building

All 6 Rocq lemma files now have a matching Lean file:

| Lean file | Ports | Declarations |
|---|---|---|
| `HelperLemmas.lean` | `helper_lemmas.v` + `axioms.v` | ~48 |
| `Subtyping.lean` | `subtyping.v` | ~35 |
| `TypingLemmas.lean` | `typing_lemmas.v` | ~50 |
| `TypePreservationPure.lean` | `type_preservation_pure.v` | 29 |
| `ExtensionLemmas.lean` | `extension_lemmas.v` | ~55 |
| `TypePreservation.lean` | `type_preservation.v` (capstone) | 13 |

Every signature is stated, every proof body is a placeholder (`sorry`),
and **the whole project compiles cleanly** — no type errors, only the
expected "uses sorry" warnings. This means the shape of the whole proof —
every lemma statement, matched field-for-field against the Rocq
original — is now locked in and mechanically checked to be *coherent*
(the types all fit together), even before a single proof is filled in.
That's the hard, error-prone part of a translation like this; what's left
is filling in proofs, which is more mechanical (though still substantial
— roughly 230 lemmas total).

A couple of honest caveats: two of the definitions in `TypingLemmas.lean`
(`instr_of` and `ai_principal_typing`) are large per-instruction case
definitions that are still placeholder bodies, not just placeholder
proofs — filling those in is real remaining work, flagged clearly in the
file. And a handful of proofs are *deliberately* left as placeholders
because the original Rocq proof itself leaves them incomplete (all
SIMD-related, plus one control-flow case) — those aren't bugs, they're
faithfully mirroring gaps that exist in the source.

## What's next

Once the remaining digests are in: build a naming dictionary between the
Rocq proof's identifiers and the auto-generated Lean file's identifiers,
then write out every lemma/definition signature from the Rocq lemma files
as Lean stubs (`sorry`), confirm it all typechecks, and start filling in
proofs — easiest ones first.
