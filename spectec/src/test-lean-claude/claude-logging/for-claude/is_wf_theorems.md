# `*_is_wf` theorem tracking

Per user instruction: track every `*_is_wf` theorem from `wasm2.0.lean`
that this project ends up relying on, with a true/false/unknown
assessment. Unknown (still `sorry` in `wasm2.0.lean`) ones are treated as
true-for-now unless trivial to prove ourselves. A separate, parallel
Claude effort is auditing `*_is_wf` theorems directly — expect
`wasm2.0.lean` to change under us; re-check before trusting.

## Status as of session 1 (Phase 1: skeleton complete, no proofs filled in yet)

**None used yet.** All lemma proofs across `HelperLemmas.lean`,
`Subtyping.lean`, `TypingLemmas.lean`, `TypePreservationPure.lean`,
`ExtensionLemmas.lean`, `TypePreservation.lean` are currently `sorry`
placeholders (Phase 1 only stated signatures, didn't write actual proof
terms). No `*_is_wf` theorem has been invoked in an actual proof term
yet, so there is nothing to track here.

The two axioms ported into `HelperLemmas.lean` (`nbytes_len`, `ibytes_len`)
reference the *opaque definitions* `nbytes_`/`ibytes_`/`wrap__`/`size`
from `wasm2.0.lean`, not their `*_is_wf` companion theorems
(`nbytes__is_wf`, `ibytes__is_wf`, `wrap___is_wf`) — those weren't needed
for stating the axioms themselves.

## Table (append rows here as Phase 2/3 proofs come to depend on `*_is_wf` theorems)

| `*_is_wf` theorem | Used by (our lemma/file) | Status in `wasm2.0.lean` (sorry/proved) | Assessed true/false/unknown | Notes |
|---|---|---|---|---|
| _(none yet)_ | | | | |

## How to fill this in going forward

When a Phase 2/3 proof needs to invoke some `Foo_is_wf` theorem from
`wasm2.0.lean`:
1. Check whether it's currently `sorry` or has a real proof
   (`grep -A3 "theorem Foo_is_wf" wasm2.0.lean` then look for `sorry` vs a
   tactic proof).
2. If it has a real proof already: mark "proved" in the table, no further
   action.
3. If it's `sorry`: try to prove it yourself if it looks simple (a few
   lines); if you do, note "proved by us" in the table and consider
   whether to leave your proof in a note here vs. actually fixing it in
   `wasm2.0.lean` — **remember `wasm2.0.lean` is not ours to edit** (it's
   the parallel effort's file); if you need the fact, restate it as your
   own local lemma in one of our files instead, referencing the
   `wasm2.0.lean` theorem name in a comment for traceability.
4. If it's `sorry` and non-trivial: mark "unknown, treated as true" in
   the table and move on — per user instruction, this is acceptable
   default behavior, just log it here so it's auditable.
5. If you have reason to believe it's actually FALSE (e.g. you found a
   counterexample): mark "false" and describe the counterexample; flag
   prominently to the user, since this would be a serious finding
   affecting both this project and the parallel `*_is_wf` audit.
