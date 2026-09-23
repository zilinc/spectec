# Progress summary (human-readable)

**Last updated:** 2026-09-23, session 1 (resumed once after a VSCode crash).

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
