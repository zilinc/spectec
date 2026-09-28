# Notes for a future Claude session — READ THIS FIRST

Last updated: 2026-09-24 (session 2 — a fresh Claude session that picked this
project up cold, per the user's instruction, continuing session 1's standing
rules; see `claude-logging/verbatim_dialogue_log/bundle3`/`bundle4`).

## ✅ 2026-09-24 UPDATE (bundle8) — `ai_principal_typing` ported, `Mathlib` now imported

`spectec/test-lean/typing_lemmas.lean` (a prior, hand-written Lean attempt
by the user, predating this project, built against a **byte-identical**
`wasm2.0.lean` — confirmed via `diff`) turned out to already contain a
mostly-complete `ai_principal_typing` (the ~340-line, 50+ case central
definition that everything in the "inversion" family depends on) plus
proved `instr_typing_inversion`/`ai_typing_inversion`/
`principal_typing_conversion`. Per the user's explicit go-ahead (check
correctness first), all four were ported into `TypingLemmas.lean`. **One
real bug was found and fixed** in the source file's `BR_TABLE` case: an
unparenthesized `∀ l ∈ ls, ...` accidentally swallowed a trailing `∃ r',
...` clause, silently dropping the default-label validity/subtyping
requirement whenever `ls = []` — checked against the live Rocq
`ai_principal_typing` (`typing_lemmas.v:414`) to confirm the fix. See
`bundle8/response_8.md` for the full list of what was ported and the other
correctness spot-checks (LOAD/STORE packed-access cases flagged as a
possible live upstream-vs-port discrepancy, not a porting bug).

**`TypingLemmas.lean` now `import Mathlib.Tactic`** (first use of Mathlib
in this project; it was already a resolved-but-unused `lakefile.lean`
dependency). Fetched via `lake exe cache get` rather than a from-source
compile. If you're picking this file up cold: it now uses `omega`,
`norm_num`, `exact_mod_cast`, `positivity`, `linarith`, and a
Mathlib-enlarged `simp_all` in a few of the newly-ported proofs — this is
expected, not a mistake to "clean up."

**A real representation gap was found (not fixed, per the user's explicit
instruction to leave it for their own review)**: `Vals_ok_non_bot` is false
as literally stated, because this project's generated `Forall₂` is a
zip-based `def` (doesn't force equal list lengths) unlike Rocq's
length-forcing inductive `Forall2`. Full writeup with fix options:
`bundle8/vals_ok_non_bot_analysis.md`. **Do not attempt to prove
`Vals_ok_non_bot` as currently stated** — it needs either a length
hypothesis added to its signature or `Vals_ok`'s own definition changed
first; see the analysis doc before touching it.

**`cases`/`case` binder-ordering discovery**: beyond the previously-known
"a leading `store`/`context` index doesn't get a name if it unifies with an
existing outer variable" rule, this bundle found that hypotheses whose type
*mentions already-bound data* can get reordered ahead of hypotheses that
are textually earlier in the source constructor declaration (seen in
`Instr_ok.br_table`, `Instr_ok2.plain`, `Ref_ok.func`). When a `case tag
names... => ...` block's names don't type-check against what you expected
from reading the source declaration, don't try to hand-recompute the
order — replace the tactic body with `trace_state; sorry` (or plain
`cases h` + `rename_i` if even that doesn't help, as it didn't for one
`Ref_ok.func` spot) and read the real order off the dumped context.

## ✅ 2026-09-24 UPDATE — `ExtensionLemmas.lean` rename/reshape pass done

Per the 2026-09-23 resync update immediately below, `ExtensionLemmas.lean`
has now been brought current against the live Rocq source (`a8b585cdb`):
every renamed `store_extension_*`/`*_extension_refl*` identifier is now
`Extend_store_*`/`extend_*_refl*`, the `holds_upto` idiom (matching Rocq
`wasm.v:107`'s own definition) has been introduced and used throughout for
every lemma whose conclusion moved from `Forall₂`/existential-split to an
index-based shape, `minst_invert_funcs`/`_tables`/`_globals`/`_mems` now use
the unified `Externtype_sub` relation (already present in `wasm2.0.lean`),
6 new lemmas were added (`limits_sub_refl`/`_trans`, `externtype_sub_refl`/
`_trans`, `externtype_global_eq`/`_func_eq`, `Extend_store_refs'`), and every
lemma that gained a new `wf_*` premise or restructured hypothesis upstream
(`global_set_global_extension`, `store_none_mem_extension`,
`memory_grow_mem_extension`, `table_set_table_extension`,
`table_grow_table_extension`, `elem_drop_elem_extension`,
`data_drop_data_extension`, all 8 `addrs_*`/`addrss_*_extension` lemmas,
`construct_tableinsts_grow`, `construct_meminsts`, `construct_meminsts_grow`)
has been restated to match. `HelperLemmas.lean` also got the 7 new
`axioms.v` axioms (`nbytes_len'`, `ibytes_len'`, `ibytes_len''`,
`vbytes_len'`, `truncz_quot`, `lanes_len`, `nbytes_inv`, `ibytes_inv`,
`vbytes_inv`). **Full project `lake build` confirmed clean (exit 0, 0
errors) after this pass** — see `ExtensionLemmas.lean`'s own header comment
and per-lemma doc comments for exactly what changed and why, and
`claude-logging/verbatim_dialogue_log/bundle4/response_4.md` for the
session-level account. `Val_ok_store` and `funcinst_same` remain flagged
(not renamed-and-updated, since no matching declaration was found upstream
under any obvious name — see their in-file comments) rather than removed,
since nothing else in this project depends on them.

**All of this was a signature-only pass — no proofs were filled in this
turn** (every `sorry` from before is still a `sorry`, just against a
corrected signature where one was needed). The next natural step is Tier
B/C/D of `proof_prioritization.md` (as corrected by
`proof_prioritization_addendum.md`), starting with `HelperLemmas.lean`'s
corrected tier-0 cluster, or the newly-real Tier E2 (vector preservation
lemmas) / Tier I (`type_progress.v`) work described there.

## ⚠️ 2026-09-23 (later, same day) UPDATE — local Rocq checkout has been re-synced

## ⚠️ 2026-09-23 (later, same day) UPDATE — local Rocq checkout has been re-synced

The user manually merged `rocq-backend-proof` into this branch (commit
`b78d56eeb`, "merge with rocq-backend-proof, change in typefamilyremoval.ml").
**Verified** (by comparing against `gh api repos/Wasm-DSL/spectec/branches/rocq-backend-proof`
live, and checking for conflict markers / clean `git status`): the merge is
correct and complete — `spectec/test-rocq/theories/` is now byte-identical to
the live upstream HEAD, commit `a8b585cdb` ("Vector Instructions for
Preservation proven, and most well-formedness lemmas done."), which was
*also* confirmed still current (no further upstream commits) as of this
check. This is the same commit `bundle2/response_2.md` had flagged as the
live HEAD we were stale against (we were at `5b03ae067`, 2026-07-01).

**Full analysis of what changed and what it means for this project is in
`claude-logging/verbatim_dialogue_log/bundle3/updated_documents/resync_impact_report.md`
— read that before continuing any Phase-2/3 work.** Headline points (see
that doc for detail/evidence):

1. **The SIMD/vector gap in Preservation is CLOSED upstream.**
   `type_preservation_pure.v` and `type_preservation.v` both went from
   several `Admitted` lemmas (all SIMD-only, per our old digests) to **zero**
   `Admitted` in the new checkout — ~90 new vector-instruction lemmas were
   added and fully `Qed`-proved. Our `sorry`s in `TypePreservationPure.lean`/
   `TypePreservation.lean` justified as "faithfully mirrors a permanent Rocq
   gap" **no longer have that justification** — the Rocq side now has real
   proofs to port. This is the single biggest scope change from the resync.
2. **`extension_lemmas.v` was renamed wholesale.** Every
   `store_extension_*`/`*_extension_refl*`/`Val_ok_store`/`funcinst_same`
   name our `ExtensionLemmas.lean` was ported against no longer exists in
   the new checkout — renamed to `Extend_store_*`/`extend_*_refl*`
   (converging on the same naming convention as the auto-generated Lean
   `Extend_store`/`Extend_funcinst` etc. — possibly not a coincidence). Our
   Lean file's *declarations* (facts/proofs) are still fine, but its
   *names* are now stale relative to the "signatures must be directly from
   the Rocq proof" requirement — needs a rename pass.
3. **`type_progress.v` now exists** (4260 lines, was previously only a
   staging-directory draft at the old commit) — the Progress half of type
   safety, previously entirely out of scope for lack of a copy. Digested in
   `claude-logging/for-claude/digest_type_progress.md`. It depends on
   `wasm`, `helper_lemmas`, `helper_tactics`, `typing_lemmas`,
   `extension_lemmas`, `subtyping`, `axioms` — **not** on
   `type_preservation`/`type_preservation_pure` (Progress and Preservation
   are independent branches off the same shared infra, contrary to what
   `proof_prioritization.md` Tier H #37 guessed).
4. **`helper_lemmas.v` lost several lemmas** our `HelperLemmas.lean` already
   stubbed (`leadd`, `length_app_lt`, `add_false`, `concat_cancel_last_n`,
   `lt_irrefl`, the whole `Forall2_nth`/`_lookup`/`_list_update*` family,
   `Forall_nth'`, `repeat_size`, `ltsize`, `list_update_func_split*`,
   `list_update_map`, `lookup_list_update_func`) — these are gone upstream,
   so `proof_prioritization.md` Tier B item 2 ("tier-0 cluster", listed as
   free/easy wins) is pointing at several lemmas that no longer need
   porting at all. Don't waste time "faithfully" keeping dead stubs; see
   the impact report for the reconciled list.
5. **`axioms.v` grew from 2 to 9 axioms** (`nbytes_len`/`ibytes_len`
   themselves are byte-for-byte unchanged — our existing port of those two
   is still correct — but 7 new vector/inverse-bijection axioms were added:
   `nbytes_len'`, `ibytes_len'`, `ibytes_len''`, `vbytes_len'`,
   `truncz_quot`, `lanes_len`, `nbytes_inv`, `ibytes_inv`, `vbytes_inv`).
6. **One real gap remains in Preservation**: `extension_lemmas.v`'s
   `construct_meminsts_grow` (the `lim_old + v_n <= 2^16` memory-growth
   bound) is still `Admitted` upstream — same lemma flagged in
   `proof_prioritization.md` Tier F #27 — but new supporting machinery
   (`pagediv`, `update_holds_upto_le`/`_lt`, `holds_upto_*`) was added
   alongside it, suggesting the author was actively working toward closing
   it and got partway. Worth a fresh look with the new lemmas available.
7. **Progress's one remaining gap (`t_progress_be`, 5 `admit.` sites) is
   confirmed, in the author's own inline comments, to be exactly the
   `lane_`-union generator encoding bug** diagnosed via commit-history
   archaeology in `rocq_proof_intuition.md` — that diagnosis is now
   validated word-for-word against the actual source, not just inferred.

None of this required modifying anything outside `spectec/src/test-lean-claude/`
— the resync itself was the user's own manual merge; my role here was
read-only verification (`gh api`, `git diff`/`show` against two already-local
commit objects, `git status`) plus writing new analysis into this project's
own directory. Safety check re-run and clean, see
`claude-logging/safety-checks/`.

## Task recap

Translate `spectec/test-rocq/theories/` (a Rocq/Coq mechanized proof of WASM
2.0 type safety, on branch `rocq-backend-proof` of Wasm-DSL/spectec,
~27,000 lines across 9 `.v` files) into Lean 4, in this directory
(`spectec/src/test-lean-claude/`), lemma-for-lemma / definition-for-definition
where possible. Proofs may use different tactics than Rocq (Lean has proof
irrelevance so the *how* doesn't need to match) but **signatures must match
the Rocq statements**, up to the unavoidable renaming forced by the
auto-generated Lean backend's naming (see "Name mapping" TODO below).

There's also a partial Isabelle proof (branch `isabelle-mech-backend`,
backend output `isabelle_type_safety_proof/isabelle_reference_output_wasm2.thy`)
that can be consulted as secondary reference, but Rocq is the priority since
it's closer to Lean; final structure should mirror Rocq, not Isabelle.

**SAFETY RULE (hard constraint):** Never modify any file outside
`spectec/src/test-lean-claude/`. Run
`bash spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh`
(from repo root `/home/zhengyew/spectec`) periodically and after any batch of
edits; it writes a timestamped report into `claude-logging/safety-checks/`.
If you spawn any agent/subagent, you MUST tell it this rule explicitly and
have it either avoid writing files entirely (pure research agents should
just report findings in their final text answer, no file writes needed), or
(if it must scratch-write) only write under `claude-logging/`, and run the
same check script.

Separately, note the user has an INDEPENDENT parallel Claude effort auditing
the `*_is_wf` theorems in `wasm2.0.lean` (currently mostly `sorry`) to
determine which are actually true. That means **`wasm2.0.lean` may change
out from under you** — re-diff/re-check line numbers before trusting them if
significant time has passed. When you rely on an `*_is_wf` theorem that's
still `sorry`, log it in `is_wf_theorems.md` (see below) as true/false/unknown
(default: treat `sorry`'d ones as true-for-now unless trivial to prove
yourself).

## Directory / build setup (already done as of this writing — verify, don't blindly redo)

- `spectec/src/test-lean-claude/wasm2.0.lean` (12503 lines as of session 1) —
  **auto-generated** by the SpecTec Lean backend from
  `specification/wasm-2.0/*.spectec` (the EL spec). This is the Rocq
  `wasm.v` equivalent, i.e. it already defines all base syntax types,
  store/runtime types, typing judgments (`*_ok`), and reduction relations
  (`Step`, `Steps`, alloc/instantiate functions). **Do not hand-edit this
  file** — it's backend output, and belongs to the parallel `*_is_wf` effort.
- `spectec/src/test-lean-claude/ExtendedDeriveDecEq.lean` (738 lines) —
  library needed by `wasm2.0.lean`'s `derive_deceq`-style
  `deriving ... DecidableEq` clauses on the big mutual inductive AST. Also
  defines `Forall`, `Forall₂`, `Forall₃`, `Map`, `Map₂`, `Map₃`, `OMap`,
  `List.ap`, `Option.ap` — these are the Lean stand-ins for Coq's
  `List.Forall`/`Forall2`/`map` used pervasively in the Rocq proof's lemma
  statements. **Use these, don't redefine.** Note `Forall`/`Forall₂`/`Forall₃`
  here are defined via `∀ t ∈ xs.zip ys, P t.1 t.2` rather than as inductive
  props — this is NOT the same shape as Coq's `Forall2` (an inductive
  relation you can do induction/inversion on term-by-term). When porting a
  Rocq lemma proved by induction on a `Forall2` derivation, you may need to
  either (a) prove an induction principle for this `Forall₂` def first, or
  (b) just prove the ported lemma by whatever means work for this
  `zip`-based definition (list induction on the underlying lists + `simp`
  lemmas about `List.zip`/`List.mem`) since proof method is free to differ.
- `lakefile.lean`, `lean-toolchain` (`leanprover/lean4:v4.32.0`),
  `lake-manifest.json`, `.lake/` — set up by copying from the sibling
  `spectec/test-lean/` project (which already had mathlib v4.32.0
  fetched/built — copying avoided a fresh multi-GB mathlib fetch).
  `lake build` succeeded as of session 1 (exit 0, only warnings for
  pre-existing `sorry`s and a few unused-variable lints in `wasm2.0.lean`,
  not ours to fix). **When you add new `.lean` files to this project, add
  them to the `globs` list in `lakefile.lean`'s `lean_lib TestLeanClaude`
  stanza** (currently just `wasm2.0` and `ExtendedDeriveDecEq`) or they
  won't build. Re-run `lake build` from
  `/home/zhengyew/spectec/spectec/src/test-lean-claude` to check.
- `claude-logging/safety-checks/check.sh` — the periodic safety-check script.

## Key structural fact: most *definitions* already exist in wasm2.0.lean

Unlike a from-scratch port, the base types/judgments/relations that Rocq's
`wasm.v` hand-defines are **already auto-generated** in `wasm2.0.lean` from
the same underlying EL spec that produced `wasm.v` (Rocq) — both are backend
outputs of the same SpecTec pipeline, just different target languages. So:

- Rocq's `wasm.v` ≈ Lean's `wasm2.0.lean` (don't re-port this file's
  content as a new file; just use its defs).
- The **lemma files** (`helper_lemmas.v`, `subtyping.v`, `extension_lemmas.v`,
  `typing_lemmas.v`, `type_preservation_pure.v`, `type_preservation.v`,
  `helper_tactics.v`) are hand-written Rocq and have **no Lean counterpart
  yet** — these are what actually need porting, as new files in this
  directory. `helper_tactics.v` is pure Ltac (see digest below) — no
  signatures to port 1:1, since Lean tactics (`simp`, `omega`, `aesop`,
  custom `induction`/`cases` idioms) cover the same ground differently; skip
  direct porting of this file, just keep its *purpose* in mind (generalized
  induction helpers, list-equality destructuring, `Forall` inversion) when
  proving ported lemmas that need the same maneuvers.
- `axioms.v` (18 lines) has exactly 2 axioms about byte-encoding lengths:
  ```coq
  Axiom nbytes_len: forall v_nt v_c,
      length (nbytes_ v_nt v_c) =
      (Nat.divmod (the (res_size (valtype_numtype v_nt))) 7 0 7).1.
  Axiom ibytes_len: forall size v_n v_c,
      length (ibytes_ v_n (wrap__ size v_n v_c)) =
      (Nat.divmod v_n 7 0 7).1.
  ```
  Need Lean `axiom` (or `sorry`) equivalents; check if `wasm2.0.lean` already
  has `nbytes_`/`ibytes_` functions with `_is_wf`-style theorems that could
  subsume these instead of a bare axiom (search `wasm2.0.lean` for
  `nbytes_` / `ibytes_`). `Nat.divmod n 7 0 7).1` ≈ `n / 8` (stdlib's
  underlying impl of integer division) — i.e. these assert "the
  byte-encoding of an N-bit numeric/int value has `⌈N/8⌉`-ish length."

Confirmed by grep of `wasm2.0.lean` (line numbers as of session 1, may drift
if the file is regenerated by the parallel `*_is_wf` effort):
- `store` (8312), `moduleinst` (8187), `frame` (8343), `config` (8771),
  `context` (9312, with `append_context`/`++` instance and `wf_context`)
- Typing/validation judgments: `Instr_ok`, `Instrs_ok`, `Expr_ok`, `Func_ok`,
  `Module_ok`, `Type_ok`, `Blocktype_ok`, etc. (search `^inductive .*_ok`)
- Reduction: `Step_pure`, `Step_read`, `Step` (11106), `Steps` (11216),
  `Eval_expr`
- Allocation/instantiation: `fun_allocfunc` ... `fun_allocmodule`,
  `fun_instantiate`, `fun_invoke`
- **Store extension already defined**: `Extend_globalinst`, `Extend_meminst`,
  `Extend_tableinst`, `Extend_funcinst`, `Extend_datainst`, `Extend_eleminst`,
  `Extend_store` (12346–12484) — this is the Lean equivalent of whatever
  Rocq's `extension_lemmas.v` calls its extension relation(s) (its
  *definition* should already be in `wasm.v`/mirrored here; the .v file is
  presumably *lemmas about* this relation — transitivity, preservation of
  typing, etc). Confirm exact Rocq name via the digest and note the mapping.
- Runtime "OK" (store-relative typing) judgments distinct from static `_ok`:
  `Val_ok`, `Result_ok`, `Ref_ok`, `Frame_ok`, `Instr_ok2`, `Instrs_ok2`,
  `Expr_ok2`, `Store_ok`, `Config_ok`, `State_ok`, `Moduleinst_ok`, etc.
  (11830–12503ish). These are probably what Rocq calls things like
  `Config_typing` / `Frame_typing` / `Instr_typing` / `s_typing` — get exact
  Rocq names from the wasm.v digest, build a name-mapping table (TODO #2).

## Base AST/type names in wasm2.0.lean (for constructor-name mapping)

`numtype` (422), `reftype` (444), `valtype` (450), `resulttype := list
valtype` (520, NOTE: uses the custom `list` inductive-wrapper type from
`ExtendedDeriveDecEq.lean`-adjacent defs, not raw Lean `List` — double check
whether `resulttype` should actually unify with `List valtype` at use sites,
or whether there's an unwrap needed everywhere — see `proj_list_0`),
`functype` (614), `instr` (1677, the *static*/source instruction AST), `val`
(8126), `admininstr` (8376, the *administrative*/runtime instruction AST —
confirm what Rocq calls its runtime AST, e.g. `administrative_instruction`).

## IMPORTANT naming discovery: Rocq and Lean names mostly MATCH directly

Cross-checked against the `type_preservation.v` digest (see
`digest_type_preservation.md`): the Rocq capstone theorem is
`Theorem t_preservation: forall c1 ts c2, Step c1 c2 -> Config_ok c1 ts ->
Config_ok c2 ts.` — and `wasm2.0.lean` **already has** `inductive Config_ok :
config → resulttype → Prop` (line 12496) with essentially the same shape
(`Config_ok (config.mk_config (state.mk_state s f) admininstr_lst) (.mk_list
t_lst)`). Likewise Rocq's `Store_extension` ≈ Lean's `Extend_store` (line
12460, confirmed same field-by-field structure: per-array `Forall` over
`List.range` index bounds + pointwise `Extend_*inst` for GLOBALS/MEMS/
TABLES/FUNCS/DATAS/ELEMS + `wf_store` on both sides) — so the mapping isn't
identical in every name (`Store_extension`→`Extend_store`) but is close and
structurally 1:1. **Conclusion: don't assume a big scary renaming exercise —
check `wasm2.0.lean` by grepping the Rocq name or its likely Lean-cased
variant FIRST before assuming something needs porting from scratch.** Many
Rocq relation names (`Config_ok`, `Store_ok`, `Frame_ok`, `Module_instance_ok`-ish,
etc.) appear to come from the same EL-spec-driven naming convention on both
backends, just sometimes with `_ok`/`Extend_`/case differences. Build the
name-mapping table (TODO #2) by grep-checking each Rocq name against
`wasm2.0.lean` rather than guessing blind.

Also confirmed: `wasm2.0.lean` DOES already have `nbytes_`, `ibytes_`,
`inv_nbytes_`, `inv_ibytes_`, `wrap__` as `opaque` defs with matching
`*_is_wf` theorems (lines ~2593, 3626, 3654, 3712, 3740) — so `axioms.v`'s
two Rocq axioms (`nbytes_len`, `ibytes_len`) should be portable as new
`axiom`/`theorem ... := sorry` statements directly about these existing
`nbytes_`/`ibytes_` opaques, no need to redefine them.

## Digest received so far (session 1, before crash): `helper_lemmas.v` + `axioms.v`

A background research agent fully digested `helper_lemmas.v` (850 lines) and
`axioms.v` (18 lines) before the crash. Full digest text is long (~50
lemmas) — **not re-copied into this file to keep it scannable; if this
digest is not visible elsewhere by the time you read this, the fastest path
is to just re-read `helper_lemmas.v` directly (850 lines, cheap) rather than
regenerate the digest.** Key takeaways to remember without re-reading:

- `helper_lemmas.v` depends ONLY on `wasm.v` (no other proof files) — good
  candidate to port first/early.
- It has 1 `Fixpoint` (`In2`, line 248 — "pair occurs at same position in
  two lists"), 1 plain `Definition` (`prepend_label`, line 718 — pushes a
  new label onto a `context`'s `LABELS` field via the generic `@@`
  append-typeclass), and 45 `Lemma`s (no `Theorem`/`Corollary` anywhere).
- Many lemmas are **mathcomp/ssreflect artifacts with no 1:1 Lean need**:
  bridging stdlib `List.nth`/`List.In` vs mathcomp `seq.nth`/`\in`
  (`nth_is_same_as_seq_nth`, `in_same_as_In`, `Forall_size` partially) —
  these collapse away or become trivial/unnecessary in Lean, which has one
  canonical list library. Also `lt_irrefl` is stated as a **Boolean**
  equation (`x < x = false`, ssrnat-style) rather than Prop irreflexivity —
  just use `Nat.lt_irrefl` in Lean.
- Several **near-duplicate lemma families** exist purely because Rocq
  phrases the same fact with ssreflect-bool vs stdlib-Prop `<`, or
  left-vs-right symmetric versions: `Forall2_nth`/`_nth2`/`_lookup`/`_lookup2`
  (4 lemmas → likely 1-2 in Lean), `Forall2_list_update_func`/`_func2`/
  `(plain)`/`_2`/`_both` (5 lemmas, one general pattern), `split_append_1`/
  `_2`/`_last`/`_left_1` (4 small append-splitting variants). Fine to keep
  as separate named Lean lemmas for 1:1 fidelity, but consider proving one
  generic version and deriving the rest to save effort — this is an
  "obvious optimization" the user explicitly allowed.
- `concat_cancel_last_n` (monomorphic in `valtype`) and `size_eq_cat`
  (polymorphic `{A:Type}`) are essentially the **same fact proved two
  different ways** — recommend generalizing `concat_cancel_last_n` to
  `{A:Type}` in the Lean port and possibly deriving both from one lemma.
  Also: **check mathlib first** — `List.append_inj`/`append_right_cancel`
  family may already give this for free; same for `take_size_cat`/
  `drop_size_cat`/`sizecat_le1`/`sizecat_le2` (plain `List.take`/`List.drop`
  monotonicity/cancellation — mathlib likely has these already).
- `prepend_label`/`lookup_label_0`/`lookup_label_1` need the Rocq `context`
  record's generic `Append`/`@@` typeclass instance (defined in `wasm.v`,
  not this file) to port faithfully — check how `wasm2.0.lean`'s
  `append_context` (line 9327, confirmed above) behaves fieldwise and
  whether it matches Rocq's `_append_context` semantics before porting
  `lookup_label_1` (which is Coq's key "de Bruijn shift on LABELS lookup"
  lemma — semantically important for later typing-inversion lemmas about
  block/loop instructions).
- The `Append_Option` instance (`_append (Some b) c = Some b`, i.e.
  left-biased/first-Some-wins) — check if Lean's `Option.orElse` already
  matches this semantics before re-deriving `_append_option_none`/
  `_append_option_none_left`/`_append_some_left`.

## MAJOR MILESTONE (session 1, later in the same continuation): Phase 1 complete

All 6 Rocq lemma files now have a corresponding Lean file in this
directory, with every signature stated and every proof `sorry`, and the
**entire project builds cleanly** (`lake build` from this directory, exit
0, only expected `sorry`/pre-existing `wasm2.0.lean` warnings):

- `HelperLemmas.lean` ← `helper_lemmas.v` (+ the 2 `axioms.v` axioms at
  the bottom, as Lean `axiom`s referencing `wasm2.0.lean`'s existing
  `nbytes_`/`ibytes_`/`wrap__`/`size` opaques)
- `Subtyping.lean` ← `subtyping.v`
- `TypingLemmas.lean` ← `typing_lemmas.v` (⚠ `instr_of` and
  `ai_principal_typing` are signature-only stubs, body `:= sorry` — see
  the file's own TODO comment; their actual per-constructor case bodies
  still need transcribing, this is real remaining Phase-1/2 work)
- `TypePreservationPure.lean` ← `type_preservation_pure.v`
- `ExtensionLemmas.lean` ← `extension_lemmas.v`
- `TypePreservation.lean` ← `type_preservation.v` (the capstone file,
  including the top-level `t_preservation` theorem)

`helper_tactics.v` (pure Ltac) and `wasm1.v` (WASM 1.0, out of scope)
were deliberately NOT ported — see rationale in NOTES.md above.

**File organization decision**: everything lives in `namespace TLC` (short
for "TestLeanClaude") to avoid any accidental name collision with
`wasm2.0.lean`'s flat global namespace. Later files `open TLC` (or are
already inside it) to reference earlier files' lemmas/defs unqualified.
This differs from the prior sessions' un-namespaced style
(`typing_lemmas.lean`, `custom_notation.lean`) — a deliberate choice for
safety, not an oversight; flagging in case a future session wonders why.

**Naming resolutions made along the way** (see also the dedicated naming
notes inside `ExtensionLemmas.lean`'s header comment):
- Rocq's `Store_extension`/`Func_extension`/`Table_extension`/
  `Mem_extension`/`Global_extension`/`Elem_extension`/`Data_extension`
  (used throughout `extension_lemmas.v`/`type_preservation.v`, but never
  found declared under those names anywhere in the `.v` sources by direct
  grep) are treated as the digest-authors' paraphrase for the confirmed
  `Extend_store`/`Extend_funcinst`/`Extend_tableinst`/`Extend_meminst`/
  `Extend_globalinst`/`Extend_eleminst`/`Extend_datainst` — used
  throughout. If a future session finds this assumption wrong (e.g. by
  getting the Rocq project to actually build — session 1 could not get
  `dune build` to find `mathcomp` despite a local `_opam` switch existing;
  didn't chase further), revisit every lemma in `ExtensionLemmas.lean`.
- Rocq's `Module_instance_ok` → Lean's `Moduleinst_ok` (confirmed exact
  match by argument shape and by direct presence in `wasm2.0.lean`).
- Rocq's `Admin_instrs_ok`/`Thread_ok`/`Admin_instr_ok` (cited only in the
  `extension_lemmas.v` digest for `store_extension_ais`'s custom mutual
  induction scheme) do not exist under those names in either `wasm.v` or
  `wasm2.0.lean` — `store_extension_ais` is stated using `Instrs_ok2`
  instead, matching argument shapes.
- The Rocq type alias `mut` collides with Lean 4's `mut` keyword (used in
  `do`-block mutable-variable syntax) — the backend already handles this
  by escaping it as `«mut»` in `wasm2.0.lean` (e.g. `globaltype.mk_globaltype`'s
  first field); use `«mut»` (French-quote escaped) whenever the Rocq
  `mut` type is needed in a new signature.
- `Datainst_ok` takes 3 arguments (`store → datainst → datatype → Prop`),
  not 2 as its Rocq digest's prose summary suggested (`datatype` has only
  one inhabitant, `OK` — pass `datatype.OK` explicitly).
- `val`/`ref`/`admininstr` constructors do NOT repeat their type name as a
  prefix in Lean (Rocq: `val_REF_NULL`; Lean: `val.REF_NULL`), matching
  the general backend convention (dot-notation disambiguates, no need for
  the Rocq-style flat-namespace prefix) — this bit session 1 more than
  once when transcribing signatures from the Rocq digests; **always grep
  `wasm2.0.lean` for the actual constructor name before trusting a
  digest's Rocq-cased name verbatim.**

## TODO for next session (in priority order, UPDATED post-Phase-1)

0. **Phase 1 is done** (see milestone section above) — don't redo it. Start
   with Phase 2: fill in real proofs. Suggested order (easiest/highest-value
   first):
   a. `HelperLemmas.lean` — small, self-contained list/arithmetic facts,
      no dependencies on anything else in this project; good warm-up.
      Several should be one-liners via `omega`/`simp`/mathlib lemmas.
   b. Reuse already-complete proofs from prior sessions, per the
      in-file comments pointing to them: `Subtyping.lean`'s
      `instrtype_sub_refl`, `instrtype_sub_trans`, `instr_subtyping_weaken2`,
      `instr_subtyping_strengthen2`, `resulttype_sub_split`/`_sup`/`_sup'`
      (all cited as already proved 0-sorry in
      `spectec/test-lean/test-lean-claude/InstrtypeSub.lean` and
      `spectec/test-lean/typing_lemmas.lean`) — the OLD proofs were against
      slightly different helper defs (different variable names in
      `instrtype_sub`, different `context`/`resulttype` plumbing), so
      **don't copy-paste blindly**; re-derive using the old proof as a
      guide, checking each step still applies to this project's actual
      defs. Similarly `ExtensionLemmas.lean`'s `store_extension_refl` and
      the 6 `*_extension_refl`/`*_extension_refl0` lemmas are cited as
      already proved in `spectec/test-lean/test-lean-claude/Extension.lean`
      — same caveat.
   c. `TypingLemmas.lean`'s `instr_of` and `ai_principal_typing` need
      their actual bodies transcribed (currently `sorry`-stubbed
      placeholders even though their *type* is right) — this is
      substantial mechanical work (~50 and ~57 per-constructor cases
      respectively), see the digest file
      `digest_typing_lemmas_and_type_preservation_pure.md` for the
      complete Rocq case list. Needed before most `TypingLemmas.lean`
      lemma proofs can even be attempted (they case on these defs).
   d. Everything else: work file-by-file in Rocq dependency order
      (`HelperLemmas` → `Subtyping` → `TypingLemmas` → `TypePreservationPure`
      → `ExtensionLemmas` → `TypePreservation`), since later files'
      lemmas often reduce to earlier ones once unfolded.
   e. **Deliberately-kept gaps** (mirror Rocq, do not "fix"): in
      `TypePreservationPure.lean`, `Step_pure__return_frame_preserves` and
      `t_pure_preservation`'s SIMD cases; in `TypePreservation.lean`,
      `store_extension_reduce`, `t_read_preservation`, and
      `t_preservation_type`'s SIMD cases. These are `sorry` in Rocq too
      (`Admitted`) — leave as `sorry` unless the user asks otherwise.
   f. Run `bash spectec/src/test-lean-claude/claude-logging/safety-checks/check.sh`
      after every batch of edits, and re-run `lake build` from
      `spectec/src/test-lean-claude` after every file change (fast once
      mathlib's `.olean`s are cached — under a minute per file).

1. **Collect the remaining research digests.** Status as of this writing
   (session 1, post-crash-resume):
   - ✅ `helper_lemmas.v` + `axioms.v` — digested inline in this file (see
     section above), not yet saved as a separate file (low urgency, small).
   - ✅ `type_preservation.v` (the capstone file, 2802 lines) — SAVED to
     `claude-logging/for-claude/digest_type_preservation.md`. Read that
     file. Key takeaway: only 3 lemmas Admitted, gaps are 100% SIMD-only,
     everything else (including the top theorem `t_preservation`) is fully
     `Qed`-proved in Rocq.
   - ✅ Prior Lean attempts in `spectec/test-lean/` — SAVED to
     `claude-logging/for-claude/digest_prior_lean_attempts.md`. Read that
     file before writing ANY proof — it documents a false-theorem bug
     (`instrs_seq_typing_inversion`), several Lean-elaboration gotchas
     specific to this codebase, and (in `InstrtypeSub.lean`,
     `Extension.lean`, `Subtyping.lean`) several already-complete,
     zero-sorry Lean proofs of lemmas that map directly onto Rocq
     `subtyping.v`/`extension_lemmas.v` content — these can likely be
     reused near-verbatim once restated against the *current*
     `wasm2.0.lean` (their line-number citations were against the OLD
     `test-lean/wasm2.0.lean`, not ours — re-verify signatures via grep
     before reuse, per that file's own stated convention).
   - ⏳ STILL PENDING as of this writing: `wasm.v` (core file, 11133
     lines), `subtyping.v` + `extension_lemmas.v` (914+2044 lines),
     `typing_lemmas.v` + `type_preservation_pure.v` (2222+947 lines). 3
     background agents were commissioned for these, interrupted once by an
     environment crash, and resumed. If this session ends before they
     report back, either re-check for a pending SendMessage-resumable
     agent (their IDs, if still resolvable this session:
     `a09f454e056a3bcf1` for wasm.v, `a3e7713821c051efc` for
     subtyping/extension_lemmas, `a588bce17fa589162` for
     typing_lemmas/type_preservation_pure — these IDs are almost certainly
     NOT resolvable in a brand-new session, so don't rely on them past
     this session), or just re-read the `.v` files directly (budget is
     large, ~11k+3k+3k lines is very feasible turn-by-turn).
2. Build a **name-mapping table** Rocq-identifier → Lean-identifier for every
   base type, constructor, and judgment referenced by the lemma files
   (e.g. Rocq's extension relation name → `Extend_store` etc, Rocq's
   `Instr_typing`/`Config_typing`-ish names → `Instr_ok2`/`Config_ok` etc —
   confirm exact Rocq names from the wasm.v digest first). Write to
   `claude-logging/for-claude/NAME_MAPPING.md` once built, keep it updated.
3. Decide file organization for the new Lean files (one file per Rocq file
   is the natural default: `HelperLemmas.lean`, `Subtyping.lean`,
   `ExtensionLemmas.lean`, `TypingLemmas.lean`, `TypePreservationPure.lean`,
   `TypePreservation.lean`; skip a literal `HelperTactics.lean` port per
   above). Remember: do NOT imitate old attempts' file layout blindly (user
   explicitly said prior attempts' organization differs, e.g. no
   `Counterexample.lean` equivalent exists in Rocq) — but DO reuse old
   attempts' lemma statements/proofs where signatures genuinely match.
4. Phase 1 (per user instructions): sketch **every** lemma/definition
   signature from all 6 lemma files + axioms.v as Lean `def`/`theorem ...
   := sorry`, get it all to typecheck (`lake build`), before filling in any
   proofs. Add new files to `lakefile.lean`'s globs as you create them.
5. Phase 2: fill in "easier" supporting lemmas/proofs (helper_lemmas.v is
   the natural starting point — see digest above, depends only on wasm.v).
6. Phase 3 (if time remains): harder proofs (main type_preservation.v
   theorems — progress/preservation).
7. Track every `*_is_wf` theorem from `wasm2.0.lean` you end up relying on
   in `claude-logging/for-claude/is_wf_theorems.md` (true/false/unknown —
   unknown ones are currently `sorry` and should be treated as true unless
   trivial to prove yourself). Expect `wasm2.0.lean` to change under you
   (separate parallel effort) — re-check line numbers before trusting them.
8. Ask the user before making any interpretive judgment call that changes
   the shape of a lemma (e.g. "should I generalize this monomorphic Rocq
   lemma to be polymorphic since the proof clearly doesn't need the
   specific type" is fine to just do per "obvious optimizations" allowance,
   but bigger structural questions should be flagged).

## Prior attempts (reference only, don't imitate structure)

- `spectec/test-lean/typing_inversion.lean`, `spectec/test-lean/custom_notation.lean`
  — explicitly called out by the user as useful hand-written references that
  mimic the Rocq proof "almost lemma by lemma".
- `spectec/test-lean/test-lean-claude/` — a full previous session's attempt
  (Subtyping.lean, Extension.lean, StoreExtension.lean, InstrtypeSub.lean,
  SeqTypingInversion.lean, MemoryWriteAxioms.lean, CounterexampleCheck.lean,
  PROGRESS.md, logs/). Do NOT copy its file layout, but DO mine it for
  working Lean proofs/idioms — a digest was commissioned this session (see
  TODO #1).
