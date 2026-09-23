import «wasm2.0»
import HelperLemmas
import Subtyping

/-!
# TypingLemmas

Lean port of `spectec/test-rocq/theories/typing_lemmas.v`. Full digest:
`claude-logging/for-claude/digest_typing_lemmas_and_type_preservation_pure.md`.

Architecture (mirrors Rocq exactly, do not decompose differently): ONE
big case-exhaustive `ai_principal_typing` Prop gives, for every
`admininstr` constructor, its principal (most specific) type; two
"soundness" theorems (`instr_typing_inversion`, `ai_typing_inversion`)
connect it to the real typing judgments `Instr_ok`/`Instr_ok2`. All later
per-instruction facts go through `ai_principal_typing`, not separate named
lemmas per instruction (unlike `type_preservation_pure.v`, which IS one
lemma per reduction rule).

Rocq's Ltac automation layer (`typing_lemmas.v:1220-2222`: `construct_ais_typing`,
`invert_ais_typing`, `join_subtyping_*`, `resolve_subtyping`, etc.) is
NOT ported 1:1 — Lean's `simp`/tactics cover the same dispatch differently;
only the *lemma* declarations that layer sits on top of are ported.

**MAJOR TODO (flagged, not resolved in this pass)**: `instr_of` and
`ai_principal_typing` are two large per-constructor case definitions
(~50 and ~57 cases respectively in Rocq). Their *signatures* are stated
correctly below but their *bodies* are `sorry` stubs for this first pass
— filling them in requires transcribing the full case list, which is
substantial mechanical work deferred to a later pass. See the digest file
above (section "`ai_principal_typing`") for the complete per-constructor
Rocq content to transcribe.

Phase 1 (this file, first pass): every signature stated, proofs/bodies
`sorry`.
-/

namespace TLC

/-! ## Context update helpers (typing_lemmas.v:76-172) -/

/-- Rocq `typing_lemmas.v:76` `upd_label`. -/
def upd_label (C : context) (labs : List resulttype) : context := { C with LABELS := labs }

/-- Rocq `typing_lemmas.v:79` `upd_local`. -/
def upd_local (C : context) (locs : List valtype) : context := { C with LOCALS := locs }

/-- Rocq `typing_lemmas.v:82` `upd_return`. -/
def upd_return (C : context) (ret : Option resulttype) : context := { C with RETURN := ret }

/-- Rocq `typing_lemmas.v:85` `upd_local_return`. -/
def upd_local_return (C : context) (loc : List valtype) (ret : Option resulttype) : context :=
  upd_return (upd_local C loc) ret

/-- Rocq `typing_lemmas.v:88` `upd_local_label_return`. -/
def upd_local_label_return (C : context) (loc : List valtype) (lab : List resulttype) (ret : Option resulttype) : context :=
  upd_return (upd_label (upd_local C loc) lab) ret

/-- Rocq `typing_lemmas.v:105` `upd_label_overwrite`. -/
theorem upd_label_overwrite (C : context) (l1 l2 : List resulttype) :
    upd_label (upd_label C l1) l2 = upd_label C l2 := sorry

/-- Rocq `typing_lemmas.v:111` `upd_label_is_same_as_append`. Rocq builds a near-empty
    context with `LABELS := lab ++ LABELS C` and generic-appends onto `v_C`; since Lean's
    `context.LABELS` is a plain list field, `upd_label` already IS that append directly, so
    this collapses to `rfl` and is stated only for provenance. -/
theorem upd_label_is_same_as_append (C : context) (lab : List resulttype) :
    upd_label C (lab ++ C.LABELS) = { C with LABELS := lab ++ C.LABELS } := sorry

/-- Rocq `typing_lemmas.v:118` `upd_local_is_same_as_append`. -/
theorem upd_local_is_same_as_append (C : context) (loc : List valtype) :
    upd_local C (loc ++ C.LOCALS) = { C with LOCALS := loc ++ C.LOCALS } := sorry

/-- Rocq `typing_lemmas.v:125` `upd_local_return_is_same_as_append`. -/
theorem upd_local_return_is_same_as_append (C : context) (loc : List valtype) (ret : Option resulttype) :
    upd_local_return C (loc ++ C.LOCALS) (ret.orElse (fun _ => C.RETURN)) =
      { C with LOCALS := loc ++ C.LOCALS, RETURN := ret.orElse (fun _ => C.RETURN) } := sorry

/-- Rocq `typing_lemmas.v:142` `upd_return_is_same_as_append`. -/
theorem upd_return_is_same_as_append (C : context) (ret : Option resulttype) :
    upd_return C (ret.orElse (fun _ => C.RETURN)) = { C with RETURN := ret.orElse (fun _ => C.RETURN) } := sorry

/-- Rocq `typing_lemmas.v:150` `upd_label_unchanged`. -/
theorem upd_label_unchanged (C : context) (lab : List resulttype) :
    C.LABELS = lab → upd_label C lab = C := sorry

/-- Rocq `typing_lemmas.v:158` `upd_label_unchanged_typing`. See also
    `spectec/test-rocq/upd_label_unchanged_typing_verified_walkthrough.md` for a detailed
    Rocq-side walkthrough of this specific lemma. -/
theorem upd_label_unchanged_typing (v_S : store) (v_C : context) (v_admininstrs : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C v_admininstrs v_ft ↔ Instrs_ok2 v_S (upd_label v_C v_C.LABELS) v_admininstrs v_ft := sorry

/-! ## `instr_of : admininstr → Option instr` (typing_lemmas.v:174-245) -/

/-- Rocq `typing_lemmas.v:174` `instr_of`. TODO(phase 2): body is a ~50-case match
    (every "plain" `admininstr` constructor ↦ `some` of the corresponding `instr`
    constructor; purely-administrative forms ↦ `none`) — stubbed for now, see the digest's
    `instr_of` section for the full Rocq case list to transcribe. -/
def instr_of (ai : admininstr) : Option instr := sorry

/-! ## Context/store well-formedness projections (typing_lemmas.v:247-278) -/

/-- Rocq `typing_lemmas.v:247` `instr_ok_context_wf`. -/
theorem instr_ok_context_wf (v_C : context) (v_instr : instr) (v_ft : functype) :
    Instr_ok v_C v_instr v_ft → wf_context v_C ∧ wf_instr v_instr := sorry

/-- Rocq `typing_lemmas.v:255` `ainstr_ok_context_store_wf`. -/
theorem ainstr_ok_context_store_wf (v_S : store) (v_C : context) (v_ainstr : admininstr) (v_ft : functype) :
    Instr_ok2 v_S v_C v_ainstr v_ft → wf_context v_C ∧ wf_store v_S ∧ wf_admininstr v_ainstr := sorry

/-- Rocq `typing_lemmas.v:263` `instrs_ok_context_wf`. -/
theorem instrs_ok_context_wf (v_C : context) (v_instrs : List instr) (v_ft : functype) :
    Instrs_ok v_C v_instrs v_ft → wf_context v_C ∧ Forall wf_instr v_instrs := sorry

/-- Rocq `typing_lemmas.v:271` `ainstrs_ok_context_store_wf`. -/
theorem ainstrs_ok_context_store_wf (v_S : store) (v_C : context) (v_ainstrs : List admininstr) (v_ft : functype) :
    Instrs_ok2 v_S v_C v_ainstrs v_ft → wf_context v_C ∧ wf_store v_S ∧ Forall wf_admininstr v_ainstrs := sorry

/-! ## Composition/empty-typing lemmas (typing_lemmas.v:280-424) -/

/-- Rocq `typing_lemmas.v:349` `instrs_empty_typing`. -/
theorem instrs_empty_typing (v_C : context) (t1s t2s : List valtype) :
    Instrs_ok v_C [] (mkFunctype t1s t2s) ↔ (wf_context v_C ∧ ResulttypeSub t1s t2s) := sorry

/-- Rocq `typing_lemmas.v:427` `ai_principal_typing` — **THE central definition of the
    file**. TODO(phase 2): body is a ~57-case match over `admininstr` giving each
    constructor's principal (most-specific) functype as an existential/equality Prop,
    mirroring each `Instr_ok`/`Instr_ok2` typing rule's premises verbatim. Stubbed for now
    — see the digest's `ai_principal_typing` section for the complete Rocq case list
    (NOP/UNREACHABLE/DROP/SELECT/BLOCK/LOOP/IFELSE/BR/BR_IF/BR_TABLE/CALL/CALL_INDIRECT/
    RETURN/CONST/UNOP/BINOP/TESTOP/RELOP/CVTOP/VCONST/REF_NULL/REF_FUNC/REF_IS_NULL/
    LOCAL_GET,SET,TEE/GLOBAL_GET,SET/TABLE_*/ELEM_DROP/LOAD/STORE/MEMORY_*/DATA_DROP/
    REF_FUNC_ADDR/REF_HOST_ADDR/CALL_ADDR/LABEL_/FRAME_/TRAP; SIMD ops fall to a vacuous
    `True` catchall, matching `type_preservation.v`'s SIMD-only gaps). -/
def ai_principal_typing (v_S : store) (v_C : context) (v_ai : admininstr) (v_ft : functype) : Prop := sorry

/-- Rocq `typing_lemmas.v:676` `instr_principal_typing`. Store is irrelevant for the
    surface (non-administrative) judgment; Rocq plugs in `default_val : store`, matching
    Lean's `default : store` (both types already `deriving Inhabited`). -/
def instr_principal_typing (v_C : context) (v_instr : instr) (v_ft : functype) : Prop :=
  ai_principal_typing default v_C (admininstr_instr v_instr) v_ft

/-! ## Master inversion theorems (typing_lemmas.v:679-850) -/

/-- Rocq `typing_lemmas.v:679` `instr_typing_inversion`. -/
theorem instr_typing_inversion (v_C : context) (v_instr : instr) (t1s t2s : List valtype) :
    Instr_ok v_C v_instr (mkFunctype t1s t2s) → instr_principal_typing v_C v_instr (mkFunctype t1s t2s) := sorry

/-- Rocq `typing_lemmas.v:720` `ai_typing_inversion` — **the master per-instruction
    inversion lemma**, administrative level, up to `<ti:` subtyping. Highest
    difficulty/longest proof in the "inversion" family (57-way case split in Rocq). -/
theorem ai_typing_inversion (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instr_ok2 v_S v_C v_ai (mkFunctype t1s t2s) →
    ∃ t1s' t2s', ai_principal_typing v_S v_C v_ai (mkFunctype t1s' t2s') ∧
      instrtype_sub (mkFunctype t1s' t2s') (mkFunctype t1s t2s) := sorry

/-! ## Single/seq/append composition — surface and administrative, both directions
    (typing_lemmas.v:852-1218) -/

/-- Rocq `typing_lemmas.v:852` `split_single_append`. Generic list helper. -/
theorem split_single_append {α : Type} (l l' : List α) (x : α) :
    [x] = l ++ l' → (l = [x] ∧ l' = []) ∨ (l = [] ∧ l' = [x]) := sorry

/-- Rocq `typing_lemmas.v:863` `instrs_single_typing_inversion`. -/
theorem instrs_single_typing_inversion (v_C : context) (v_instr : instr) (t1s t2s : List valtype) :
    Instrs_ok v_C [v_instr] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, Instr_ok v_C v_instr (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := sorry

/-- Rocq `typing_lemmas.v:925` `ais_single_typing_inversion'`. -/
theorem ais_single_typing_inversion' (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, Instr_ok2 v_S v_C v_ai (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := sorry

/-- Rocq `typing_lemmas.v:987` `ais_single_typing_inversion`. **The single most-used lemma
    downstream** in `type_preservation_pure.v` — turns "list-of-one administrative
    instruction is typed" directly into "its principal typing, up to subtyping". -/
theorem ais_single_typing_inversion (v_S : store) (v_C : context) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t2s) →
    ∃ t1s_sup t2s_sub, ai_principal_typing v_S v_C v_ai (mkFunctype t1s_sup t2s_sub) ∧
      instrtype_sub (mkFunctype t1s_sup t2s_sub) (mkFunctype t1s t2s) := sorry

/-- Rocq `typing_lemmas.v:1002` `ais_single_ref_typing_inversion`. -/
theorem ais_single_ref_typing_inversion (v_S : store) (v_C : context) (v_ref : ref) (ts1 ts2 : List valtype) :
    Instrs_ok2 v_S v_C [admininstr_ref v_ref] (mkFunctype ts1 ts2) →
    ∃ t : reftype, instrtype_sub (mkFunctype [] [valtype_reftype t]) (mkFunctype ts1 ts2) ∧ Ref_ok v_S v_ref t := sorry

/-- Rocq `typing_lemmas.v:1019` `val_ref_null_is_ref`. -/
theorem val_ref_null_is_ref (rt : reftype) : val.REF_NULL rt = val_ref (ref.REF_NULL rt) := sorry

/-- Rocq `typing_lemmas.v:1023` `ais_single_val_typing_inversion`. -/
theorem ais_single_val_typing_inversion (v_S : store) (v_C : context) (v_val : val) (ts1 ts2 : List valtype) :
    Instrs_ok2 v_S v_C [admininstr_val v_val] (mkFunctype ts1 ts2) →
    ∃ t, instrtype_sub (mkFunctype [] [t]) (mkFunctype ts1 ts2) ∧ Val_ok v_S v_val t := sorry

/-- Rocq `typing_lemmas.v:1056` `instrs_seq_typing_inversion`. **IMPORTANT**: this is the
    Rocq-faithful sequence-level statement (`Instrs_ok`, not singular `Instr_ok`, on the
    head) — a previous session's `typing_lemmas.lean` mis-stated the analogous lemma with
    singular `Instr_ok` on the head and it was proved FALSE (see
    `claude-logging/for-claude/digest_prior_lean_attempts.md` §3). Use exactly this shape. -/
theorem instrs_seq_typing_inversion (v_C : context) (v_instrs : List instr) (v_instr : instr) (t1s t2s : List valtype) :
    Instrs_ok v_C ([v_instr] ++ v_instrs) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok v_C v_instrs (mkFunctype t3s t2s) ∧ Instrs_ok v_C [v_instr] (mkFunctype t1s t3s) := sorry

/-- Rocq `typing_lemmas.v:1121` `ais_seq_typing_inversion`. Administrative analog; matches
    the shape already proved (0 sorry) in a previous session's `SeqTypingInversion.lean`
    (`instrs_seq_typing_inversion_fixed`) — see
    `claude-logging/for-claude/digest_prior_lean_attempts.md` §3 — worth porting that proof
    once definitions are confirmed aligned. -/
theorem ais_seq_typing_inversion (v_S : store) (v_C : context) (v_ais : List admininstr) (v_ai : admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C ([v_ai] ++ v_ais) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok2 v_S v_C v_ais (mkFunctype t3s t2s) ∧ Instrs_ok2 v_S v_C [v_ai] (mkFunctype t1s t3s) := sorry

/-- Rocq `typing_lemmas.v:1184` `ais_composition_typing`. -/
theorem ais_composition_typing (v_S : store) (v_C : context) (v_ais1 v_ais2 : List admininstr) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_ais1 ++ v_ais2) (mkFunctype t1s t2s) →
    ∃ t3s, Instrs_ok2 v_S v_C v_ais1 (mkFunctype t1s t3s) ∧ Instrs_ok2 v_S v_C v_ais2 (mkFunctype t3s t2s) := sorry

/-! ## More inversion/construction lemmas (typing_lemmas.v:1335-1594) -/

/-- Rocq `typing_lemmas.v:1335` `ai_val_principal_typing_inversion`. -/
theorem ai_val_principal_typing_inversion (v_S : store) (v_C : context) (v_val : val) (t1s t2s : List valtype) :
    ai_principal_typing v_S v_C (admininstr_val v_val) (mkFunctype t1s t2s) →
    ∃ t_lst, [] = t1s ∧ [t_lst] = t2s := sorry

/-- Rocq `typing_lemmas.v:1375` `injective_admininstr_instr`. -/
theorem injective_admininstr_instr : Function.Injective admininstr_instr := sorry

/-- Rocq `typing_lemmas.v:1382` `construct_instrs_typing_single`. -/
theorem construct_instrs_typing_single (v_C : context) (v_ai : instr) (ts1 ts2 : List valtype) :
    Instr_ok v_C v_ai (mkFunctype ts1 ts2) → Instrs_ok v_C [v_ai] (mkFunctype ts1 ts2) := sorry

/-- Rocq `typing_lemmas.v:1391` `construct_ais_typing_single`. -/
theorem construct_ais_typing_single (v_S : store) (v_C : context) (v_ai : admininstr) (ts1 ts2 : List valtype) :
    Instr_ok2 v_S v_C v_ai (mkFunctype ts1 ts2) → Instrs_ok2 v_S v_C [v_ai] (mkFunctype ts1 ts2) := sorry

/-- Rocq `typing_lemmas.v:1400` `construct_ais_subtyping`. -/
theorem construct_ais_subtyping (v_S : store) (v_C : context) (v_ais : List admininstr) (ts1 ts2 ts1' ts2' : List valtype) :
    Instrs_ok2 v_S v_C v_ais (mkFunctype ts1 ts2) →
    instrtype_sub (mkFunctype ts1 ts2) (mkFunctype ts1' ts2') →
    Instrs_ok2 v_S v_C v_ais (mkFunctype ts1' ts2') := sorry

/-- Rocq `typing_lemmas.v:1423` `injective_valtype_numtype`. -/
theorem injective_valtype_numtype : Function.Injective valtype_numtype := sorry

/-- Rocq `typing_lemmas.v:1442` `construct_ais_compose`. Heavily reused in
    `type_preservation_pure.v` to glue partial typing derivations back together. -/
theorem construct_ais_compose (v_S : store) (v_C : context) (v_ais1 v_ais2 : List admininstr) (t1s t2s t3s : List valtype) :
    Instrs_ok2 v_S v_C v_ais1 (mkFunctype t1s t2s) → Instrs_ok2 v_S v_C v_ais2 (mkFunctype t2s t3s) →
    Instrs_ok2 v_S v_C (v_ais1 ++ v_ais2) (mkFunctype t1s t3s) := sorry

/-- Rocq `typing_lemmas.v:1453` `construct_ai_const_I32`. -/
theorem construct_ai_const_I32 (v_S : store) (v_C : context) (v_num : num_) :
    wf_num_ numtype.I32 v_num → wf_context v_C → wf_store v_S →
    Instr_ok2 v_S v_C (admininstr.CONST numtype.I32 v_num) (mkFunctype [] [valtype.I32]) := sorry

/-- Rocq `typing_lemmas.v:1466` `construct_ai_ref`. -/
theorem construct_ai_ref (v_S : store) (v_C : context) (v_ref : ref) (t : reftype) :
    Ref_ok v_S v_ref t → wf_context v_C → wf_store v_S →
    Instr_ok2 v_S v_C (admininstr_ref v_ref) (mkFunctype [] [valtype_reftype t]) := sorry

/-- Rocq `typing_lemmas.v:1490` `adminval_val_ref`. -/
theorem adminval_val_ref (r : ref) : admininstr_val (val_ref r) = admininstr_ref r := sorry

/-- Rocq `typing_lemmas.v:1497` `construct_ai_val`. -/
theorem construct_ai_val (v_S : store) (v_C : context) (v_val : val) (t : valtype) :
    Val_ok v_S v_val t → wf_context v_C → wf_store v_S →
    Instr_ok2 v_S v_C (admininstr_val v_val) (mkFunctype [] [t]) := sorry

/-- Rocq `typing_lemmas.v:1523` `construct_ai_maybe`. -/
theorem construct_ai_maybe (v_S : store) (v_C : context) (ai : admininstr) (t1 t2 : List valtype) :
    instr_of ai ≠ none → wf_store v_S → Instr_ok v_C (Option.get! (instr_of ai)) (mkFunctype t1 t2) →
    Instr_ok2 v_S v_C ai (mkFunctype t1 t2) := sorry

/-- Rocq `typing_lemmas.v:1540` `construct_ais_vals'`. **Context-irrelevance for
    value-list typing** (value typing doesn't depend on local/label/return components of
    `C`) — crucial for label/frame-boundary-crossing lemmas in `type_preservation_pure.v`. -/
theorem construct_ais_vals' (v_S : store) (v_C v_C' : context) (v_vals : List val) (v_ft : functype) :
    Instrs_ok2 v_S v_C (v_vals.map admininstr_val) v_ft → wf_context v_C' →
    Instrs_ok2 v_S v_C' (v_vals.map admininstr_val) v_ft := sorry

/-- Rocq `typing_lemmas.v:1578` `construct_ais_trap`. TRAP typechecks at ANY functype. -/
theorem construct_ais_trap (v_S : store) (v_C : context) (v_ft : functype) :
    wf_context v_C → wf_store v_S → Instrs_ok2 v_S v_C [admininstr.TRAP] v_ft := sorry

/-! ## Val_ok / Vals_ok infrastructure (typing_lemmas.v:1596-1805) -/

/-- Rocq `typing_lemmas.v:1597` `value_extra`. -/
def value_extra (v_S : store) (v_val : val) : Prop :=
  match v_val with
  | .REF_FUNC_ADDR v_funcaddr => ∃ v_ft, Externaddr_ok v_S (.FUNC v_funcaddr) (.FUNC v_ft)
  | _ => True

/-- Rocq `typing_lemmas.v:1604` `Vals_ok`. NOTE argument order matches Rocq exactly:
    `Forall2 P v_ts v_vals` (types first, values second). -/
def Vals_ok (v_S : store) (v_vals : List val) (v_ts : List valtype) : Prop :=
  Forall₂ (fun t v => Val_ok v_S v t) v_ts v_vals

/-- Rocq `typing_lemmas.v:1607` `Val_ok_non_bot`. -/
theorem Val_ok_non_bot (v_S : store) (v_val : val) (t : valtype) :
    Val_ok v_S v_val t → t ≠ valtype.BOT := sorry

/-- Rocq `typing_lemmas.v:1619` `ais_vals_typing_inversion`. -/
theorem ais_vals_typing_inversion (v_S : store) (v_C : context) (v_vals : List val) (t1s t2s : List valtype) :
    Instrs_ok2 v_S v_C (v_vals.map admininstr_val) (mkFunctype t1s t2s) →
    ∃ v_ts : List valtype, instrtype_sub (mkFunctype [] v_ts) (mkFunctype t1s t2s) ∧ Vals_ok v_S v_vals v_ts := sorry

/-- Rocq `typing_lemmas.v:1679` `construct_ais_vals`. Longest/most intricate proof in the
    Rocq file (~125 lines, `last_ind` on `v_vals`/`ts` simultaneously). -/
theorem construct_ais_vals (v_S : store) (v_C : context) (v_vals : List val) (t1s t2s ts : List valtype) :
    wf_context v_C → wf_store v_S → instrtype_sub (mkFunctype [] ts) (mkFunctype t1s t2s) →
    Vals_ok v_S v_vals ts → Instrs_ok2 v_S v_C (v_vals.map admininstr_val) (mkFunctype t1s t2s) := sorry

/-! ## Subtyping-composition helpers (typing_lemmas.v:1807-1831) -/

/-- Rocq `typing_lemmas.v:1807` `resulttype_sub_single_inversion`. -/
theorem resulttype_sub_single_inversion (t1 t2 : valtype) :
    ResulttypeSub [t1] [t2] → Valtype_sub t1 t2 := sorry

/-- Rocq `typing_lemmas.v:1817` `construct_ais_instrtype_sub`. Same statement/proof as
    `construct_ais_subtyping` above (Rocq keeps both names, used interchangeably
    downstream) — kept as a separate lemma for provenance fidelity. -/
theorem construct_ais_instrtype_sub (v_S : store) (v_C : context) (v_ais : List admininstr) (t1s t2s t1s' t2s' : List valtype) :
    Instrs_ok2 v_S v_C v_ais (mkFunctype t1s t2s) →
    instrtype_sub (mkFunctype t1s t2s) (mkFunctype t1s' t2s') →
    Instrs_ok2 v_S v_C v_ais (mkFunctype t1s' t2s') := sorry

/-! ## `inst_match` — context-component invariance (typing_lemmas.v:1833-1922) -/

/-- Rocq `typing_lemmas.v:1833` `inst_match`. Deliberately excludes LOCALS/LABELS/RETURN:
    "same module-instance-derived components, differing local/label/return typing". -/
def inst_match (C C' : context) : Prop :=
  C.TYPES = C'.TYPES ∧ C.FUNCS = C'.FUNCS ∧ C.GLOBALS = C'.GLOBALS ∧ C.TABLES = C'.TABLES ∧
  C.MEMS = C'.MEMS ∧ C.ELEMS = C'.ELEMS ∧ C.DATAS = C'.DATAS

/-- Rocq `typing_lemmas.v:1842` `construct_inst_match_label`. -/
theorem construct_inst_match_label (C C' : context) (lab : List resulttype) :
    inst_match C C' → inst_match C (upd_label C' lab) := sorry

/-- Rocq `typing_lemmas.v:1852` `construct_inst_match_return`. -/
theorem construct_inst_match_return (C C' : context) (ret : Option resulttype) :
    inst_match C C' → inst_match C (upd_return C' ret) := sorry

/-- Rocq `typing_lemmas.v:1862` `construct_inst_match_local`. -/
theorem construct_inst_match_local (C C' : context) (loc : List valtype) :
    inst_match C C' → inst_match C (upd_local C' loc) := sorry

/-- Rocq `typing_lemmas.v:1872` `construct_inst_match_local_label_return`. -/
theorem construct_inst_match_local_label_return (C C' : context) (loc : List valtype) (lab : List resulttype) (ret : Option resulttype) :
    inst_match C C' → inst_match C (upd_local_label_return C' loc lab ret) := sorry

/-- Rocq `typing_lemmas.v:1882` `construct_inst_match_local_return`. -/
theorem construct_inst_match_local_return (C C' : context) (loc : List valtype) (ret : Option resulttype) :
    inst_match C C' → inst_match C (upd_local_return C' loc ret) := sorry

/-- Rocq `typing_lemmas.v:1892` `construct_inst_prepend_label`. -/
theorem construct_inst_prepend_label (C C' : context) (lab : resulttype) :
    inst_match C C' → inst_match C (prepend_label C' lab) := sorry

/-! ## Non-bottom propagation to lists (typing_lemmas.v:1927-1959) -/

/-- Rocq `typing_lemmas.v:1927` `Vals_ok_non_bot`. -/
theorem Vals_ok_non_bot (v_S : store) (v_val : List val) (v_ts : List valtype) :
    Forall₂ (fun t v => Val_ok v_S v t) v_ts v_val → Forall (fun t => t ≠ valtype.BOT) v_ts := sorry

/-- Rocq `typing_lemmas.v:1952` `Ref_ok_non_bot`. -/
theorem Ref_ok_non_bot (v_S : store) (v_val : ref) (t : reftype) :
    Ref_ok v_S v_val t → valtype_reftype t ≠ valtype.BOT := sorry

end TLC
