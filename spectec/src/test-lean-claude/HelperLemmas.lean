import «wasm2.0»

/-!
# HelperLemmas

Lean port of `spectec/test-rocq/theories/helper_lemmas.v` (general
list/predicate/arithmetic helper lemmas used throughout the Rocq WASM 2.0
type safety proof), plus the two axioms from `axioms.v`.

Provenance: every declaration cites its Rocq source line number. Full
structural digest this was ported from:
`claude-logging/for-claude/NOTES.md` (inline digest section) and
`claude-logging/for-claude/digest_wasm_v.md`.

Per project policy: proof *method* is free to differ from Rocq's
ssreflect/mathcomp tactics (Lean has proof irrelevance), but *signatures*
mirror the Rocq statements. A handful of Rocq lemmas exist purely to
bridge Coq's two parallel list libraries (mathcomp `seq` vs stdlib
`List`) or to work around ssreflect rewriting quirks (the Rocq author's
own comment flags some of these as removable); those are noted inline but
not ported, since Lean has exactly one list type and no such need.

Phase 1 (this file, first pass): every signature stated, proofs `sorry`.
-/

namespace TLC

/-! ## Prelude helpers (from wasm.v's hand-written prelude, not backend-generated) -/

/-- Rocq: `lookup_total {T} {Inhabited T} (l : seq T) (n : nat) : T := seq.nth default_val l n`. -/
def lookup_total {α : Type} [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/-- Rocq: `Fixpoint list_update {A} (l : seq A) (n : nat) (y : A) : seq A`. Matches `List.set`. -/
abbrev list_update {α : Type} (l : List α) (n : Nat) (y : α) : List α := l.set n y

/-- Rocq: `Fixpoint list_update_func {A} (l : seq A) (n : nat) (y : A -> A) : seq A`.
    Matches `List.modify`. -/
abbrev list_update_func {α : Type} (l : List α) (n : Nat) (f : α → α) : List α := l.modify n f

/-- Rocq: `Fixpoint list_slice_update {A} (l : seq A) (i j : nat) (update_l : seq A) : seq A`,
    replacing the `n`-element slice `[i, i+n)` of `l` with `update_l` (where `n = |update_l|`).
    Rocq names the second index parameter `j`; we call it `n` to match the invariant
    `n = update_l.length` used at every call site (`list_slice_update_length` below). -/
def list_slice_update {α : Type} (l : List α) (i n : Nat) (update_l : List α) : List α :=
  (l.take i) ++ update_l ++ (l.drop (i + n))

/-- Rocq: `Fixpoint In2 {A B} (x : A) (y : B) (l : list A) (l' : list B) : Prop`,
    "the pair (x,y) occurs at the same position in l and l'". -/
def In2 {α β : Type} (x : α) (y : β) (l : List α) (l' : List β) : Prop :=
  match l, l' with
  | [], [] => False
  | [], _ :: _ => False
  | _ :: _, [] => False
  | a :: as', b :: bs' => (a = x ∧ b = y) ∨ In2 x y as' bs'

/-! ## Section 1 : general list/predicate helper lemmas (helper_lemmas.v:8-411ish) -/

/-- Rocq `helper_lemmas.v:16` `leadd`. -/
theorem leadd (i n : Nat) : i ≤ i + n := sorry

/-- Rocq `helper_lemmas.v:25` `list_update_func_split`. -/
theorem list_update_func_split {α : Type} (x x' : List α) (idx : Nat) (f : α → α) :
    x' = list_update_func x idx f → (∃ y, (f y) ∈ x') ∨ x = x' := sorry

/-- Rocq `helper_lemmas.v:44` `list_update_func_split_strong`. -/
theorem list_update_func_split_strong {α : Type} (x x' : List α) (idx : Nat) (f : α → α) :
    x' = list_update_func x idx f → idx < x.length → ∃ y, (f y) ∈ x' := sorry

/-- Rocq `helper_lemmas.v:64` `length_app_lt`. -/
theorem length_app_lt {α : Type} (l l' l1' l2' : List α) :
    l.length = l1'.length → l' = l1' ++ l2' → l.length ≤ l'.length := sorry

-- `nth_is_same_as_seq_nth` (helper_lemmas.v:86) NOT PORTED: pure bridge between Coq's
-- stdlib `List.nth` and mathcomp's `seq.nth`; Lean has one list library, no counterpart needed.

/-- Rocq `helper_lemmas.v:94` `length_same_split_zero`. -/
theorem length_same_split_zero {α : Type} (l l2' : List α) :
    l.length = l.length + l2'.length → l2'.length = 0 := sorry

/-- Rocq `helper_lemmas.v:106` `length_app_both_nil`. -/
theorem length_app_both_nil {α : Type} (l l' l1' l2' : List α) :
    l.length = l'.length → l.length = l1'.length → l' = l1' ++ l2' → l2' = [] := sorry

/-- Rocq `helper_lemmas.v:122` `length_app_nil`. -/
theorem length_app_nil {α : Type} (l' l1' l2' : List α) :
    l'.length = l1'.length → l' = l1' ++ l2' → l2' = [] := sorry

/-- Rocq `helper_lemmas.v:135` `Forall_nth'`. (Merged with the near-duplicate `Forall_size`,
    helper_lemmas.v:144, which only differs by a stdlib/mathcomp `List.nth`↔`nth` bridge not
    needed here — an "obvious optimization" collapsing two Rocq lemmas into one Lean lemma.) -/
theorem Forall_nth' {α : Type} [Inhabited α] (l : List α) (R : α → Prop) :
    Forall R l → ∀ i, i < l.length → R (lookup_total l i) := sorry

/-- Rocq `helper_lemmas.v:153` `Forall2_nth`. (Merged with `Forall2_nth2`, helper_lemmas.v:167,
    which only differs in whether the index bound is stated over `l` or `l'`; both hold since
    `Forall₂` forces equal length.) -/
theorem Forall2_nth {α β : Type} [Inhabited α] [Inhabited β] (l : List α) (l' : List β) (R : α → β → Prop) :
    Forall₂ R l l' → l.length = l'.length ∧ ∀ i, i < l.length → R (lookup_total l i) (lookup_total l' i) := sorry

/-- Rocq `helper_lemmas.v:181` `Forall2_lookup`. (Merged with `Forall2_lookup2`,
    helper_lemmas.v:194; same content as `Forall2_nth` phrased via `lookup_total`, kept as a
    separate named lemma for Rocq-source provenance fidelity even though the statement now
    coincides with `Forall2_nth` once the bool/Prop `<` distinction collapses in Lean.) -/
theorem Forall2_lookup {α β : Type} [Inhabited α] [Inhabited β] (l : List α) (l' : List β) (R : α → β → Prop) :
    Forall₂ R l l' → l.length = l'.length ∧ ∀ i, i < l.length → R (lookup_total l i) (lookup_total l' i) := sorry

-- `in_same_as_In` (helper_lemmas.v:207) NOT PORTED: bridges mathcomp's boolean `\in` with
-- stdlib's `List.In`; Lean has one membership notion (`∈`), no counterpart needed.

/-- Rocq `helper_lemmas.v:256` `lookup_list_update_func`. -/
theorem lookup_list_update_func {α : Type} [Inhabited α] (x : α) (f : α → α) (l : List α) (idx : Nat) :
    idx < l.length → x = lookup_total (list_update_func l idx f) idx → ∃ y, x = f y := sorry

/-- Rocq `helper_lemmas.v:270` `In2_split`. -/
theorem In2_split {α β : Type} (x : α) (y : β) (l : List α) (l' : List β) :
    In2 x y l l' → x ∈ l ∧ y ∈ l' := sorry

/-- Rocq `helper_lemmas.v:286` `Forall2_forall2`. -/
theorem Forall2_forall2 {α β : Type} (l : List α) (l' : List β) (R : α → β → Prop) :
    Forall₂ R l l' ↔ l.length = l'.length ∧ ∀ x y, In2 x y l l' → R x y := sorry

/-- Rocq `helper_lemmas.v:313` `Forall2_forall2weak`. -/
theorem Forall2_forall2weak {α β : Type} (l : List α) (l' : List β) (R : α → β → Prop) :
    Forall₂ R l l' → ∀ x, x ∈ l → ∃ y, R x y := sorry

/-- Rocq `helper_lemmas.v:325` `Forall2_forall2weak2`. -/
theorem Forall2_forall2weak2 {α β : Type} (l : List α) (l' : List β) (R : α → β → Prop) :
    Forall₂ R l l' → ∀ y, y ∈ l' → ∃ x, R x y := sorry

/-- Rocq `helper_lemmas.v:336` `Forall2_forall2weak3`. -/
theorem Forall2_forall2weak3 {α β : Type} (l : List α) (l' : List β) (R : α → β → Prop) :
    ((∀ x y, x ∈ l → R x y) ∧ l.length = l'.length) → Forall₂ R l l' := sorry

/-- Rocq `helper_lemmas.v:351` `Forall2_forall2weak4`. -/
theorem Forall2_forall2weak4 {α β : Type} (l : List α) (l' : List β) (R : α → β → Prop) :
    ((∀ x y, y ∈ l' → R x y) ∧ l.length = l'.length) → Forall₂ R l l' := sorry

/-! ## Section 2 : Forall2 interaction with list_update / list_update_func / lookup_total
    (helper_lemmas.v:366-521) -/

/-- Rocq `helper_lemmas.v:366` `Forall2_list_update_func`. -/
theorem Forall2_list_update_func {α β : Type} [Inhabited α] [Inhabited β]
    (l : List α) (l' : List β) (R : α → β → Prop) (i : Nat) (f : α → α) (x : α) (y : β) :
    Forall₂ R l l' → lookup_total l i = x → lookup_total l' i = y → R (f x) y →
    Forall₂ R (list_update_func l i f) l' := sorry

/-- Rocq `helper_lemmas.v:390` `Forall2_list_update_func2`. -/
theorem Forall2_list_update_func2 {α β : Type} [Inhabited α] [Inhabited β]
    (l : List α) (l' : List β) (R : α → β → Prop) (i : Nat) (f : β → β) (x : α) (y : β) :
    Forall₂ R l l' → lookup_total l i = x → lookup_total l' i = y → R x (f y) →
    Forall₂ R l (list_update_func l' i f) := sorry

/-- Rocq `helper_lemmas.v:414` `Forall2_list_update`. -/
theorem Forall2_list_update {α β : Type} [Inhabited α] [Inhabited β]
    (l : List α) (l' : List β) (R : α → β → Prop) (i : Nat) (x : α) (y : β) :
    Forall₂ R l l' → lookup_total l' i = y → R x y → Forall₂ R (list_update l i x) l' := sorry

/-- Rocq `helper_lemmas.v:436` `Forall2_list_update2`. -/
theorem Forall2_list_update2 {α β : Type} [Inhabited α] [Inhabited β]
    (l : List α) (l' : List β) (R : α → β → Prop) (i : Nat) (x : α) (y : β) :
    Forall₂ R l l' → lookup_total l i = x → R x y → Forall₂ R l (list_update l' i y) := sorry

/-- Rocq `helper_lemmas.v:458` `Forall2_list_update_both`. -/
theorem Forall2_list_update_both {α β : Type} [Inhabited α] [Inhabited β]
    (l : List α) (l' : List β) (R : α → β → Prop) (i : Nat) (x : α) (y : β) :
    Forall₂ R l l' → R x y → Forall₂ R (list_update l i x) (list_update l' i y) := sorry

/-- Rocq `helper_lemmas.v:479` `list_update_length`. -/
theorem list_update_length {α : Type} (l : List α) (i : Nat) (x : α) :
    (list_update l i x).length = l.length := sorry

/-- Rocq `helper_lemmas.v:492` `list_update_length_func`. -/
theorem list_update_length_func {α : Type} (l : List α) (f : α → α) (i : Nat) :
    (list_update_func l i f).length = l.length := sorry

/-- Rocq `helper_lemmas.v:504` `list_slice_update_length`. -/
theorem list_slice_update_length {α : Type} (l l' : List α) (i n : Nat) :
    n = l'.length → (list_slice_update l i n l').length = l.length := sorry

/-! ## Section 3 : list append/split lemmas (helper_lemmas.v:523-604) -/

/-- Rocq `helper_lemmas.v:523` `split_append_last`. -/
theorem split_append_last {α : Type} (z y : List α) (i j : α) :
    z ++ [i] = y ++ [j] → z = y ∧ i = j := sorry

/-- Rocq `helper_lemmas.v:539` `split_append_1`. -/
theorem split_append_1 {α : Type} (z : List α) (i j : α) :
    z ++ [i] = [j] → z = [] ∧ i = j := sorry

/-- Rocq `helper_lemmas.v:550` `split_append_2`. -/
theorem split_append_2 {α : Type} (z : List α) (i j k : α) :
    z ++ [i] = [j, k] → z = [j] ∧ i = k := sorry

/-- Rocq `helper_lemmas.v:559` `split_append_left_1`. -/
theorem split_append_left_1 {α : Type} (z : List α) (i j : α) :
    [i] ++ z = [j] → z = [] ∧ i = j := sorry

/-- Rocq `helper_lemmas.v:571` `empty_append`. -/
theorem empty_append {α : Type} (i j : List α) :
    [] = i ++ j → i = [] ∧ j = [] := sorry

/-- Rocq `helper_lemmas.v:582` `lookup_app`. -/
theorem lookup_app {α : Type} [Inhabited α] (l l' : List α) (n : Nat) :
    n < l.length → lookup_total l n = lookup_total (l ++ l') n := sorry

-- helper_lemmas.v:597-604 (`app_left_single_nil`, `app_right_nil`, `app_left_nil`) NOT PORTED:
-- the Rocq author's own comment flags these as ssreflect-rewriting-recognition workarounds
-- ("I'll probably remove them later") — trivial `List.append_nil`/`List.nil_append` facts,
-- already in Lean core, no counterpart needed.

/-! ## Section 5 : Option-append helper lemmas (helper_lemmas.v:606-624) -/

-- Rocq's `Append_Option` instance is "first-Some-wins": `_append (Some b) c = Some b`,
-- `_append None c = c`. This matches Lean's `Option.orElse` exactly (`a.orElse b` tries `a`
-- first, falls back to `b ()`). The three lemmas below restate the Rocq facts using `orElse`.

/-- Rocq `helper_lemmas.v:606` `_append_option_none`. -/
theorem option_orElse_none {α : Type} (c : Option α) : (c.orElse (fun _ => none)) = c := sorry

/-- Rocq `helper_lemmas.v:614` `_append_option_none_left`. -/
theorem option_none_orElse {α : Type} (c : Option α) : ((none : Option α).orElse (fun _ => c)) = c := sorry

/-- Rocq `helper_lemmas.v:622` `_append_some_left`. -/
theorem option_some_orElse {α : Type} (b : α) (c : Option α) :
    ((some b).orElse (fun _ => c)) = some b := sorry

/-! ## Section 6 : arithmetic helper lemmas (helper_lemmas.v:626-755) -/

/-- Rocq `helper_lemmas.v:626` `add_false`. -/
theorem add_false (n m : Nat) : n + (m + 1) ≠ n := sorry

/-- Rocq `helper_lemmas.v:742` `add_sub`. -/
theorem add_sub (a b : Nat) : a + b - b = a := sorry

/-- Rocq `helper_lemmas.v:749` `add_sub'`. -/
theorem add_sub' (a b : Nat) : a + b - a = b := sorry

/-! ## Section 7 : list-concatenation cancellation (helper_lemmas.v:637-683) -/

/-- Rocq `helper_lemmas.v:637` `concat_cancel_last_n`. Rocq states this monomorphically for
    `list valtype`; generalized to `{α : Type}` here since the proof never uses anything
    `valtype`-specific (an "obvious optimization" per project policy). Semantically the same
    fact as `size_eq_cat` below (subtyping.v's/extension_lemmas.v's polymorphic twin, proved
    via `take`/`drop` in Rocq rather than direct induction) — in Lean only one needs a real
    proof; the other can be derived from it. -/
theorem concat_cancel_last_n {α : Type} (l1 l2 l3 l4 : List α) :
    l1 ++ l2 = l3 ++ l4 → l2.length = l4.length → l1 = l3 ∧ l2 = l4 := sorry

/-! ## Section 8 : context/prepend_label helpers (helper_lemmas.v:718-740) -/

/-- Rocq `helper_lemmas.v:718` `prepend_label`. Rocq builds a near-empty `context` with only
    `LABELS := [t]` and appends it (fieldwise) onto `v_C`; since Lean's `context.LABELS` is a
    plain `List resulttype` field, this collapses to a direct cons. -/
def prepend_label (C : context) (t : resulttype) : context := { C with LABELS := t :: C.LABELS }

/-- Rocq `helper_lemmas.v:721` `lookup_label_0`. -/
theorem lookup_label_0 (C : context) (t : resulttype) :
    lookup_total (prepend_label C t).LABELS 0 = t := sorry

/-- Rocq `helper_lemmas.v:727` `lookup_label_1`. -/
theorem lookup_label_1 (C : context) (t : resulttype) (n : Nat) :
    lookup_total (prepend_label C t).LABELS (n + 1) = lookup_total C.LABELS n := sorry

/-! ## Section 9 : more seq/arithmetic lemmas (helper_lemmas.v:757-850) -/

/-- Rocq `helper_lemmas.v:757` `sizecat_le1`. -/
theorem sizecat_le1 {α : Type} (l l' : List α) : l.length ≤ (l ++ l').length := sorry

/-- Rocq `helper_lemmas.v:765` `sizecat_le2`. -/
theorem sizecat_le2 {α : Type} (l l' : List α) : l'.length ≤ (l ++ l').length := sorry

-- `lt_irrefl` (helper_lemmas.v:773) NOT PORTED: Rocq states this as a *Boolean* equation
-- (ssrnat idiom, `x < x = false`); Lean's `Nat.lt_irrefl` (already in core) is the direct
-- Prop-valued equivalent, no restatement needed.

/-- Rocq `helper_lemmas.v:779` `drop_size_cat`. -/
theorem drop_size_cat {α : Type} (x y : List α) : (x ++ y).drop x.length = y := sorry

/-- Rocq `helper_lemmas.v:789` `take_size_cat`. -/
theorem take_size_cat {α : Type} (x y : List α) : (x ++ y).take x.length = x := sorry

/-- Rocq `helper_lemmas.v:800` `size_eq_cat`. Polymorphic twin of `concat_cancel_last_n`
    above (same conclusion, different Rocq proof technique via `take`/`drop`). -/
theorem size_eq_cat {α : Type} (l1 l2 l1' l2' : List α) :
    l1.length = l2.length → l1' ++ l1 = l2' ++ l2 → l1' = l2' ∧ l1 = l2 := sorry

-- `size_cons` (helper_lemmas.v:833) NOT PORTED: trivial `List.length_cons`, already in Lean core.

/-- Rocq `helper_lemmas.v:837` `ltsize`. -/
theorem ltsize {α : Type} (x : Nat) (s s2 : List α) : x < s.length → x < (s ++ s2).length := sorry

-- `repeat_size` (helper_lemmas.v:849) NOT PORTED: trivial `List.length_replicate`, already in
-- Lean core.

/-! ## Axioms (from `axioms.v`, the Rocq development's only 2 primitive axioms) -/

/-- Rocq `axioms.v:13` `nbytes_len`. `nbytes_` and `size` (Rocq: `res_size`) already exist as
    backend `opaque`s in `wasm2.0.lean` (lines ~705, ~3654); this restates Rocq's axiom about
    their relationship, adding the `≠ none` guard that `nbytes_'s` `Option` return type (not
    present in Rocq, where it's total for `numtype` inputs) requires. `(Nat.divmod n 7 0 7).1`
    in Rocq is stdlib's internal implementation of `n / 8`; restated directly as `/ 8` here. -/
axiom nbytes_len (v_nt : numtype) (v_c : num_) (h : nbytes_ v_nt v_c ≠ none) :
    (Option.get! (nbytes_ v_nt v_c)).length = (Option.get! (size (valtype_numtype v_nt))) / 8

/-- Rocq `axioms.v:17` `ibytes_len`. Rocq's bound variable is itself named `size`, shadowing
    the unrelated `size` byte-length function used in `nbytes_len` above (a Rocq/spectec
    naming collision, not our doing) — renamed to `sz` here to avoid shadowing the `size` def
    from `wasm2.0.lean` (`size : valtype → Option Nat`, unrelated to this `sz : N`). -/
axiom ibytes_len (sz v_n : N) (v_c : iN) :
    (ibytes_ v_n (wrap__ sz v_n v_c)).length = v_n / 8

end TLC
