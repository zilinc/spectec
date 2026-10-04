import Mathlib.Tactic
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
-- TODO FROM USER: This looks like a Rocq-specific design choice that I overturned in my handwritten test-lean. Investigate further to see if this is necessary.
def lookup_total {α : Type} [Inhabited α] (l : List α) (n : Nat) : α := l[n]!

/-- Rocq: `Fixpoint list_update {A} (l : seq A) (n : nat) (y : A) : seq A`. Matches `List.set`. -/
abbrev list_update {α : Type} (l : List α) (n : Nat) (y : α) : List α := l.set n y

/-- Rocq: `Fixpoint list_update_func {A} (l : seq A) (n : nat) (y : A -> A) : seq A`.
    Matches `List.modify`. -/
abbrev list_update_func {α : Type} (l : List α) (n : Nat) (f : α → α) : List α := l.modify n f

/-- Not a Rocq port — new project-local infrastructure (bundle15, "Template A"
    per the `ExtensionLemmas.lean` sorry-triage report). The `[a]!`-indexed
    characterization of `List.modify` needed to prove every `*_extension`
    lemma's `holds_upto`-monotonicity goal: at the modified index, the
    updated value is `f` applied to the old one; elsewhere, unchanged. Built
    from Lean core's `getElem_modify_eq`/`getElem_modify_ne`
    (`Init/Data/List/Nat/Modify.lean`) via the standard `[a]!`-to-`[a]'h`
    bridge (`getElem!_pos`). -/
theorem getElem!_modify_eq_or_ne {α : Type} [Inhabited α] (l : List α) (idx a : Nat) (f : α → α)
    (ha : a < l.length) :
    (l.modify idx f)[a]! = if a = idx then f (l[a]!) else l[a]! := by
  have hmod : a < (l.modify idx f).length := by simp [ha]
  rw [getElem!_pos (l.modify idx f) a hmod]
  by_cases h : a = idx
  · subst h
    rw [List.getElem_modify_eq f a l (by simpa using hmod), getElem!_pos l a ha]
    simp
  · rw [List.getElem_modify_ne f l (Ne.symm h) hmod, getElem!_pos l a ha, if_neg h]

/-! ### "Template B": membership in a `zip` after a `List.modify`

    Not Rocq ports — new project-local infrastructure (bundle16). Rocq's
    `Forall2` is an *inductive* relation, so its `construct_*` proofs in
    `extension_lemmas.v` can induct on it directly and peel off the updated
    position. This codebase's generated `Forall₂` is the zip-based `def`
    `∀ p ∈ xs.zip ys, P p.1 p.2`, so the corresponding step is: "every pair in
    the zip of a modified list is either an original pair, or the image of the
    pair at the modified index". That is exactly what these three lemmas say,
    and they are what the whole `ExtensionLemmas.lean` `construct_*` family
    needs (the position-correlation bridge noted as missing in
    `proof_prioritization_v5.md`). Each also hands back membership of the
    *original* element, so the caller can feed it the `Forall`/`Forall₂`
    hypothesis it already has. -/

theorem mem_modify {α : Type} [Inhabited α] (f : α → α) (l : List α) :
    ∀ (idx : Nat) (x : α), x ∈ l.modify idx f → x ∈ l ∨ (x = f (l[idx]!) ∧ l[idx]! ∈ l) := by
  induction l with
  | nil => intro idx x hx; simp at hx
  | cons a l ih =>
    intro idx x hx
    cases idx with
    | zero =>
      simp only [List.modify_zero_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr ⟨by simp, by simp⟩
      · exact Or.inl (by simp [hx])
    | succ i =>
      simp only [List.modify_succ_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl (by simp)
      · rcases ih i x hx with h | ⟨h1, h2⟩
        · exact Or.inl (by simp [h])
        · exact Or.inr ⟨by simpa using h1, by simpa using List.mem_cons_of_mem a h2⟩

theorem mem_zip_modify {α β : Type} [Inhabited α] (f : α → α) (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ (l.modify idx f).zip ts →
      p ∈ l.zip ts ∨ (p.1 = f (l[idx]!) ∧ (l[idx]!, p.2) ∈ l.zip ts) := by
  induction l with
  | nil => intro ts idx p hp; simp at hp
  | cons a l ih =>
    intro ts idx p hp
    cases ts with
    | nil => simp at hp
    | cons b ts =>
      cases idx with
      | zero =>
        simp only [List.modify_zero_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨by simp, by simp⟩
        · exact Or.inl (by simp [hp])
      | succ i =>
        simp only [List.modify_succ_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (by simp)
        · rcases ih ts i p hp with h | ⟨h1, h2⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr ⟨by simpa using h1, by simpa using List.mem_cons_of_mem (a, b) h2⟩

theorem mem_zip_modify₂ {α β : Type} [Inhabited α] [Inhabited β] (f : α → α) (g : β → β)
    (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ (l.modify idx f).zip (ts.modify idx g) →
      p ∈ l.zip ts ∨
        (p.1 = f (l[idx]!) ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts) := by
  induction l with
  | nil => intro ts idx p hp; simp at hp
  | cons a l ih =>
    intro ts idx p hp
    cases ts with
    | nil => simp at hp
    | cons b ts =>
      cases idx with
      | zero =>
        simp only [List.modify_zero_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨by simp, by simp, by simp⟩
        · exact Or.inl (by simp [hp])
      | succ i =>
        simp only [List.modify_succ_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (by simp)
        · rcases ih ts i p hp with h | ⟨h1, h2, h3⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr ⟨by simpa using h1, by simpa using h2,
              by simpa using List.mem_cons_of_mem (a, b) h3⟩

/-- Rocq: `Fixpoint list_slice_update {A} (l : seq A) (i j : nat) (update_l : seq A) : seq A`
    (`wasm.v:66-74`), replacing (up to) the `n`-element slice `[i, i+n)` of `l` with
    `update_l` (where `n = |update_l|` at every real call site). **Redefined 2026-09-30
    (bundle13 signature audit)** to mirror Rocq's actual structural-recursion algorithm
    exactly, rather than the earlier `take`/`append`/`drop` formulation: that formulation is
    only length-preserving when `n = update_l.length` exactly, whereas Rocq's version
    recurses element-by-element down `l`, stops early and returns the untouched remainder as
    soon as either the index countdown or `update_l` itself runs out, and is therefore
    *unconditionally* length-preserving (`list_slice_update_length` below needs no side
    hypothesis, matching Rocq). Behaviorally identical to the old definition at every call
    site in this codebase (all of which supply `n = update_l.length`), so this is a pure
    representational correction, not a behavior change for anything already relying on it. -/
def list_slice_update {α : Type} (l : List α) (i n : Nat) (update_l : List α) : List α :=
  match l, update_l with
  | [], _ => []
  | l, [] => l
  | x :: l', y :: u_l' =>
    match i, n with
    | 0, 0 => x :: l'
    | _ + 1, 0 => x :: l'
    | 0, n + 1 => y :: list_slice_update l' 0 n u_l'
    | i + 1, n => x :: list_slice_update l' i n (y :: u_l')

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
theorem leadd (i n : Nat) : i ≤ i + n := by omega

/-- Rocq `helper_lemmas.v:25` `list_update_func_split`. -/
theorem list_update_func_split {α : Type} (x x' : List α) (idx : Nat) (f : α → α) :
    x' = list_update_func x idx f → (∃ y, (f y) ∈ x') ∨ x = x' := sorry

/-- Rocq `helper_lemmas.v:44` `list_update_func_split_strong`. -/
theorem list_update_func_split_strong {α : Type} (x x' : List α) (idx : Nat) (f : α → α) :
    x' = list_update_func x idx f → idx < x.length → ∃ y, (f y) ∈ x' := sorry

/-- Rocq `helper_lemmas.v:64` `length_app_lt`. -/
theorem length_app_lt {α : Type} (l l' l1' l2' : List α) :
    l.length = l1'.length → l' = l1' ++ l2' → l.length ≤ l'.length := by
  intro hlen heq
  subst heq
  rw [List.length_append]
  omega

-- `nth_is_same_as_seq_nth` (helper_lemmas.v:86) NOT PORTED: pure bridge between Coq's
-- stdlib `List.nth` and mathcomp's `seq.nth`; Lean has one list library, no counterpart needed.

/-- Rocq `helper_lemmas.v:94` `length_same_split_zero`. -/
theorem length_same_split_zero {α : Type} (l l2' : List α) :
    l.length = l.length + l2'.length → l2'.length = 0 := by
  intro h; omega

/-- Rocq `helper_lemmas.v:106` `length_app_both_nil`. -/
theorem length_app_both_nil {α : Type} (l l' l1' l2' : List α) :
    l.length = l'.length → l.length = l1'.length → l' = l1' ++ l2' → l2' = [] := by
  intro h1 h2 h3
  have hlen : l2'.length = 0 := by
    rw [h3, List.length_append] at h1
    omega
  cases l2' with
  | nil => rfl
  | cons a as => simp at hlen

/-- Rocq `helper_lemmas.v:122` `length_app_nil`. -/
theorem length_app_nil {α : Type} (l' l1' l2' : List α) :
    l'.length = l1'.length → l' = l1' ++ l2' → l2' = [] := by
  intro h1 h2
  have hlen : l2'.length = 0 := by
    rw [h2, List.length_append] at h1
    omega
  cases l2' with
  | nil => rfl
  | cons a as => simp at hlen

/-- Rocq `helper_lemmas.v:135` `Forall_nth'`. (Merged with the near-duplicate `Forall_size`,
    helper_lemmas.v:144, which only differs by a stdlib/mathcomp `List.nth`↔`nth` bridge not
    needed here — an "obvious optimization" collapsing two Rocq lemmas into one Lean lemma.) -/
theorem Forall_nth' {α : Type} [Inhabited α] (l : List α) (R : α → Prop) :
    Forall R l → ∀ i, i < l.length → R (lookup_total l i) := by
  intro h i hi
  simp only [lookup_total, getElem!_pos l i hi]
  exact h (l[i]'hi) (List.getElem_mem hi)

/-- Rocq `helper_lemmas.v:141` `Forall_size` (added bundle18). Same statement as
    `Forall_nth'` above, which is that lemma's name before the upstream `nat`→`N` rework. -/
theorem Forall_size {α : Type} [Inhabited α] (l : List α) (R : α → Prop) :
    Forall R l → ∀ i, i < l.length → R (lookup_total l i) :=
  Forall_nth' l R

/-- Membership of the same-index pair in a `zip`, given both bounds. The
    missing half of "Template B": `Forall₂`'s zip representation makes
    *pointwise* facts free but says nothing index-correlated until you can
    exhibit the pair. New project-local infrastructure (bundle16). -/
theorem mem_zip_getElem! {α β : Type} [Inhabited α] [Inhabited β] (l : List α) :
    ∀ (l' : List β) (i : Nat), i < l.length → i < l'.length → (l[i]!, l'[i]!) ∈ l.zip l' := by
  induction l with
  | nil => intro l' i hi _; simp at hi
  | cons a l ih =>
    intro l' i hi hi'
    cases l' with
    | nil => simp at hi'
    | cons b l' =>
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.zip_cons_cons, List.mem_cons]
        exact Or.inr (by simpa using ih l' j (by simpa using hi) (by simpa using hi'))

/-- Index-wise consequence of `Forall₂`, *with* the length hypothesis supplied
    explicitly. This is the usable form of `Forall2_nth` below: that lemma's
    Rocq statement *derives* `l.length = l'.length` from `Forall2`, which this
    codebase's zip-based `Forall₂` cannot do (see its own note), so callers
    pass the length in instead — every call site has it. -/
theorem Forall2_nth_of_length {α β : Type} [Inhabited α] [Inhabited β] {R : α → β → Prop}
    (l : List α) (l' : List β) (h : Forall₂ R l l') (hlen : l.length = l'.length)
    (i : Nat) (hi : i < l.length) : R (l[i]!) (l'[i]!) :=
  h _ (mem_zip_getElem! l l' i hi (hlen ▸ hi))

theorem mem_zip_modify_right {α β : Type} [Inhabited α] [Inhabited β] (g : β → β)
    (l : List α) :
    ∀ (ts : List β) (idx : Nat) (p : α × β), p ∈ l.zip (ts.modify idx g) →
      p ∈ l.zip ts ∨
        (p.1 = l[idx]! ∧ p.2 = g (ts[idx]!) ∧ (l[idx]!, ts[idx]!) ∈ l.zip ts) := by
  induction l with
  | nil => intro ts idx p hp; simp at hp
  | cons a l ih =>
    intro ts idx p hp
    cases ts with
    | nil => simp at hp
    | cons b ts =>
      cases idx with
      | zero =>
        simp only [List.modify_zero_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inr ⟨by simp, by simp, by simp⟩
        · exact Or.inl (by simp [hp])
      | succ i =>
        simp only [List.modify_succ_cons, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Or.inl (by simp)
        · rcases ih ts i p hp with h | ⟨h1, h2, h3⟩
          · exact Or.inl (by simp [h])
          · exact Or.inr ⟨by simpa using h1, by simpa using h2,
              by simpa using List.mem_cons_of_mem (a, b) h3⟩

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
    In2 x y l l' → x ∈ l ∧ y ∈ l' := by
  induction l generalizing l' with
  | nil => cases l' <;> (intro h; simp only [In2] at h)
  | cons a as ih =>
    cases l' with
    | nil => intro h; simp only [In2] at h
    | cons b bs =>
      intro h
      simp only [In2] at h
      rcases h with ⟨ha, hb⟩ | h
      · subst ha; subst hb; exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · obtain ⟨hx, hy⟩ := ih bs h
        exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

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
    (list_update l i x).length = l.length := List.length_set

/-- Rocq `helper_lemmas.v:492` `list_update_length_func`. -/
theorem list_update_length_func {α : Type} (l : List α) (f : α → α) (i : Nat) :
    (list_update_func l i f).length = l.length := List.length_modify f l i

/-- Rocq `helper_lemmas.v:504` `list_slice_update_length`. Unconditional (2026-09-30
    resync — see `list_slice_update`'s own comment): the old `take`/`append`/`drop`-based
    `def` needed `n = l'.length` as a side hypothesis for this to hold; the redefinition
    matching Rocq's actual structurally-recursive algorithm does not. -/
theorem list_slice_update_length {α : Type} (l l' : List α) (i n : Nat) :
    (list_slice_update l i n l').length = l.length := by
  induction l, i, n, l' using list_slice_update.induct
  all_goals (first | rfl | simp_all [list_slice_update])

/-- Not a Rocq port — new project-local infrastructure (bundle15, needed by
    `ExtensionLemmas.lean`'s `store_none_mem_extension`/`construct_meminsts`:
    a `memory.store`/`memory.init` writes a slice of fresh, already-known-
    well-formed bytes into an existing, already-well-formed byte buffer; the
    result is well-formed pointwise). Same proof technique as
    `list_slice_update_length` above (`induction ... using
    list_slice_update.induct`), since `Forall P` pointwise-respects the same
    "copy old / splice in new / stop early" recursion that length does. -/
theorem list_slice_update_forall {α : Type} {P : α → Prop} (l l' : List α) (i n : Nat)
    (hl : Forall P l) (hl' : Forall P l') : Forall P (list_slice_update l i n l') := by
  induction l, i, n, l' using list_slice_update.induct with
  | _ => first
    | (simp_all [list_slice_update, Forall])
    | (intro z hz
       simp only [list_slice_update, List.mem_cons] at hz
       rcases hz with rfl | hz'
       · simp_all [Forall, List.mem_cons]
       · simp_all [Forall, List.mem_cons])


/-- `splice` (the generated prelude helper behind `$with_mem`, added to `wasm2.0.lean` by the
    user's bundle18 backend change) agrees with Rocq's `list_slice_update` once the declared
    slice length is the payload's own length. Not a Rocq lemma: it bridges the Lean
    backend's rendering of `BYTES[i : j] = b*` to the Rocq backend's, so the Rocq-shaped
    statements (`store_none_mem_extension`, `construct_meminsts`, `mem_store_extension`, …)
    apply to the Lean `with_mem`. -/
theorem splice_eq_list_slice_update {α : Type} (l b : List α) (i : Nat) :
    splice l b i = list_slice_update l i b.length b := by
  induction l generalizing b i with
  | nil => simp [splice, list_slice_update]
  | cons x l' ih =>
    cases b with
    | nil => simp [splice, list_slice_update]
    | cons y u =>
      cases i with
      | zero =>
        have h := ih u 0
        simp only [splice] at h ⊢
        simp only [list_slice_update, List.length_cons]
        rw [← h]
        simp [Nat.succ_min_succ]
      | succ i0 =>
        have h := ih (y :: u) i0
        simp only [splice, List.length_cons] at h ⊢
        simp only [list_slice_update]
        rw [← h]
        simp [Nat.succ_min_succ]
        rw [Nat.add_right_comm]
        simp

/-- `splice` never changes the length of the list it writes into (Lean-only, bundle18). -/
theorem splice_length {α : Type} (l b : List α) (i : Nat) : (splice l b i).length = l.length := by
  rw [splice_eq_list_slice_update]
  exact list_slice_update_length l b i b.length

/-! ## Section 3 : list append/split lemmas (helper_lemmas.v:523-604) -/

/-- Rocq `helper_lemmas.v:523` `split_append_last`. -/
theorem split_append_last {α : Type} (z y : List α) (i j : α) :
    z ++ [i] = y ++ [j] → z = y ∧ i = j := by
  intro h
  have hrev : i :: z.reverse = j :: y.reverse := by
    simpa using congrArg List.reverse h
  injection hrev with hij hzy
  refine ⟨?_, hij⟩
  simpa using congrArg List.reverse hzy

/-- Rocq `helper_lemmas.v:539` `split_append_1`. -/
theorem split_append_1 {α : Type} (z : List α) (i j : α) :
    z ++ [i] = [j] → z = [] ∧ i = j := by
  intro h
  exact split_append_last z [] i j (by simpa using h)

/-- Rocq `helper_lemmas.v:550` `split_append_2`. -/
theorem split_append_2 {α : Type} (z : List α) (i j k : α) :
    z ++ [i] = [j, k] → z = [j] ∧ i = k := by
  intro h
  exact split_append_last z [j] i k (by simpa using h)

/-- Rocq `helper_lemmas.v:559` `split_append_left_1`. -/
theorem split_append_left_1 {α : Type} (z : List α) (i j : α) :
    [i] ++ z = [j] → z = [] ∧ i = j := by
  intro h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  exact ⟨h.2, h.1⟩

/-- Rocq `helper_lemmas.v:571` `empty_append`. -/
theorem empty_append {α : Type} (i j : List α) :
    [] = i ++ j → i = [] ∧ j = [] := by
  intro h
  cases i with
  | nil => exact ⟨rfl, by simpa using h.symm⟩
  | cons a as => simp at h

/-- Rocq `helper_lemmas.v:582` `lookup_app`. -/
theorem lookup_app {α : Type} [Inhabited α] (l l' : List α) (n : Nat) :
    n < l.length → lookup_total l n = lookup_total (l ++ l') n := by
  intro h
  simp [lookup_total, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

-- helper_lemmas.v:597-604 (`app_left_single_nil`, `app_right_nil`, `app_left_nil`) NOT PORTED:
-- the Rocq author's own comment flags these as ssreflect-rewriting-recognition workarounds
-- ("I'll probably remove them later") — trivial `List.append_nil`/`List.nil_append` facts,
-- already in Lean core, no counterpart needed.

/-! ## Section 5 : Option-append helper lemmas (helper_lemmas.v:606-624) -/

-- Rocq's `Append_Option` instance is "first-Some-wins": `_append (Some b) c = Some b`,
-- `_append None c = c`. This matches Lean's `Option.orElse` exactly (`a.orElse b` tries `a`
-- first, falls back to `b ()`). The three lemmas below restate the Rocq facts using `orElse`.

/-- Rocq `helper_lemmas.v:606` `_append_option_none`. -/
theorem option_orElse_none {α : Type} (c : Option α) : (c.orElse (fun _ => none)) = c := by
  cases c <;> simp

/-- Rocq `helper_lemmas.v:614` `_append_option_none_left`. -/
theorem option_none_orElse {α : Type} (c : Option α) : ((none : Option α).orElse (fun _ => c)) = c := by
  simp

/-- Rocq `helper_lemmas.v:622` `_append_some_left`. -/
theorem option_some_orElse {α : Type} (b : α) (c : Option α) :
    ((some b).orElse (fun _ => c)) = some b := by
  simp

/-! ## Section 6 : arithmetic helper lemmas (helper_lemmas.v:626-755) -/

/-- Rocq `helper_lemmas.v:626` `add_false`. -/
theorem add_false (n m : Nat) : n + (m + 1) ≠ n := by omega

/-- Rocq `helper_lemmas.v:742` `add_sub`. -/
theorem add_sub (a b : Nat) : a + b - b = a := by omega

/-- Rocq `helper_lemmas.v:749` `add_sub'`. -/
theorem add_sub' (a b : Nat) : a + b - a = b := by omega

/-! ## Section 7 : list-concatenation cancellation (helper_lemmas.v:637-683) -/

-- `concat_cancel_last_n` (helper_lemmas.v:637) moved below `size_eq_cat`, which it's now
-- derived from directly (both need `take_size_cat`/`drop_size_cat`, defined further down).

/-! ## Section 8 : context/prepend_label helpers (helper_lemmas.v:718-740) -/

/-- Rocq `helper_lemmas.v:718` `prepend_label`. Rocq builds a near-empty `context` with only
    `LABELS := [t]` and appends it (fieldwise) onto `v_C`; since Lean's `context.LABELS` is a
    plain `List resulttype` field, this collapses to a direct cons. -/
def prepend_label (C : context) (t : resulttype) : context := { C with LABELS := t :: C.LABELS }

/-- Rocq `helper_lemmas.v` `prepend_local` (added bundle18). Defined as Rocq's literal
    `{| …; context_LOCALS := t_lst; … |} @@ v_C`, which is also exactly the context shape
    the generated `Frame_ok` conclusion uses, so the two unfold to the same term. -/
def prepend_local (C : context) (t_lst : List valtype) : context :=
  ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := t_lst, LABELS := [], RETURN := none } : context) ++ C

/-- Rocq `helper_lemmas.v` `prepend_return` (added bundle18). Rocq's literal
    `{| …; context_RETURN := Some v_t |} @@ v_C`; the generated `Instr_ok2.Instr_ok2_frame`
    rule uses exactly this shape for the frame body's context. -/
def prepend_return (C : context) (t : resulttype) : context :=
  ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [], RETURN := some t } : context) ++ C

/-- Rocq `helper_lemmas.v` `append_local` (added bundle18): `v_C @@ {| …; context_LOCALS := t_lst; … |}`. -/
def append_local (C : context) (t_lst : List valtype) : context :=
  C ++ ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := t_lst, LABELS := [], RETURN := none } : context)

/-- Rocq `helper_lemmas.v` `append_label` (added bundle18): `v_C @@ {| …; LABELS := [t_lst]; … |}`. -/
def append_label (C : context) (t : resulttype) : context :=
  C ++ ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [t], RETURN := none } : context)

/-- Rocq `helper_lemmas.v` `append_return` (added bundle18): `v_C @@ {| …; context_RETURN := Some v_t |}`. -/
def append_return (C : context) (t : resulttype) : context :=
  C ++ ({
    TYPES := [], FUNCS := [], GLOBALS := [], TABLES := [], MEMS := [], ELEMS := [], DATAS := [],
    LOCALS := [], LABELS := [], RETURN := some t } : context)

/-- Rocq `helper_lemmas.v:721` `lookup_label_0`. -/
theorem lookup_label_0 (C : context) (t : resulttype) :
    lookup_total (prepend_label C t).LABELS 0 = t := by
  simp [lookup_total, prepend_label]

/-- Rocq `helper_lemmas.v:727` `lookup_label_1`. -/
theorem lookup_label_1 (C : context) (t : resulttype) (n : Nat) :
    lookup_total (prepend_label C t).LABELS (n + 1) = lookup_total C.LABELS n := by
  simp [lookup_total, prepend_label]

/-! ## Section 9 : more seq/arithmetic lemmas (helper_lemmas.v:757-850) -/

/-- Rocq `helper_lemmas.v:757` `sizecat_le1`. -/
theorem sizecat_le1 {α : Type} (l l' : List α) : l.length ≤ (l ++ l').length := by
  rw [List.length_append]; omega

/-- Rocq `helper_lemmas.v:765` `sizecat_le2`. -/
theorem sizecat_le2 {α : Type} (l l' : List α) : l'.length ≤ (l ++ l').length := by
  rw [List.length_append]; omega

-- `lt_irrefl` (helper_lemmas.v:773) NOT PORTED: Rocq states this as a *Boolean* equation
-- (ssrnat idiom, `x < x = false`); Lean's `Nat.lt_irrefl` (already in core) is the direct
-- Prop-valued equivalent, no restatement needed.

/-- Rocq `helper_lemmas.v:779` `drop_size_cat`. -/
theorem drop_size_cat {α : Type} (x y : List α) : (x ++ y).drop x.length = y := by
  induction x with
  | nil => simp
  | cons a as ih => simpa using ih

/-- Rocq `helper_lemmas.v:789` `take_size_cat`. -/
theorem take_size_cat {α : Type} (x y : List α) : (x ++ y).take x.length = x := by
  induction x with
  | nil => simp
  | cons a as ih => simpa using ih

/-- Rocq `helper_lemmas.v:800` `size_eq_cat`. Polymorphic twin of `concat_cancel_last_n`
    above (same conclusion, different Rocq proof technique via `take`/`drop`). -/
theorem size_eq_cat {α : Type} (l1 l2 l1' l2' : List α) :
    l1.length = l2.length → l1' ++ l1 = l2' ++ l2 → l1' = l2' ∧ l1 = l2 := by
  intro hlen heq
  have hlen' : l1'.length = l2'.length := by
    have hl := congrArg List.length heq
    simp only [List.length_append] at hl
    omega
  have h1 : l2' = l1' := by
    have h := take_size_cat l1' l1
    rw [heq, hlen'] at h
    rwa [take_size_cat] at h
  have h2 : l2 = l1 := by
    have h := drop_size_cat l1' l1
    rw [heq, hlen'] at h
    rwa [drop_size_cat] at h
  exact ⟨h1.symm, h2.symm⟩

/-- Rocq `helper_lemmas.v:637` `concat_cancel_last_n`. Rocq states this monomorphically for
    `list valtype`; generalized to `{α : Type}` here since the proof never uses anything
    `valtype`-specific (an "obvious optimization" per project policy). Semantically the same
    fact as `size_eq_cat` above — derived from it directly. -/
theorem concat_cancel_last_n {α : Type} (l1 l2 l3 l4 : List α) :
    l1 ++ l2 = l3 ++ l4 → l2.length = l4.length → l1 = l3 ∧ l2 = l4 := fun heq hlen =>
  size_eq_cat l2 l4 l1 l3 hlen heq

-- `size_cons` (helper_lemmas.v:833) NOT PORTED: trivial `List.length_cons`, already in Lean core.

/-- Rocq `helper_lemmas.v:837` `ltsize`. -/
theorem ltsize {α : Type} (x : Nat) (s s2 : List α) : x < s.length → x < (s ++ s2).length := by
  intro h
  have := sizecat_le1 s s2
  omega

-- `repeat_size` (helper_lemmas.v:849) NOT PORTED: trivial `List.length_replicate`, already in
-- Lean core.

/-! ## Axioms (from `axioms.v`). Originally 2 primitive axioms; the
    2026-09-24 resync (see
    `claude-logging/verbatim_dialogue_log/bundle3/updated_documents/resync_impact_report.md`)
    brought `axioms.v` up from 2 to 9 axioms — the original `nbytes_len`/
    `ibytes_len` are byte-for-byte unchanged upstream (still correct as
    ported below); the 7 new ones (all vector/SIMD or inverse-bijection
    facts, needed by the newly-closed-upstream vector preservation lemmas —
    see `NOTES.md`) are added below them. -/

/-- Rocq `axioms.v:13` `nbytes_len`. `nbytes_` and `size` (Rocq: `res_size`) already exist as
    backend `opaque`s in `wasm2.0.lean` (lines ~705, ~3967); this restates Rocq's axiom about
    their relationship. (2026-09-30 resync: `nbytes_`'s `wasm2.0.lean` signature is now
    `List byte` directly, matching Rocq's totality for `numtype` inputs — the earlier `Option`
    return type this axiom's `≠ none` guard worked around is gone from the regenerated file,
    so the guard and `Option.get!` wrapper on `nbytes_` are dropped here too; `size` itself is
    still `Option Nat`, so its own `Option.get!` is unchanged.) `(Nat.divmod n 7 0 7).1` in Rocq
    is stdlib's internal implementation of `n / 8`; restated directly as `/ 8` here. -/
axiom nbytes_len (v_nt : numtype) (v_c : num_) :
    (nbytes_ v_nt v_c).length = (Option.get! (size (valtype_numtype v_nt))) / 8

/-- Rocq `axioms.v:17` `ibytes_len`. Rocq's bound variable is itself named `size`, shadowing
    the unrelated `size` byte-length function used in `nbytes_len` above (a Rocq/spectec
    naming collision, not our doing) — renamed to `sz` here to avoid shadowing the `size` def
    from `wasm2.0.lean` (`size : valtype → Option Nat`, unrelated to this `sz : N`). -/
axiom ibytes_len (sz v_n : N) (v_c : iN) :
    (ibytes_ v_n (wrap__ sz v_n v_c)).length = v_n / 8

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `nbytes_len'`. A `Rat`-valued
    restatement of `nbytes_len` without the Nat-division floor — the two
    coincide since bit-widths are always multiples of 8, but the current
    Rocq source states both. (2026-09-30 resync: `≠ none`/`Option.get!` on
    `nbytes_` dropped — see `nbytes_len` above.) -/
axiom nbytes_len' (v_nt : numtype) (v_c : num_) :
    ((nbytes_ v_nt v_c).length : Rat) = (Option.get! (size (valtype_numtype v_nt)) : Rat) / 8

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `ibytes_len'`. `Rat`-valued
    restatement of `ibytes_len`. -/
axiom ibytes_len' (sz v_n : N) (v_c : iN) :
    ((ibytes_ v_n (wrap__ sz v_n v_c)).length : Rat) = (v_n : Rat) / 8

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `ibytes_len''`. Same fact as
    `ibytes_len'` but without the `wrap__` composition — a direct statement
    about `ibytes_` at any bit-width, independent of how the underlying
    integer value was produced. -/
axiom ibytes_len'' (v_n : N) (v_c : iN) :
    ((ibytes_ v_n v_c).length : Rat) = (v_n : Rat) / 8

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `vbytes_len'`. The vector/SIMD
    analogue of `nbytes_len'`/`ibytes_len'`. -/
axiom vbytes_len' (v_vt : vectype) (v_c : vec_) :
    ((vbytes_ v_vt v_c).length : Rat) = (Option.get! (size (valtype_vectype v_vt)) : Rat) / 8

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `truncz_quot`. `truncz`
    (truncation of a rational towards zero) is an uninterpreted `opaque` in
    `wasm2.0.lean` (line ~2384, `truncz : Rat → Int`); on a quotient of two
    integers — the only way the spec's integer operators ever use it — it
    coincides with Lean's `Int.tdiv` (truncating division, matching Coq's
    `Z.quot`). -/
axiom truncz_quot (a b : Int) (h : b ≠ 0) :
    truncz ((a : Rat) / (b : Rat)) = Int.tdiv a b

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `lanes_len`. `lanes_` is an
    uninterpreted `opaque` in `wasm2.0.lean` (line ~4062). By its definition
    in the specification it splits a 128-bit vector into exactly `dim`
    lanes. -/
axiom lanes_len (lt : lanetype) (v_N : N) (c : vec_) :
    (lanes_ (shape.X lt (dim.mk_dim v_N)) c).length = v_N

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `nbytes_inv`. `nbytes_`/
    `ibytes_` and their inverses `inv_nbytes_`/`inv_ibytes_` are
    uninterpreted `opaque`s in `wasm2.0.lean`. In the specification they are
    mutually inverse bijections between values and byte sequences of the
    right width. (2026-09-30 resync: `≠ none`/`Option.get!` on `nbytes_`
    dropped — see `nbytes_len` above.) -/
axiom nbytes_inv (nt : numtype) (bs : List byte)
    (hlen : (bs.length : Rat) = (Option.get! (size (valtype_numtype nt)) : Rat) / 8) :
    nbytes_ nt (inv_nbytes_ nt bs) = bs

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `ibytes_inv`. -/
axiom ibytes_inv (v_N : N) (bs : List byte) (hlen : (bs.length : Rat) = (v_N : Rat) / 8) :
    ibytes_ v_N (inv_ibytes_ v_N bs) = bs

/-- Rocq `axioms.v` (2026-09-24 resync: NEW) `vbytes_inv`. -/
axiom vbytes_inv (vt : vectype) (bs : List byte)
    (hlen : (bs.length : Rat) = (Option.get! (size (valtype_vectype vt)) : Rat) / 8) :
    vbytes_ vt (inv_vbytes_ vt bs) = bs

/-! ## `Forall₂` bridge to Mathlib's `List.Forall₂` (2026-09-30, bundle9)

Not a port of any Rocq lemma — new project-local infrastructure. This
codebase's generated `Forall₂` (`wasm2.0.lean:18`) is a zip-based `def`
(`∀ t ∈ xs₁.zip xs₂, P t.1 t.2`), unlike Rocq's `Forall2`, which is an
*inductive* relation that forces `xs₁.length = xs₂.length` as part of its
own shape. Concretely: with `xs₁ := [x]`, `xs₂ := []`, our `Forall₂ P xs₁
xs₂` reduces to `∀ p ∈ [], _`, which is vacuously `True` — a fact Rocq's
`Forall2 P [x] []` simply has no proof of at all (`nil`/`cons` mismatch is
uninhabited there). This gap is invisible as long as a Rocq `Forall2` proof
never needs the length fact, but several downstream lemmas do (see
`TypingLemmas.lean`'s `Vals_ok`/`Vals_ok_non_bot`, and the same class of
issue previously flagged for `funcinst_same` in
`ExtensionLemmas.lean`/bundle3's resync notes). Once an explicit length
hypothesis is supplied, this pair of lemmas converts freely between our
`Forall₂` and Mathlib's `List.Forall₂` (an inductive relation with a real
`nil`/`cons` induction principle), which is more ergonomic to do induction
on directly than the zip-based version. -/

/-- Given an explicit length hypothesis, this codebase's zip-based `Forall₂`
    coincides with Mathlib's inductive `List.Forall₂`. -/
theorem to_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (hlen : l1.length = l2.length) (h : Forall₂ R l1 l2) : List.Forall₂ R l1 l2 := by
  rw [List.forall₂_iff_zip]
  refine ⟨hlen, ?_⟩
  intro a b hab
  exact h (a, b) hab

/-- The reverse direction needs no extra hypothesis: Mathlib's `List.Forall₂`
    already forces equal length by construction (`List.Forall₂.length_eq`). -/
theorem from_mathlib_forall₂ {α β : Type} {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) : l1.length = l2.length ∧ Forall₂ R l1 l2 := by
  rw [List.forall₂_iff_zip] at h
  obtain ⟨hlen, hz⟩ := h
  refine ⟨hlen, ?_⟩
  intro p hp
  exact hz hp

end TLC
