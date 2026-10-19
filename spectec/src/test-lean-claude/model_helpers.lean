/-! Hand-written helper lemmas for the `*_is_wf` proofs below (bundle19; not generated). -/

theorem iswf_Forall_nil {α : Type} (P : α → Prop) : Forall P [] := by
  intro x hx; cases hx

theorem iswf_Forall_cons {α : Type} {P : α → Prop} {x : α} {l : List α} :
    P x → Forall P l → Forall P (x :: l) := by
  intro hx hl y hy
  cases hy with
  | head => exact hx
  | tail _ h => exact hl y h

theorem iswf_Forall_append {α : Type} {P : α → Prop} {l1 l2 : List α} :
    Forall P l1 → Forall P l2 → Forall P (l1 ++ l2) := by
  intro h1 h2 x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

theorem iswf_Forall_mono {α : Type} {P Q : α → Prop} {l : List α} :
    Forall P l → (∀ x, P x → Q x) → Forall Q l := fun h hpq x hx => hpq x (h x hx)

theorem iswf_Forall_getElem! {α : Type} [Inhabited α] {P : α → Prop} {l : List α} (n : Nat) :
    Forall P l → P default → P l[n]! := by
  intro h hd
  by_cases hn : n < l.length
  · rw [getElem!_pos l n hn]; exact h _ (List.getElem_mem hn)
  · rw [getElem!_neg l n hn]; exact hd

theorem iswf_Forall_modify {α : Type} {P : α → Prop} (f : α → α) (hf : ∀ x, P x → P (f x)) :
    ∀ (l : List α) (n : Nat), Forall P l → Forall P (l.modify n f) := by
  intro l
  induction l with
  | nil => intro n _; rw [List.modify_nil]; exact iswf_Forall_nil P
  | cons a t ih =>
    intro n h
    have ha : P a := h a (by simp)
    have ht : Forall P t := fun y hy => h y (by simp [hy])
    cases n with
    | zero => rw [List.modify_zero_cons]; exact iswf_Forall_cons (hf a ha) ht
    | succ k => rw [List.modify_succ_cons]; exact iswf_Forall_cons ha (ih k ht)

theorem iswf_Forall_splice {α : Type} {P : α → Prop} (l u : List α) (i : Nat) :
    Forall P l → Forall P u → Forall P (splice l u i) := by
  intro hl hu
  unfold splice
  refine iswf_Forall_append (iswf_Forall_append ?_ ?_) ?_
  · exact fun x hx => hl x (List.mem_of_mem_take hx)
  · exact fun x hx => hu x (List.mem_of_mem_take hx)
  · exact fun x hx => hl x (List.mem_of_mem_drop hx)

theorem iswf_uN_zero (v_N : N) : wf_uN v_N (uN.mk_uN 0) :=
  wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem iswf_two_pow_cast (n : Nat) : ((2 : Int) ^ n) = ((2 ^ n : Nat) : Int) := by
  rw [Int.natCast_pow]; rfl

theorem iswf_uN_of_lt {v_N i : Nat} (h : i < 2 ^ v_N) : wf_uN v_N (uN.mk_uN i) := by
  refine wf_uN.uN_case_0 _ _ ⟨Nat.zero_le _, ?_⟩
  rw [iswf_two_pow_cast]
  omega

theorem iswf_uN_lt {v_N i : Nat} (h : wf_uN v_N (uN.mk_uN i)) : i < 2 ^ v_N := by
  cases h
  rename_i h
  have h2 := h.2
  rw [iswf_two_pow_cast] at h2
  have hp := Nat.two_pow_pos v_N
  omega

theorem iswf_uN_proj_lt {v_N : Nat} {x : uN} (h : wf_uN v_N x) : proj_uN_0 x < 2 ^ v_N := by
  cases x with | mk_uN i => exact iswf_uN_lt h

theorem iswf_toNat_sub_le (a b : Nat) : Int.toNat ((a : Int) - (b : Int)) ≤ a := by omega

theorem iswf_uN_toNat_emod (v_N : Nat) (x : Int) :
    wf_uN v_N (uN.mk_uN (Int.toNat (x % ((2 : Int) ^ v_N)))) := by
  apply iswf_uN_of_lt
  rw [iswf_two_pow_cast]
  have hp := Nat.two_pow_pos v_N
  have h1 := Int.emod_nonneg x (by omega : ((2 ^ v_N : Nat) : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos x (by omega : (0 : Int) < ((2 ^ v_N : Nat) : Int))
  omega

theorem iswf_Forall_map {α β : Type} {P : β → Prop} {Q : α → Prop} (f : α → β) (l : List α) :
    Forall Q l → (∀ x, Q x → P (f x)) → Forall P (Map f l) := by
  intro h hq y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact hq x (h x hx)
