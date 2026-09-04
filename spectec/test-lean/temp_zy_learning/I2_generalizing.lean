import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON I2: GENERALIZING -- what `induction` does with hypotheses that
   mention the thing you're inducting on, and why it matters so much.

   Real world: same PearStack. -/

inductive PearStack where
  | empty
  | onePear (rest : PearStack)

def pearCount : PearStack → Nat
  | .empty => 0
  | .onePear rest => pearCount rest + 1

/- ─── Problem 1: inducting on something that's not "bare" ───
   Suppose your goal is about `onePear s` for a FIXED, already-specific
   `s` -- not about an arbitrary PearStack. Try to induct directly: -/
theorem stuck_example (s : PearStack) :
    pearCount (.onePear s) = pearCount s + 1 := by
  induction s with
  | empty => rfl
  | onePear rest ih =>
    -- `ih` here is about `pearCount (.onePear rest) = pearCount rest + 1`
    -- -- i.e. it's ALREADY the theorem's own conclusion, recursively, for
    -- `rest`. That's fine for THIS particular goal (which is actually
    -- provable directly by `rfl` in every branch, since `pearCount`'s
    -- own definition IS this equation) -- but notice `s` here doesn't
    -- interact with anything external. The next example is where the
    -- real problem shows up.
    rfl

/- ─── Problem 2: a hypothesis ELSEWHERE mentions the target ───
   This is the shape of the actual, real difficulty from the
   `instrs_seq_typing_inversion` saga earlier this session. Say you have
   an EXTRA fact tying some outer, fixed value to your induction target,
   and you want to induct on the target while KEEPING that connection
   available, case by case. -/

theorem with_extra_fact (fixed : PearStack) (n : Nat) (h : pearCount fixed = n) :
    n = 0 ∨ n > 0 := by
  /- If you `induction fixed` directly WITHOUT first dealing with `h`,
     Lean has a problem: `h`'s statement mentions `fixed`, the very thing
     about to be case-split. Lean's `induction` tactic actually handles
     this automatically for you -- it REVERTS any hypothesis depending on
     the target, does the induction, then re-introduces it per branch,
     freshly specialized. Watch: -/
  induction fixed with
  | empty =>
    -- Lean has automatically turned `h : pearCount fixed = n` into
    -- `h : pearCount PearStack.empty = n` for you, right here:
    trace_state
    left; simp [pearCount] at h; omega
  | onePear rest ih =>
    -- and here, `h : pearCount (.onePear rest) = n` -- STILL correctly
    -- connected, per-branch, without you writing a single `generalize`.
    trace_state
    right; simp [pearCount] at h; omega

/- So when DO you need `generalize` yourself? When the CONNECTION you
   care about isn't a plain hypothesis sitting in context already -- it's
   baked into the GOAL's own shape, or you deliberately want to name and
   inspect the equation Lean would otherwise handle silently. -/

theorem manual_generalize_needed (n : Nat) (fixed : PearStack) (hn : pearCount fixed = n) :
    pearCount fixed = n := by
  -- Trivial on its own, but let's do it the SAME way `induction using`
  -- constructs its ih's -- deliberately generalizing `fixed` and its
  -- functional relationship to `n` FIRST, then inducting, so you can see
  -- the mechanism explicitly rather than have `induction` do it for you.
  generalize eq1 : fixed = s at hn
  induction s with
  | empty =>
    trace_state  -- `eq1 : fixed = PearStack.empty` sits right there
    simp_all
  | onePear rest ih =>
    trace_state  -- `eq1 : fixed = PearStack.onePear rest`
    simp_all

/- ─── The REAL danger: generalizing something, then the CONCLUSION not
   depending on the recursion target at all ───
   This is the exact shape of the `instrs_seq_typing_inversion` problem.
   If your GOAL doesn't mention the target's own structure (only some
   OUTER fixed value tied to it via a `generalize`-produced equation),
   the `ih` you get in each branch stays tied to that OUTER value -- not
   genuinely general over the branch's own sub-piece. Watch this fail to
   be useful in the "cons"-like branch, on purpose: -/
theorem narrow_ih_demo (p : PearStack) :
    p = .onePear .empty → pearCount p = 1 := by
  intro hp
  -- generalize BOTH the hypothesis and the goal, so `p` is replaced
  -- everywhere (not just inside `hp`) -- otherwise the goal keeps
  -- talking about the un-generalized `p` and nothing lines up.
  generalize eq1 : p = s at hp ⊢
  induction s with
  | empty =>
    exact absurd hp.symm (by simp)
  | onePear rest ih =>
    -- `ih`'s TYPE mentions the OUTER `p`, not a freshly-quantified
    -- statement about `rest` in general. Print it:
    trace_state
    -- ih : p = PearStack.onePear rest → pearCount (PearStack.onePear rest) = 1
    -- Useful here ONLY because `p` still happens to be around and
    -- connected via `hp`/`eq1` -- but if `rest` were, say, TWO levels
    -- deep inside a bigger structure (as in the real `seq` case), this
    -- ih would be gated on `p` equaling something it almost never does.
    -- This is precisely I2's lesson, and precisely what Lesson I5 fixes
    -- by stating a properly GENERAL auxiliary goal before inducting.
    injection hp with rest_eq
    subst rest_eq
    rfl

/- ─── Under the hood, for every theorem above ───
   Every `induction ... with | ctor args => tac` block in this file
   compiles to a `PearStack.rec` (or the compiler's `brecOn`-based
   cousin) application: one argument per constructor, each built from
   the tactic block for that case, with the `ih` names you wrote slotted
   into exactly the ih POSITIONS R3 identified in the raw recursor type.
   `generalize ... at h ⊢` never changes THAT fact -- it only changes
   WHAT GOAL each of those tactic-block arguments has to prove, by
   altering what `h`/⊢ look like at the moment the recursor gets built.
   Confirm directly: -/
set_option pp.proofs true in
#print with_extra_fact
