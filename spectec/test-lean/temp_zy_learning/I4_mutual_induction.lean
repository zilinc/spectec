import Mathlib.Tactic

/- ═══════════════════════════════════════════════════════════════════════
   LESSON I4: `induction ... using` on a MUTUAL recursor -- you must
   supply a value (even if trivial) for every OTHER motive in the group,
   and get one `case` per constructor across the WHOLE mutual group, not
   just the type you're inducting on.

   Real world: FruitBasket/GiftWrap from R5. -/

mutual
inductive FruitBasket where
  | empty
  | addFruit (kind : String) (rest : FruitBasket)
  | addGift  (gift : GiftWrap) (rest : FruitBasket)

inductive GiftWrap where
  | wrap (contents : FruitBasket) : GiftWrap
end

mutual
def fruitCount : FruitBasket → Nat
  | .empty => 0
  | .addFruit _ rest => fruitCount rest + 1
  | .addGift gift rest => giftCount gift + fruitCount rest

def giftCount : GiftWrap → Nat
  | .wrap contents => fruitCount contents
end

/- `induction b` on `b : FruitBasket` needs a value for BOTH motive_1
   (FruitBasket) and motive_2 (GiftWrap) -- even though you're only
   inducting on a FruitBasket, the recursor is shared, so Lean needs to
   know what to do with the GiftWrap side too. If you genuinely don't
   care about GiftWrap's own answer, stub it with something trivial
   (`True`, as in every earlier lesson) -- Lean auto-infers the REAL
   motive (motive_1, here) from your goal, same as always; only the
   OTHER one(s) need your help. -/
theorem count_nonneg (b : FruitBasket) : fruitCount b ≥ 0 := by
  induction b using FruitBasket.rec (motive_2 := fun _ => True) with
  | empty => exact Nat.zero_le _
  | addFruit kind rest ih => exact Nat.zero_le _
  | addGift gift rest giftIh ih => exact Nat.zero_le _
  | wrap contents ih => trivial
/- FOUR cases, not one-per-FruitBasket-constructor (three) -- the fourth,
   `wrap`, belongs to GiftWrap, the OTHER type in the mutual group. This
   is because it's ALL ONE shared recursor: every constructor of EVERY
   type in the `mutual` block gets a case, whether or not you personally
   care about that type's own motive. `motive_2`'s cases (`wrap`, here)
   just get whatever trivial content you supplied for `motive_2` as
   their goal. -/

/- ─── A genuinely mutual PROOF, both motives doing real work ─── -/
theorem count_matches (b : FruitBasket) (g : GiftWrap) :
    fruitCount b = fruitCount b ∧ giftCount g = giftCount g := by
  constructor
  · induction b using FruitBasket.rec (motive_2 := fun g => giftCount g = giftCount g) with
    | empty => rfl
    | addFruit kind rest ih => rfl
    | addGift gift rest giftIh restIh => rfl
    | wrap contents ih => rfl
  · induction g using GiftWrap.rec (motive_1 := fun b => fruitCount b = fruitCount b) with
    | empty => rfl
    | addFruit kind rest ih => rfl
    | addGift gift rest giftIh restIh => rfl
    | wrap contents ih => rfl
/- ─── Under the hood ───
   `count_nonneg` only inducted on `b : FruitBasket`, and never even
   named `motive_2`'s cases' logic explicitly beyond a `trivial` -- but
   the compiled term still had to supply values for the FULL, shared
   recursor, both motives at once: -/
set_option pp.proofs true in
#print count_nonneg
-- Look for `motive_2` in the printed type -- it's set to `fun _ => True`
-- (exactly what you passed), and the `wrap` case's own argument is a
-- function producing `trivial : True`, sitting right alongside the
-- three FruitBasket-motive arguments, all as siblings of ONE
-- `FruitBasket.rec` application.

/- Note we called TWO different recursors here (`FruitBasket.rec` and
   `GiftWrap.rec`) for the two halves of the proof -- and BOTH accepted
   the SAME four case names (`empty`, `addFruit`, `addGift`, `wrap`),
   because -- as R5 showed via `#check` on both -- they share the exact
   same minor premises, only their FINAL conclusion (which motive gets
   the bare `(t : _) → motive_k t` treatment) differs. Which one you
   invoke just tells Lean which type's value you're actually
   case-splitting; the case list is identical either way. -/
