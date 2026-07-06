inductive Color where
  | red   : Color
  | green : Color
  | blue  : Color

class Warmth (c : Color) where
  warm : Bool

instance : Warmth .red   where warm := true
instance : Warmth .green where warm := false
instance : Warmth .blue  where warm := false

def isWarm (c : Color) [Warmth c] : Bool :=
  match c with
  | .red => true               -- deconstructs; c = .red, inst still fine
  | _    => Warmth.warm c      -- catch-all; uses [Warmth c] from outer scope

#eval isWarm .red    -- true
#eval isWarm .green  -- false
#eval isWarm .blue   -- false


-- ===========================================================
-- Scenario 1: X : Type never deconstructed → REMOVE from match
-- ===========================================================

-- Uncomment to see the error (failed to synthesize BEq α✝):
-- def disjoint_broken (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
--   match X, var_0_lst with
--   | _, []          => true
--   | _, w :: w'_lst => (!List.contains w'_lst w) && disjoint_broken X w'_lst

def disjoint_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with          -- X removed
  | []          => true
  | w :: w'_lst => (!List.contains w'_lst w) && disjoint_ X w'_lst

#eval disjoint_ Nat [1, 2, 3]  -- true
#eval disjoint_ Nat [1, 2, 1]  -- false


-- ===========================================================
-- Scenario 2: var_0_lst deconstructed in at least one arm → KEEP in match
-- ===========================================================
-- var_0_lst above is deconstructed into [] and w :: w'_lst — so it stays.
-- Standalone example:

def sum_list (var_0_lst : List Nat) : Nat :=
  match var_0_lst with          -- deconstructed → kept
  | []      => 0
  | n :: t  => n + sum_list t

#eval sum_list [1, 2, 3, 4]    -- 10


-- ===========================================================
-- Scenario 3: pass-through arg, different names per clause → REMOVE + RENAME
-- ===========================================================
-- Two IL clauses name the first arg differently ('w_lst' vs 'w_lst2'),
-- but neither deconstructs it. The naive generated match has var_0 in it
-- with different pattern-bound names per arm.

-- Step A — original generated match (compiles, but var_0 should be dropped):
-- def concat_ (X : Type) (var_0 : List X) (var_1 : List (List X)) : List X :=
--   match var_0, var_1 with
--   | w_lst,  []            => w_lst
--   | w_lst2, w' :: w''_lst => concat_ X (w_lst2 ++ w') w''_lst

-- Step B — drop var_0 but forget to rename (broken):
-- def concat_ (X : Type) (var_0 : List X) (var_1 : List (List X)) : List X :=
--   match var_1 with
--   | []            => w_lst    -- ERROR: w_lst no longer in scope
--   | w' :: w''_lst => concat_ X (w_lst2 ++ w') w''_lst  -- ERROR: w_lst2 no longer in scope

-- Step C — drop var_0 AND rename w_lst → var_0, w_lst2 → var_0 (fixed):
def concat_ (X : Type) (var_0 : List X) (var_1 : List (List X)) : List X :=
  match var_1 with
  | []            => var_0                       -- w_lst  → var_0
  | w' :: w''_lst => concat_ X (var_0 ++ w') w''_lst  -- w_lst2 → var_0

#eval concat_ Nat [0] [[1, 2], [3]]  -- [0, 1, 2, 3]
