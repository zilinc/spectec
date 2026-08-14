def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


def count_ (X : Type) (var_0_lst : List X) : Nat :=
  match var_0_lst with
  | [] => 0
  | w :: w'_lst => 1 + (count_ X w'_lst)

def reverse_ (X : Type) (var_0_lst : List X) : List X :=
  match var_0_lst with
  | [] => []
  | w :: w'_lst => (reverse_ X w'_lst) ++ [w]

def elem_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => false
  | _ => List.contains var_0_lst X_0

def remove1_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : List X :=
  match var_0_lst with
  | [] => []
  | w_1 :: w'_lst => if
    X_0 == w_1
  then
    w'_lst
  else
    [w_1] ++ (remove1_ X X_0 w'_lst)

def subset_ (X : Type) [BEq X] (var_0_lst : List X) (var_1_lst : List X) : Bool :=
  match var_0_lst with
  | [] => true
  | w_1 :: w_lst => (elem_ X w_1 var_1_lst) && (subset_ X w_lst var_1_lst)

def equal_sets_ (X : Type) [BEq X] (var_0_lst : List X) (var_1_lst : List X) : Bool :=
  (subset_ X var_0_lst var_1_lst) && (subset_ X var_1_lst var_0_lst)

mutual
def even_len_ (X : Type) (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => true
  | w :: w'_lst => odd_len_ X w'_lst
def odd_len_ (X : Type) (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => false
  | w :: w'_lst => even_len_ X w'_lst

end

def has_dup_tl_ (X : Type) [BEq X] (X_0 : X) (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => false
  | w_1 :: w'_lst => if
    X_0 == w_1
  then
    true
  else
    has_dup_tl_ X X_0 w'_lst

def has_dup_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => false
  | w :: w'_lst => (has_dup_tl_ X w w'_lst) || (has_dup_ X w'_lst)

def lookup_ (K : Type) [BEq K] (V : Type) (var_0_lst : List K) (var_1_lst : List V) (K_0 : K) : Option V :=
  match var_0_lst, var_1_lst with
  | [], [] => none
  | k_1 :: k'_lst, v_1 :: v'_lst => if
    K_0 == k_1
  then
    some v_1
  else
    lookup_ K V k'_lst v'_lst K_0

