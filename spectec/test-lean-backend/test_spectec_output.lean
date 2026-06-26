def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

abbrev N : Type := Nat

abbrev M : Type := Nat

abbrev n : Type := Nat

abbrev m : Type := Nat

def Ki : Nat :=
  1024

def min (nat : Nat) (nat_0 : Nat) : Nat :=
  match nat, nat_0 with
  | i, j => if i ≤ j then i else j

def opt_ (X : Type) (var_0 : List X) : Option (Option X) :=
  match X, var_0 with
  | X, [] => some none
  | X, [w] => some (some w)
  | X, x1 => TEMPORARY_PREM → none

def list_ (X : Type) (var_0 : Option X) : List X :=
  match X, var_0 with
  | X, none => []
  | X, some w => [w]
