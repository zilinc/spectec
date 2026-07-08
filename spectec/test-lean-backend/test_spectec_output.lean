def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by 
  first
     | exact Inhabited.default
     | intros ; assumption


def Forall {α₁ : Type} (P : α₁ → Prop) (xs₁ : List α₁) : Prop :=
  ∀ t_elem ∈ xs₁, P t_elem

def Forall₂ {α₁ α₂ : Type} (P : α₁ → α₂ → Prop) (xs₁ : List α₁) (xs₂ : List α₂) : Prop :=
  ∀ t ∈ xs₁ |>.zip xs₂, P (t.1) (t.2)

def Forall₃ {α₁ α₂ α₃ : Type} (P : α₁ → α₂ → α₃ → Prop) (xs₁ : List α₁) (xs₂ : List α₂) (xs₃ : List α₃) : Prop :=
  ∀ t ∈ xs₁ |>.zip xs₂ |>.zip xs₃, P (t.1.1) (t.1.2) (t.2)

def Map {α₁ β : Type} (f : α₁ → β) (xs₁ : List α₁) : List β :=
  xs₁ |>.map f

def Map₂ {α₁ α₂ β : Type} (f : α₁ → α₂ → β) (xs₁ : List α₁) (xs₂ : List α₂) : List β :=
  xs₁ |>.map f |>.ap xs₂

def OMap {α₁ β : Type} (f : α₁ → β) (xs₁ : Option α₁) : Option β :=
  xs₁ |>.map f

inductive r_MUT : Type where
  | MUT : r_MUT
deriving Inhabited, BEq

abbrev N : Type := Nat

abbrev M : Type := Nat

abbrev n : Type := Nat

abbrev m : Type := Nat

def Ki : Nat :=
  1024

def min (nat : Nat) (nat_0 : Nat) : Nat :=
  if nat ≤ nat_0 then nat else nat_0

inductive fun_sum : List Nat → Nat → Prop where
  | fun_sum_case_0 : fun_sum [] 0
  | fun_sum_case_1 (v_n : Nat) (n'_lst : List n) (var_0 : Nat) : 
    fun_sum n'_lst var_0 →
    fun_sum ([v_n] ++ n'_lst) (v_n + var_0)


def opt_ (X : Type) (var_0_lst : List X) : Option (Option X) :=
  match var_0_lst with
  | [] => some none
  | [w] => some (some w)
  | _ => none

def list_ (X : Type) (var_0_opt : Option X) : List X :=
  match var_0_opt with
  | none => []
  | some w => [w]

def concat_ (X : Type) (var_0_lst_lst : List (List X)) : List X :=
  match var_0_lst_lst with
  | [] => []
  | w_lst :: w'_lst_lst => w_lst ++ (concat_ X w'_lst_lst)

opaque inv_concat_ (X : Type) (var_0_lst : List X) : List (List X) := by 
  first
     | exact Inhabited.default
     | intros ; assumption


def setproduct2_ (X : Type) (X_0 : X) (var_0_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst_lst with
  | [] => []
  | w'_lst :: w_lst_lst => [[X_0] ++ w'_lst] ++ (setproduct2_ X X_0 w_lst_lst)

def setproduct1_ (X : Type) (var_0_lst : List X) (var_1_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst with
  | [] => []
  | w_1 :: w'_lst => (setproduct2_ X w_1 var_1_lst_lst) ++ (setproduct1_ X w'_lst var_1_lst_lst)

def setproduct_ (X : Type) (var_0_lst_lst : List (List X)) : List (List X) :=
  match var_0_lst_lst with
  | [] => [[]]
  | w_1_lst :: w_lst_lst => setproduct1_ X w_1_lst (setproduct_ X w_lst_lst)

def disjoint_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => true
  | w :: w'_lst => (! (List.contains w'_lst w)) && (disjoint_ X w'_lst)

inductive list (X : Type) : Type where
  | mk_list (X_lst : List X) : list X
deriving Inhabited, BEq

inductive bit : Type where
  | mk_bit (i : Nat) : bit
deriving Inhabited, BEq

inductive wf_bit : bit → Prop where
  | bit_case_0 (i : Nat) : 
    (i == 0) || (i == 1) →
    wf_bit (bit.mk_bit i)


inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq

inductive wf_byte : byte → Prop where
  | byte_case_0 (i : Nat) : 
    (i ≥ 0) && (i ≤ 255) →
    wf_byte (byte.mk_byte i)


inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq

def proj_uN_0 (x : uN) : Nat :=
  match x with
  | uN.mk_uN v_num_0 => (v_num_0)

inductive wf_uN : N → uN → Prop where
  | uN_case_0 (v_N : N) (i : Nat) : 
    (i ≥ 0) && (i ≤ (Int.toNat (((2 ^ v_N) : Int) - (1 : Int)))) →
    wf_uN v_N (uN.mk_uN i)


inductive sN : Type where
  | mk_sN (i : Int) : sN
deriving Inhabited, BEq

inductive wf_sN : N → sN → Prop where
  | sN_case_0 (v_N : N) (i : Int) : 
    (((i ≥ (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int))) && (i ≤ (- (1 : Int)))) || (i == (0 : Int))) || ((i ≥ (1 : Int)) && (i ≤ (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)))) →
    wf_sN v_N (sN.mk_sN i)


abbrev iN : Type := uN

abbrev u8 : Type := uN

abbrev u16 : Type := uN

abbrev u31 : Type := uN

abbrev u32 : Type := uN

abbrev u64 : Type := uN

abbrev s33 : Type := sN

abbrev i32 : Type := iN

abbrev i64 : Type := iN

abbrev i128 : Type := iN

def signif (v_N : N) : Option Nat :=
  match v_N with
  | 32 => some 23
  | 64 => some 52
  | _ => none

def expon (v_N : N) : Option Nat :=
  match v_N with
  | 32 => some 8
  | 64 => some 11
  | _ => none

def fun_M (v_N : N) : Nat :=
  Option.get! (signif v_N)

def E (v_N : N) : Nat :=
  Option.get! (expon v_N)

abbrev exp : Type := Int

inductive fNmag : Type where
  | NORM (v_m : m) (v_exp : exp) : fNmag
  | SUBNORM (v_m : m) : fNmag
  | INF : fNmag
  | NAN (v_m : m) : fNmag
deriving Inhabited, BEq

inductive wf_fNmag : N → fNmag → Prop where
  | fNmag_case_0 (v_N : N) (v_m : m) (v_exp : exp) : 
    (v_m < (2 ^ (fun_M v_N))) && ((((2 : Int) - ((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int)) ≤ v_exp) && (v_exp ≤ (((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int) - (1 : Int)))) →
    wf_fNmag v_N (fNmag.NORM v_m v_exp)
  | fNmag_case_1 (v_N : N) (v_exp : exp) (v_m : m) : 
    (v_m < (2 ^ (fun_M v_N))) && (((2 : Int) - ((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int)) == v_exp) →
    wf_fNmag v_N (fNmag.SUBNORM v_m)
  | fNmag_case_2 (v_N : N) : wf_fNmag v_N fNmag.INF
  | fNmag_case_3 (v_N : N) (v_m : m) : 
    (1 ≤ v_m) && (v_m < (2 ^ (fun_M v_N))) →
    wf_fNmag v_N (fNmag.NAN v_m)


inductive fN : Type where
  | POS (_ : fNmag) : fN
  | NEG (_ : fNmag) : fN
deriving Inhabited, BEq

inductive wf_fN : N → fN → Prop where
  | fN_case_0 (v_N : N) (var_0 : fNmag) : 
    wf_fNmag v_N var_0 →
    wf_fN v_N (fN.POS var_0)
  | fN_case_1 (v_N : N) (var_0 : fNmag) : 
    wf_fNmag v_N var_0 →
    wf_fN v_N (fN.NEG var_0)


abbrev f32 : Type := fN

abbrev f64 : Type := fN

def fzero (v_N : N) : fN :=
  fN.POS (fNmag.SUBNORM 0)

inductive fzero_is_wf : N → fN → Prop where
  | fzero_is_wf_0 (v_N : N) (ret_val : fN) : 
    ret_val == (fzero v_N) →
    wf_fN v_N ret_val →
    fzero_is_wf v_N ret_val


def fone (v_N : N) : fN :=
  fN.POS (fNmag.NORM 1 (0 : Int))

inductive fone_is_wf : N → fN → Prop where
  | fone_is_wf_0 (v_N : N) (ret_val : fN) : 
    ret_val == (fone v_N) →
    wf_fN v_N ret_val →
    fone_is_wf v_N ret_val


def canon_ (v_N : N) : Nat :=
  2 ^ (Int.toNat (((Option.get! (signif v_N)) : Int) - (1 : Int)))

abbrev vN : Type := iN

inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq

inductive wf_char : char → Prop where
  | char_case_0 (i : Nat) : 
    ((i ≥ 0) && (i ≤ 55295)) || ((i ≥ 57344) && (i ≤ 1114111)) →
    wf_char (char.mk_char i)


opaque utf8 (var_0_lst : List char) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive utf8_is_wf : List char → List byte → Prop where
  | utf8_is_wf_0 (var_0_lst : List char) (ret_val_lst : List byte) : 
    Forall (fun var_0_elem => wf_char var_0_elem) var_0_lst →
    ret_val_lst == (utf8 var_0_lst) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    utf8_is_wf var_0_lst ret_val_lst


inductive name : Type where
  | mk_name (char_lst : List char) : name
deriving Inhabited, BEq

inductive wf_name : name → Prop where
  | name_case_0 (char_lst : List char) : 
    Forall (fun v_char_elem => wf_char v_char_elem) char_lst →
    (List.length (utf8 char_lst)) < (2 ^ 32) →
    wf_name (name.mk_name char_lst)


abbrev idx : Type := u32

abbrev laneidx : Type := u8

abbrev typeidx : Type := idx

abbrev funcidx : Type := idx

abbrev globalidx : Type := idx

abbrev tableidx : Type := idx

abbrev memidx : Type := idx

abbrev elemidx : Type := idx

abbrev dataidx : Type := idx

abbrev labelidx : Type := idx

abbrev localidx : Type := idx

inductive numtype : Type where
  | I32 : numtype
  | I64 : numtype
  | F32 : numtype
  | F64 : numtype
deriving Inhabited, BEq

inductive vectype : Type where
  | V128 : vectype
deriving Inhabited, BEq

inductive consttype : Type where
  | I32 : consttype
  | I64 : consttype
  | F32 : consttype
  | F64 : consttype
  | V128 : consttype
deriving Inhabited, BEq

inductive reftype : Type where
  | FUNCREF : reftype
  | EXTERNREF : reftype
deriving Inhabited, BEq

inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
  | V128 : valtype
  | FUNCREF : valtype
  | EXTERNREF : valtype
  | BOT : valtype
deriving Inhabited, BEq

def valtype_numtype (var_0 : numtype) : valtype :=
  match var_0 with
  | numtype.I32 => valtype.I32
  | numtype.I64 => valtype.I64
  | numtype.F32 => valtype.F32
  | numtype.F64 => valtype.F64

def valtype_vectype (var_0 : vectype) : valtype :=
  match var_0 with
  | vectype.V128 => valtype.V128

inductive Inn : Type where
  | I32 : Inn
  | I64 : Inn
deriving Inhabited, BEq

def numtype_Inn (var_0 : Inn) : numtype :=
  match var_0 with
  | Inn.I32 => numtype.I32
  | Inn.I64 => numtype.I64

def valtype_Inn (var_0 : Inn) : valtype :=
  match var_0 with
  | Inn.I32 => valtype.I32
  | Inn.I64 => valtype.I64

inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq

def numtype_Fnn (var_0 : Fnn) : numtype :=
  match var_0 with
  | Fnn.F32 => numtype.F32
  | Fnn.F64 => numtype.F64

def valtype_Fnn (var_0 : Fnn) : valtype :=
  match var_0 with
  | Fnn.F32 => valtype.F32
  | Fnn.F64 => valtype.F64

abbrev Vnn : Type := vectype

abbrev resulttype : Type := list valtype

inductive packtype : Type where
  | I8 : packtype
  | I16 : packtype
deriving Inhabited, BEq

inductive lanetype : Type where
  | I32 : lanetype
  | I64 : lanetype
  | F32 : lanetype
  | F64 : lanetype
  | I8 : lanetype
  | I16 : lanetype
deriving Inhabited, BEq

def lanetype_Fnn (var_0 : Fnn) : lanetype :=
  match var_0 with
  | Fnn.F32 => lanetype.F32
  | Fnn.F64 => lanetype.F64

def lanetype_Inn (var_0 : Inn) : lanetype :=
  match var_0 with
  | Inn.I32 => lanetype.I32
  | Inn.I64 => lanetype.I64

def lanetype_numtype (var_0 : numtype) : lanetype :=
  match var_0 with
  | numtype.I32 => lanetype.I32
  | numtype.I64 => lanetype.I64
  | numtype.F32 => lanetype.F32
  | numtype.F64 => lanetype.F64

def lanetype_packtype (var_0 : packtype) : lanetype :=
  match var_0 with
  | packtype.I8 => lanetype.I8
  | packtype.I16 => lanetype.I16

abbrev Pnn : Type := packtype

inductive Jnn : Type where
  | I32 : Jnn
  | I64 : Jnn
  | I8 : Jnn
  | I16 : Jnn
deriving Inhabited, BEq

def lanetype_Jnn (var_0 : Jnn) : lanetype :=
  match var_0 with
  | Jnn.I32 => lanetype.I32
  | Jnn.I64 => lanetype.I64
  | Jnn.I8 => lanetype.I8
  | Jnn.I16 => lanetype.I16

abbrev Lnn : Type := lanetype

abbrev «mut» : Type := Option r_MUT

inductive limits : Type where
  | mk_limits (v_u32 : u32) (u32_opt : Option u32) : limits
deriving Inhabited, BEq

inductive wf_limits : limits → Prop where
  | limits_case_0 (v_u32 : u32) (u32_opt : Option u32) : 
    wf_uN 32 v_u32 →
    wf_limits (limits.mk_limits v_u32 u32_opt)


inductive globaltype : Type where
  | mk_globaltype (v_mut : «mut») (v_valtype : valtype) : globaltype
deriving Inhabited, BEq

inductive functype : Type where
  | mk_functype (v_resulttype_0 : resulttype) (v_resulttype_1 : resulttype) : functype
deriving Inhabited, BEq

inductive tabletype : Type where
  | mk_tabletype (v_limits : limits) (v_reftype : reftype) : tabletype
deriving Inhabited, BEq

inductive wf_tabletype : tabletype → Prop where
  | tabletype_case_0 (v_limits : limits) (v_reftype : reftype) : 
    wf_limits v_limits →
    wf_tabletype (tabletype.mk_tabletype v_limits v_reftype)


inductive memtype : Type where
  | PAGE (v_limits : limits) : memtype
deriving Inhabited, BEq

inductive wf_memtype : memtype → Prop where
  | memtype_case_0 (v_limits : limits) : 
    wf_limits v_limits →
    wf_memtype (memtype.PAGE v_limits)


abbrev elemtype : Type := reftype

inductive datatype : Type where
  | OK : datatype
deriving Inhabited, BEq

inductive externtype : Type where
  | FUNC (v_functype : functype) : externtype
  | GLOBAL (v_globaltype : globaltype) : externtype
  | TABLE (v_tabletype : tabletype) : externtype
  | MEM (v_memtype : memtype) : externtype
deriving Inhabited, BEq

inductive wf_externtype : externtype → Prop where
  | externtype_case_0 (v_functype : functype) : wf_externtype (externtype.FUNC v_functype)
  | externtype_case_1 (v_globaltype : globaltype) : wf_externtype (externtype.GLOBAL v_globaltype)
  | externtype_case_2 (v_tabletype : tabletype) : 
    wf_tabletype v_tabletype →
    wf_externtype (externtype.TABLE v_tabletype)
  | externtype_case_3 (v_memtype : memtype) : 
    wf_memtype v_memtype →
    wf_externtype (externtype.MEM v_memtype)


inductive dim : Type where
  | mk_dim (i : Nat) : dim
deriving Inhabited, BEq

inductive wf_dim : dim → Prop where
  | dim_case_0 (i : Nat) : 
    ((((i == 1) || (i == 2)) || (i == 4)) || (i == 8)) || (i == 16) →
    wf_dim (dim.mk_dim i)


inductive shape : Type where
  | X (v_lanetype : lanetype) (v_dim : dim) : shape
deriving Inhabited, BEq

inductive wf_shape : shape → Prop where
  | shape_case_0 (v_lanetype : lanetype) (v_dim : dim) : 
    wf_dim v_dim →
    wf_shape (shape.X v_lanetype v_dim)


def fun_lanetype (v_shape : shape) : lanetype :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => v_Lnn

def size (v_valtype : valtype) : Option Nat :=
  match v_valtype with
  | valtype.I32 => some 32
  | valtype.I64 => some 64
  | valtype.F32 => some 32
  | valtype.F64 => some 64
  | valtype.V128 => some 128
  | _ => none

def psize (v_packtype : packtype) : Nat :=
  match v_packtype with
  | packtype.I8 => 8
  | packtype.I16 => 16

def lsize (v_lanetype : lanetype) : Nat :=
  match v_lanetype with
  | lanetype.I32 => Option.get! (size (valtype_numtype numtype.I32))
  | lanetype.I64 => Option.get! (size (valtype_numtype numtype.I64))
  | lanetype.F32 => Option.get! (size (valtype_numtype numtype.F32))
  | lanetype.F64 => Option.get! (size (valtype_numtype numtype.F64))
  | lanetype.I8 => psize packtype.I8
  | lanetype.I16 => psize packtype.I16

def isize (v_Inn : Inn) : Nat :=
  Option.get! (size (valtype_Inn v_Inn))

def jsize (v_Jnn : Jnn) : Nat :=
  lsize (lanetype_Jnn v_Jnn)

def fsize (v_Fnn : Fnn) : Nat :=
  Option.get! (size (valtype_Fnn v_Fnn))

def sizenn (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

def sizenn1 (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

def sizenn2 (v_numtype : numtype) : Nat :=
  Option.get! (size (valtype_numtype v_numtype))

def lsizenn (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

def lsizenn1 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

def lsizenn2 (v_lanetype : lanetype) : Nat :=
  lsize v_lanetype

def inv_isize (nat : Nat) : Option Inn :=
  match nat with
  | 32 => some Inn.I32
  | 64 => some Inn.I64
  | _ => none

def inv_jsize (nat : Nat) : Option Jnn :=
  match nat with
  | 8 => some Jnn.I8
  | 16 => some Jnn.I16
  | 32 => some Jnn.I32
  | 64 => some Jnn.I64
  | _ => none

def inv_fsize (nat : Nat) : Option Fnn :=
  match nat with
  | 32 => some Fnn.F32
  | 64 => some Fnn.F64
  | _ => none

inductive num_ : Type where
  | mk_num__0 (v_Inn : Inn) (var_x : iN) : num_
  | mk_num__1 (v_Fnn : Fnn) (var_x : fN) : num_
deriving Inhabited, BEq

inductive wf_num_ : numtype → num_ → Prop where
  | num__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : iN) : 
    (size (valtype_Inn v_Inn)) != none →
    wf_uN (Option.get! (size (valtype_Inn v_Inn))) var_x →
    v_numtype == (numtype_Inn v_Inn) →
    wf_num_ v_numtype (num_.mk_num__0 v_Inn var_x)
  | num__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : fN) : 
    wf_fN (sizenn (numtype_Fnn v_Fnn)) var_x →
    v_numtype == (numtype_Fnn v_Fnn) →
    wf_num_ v_numtype (num_.mk_num__1 v_Fnn var_x)


def proj_num__0 (var_x : num_) : Option iN :=
  match var_x with
  | num_.mk_num__0 v_Inn var_x => some var_x
  | _ => none

def proj_num__1 (var_x : num_) : Option fN :=
  match var_x with
  | num_.mk_num__1 v_Fnn var_x => some var_x
  | _ => none

abbrev pack_ : Type := iN

inductive lane_ : Type where
  | mk_lane__0 (v_numtype : numtype) (var_x : num_) : lane_
  | mk_lane__1 (v_packtype : packtype) (var_x : pack_) : lane_
  | mk_lane__2 (v_Jnn : Jnn) (var_x : iN) : lane_
deriving Inhabited, BEq

inductive wf_lane_ : lanetype → lane_ → Prop where
  | lane__case_0 (v_lanetype : lanetype) (v_numtype : numtype) (var_x : num_) : 
    wf_num_ v_numtype var_x →
    v_lanetype == (lanetype_numtype v_numtype) →
    wf_lane_ v_lanetype (lane_.mk_lane__0 v_numtype var_x)
  | lane__case_1 (v_lanetype : lanetype) (v_packtype : packtype) (var_x : pack_) : 
    wf_uN (psize v_packtype) var_x →
    v_lanetype == (lanetype_packtype v_packtype) →
    wf_lane_ v_lanetype (lane_.mk_lane__1 v_packtype var_x)
  | lane__case_2 (v_lanetype : lanetype) (v_Jnn : Jnn) (var_x : iN) : 
    wf_uN (lsize (lanetype_Jnn v_Jnn)) var_x →
    v_lanetype == (lanetype_Jnn v_Jnn) →
    wf_lane_ v_lanetype (lane_.mk_lane__2 v_Jnn var_x)


def proj_lane__0 (var_x : lane_) : Option num_ :=
  match var_x with
  | lane_.mk_lane__0 v_numtype var_x => some var_x
  | _ => none

def proj_lane__1 (var_x : lane_) : Option pack_ :=
  match var_x with
  | lane_.mk_lane__1 v_packtype var_x => some var_x
  | _ => none

def proj_lane__2 (var_x : lane_) : Option iN :=
  match var_x with
  | lane_.mk_lane__2 v_Jnn var_x => some var_x
  | _ => none

abbrev vec_ : Type := vN

def fun_zero (v_numtype : numtype) : num_ :=
  match v_numtype with
  | numtype.I32 => num_.mk_num__0 Inn.I32 (uN.mk_uN 0)
  | numtype.I64 => num_.mk_num__0 Inn.I64 (uN.mk_uN 0)
  | numtype.F32 => num_.mk_num__1 Fnn.F32 (fzero (Option.get! (size (valtype_Fnn Fnn.F32))))
  | numtype.F64 => num_.mk_num__1 Fnn.F64 (fzero (Option.get! (size (valtype_Fnn Fnn.F64))))

inductive zero_is_wf : numtype → num_ → Prop where
  | zero_is_wf_0 (v_numtype : numtype) (ret_val : num_) : 
    ret_val == (fun_zero v_numtype) →
    wf_num_ v_numtype ret_val →
    zero_is_wf v_numtype ret_val


inductive sx : Type where
  | U : sx
  | S : sx
deriving Inhabited, BEq

inductive sz : Type where
  | mk_sz (i : Nat) : sz
deriving Inhabited, BEq

def proj_sz_0 (x : sz) : Nat :=
  match x with
  | sz.mk_sz v_num_0 => (v_num_0)

inductive wf_sz : sz → Prop where
  | sz_case_0 (i : Nat) : 
    (((i == 8) || (i == 16)) || (i == 32)) || (i == 64) →
    wf_sz (sz.mk_sz i)


inductive unop_Inn : Type where
  | CLZ : unop_Inn
  | CTZ : unop_Inn
  | POPCNT : unop_Inn
  | EXTEND (v_n : n) : unop_Inn
deriving Inhabited, BEq

inductive unop_Fnn : Type where
  | ABS : unop_Fnn
  | NEG : unop_Fnn
  | SQRT : unop_Fnn
  | CEIL : unop_Fnn
  | FLOOR : unop_Fnn
  | TRUNC : unop_Fnn
  | NEAREST : unop_Fnn
deriving Inhabited, BEq

inductive unop_ : Type where
  | mk_unop__0 (v_Inn : Inn) (var_x : unop_Inn) : unop_
  | mk_unop__1 (v_Fnn : Fnn) (var_x : unop_Fnn) : unop_
deriving Inhabited, BEq

inductive wf_unop_ : numtype → unop_ → Prop where
  | unop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : unop_Inn) : 
    v_numtype == (numtype_Inn v_Inn) →
    wf_unop_ v_numtype (unop_.mk_unop__0 v_Inn var_x)
  | unop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : unop_Fnn) : 
    v_numtype == (numtype_Fnn v_Fnn) →
    wf_unop_ v_numtype (unop_.mk_unop__1 v_Fnn var_x)


def proj_unop__0 (var_x : unop_) : Option unop_Inn :=
  match var_x with
  | unop_.mk_unop__0 v_Inn var_x => some var_x
  | _ => none

def proj_unop__1 (var_x : unop_) : Option unop_Fnn :=
  match var_x with
  | unop_.mk_unop__1 v_Fnn var_x => some var_x
  | _ => none

inductive binop_Inn : Type where
  | ADD : binop_Inn
  | SUB : binop_Inn
  | MUL : binop_Inn
  | DIV (v_sx : sx) : binop_Inn
  | REM (v_sx : sx) : binop_Inn
  | AND : binop_Inn
  | OR : binop_Inn
  | XOR : binop_Inn
  | SHL : binop_Inn
  | SHR (v_sx : sx) : binop_Inn
  | ROTL : binop_Inn
  | ROTR : binop_Inn
deriving Inhabited, BEq

inductive binop_Fnn : Type where
  | ADD : binop_Fnn
  | SUB : binop_Fnn
  | MUL : binop_Fnn
  | DIV : binop_Fnn
  | MIN : binop_Fnn
  | MAX : binop_Fnn
  | COPYSIGN : binop_Fnn
deriving Inhabited, BEq

inductive binop_ : Type where
  | mk_binop__0 (v_Inn : Inn) (var_x : binop_Inn) : binop_
  | mk_binop__1 (v_Fnn : Fnn) (var_x : binop_Fnn) : binop_
deriving Inhabited, BEq

inductive wf_binop_ : numtype → binop_ → Prop where
  | binop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : binop_Inn) : 
    v_numtype == (numtype_Inn v_Inn) →
    wf_binop_ v_numtype (binop_.mk_binop__0 v_Inn var_x)
  | binop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : binop_Fnn) : 
    v_numtype == (numtype_Fnn v_Fnn) →
    wf_binop_ v_numtype (binop_.mk_binop__1 v_Fnn var_x)


def proj_binop__0 (var_x : binop_) : Option binop_Inn :=
  match var_x with
  | binop_.mk_binop__0 v_Inn var_x => some var_x
  | _ => none

def proj_binop__1 (var_x : binop_) : Option binop_Fnn :=
  match var_x with
  | binop_.mk_binop__1 v_Fnn var_x => some var_x
  | _ => none

inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq

inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq

inductive wf_testop_ : numtype → testop_ → Prop where
  | testop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : testop_Inn) : 
    v_numtype == (numtype_Inn v_Inn) →
    wf_testop_ v_numtype (testop_.mk_testop__0 v_Inn var_x)


def proj_testop__0 (var_x : testop_) : testop_Inn :=
  match var_x with
  | testop_.mk_testop__0 v_Inn var_x => var_x

inductive relop_Inn : Type where
  | EQ : relop_Inn
  | NE : relop_Inn
  | LT (v_sx : sx) : relop_Inn
  | GT (v_sx : sx) : relop_Inn
  | LE (v_sx : sx) : relop_Inn
  | GE (v_sx : sx) : relop_Inn
deriving Inhabited, BEq

inductive relop_Fnn : Type where
  | EQ : relop_Fnn
  | NE : relop_Fnn
  | LT : relop_Fnn
  | GT : relop_Fnn
  | LE : relop_Fnn
  | GE : relop_Fnn
deriving Inhabited, BEq

inductive relop_ : Type where
  | mk_relop__0 (v_Inn : Inn) (var_x : relop_Inn) : relop_
  | mk_relop__1 (v_Fnn : Fnn) (var_x : relop_Fnn) : relop_
deriving Inhabited, BEq

inductive wf_relop_ : numtype → relop_ → Prop where
  | relop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : relop_Inn) : 
    v_numtype == (numtype_Inn v_Inn) →
    wf_relop_ v_numtype (relop_.mk_relop__0 v_Inn var_x)
  | relop__case_1 (v_numtype : numtype) (v_Fnn : Fnn) (var_x : relop_Fnn) : 
    v_numtype == (numtype_Fnn v_Fnn) →
    wf_relop_ v_numtype (relop_.mk_relop__1 v_Fnn var_x)


def proj_relop__0 (var_x : relop_) : Option relop_Inn :=
  match var_x with
  | relop_.mk_relop__0 v_Inn var_x => some var_x
  | _ => none

def proj_relop__1 (var_x : relop_) : Option relop_Fnn :=
  match var_x with
  | relop_.mk_relop__1 v_Fnn var_x => some var_x
  | _ => none

inductive cvtop : Type where
  | EXTEND (v_sx : sx) : cvtop
  | WRAP : cvtop
  | CONVERT (v_sx : sx) : cvtop
  | TRUNC (v_sx : sx) : cvtop
  | TRUNC_SAT (v_sx : sx) : cvtop
  | PROMOTE : cvtop
  | DEMOTE : cvtop
  | REINTERPRET : cvtop
deriving Inhabited, BEq

inductive ishape : Type where
  | X (v_Jnn : Jnn) (v_dim : dim) : ishape
deriving Inhabited, BEq

def shape_ishape (var_0 : ishape) : shape :=
  match var_0 with
  | ishape.X x0 x1 => shape.X (lanetype_Jnn x0) x1

inductive wf_ishape : ishape → Prop where
  | ishape_case_0 (v_Jnn : Jnn) (v_dim : dim) : 
    wf_dim v_dim →
    wf_ishape (ishape.X v_Jnn v_dim)


inductive fshape : Type where
  | X (v_Fnn : Fnn) (v_dim : dim) : fshape
deriving Inhabited, BEq

inductive wf_fshape : fshape → Prop where
  | fshape_case_0 (v_Fnn : Fnn) (v_dim : dim) : 
    wf_dim v_dim →
    wf_fshape (fshape.X v_Fnn v_dim)


inductive pshape : Type where
  | X (v_Pnn : Pnn) (v_dim : dim) : pshape
deriving Inhabited, BEq

inductive wf_pshape : pshape → Prop where
  | pshape_case_0 (v_Pnn : Pnn) (v_dim : dim) : 
    wf_dim v_dim →
    wf_pshape (pshape.X v_Pnn v_dim)


def fun_dim (v_shape : shape) : dim :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => dim.mk_dim v_N

inductive dim_is_wf : shape → dim → Prop where
  | dim_is_wf_0 (v_shape : shape) (ret_val : dim) : 
    wf_shape v_shape →
    ret_val == (fun_dim v_shape) →
    wf_dim ret_val →
    dim_is_wf v_shape ret_val


def shsize (v_shape : shape) : Nat :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => (lsize v_Lnn) * v_N

inductive vvunop : Type where
  | NOT : vvunop
deriving Inhabited, BEq

inductive vvbinop : Type where
  | AND : vvbinop
  | ANDNOT : vvbinop
  | OR : vvbinop
  | XOR : vvbinop
deriving Inhabited, BEq

inductive vvternop : Type where
  | BITSELECT : vvternop
deriving Inhabited, BEq

inductive vvtestop : Type where
  | ANY_TRUE : vvtestop
deriving Inhabited, BEq

inductive vunop_Jnn_N : Type where
  | ABS : vunop_Jnn_N
  | NEG : vunop_Jnn_N
  | POPCNT : vunop_Jnn_N
deriving Inhabited, BEq

inductive wf_vunop_Jnn_N : Jnn → N → vunop_Jnn_N → Prop where
  | vunop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) : wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N.ABS
  | vunop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N.NEG
  | vunop_Jnn_N_case_2 (v_Jnn : Jnn) (v_N : N) : 
    v_Jnn == Jnn.I8 →
    wf_vunop_Jnn_N v_Jnn v_N vunop_Jnn_N.POPCNT


inductive vunop_Fnn_N : Type where
  | ABS : vunop_Fnn_N
  | NEG : vunop_Fnn_N
  | SQRT : vunop_Fnn_N
  | CEIL : vunop_Fnn_N
  | FLOOR : vunop_Fnn_N
  | TRUNC : vunop_Fnn_N
  | NEAREST : vunop_Fnn_N
deriving Inhabited, BEq

inductive vunop_ : Type where
  | mk_vunop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vunop_Jnn_N) : vunop_
  | mk_vunop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vunop_Fnn_N) : vunop_
deriving Inhabited, BEq

inductive wf_vunop_ : shape → vunop_ → Prop where
  | vunop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vunop_Jnn_N) : 
    wf_vunop_Jnn_N v_Jnn v_N var_x →
    v_shape == (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vunop_ v_shape (vunop_.mk_vunop__0 v_Jnn v_N var_x)
  | vunop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vunop_Fnn_N) : 
    v_shape == (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_N)) →
    wf_vunop_ v_shape (vunop_.mk_vunop__1 v_Fnn v_N var_x)


def proj_vunop__0 (var_x : vunop_) : Option vunop_Jnn_N :=
  match var_x with
  | vunop_.mk_vunop__0 v_Jnn v_N var_x => some var_x
  | _ => none

def proj_vunop__1 (var_x : vunop_) : Option vunop_Fnn_N :=
  match var_x with
  | vunop_.mk_vunop__1 v_Fnn v_N var_x => some var_x
  | _ => none

inductive vbinop_Jnn_N : Type where
  | ADD : vbinop_Jnn_N
  | SUB : vbinop_Jnn_N
  | ADD_SAT (v_sx : sx) : vbinop_Jnn_N
  | SUB_SAT (v_sx : sx) : vbinop_Jnn_N
  | MUL : vbinop_Jnn_N
  | AVGRU : vbinop_Jnn_N
  | Q15MULR_SATS : vbinop_Jnn_N
  | MIN (v_sx : sx) : vbinop_Jnn_N
  | MAX (v_sx : sx) : vbinop_Jnn_N
deriving Inhabited, BEq

inductive wf_vbinop_Jnn_N : Jnn → N → vbinop_Jnn_N → Prop where
  | vbinop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) : wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.ADD
  | vbinop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.SUB
  | vbinop_Jnn_N_case_2 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.ADD_SAT v_sx)
  | vbinop_Jnn_N_case_3 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.SUB_SAT v_sx)
  | vbinop_Jnn_N_case_4 (v_Jnn : Jnn) (v_N : N) : 
    (lsizenn (lanetype_Jnn v_Jnn)) ≥ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.MUL
  | vbinop_Jnn_N_case_5 (v_Jnn : Jnn) (v_N : N) : 
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 16 →
    wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.AVGRU
  | vbinop_Jnn_N_case_6 (v_Jnn : Jnn) (v_N : N) : 
    (lsizenn (lanetype_Jnn v_Jnn)) == 16 →
    wf_vbinop_Jnn_N v_Jnn v_N vbinop_Jnn_N.Q15MULR_SATS
  | vbinop_Jnn_N_case_7 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 32 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.MIN v_sx)
  | vbinop_Jnn_N_case_8 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    (lsizenn (lanetype_Jnn v_Jnn)) ≤ 32 →
    wf_vbinop_Jnn_N v_Jnn v_N (vbinop_Jnn_N.MAX v_sx)


inductive vbinop_Fnn_N : Type where
  | ADD : vbinop_Fnn_N
  | SUB : vbinop_Fnn_N
  | MUL : vbinop_Fnn_N
  | DIV : vbinop_Fnn_N
  | MIN : vbinop_Fnn_N
  | MAX : vbinop_Fnn_N
  | PMIN : vbinop_Fnn_N
  | PMAX : vbinop_Fnn_N
deriving Inhabited, BEq

inductive vbinop_ : Type where
  | mk_vbinop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vbinop_Jnn_N) : vbinop_
  | mk_vbinop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vbinop_Fnn_N) : vbinop_
deriving Inhabited, BEq

inductive wf_vbinop_ : shape → vbinop_ → Prop where
  | vbinop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vbinop_Jnn_N) : 
    wf_vbinop_Jnn_N v_Jnn v_N var_x →
    v_shape == (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vbinop_ v_shape (vbinop_.mk_vbinop__0 v_Jnn v_N var_x)
  | vbinop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vbinop_Fnn_N) : 
    v_shape == (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_N)) →
    wf_vbinop_ v_shape (vbinop_.mk_vbinop__1 v_Fnn v_N var_x)


def proj_vbinop__0 (var_x : vbinop_) : Option vbinop_Jnn_N :=
  match var_x with
  | vbinop_.mk_vbinop__0 v_Jnn v_N var_x => some var_x
  | _ => none

def proj_vbinop__1 (var_x : vbinop_) : Option vbinop_Fnn_N :=
  match var_x with
  | vbinop_.mk_vbinop__1 v_Fnn v_N var_x => some var_x
  | _ => none

inductive vtestop_Jnn_N : Type where
  | ALL_TRUE : vtestop_Jnn_N
deriving Inhabited, BEq

inductive vtestop_ : Type where
  | mk_vtestop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vtestop_Jnn_N) : vtestop_
deriving Inhabited, BEq

inductive wf_vtestop_ : shape → vtestop_ → Prop where
  | vtestop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vtestop_Jnn_N) : 
    v_shape == (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vtestop_ v_shape (vtestop_.mk_vtestop__0 v_Jnn v_N var_x)


def proj_vtestop__0 (var_x : vtestop_) : vtestop_Jnn_N :=
  match var_x with
  | vtestop_.mk_vtestop__0 v_Jnn v_N var_x => var_x

inductive vrelop_Jnn_N : Type where
  | EQ : vrelop_Jnn_N
  | NE : vrelop_Jnn_N
  | LT (v_sx : sx) : vrelop_Jnn_N
  | GT (v_sx : sx) : vrelop_Jnn_N
  | LE (v_sx : sx) : vrelop_Jnn_N
  | GE (v_sx : sx) : vrelop_Jnn_N
deriving Inhabited, BEq

inductive wf_vrelop_Jnn_N : Jnn → N → vrelop_Jnn_N → Prop where
  | vrelop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) : wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N.EQ
  | vrelop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : wf_vrelop_Jnn_N v_Jnn v_N vrelop_Jnn_N.NE
  | vrelop_Jnn_N_case_2 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    ((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.LT v_sx)
  | vrelop_Jnn_N_case_3 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    ((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.GT v_sx)
  | vrelop_Jnn_N_case_4 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    ((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.LE v_sx)
  | vrelop_Jnn_N_case_5 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    ((lsizenn (lanetype_Jnn v_Jnn)) != 64) || (v_sx == sx.S) →
    wf_vrelop_Jnn_N v_Jnn v_N (vrelop_Jnn_N.GE v_sx)


inductive vrelop_Fnn_N : Type where
  | EQ : vrelop_Fnn_N
  | NE : vrelop_Fnn_N
  | LT : vrelop_Fnn_N
  | GT : vrelop_Fnn_N
  | LE : vrelop_Fnn_N
  | GE : vrelop_Fnn_N
deriving Inhabited, BEq

inductive vrelop_ : Type where
  | mk_vrelop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vrelop_Jnn_N) : vrelop_
  | mk_vrelop__1 (v_Fnn : Fnn) (v_N : N) (var_x : vrelop_Fnn_N) : vrelop_
deriving Inhabited, BEq

inductive wf_vrelop_ : shape → vrelop_ → Prop where
  | vrelop__case_0 (v_shape : shape) (v_Jnn : Jnn) (v_N : N) (var_x : vrelop_Jnn_N) : 
    wf_vrelop_Jnn_N v_Jnn v_N var_x →
    v_shape == (shape.X (lanetype_Jnn v_Jnn) (dim.mk_dim v_N)) →
    wf_vrelop_ v_shape (vrelop_.mk_vrelop__0 v_Jnn v_N var_x)
  | vrelop__case_1 (v_shape : shape) (v_Fnn : Fnn) (v_N : N) (var_x : vrelop_Fnn_N) : 
    v_shape == (shape.X (lanetype_Fnn v_Fnn) (dim.mk_dim v_N)) →
    wf_vrelop_ v_shape (vrelop_.mk_vrelop__1 v_Fnn v_N var_x)


def proj_vrelop__0 (var_x : vrelop_) : Option vrelop_Jnn_N :=
  match var_x with
  | vrelop_.mk_vrelop__0 v_Jnn v_N var_x => some var_x
  | _ => none

def proj_vrelop__1 (var_x : vrelop_) : Option vrelop_Fnn_N :=
  match var_x with
  | vrelop_.mk_vrelop__1 v_Fnn v_N var_x => some var_x
  | _ => none

inductive half : Type where
  | LOW : half
  | HIGH : half
deriving Inhabited, BEq

inductive zero : Type where
  | ZERO : zero
deriving Inhabited, BEq

inductive vcvtop : Type where
  | EXTEND (v_half : half) (v_sx : sx) : vcvtop
  | TRUNC_SAT (v_sx : sx) (zero_opt : Option zero) : vcvtop
  | CONVERT (half_opt : Option half) (v_sx : sx) : vcvtop
  | DEMOTE (v_zero : zero) : vcvtop
  | PROMOTELOW : vcvtop
deriving Inhabited, BEq

inductive vshiftop_Jnn_N : Type where
  | SHL : vshiftop_Jnn_N
  | SHR (v_sx : sx) : vshiftop_Jnn_N
deriving Inhabited, BEq

inductive vshiftop_ : Type where
  | mk_vshiftop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vshiftop_Jnn_N) : vshiftop_
deriving Inhabited, BEq

inductive wf_vshiftop_ : ishape → vshiftop_ → Prop where
  | vshiftop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vshiftop_Jnn_N) : 
    v_ishape == (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_vshiftop_ v_ishape (vshiftop_.mk_vshiftop__0 v_Jnn v_N var_x)


def proj_vshiftop__0 (var_x : vshiftop_) : vshiftop_Jnn_N :=
  match var_x with
  | vshiftop_.mk_vshiftop__0 v_Jnn v_N var_x => var_x

inductive vextunop_Jnn_N : Type where
  | EXTADD_PAIRWISE (v_sx : sx) : vextunop_Jnn_N
deriving Inhabited, BEq

inductive wf_vextunop_Jnn_N : Jnn → N → vextunop_Jnn_N → Prop where
  | vextunop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) (v_sx : sx) : 
    (16 ≤ (lsizenn (lanetype_Jnn v_Jnn))) && ((lsizenn (lanetype_Jnn v_Jnn)) ≤ 32) →
    wf_vextunop_Jnn_N v_Jnn v_N (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)


inductive vextunop_ : Type where
  | mk_vextunop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vextunop_Jnn_N) : vextunop_
deriving Inhabited, BEq

inductive wf_vextunop_ : ishape → vextunop_ → Prop where
  | vextunop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vextunop_Jnn_N) : 
    wf_vextunop_Jnn_N v_Jnn v_N var_x →
    v_ishape == (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_vextunop_ v_ishape (vextunop_.mk_vextunop__0 v_Jnn v_N var_x)


def proj_vextunop__0 (var_x : vextunop_) : vextunop_Jnn_N :=
  match var_x with
  | vextunop_.mk_vextunop__0 v_Jnn v_N var_x => var_x

inductive vextbinop_Jnn_N : Type where
  | EXTMUL (v_half : half) (v_sx : sx) : vextbinop_Jnn_N
  | DOTS : vextbinop_Jnn_N
deriving Inhabited, BEq

inductive wf_vextbinop_Jnn_N : Jnn → N → vextbinop_Jnn_N → Prop where
  | vextbinop_Jnn_N_case_0 (v_Jnn : Jnn) (v_N : N) (v_half : half) (v_sx : sx) : wf_vextbinop_Jnn_N v_Jnn v_N (vextbinop_Jnn_N.EXTMUL v_half v_sx)
  | vextbinop_Jnn_N_case_1 (v_Jnn : Jnn) (v_N : N) : 
    (lsizenn (lanetype_Jnn v_Jnn)) == 32 →
    wf_vextbinop_Jnn_N v_Jnn v_N vextbinop_Jnn_N.DOTS


inductive vextbinop_ : Type where
  | mk_vextbinop__0 (v_Jnn : Jnn) (v_N : N) (var_x : vextbinop_Jnn_N) : vextbinop_
deriving Inhabited, BEq

inductive wf_vextbinop_ : ishape → vextbinop_ → Prop where
  | vextbinop__case_0 (v_ishape : ishape) (v_Jnn : Jnn) (v_N : N) (var_x : vextbinop_Jnn_N) : 
    wf_vextbinop_Jnn_N v_Jnn v_N var_x →
    v_ishape == (ishape.X v_Jnn (dim.mk_dim v_N)) →
    wf_vextbinop_ v_ishape (vextbinop_.mk_vextbinop__0 v_Jnn v_N var_x)


def proj_vextbinop__0 (var_x : vextbinop_) : vextbinop_Jnn_N :=
  match var_x with
  | vextbinop_.mk_vextbinop__0 v_Jnn v_N var_x => var_x

structure memarg where
  MKmemarg ::
  ALIGN : u32
  OFFSET : u32
deriving Inhabited, BEq

inductive wf_memarg : memarg → Prop where
  | memarg_case_ (var_0 : u32) (var_1 : u32) : 
    wf_uN 32 var_0 →
    wf_uN 32 var_1 →
    wf_memarg ({
      ALIGN := var_0
      OFFSET := var_1 : memarg
    })


inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq

inductive wf_loadop_Inn : Inn → loadop_Inn → Prop where
  | loadop_Inn_case_0 (v_Inn : Inn) (v_sz : sz) (v_sx : sx) : 
    wf_sz v_sz →
    (proj_sz_0 v_sz) < (sizenn (numtype_Inn v_Inn)) →
    wf_loadop_Inn v_Inn (loadop_Inn.mk_loadop_Inn v_sz v_sx)


inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq

inductive wf_loadop_ : numtype → loadop_ → Prop where
  | loadop__case_0 (v_numtype : numtype) (v_Inn : Inn) (var_x : loadop_Inn) : 
    wf_loadop_Inn v_Inn var_x →
    v_numtype == (numtype_Inn v_Inn) →
    wf_loadop_ v_numtype (loadop_.mk_loadop__0 v_Inn var_x)


def proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
  match var_x with
  | loadop_.mk_loadop__0 v_Inn var_x => var_x

inductive vloadop : Type where
  | SHAPEX_ (__0 : Nat) (__1 : Nat) (v_sx : sx) : vloadop
  | SPLAT (_ : Nat) : vloadop
  | ZERO (_ : Nat) : vloadop
deriving Inhabited, BEq

inductive blocktype : Type where
  | _RESULT (valtype_opt : Option valtype) : blocktype
  | _IDX (v_typeidx : typeidx) : blocktype
deriving Inhabited, BEq

inductive wf_blocktype : blocktype → Prop where
  | blocktype_case_0 (valtype_opt : Option valtype) : wf_blocktype (blocktype._RESULT valtype_opt)
  | blocktype_case_1 (v_typeidx : typeidx) : 
    wf_uN 32 v_typeidx →
    wf_blocktype (blocktype._IDX v_typeidx)


inductive instr : Type where
  | NOP : instr
  | UNREACHABLE : instr
  | DROP : instr
  | SELECT (valtype_lst_opt : Option (List valtype)) : instr
  | BLOCK (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | LOOP (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | IFELSE (v_blocktype : blocktype) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : instr
  | BR (v_labelidx : labelidx) : instr
  | BR_IF (v_labelidx : labelidx) : instr
  | BR_TABLE (labelidx_lst : List labelidx) (v_labelidx : labelidx) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_INDIRECT (v_tableidx : tableidx) (v_typeidx : typeidx) : instr
  | RETURN : instr
  | CONST (v_numtype : numtype) (_ : num_) : instr
  | UNOP (v_numtype : numtype) (_ : unop_) : instr
  | BINOP (v_numtype : numtype) (_ : binop_) : instr
  | TESTOP (v_numtype : numtype) (_ : testop_) : instr
  | RELOP (v_numtype : numtype) (_ : relop_) : instr
  | CVTOP (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) : instr
  | EXTEND (v_numtype : numtype) (v_n : n) : instr
  | VCONST (v_vectype : vectype) (_ : vec_) : instr
  | VVUNOP (v_vectype : vectype) (v_vvunop : vvunop) : instr
  | VVBINOP (v_vectype : vectype) (v_vvbinop : vvbinop) : instr
  | VVTERNOP (v_vectype : vectype) (v_vvternop : vvternop) : instr
  | VVTESTOP (v_vectype : vectype) (v_vvtestop : vvtestop) : instr
  | VUNOP (v_shape : shape) (_ : vunop_) : instr
  | VBINOP (v_shape : shape) (_ : vbinop_) : instr
  | VTESTOP (v_shape : shape) (_ : vtestop_) : instr
  | VRELOP (v_shape : shape) (_ : vrelop_) : instr
  | VSHIFTOP (v_ishape : ishape) (_ : vshiftop_) : instr
  | VBITMASK (v_ishape : ishape) : instr
  | VSWIZZLE (v_ishape : ishape) : instr
  | VSHUFFLE (v_ishape : ishape) (laneidx_lst : List laneidx) : instr
  | VSPLAT (v_shape : shape) : instr
  | VEXTRACT_LANE (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) : instr
  | VREPLACE_LANE (v_shape : shape) (v_laneidx : laneidx) : instr
  | VEXTUNOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextunop_) : instr
  | VEXTBINOP (ishape_1 : ishape) (ishape_2 : ishape) (_ : vextbinop_) : instr
  | VNARROW (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : instr
  | VCVTOP (v_shape_0 : shape) (v_shape_1 : shape) (v_vcvtop : vcvtop) : instr
  | REF_NULL (v_reftype : reftype) : instr
  | REF_FUNC (v_funcidx : funcidx) : instr
  | REF_IS_NULL : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | LOCAL_TEE (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
  | TABLE_GET (v_tableidx : tableidx) : instr
  | TABLE_SET (v_tableidx : tableidx) : instr
  | TABLE_SIZE (v_tableidx : tableidx) : instr
  | TABLE_GROW (v_tableidx : tableidx) : instr
  | TABLE_FILL (v_tableidx : tableidx) : instr
  | TABLE_COPY (v_tableidx_0 : tableidx) (v_tableidx_1 : tableidx) : instr
  | TABLE_INIT (v_tableidx : tableidx) (v_elemidx : elemidx) : instr
  | ELEM_DROP (v_elemidx : elemidx) : instr
  | LOAD (v_numtype : numtype) (_ : Option loadop_) (v_memarg : memarg) : instr
  | STORE (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) : instr
  | VLOAD (v_vectype : vectype) (vloadop_opt : Option vloadop) (v_memarg : memarg) : instr
  | VLOAD_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | VSTORE (v_vectype : vectype) (v_memarg : memarg) : instr
  | VSTORE_LANE (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : instr
  | MEMORY_SIZE : instr
  | MEMORY_GROW : instr
  | MEMORY_FILL : instr
  | MEMORY_COPY : instr
  | MEMORY_INIT (v_dataidx : dataidx) : instr
  | DATA_DROP (v_dataidx : dataidx) : instr
deriving Inhabited, BEq

inductive wf_instr : instr → Prop where
  | instr_case_0 : wf_instr instr.NOP
  | instr_case_1 : wf_instr instr.UNREACHABLE
  | instr_case_2 : wf_instr instr.DROP
  | instr_case_3 (valtype_lst_opt : Option (List valtype)) : wf_instr (instr.SELECT valtype_lst_opt)
  | instr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) : 
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.BLOCK v_blocktype instr_lst)
  | instr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) : 
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    wf_instr (instr.LOOP v_blocktype instr_lst)
  | instr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) : 
    wf_blocktype v_blocktype →
    Forall (fun v_instr_elem => wf_instr v_instr_elem) instr_lst →
    Forall (fun instr_lst_0_elem => wf_instr instr_lst_0_elem) instr_lst_0_lst →
    wf_instr (instr.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | instr_case_7 (v_labelidx : labelidx) : 
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR v_labelidx)
  | instr_case_8 (v_labelidx : labelidx) : 
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_IF v_labelidx)
  | instr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) : 
    Forall (fun v_labelidx_elem => wf_uN 32 v_labelidx_elem) labelidx_lst →
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_TABLE labelidx_lst v_labelidx)
  | instr_case_10 (v_funcidx : funcidx) : 
    wf_uN 32 v_funcidx →
    wf_instr (instr.CALL v_funcidx)
  | instr_case_11 (v_tableidx : tableidx) (v_typeidx : typeidx) : 
    wf_uN 32 v_tableidx →
    wf_uN 32 v_typeidx →
    wf_instr (instr.CALL_INDIRECT v_tableidx v_typeidx)
  | instr_case_12 : wf_instr instr.RETURN
  | instr_case_13 (v_numtype : numtype) (var_0 : num_) : 
    wf_num_ v_numtype var_0 →
    wf_instr (instr.CONST v_numtype var_0)
  | instr_case_14 (v_numtype : numtype) (var_0 : unop_) : 
    wf_unop_ v_numtype var_0 →
    wf_instr (instr.UNOP v_numtype var_0)
  | instr_case_15 (v_numtype : numtype) (var_0 : binop_) : 
    wf_binop_ v_numtype var_0 →
    wf_instr (instr.BINOP v_numtype var_0)
  | instr_case_16 (v_numtype : numtype) (var_0 : testop_) : 
    wf_testop_ v_numtype var_0 →
    wf_instr (instr.TESTOP v_numtype var_0)
  | instr_case_17 (v_numtype : numtype) (var_0 : relop_) : 
    wf_relop_ v_numtype var_0 →
    wf_instr (instr.RELOP v_numtype var_0)
  | instr_case_18 (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) : 
    numtype_1 != numtype_2 →
    wf_instr (instr.CVTOP numtype_1 numtype_2 v_cvtop)
  | instr_case_19 (v_numtype : numtype) (v_n : n) : wf_instr (instr.EXTEND v_numtype v_n)
  | instr_case_20 (v_vectype : vectype) (var_0 : vec_) : 
    (size (valtype_vectype v_vectype)) != none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) var_0 →
    wf_instr (instr.VCONST v_vectype var_0)
  | instr_case_21 (v_vectype : vectype) (v_vvunop : vvunop) : wf_instr (instr.VVUNOP v_vectype v_vvunop)
  | instr_case_22 (v_vectype : vectype) (v_vvbinop : vvbinop) : wf_instr (instr.VVBINOP v_vectype v_vvbinop)
  | instr_case_23 (v_vectype : vectype) (v_vvternop : vvternop) : wf_instr (instr.VVTERNOP v_vectype v_vvternop)
  | instr_case_24 (v_vectype : vectype) (v_vvtestop : vvtestop) : wf_instr (instr.VVTESTOP v_vectype v_vvtestop)
  | instr_case_25 (v_shape : shape) (var_0 : vunop_) : 
    wf_shape v_shape →
    wf_vunop_ v_shape var_0 →
    wf_instr (instr.VUNOP v_shape var_0)
  | instr_case_26 (v_shape : shape) (var_0 : vbinop_) : 
    wf_shape v_shape →
    wf_vbinop_ v_shape var_0 →
    wf_instr (instr.VBINOP v_shape var_0)
  | instr_case_27 (v_shape : shape) (var_0 : vtestop_) : 
    wf_shape v_shape →
    wf_vtestop_ v_shape var_0 →
    wf_instr (instr.VTESTOP v_shape var_0)
  | instr_case_28 (v_shape : shape) (var_0 : vrelop_) : 
    wf_shape v_shape →
    wf_vrelop_ v_shape var_0 →
    wf_instr (instr.VRELOP v_shape var_0)
  | instr_case_29 (v_ishape : ishape) (var_0 : vshiftop_) : 
    wf_ishape v_ishape →
    wf_vshiftop_ v_ishape var_0 →
    wf_instr (instr.VSHIFTOP v_ishape var_0)
  | instr_case_30 (v_ishape : ishape) : 
    wf_ishape v_ishape →
    wf_instr (instr.VBITMASK v_ishape)
  | instr_case_31 (v_ishape : ishape) : 
    wf_ishape v_ishape →
    v_ishape == (ishape.X Jnn.I8 (dim.mk_dim 16)) →
    wf_instr (instr.VSWIZZLE v_ishape)
  | instr_case_32 (v_ishape : ishape) (laneidx_lst : List laneidx) : 
    wf_ishape v_ishape →
    Forall (fun v_laneidx_elem => wf_uN 8 v_laneidx_elem) laneidx_lst →
    (v_ishape == (ishape.X Jnn.I8 (dim.mk_dim 16))) && ((List.length laneidx_lst) == 16) →
    wf_instr (instr.VSHUFFLE v_ishape laneidx_lst)
  | instr_case_33 (v_shape : shape) : 
    wf_shape v_shape →
    wf_instr (instr.VSPLAT v_shape)
  | instr_case_34 (v_numtype : numtype) (v_shape : shape) (sx_opt : Option sx) (v_laneidx : laneidx) : 
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    (((fun_lanetype v_shape) == (lanetype_numtype v_numtype)) ↔ (sx_opt == none)) →
    wf_instr (instr.VEXTRACT_LANE v_shape sx_opt v_laneidx)
  | instr_case_35 (v_shape : shape) (v_laneidx : laneidx) : 
    wf_shape v_shape →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VREPLACE_LANE v_shape v_laneidx)
  | instr_case_36 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextunop_) : 
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextunop_ ishape_1 var_0 →
    (lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2)))) →
    wf_instr (instr.VEXTUNOP ishape_1 ishape_2 var_0)
  | instr_case_37 (ishape_1 : ishape) (ishape_2 : ishape) (var_0 : vextbinop_) : 
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextbinop_ ishape_1 var_0 →
    (lsize (fun_lanetype (shape_ishape ishape_1))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_2)))) →
    wf_instr (instr.VEXTBINOP ishape_1 ishape_2 var_0)
  | instr_case_38 (ishape_1 : ishape) (ishape_2 : ishape) (v_sx : sx) : 
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    ((lsize (fun_lanetype (shape_ishape ishape_2))) == (2 * (lsize (fun_lanetype (shape_ishape ishape_1))))) && ((2 * (lsize (fun_lanetype (shape_ishape ishape_1)))) ≤ 32) →
    wf_instr (instr.VNARROW ishape_1 ishape_2 v_sx)
  | instr_case_39 (v_shape : shape) (shape_0 : shape) (v_vcvtop : vcvtop) : 
    wf_shape v_shape →
    wf_shape shape_0 →
    wf_instr (instr.VCVTOP v_shape shape_0 v_vcvtop)
  | instr_case_40 (v_reftype : reftype) : wf_instr (instr.REF_NULL v_reftype)
  | instr_case_41 (v_funcidx : funcidx) : 
    wf_uN 32 v_funcidx →
    wf_instr (instr.REF_FUNC v_funcidx)
  | instr_case_42 : wf_instr instr.REF_IS_NULL
  | instr_case_43 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_GET v_localidx)
  | instr_case_44 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_SET v_localidx)
  | instr_case_45 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_TEE v_localidx)
  | instr_case_46 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_GET v_globalidx)
  | instr_case_47 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_SET v_globalidx)
  | instr_case_48 (v_tableidx : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_GET v_tableidx)
  | instr_case_49 (v_tableidx : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_SET v_tableidx)
  | instr_case_50 (v_tableidx : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_SIZE v_tableidx)
  | instr_case_51 (v_tableidx : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_GROW v_tableidx)
  | instr_case_52 (v_tableidx : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_instr (instr.TABLE_FILL v_tableidx)
  | instr_case_53 (v_tableidx : tableidx) (tableidx_0 : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_uN 32 tableidx_0 →
    wf_instr (instr.TABLE_COPY v_tableidx tableidx_0)
  | instr_case_54 (v_tableidx : tableidx) (v_elemidx : elemidx) : 
    wf_uN 32 v_tableidx →
    wf_uN 32 v_elemidx →
    wf_instr (instr.TABLE_INIT v_tableidx v_elemidx)
  | instr_case_55 (v_elemidx : elemidx) : 
    wf_uN 32 v_elemidx →
    wf_instr (instr.ELEM_DROP v_elemidx)
  | instr_case_56 (v_numtype : numtype) (var_0_opt : Option loadop_) (v_memarg : memarg) : 
    Forall (fun var_0_elem => wf_loadop_ v_numtype var_0_elem) (Option.toList var_0_opt) →
    wf_memarg v_memarg →
    wf_instr (instr.LOAD v_numtype var_0_opt v_memarg)
  | instr_case_57 (Inn_opt : Option Inn) (numtype_opt : Option numtype) (v_numtype : numtype) (sz_opt : Option sz) (v_memarg : memarg) : 
    Forall (fun v_sz_elem => wf_sz v_sz_elem) (Option.toList sz_opt) →
    wf_memarg v_memarg →
    ((Inn_opt == none) ↔ (numtype_opt == none)) →
    ((Inn_opt == none) ↔ (sz_opt == none)) →
    Forall₃ (fun v_Inn_elem v_numtype_elem v_sz_elem => (v_numtype_elem == (numtype_Inn v_Inn_elem)) && ((proj_sz_0 v_sz_elem) < (sizenn (numtype_Inn v_Inn_elem)))) (Option.toList Inn_opt) (Option.toList numtype_opt) (Option.toList sz_opt) →
    wf_instr (instr.STORE v_numtype sz_opt v_memarg)
  | instr_case_58 (v_vectype : vectype) (vloadop_opt : Option vloadop) (v_memarg : memarg) : 
    wf_memarg v_memarg →
    wf_instr (instr.VLOAD v_vectype vloadop_opt v_memarg)
  | instr_case_59 (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : 
    wf_sz v_sz →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VLOAD_LANE v_vectype v_sz v_memarg v_laneidx)
  | instr_case_60 (v_vectype : vectype) (v_memarg : memarg) : 
    wf_memarg v_memarg →
    wf_instr (instr.VSTORE v_vectype v_memarg)
  | instr_case_61 (v_vectype : vectype) (v_sz : sz) (v_memarg : memarg) (v_laneidx : laneidx) : 
    wf_sz v_sz →
    wf_memarg v_memarg →
    wf_uN 8 v_laneidx →
    wf_instr (instr.VSTORE_LANE v_vectype v_sz v_memarg v_laneidx)
  | instr_case_62 : wf_instr instr.MEMORY_SIZE
  | instr_case_63 : wf_instr instr.MEMORY_GROW
  | instr_case_64 : wf_instr instr.MEMORY_FILL
  | instr_case_65 : wf_instr instr.MEMORY_COPY
  | instr_case_66 (v_dataidx : dataidx) : 
    wf_uN 32 v_dataidx →
    wf_instr (instr.MEMORY_INIT v_dataidx)
  | instr_case_67 (v_dataidx : dataidx) : 
    wf_uN 32 v_dataidx →
    wf_instr (instr.DATA_DROP v_dataidx)


abbrev expr : Type := List instr

inductive elemmode : Type where
  | ACTIVE (v_tableidx : tableidx) (v_expr : expr) : elemmode
  | PASSIVE : elemmode
  | DECLARE : elemmode
deriving Inhabited, BEq

inductive wf_elemmode : elemmode → Prop where
  | elemmode_case_0 (v_tableidx : tableidx) (v_expr : expr) : 
    wf_uN 32 v_tableidx →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_elemmode (elemmode.ACTIVE v_tableidx v_expr)
  | elemmode_case_1 : wf_elemmode elemmode.PASSIVE
  | elemmode_case_2 : wf_elemmode elemmode.DECLARE


inductive datamode : Type where
  | ACTIVE (v_memidx : memidx) (v_expr : expr) : datamode
  | PASSIVE : datamode
deriving Inhabited, BEq

inductive wf_datamode : datamode → Prop where
  | datamode_case_0 (v_memidx : memidx) (v_expr : expr) : 
    wf_uN 32 v_memidx →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_datamode (datamode.ACTIVE v_memidx v_expr)
  | datamode_case_1 : wf_datamode datamode.PASSIVE


inductive type : Type where
  | TYPE (v_functype : functype) : type
deriving Inhabited, BEq

inductive «local» : Type where
  | LOCAL (v_valtype : valtype) : «local»
deriving Inhabited, BEq

inductive func : Type where
  | FUNC (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) : func
deriving Inhabited, BEq

inductive wf_func : func → Prop where
  | func_case_0 (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) : 
    wf_uN 32 v_typeidx →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_func (func.FUNC v_typeidx local_lst v_expr)


inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq

inductive wf_global : global → Prop where
  | global_case_0 (v_globaltype : globaltype) (v_expr : expr) : 
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    wf_global (global.GLOBAL v_globaltype v_expr)


inductive table : Type where
  | TABLE (v_tabletype : tabletype) : table
deriving Inhabited, BEq

inductive wf_table : table → Prop where
  | table_case_0 (v_tabletype : tabletype) : 
    wf_tabletype v_tabletype →
    wf_table (table.TABLE v_tabletype)


inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq

inductive wf_mem : mem → Prop where
  | mem_case_0 (v_memtype : memtype) : 
    wf_memtype v_memtype →
    wf_mem (mem.MEMORY v_memtype)


inductive elem : Type where
  | ELEM (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) : elem
deriving Inhabited, BEq

inductive wf_elem : elem → Prop where
  | elem_case_0 (v_reftype : reftype) (expr_lst : List expr) (v_elemmode : elemmode) : 
    Forall (fun v_expr_elem => Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr_elem) expr_lst →
    wf_elemmode v_elemmode →
    wf_elem (elem.ELEM v_reftype expr_lst v_elemmode)


inductive data : Type where
  | DATA (byte_lst : List byte) (v_datamode : datamode) : data
deriving Inhabited, BEq

inductive wf_data : data → Prop where
  | data_case_0 (byte_lst : List byte) (v_datamode : datamode) : 
    Forall (fun v_byte_elem => wf_byte v_byte_elem) byte_lst →
    wf_datamode v_datamode →
    wf_data (data.DATA byte_lst v_datamode)


inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq

inductive wf_start : start → Prop where
  | start_case_0 (v_funcidx : funcidx) : 
    wf_uN 32 v_funcidx →
    wf_start (start.START v_funcidx)


inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
deriving Inhabited, BEq

inductive wf_externidx : externidx → Prop where
  | externidx_case_0 (v_funcidx : funcidx) : 
    wf_uN 32 v_funcidx →
    wf_externidx (externidx.FUNC v_funcidx)
  | externidx_case_1 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_externidx (externidx.GLOBAL v_globalidx)
  | externidx_case_2 (v_tableidx : tableidx) : 
    wf_uN 32 v_tableidx →
    wf_externidx (externidx.TABLE v_tableidx)
  | externidx_case_3 (v_memidx : memidx) : 
    wf_uN 32 v_memidx →
    wf_externidx (externidx.MEM v_memidx)


inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq

inductive wf_export : «export» → Prop where
  | export_case_0 (v_name : name) (v_externidx : externidx) : 
    wf_name v_name →
    wf_externidx v_externidx →
    wf_export (export.EXPORT v_name v_externidx)


inductive «import» : Type where
  | IMPORT (v_name_0 : name) (v_name_1 : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq

inductive wf_import : «import» → Prop where
  | import_case_0 (v_name : name) (name_0 : name) (v_externtype : externtype) : 
    wf_name v_name →
    wf_name name_0 →
    wf_externtype v_externtype →
    wf_import (import.IMPORT v_name name_0 v_externtype)


inductive module : Type where
  | MODULE (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») : module
deriving Inhabited, BEq

inductive wf_module : module → Prop where
  | module_case_0 (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») : 
    Forall (fun v_import_elem => wf_import v_import_elem) import_lst →
    Forall (fun v_func_elem => wf_func v_func_elem) func_lst →
    Forall (fun v_global_elem => wf_global v_global_elem) global_lst →
    Forall (fun v_table_elem => wf_table v_table_elem) table_lst →
    Forall (fun v_mem_elem => wf_mem v_mem_elem) mem_lst →
    Forall (fun v_elem_elem => wf_elem v_elem_elem) elem_lst →
    Forall (fun v_data_elem => wf_data v_data_elem) data_lst →
    Forall (fun v_start_elem => wf_start v_start_elem) (Option.toList start_opt) →
    Forall (fun v_export_elem => wf_export v_export_elem) export_lst →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)


inductive fun_concat_bytes : List (List byte) → List byte → Prop where
  | fun_concat_bytes_case_0 : fun_concat_bytes [] []
  | fun_concat_bytes_case_1 (b_lst : List byte) (b'_lst_lst : List (List byte)) (var_0 : List byte) : 
    fun_concat_bytes b'_lst_lst var_0 →
    fun_concat_bytes ([b_lst] ++ b'_lst_lst) (b_lst ++ var_0)


inductive concat_bytes_is_wf : List (List byte) → List byte → Prop where
  | concat_bytes_is_wf_0 (var_0_lst_lst : List (List byte)) (ret_val_lst : List byte) (var_0 : List byte) : 
    fun_concat_bytes var_0_lst_lst var_0 →
    Forall (fun var_0_lst_elem => Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst_elem) var_0_lst_lst →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    concat_bytes_is_wf var_0_lst_lst ret_val_lst


def unpack (v_lanetype : lanetype) : numtype :=
  match v_lanetype with
  | lanetype.I32 => numtype.I32
  | lanetype.I64 => numtype.I64
  | lanetype.F32 => numtype.F32
  | lanetype.F64 => numtype.F64
  | lanetype.I8 => numtype.I32
  | lanetype.I16 => numtype.I32

def shunpack (v_shape : shape) : numtype :=
  match v_shape with
  | shape.X v_Lnn (dim.mk_dim v_N) => unpack v_Lnn

inductive fun_funcsxt : List externtype → List functype → Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 (ft : functype) (xt_lst : List externtype) (var_0 : List functype) : 
    fun_funcsxt xt_lst var_0 →
    fun_funcsxt ([externtype.FUNC ft] ++ xt_lst) ([ft] ++ var_0)
  | fun_funcsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List functype) : 
    fun_funcsxt xt_lst var_0 →
    fun_funcsxt ([v_externtype] ++ xt_lst) var_0


inductive fun_globalsxt : List externtype → List globaltype → Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 (gt : globaltype) (xt_lst : List externtype) (var_0 : List globaltype) : 
    fun_globalsxt xt_lst var_0 →
    fun_globalsxt ([externtype.GLOBAL gt] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List globaltype) : 
    fun_globalsxt xt_lst var_0 →
    fun_globalsxt ([v_externtype] ++ xt_lst) var_0


inductive fun_tablesxt : List externtype → List tabletype → Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 (tt : tabletype) (xt_lst : List externtype) (var_0 : List tabletype) : 
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([externtype.TABLE tt] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List tabletype) : 
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0


inductive tablesxt_is_wf : List externtype → List tabletype → Prop where
  | tablesxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List tabletype) (var_0 : List tabletype) : 
    fun_tablesxt var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externtype var_0_elem) var_0_lst →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_tabletype ret_val_elem) ret_val_lst →
    tablesxt_is_wf var_0_lst ret_val_lst


inductive fun_memsxt : List externtype → List memtype → Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 (mt : memtype) (xt_lst : List externtype) (var_0 : List memtype) : 
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([externtype.MEM mt] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List memtype) : 
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([v_externtype] ++ xt_lst) var_0


inductive memsxt_is_wf : List externtype → List memtype → Prop where
  | memsxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List memtype) (var_0 : List memtype) : 
    fun_memsxt var_0_lst var_0 →
    Forall (fun var_0_elem => wf_externtype var_0_elem) var_0_lst →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_memtype ret_val_elem) ret_val_lst →
    memsxt_is_wf var_0_lst ret_val_lst


def dataidx_instr (v_instr : instr) : List dataidx :=
  match v_instr with
  | instr.MEMORY_INIT x => [x]
  | instr.DATA_DROP x => [x]
  | _ => []

inductive dataidx_instr_is_wf : instr → List dataidx → Prop where
  | dataidx_instr_is_wf_0 (v_instr : instr) (ret_val_lst : List dataidx) : 
    wf_instr v_instr →
    ret_val_lst == (dataidx_instr v_instr) →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    dataidx_instr_is_wf v_instr ret_val_lst


inductive fun_dataidx_instrs : List instr → List dataidx → Prop where
  | fun_dataidx_instrs_case_0 : fun_dataidx_instrs [] []
  | fun_dataidx_instrs_case_1 (v_instr : instr) (instr'_lst : List instr) (var_0 : List dataidx) : 
    fun_dataidx_instrs instr'_lst var_0 →
    fun_dataidx_instrs ([v_instr] ++ instr'_lst) ((dataidx_instr v_instr) ++ var_0)


inductive dataidx_instrs_is_wf : List instr → List dataidx → Prop where
  | dataidx_instrs_is_wf_0 (var_0_lst : List instr) (ret_val_lst : List dataidx) (var_0 : List dataidx) : 
    fun_dataidx_instrs var_0_lst var_0 →
    Forall (fun var_0_elem => wf_instr var_0_elem) var_0_lst →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    dataidx_instrs_is_wf var_0_lst ret_val_lst


inductive fun_dataidx_expr : expr → List dataidx → Prop where
  | fun_dataidx_expr_case_0 (in_lst : List instr) (var_0 : List dataidx) : 
    fun_dataidx_instrs in_lst var_0 →
    fun_dataidx_expr in_lst var_0


inductive dataidx_expr_is_wf : expr → List dataidx → Prop where
  | dataidx_expr_is_wf_0 (v_expr : expr) (ret_val_lst : List dataidx) (var_0 : List dataidx) : 
    fun_dataidx_expr v_expr var_0 →
    Forall (fun v_expr_elem => wf_instr v_expr_elem) v_expr →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    dataidx_expr_is_wf v_expr ret_val_lst


inductive fun_dataidx_func : func → List dataidx → Prop where
  | fun_dataidx_func_case_0 (x : uN) (loc_lst : List «local») (e : List instr) (var_0 : List dataidx) : 
    fun_dataidx_expr e var_0 →
    fun_dataidx_func (func.FUNC x loc_lst e) var_0


inductive dataidx_func_is_wf : func → List dataidx → Prop where
  | dataidx_func_is_wf_0 (v_func : func) (ret_val_lst : List dataidx) (var_0 : List dataidx) : 
    fun_dataidx_func v_func var_0 →
    wf_func v_func →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    dataidx_func_is_wf v_func ret_val_lst


inductive fun_dataidx_funcs : List func → List dataidx → Prop where
  | fun_dataidx_funcs_case_0 : fun_dataidx_funcs [] []
  | fun_dataidx_funcs_case_1 (v_func : func) (func'_lst : List func) (var_1 : List dataidx) (var_0 : List dataidx) : 
    fun_dataidx_funcs func'_lst var_1 →
    fun_dataidx_func v_func var_0 →
    fun_dataidx_funcs ([v_func] ++ func'_lst) (var_0 ++ var_1)


inductive dataidx_funcs_is_wf : List func → List dataidx → Prop where
  | dataidx_funcs_is_wf_0 (var_0_lst : List func) (ret_val_lst : List dataidx) (var_0 : List dataidx) : 
    fun_dataidx_funcs var_0_lst var_0 →
    Forall (fun var_0_elem => wf_func var_0_elem) var_0_lst →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_uN 32 ret_val_elem) ret_val_lst →
    dataidx_funcs_is_wf var_0_lst ret_val_lst


def memarg0 : memarg :=
  {
    ALIGN := .mk_uN 0
    OFFSET := .mk_uN 0 : memarg
  }

inductive memarg0_is_wf : memarg → Prop where
  | memarg0_is_wf_0 (ret_val : memarg) : 
    ret_val == memarg0 →
    wf_memarg ret_val →
    memarg0_is_wf ret_val


opaque s33_to_u32 (v_s33 : s33) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive s33_to_u32_is_wf : s33 → u32 → Prop where
  | s33_to_u32_is_wf_0 (v_s33 : s33) (ret_val : u32) : 
    wf_sN 33 v_s33 →
    ret_val == (s33_to_u32 v_s33) →
    wf_uN 32 ret_val →
    s33_to_u32_is_wf v_s33 ret_val


def nat_of_bool (v_bool : Bool) : Nat :=
  match v_bool with
  | false => 0
  | true => 1

opaque truncz (rat : Rat) : Int := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fun_signed_ : N → Nat → Int → Prop where
  | fun_signed__case_0 (v_N : Nat) (i : Nat) : 
    i < (2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) →
    fun_signed_ v_N i (i : Int)
  | fun_signed__case_1 (v_N : Nat) (i : Nat) : 
    ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) ≤ i) && (i < (2 ^ v_N)) →
    fun_signed_ v_N i ((i : Int) - ((2 ^ v_N) : Int))


inductive fun_inv_signed_ : N → Int → Nat → Prop where
  | fun_inv_signed__case_0 (v_N : Nat) (i : Int) : 
    ((0 : Int) ≤ i) && (i < ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) →
    fun_inv_signed_ v_N i (Int.toNat i)
  | fun_inv_signed__case_1 (v_N : Nat) (i : Int) : 
    ((- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) ≤ i) && (i < (0 : Int)) →
    fun_inv_signed_ v_N i (Int.toNat (i + ((2 ^ v_N) : Int)))


def sat_u_ (v_N : N) (int : Int) : Nat :=
  if int < (0 : Int) then 0 else if int > (((2 ^ v_N) : Int) - (1 : Int)) then Int.toNat (((2 ^ v_N) : Int) - (1 : Int)) else Int.toNat int

def sat_s_ (v_N : N) (int : Int) : Int :=
  if int < (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) then - ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) else if int > (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)) then ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int) else int

opaque extend__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive extend___is_wf : M → N → sx → iN → iN → Prop where
  | extend___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_M v_iN →
    ret_val == (extend__ v_M v_N v_sx v_iN) →
    wf_uN v_N ret_val →
    extend___is_wf v_M v_N v_sx v_iN ret_val


opaque fabs_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fabs__is_wf : N → fN → List fN → Prop where
  | fabs__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fabs_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fabs__is_wf v_N v_fN ret_val_lst


opaque fceil_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fceil__is_wf : N → fN → List fN → Prop where
  | fceil__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fceil_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fceil__is_wf v_N v_fN ret_val_lst


opaque ffloor_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ffloor__is_wf : N → fN → List fN → Prop where
  | ffloor__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (ffloor_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    ffloor__is_wf v_N v_fN ret_val_lst


opaque fnearest_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fnearest__is_wf : N → fN → List fN → Prop where
  | fnearest__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fnearest_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fnearest__is_wf v_N v_fN ret_val_lst


opaque fneg_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fneg__is_wf : N → fN → List fN → Prop where
  | fneg__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fneg_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fneg__is_wf v_N v_fN ret_val_lst


opaque fsqrt_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsqrt__is_wf : N → fN → List fN → Prop where
  | fsqrt__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fsqrt_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fsqrt__is_wf v_N v_fN ret_val_lst


opaque ftrunc_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ftrunc__is_wf : N → fN → List fN → Prop where
  | ftrunc__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (ftrunc_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    ftrunc__is_wf v_N v_fN ret_val_lst


opaque iclz_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iclz__is_wf : N → iN → iN → Prop where
  | iclz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    ret_val == (iclz_ v_N v_iN) →
    wf_uN v_N ret_val →
    iclz__is_wf v_N v_iN ret_val


opaque ictz_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ictz__is_wf : N → iN → iN → Prop where
  | ictz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    ret_val == (ictz_ v_N v_iN) →
    wf_uN v_N ret_val →
    ictz__is_wf v_N v_iN ret_val


opaque ipopcnt_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ipopcnt__is_wf : N → iN → iN → Prop where
  | ipopcnt__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    ret_val == (ipopcnt_ v_N v_iN) →
    wf_uN v_N ret_val →
    ipopcnt__is_wf v_N v_iN ret_val


opaque wrap__ (v_M : M) (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive wrap___is_wf : M → N → iN → iN → Prop where
  | wrap___is_wf_0 (v_M : M) (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_M v_iN →
    ret_val == (wrap__ v_M v_N v_iN) →
    wf_uN v_N ret_val →
    wrap___is_wf v_M v_N v_iN ret_val


def fun_unop_ (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) : List num_ :=
  match v_numtype, v_unop_, v_num_ with
  | numtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.CLZ, num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (iclz_ (sizenn (numtype_Inn Inn.I32)) v_iN)]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.CLZ, num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (iclz_ (sizenn (numtype_Inn Inn.I64)) v_iN)]
  | numtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.CTZ, num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (ictz_ (sizenn (numtype_Inn Inn.I32)) v_iN)]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.CTZ, num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (ictz_ (sizenn (numtype_Inn Inn.I64)) v_iN)]
  | numtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.POPCNT, num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (ipopcnt_ (sizenn (numtype_Inn Inn.I32)) v_iN)]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.POPCNT, num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (ipopcnt_ (sizenn (numtype_Inn Inn.I64)) v_iN)]
  | numtype.I32, unop_.mk_unop__0 Inn.I32 (unop_Inn.EXTEND v_M), num_.mk_num__0 Inn.I32 v_iN => [num_.mk_num__0 Inn.I32 (extend__ v_M (sizenn (numtype_Inn Inn.I32)) sx.S (wrap__ (sizenn (numtype_Inn Inn.I32)) v_M v_iN))]
  | numtype.I64, unop_.mk_unop__0 Inn.I64 (unop_Inn.EXTEND v_M), num_.mk_num__0 Inn.I64 v_iN => [num_.mk_num__0 Inn.I64 (extend__ v_M (sizenn (numtype_Inn Inn.I64)) sx.S (wrap__ (sizenn (numtype_Inn Inn.I64)) v_M v_iN))]
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.ABS, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_1_elem => num_.mk_num__1 Fnn.F32 iter_0_1_elem) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.ABS, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_2_elem => num_.mk_num__1 Fnn.F64 iter_0_2_elem) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEG, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_3_elem => num_.mk_num__1 Fnn.F32 iter_0_3_elem) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEG, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_4_elem => num_.mk_num__1 Fnn.F64 iter_0_4_elem) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.SQRT, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_5_elem => num_.mk_num__1 Fnn.F32 iter_0_5_elem) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.SQRT, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_6_elem => num_.mk_num__1 Fnn.F64 iter_0_6_elem) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.CEIL, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_7_elem => num_.mk_num__1 Fnn.F32 iter_0_7_elem) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.CEIL, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_8_elem => num_.mk_num__1 Fnn.F64 iter_0_8_elem) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.FLOOR, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_9_elem => num_.mk_num__1 Fnn.F32 iter_0_9_elem) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.FLOOR, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_10_elem => num_.mk_num__1 Fnn.F64 iter_0_10_elem) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.TRUNC, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_11_elem => num_.mk_num__1 Fnn.F32 iter_0_11_elem) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.TRUNC, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_12_elem => num_.mk_num__1 Fnn.F64 iter_0_12_elem) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)
  | numtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEAREST, num_.mk_num__1 Fnn.F32 v_fN => Map (fun iter_0_13_elem => num_.mk_num__1 Fnn.F32 iter_0_13_elem) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) v_fN)
  | numtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEAREST, num_.mk_num__1 Fnn.F64 v_fN => Map (fun iter_0_14_elem => num_.mk_num__1 Fnn.F64 iter_0_14_elem) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) v_fN)

inductive unop__is_wf : numtype → unop_ → num_ → List num_ → Prop where
  | unop__is_wf_0 (v_numtype : numtype) (v_unop_ : unop_) (v_num_ : num_) (ret_val_lst : List num_) : 
    wf_unop_ v_numtype v_unop_ →
    wf_num_ v_numtype v_num_ →
    ret_val_lst == (fun_unop_ v_numtype v_unop_ v_num_) →
    Forall (fun ret_val_elem => wf_num_ v_numtype ret_val_elem) ret_val_lst →
    unop__is_wf v_numtype v_unop_ v_num_ ret_val_lst


opaque fadd_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fadd__is_wf : N → fN → fN → List fN → Prop where
  | fadd__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fadd_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fadd__is_wf v_N v_fN fN_0 ret_val_lst


opaque fcopysign_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fcopysign__is_wf : N → fN → fN → List fN → Prop where
  | fcopysign__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fcopysign_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fcopysign__is_wf v_N v_fN fN_0 ret_val_lst


opaque fdiv_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fdiv__is_wf : N → fN → fN → List fN → Prop where
  | fdiv__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fdiv_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fdiv__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmax__is_wf : N → fN → fN → List fN → Prop where
  | fmax__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fmax_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fmax__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmin__is_wf : N → fN → fN → List fN → Prop where
  | fmin__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fmin_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fmin__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmul_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmul__is_wf : N → fN → fN → List fN → Prop where
  | fmul__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fmul_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fmul__is_wf v_N v_fN fN_0 ret_val_lst


opaque fsub_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsub__is_wf : N → fN → fN → List fN → Prop where
  | fsub__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fsub_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fsub__is_wf v_N v_fN fN_0 ret_val_lst


def iadd_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  .mk_uN (((proj_uN_0 v_iN) + (proj_uN_0 iN_0)) % (2 ^ v_N))

inductive iadd__is_wf : N → iN → iN → iN → Prop where
  | iadd__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (iadd_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    iadd__is_wf v_N v_iN iN_0 ret_val


opaque iand_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iand__is_wf : N → iN → iN → iN → Prop where
  | iand__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (iand_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    iand__is_wf v_N v_iN iN_0 ret_val


inductive fun_idiv_ : N → sx → iN → iN → Option iN → Prop where
  | fun_idiv__case_0 (v_N : Nat) (i_1 : uN) : fun_idiv_ v_N sx.U i_1 (.mk_uN 0) none
  | fun_idiv__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_idiv_ v_N sx.U i_1 i_2 (some (.mk_uN (Int.toNat (truncz (((proj_uN_0 i_1) : Rat) / ((proj_uN_0 i_2) : Rat))))))
  | fun_idiv__case_2 (v_N : Nat) (i_1 : uN) : fun_idiv_ v_N sx.S i_1 (.mk_uN 0) none
  | fun_idiv__case_3 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    ((var_0 : Rat) / (var_1 : Rat)) == ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Rat) →
    fun_idiv_ v_N sx.S i_1 i_2 none
  | fun_idiv__case_4 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (truncz ((var_1 : Rat) / (var_2 : Rat))) var_0 →
    fun_idiv_ v_N sx.S i_1 i_2 (some (.mk_uN var_0))


inductive idiv__is_wf : N → sx → iN → iN → Option iN → Prop where
  | idiv__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) : 
    fun_idiv_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val_opt == var_0 →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    idiv__is_wf v_N v_sx v_iN iN_0 ret_val_opt


def imul_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  .mk_uN (((proj_uN_0 v_iN) * (proj_uN_0 iN_0)) % (2 ^ v_N))

inductive imul__is_wf : N → iN → iN → iN → Prop where
  | imul__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (imul_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    imul__is_wf v_N v_iN iN_0 ret_val


opaque ior_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ior__is_wf : N → iN → iN → iN → Prop where
  | ior__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (ior_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    ior__is_wf v_N v_iN iN_0 ret_val


inductive fun_irem_ : N → sx → iN → iN → Option iN → Prop where
  | fun_irem__case_0 (v_N : Nat) (i_1 : uN) : fun_irem_ v_N sx.U i_1 (.mk_uN 0) none
  | fun_irem__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_irem_ v_N sx.U i_1 i_2 (some (.mk_uN (Int.toNat (((proj_uN_0 i_1) : Int) - (((proj_uN_0 i_2) * (Int.toNat (truncz (((proj_uN_0 i_1) : Rat) / ((proj_uN_0 i_2) : Rat))))) : Int)))))
  | fun_irem__case_2 (v_N : Nat) (i_1 : uN) : fun_irem_ v_N sx.S i_1 (.mk_uN 0) none
  | fun_irem__case_3 (v_N : Nat) (i_1 : uN) (i_2 : uN) (j_1 : Int) (j_2 : Int) (var_2 : Int) (var_1 : Int) (var_0 : Nat) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (j_1 - (j_2 * (truncz ((j_1 : Rat) / (j_2 : Rat))))) var_0 →
    (j_1 == var_1) && (j_2 == var_2) →
    fun_irem_ v_N sx.S i_1 i_2 (some (.mk_uN var_0))


inductive irem__is_wf : N → sx → iN → iN → Option iN → Prop where
  | irem__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) : 
    fun_irem_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val_opt == var_0 →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    irem__is_wf v_N v_sx v_iN iN_0 ret_val_opt


opaque irotl_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irotl__is_wf : N → iN → iN → iN → Prop where
  | irotl__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (irotl_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    irotl__is_wf v_N v_iN iN_0 ret_val


opaque irotr_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irotr__is_wf : N → iN → iN → iN → Prop where
  | irotr__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (irotr_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    irotr__is_wf v_N v_iN iN_0 ret_val


opaque ishl_ (v_N : N) (v_iN : iN) (v_u32 : u32) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ishl__is_wf : N → iN → u32 → iN → Prop where
  | ishl__is_wf_0 (v_N : N) (v_iN : iN) (v_u32 : u32) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN 32 v_u32 →
    ret_val == (ishl_ v_N v_iN v_u32) →
    wf_uN v_N ret_val →
    ishl__is_wf v_N v_iN v_u32 ret_val


opaque ishr_ (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ishr__is_wf : N → sx → iN → u32 → iN → Prop where
  | ishr__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN 32 v_u32 →
    ret_val == (ishr_ v_N v_sx v_iN v_u32) →
    wf_uN v_N ret_val →
    ishr__is_wf v_N v_sx v_iN v_u32 ret_val


def isub_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  .mk_uN (Int.toNat (((((2 ^ v_N) + (proj_uN_0 v_iN)) : Int) - ((proj_uN_0 iN_0) : Int)) % ((2 ^ v_N) : Int)))

inductive isub__is_wf : N → iN → iN → iN → Prop where
  | isub__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (isub_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    isub__is_wf v_N v_iN iN_0 ret_val


opaque ixor_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ixor__is_wf : N → iN → iN → iN → Prop where
  | ixor__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (ixor_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    ixor__is_wf v_N v_iN iN_0 ret_val


inductive fun_binop_ : numtype → binop_ → num_ → num_ → List num_ → Prop where
  | fun_binop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ADD) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (iadd_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ADD) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (iadd_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.SUB) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (isub_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.SUB) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (isub_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_4 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.MUL) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (imul_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_5 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.MUL) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (imul_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_idiv_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.DIV v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (list_ num_ (OMap (fun iter_0_15_elem => num_.mk_num__0 Inn.I32 iter_0_15_elem) var_0))
  | fun_binop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_idiv_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.DIV v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (list_ num_ (OMap (fun iter_0_16_elem => num_.mk_num__0 Inn.I64 iter_0_16_elem) var_0))
  | fun_binop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_irem_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.REM v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (list_ num_ (OMap (fun iter_0_17_elem => num_.mk_num__0 Inn.I32 iter_0_17_elem) var_0))
  | fun_binop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_irem_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.REM v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (list_ num_ (OMap (fun iter_0_18_elem => num_.mk_num__0 Inn.I64 iter_0_18_elem) var_0))
  | fun_binop__case_10 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.AND) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (iand_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_11 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.AND) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (iand_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_12 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.OR) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ior_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_13 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.OR) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ior_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_14 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.XOR) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ixor_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_15 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.XOR) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ixor_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_16 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.SHL) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ishl_ (sizenn (numtype_Inn Inn.I32)) iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_17 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.SHL) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ishl_ (sizenn (numtype_Inn Inn.I64)) iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_18 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.SHR v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (ishr_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_19 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.SHR v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (ishr_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_20 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ROTL) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (irotl_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_21 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ROTL) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (irotl_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_22 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ROTR) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) [num_.mk_num__0 Inn.I32 (irotr_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_23 (iN_1 : uN) (iN_2 : uN) : fun_binop_ numtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ROTR) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) [num_.mk_num__0 Inn.I64 (irotr_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_24 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.ADD) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_19_elem => num_.mk_num__1 Fnn.F32 iter_0_19_elem) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_25 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.ADD) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_20_elem => num_.mk_num__1 Fnn.F64 iter_0_20_elem) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_26 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.SUB) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_21_elem => num_.mk_num__1 Fnn.F32 iter_0_21_elem) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_27 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.SUB) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_22_elem => num_.mk_num__1 Fnn.F64 iter_0_22_elem) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_28 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MUL) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_23_elem => num_.mk_num__1 Fnn.F32 iter_0_23_elem) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_29 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MUL) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_24_elem => num_.mk_num__1 Fnn.F64 iter_0_24_elem) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_30 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.DIV) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_25_elem => num_.mk_num__1 Fnn.F32 iter_0_25_elem) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_31 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.DIV) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_26_elem => num_.mk_num__1 Fnn.F64 iter_0_26_elem) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_32 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MIN) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_27_elem => num_.mk_num__1 Fnn.F32 iter_0_27_elem) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_33 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MIN) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_28_elem => num_.mk_num__1 Fnn.F64 iter_0_28_elem) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_34 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MAX) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_29_elem => num_.mk_num__1 Fnn.F32 iter_0_29_elem) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_35 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MAX) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_30_elem => num_.mk_num__1 Fnn.F64 iter_0_30_elem) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_binop__case_36 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.COPYSIGN) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (Map (fun iter_0_31_elem => num_.mk_num__1 Fnn.F32 iter_0_31_elem) (fcopysign_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_binop__case_37 (fN_1 : fN) (fN_2 : fN) : fun_binop_ numtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.COPYSIGN) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (Map (fun iter_0_32_elem => num_.mk_num__1 Fnn.F64 iter_0_32_elem) (fcopysign_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))


inductive binop__is_wf : numtype → binop_ → num_ → num_ → List num_ → Prop where
  | binop__is_wf_0 (v_numtype : numtype) (v_binop_ : binop_) (v_num_ : num_) (num__0 : num_) (ret_val_lst : List num_) (var_0 : List num_) : 
    fun_binop_ v_numtype v_binop_ v_num_ num__0 var_0 →
    wf_binop_ v_numtype v_binop_ →
    wf_num_ v_numtype v_num_ →
    wf_num_ v_numtype num__0 →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_num_ v_numtype ret_val_elem) ret_val_lst →
    binop__is_wf v_numtype v_binop_ v_num_ num__0 ret_val_lst


def ieqz_ (v_N : N) (v_iN : iN) : u32 :=
  .mk_uN (nat_of_bool ((proj_uN_0 v_iN) == 0))

inductive ieqz__is_wf : N → iN → u32 → Prop where
  | ieqz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) : 
    wf_uN v_N v_iN →
    ret_val == (ieqz_ v_N v_iN) →
    wf_uN 32 ret_val →
    ieqz__is_wf v_N v_iN ret_val


def fun_testop_ (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) : num_ :=
  match v_numtype, v_testop_, v_num_ with
  | numtype.I32, testop_.mk_testop__0 Inn.I32 testop_Inn.EQZ, num_.mk_num__0 Inn.I32 v_iN => num_.mk_num__0 Inn.I32 (ieqz_ (sizenn (numtype_Inn Inn.I32)) v_iN)
  | numtype.I64, testop_.mk_testop__0 Inn.I64 testop_Inn.EQZ, num_.mk_num__0 Inn.I64 v_iN => num_.mk_num__0 Inn.I32 (ieqz_ (sizenn (numtype_Inn Inn.I64)) v_iN)

inductive testop__is_wf : numtype → testop_ → num_ → num_ → Prop where
  | testop__is_wf_0 (v_numtype : numtype) (v_testop_ : testop_) (v_num_ : num_) (ret_val : num_) : 
    wf_testop_ v_numtype v_testop_ →
    wf_num_ v_numtype v_num_ →
    ret_val == (fun_testop_ v_numtype v_testop_ v_num_) →
    wf_num_ numtype.I32 ret_val →
    testop__is_wf v_numtype v_testop_ v_num_ ret_val


opaque feq_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive feq__is_wf : N → fN → fN → u32 → Prop where
  | feq__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val == (feq_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    feq__is_wf v_N v_fN fN_0 ret_val


opaque fge_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fge__is_wf : N → fN → fN → u32 → Prop where
  | fge__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val == (fge_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fge__is_wf v_N v_fN fN_0 ret_val


opaque fgt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fgt__is_wf : N → fN → fN → u32 → Prop where
  | fgt__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val == (fgt_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fgt__is_wf v_N v_fN fN_0 ret_val


opaque fle_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fle__is_wf : N → fN → fN → u32 → Prop where
  | fle__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val == (fle_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fle__is_wf v_N v_fN fN_0 ret_val


opaque flt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive flt__is_wf : N → fN → fN → u32 → Prop where
  | flt__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val == (flt_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    flt__is_wf v_N v_fN fN_0 ret_val


opaque fne_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fne__is_wf : N → fN → fN → u32 → Prop where
  | fne__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val == (fne_ v_N v_fN fN_0) →
    wf_uN 32 ret_val →
    fne__is_wf v_N v_fN fN_0 ret_val


def ieq_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  .mk_uN (nat_of_bool (v_iN == iN_0))

inductive ieq__is_wf : N → iN → iN → u32 → Prop where
  | ieq__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (ieq_ v_N v_iN iN_0) →
    wf_uN 32 ret_val →
    ieq__is_wf v_N v_iN iN_0 ret_val


inductive fun_ige_ : N → sx → iN → iN → u32 → Prop where
  | fun_ige__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ige_ v_N sx.U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) ≥ (proj_uN_0 i_2))))
  | fun_ige__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_ige_ v_N sx.S i_1 i_2 (.mk_uN (nat_of_bool (var_0 ≥ var_1)))


inductive ige__is_wf : N → sx → iN → iN → u32 → Prop where
  | ige__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : 
    fun_ige_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN 32 ret_val →
    ige__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_igt_ : N → sx → iN → iN → u32 → Prop where
  | fun_igt__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_igt_ v_N sx.U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))
  | fun_igt__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_igt_ v_N sx.S i_1 i_2 (.mk_uN (nat_of_bool (var_0 > var_1)))


inductive igt__is_wf : N → sx → iN → iN → u32 → Prop where
  | igt__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : 
    fun_igt_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN 32 ret_val →
    igt__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_ile_ : N → sx → iN → iN → u32 → Prop where
  | fun_ile__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ile_ v_N sx.U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) ≤ (proj_uN_0 i_2))))
  | fun_ile__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_ile_ v_N sx.S i_1 i_2 (.mk_uN (nat_of_bool (var_0 ≤ var_1)))


inductive ile__is_wf : N → sx → iN → iN → u32 → Prop where
  | ile__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : 
    fun_ile_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN 32 ret_val →
    ile__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_ilt_ : N → sx → iN → iN → u32 → Prop where
  | fun_ilt__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ilt_ v_N sx.U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))
  | fun_ilt__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_ilt_ v_N sx.S i_1 i_2 (.mk_uN (nat_of_bool (var_0 < var_1)))


inductive ilt__is_wf : N → sx → iN → iN → u32 → Prop where
  | ilt__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : 
    fun_ilt_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN 32 ret_val →
    ilt__is_wf v_N v_sx v_iN iN_0 ret_val


def ine_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  .mk_uN (nat_of_bool (v_iN != iN_0))

inductive ine__is_wf : N → iN → iN → u32 → Prop where
  | ine__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (ine_ v_N v_iN iN_0) →
    wf_uN 32 ret_val →
    ine__is_wf v_N v_iN iN_0 ret_val


inductive fun_relop_ : numtype → relop_ → num_ → num_ → num_ → Prop where
  | fun_relop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 relop_Inn.EQ) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 (ieq_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2))
  | fun_relop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 relop_Inn.EQ) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 (ieq_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2))
  | fun_relop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 relop_Inn.NE) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 (ine_ (sizenn (numtype_Inn Inn.I32)) iN_1 iN_2))
  | fun_relop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 relop_Inn.NE) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 (ine_ (sizenn (numtype_Inn Inn.I64)) iN_1 iN_2))
  | fun_relop__case_4 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ilt_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.LT v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_5 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ilt_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.LT v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_igt_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.GT v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_igt_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.GT v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ile_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.LE v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ile_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.LE v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_10 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ige_ (sizenn (numtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.GE v_sx)) (num_.mk_num__0 Inn.I32 iN_1) (num_.mk_num__0 Inn.I32 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_11 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ige_ (sizenn (numtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ numtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.GE v_sx)) (num_.mk_num__0 Inn.I64 iN_1) (num_.mk_num__0 Inn.I64 iN_2) (num_.mk_num__0 Inn.I32 var_0)
  | fun_relop__case_12 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.EQ) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (feq_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_13 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.EQ) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (feq_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_14 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.NE) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fne_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_15 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.NE) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fne_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_16 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.LT) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (flt_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_17 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.LT) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (flt_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_18 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.GT) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fgt_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_19 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.GT) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fgt_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_20 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.LE) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fle_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_21 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.LE) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fle_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_22 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.GE) (num_.mk_num__1 Fnn.F32 fN_1) (num_.mk_num__1 Fnn.F32 fN_2) (num_.mk_num__0 Inn.I32 (fge_ (sizenn (numtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_23 (fN_1 : fN) (fN_2 : fN) : fun_relop_ numtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.GE) (num_.mk_num__1 Fnn.F64 fN_1) (num_.mk_num__1 Fnn.F64 fN_2) (num_.mk_num__0 Inn.I32 (fge_ (sizenn (numtype_Fnn Fnn.F64)) fN_1 fN_2))


inductive relop__is_wf : numtype → relop_ → num_ → num_ → num_ → Prop where
  | relop__is_wf_0 (v_numtype : numtype) (v_relop_ : relop_) (v_num_ : num_) (num__0 : num_) (ret_val : num_) (var_0 : num_) : 
    fun_relop_ v_numtype v_relop_ v_num_ num__0 var_0 →
    wf_relop_ v_numtype v_relop_ →
    wf_num_ v_numtype v_num_ →
    wf_num_ v_numtype num__0 →
    ret_val == var_0 →
    wf_num_ numtype.I32 ret_val →
    relop__is_wf v_numtype v_relop_ v_num_ num__0 ret_val


opaque convert__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive convert___is_wf : M → N → sx → iN → fN → Prop where
  | convert___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : fN) : 
    wf_uN v_M v_iN →
    ret_val == (convert__ v_M v_N v_sx v_iN) →
    wf_fN v_N ret_val →
    convert___is_wf v_M v_N v_sx v_iN ret_val


opaque demote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive demote___is_wf : M → N → fN → List fN → Prop where
  | demote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_M v_fN →
    ret_val_lst == (demote__ v_M v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    demote___is_wf v_M v_N v_fN ret_val_lst


opaque promote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive promote___is_wf : M → N → fN → List fN → Prop where
  | promote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_M v_fN →
    ret_val_lst == (promote__ v_M v_N v_fN) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    promote___is_wf v_M v_N v_fN ret_val_lst


opaque reinterpret__ (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) : num_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive reinterpret___is_wf : numtype → numtype → num_ → num_ → Prop where
  | reinterpret___is_wf_0 (numtype_1 : numtype) (numtype_2 : numtype) (v_num_ : num_) (ret_val : num_) : 
    wf_num_ numtype_1 v_num_ →
    ret_val == (reinterpret__ numtype_1 numtype_2 v_num_) →
    wf_num_ numtype_2 ret_val →
    reinterpret___is_wf numtype_1 numtype_2 v_num_ ret_val


opaque trunc__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive trunc___is_wf : M → N → sx → fN → Option iN → Prop where
  | trunc___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) : 
    wf_fN v_M v_fN →
    ret_val_opt == (trunc__ v_M v_N v_sx v_fN) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    trunc___is_wf v_M v_N v_sx v_fN ret_val_opt


opaque trunc_sat__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive trunc_sat___is_wf : M → N → sx → fN → Option iN → Prop where
  | trunc_sat___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) : 
    wf_fN v_M v_fN →
    ret_val_opt == (trunc_sat__ v_M v_N v_sx v_fN) →
    Forall (fun ret_val_elem => wf_uN v_N ret_val_elem) (Option.toList ret_val_opt) →
    trunc_sat___is_wf v_M v_N v_sx v_fN ret_val_opt


inductive fun_cvtop__ : numtype → numtype → cvtop → num_ → List num_ → Prop where
  | fun_cvtop___case_0 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I32 (cvtop.EXTEND v_sx) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I32 (extend__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I32)) v_sx iN_1)]
  | fun_cvtop___case_1 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I32 (cvtop.EXTEND v_sx) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I32 (extend__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I32)) v_sx iN_1)]
  | fun_cvtop___case_2 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I64 (cvtop.EXTEND v_sx) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I64 (extend__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I64)) v_sx iN_1)]
  | fun_cvtop___case_3 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I64 (cvtop.EXTEND v_sx) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I64 (extend__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I64)) v_sx iN_1)]
  | fun_cvtop___case_4 (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I32 cvtop.WRAP (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I32 (wrap__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I32)) iN_1)]
  | fun_cvtop___case_5 (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I32 cvtop.WRAP (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I32 (wrap__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I32)) iN_1)]
  | fun_cvtop___case_6 (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.I64 cvtop.WRAP (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__0 Inn.I64 (wrap__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Inn Inn.I64)) iN_1)]
  | fun_cvtop___case_7 (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.I64 cvtop.WRAP (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__0 Inn.I64 (wrap__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Inn Inn.I64)) iN_1)]
  | fun_cvtop___case_8 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I32 (cvtop.TRUNC v_sx) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun iter_0_33_elem => num_.mk_num__0 Inn.I32 iter_0_33_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_9 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I32 (cvtop.TRUNC v_sx) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun iter_0_34_elem => num_.mk_num__0 Inn.I32 iter_0_34_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_10 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I64 (cvtop.TRUNC v_sx) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun iter_0_35_elem => num_.mk_num__0 Inn.I64 iter_0_35_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_11 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I64 (cvtop.TRUNC v_sx) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun iter_0_36_elem => num_.mk_num__0 Inn.I64 iter_0_36_elem) (trunc__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_12 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I32 (cvtop.TRUNC_SAT v_sx) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun iter_0_37_elem => num_.mk_num__0 Inn.I32 iter_0_37_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_13 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I32 (cvtop.TRUNC_SAT v_sx) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun iter_0_38_elem => num_.mk_num__0 Inn.I32 iter_0_38_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I32)) v_sx fN_1)))
  | fun_cvtop___case_14 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.I64 (cvtop.TRUNC_SAT v_sx) (num_.mk_num__1 Fnn.F32 fN_1) (list_ num_ (OMap (fun iter_0_39_elem => num_.mk_num__0 Inn.I64 iter_0_39_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_15 (v_sx : sx) (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.I64 (cvtop.TRUNC_SAT v_sx) (num_.mk_num__1 Fnn.F64 fN_1) (list_ num_ (OMap (fun iter_0_40_elem => num_.mk_num__0 Inn.I64 iter_0_40_elem) (trunc_sat__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Inn Inn.I64)) v_sx fN_1)))
  | fun_cvtop___case_16 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.F32 (cvtop.CONVERT v_sx) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__1 Fnn.F32 (convert__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Fnn Fnn.F32)) v_sx iN_1)]
  | fun_cvtop___case_17 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.F32 (cvtop.CONVERT v_sx) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__1 Fnn.F32 (convert__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Fnn Fnn.F32)) v_sx iN_1)]
  | fun_cvtop___case_18 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I32 numtype.F64 (cvtop.CONVERT v_sx) (num_.mk_num__0 Inn.I32 iN_1) [num_.mk_num__1 Fnn.F64 (convert__ (sizenn1 (numtype_Inn Inn.I32)) (sizenn2 (numtype_Fnn Fnn.F64)) v_sx iN_1)]
  | fun_cvtop___case_19 (v_sx : sx) (iN_1 : uN) : fun_cvtop__ numtype.I64 numtype.F64 (cvtop.CONVERT v_sx) (num_.mk_num__0 Inn.I64 iN_1) [num_.mk_num__1 Fnn.F64 (convert__ (sizenn1 (numtype_Inn Inn.I64)) (sizenn2 (numtype_Fnn Fnn.F64)) v_sx iN_1)]
  | fun_cvtop___case_20 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F32 cvtop.PROMOTE (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun iter_0_41_elem => num_.mk_num__1 Fnn.F32 iter_0_41_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_21 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F32 cvtop.PROMOTE (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun iter_0_42_elem => num_.mk_num__1 Fnn.F32 iter_0_42_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_22 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F64 cvtop.PROMOTE (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun iter_0_43_elem => num_.mk_num__1 Fnn.F64 iter_0_43_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_23 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F64 cvtop.PROMOTE (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun iter_0_44_elem => num_.mk_num__1 Fnn.F64 iter_0_44_elem) (promote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_24 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F32 cvtop.DEMOTE (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun iter_0_45_elem => num_.mk_num__1 Fnn.F32 iter_0_45_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_25 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F32 cvtop.DEMOTE (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun iter_0_46_elem => num_.mk_num__1 Fnn.F32 iter_0_46_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F32)) fN_1))
  | fun_cvtop___case_26 (fN_1 : fN) : fun_cvtop__ numtype.F32 numtype.F64 cvtop.DEMOTE (num_.mk_num__1 Fnn.F32 fN_1) (Map (fun iter_0_47_elem => num_.mk_num__1 Fnn.F64 iter_0_47_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F32)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_27 (fN_1 : fN) : fun_cvtop__ numtype.F64 numtype.F64 cvtop.DEMOTE (num_.mk_num__1 Fnn.F64 fN_1) (Map (fun iter_0_48_elem => num_.mk_num__1 Fnn.F64 iter_0_48_elem) (demote__ (sizenn1 (numtype_Fnn Fnn.F64)) (sizenn2 (numtype_Fnn Fnn.F64)) fN_1))
  | fun_cvtop___case_28 (iN_1 : uN) : 
    (size (valtype_Inn Inn.I32)) != none →
    (size (valtype_Fnn Fnn.F32)) != none →
    (Option.get! (size (valtype_Inn Inn.I32))) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    fun_cvtop__ numtype.I32 numtype.F32 cvtop.REINTERPRET (num_.mk_num__0 Inn.I32 iN_1) [reinterpret__ (numtype_Inn Inn.I32) (numtype_Fnn Fnn.F32) (num_.mk_num__0 Inn.I32 iN_1)]
  | fun_cvtop___case_29 (iN_1 : uN) : 
    (size (valtype_Inn Inn.I64)) != none →
    (size (valtype_Fnn Fnn.F32)) != none →
    (Option.get! (size (valtype_Inn Inn.I64))) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    fun_cvtop__ numtype.I64 numtype.F32 cvtop.REINTERPRET (num_.mk_num__0 Inn.I64 iN_1) [reinterpret__ (numtype_Inn Inn.I64) (numtype_Fnn Fnn.F32) (num_.mk_num__0 Inn.I64 iN_1)]
  | fun_cvtop___case_30 (iN_1 : uN) : 
    (size (valtype_Inn Inn.I32)) != none →
    (size (valtype_Fnn Fnn.F64)) != none →
    (Option.get! (size (valtype_Inn Inn.I32))) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    fun_cvtop__ numtype.I32 numtype.F64 cvtop.REINTERPRET (num_.mk_num__0 Inn.I32 iN_1) [reinterpret__ (numtype_Inn Inn.I32) (numtype_Fnn Fnn.F64) (num_.mk_num__0 Inn.I32 iN_1)]
  | fun_cvtop___case_31 (iN_1 : uN) : 
    (size (valtype_Inn Inn.I64)) != none →
    (size (valtype_Fnn Fnn.F64)) != none →
    (Option.get! (size (valtype_Inn Inn.I64))) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    fun_cvtop__ numtype.I64 numtype.F64 cvtop.REINTERPRET (num_.mk_num__0 Inn.I64 iN_1) [reinterpret__ (numtype_Inn Inn.I64) (numtype_Fnn Fnn.F64) (num_.mk_num__0 Inn.I64 iN_1)]
  | fun_cvtop___case_32 (fN_1 : fN) : 
    (size (valtype_Fnn Fnn.F32)) != none →
    (size (valtype_Inn Inn.I32)) != none →
    (Option.get! (size (valtype_Fnn Fnn.F32))) == (Option.get! (size (valtype_Inn Inn.I32))) →
    fun_cvtop__ numtype.F32 numtype.I32 cvtop.REINTERPRET (num_.mk_num__1 Fnn.F32 fN_1) [reinterpret__ (numtype_Fnn Fnn.F32) (numtype_Inn Inn.I32) (num_.mk_num__1 Fnn.F32 fN_1)]
  | fun_cvtop___case_33 (fN_1 : fN) : 
    (size (valtype_Fnn Fnn.F64)) != none →
    (size (valtype_Inn Inn.I32)) != none →
    (Option.get! (size (valtype_Fnn Fnn.F64))) == (Option.get! (size (valtype_Inn Inn.I32))) →
    fun_cvtop__ numtype.F64 numtype.I32 cvtop.REINTERPRET (num_.mk_num__1 Fnn.F64 fN_1) [reinterpret__ (numtype_Fnn Fnn.F64) (numtype_Inn Inn.I32) (num_.mk_num__1 Fnn.F64 fN_1)]
  | fun_cvtop___case_34 (fN_1 : fN) : 
    (size (valtype_Fnn Fnn.F32)) != none →
    (size (valtype_Inn Inn.I64)) != none →
    (Option.get! (size (valtype_Fnn Fnn.F32))) == (Option.get! (size (valtype_Inn Inn.I64))) →
    fun_cvtop__ numtype.F32 numtype.I64 cvtop.REINTERPRET (num_.mk_num__1 Fnn.F32 fN_1) [reinterpret__ (numtype_Fnn Fnn.F32) (numtype_Inn Inn.I64) (num_.mk_num__1 Fnn.F32 fN_1)]
  | fun_cvtop___case_35 (fN_1 : fN) : 
    (size (valtype_Fnn Fnn.F64)) != none →
    (size (valtype_Inn Inn.I64)) != none →
    (Option.get! (size (valtype_Fnn Fnn.F64))) == (Option.get! (size (valtype_Inn Inn.I64))) →
    fun_cvtop__ numtype.F64 numtype.I64 cvtop.REINTERPRET (num_.mk_num__1 Fnn.F64 fN_1) [reinterpret__ (numtype_Fnn Fnn.F64) (numtype_Inn Inn.I64) (num_.mk_num__1 Fnn.F64 fN_1)]


inductive cvtop___is_wf : numtype → numtype → cvtop → num_ → List num_ → Prop where
  | cvtop___is_wf_0 (numtype_1 : numtype) (numtype_2 : numtype) (v_cvtop : cvtop) (v_num_ : num_) (ret_val_lst : List num_) (var_0 : List num_) : 
    fun_cvtop__ numtype_1 numtype_2 v_cvtop v_num_ var_0 →
    wf_num_ numtype_1 v_num_ →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_num_ numtype_2 ret_val_elem) ret_val_lst →
    cvtop___is_wf numtype_1 numtype_2 v_cvtop v_num_ ret_val_lst


opaque narrow__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive narrow___is_wf : M → N → sx → iN → iN → Prop where
  | narrow___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_M v_iN →
    ret_val == (narrow__ v_M v_N v_sx v_iN) →
    wf_uN v_N ret_val →
    narrow___is_wf v_M v_N v_sx v_iN ret_val


opaque ibits_ (v_N : N) (v_iN : iN) : List bit := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibits__is_wf : N → iN → List bit → Prop where
  | ibits__is_wf_0 (v_N : N) (v_iN : iN) (ret_val_lst : List bit) : 
    wf_uN v_N v_iN →
    ret_val_lst == (ibits_ v_N v_iN) →
    Forall (fun ret_val_elem => wf_bit ret_val_elem) ret_val_lst →
    ibits__is_wf v_N v_iN ret_val_lst


opaque fbits_ (v_N : N) (v_fN : fN) : List bit := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fbits__is_wf : N → fN → List bit → Prop where
  | fbits__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List bit) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fbits_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_bit ret_val_elem) ret_val_lst →
    fbits__is_wf v_N v_fN ret_val_lst


opaque ibytes_ (v_N : N) (v_iN : iN) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibytes__is_wf : N → iN → List byte → Prop where
  | ibytes__is_wf_0 (v_N : N) (v_iN : iN) (ret_val_lst : List byte) : 
    wf_uN v_N v_iN →
    ret_val_lst == (ibytes_ v_N v_iN) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    ibytes__is_wf v_N v_iN ret_val_lst


opaque fbytes_ (v_N : N) (v_fN : fN) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fbytes__is_wf : N → fN → List byte → Prop where
  | fbytes__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List byte) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fbytes_ v_N v_fN) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    fbytes__is_wf v_N v_fN ret_val_lst


opaque nbytes_ (v_numtype : numtype) (v_num_ : num_) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive nbytes__is_wf : numtype → num_ → List byte → Prop where
  | nbytes__is_wf_0 (v_numtype : numtype) (v_num_ : num_) (ret_val_lst : List byte) : 
    wf_num_ v_numtype v_num_ →
    ret_val_lst == (nbytes_ v_numtype v_num_) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    nbytes__is_wf v_numtype v_num_ ret_val_lst


opaque vbytes_ (v_vectype : vectype) (v_vec_ : vec_) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive vbytes__is_wf : vectype → vec_ → List byte → Prop where
  | vbytes__is_wf_0 (v_vectype : vectype) (v_vec_ : vec_) (ret_val_lst : List byte) : 
    (size (valtype_vectype v_vectype)) != none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
    ret_val_lst == (vbytes_ v_vectype v_vec_) →
    Forall (fun ret_val_elem => wf_byte ret_val_elem) ret_val_lst →
    vbytes__is_wf v_vectype v_vec_ ret_val_lst


opaque inv_ibits_ (v_N : N) (var_0_lst : List bit) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_ibits__is_wf : N → List bit → iN → Prop where
  | inv_ibits__is_wf_0 (v_N : N) (var_0_lst : List bit) (ret_val : iN) : 
    Forall (fun var_0_elem => wf_bit var_0_elem) var_0_lst →
    ret_val == (inv_ibits_ v_N var_0_lst) →
    wf_uN v_N ret_val →
    inv_ibits__is_wf v_N var_0_lst ret_val


opaque inv_fbits_ (v_N : N) (var_0_lst : List bit) : fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_fbits__is_wf : N → List bit → fN → Prop where
  | inv_fbits__is_wf_0 (v_N : N) (var_0_lst : List bit) (ret_val : fN) : 
    Forall (fun var_0_elem => wf_bit var_0_elem) var_0_lst →
    ret_val == (inv_fbits_ v_N var_0_lst) →
    wf_fN v_N ret_val →
    inv_fbits__is_wf v_N var_0_lst ret_val


opaque inv_ibytes_ (v_N : N) (var_0_lst : List byte) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_ibytes__is_wf : N → List byte → iN → Prop where
  | inv_ibytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : iN) : 
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val == (inv_ibytes_ v_N var_0_lst) →
    wf_uN v_N ret_val →
    inv_ibytes__is_wf v_N var_0_lst ret_val


opaque inv_fbytes_ (v_N : N) (var_0_lst : List byte) : fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_fbytes__is_wf : N → List byte → fN → Prop where
  | inv_fbytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : fN) : 
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val == (inv_fbytes_ v_N var_0_lst) →
    wf_fN v_N ret_val →
    inv_fbytes__is_wf v_N var_0_lst ret_val


opaque inv_nbytes_ (v_numtype : numtype) (var_0_lst : List byte) : num_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_nbytes__is_wf : numtype → List byte → num_ → Prop where
  | inv_nbytes__is_wf_0 (v_numtype : numtype) (var_0_lst : List byte) (ret_val : num_) : 
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val == (inv_nbytes_ v_numtype var_0_lst) →
    wf_num_ v_numtype ret_val →
    inv_nbytes__is_wf v_numtype var_0_lst ret_val


opaque inv_vbytes_ (v_vectype : vectype) (var_0_lst : List byte) : vec_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_vbytes__is_wf : vectype → List byte → vec_ → Prop where
  | inv_vbytes__is_wf_0 (v_vectype : vectype) (var_0_lst : List byte) (ret_val : vec_) : 
    Forall (fun var_0_elem => wf_byte var_0_elem) var_0_lst →
    ret_val == (inv_vbytes_ v_vectype var_0_lst) →
    (size (valtype_vectype v_vectype)) != none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val →
    inv_vbytes__is_wf v_vectype var_0_lst ret_val


opaque inot_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inot__is_wf : N → iN → iN → Prop where
  | inot__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    ret_val == (inot_ v_N v_iN) →
    wf_uN v_N ret_val →
    inot__is_wf v_N v_iN ret_val


opaque irev_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irev__is_wf : N → iN → iN → Prop where
  | irev__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    ret_val == (irev_ v_N v_iN) →
    wf_uN v_N ret_val →
    irev__is_wf v_N v_iN ret_val


opaque iandnot_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iandnot__is_wf : N → iN → iN → iN → Prop where
  | iandnot__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (iandnot_ v_N v_iN iN_0) →
    wf_uN v_N ret_val →
    iandnot__is_wf v_N v_iN iN_0 ret_val


def inez_ (v_N : N) (v_iN : iN) : u32 :=
  .mk_uN (nat_of_bool ((proj_uN_0 v_iN) != 0))

inductive inez__is_wf : N → iN → u32 → Prop where
  | inez__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) : 
    wf_uN v_N v_iN →
    ret_val == (inez_ v_N v_iN) →
    wf_uN 32 ret_val →
    inez__is_wf v_N v_iN ret_val


opaque ibitselect_ (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibitselect__is_wf : N → iN → iN → iN → iN → Prop where
  | ibitselect__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (iN_1 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    wf_uN v_N iN_1 →
    ret_val == (ibitselect_ v_N v_iN iN_0 iN_1) →
    wf_uN v_N ret_val →
    ibitselect__is_wf v_N v_iN iN_0 iN_1 ret_val


def ineg_ (v_N : N) (v_iN : iN) : iN :=
  .mk_uN (Int.toNat ((((2 ^ v_N) : Int) - ((proj_uN_0 v_iN) : Int)) % ((2 ^ v_N) : Int)))

inductive ineg__is_wf : N → iN → iN → Prop where
  | ineg__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    ret_val == (ineg_ v_N v_iN) →
    wf_uN v_N ret_val →
    ineg__is_wf v_N v_iN ret_val


inductive fun_iabs_ : N → iN → iN → Prop where
  | fun_iabs__case_0 (v_N : Nat) (i_1 : uN) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_iabs_ v_N i_1 (if var_0 ≥ (0 : Int) then i_1 else ineg_ v_N i_1)


inductive iabs__is_wf : N → iN → iN → Prop where
  | iabs__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) (var_0 : iN) : 
    fun_iabs_ v_N v_iN var_0 →
    wf_uN v_N v_iN →
    ret_val == var_0 →
    wf_uN v_N ret_val →
    iabs__is_wf v_N v_iN ret_val


inductive fun_imin_ : N → sx → iN → iN → iN → Prop where
  | fun_imin__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : 
    (proj_uN_0 i_1) ≤ (proj_uN_0 i_2) →
    fun_imin_ v_N sx.U i_1 i_2 i_1
  | fun_imin__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : 
    (proj_uN_0 i_1) > (proj_uN_0 i_2) →
    fun_imin_ v_N sx.U i_1 i_2 i_2
  | fun_imin__case_2 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_imin_ v_N sx.S i_1 i_2 (if var_0 ≤ var_1 then i_1 else i_2)


inductive imin__is_wf : N → sx → iN → iN → iN → Prop where
  | imin__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) : 
    fun_imin_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN v_N ret_val →
    imin__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_imax_ : N → sx → iN → iN → iN → Prop where
  | fun_imax__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : 
    (proj_uN_0 i_1) ≥ (proj_uN_0 i_2) →
    fun_imax_ v_N sx.U i_1 i_2 i_1
  | fun_imax__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : 
    (proj_uN_0 i_1) < (proj_uN_0 i_2) →
    fun_imax_ v_N sx.U i_1 i_2 i_2
  | fun_imax__case_2 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_1 →
    fun_signed_ v_N (proj_uN_0 i_1) var_0 →
    fun_imax_ v_N sx.S i_1 i_2 (if var_0 ≥ var_1 then i_1 else i_2)


inductive imax__is_wf : N → sx → iN → iN → iN → Prop where
  | imax__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) : 
    fun_imax_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN v_N ret_val →
    imax__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_iadd_sat_ : N → sx → iN → iN → iN → Prop where
  | fun_iadd_sat__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_iadd_sat_ v_N sx.U i_1 i_2 (.mk_uN (sat_u_ v_N (((proj_uN_0 i_1) + (proj_uN_0 i_2)) : Int)))
  | fun_iadd_sat__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (sat_s_ v_N (var_1 + var_2)) var_0 →
    fun_iadd_sat_ v_N sx.S i_1 i_2 (.mk_uN var_0)


inductive iadd_sat__is_wf : N → sx → iN → iN → iN → Prop where
  | iadd_sat__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) : 
    fun_iadd_sat_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN v_N ret_val →
    iadd_sat__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_isub_sat_ : N → sx → iN → iN → iN → Prop where
  | fun_isub_sat__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_isub_sat_ v_N sx.U i_1 i_2 (.mk_uN (sat_u_ v_N (((proj_uN_0 i_1) : Int) - ((proj_uN_0 i_2) : Int))))
  | fun_isub_sat__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) : 
    fun_signed_ v_N (proj_uN_0 i_2) var_2 →
    fun_signed_ v_N (proj_uN_0 i_1) var_1 →
    fun_inv_signed_ v_N (sat_s_ v_N (var_1 - var_2)) var_0 →
    fun_isub_sat_ v_N sx.S i_1 i_2 (.mk_uN var_0)


inductive isub_sat__is_wf : N → sx → iN → iN → iN → Prop where
  | isub_sat__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) (var_0 : iN) : 
    fun_isub_sat_ v_N v_sx v_iN iN_0 var_0 →
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == var_0 →
    wf_uN v_N ret_val →
    isub_sat__is_wf v_N v_sx v_iN iN_0 ret_val


opaque iavgr_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iavgr__is_wf : N → sx → iN → iN → iN → Prop where
  | iavgr__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (iavgr_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    iavgr__is_wf v_N v_sx v_iN iN_0 ret_val


opaque iq15mulr_sat_ (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iq15mulr_sat__is_wf : N → sx → iN → iN → iN → Prop where
  | iq15mulr_sat__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : 
    wf_uN v_N v_iN →
    wf_uN v_N iN_0 →
    ret_val == (iq15mulr_sat_ v_N v_sx v_iN iN_0) →
    wf_uN v_N ret_val →
    iq15mulr_sat__is_wf v_N v_sx v_iN iN_0 ret_val


opaque fpmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fpmin__is_wf : N → fN → fN → List fN → Prop where
  | fpmin__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fpmin_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fpmin__is_wf v_N v_fN fN_0 ret_val_lst


opaque fpmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fpmax__is_wf : N → fN → fN → List fN → Prop where
  | fpmax__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fpmax_ v_N v_fN fN_0) →
    Forall (fun ret_val_elem => wf_fN v_N ret_val_elem) ret_val_lst →
    fpmax__is_wf v_N v_fN fN_0 ret_val_lst


def packnum_ (v_lanetype : lanetype) (v_num_ : num_) : lane_ :=
  match v_lanetype, v_num_ with
  | lanetype.I32, _ => lane_.mk_lane__0 numtype.I32 v_num_
  | lanetype.I64, _ => lane_.mk_lane__0 numtype.I64 v_num_
  | lanetype.F32, _ => lane_.mk_lane__0 numtype.F32 v_num_
  | lanetype.F64, _ => lane_.mk_lane__0 numtype.F64 v_num_
  | lanetype.I8, num_.mk_num__0 Inn.I32 c => lane_.mk_lane__1 packtype.I8 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I8))))) (psize packtype.I8) c)
  | lanetype.I16, num_.mk_num__0 Inn.I32 c => lane_.mk_lane__1 packtype.I16 (wrap__ (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I16))))) (psize packtype.I16) c)

inductive packnum__is_wf : lanetype → num_ → lane_ → Prop where
  | packnum__is_wf_0 (v_lanetype : lanetype) (v_num_ : num_) (ret_val : lane_) : 
    wf_num_ (unpack v_lanetype) v_num_ →
    ret_val == (packnum_ v_lanetype v_num_) →
    wf_lane_ v_lanetype ret_val →
    packnum__is_wf v_lanetype v_num_ ret_val


def unpacknum_ (v_lanetype : lanetype) (v_lane_ : lane_) : num_ :=
  match v_lanetype, v_lane_ with
  | lanetype.I32, lane_.mk_lane__0 numtype.I32 c => c
  | lanetype.I64, lane_.mk_lane__0 numtype.I64 c => c
  | lanetype.F32, lane_.mk_lane__0 numtype.F32 c => c
  | lanetype.F64, lane_.mk_lane__0 numtype.F64 c => c
  | lanetype.I8, lane_.mk_lane__1 packtype.I8 c => num_.mk_num__0 Inn.I32 (extend__ (psize packtype.I8) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I8))))) sx.U c)
  | lanetype.I16, lane_.mk_lane__1 packtype.I16 c => num_.mk_num__0 Inn.I32 (extend__ (psize packtype.I16) (Option.get! (size (valtype_numtype (unpack (lanetype_packtype packtype.I16))))) sx.U c)

inductive unpacknum__is_wf : lanetype → lane_ → num_ → Prop where
  | unpacknum__is_wf_0 (v_lanetype : lanetype) (v_lane_ : lane_) (ret_val : num_) : 
    wf_lane_ v_lanetype v_lane_ →
    ret_val == (unpacknum_ v_lanetype v_lane_) →
    wf_num_ (unpack v_lanetype) ret_val →
    unpacknum__is_wf v_lanetype v_lane_ ret_val


opaque lanes_ (v_shape : shape) (v_vec_ : vec_) : List lane_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive lanes__is_wf : shape → vec_ → List lane_ → Prop where
  | lanes__is_wf_0 (v_shape : shape) (v_vec_ : vec_) (ret_val_lst : List lane_) : 
    wf_shape v_shape →
    wf_uN 128 v_vec_ →
    ret_val_lst == (lanes_ v_shape v_vec_) →
    Forall (fun ret_val_elem => wf_lane_ (fun_lanetype v_shape) ret_val_elem) ret_val_lst →
    lanes__is_wf v_shape v_vec_ ret_val_lst


opaque inv_lanes_ (v_shape : shape) (var_0_lst : List lane_) : vec_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_lanes__is_wf : shape → List lane_ → vec_ → Prop where
  | inv_lanes__is_wf_0 (v_shape : shape) (var_0_lst : List lane_) (ret_val : vec_) : 
    wf_shape v_shape →
    Forall (fun var_0_elem => wf_lane_ (fun_lanetype v_shape) var_0_elem) var_0_lst →
    ret_val == (inv_lanes_ v_shape var_0_lst) →
    wf_uN 128 ret_val →
    inv_lanes__is_wf v_shape var_0_lst ret_val


def zeroop (v_vcvtop : vcvtop) : Option zero :=
  match v_vcvtop with
  | vcvtop.EXTEND v_half v_sx => none
  | vcvtop.CONVERT half_opt v_sx => none
  | vcvtop.TRUNC_SAT v_sx zero_opt => zero_opt
  | vcvtop.DEMOTE v_zero => some v_zero
  | vcvtop.PROMOTELOW => none

def halfop (v_vcvtop : vcvtop) : Option half :=
  match v_vcvtop with
  | vcvtop.EXTEND v_half v_sx => some v_half
  | vcvtop.CONVERT half_opt v_sx => half_opt
  | vcvtop.TRUNC_SAT v_sx zero_opt => none
  | vcvtop.DEMOTE v_zero => none
  | vcvtop.PROMOTELOW => some half.LOW

def fun_half (v_half : half) (nat : Nat) (nat_0 : Nat) : Nat :=
  match v_half with
  | half.LOW => nat
  | half.HIGH => nat_0

def vvunop_ (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) : vec_ :=
  match v_vectype, v_vvunop with
  | vectype.V128, vvunop.NOT => inot_ (Option.get! (size valtype.V128)) v_vec_

inductive vvunop__is_wf : vectype → vvunop → vec_ → vec_ → Prop where
  | vvunop__is_wf_0 (v_vectype : vectype) (v_vvunop : vvunop) (v_vec_ : vec_) (ret_val : vec_) : 
    (size (valtype_vectype v_vectype)) != none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
    ret_val == (vvunop_ v_vectype v_vvunop v_vec_) →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val →
    vvunop__is_wf v_vectype v_vvunop v_vec_ ret_val


def vvbinop_ (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) : vec_ :=
  match v_vectype, v_vvbinop with
  | vectype.V128, vvbinop.AND => iand_ (Option.get! (size valtype.V128)) v_vec_ vec__0
  | vectype.V128, vvbinop.ANDNOT => iandnot_ (Option.get! (size valtype.V128)) v_vec_ vec__0
  | vectype.V128, vvbinop.OR => ior_ (Option.get! (size valtype.V128)) v_vec_ vec__0
  | vectype.V128, vvbinop.XOR => ixor_ (Option.get! (size valtype.V128)) v_vec_ vec__0

inductive vvbinop__is_wf : vectype → vvbinop → vec_ → vec_ → vec_ → Prop where
  | vvbinop__is_wf_0 (v_vectype : vectype) (v_vvbinop : vvbinop) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) : 
    (size (valtype_vectype v_vectype)) != none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) vec__0 →
    ret_val == (vvbinop_ v_vectype v_vvbinop v_vec_ vec__0) →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val →
    vvbinop__is_wf v_vectype v_vvbinop v_vec_ vec__0 ret_val


def vvternop_ (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) : vec_ :=
  match v_vectype, v_vvternop with
  | vectype.V128, vvternop.BITSELECT => ibitselect_ (Option.get! (size valtype.V128)) v_vec_ vec__0 vec__1

inductive vvternop__is_wf : vectype → vvternop → vec_ → vec_ → vec_ → vec_ → Prop where
  | vvternop__is_wf_0 (v_vectype : vectype) (v_vvternop : vvternop) (v_vec_ : vec_) (vec__0 : vec_) (vec__1 : vec_) (ret_val : vec_) : 
    (size (valtype_vectype v_vectype)) != none →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) v_vec_ →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) vec__0 →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) vec__1 →
    ret_val == (vvternop_ v_vectype v_vvternop v_vec_ vec__0 vec__1) →
    wf_uN (Option.get! (size (valtype_vectype v_vectype))) ret_val →
    vvternop__is_wf v_vectype v_vvternop v_vec_ vec__0 vec__1 ret_val


inductive fun_vunop_ : shape → vunop_ → vec_ → List vec_ → Prop where
  | fun_vunop__case_0 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_3_elem => (proj_lane__2 lane_1_3_elem) != none) lane_1_lst →
    Forall₂ (fun var_1_elem lane_1_3_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_3_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_2_elem => (proj_lane__2 lane_1_2_elem) != none) lane_1_lst →
    Forall₂ (fun var_0_elem lane_1_2_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_2_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_1 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_6_elem => (proj_lane__2 lane_1_6_elem) != none) lane_1_lst →
    Forall₂ (fun var_1_elem lane_1_6_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_6_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_5_elem => (proj_lane__2 lane_1_5_elem) != none) lane_1_lst →
    Forall₂ (fun var_0_elem lane_1_5_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_5_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_2 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_9_elem => (proj_lane__2 lane_1_9_elem) != none) lane_1_lst →
    Forall₂ (fun var_1_elem lane_1_9_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_9_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_8_elem => (proj_lane__2 lane_1_8_elem) != none) lane_1_lst →
    Forall₂ (fun var_0_elem lane_1_8_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_8_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_3 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_12_elem => (proj_lane__2 lane_1_12_elem) != none) lane_1_lst →
    Forall₂ (fun var_1_elem lane_1_12_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_12_elem)) var_1_elem) var_1_lst lane_1_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    Forall (fun lane_1_11_elem => (proj_lane__2 lane_1_11_elem) != none) lane_1_lst →
    Forall₂ (fun var_0_elem lane_1_11_elem => fun_iabs_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_11_elem)) var_0_elem) var_0_lst lane_1_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_N.ABS) v128_1 [v128]
  | fun_vunop__case_4 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_14_elem => (proj_lane__2 lane_1_14_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_1_14_elem => lane_.mk_lane__2 Jnn.I32 (ineg_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_14_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_15_elem => (proj_lane__2 lane_1_15_elem) != none) lane_1_lst →
    Forall (fun lane_1_15_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (ineg_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_15_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_5 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_17_elem => (proj_lane__2 lane_1_17_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_1_17_elem => lane_.mk_lane__2 Jnn.I64 (ineg_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_17_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_18_elem => (proj_lane__2 lane_1_18_elem) != none) lane_1_lst →
    Forall (fun lane_1_18_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (ineg_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_18_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_6 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_20_elem => (proj_lane__2 lane_1_20_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_1_20_elem => lane_.mk_lane__2 Jnn.I8 (ineg_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_20_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun lane_1_21_elem => (proj_lane__2 lane_1_21_elem) != none) lane_1_lst →
    Forall (fun lane_1_21_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (ineg_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_21_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_7 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_23_elem => (proj_lane__2 lane_1_23_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_1_23_elem => lane_.mk_lane__2 Jnn.I16 (ineg_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_23_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun lane_1_24_elem => (proj_lane__2 lane_1_24_elem) != none) lane_1_lst →
    Forall (fun lane_1_24_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (ineg_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_24_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_N.NEG) v128_1 [v128]
  | fun_vunop__case_8 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_26_elem => (proj_lane__2 lane_1_26_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_1_26_elem => lane_.mk_lane__2 Jnn.I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_26_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_27_elem => (proj_lane__2 lane_1_27_elem) != none) lane_1_lst →
    Forall (fun lane_1_27_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_27_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I32 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_9 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_29_elem => (proj_lane__2 lane_1_29_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_1_29_elem => lane_.mk_lane__2 Jnn.I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_29_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_30_elem => (proj_lane__2 lane_1_30_elem) != none) lane_1_lst →
    Forall (fun lane_1_30_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_30_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I64 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_10 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_32_elem => (proj_lane__2 lane_1_32_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_1_32_elem => lane_.mk_lane__2 Jnn.I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_32_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun lane_1_33_elem => (proj_lane__2 lane_1_33_elem) != none) lane_1_lst →
    Forall (fun lane_1_33_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_33_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I8 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_11 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    Forall (fun lane_1_35_elem => (proj_lane__2 lane_1_35_elem) != none) lane_1_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_1_35_elem => lane_.mk_lane__2 Jnn.I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_35_elem)))) lane_1_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun lane_1_36_elem => (proj_lane__2 lane_1_36_elem) != none) lane_1_lst →
    Forall (fun lane_1_36_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (ipopcnt_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_36_elem))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vunop_.mk_vunop__0 Jnn.I16 M_0 vunop_Jnn_N.POPCNT) v128_1 [v128]
  | fun_vunop__case_12 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_38_elem => Map (fun iter_0_49_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_49_elem)) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_38_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_2_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_2_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_39_elem => Forall (fun iter_0_50_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_50_elem))) (fabs_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_39_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.ABS) v128_1 v128_lst
  | fun_vunop__case_13 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_41_elem => Map (fun iter_0_51_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_51_elem)) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_41_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_4_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_4_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_42_elem => Forall (fun iter_0_52_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_52_elem))) (fabs_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_42_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.ABS) v128_1 v128_lst
  | fun_vunop__case_14 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_44_elem => Map (fun iter_0_53_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_53_elem)) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_44_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_6_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_6_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_45_elem => Forall (fun iter_0_54_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_54_elem))) (fneg_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_45_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.NEG) v128_1 v128_lst
  | fun_vunop__case_15 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_47_elem => Map (fun iter_0_55_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_55_elem)) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_47_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_8_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_8_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_48_elem => Forall (fun iter_0_56_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_56_elem))) (fneg_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_48_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.NEG) v128_1 v128_lst
  | fun_vunop__case_16 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_50_elem => Map (fun iter_0_57_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_57_elem)) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_50_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_10_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_10_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_51_elem => Forall (fun iter_0_58_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_58_elem))) (fsqrt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_51_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.SQRT) v128_1 v128_lst
  | fun_vunop__case_17 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_53_elem => Map (fun iter_0_59_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_59_elem)) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_53_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_12_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_12_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_54_elem => Forall (fun iter_0_60_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_60_elem))) (fsqrt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_54_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.SQRT) v128_1 v128_lst
  | fun_vunop__case_18 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_56_elem => Map (fun iter_0_61_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_61_elem)) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_56_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_14_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_14_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_57_elem => Forall (fun iter_0_62_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_62_elem))) (fceil_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_57_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.CEIL) v128_1 v128_lst
  | fun_vunop__case_19 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_59_elem => Map (fun iter_0_63_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_63_elem)) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_59_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_16_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_16_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_60_elem => Forall (fun iter_0_64_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_64_elem))) (fceil_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_60_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.CEIL) v128_1 v128_lst
  | fun_vunop__case_20 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_62_elem => Map (fun iter_0_65_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_65_elem)) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_62_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_18_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_18_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_63_elem => Forall (fun iter_0_66_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_66_elem))) (ffloor_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_63_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.FLOOR) v128_1 v128_lst
  | fun_vunop__case_21 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_65_elem => Map (fun iter_0_67_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_67_elem)) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_65_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_20_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_20_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_66_elem => Forall (fun iter_0_68_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_68_elem))) (ffloor_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_66_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.FLOOR) v128_1 v128_lst
  | fun_vunop__case_22 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_68_elem => Map (fun iter_0_69_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_69_elem)) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_68_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_22_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_22_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_69_elem => Forall (fun iter_0_70_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_70_elem))) (ftrunc_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_69_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.TRUNC) v128_1 v128_lst
  | fun_vunop__case_23 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_71_elem => Map (fun iter_0_71_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_71_elem)) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_71_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_24_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_24_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_72_elem => Forall (fun iter_0_72_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_72_elem))) (ftrunc_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_72_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.TRUNC) v128_1 v128_lst
  | fun_vunop__case_24 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_74_elem => Map (fun iter_0_73_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_73_elem)) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_74_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_26_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_26_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    Forall (fun lane_1_75_elem => Forall (fun iter_0_74_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_74_elem))) (fnearest_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_75_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F32 M_0 vunop_Fnn_N.NEAREST) v128_1 v128_lst
  | fun_vunop__case_25 (v_M : Nat) (v128_1 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_lst_lst == (setproduct_ lane_ (Map (fun lane_1_77_elem => Map (fun iter_0_75_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_75_elem)) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_77_elem)))))) lane_1_lst)) →
    v128_lst == (Map (fun lane_lst_28_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_28_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    Forall (fun lane_1_78_elem => Forall (fun iter_0_76_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_76_elem))) (fnearest_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_78_elem)))))) lane_1_lst →
    v_M == M_0 →
    fun_vunop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vunop_.mk_vunop__1 Fnn.F64 M_0 vunop_Fnn_N.NEAREST) v128_1 v128_lst


inductive vunop__is_wf : shape → vunop_ → vec_ → List vec_ → Prop where
  | vunop__is_wf_0 (v_shape : shape) (v_vunop_ : vunop_) (v_vec_ : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) : 
    fun_vunop_ v_shape v_vunop_ v_vec_ var_0 →
    wf_shape v_shape →
    wf_vunop_ v_shape v_vunop_ →
    wf_uN 128 v_vec_ →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    vunop__is_wf v_shape v_vunop_ v_vec_ ret_val_lst


inductive fun_vbinop_ : shape → vbinop_ → vec_ → vec_ → List vec_ → Prop where
  | fun_vbinop__case_0 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_80_elem => (proj_lane__2 lane_1_80_elem) != none) lane_1_lst →
    Forall (fun lane_2_2_elem => (proj_lane__2 lane_2_2_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun lane_1_80_elem lane_2_2_elem => lane_.mk_lane__2 Jnn.I32 (iadd_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_80_elem)) (Option.get! (proj_lane__2 lane_2_2_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_81_elem => (proj_lane__2 lane_1_81_elem) != none) lane_1_lst →
    Forall (fun lane_2_3_elem => (proj_lane__2 lane_2_3_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_81_elem lane_2_3_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (iadd_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_81_elem)) (Option.get! (proj_lane__2 lane_2_3_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_1 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_83_elem => (proj_lane__2 lane_1_83_elem) != none) lane_1_lst →
    Forall (fun lane_2_5_elem => (proj_lane__2 lane_2_5_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun lane_1_83_elem lane_2_5_elem => lane_.mk_lane__2 Jnn.I64 (iadd_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_83_elem)) (Option.get! (proj_lane__2 lane_2_5_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_84_elem => (proj_lane__2 lane_1_84_elem) != none) lane_1_lst →
    Forall (fun lane_2_6_elem => (proj_lane__2 lane_2_6_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_84_elem lane_2_6_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (iadd_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_84_elem)) (Option.get! (proj_lane__2 lane_2_6_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_2 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_86_elem => (proj_lane__2 lane_1_86_elem) != none) lane_1_lst →
    Forall (fun lane_2_8_elem => (proj_lane__2 lane_2_8_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun lane_1_86_elem lane_2_8_elem => lane_.mk_lane__2 Jnn.I8 (iadd_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_86_elem)) (Option.get! (proj_lane__2 lane_2_8_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_87_elem => (proj_lane__2 lane_1_87_elem) != none) lane_1_lst →
    Forall (fun lane_2_9_elem => (proj_lane__2 lane_2_9_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_87_elem lane_2_9_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (iadd_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_87_elem)) (Option.get! (proj_lane__2 lane_2_9_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_3 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_89_elem => (proj_lane__2 lane_1_89_elem) != none) lane_1_lst →
    Forall (fun lane_2_11_elem => (proj_lane__2 lane_2_11_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun lane_1_89_elem lane_2_11_elem => lane_.mk_lane__2 Jnn.I16 (iadd_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_89_elem)) (Option.get! (proj_lane__2 lane_2_11_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_90_elem => (proj_lane__2 lane_1_90_elem) != none) lane_1_lst →
    Forall (fun lane_2_12_elem => (proj_lane__2 lane_2_12_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_90_elem lane_2_12_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (iadd_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_90_elem)) (Option.get! (proj_lane__2 lane_2_12_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.ADD) v128_1 v128_2 [v128]
  | fun_vbinop__case_4 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_92_elem => (proj_lane__2 lane_1_92_elem) != none) lane_1_lst →
    Forall (fun lane_2_14_elem => (proj_lane__2 lane_2_14_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun lane_1_92_elem lane_2_14_elem => lane_.mk_lane__2 Jnn.I32 (isub_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_92_elem)) (Option.get! (proj_lane__2 lane_2_14_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_93_elem => (proj_lane__2 lane_1_93_elem) != none) lane_1_lst →
    Forall (fun lane_2_15_elem => (proj_lane__2 lane_2_15_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_93_elem lane_2_15_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (isub_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_93_elem)) (Option.get! (proj_lane__2 lane_2_15_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_5 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_95_elem => (proj_lane__2 lane_1_95_elem) != none) lane_1_lst →
    Forall (fun lane_2_17_elem => (proj_lane__2 lane_2_17_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun lane_1_95_elem lane_2_17_elem => lane_.mk_lane__2 Jnn.I64 (isub_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_95_elem)) (Option.get! (proj_lane__2 lane_2_17_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_96_elem => (proj_lane__2 lane_1_96_elem) != none) lane_1_lst →
    Forall (fun lane_2_18_elem => (proj_lane__2 lane_2_18_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_96_elem lane_2_18_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (isub_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_96_elem)) (Option.get! (proj_lane__2 lane_2_18_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_6 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_98_elem => (proj_lane__2 lane_1_98_elem) != none) lane_1_lst →
    Forall (fun lane_2_20_elem => (proj_lane__2 lane_2_20_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun lane_1_98_elem lane_2_20_elem => lane_.mk_lane__2 Jnn.I8 (isub_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_98_elem)) (Option.get! (proj_lane__2 lane_2_20_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_99_elem => (proj_lane__2 lane_1_99_elem) != none) lane_1_lst →
    Forall (fun lane_2_21_elem => (proj_lane__2 lane_2_21_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_99_elem lane_2_21_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (isub_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_99_elem)) (Option.get! (proj_lane__2 lane_2_21_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_7 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_101_elem => (proj_lane__2 lane_1_101_elem) != none) lane_1_lst →
    Forall (fun lane_2_23_elem => (proj_lane__2 lane_2_23_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun lane_1_101_elem lane_2_23_elem => lane_.mk_lane__2 Jnn.I16 (isub_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_101_elem)) (Option.get! (proj_lane__2 lane_2_23_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_102_elem => (proj_lane__2 lane_1_102_elem) != none) lane_1_lst →
    Forall (fun lane_2_24_elem => (proj_lane__2 lane_2_24_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_102_elem lane_2_24_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (isub_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_102_elem)) (Option.get! (proj_lane__2 lane_2_24_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.SUB) v128_1 v128_2 [v128]
  | fun_vbinop__case_8 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_105_elem => (proj_lane__2 lane_1_105_elem) != none) lane_1_lst →
    Forall (fun lane_2_27_elem => (proj_lane__2 lane_2_27_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_105_elem lane_2_27_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_105_elem)) (Option.get! (proj_lane__2 lane_2_27_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_104_elem => (proj_lane__2 lane_1_104_elem) != none) lane_1_lst →
    Forall (fun lane_2_26_elem => (proj_lane__2 lane_2_26_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_104_elem lane_2_26_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_104_elem)) (Option.get! (proj_lane__2 lane_2_26_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_9 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_108_elem => (proj_lane__2 lane_1_108_elem) != none) lane_1_lst →
    Forall (fun lane_2_30_elem => (proj_lane__2 lane_2_30_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_108_elem lane_2_30_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_108_elem)) (Option.get! (proj_lane__2 lane_2_30_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_107_elem => (proj_lane__2 lane_1_107_elem) != none) lane_1_lst →
    Forall (fun lane_2_29_elem => (proj_lane__2 lane_2_29_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_107_elem lane_2_29_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_107_elem)) (Option.get! (proj_lane__2 lane_2_29_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_10 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_111_elem => (proj_lane__2 lane_1_111_elem) != none) lane_1_lst →
    Forall (fun lane_2_33_elem => (proj_lane__2 lane_2_33_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_111_elem lane_2_33_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_111_elem)) (Option.get! (proj_lane__2 lane_2_33_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_110_elem => (proj_lane__2 lane_1_110_elem) != none) lane_1_lst →
    Forall (fun lane_2_32_elem => (proj_lane__2 lane_2_32_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_110_elem lane_2_32_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_110_elem)) (Option.get! (proj_lane__2 lane_2_32_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_11 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_114_elem => (proj_lane__2 lane_1_114_elem) != none) lane_1_lst →
    Forall (fun lane_2_36_elem => (proj_lane__2 lane_2_36_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_114_elem lane_2_36_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_114_elem)) (Option.get! (proj_lane__2 lane_2_36_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_113_elem => (proj_lane__2 lane_1_113_elem) != none) lane_1_lst →
    Forall (fun lane_2_35_elem => (proj_lane__2 lane_2_35_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_113_elem lane_2_35_elem => fun_imin_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_113_elem)) (Option.get! (proj_lane__2 lane_2_35_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.MIN v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_12 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_117_elem => (proj_lane__2 lane_1_117_elem) != none) lane_1_lst →
    Forall (fun lane_2_39_elem => (proj_lane__2 lane_2_39_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_117_elem lane_2_39_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_117_elem)) (Option.get! (proj_lane__2 lane_2_39_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_116_elem => (proj_lane__2 lane_1_116_elem) != none) lane_1_lst →
    Forall (fun lane_2_38_elem => (proj_lane__2 lane_2_38_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_116_elem lane_2_38_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_116_elem)) (Option.get! (proj_lane__2 lane_2_38_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_13 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_120_elem => (proj_lane__2 lane_1_120_elem) != none) lane_1_lst →
    Forall (fun lane_2_42_elem => (proj_lane__2 lane_2_42_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_120_elem lane_2_42_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_120_elem)) (Option.get! (proj_lane__2 lane_2_42_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_119_elem => (proj_lane__2 lane_1_119_elem) != none) lane_1_lst →
    Forall (fun lane_2_41_elem => (proj_lane__2 lane_2_41_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_119_elem lane_2_41_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_119_elem)) (Option.get! (proj_lane__2 lane_2_41_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_14 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_123_elem => (proj_lane__2 lane_1_123_elem) != none) lane_1_lst →
    Forall (fun lane_2_45_elem => (proj_lane__2 lane_2_45_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_123_elem lane_2_45_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_123_elem)) (Option.get! (proj_lane__2 lane_2_45_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_122_elem => (proj_lane__2 lane_1_122_elem) != none) lane_1_lst →
    Forall (fun lane_2_44_elem => (proj_lane__2 lane_2_44_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_122_elem lane_2_44_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_122_elem)) (Option.get! (proj_lane__2 lane_2_44_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_15 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_126_elem => (proj_lane__2 lane_1_126_elem) != none) lane_1_lst →
    Forall (fun lane_2_48_elem => (proj_lane__2 lane_2_48_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_126_elem lane_2_48_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_126_elem)) (Option.get! (proj_lane__2 lane_2_48_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_125_elem => (proj_lane__2 lane_1_125_elem) != none) lane_1_lst →
    Forall (fun lane_2_47_elem => (proj_lane__2 lane_2_47_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_125_elem lane_2_47_elem => fun_imax_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_125_elem)) (Option.get! (proj_lane__2 lane_2_47_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.MAX v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_16 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_129_elem => (proj_lane__2 lane_1_129_elem) != none) lane_1_lst →
    Forall (fun lane_2_51_elem => (proj_lane__2 lane_2_51_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_129_elem lane_2_51_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_129_elem)) (Option.get! (proj_lane__2 lane_2_51_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_128_elem => (proj_lane__2 lane_1_128_elem) != none) lane_1_lst →
    Forall (fun lane_2_50_elem => (proj_lane__2 lane_2_50_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_128_elem lane_2_50_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_128_elem)) (Option.get! (proj_lane__2 lane_2_50_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_17 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_132_elem => (proj_lane__2 lane_1_132_elem) != none) lane_1_lst →
    Forall (fun lane_2_54_elem => (proj_lane__2 lane_2_54_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_132_elem lane_2_54_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_132_elem)) (Option.get! (proj_lane__2 lane_2_54_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_131_elem => (proj_lane__2 lane_1_131_elem) != none) lane_1_lst →
    Forall (fun lane_2_53_elem => (proj_lane__2 lane_2_53_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_131_elem lane_2_53_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_131_elem)) (Option.get! (proj_lane__2 lane_2_53_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_18 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_135_elem => (proj_lane__2 lane_1_135_elem) != none) lane_1_lst →
    Forall (fun lane_2_57_elem => (proj_lane__2 lane_2_57_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_135_elem lane_2_57_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_135_elem)) (Option.get! (proj_lane__2 lane_2_57_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_134_elem => (proj_lane__2 lane_1_134_elem) != none) lane_1_lst →
    Forall (fun lane_2_56_elem => (proj_lane__2 lane_2_56_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_134_elem lane_2_56_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_134_elem)) (Option.get! (proj_lane__2 lane_2_56_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_19 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_138_elem => (proj_lane__2 lane_1_138_elem) != none) lane_1_lst →
    Forall (fun lane_2_60_elem => (proj_lane__2 lane_2_60_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_138_elem lane_2_60_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_138_elem)) (Option.get! (proj_lane__2 lane_2_60_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_137_elem => (proj_lane__2 lane_1_137_elem) != none) lane_1_lst →
    Forall (fun lane_2_59_elem => (proj_lane__2 lane_2_59_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_137_elem lane_2_59_elem => fun_iadd_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_137_elem)) (Option.get! (proj_lane__2 lane_2_59_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.ADD_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_20 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_141_elem => (proj_lane__2 lane_1_141_elem) != none) lane_1_lst →
    Forall (fun lane_2_63_elem => (proj_lane__2 lane_2_63_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_141_elem lane_2_63_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_141_elem)) (Option.get! (proj_lane__2 lane_2_63_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_140_elem => (proj_lane__2 lane_1_140_elem) != none) lane_1_lst →
    Forall (fun lane_2_62_elem => (proj_lane__2 lane_2_62_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_140_elem lane_2_62_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_140_elem)) (Option.get! (proj_lane__2 lane_2_62_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I32 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_21 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_144_elem => (proj_lane__2 lane_1_144_elem) != none) lane_1_lst →
    Forall (fun lane_2_66_elem => (proj_lane__2 lane_2_66_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_144_elem lane_2_66_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_144_elem)) (Option.get! (proj_lane__2 lane_2_66_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_143_elem => (proj_lane__2 lane_1_143_elem) != none) lane_1_lst →
    Forall (fun lane_2_65_elem => (proj_lane__2 lane_2_65_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_143_elem lane_2_65_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_143_elem)) (Option.get! (proj_lane__2 lane_2_65_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I64 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_22 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_147_elem => (proj_lane__2 lane_1_147_elem) != none) lane_1_lst →
    Forall (fun lane_2_69_elem => (proj_lane__2 lane_2_69_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_147_elem lane_2_69_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_147_elem)) (Option.get! (proj_lane__2 lane_2_69_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_146_elem => (proj_lane__2 lane_1_146_elem) != none) lane_1_lst →
    Forall (fun lane_2_68_elem => (proj_lane__2 lane_2_68_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_146_elem lane_2_68_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_146_elem)) (Option.get! (proj_lane__2 lane_2_68_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I8 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_23 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_150_elem => (proj_lane__2 lane_1_150_elem) != none) lane_1_lst →
    Forall (fun lane_2_72_elem => (proj_lane__2 lane_2_72_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_150_elem lane_2_72_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_150_elem)) (Option.get! (proj_lane__2 lane_2_72_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_149_elem => (proj_lane__2 lane_1_149_elem) != none) lane_1_lst →
    Forall (fun lane_2_71_elem => (proj_lane__2 lane_2_71_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_149_elem lane_2_71_elem => fun_isub_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_149_elem)) (Option.get! (proj_lane__2 lane_2_71_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun var_0_elem => lane_.mk_lane__2 Jnn.I16 var_0_elem) var_0_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 var_1_elem)) var_1_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 (vbinop_Jnn_N.SUB_SAT v_sx)) v128_1 v128_2 [v128]
  | fun_vbinop__case_24 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_152_elem => (proj_lane__2 lane_1_152_elem) != none) lane_1_lst →
    Forall (fun lane_2_74_elem => (proj_lane__2 lane_2_74_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun lane_1_152_elem lane_2_74_elem => lane_.mk_lane__2 Jnn.I32 (imul_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_152_elem)) (Option.get! (proj_lane__2 lane_2_74_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_153_elem => (proj_lane__2 lane_1_153_elem) != none) lane_1_lst →
    Forall (fun lane_2_75_elem => (proj_lane__2 lane_2_75_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_153_elem lane_2_75_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (imul_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_153_elem)) (Option.get! (proj_lane__2 lane_2_75_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_25 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_155_elem => (proj_lane__2 lane_1_155_elem) != none) lane_1_lst →
    Forall (fun lane_2_77_elem => (proj_lane__2 lane_2_77_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun lane_1_155_elem lane_2_77_elem => lane_.mk_lane__2 Jnn.I64 (imul_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_155_elem)) (Option.get! (proj_lane__2 lane_2_77_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_156_elem => (proj_lane__2 lane_1_156_elem) != none) lane_1_lst →
    Forall (fun lane_2_78_elem => (proj_lane__2 lane_2_78_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_156_elem lane_2_78_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (imul_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_156_elem)) (Option.get! (proj_lane__2 lane_2_78_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_26 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_158_elem => (proj_lane__2 lane_1_158_elem) != none) lane_1_lst →
    Forall (fun lane_2_80_elem => (proj_lane__2 lane_2_80_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun lane_1_158_elem lane_2_80_elem => lane_.mk_lane__2 Jnn.I8 (imul_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_158_elem)) (Option.get! (proj_lane__2 lane_2_80_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_159_elem => (proj_lane__2 lane_1_159_elem) != none) lane_1_lst →
    Forall (fun lane_2_81_elem => (proj_lane__2 lane_2_81_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_159_elem lane_2_81_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (imul_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_159_elem)) (Option.get! (proj_lane__2 lane_2_81_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_27 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_161_elem => (proj_lane__2 lane_1_161_elem) != none) lane_1_lst →
    Forall (fun lane_2_83_elem => (proj_lane__2 lane_2_83_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun lane_1_161_elem lane_2_83_elem => lane_.mk_lane__2 Jnn.I16 (imul_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_161_elem)) (Option.get! (proj_lane__2 lane_2_83_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_162_elem => (proj_lane__2 lane_1_162_elem) != none) lane_1_lst →
    Forall (fun lane_2_84_elem => (proj_lane__2 lane_2_84_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_162_elem lane_2_84_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (imul_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_162_elem)) (Option.get! (proj_lane__2 lane_2_84_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.MUL) v128_1 v128_2 [v128]
  | fun_vbinop__case_28 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_164_elem => (proj_lane__2 lane_1_164_elem) != none) lane_1_lst →
    Forall (fun lane_2_86_elem => (proj_lane__2 lane_2_86_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun lane_1_164_elem lane_2_86_elem => lane_.mk_lane__2 Jnn.I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.U (Option.get! (proj_lane__2 lane_1_164_elem)) (Option.get! (proj_lane__2 lane_2_86_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_165_elem => (proj_lane__2 lane_1_165_elem) != none) lane_1_lst →
    Forall (fun lane_2_87_elem => (proj_lane__2 lane_2_87_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_165_elem lane_2_87_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.U (Option.get! (proj_lane__2 lane_1_165_elem)) (Option.get! (proj_lane__2 lane_2_87_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_29 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_167_elem => (proj_lane__2 lane_1_167_elem) != none) lane_1_lst →
    Forall (fun lane_2_89_elem => (proj_lane__2 lane_2_89_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun lane_1_167_elem lane_2_89_elem => lane_.mk_lane__2 Jnn.I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.U (Option.get! (proj_lane__2 lane_1_167_elem)) (Option.get! (proj_lane__2 lane_2_89_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_168_elem => (proj_lane__2 lane_1_168_elem) != none) lane_1_lst →
    Forall (fun lane_2_90_elem => (proj_lane__2 lane_2_90_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_168_elem lane_2_90_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.U (Option.get! (proj_lane__2 lane_1_168_elem)) (Option.get! (proj_lane__2 lane_2_90_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_30 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_170_elem => (proj_lane__2 lane_1_170_elem) != none) lane_1_lst →
    Forall (fun lane_2_92_elem => (proj_lane__2 lane_2_92_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun lane_1_170_elem lane_2_92_elem => lane_.mk_lane__2 Jnn.I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.U (Option.get! (proj_lane__2 lane_1_170_elem)) (Option.get! (proj_lane__2 lane_2_92_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_171_elem => (proj_lane__2 lane_1_171_elem) != none) lane_1_lst →
    Forall (fun lane_2_93_elem => (proj_lane__2 lane_2_93_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_171_elem lane_2_93_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.U (Option.get! (proj_lane__2 lane_1_171_elem)) (Option.get! (proj_lane__2 lane_2_93_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_31 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_173_elem => (proj_lane__2 lane_1_173_elem) != none) lane_1_lst →
    Forall (fun lane_2_95_elem => (proj_lane__2 lane_2_95_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun lane_1_173_elem lane_2_95_elem => lane_.mk_lane__2 Jnn.I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.U (Option.get! (proj_lane__2 lane_1_173_elem)) (Option.get! (proj_lane__2 lane_2_95_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_174_elem => (proj_lane__2 lane_1_174_elem) != none) lane_1_lst →
    Forall (fun lane_2_96_elem => (proj_lane__2 lane_2_96_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_174_elem lane_2_96_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (iavgr_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.U (Option.get! (proj_lane__2 lane_1_174_elem)) (Option.get! (proj_lane__2 lane_2_96_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.AVGRU) v128_1 v128_2 [v128]
  | fun_vbinop__case_32 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_176_elem => (proj_lane__2 lane_1_176_elem) != none) lane_1_lst →
    Forall (fun lane_2_98_elem => (proj_lane__2 lane_2_98_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map₂ (fun lane_1_176_elem lane_2_98_elem => lane_.mk_lane__2 Jnn.I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (Option.get! (proj_lane__2 lane_1_176_elem)) (Option.get! (proj_lane__2 lane_2_98_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_177_elem => (proj_lane__2 lane_1_177_elem) != none) lane_1_lst →
    Forall (fun lane_2_99_elem => (proj_lane__2 lane_2_99_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_177_elem lane_2_99_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (Option.get! (proj_lane__2 lane_1_177_elem)) (Option.get! (proj_lane__2 lane_2_99_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I32 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_33 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_179_elem => (proj_lane__2 lane_1_179_elem) != none) lane_1_lst →
    Forall (fun lane_2_101_elem => (proj_lane__2 lane_2_101_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map₂ (fun lane_1_179_elem lane_2_101_elem => lane_.mk_lane__2 Jnn.I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (Option.get! (proj_lane__2 lane_1_179_elem)) (Option.get! (proj_lane__2 lane_2_101_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_180_elem => (proj_lane__2 lane_1_180_elem) != none) lane_1_lst →
    Forall (fun lane_2_102_elem => (proj_lane__2 lane_2_102_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_180_elem lane_2_102_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (Option.get! (proj_lane__2 lane_1_180_elem)) (Option.get! (proj_lane__2 lane_2_102_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I64 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_34 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_182_elem => (proj_lane__2 lane_1_182_elem) != none) lane_1_lst →
    Forall (fun lane_2_104_elem => (proj_lane__2 lane_2_104_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map₂ (fun lane_1_182_elem lane_2_104_elem => lane_.mk_lane__2 Jnn.I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (Option.get! (proj_lane__2 lane_1_182_elem)) (Option.get! (proj_lane__2 lane_2_104_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_183_elem => (proj_lane__2 lane_1_183_elem) != none) lane_1_lst →
    Forall (fun lane_2_105_elem => (proj_lane__2 lane_2_105_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_183_elem lane_2_105_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (Option.get! (proj_lane__2 lane_1_183_elem)) (Option.get! (proj_lane__2 lane_2_105_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I8 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_35 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_185_elem => (proj_lane__2 lane_1_185_elem) != none) lane_1_lst →
    Forall (fun lane_2_107_elem => (proj_lane__2 lane_2_107_elem) != none) lane_2_lst →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map₂ (fun lane_1_185_elem lane_2_107_elem => lane_.mk_lane__2 Jnn.I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (Option.get! (proj_lane__2 lane_1_185_elem)) (Option.get! (proj_lane__2 lane_2_107_elem)))) lane_1_lst lane_2_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_186_elem => (proj_lane__2 lane_1_186_elem) != none) lane_1_lst →
    Forall (fun lane_2_108_elem => (proj_lane__2 lane_2_108_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_186_elem lane_2_108_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 (iq15mulr_sat_ (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (Option.get! (proj_lane__2 lane_1_186_elem)) (Option.get! (proj_lane__2 lane_2_108_elem))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__0 Jnn.I16 M_0 vbinop_Jnn_N.Q15MULR_SATS) v128_1 v128_2 [v128]
  | fun_vbinop__case_36 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_188_elem lane_2_110_elem => Map (fun iter_0_77_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_77_elem)) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_188_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_110_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_30_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_30_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_189_elem lane_2_111_elem => Forall (fun iter_0_78_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_78_elem))) (fadd_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_189_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_111_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.ADD) v128_1 v128_2 v128_lst
  | fun_vbinop__case_37 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_191_elem lane_2_113_elem => Map (fun iter_0_79_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_79_elem)) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_191_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_113_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_32_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_32_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_192_elem lane_2_114_elem => Forall (fun iter_0_80_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_80_elem))) (fadd_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_192_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_114_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.ADD) v128_1 v128_2 v128_lst
  | fun_vbinop__case_38 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_194_elem lane_2_116_elem => Map (fun iter_0_81_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_81_elem)) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_194_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_116_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_34_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_34_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_195_elem lane_2_117_elem => Forall (fun iter_0_82_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_82_elem))) (fsub_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_195_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_117_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.SUB) v128_1 v128_2 v128_lst
  | fun_vbinop__case_39 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_197_elem lane_2_119_elem => Map (fun iter_0_83_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_83_elem)) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_197_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_119_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_36_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_36_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_198_elem lane_2_120_elem => Forall (fun iter_0_84_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_84_elem))) (fsub_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_198_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_120_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.SUB) v128_1 v128_2 v128_lst
  | fun_vbinop__case_40 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_200_elem lane_2_122_elem => Map (fun iter_0_85_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_85_elem)) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_200_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_122_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_38_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_38_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_201_elem lane_2_123_elem => Forall (fun iter_0_86_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_86_elem))) (fmul_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_201_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_123_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.MUL) v128_1 v128_2 v128_lst
  | fun_vbinop__case_41 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_203_elem lane_2_125_elem => Map (fun iter_0_87_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_87_elem)) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_203_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_125_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_40_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_40_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_204_elem lane_2_126_elem => Forall (fun iter_0_88_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_88_elem))) (fmul_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_204_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_126_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.MUL) v128_1 v128_2 v128_lst
  | fun_vbinop__case_42 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_206_elem lane_2_128_elem => Map (fun iter_0_89_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_89_elem)) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_206_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_128_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_42_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_42_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_207_elem lane_2_129_elem => Forall (fun iter_0_90_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_90_elem))) (fdiv_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_207_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_129_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.DIV) v128_1 v128_2 v128_lst
  | fun_vbinop__case_43 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_209_elem lane_2_131_elem => Map (fun iter_0_91_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_91_elem)) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_209_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_131_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_44_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_44_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_210_elem lane_2_132_elem => Forall (fun iter_0_92_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_92_elem))) (fdiv_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_210_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_132_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.DIV) v128_1 v128_2 v128_lst
  | fun_vbinop__case_44 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_212_elem lane_2_134_elem => Map (fun iter_0_93_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_93_elem)) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_212_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_134_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_46_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_46_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_213_elem lane_2_135_elem => Forall (fun iter_0_94_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_94_elem))) (fmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_213_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_135_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.MIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_45 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_215_elem lane_2_137_elem => Map (fun iter_0_95_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_95_elem)) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_215_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_137_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_48_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_48_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_216_elem lane_2_138_elem => Forall (fun iter_0_96_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_96_elem))) (fmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_216_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_138_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.MIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_46 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_218_elem lane_2_140_elem => Map (fun iter_0_97_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_97_elem)) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_218_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_140_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_50_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_50_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_219_elem lane_2_141_elem => Forall (fun iter_0_98_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_98_elem))) (fmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_219_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_141_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.MAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_47 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_221_elem lane_2_143_elem => Map (fun iter_0_99_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_99_elem)) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_221_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_143_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_52_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_52_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_222_elem lane_2_144_elem => Forall (fun iter_0_100_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_100_elem))) (fmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_222_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_144_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.MAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_48 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_224_elem lane_2_146_elem => Map (fun iter_0_101_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_101_elem)) (fpmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_224_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_146_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_54_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_54_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_225_elem lane_2_147_elem => Forall (fun iter_0_102_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_102_elem))) (fpmin_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_225_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_147_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.PMIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_49 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_227_elem lane_2_149_elem => Map (fun iter_0_103_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_103_elem)) (fpmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_227_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_149_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_56_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_56_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_228_elem lane_2_150_elem => Forall (fun iter_0_104_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_104_elem))) (fpmin_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_228_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_150_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.PMIN) v128_1 v128_2 v128_lst
  | fun_vbinop__case_50 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_230_elem lane_2_152_elem => Map (fun iter_0_105_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_105_elem)) (fpmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_230_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_152_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_58_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) lane_lst_58_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_231_elem lane_2_153_elem => Forall (fun iter_0_106_elem => wf_lane_ (lanetype_Fnn Fnn.F32) (lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 iter_0_106_elem))) (fpmax_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_231_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_153_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F32 M_0 vbinop_Fnn_N.PMAX) v128_1 v128_2 v128_lst
  | fun_vbinop__case_51 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_lst_lst : List (List lane_)) (v128_lst : List vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    lane_lst_lst == (setproduct_ lane_ (Map₂ (fun lane_1_233_elem lane_2_155_elem => Map (fun iter_0_107_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_107_elem)) (fpmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_233_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_155_elem)))))) lane_1_lst lane_2_lst)) →
    v128_lst == (Map (fun lane_lst_60_elem => inv_lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) lane_lst_60_elem) lane_lst_lst) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall₂ (fun lane_1_234_elem lane_2_156_elem => Forall (fun iter_0_108_elem => wf_lane_ (lanetype_Fnn Fnn.F64) (lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 iter_0_108_elem))) (fpmax_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_234_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_156_elem)))))) lane_1_lst lane_2_lst →
    v_M == M_0 →
    fun_vbinop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vbinop_.mk_vbinop__1 Fnn.F64 M_0 vbinop_Fnn_N.PMAX) v128_1 v128_2 v128_lst


inductive vbinop__is_wf : shape → vbinop_ → vec_ → vec_ → List vec_ → Prop where
  | vbinop__is_wf_0 (v_shape : shape) (v_vbinop_ : vbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val_lst : List vec_) (var_0 : List vec_) : 
    fun_vbinop_ v_shape v_vbinop_ v_vec_ vec__0 var_0 →
    wf_shape v_shape →
    wf_vbinop_ v_shape v_vbinop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val_lst == var_0 →
    Forall (fun ret_val_elem => wf_uN 128 ret_val_elem) ret_val_lst →
    vbinop__is_wf v_shape v_vbinop_ v_vec_ vec__0 ret_val_lst


inductive fun_vrelop_ : shape → vrelop_ → vec_ → vec_ → vec_ → Prop where
  | fun_vrelop__case_0 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_236_elem => (proj_lane__2 lane_1_236_elem) != none) lane_1_lst →
    Forall (fun lane_2_158_elem => (proj_lane__2 lane_2_158_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_236_elem lane_2_158_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_236_elem)) (Option.get! (proj_lane__2 lane_2_158_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_3_2_elem => lane_.mk_lane__2 Jnn.I32 lane_3_2_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_237_elem => (proj_lane__2 lane_1_237_elem) != none) lane_1_lst →
    Forall (fun lane_2_159_elem => (proj_lane__2 lane_2_159_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_237_elem lane_2_159_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_237_elem)) (Option.get! (proj_lane__2 lane_2_159_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_3_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_3_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_1 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_239_elem => (proj_lane__2 lane_1_239_elem) != none) lane_1_lst →
    Forall (fun lane_2_161_elem => (proj_lane__2 lane_2_161_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_239_elem lane_2_161_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_239_elem)) (Option.get! (proj_lane__2 lane_2_161_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_3_5_elem => lane_.mk_lane__2 Jnn.I64 lane_3_5_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_240_elem => (proj_lane__2 lane_1_240_elem) != none) lane_1_lst →
    Forall (fun lane_2_162_elem => (proj_lane__2 lane_2_162_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_240_elem lane_2_162_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_240_elem)) (Option.get! (proj_lane__2 lane_2_162_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_6_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_6_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_2 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_242_elem => (proj_lane__2 lane_1_242_elem) != none) lane_1_lst →
    Forall (fun lane_2_164_elem => (proj_lane__2 lane_2_164_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_242_elem lane_2_164_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_242_elem)) (Option.get! (proj_lane__2 lane_2_164_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_3_8_elem => lane_.mk_lane__2 Jnn.I8 lane_3_8_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_243_elem => (proj_lane__2 lane_1_243_elem) != none) lane_1_lst →
    Forall (fun lane_2_165_elem => (proj_lane__2 lane_2_165_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_243_elem lane_2_165_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_243_elem)) (Option.get! (proj_lane__2 lane_2_165_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_9_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_9_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_3 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_245_elem => (proj_lane__2 lane_1_245_elem) != none) lane_1_lst →
    Forall (fun lane_2_167_elem => (proj_lane__2 lane_2_167_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_245_elem lane_2_167_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_245_elem)) (Option.get! (proj_lane__2 lane_2_167_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_3_11_elem => lane_.mk_lane__2 Jnn.I16 lane_3_11_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_246_elem => (proj_lane__2 lane_1_246_elem) != none) lane_1_lst →
    Forall (fun lane_2_168_elem => (proj_lane__2 lane_2_168_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_246_elem lane_2_168_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ieq_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_246_elem)) (Option.get! (proj_lane__2 lane_2_168_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_12_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_12_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 vrelop_Jnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_4 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_248_elem => (proj_lane__2 lane_1_248_elem) != none) lane_1_lst →
    Forall (fun lane_2_170_elem => (proj_lane__2 lane_2_170_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_248_elem lane_2_170_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_248_elem)) (Option.get! (proj_lane__2 lane_2_170_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_3_14_elem => lane_.mk_lane__2 Jnn.I32 lane_3_14_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_249_elem => (proj_lane__2 lane_1_249_elem) != none) lane_1_lst →
    Forall (fun lane_2_171_elem => (proj_lane__2 lane_2_171_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_249_elem lane_2_171_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I32)) (Option.get! (proj_lane__2 lane_1_249_elem)) (Option.get! (proj_lane__2 lane_2_171_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_15_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_15_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_5 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_251_elem => (proj_lane__2 lane_1_251_elem) != none) lane_1_lst →
    Forall (fun lane_2_173_elem => (proj_lane__2 lane_2_173_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_251_elem lane_2_173_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_251_elem)) (Option.get! (proj_lane__2 lane_2_173_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_3_17_elem => lane_.mk_lane__2 Jnn.I64 lane_3_17_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_252_elem => (proj_lane__2 lane_1_252_elem) != none) lane_1_lst →
    Forall (fun lane_2_174_elem => (proj_lane__2 lane_2_174_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_252_elem lane_2_174_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I64)) (Option.get! (proj_lane__2 lane_1_252_elem)) (Option.get! (proj_lane__2 lane_2_174_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_18_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_18_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_6 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_254_elem => (proj_lane__2 lane_1_254_elem) != none) lane_1_lst →
    Forall (fun lane_2_176_elem => (proj_lane__2 lane_2_176_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_254_elem lane_2_176_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_254_elem)) (Option.get! (proj_lane__2 lane_2_176_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_3_20_elem => lane_.mk_lane__2 Jnn.I8 lane_3_20_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_255_elem => (proj_lane__2 lane_1_255_elem) != none) lane_1_lst →
    Forall (fun lane_2_177_elem => (proj_lane__2 lane_2_177_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_255_elem lane_2_177_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I8)) (Option.get! (proj_lane__2 lane_1_255_elem)) (Option.get! (proj_lane__2 lane_2_177_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_21_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_21_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_7 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_257_elem => (proj_lane__2 lane_1_257_elem) != none) lane_1_lst →
    Forall (fun lane_2_179_elem => (proj_lane__2 lane_2_179_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_257_elem lane_2_179_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_257_elem)) (Option.get! (proj_lane__2 lane_2_179_elem)))))) lane_1_lst lane_2_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_3_23_elem => lane_.mk_lane__2 Jnn.I16 lane_3_23_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_258_elem => (proj_lane__2 lane_1_258_elem) != none) lane_1_lst →
    Forall (fun lane_2_180_elem => (proj_lane__2 lane_2_180_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_258_elem lane_2_180_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (ine_ (lsizenn (lanetype_Jnn Jnn.I16)) (Option.get! (proj_lane__2 lane_1_258_elem)) (Option.get! (proj_lane__2 lane_2_180_elem)))))) lane_1_lst lane_2_lst →
    Forall (fun lane_3_24_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_24_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 vrelop_Jnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_8 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_261_elem => (proj_lane__2 lane_1_261_elem) != none) lane_1_lst →
    Forall (fun lane_2_183_elem => (proj_lane__2 lane_2_183_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_261_elem lane_2_183_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_261_elem)) (Option.get! (proj_lane__2 lane_2_183_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_260_elem => (proj_lane__2 lane_1_260_elem) != none) lane_1_lst →
    Forall (fun lane_2_182_elem => (proj_lane__2 lane_2_182_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_260_elem lane_2_182_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_260_elem)) (Option.get! (proj_lane__2 lane_2_182_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_3_26_elem => lane_.mk_lane__2 Jnn.I32 lane_3_26_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_27_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_27_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_9 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_264_elem => (proj_lane__2 lane_1_264_elem) != none) lane_1_lst →
    Forall (fun lane_2_186_elem => (proj_lane__2 lane_2_186_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_264_elem lane_2_186_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_264_elem)) (Option.get! (proj_lane__2 lane_2_186_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_263_elem => (proj_lane__2 lane_1_263_elem) != none) lane_1_lst →
    Forall (fun lane_2_185_elem => (proj_lane__2 lane_2_185_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_263_elem lane_2_185_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_263_elem)) (Option.get! (proj_lane__2 lane_2_185_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_3_29_elem => lane_.mk_lane__2 Jnn.I64 lane_3_29_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_30_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_30_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_10 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_267_elem => (proj_lane__2 lane_1_267_elem) != none) lane_1_lst →
    Forall (fun lane_2_189_elem => (proj_lane__2 lane_2_189_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_267_elem lane_2_189_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_267_elem)) (Option.get! (proj_lane__2 lane_2_189_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_266_elem => (proj_lane__2 lane_1_266_elem) != none) lane_1_lst →
    Forall (fun lane_2_188_elem => (proj_lane__2 lane_2_188_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_266_elem lane_2_188_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_266_elem)) (Option.get! (proj_lane__2 lane_2_188_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_3_32_elem => lane_.mk_lane__2 Jnn.I8 lane_3_32_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_33_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_33_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_11 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_270_elem => (proj_lane__2 lane_1_270_elem) != none) lane_1_lst →
    Forall (fun lane_2_192_elem => (proj_lane__2 lane_2_192_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_270_elem lane_2_192_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_270_elem)) (Option.get! (proj_lane__2 lane_2_192_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_269_elem => (proj_lane__2 lane_1_269_elem) != none) lane_1_lst →
    Forall (fun lane_2_191_elem => (proj_lane__2 lane_2_191_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_269_elem lane_2_191_elem => fun_ilt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_269_elem)) (Option.get! (proj_lane__2 lane_2_191_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_3_35_elem => lane_.mk_lane__2 Jnn.I16 lane_3_35_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_36_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_36_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.LT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_12 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_273_elem => (proj_lane__2 lane_1_273_elem) != none) lane_1_lst →
    Forall (fun lane_2_195_elem => (proj_lane__2 lane_2_195_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_273_elem lane_2_195_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_273_elem)) (Option.get! (proj_lane__2 lane_2_195_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_272_elem => (proj_lane__2 lane_1_272_elem) != none) lane_1_lst →
    Forall (fun lane_2_194_elem => (proj_lane__2 lane_2_194_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_272_elem lane_2_194_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_272_elem)) (Option.get! (proj_lane__2 lane_2_194_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_3_38_elem => lane_.mk_lane__2 Jnn.I32 lane_3_38_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_39_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_39_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_13 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_276_elem => (proj_lane__2 lane_1_276_elem) != none) lane_1_lst →
    Forall (fun lane_2_198_elem => (proj_lane__2 lane_2_198_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_276_elem lane_2_198_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_276_elem)) (Option.get! (proj_lane__2 lane_2_198_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_275_elem => (proj_lane__2 lane_1_275_elem) != none) lane_1_lst →
    Forall (fun lane_2_197_elem => (proj_lane__2 lane_2_197_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_275_elem lane_2_197_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_275_elem)) (Option.get! (proj_lane__2 lane_2_197_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_3_41_elem => lane_.mk_lane__2 Jnn.I64 lane_3_41_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_42_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_42_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_14 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_279_elem => (proj_lane__2 lane_1_279_elem) != none) lane_1_lst →
    Forall (fun lane_2_201_elem => (proj_lane__2 lane_2_201_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_279_elem lane_2_201_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_279_elem)) (Option.get! (proj_lane__2 lane_2_201_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_278_elem => (proj_lane__2 lane_1_278_elem) != none) lane_1_lst →
    Forall (fun lane_2_200_elem => (proj_lane__2 lane_2_200_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_278_elem lane_2_200_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_278_elem)) (Option.get! (proj_lane__2 lane_2_200_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_3_44_elem => lane_.mk_lane__2 Jnn.I8 lane_3_44_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_45_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_45_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_15 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_282_elem => (proj_lane__2 lane_1_282_elem) != none) lane_1_lst →
    Forall (fun lane_2_204_elem => (proj_lane__2 lane_2_204_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_282_elem lane_2_204_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_282_elem)) (Option.get! (proj_lane__2 lane_2_204_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_281_elem => (proj_lane__2 lane_1_281_elem) != none) lane_1_lst →
    Forall (fun lane_2_203_elem => (proj_lane__2 lane_2_203_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_281_elem lane_2_203_elem => fun_igt_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_281_elem)) (Option.get! (proj_lane__2 lane_2_203_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_3_47_elem => lane_.mk_lane__2 Jnn.I16 lane_3_47_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_48_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_48_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.GT v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_16 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_285_elem => (proj_lane__2 lane_1_285_elem) != none) lane_1_lst →
    Forall (fun lane_2_207_elem => (proj_lane__2 lane_2_207_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_285_elem lane_2_207_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_285_elem)) (Option.get! (proj_lane__2 lane_2_207_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_284_elem => (proj_lane__2 lane_1_284_elem) != none) lane_1_lst →
    Forall (fun lane_2_206_elem => (proj_lane__2 lane_2_206_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_284_elem lane_2_206_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_284_elem)) (Option.get! (proj_lane__2 lane_2_206_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_3_50_elem => lane_.mk_lane__2 Jnn.I32 lane_3_50_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_51_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_51_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_17 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_288_elem => (proj_lane__2 lane_1_288_elem) != none) lane_1_lst →
    Forall (fun lane_2_210_elem => (proj_lane__2 lane_2_210_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_288_elem lane_2_210_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_288_elem)) (Option.get! (proj_lane__2 lane_2_210_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_287_elem => (proj_lane__2 lane_1_287_elem) != none) lane_1_lst →
    Forall (fun lane_2_209_elem => (proj_lane__2 lane_2_209_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_287_elem lane_2_209_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_287_elem)) (Option.get! (proj_lane__2 lane_2_209_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_3_53_elem => lane_.mk_lane__2 Jnn.I64 lane_3_53_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_54_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_54_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_18 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_291_elem => (proj_lane__2 lane_1_291_elem) != none) lane_1_lst →
    Forall (fun lane_2_213_elem => (proj_lane__2 lane_2_213_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_291_elem lane_2_213_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_291_elem)) (Option.get! (proj_lane__2 lane_2_213_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_290_elem => (proj_lane__2 lane_1_290_elem) != none) lane_1_lst →
    Forall (fun lane_2_212_elem => (proj_lane__2 lane_2_212_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_290_elem lane_2_212_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_290_elem)) (Option.get! (proj_lane__2 lane_2_212_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_3_56_elem => lane_.mk_lane__2 Jnn.I8 lane_3_56_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_57_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_57_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_19 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_294_elem => (proj_lane__2 lane_1_294_elem) != none) lane_1_lst →
    Forall (fun lane_2_216_elem => (proj_lane__2 lane_2_216_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_294_elem lane_2_216_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_294_elem)) (Option.get! (proj_lane__2 lane_2_216_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_293_elem => (proj_lane__2 lane_1_293_elem) != none) lane_1_lst →
    Forall (fun lane_2_215_elem => (proj_lane__2 lane_2_215_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_293_elem lane_2_215_elem => fun_ile_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_293_elem)) (Option.get! (proj_lane__2 lane_2_215_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_3_59_elem => lane_.mk_lane__2 Jnn.I16 lane_3_59_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_60_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_60_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.LE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_20 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_297_elem => (proj_lane__2 lane_1_297_elem) != none) lane_1_lst →
    Forall (fun lane_2_219_elem => (proj_lane__2 lane_2_219_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_297_elem lane_2_219_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_297_elem)) (Option.get! (proj_lane__2 lane_2_219_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_296_elem => (proj_lane__2 lane_1_296_elem) != none) lane_1_lst →
    Forall (fun lane_2_218_elem => (proj_lane__2 lane_2_218_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_296_elem lane_2_218_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I32)) v_sx (Option.get! (proj_lane__2 lane_1_296_elem)) (Option.get! (proj_lane__2 lane_2_218_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I32)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) (Map (fun lane_3_62_elem => lane_.mk_lane__2 Jnn.I32 lane_3_62_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_63_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I32) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I32 lane_3_63_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I32 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_21 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_300_elem => (proj_lane__2 lane_1_300_elem) != none) lane_1_lst →
    Forall (fun lane_2_222_elem => (proj_lane__2 lane_2_222_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_300_elem lane_2_222_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_300_elem)) (Option.get! (proj_lane__2 lane_2_222_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_299_elem => (proj_lane__2 lane_1_299_elem) != none) lane_1_lst →
    Forall (fun lane_2_221_elem => (proj_lane__2 lane_2_221_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_299_elem lane_2_221_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I64)) v_sx (Option.get! (proj_lane__2 lane_1_299_elem)) (Option.get! (proj_lane__2 lane_2_221_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I64)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) (Map (fun lane_3_65_elem => lane_.mk_lane__2 Jnn.I64 lane_3_65_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_66_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I64) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I64 lane_3_66_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I64 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_22 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_303_elem => (proj_lane__2 lane_1_303_elem) != none) lane_1_lst →
    Forall (fun lane_2_225_elem => (proj_lane__2 lane_2_225_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_303_elem lane_2_225_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_303_elem)) (Option.get! (proj_lane__2 lane_2_225_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_302_elem => (proj_lane__2 lane_1_302_elem) != none) lane_1_lst →
    Forall (fun lane_2_224_elem => (proj_lane__2 lane_2_224_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_302_elem lane_2_224_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I8)) v_sx (Option.get! (proj_lane__2 lane_1_302_elem)) (Option.get! (proj_lane__2 lane_2_224_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I8)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) (Map (fun lane_3_68_elem => lane_.mk_lane__2 Jnn.I8 lane_3_68_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_69_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I8) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I8 lane_3_69_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I8 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I8 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_23 (v_M : Nat) (v_sx : sx) (v128_1 : uN) (v128_2 : uN) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) (var_1_lst : List uN) (var_0_lst : List uN) : 
    (List.length var_1_lst) == (List.length lane_1_lst) →
    (List.length var_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_306_elem => (proj_lane__2 lane_1_306_elem) != none) lane_1_lst →
    Forall (fun lane_2_228_elem => (proj_lane__2 lane_2_228_elem) != none) lane_2_lst →
    Forall₃ (fun var_1_elem lane_1_306_elem lane_2_228_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_306_elem)) (Option.get! (proj_lane__2 lane_2_228_elem)) var_1_elem) var_1_lst lane_1_lst lane_2_lst →
    (List.length var_0_lst) == (List.length lane_1_lst) →
    (List.length var_0_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_305_elem => (proj_lane__2 lane_1_305_elem) != none) lane_1_lst →
    Forall (fun lane_2_227_elem => (proj_lane__2 lane_2_227_elem) != none) lane_2_lst →
    Forall₃ (fun var_0_elem lane_1_305_elem lane_2_227_elem => fun_ige_ (lsizenn (lanetype_Jnn Jnn.I16)) v_sx (Option.get! (proj_lane__2 lane_1_305_elem)) (Option.get! (proj_lane__2 lane_2_227_elem)) var_0_elem) var_0_lst lane_1_lst lane_2_lst →
    lane_1_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) v128_2) →
    lane_3_lst == (Map (fun var_0_elem => extend__ 1 (lsizenn (lanetype_Jnn Jnn.I16)) sx.S (.mk_uN (proj_uN_0 var_0_elem))) var_0_lst) →
    v128 == (inv_lanes_ (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) (Map (fun lane_3_71_elem => lane_.mk_lane__2 Jnn.I16 lane_3_71_elem) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M)) →
    Forall (fun var_1_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 var_1_elem))) var_1_lst →
    Forall (fun lane_3_72_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Jnn Jnn.I16) (dim.mk_dim v_M))) (lane_.mk_lane__2 Jnn.I16 lane_3_72_elem)) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.I16 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__0 Jnn.I16 M_0 (vrelop_Jnn_N.GE v_sx)) v128_1 v128_2 v128
  | fun_vrelop__case_24 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_308_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_308_elem))) != none) lane_1_lst →
    Forall (fun lane_1_308_elem => (proj_lane__0 lane_1_308_elem) != none) lane_1_lst →
    Forall (fun lane_2_230_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_230_elem))) != none) lane_2_lst →
    Forall (fun lane_2_230_elem => (proj_lane__0 lane_2_230_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_308_elem lane_2_230_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_308_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_230_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_74_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_74_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_309_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_309_elem))) != none) lane_1_lst →
    Forall (fun lane_1_309_elem => (proj_lane__0 lane_1_309_elem) != none) lane_1_lst →
    Forall (fun lane_2_231_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_231_elem))) != none) lane_2_lst →
    Forall (fun lane_2_231_elem => (proj_lane__0 lane_2_231_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_309_elem lane_2_231_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_309_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_231_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_75_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_75_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_25 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_311_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_311_elem))) != none) lane_1_lst →
    Forall (fun lane_1_311_elem => (proj_lane__0 lane_1_311_elem) != none) lane_1_lst →
    Forall (fun lane_2_233_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_233_elem))) != none) lane_2_lst →
    Forall (fun lane_2_233_elem => (proj_lane__0 lane_2_233_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_311_elem lane_2_233_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_311_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_233_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_77_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_77_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_312_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_312_elem))) != none) lane_1_lst →
    Forall (fun lane_1_312_elem => (proj_lane__0 lane_1_312_elem) != none) lane_1_lst →
    Forall (fun lane_2_234_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_234_elem))) != none) lane_2_lst →
    Forall (fun lane_2_234_elem => (proj_lane__0 lane_2_234_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_312_elem lane_2_234_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (feq_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_312_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_234_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_78_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_78_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.EQ) v128_1 v128_2 v128
  | fun_vrelop__case_26 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_314_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_314_elem))) != none) lane_1_lst →
    Forall (fun lane_1_314_elem => (proj_lane__0 lane_1_314_elem) != none) lane_1_lst →
    Forall (fun lane_2_236_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_236_elem))) != none) lane_2_lst →
    Forall (fun lane_2_236_elem => (proj_lane__0 lane_2_236_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_314_elem lane_2_236_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_314_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_236_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_80_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_80_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_315_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_315_elem))) != none) lane_1_lst →
    Forall (fun lane_1_315_elem => (proj_lane__0 lane_1_315_elem) != none) lane_1_lst →
    Forall (fun lane_2_237_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_237_elem))) != none) lane_2_lst →
    Forall (fun lane_2_237_elem => (proj_lane__0 lane_2_237_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_315_elem lane_2_237_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_315_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_237_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_81_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_81_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_27 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_317_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_317_elem))) != none) lane_1_lst →
    Forall (fun lane_1_317_elem => (proj_lane__0 lane_1_317_elem) != none) lane_1_lst →
    Forall (fun lane_2_239_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_239_elem))) != none) lane_2_lst →
    Forall (fun lane_2_239_elem => (proj_lane__0 lane_2_239_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_317_elem lane_2_239_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_317_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_239_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_83_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_83_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_318_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_318_elem))) != none) lane_1_lst →
    Forall (fun lane_1_318_elem => (proj_lane__0 lane_1_318_elem) != none) lane_1_lst →
    Forall (fun lane_2_240_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_240_elem))) != none) lane_2_lst →
    Forall (fun lane_2_240_elem => (proj_lane__0 lane_2_240_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_318_elem lane_2_240_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fne_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_318_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_240_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_84_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_84_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.NE) v128_1 v128_2 v128
  | fun_vrelop__case_28 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_320_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_320_elem))) != none) lane_1_lst →
    Forall (fun lane_1_320_elem => (proj_lane__0 lane_1_320_elem) != none) lane_1_lst →
    Forall (fun lane_2_242_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_242_elem))) != none) lane_2_lst →
    Forall (fun lane_2_242_elem => (proj_lane__0 lane_2_242_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_320_elem lane_2_242_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_320_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_242_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_86_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_86_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_321_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_321_elem))) != none) lane_1_lst →
    Forall (fun lane_1_321_elem => (proj_lane__0 lane_1_321_elem) != none) lane_1_lst →
    Forall (fun lane_2_243_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_243_elem))) != none) lane_2_lst →
    Forall (fun lane_2_243_elem => (proj_lane__0 lane_2_243_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_321_elem lane_2_243_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_321_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_243_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_87_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_87_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.LT) v128_1 v128_2 v128
  | fun_vrelop__case_29 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_323_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_323_elem))) != none) lane_1_lst →
    Forall (fun lane_1_323_elem => (proj_lane__0 lane_1_323_elem) != none) lane_1_lst →
    Forall (fun lane_2_245_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_245_elem))) != none) lane_2_lst →
    Forall (fun lane_2_245_elem => (proj_lane__0 lane_2_245_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_323_elem lane_2_245_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_323_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_245_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_89_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_89_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_324_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_324_elem))) != none) lane_1_lst →
    Forall (fun lane_1_324_elem => (proj_lane__0 lane_1_324_elem) != none) lane_1_lst →
    Forall (fun lane_2_246_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_246_elem))) != none) lane_2_lst →
    Forall (fun lane_2_246_elem => (proj_lane__0 lane_2_246_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_324_elem lane_2_246_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (flt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_324_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_246_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_90_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_90_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.LT) v128_1 v128_2 v128
  | fun_vrelop__case_30 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_326_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_326_elem))) != none) lane_1_lst →
    Forall (fun lane_1_326_elem => (proj_lane__0 lane_1_326_elem) != none) lane_1_lst →
    Forall (fun lane_2_248_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_248_elem))) != none) lane_2_lst →
    Forall (fun lane_2_248_elem => (proj_lane__0 lane_2_248_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_326_elem lane_2_248_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_326_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_248_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_92_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_92_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_327_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_327_elem))) != none) lane_1_lst →
    Forall (fun lane_1_327_elem => (proj_lane__0 lane_1_327_elem) != none) lane_1_lst →
    Forall (fun lane_2_249_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_249_elem))) != none) lane_2_lst →
    Forall (fun lane_2_249_elem => (proj_lane__0 lane_2_249_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_327_elem lane_2_249_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_327_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_249_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_93_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_93_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.GT) v128_1 v128_2 v128
  | fun_vrelop__case_31 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_329_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_329_elem))) != none) lane_1_lst →
    Forall (fun lane_1_329_elem => (proj_lane__0 lane_1_329_elem) != none) lane_1_lst →
    Forall (fun lane_2_251_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_251_elem))) != none) lane_2_lst →
    Forall (fun lane_2_251_elem => (proj_lane__0 lane_2_251_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_329_elem lane_2_251_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_329_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_251_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_95_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_95_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_330_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_330_elem))) != none) lane_1_lst →
    Forall (fun lane_1_330_elem => (proj_lane__0 lane_1_330_elem) != none) lane_1_lst →
    Forall (fun lane_2_252_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_252_elem))) != none) lane_2_lst →
    Forall (fun lane_2_252_elem => (proj_lane__0 lane_2_252_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_330_elem lane_2_252_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fgt_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_330_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_252_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_96_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_96_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.GT) v128_1 v128_2 v128
  | fun_vrelop__case_32 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_332_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_332_elem))) != none) lane_1_lst →
    Forall (fun lane_1_332_elem => (proj_lane__0 lane_1_332_elem) != none) lane_1_lst →
    Forall (fun lane_2_254_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_254_elem))) != none) lane_2_lst →
    Forall (fun lane_2_254_elem => (proj_lane__0 lane_2_254_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_332_elem lane_2_254_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_332_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_254_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_98_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_98_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_333_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_333_elem))) != none) lane_1_lst →
    Forall (fun lane_1_333_elem => (proj_lane__0 lane_1_333_elem) != none) lane_1_lst →
    Forall (fun lane_2_255_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_255_elem))) != none) lane_2_lst →
    Forall (fun lane_2_255_elem => (proj_lane__0 lane_2_255_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_333_elem lane_2_255_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_333_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_255_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_99_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_99_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.LE) v128_1 v128_2 v128
  | fun_vrelop__case_33 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_335_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_335_elem))) != none) lane_1_lst →
    Forall (fun lane_1_335_elem => (proj_lane__0 lane_1_335_elem) != none) lane_1_lst →
    Forall (fun lane_2_257_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_257_elem))) != none) lane_2_lst →
    Forall (fun lane_2_257_elem => (proj_lane__0 lane_2_257_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_335_elem lane_2_257_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_335_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_257_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_101_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_101_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_336_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_336_elem))) != none) lane_1_lst →
    Forall (fun lane_1_336_elem => (proj_lane__0 lane_1_336_elem) != none) lane_1_lst →
    Forall (fun lane_2_258_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_258_elem))) != none) lane_2_lst →
    Forall (fun lane_2_258_elem => (proj_lane__0 lane_2_258_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_336_elem lane_2_258_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fle_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_336_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_258_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_102_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_102_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.LE) v128_1 v128_2 v128
  | fun_vrelop__case_34 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_338_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_338_elem))) != none) lane_1_lst →
    Forall (fun lane_1_338_elem => (proj_lane__0 lane_1_338_elem) != none) lane_1_lst →
    Forall (fun lane_2_260_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_260_elem))) != none) lane_2_lst →
    Forall (fun lane_2_260_elem => (proj_lane__0 lane_2_260_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_338_elem lane_2_260_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F32)) sx.S (.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_338_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_260_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F32)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F32))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_104_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_104_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F32) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_339_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_339_elem))) != none) lane_1_lst →
    Forall (fun lane_1_339_elem => (proj_lane__0 lane_1_339_elem) != none) lane_1_lst →
    Forall (fun lane_2_261_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_261_elem))) != none) lane_2_lst →
    Forall (fun lane_2_261_elem => (proj_lane__0 lane_2_261_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_339_elem lane_2_261_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F32)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_339_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_261_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_105_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_105_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F32 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F32 M_0 vrelop_Fnn_N.GE) v128_1 v128_2 v128
  | fun_vrelop__case_35 (v_M : Nat) (v128_1 : uN) (v128_2 : uN) (v_Inn : Inn) (M_0 : Nat) (lane_1_lst : List lane_) (lane_2_lst : List lane_) (lane_3_lst : List iN) (v128 : vec_) : 
    lane_1_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_1) →
    lane_2_lst == (lanes_ (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) v128_2) →
    Forall (fun lane_1_341_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_341_elem))) != none) lane_1_lst →
    Forall (fun lane_1_341_elem => (proj_lane__0 lane_1_341_elem) != none) lane_1_lst →
    Forall (fun lane_2_263_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_263_elem))) != none) lane_2_lst →
    Forall (fun lane_2_263_elem => (proj_lane__0 lane_2_263_elem) != none) lane_2_lst →
    lane_3_lst == (Map₂ (fun lane_1_341_elem lane_2_263_elem => extend__ 1 (sizenn (numtype_Fnn Fnn.F64)) sx.S (.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_341_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_263_elem)))))))) lane_1_lst lane_2_lst) →
    (size (valtype_Fnn Fnn.F64)) != none →
    (isize v_Inn) == (Option.get! (size (valtype_Fnn Fnn.F64))) →
    v128 == (inv_lanes_ (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) (Map (fun lane_3_107_elem => lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_107_elem)))) lane_3_lst)) →
    wf_shape (shape.X (lanetype_Fnn Fnn.F64) (dim.mk_dim v_M)) →
    (List.length lane_1_lst) == (List.length lane_2_lst) →
    Forall (fun lane_1_342_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_1_342_elem))) != none) lane_1_lst →
    Forall (fun lane_1_342_elem => (proj_lane__0 lane_1_342_elem) != none) lane_1_lst →
    Forall (fun lane_2_264_elem => (proj_num__1 (Option.get! (proj_lane__0 lane_2_264_elem))) != none) lane_2_lst →
    Forall (fun lane_2_264_elem => (proj_lane__0 lane_2_264_elem) != none) lane_2_lst →
    Forall₂ (fun lane_1_342_elem lane_2_264_elem => wf_uN 1 (uN.mk_uN (proj_uN_0 (fge_ (sizenn (numtype_Fnn Fnn.F64)) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_1_342_elem)))) (Option.get! (proj_num__1 (Option.get! (proj_lane__0 lane_2_264_elem)))))))) lane_1_lst lane_2_lst →
    wf_shape (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M)) →
    Forall (fun lane_3_108_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn v_Inn) (dim.mk_dim v_M))) (lane_.mk_lane__0 (numtype_Inn v_Inn) (num_.mk_num__0 v_Inn (uN.mk_uN (proj_uN_0 lane_3_108_elem))))) lane_3_lst →
    v_M == M_0 →
    fun_vrelop_ (shape.X lanetype.F64 (dim.mk_dim v_M)) (vrelop_.mk_vrelop__1 Fnn.F64 M_0 vrelop_Fnn_N.GE) v128_1 v128_2 v128


inductive vrelop__is_wf : shape → vrelop_ → vec_ → vec_ → vec_ → Prop where
  | vrelop__is_wf_0 (v_shape : shape) (v_vrelop_ : vrelop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) : 
    fun_vrelop_ v_shape v_vrelop_ v_vec_ vec__0 var_0 →
    wf_shape v_shape →
    wf_vrelop_ v_shape v_vrelop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val == var_0 →
    wf_uN 128 ret_val →
    vrelop__is_wf v_shape v_vrelop_ v_vec_ vec__0 ret_val


def vcvtop__ (shape_1 : shape) (shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : lane_) : List lane_ :=
  match shape_1, shape_2, v_vcvtop, v_lane_ with
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I32 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I64 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I8 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I8 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.I16 (dim.mk_dim M_2), vcvtop.EXTEND v_half v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__2 Jnn.I16 iN_2]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2)]
  | shape.X lanetype.I32 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I32 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.I64 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I64 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.I8 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I8 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.I16 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.CONVERT half_opt v_sx, lane_.mk_lane__2 Jnn.I16 iN_1 => TEMPORARY_PREM → [lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2)]
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => TEMPORARY_PREM → list_ lane_ (OMap (fun iN_2_2_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 iN_2_2_elem)) iN_2_opt)
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => TEMPORARY_PREM → list_ lane_ (OMap (fun iN_2_4_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 iN_2_4_elem)) iN_2_opt)
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.I32 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => TEMPORARY_PREM → list_ lane_ (OMap (fun iN_2_6_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 iN_2_6_elem)) iN_2_opt)
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.I64 (dim.mk_dim M_2), vcvtop.TRUNC_SAT v_sx zero_opt, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => TEMPORARY_PREM → list_ lane_ (OMap (fun iN_2_8_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 iN_2_8_elem)) iN_2_opt)
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => TEMPORARY_PREM → Map (fun fN_2_2_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_2_elem)) fN_2_lst
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => TEMPORARY_PREM → Map (fun fN_2_4_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_4_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => TEMPORARY_PREM → Map (fun fN_2_6_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_6_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.DEMOTE zero.ZERO, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => TEMPORARY_PREM → Map (fun fN_2_8_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_8_elem)) fN_2_lst
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => TEMPORARY_PREM → Map (fun fN_2_10_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_10_elem)) fN_2_lst
  | shape.X lanetype.F32 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F32 (num_.mk_num__1 Fnn.F32 fN_1) => TEMPORARY_PREM → Map (fun fN_2_12_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_12_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F32 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => TEMPORARY_PREM → Map (fun fN_2_14_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F32) (num_.mk_num__1 Fnn.F32 fN_2_14_elem)) fN_2_lst
  | shape.X lanetype.F64 (dim.mk_dim M_1), shape.X lanetype.F64 (dim.mk_dim M_2), vcvtop.PROMOTELOW, lane_.mk_lane__0 numtype.F64 (num_.mk_num__1 Fnn.F64 fN_1) => TEMPORARY_PREM → Map (fun fN_2_16_elem => lane_.mk_lane__0 (numtype_Fnn Fnn.F64) (num_.mk_num__1 Fnn.F64 fN_2_16_elem)) fN_2_lst

inductive vcvtop___is_wf : shape → shape → vcvtop → lane_ → List lane_ → Prop where
  | vcvtop___is_wf_0 (shape_1 : shape) (shape_2 : shape) (v_vcvtop : vcvtop) (v_lane_ : lane_) (ret_val_lst : List lane_) : 
    wf_shape shape_1 →
    wf_shape shape_2 →
    wf_lane_ (fun_lanetype shape_1) v_lane_ →
    ret_val_lst == (vcvtop__ shape_1 shape_2 v_vcvtop v_lane_) →
    Forall (fun ret_val_elem => wf_lane_ (fun_lanetype shape_2) ret_val_elem) ret_val_lst →
    vcvtop___is_wf shape_1 shape_2 v_vcvtop v_lane_ ret_val_lst


inductive fun_vextunop__ : ishape → ishape → vextunop_ → vec_ → vec_ → Prop where
  | fun_vextunop___case_0 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) : 
    ci_lst == (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    Forall (fun ci_2_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_elem))) != none) ci_lst →
    Forall (fun ci_2_elem => (proj_lane__0 ci_2_elem) != none) ci_lst →
    (concat_ iN (Map₂ (fun cj_1_1_elem cj_2_1_elem => [cj_1_1_elem, cj_2_1_elem]) cj_1_lst cj_2_lst)) == (Map (fun ci_2_elem => extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_elem))))) ci_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun cj_1_2_elem cj_2_2_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_2_elem cj_2_2_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_3_elem cj_2_3_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_3_elem cj_2_3_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I32 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_1 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) : 
    ci_lst == (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    Forall (fun ci_4_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_4_elem))) != none) ci_lst →
    Forall (fun ci_4_elem => (proj_lane__0 ci_4_elem) != none) ci_lst →
    (concat_ iN (Map₂ (fun cj_1_4_elem cj_2_4_elem => [cj_1_4_elem, cj_2_4_elem]) cj_1_lst cj_2_lst)) == (Map (fun ci_4_elem => extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_4_elem))))) ci_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun cj_1_5_elem cj_2_5_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_5_elem cj_2_5_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_6_elem cj_2_6_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_6_elem cj_2_6_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I32 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_2 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) : 
    ci_lst == (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    Forall (fun ci_6_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_6_elem))) != none) ci_lst →
    Forall (fun ci_6_elem => (proj_lane__0 ci_6_elem) != none) ci_lst →
    (concat_ iN (Map₂ (fun cj_1_7_elem cj_2_7_elem => [cj_1_7_elem, cj_2_7_elem]) cj_1_lst cj_2_lst)) == (Map (fun ci_6_elem => extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_6_elem))))) ci_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun cj_1_8_elem cj_2_8_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_8_elem cj_2_8_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_9_elem cj_2_9_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_9_elem cj_2_9_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I64 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c
  | fun_vextunop___case_3 (M_1 : Nat) (M_2 : Nat) (v_sx : sx) (c_1 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_lst : List lane_) (c : vec_) : 
    ci_lst == (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    Forall (fun ci_8_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_8_elem))) != none) ci_lst →
    Forall (fun ci_8_elem => (proj_lane__0 ci_8_elem) != none) ci_lst →
    (concat_ iN (Map₂ (fun cj_1_10_elem cj_2_10_elem => [cj_1_10_elem, cj_2_10_elem]) cj_1_lst cj_2_lst)) == (Map (fun ci_8_elem => extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_8_elem))))) ci_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun cj_1_11_elem cj_2_11_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_11_elem cj_2_11_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_12_elem cj_2_12_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_12_elem cj_2_12_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextunop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextunop_.mk_vextunop__0 Jnn.I64 M_1_0 (vextunop_Jnn_N.EXTADD_PAIRWISE v_sx)) c_1 c


inductive vextunop___is_wf : ishape → ishape → vextunop_ → vec_ → vec_ → Prop where
  | vextunop___is_wf_0 (ishape_1 : ishape) (ishape_2 : ishape) (v_vextunop_ : vextunop_) (v_vec_ : vec_) (ret_val : vec_) (var_0 : vec_) : 
    fun_vextunop__ ishape_1 ishape_2 v_vextunop_ v_vec_ var_0 →
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextunop_ ishape_1 v_vextunop_ →
    wf_uN 128 v_vec_ →
    ret_val == var_0 →
    wf_uN 128 ret_val →
    vextunop___is_wf ishape_1 ishape_2 v_vextunop_ v_vec_ ret_val


inductive fun_vextbinop__ : ishape → ishape → vextbinop_ → vec_ → vec_ → vec_ → Prop where
  | fun_vextbinop___case_0 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2))) →
    Forall (fun ci_1_2_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_2_elem))) != none) ci_1_lst →
    Forall (fun ci_1_2_elem => (proj_lane__0 ci_1_2_elem) != none) ci_1_lst →
    Forall (fun ci_2_2_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_2_elem))) != none) ci_2_lst →
    Forall (fun ci_2_2_elem => (proj_lane__0 ci_2_2_elem) != none) ci_2_lst →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun ci_1_2_elem ci_2_2_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_2_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_2_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) == (List.length ci_2_lst) →
    Forall (fun ci_1_3_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_3_elem))) != none) ci_1_lst →
    Forall (fun ci_1_3_elem => (proj_lane__0 ci_1_3_elem) != none) ci_1_lst →
    Forall (fun ci_2_3_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_3_elem))) != none) ci_2_lst →
    Forall (fun ci_2_3_elem => (proj_lane__0 ci_2_3_elem) != none) ci_2_lst →
    Forall₂ (fun ci_1_3_elem ci_2_3_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_3_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_3_elem))))))))) ci_1_lst ci_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_1 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2))) →
    Forall (fun ci_1_5_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_5_elem))) != none) ci_1_lst →
    Forall (fun ci_1_5_elem => (proj_lane__0 ci_1_5_elem) != none) ci_1_lst →
    Forall (fun ci_2_5_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_5_elem))) != none) ci_2_lst →
    Forall (fun ci_2_5_elem => (proj_lane__0 ci_2_5_elem) != none) ci_2_lst →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun ci_1_5_elem ci_2_5_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_5_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_5_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) == (List.length ci_2_lst) →
    Forall (fun ci_1_6_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_6_elem))) != none) ci_1_lst →
    Forall (fun ci_1_6_elem => (proj_lane__0 ci_1_6_elem) != none) ci_1_lst →
    Forall (fun ci_2_6_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_6_elem))) != none) ci_2_lst →
    Forall (fun ci_2_6_elem => (proj_lane__0 ci_2_6_elem) != none) ci_2_lst →
    Forall₂ (fun ci_1_6_elem ci_2_6_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_6_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_6_elem))))))))) ci_1_lst ci_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_2 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2))) →
    Forall (fun ci_1_8_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_8_elem))) != none) ci_1_lst →
    Forall (fun ci_1_8_elem => (proj_lane__0 ci_1_8_elem) != none) ci_1_lst →
    Forall (fun ci_2_8_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_8_elem))) != none) ci_2_lst →
    Forall (fun ci_2_8_elem => (proj_lane__0 ci_2_8_elem) != none) ci_2_lst →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun ci_1_8_elem ci_2_8_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_8_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_8_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) == (List.length ci_2_lst) →
    Forall (fun ci_1_9_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_9_elem))) != none) ci_1_lst →
    Forall (fun ci_1_9_elem => (proj_lane__0 ci_1_9_elem) != none) ci_1_lst →
    Forall (fun ci_2_9_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_9_elem))) != none) ci_2_lst →
    Forall (fun ci_2_9_elem => (proj_lane__0 ci_2_9_elem) != none) ci_2_lst →
    Forall₂ (fun ci_1_9_elem ci_2_9_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_9_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_9_elem))))))))) ci_1_lst ci_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_3 (M_1 : Nat) (M_2 : Nat) (v_half : half) (v_sx : sx) (c_1 : uN) (c_2 : uN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1))) →
    ci_2_lst == (List.take M_1 (List.drop (fun_half v_half 0 M_1) (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2))) →
    Forall (fun ci_1_11_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_11_elem))) != none) ci_1_lst →
    Forall (fun ci_1_11_elem => (proj_lane__0 ci_1_11_elem) != none) ci_1_lst →
    Forall (fun ci_2_11_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_11_elem))) != none) ci_2_lst →
    Forall (fun ci_2_11_elem => (proj_lane__0 ci_2_11_elem) != none) ci_2_lst →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun ci_1_11_elem ci_2_11_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_11_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_11_elem)))))))) ci_1_lst ci_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length ci_1_lst) == (List.length ci_2_lst) →
    Forall (fun ci_1_12_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_12_elem))) != none) ci_1_lst →
    Forall (fun ci_1_12_elem => (proj_lane__0 ci_1_12_elem) != none) ci_1_lst →
    Forall (fun ci_2_12_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_12_elem))) != none) ci_2_lst →
    Forall (fun ci_2_12_elem => (proj_lane__0 ci_2_12_elem) != none) ci_2_lst →
    Forall₂ (fun ci_1_12_elem ci_2_12_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_12_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) v_sx (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_12_elem))))))))) ci_1_lst ci_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 (vextbinop_Jnn_N.EXTMUL v_half v_sx)) c_1 c_2 c
  | fun_vextbinop___case_4 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    ci_2_lst == (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2) →
    Forall (fun ci_1_14_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_14_elem))) != none) ci_1_lst →
    Forall (fun ci_1_14_elem => (proj_lane__0 ci_1_14_elem) != none) ci_1_lst →
    Forall (fun ci_2_14_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_14_elem))) != none) ci_2_lst →
    Forall (fun ci_2_14_elem => (proj_lane__0 ci_2_14_elem) != none) ci_2_lst →
    (concat_ iN (Map₂ (fun cj_1_13_elem cj_2_13_elem => [cj_1_13_elem, cj_2_13_elem]) cj_1_lst cj_2_lst)) == (Map₂ (fun ci_1_14_elem ci_2_14_elem => imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_14_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_14_elem)))))) ci_1_lst ci_2_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun cj_1_14_elem cj_2_14_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_14_elem cj_2_14_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_15_elem cj_2_15_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_15_elem cj_2_15_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c
  | fun_vextbinop___case_5 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    ci_2_lst == (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2) →
    Forall (fun ci_1_16_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_16_elem))) != none) ci_1_lst →
    Forall (fun ci_1_16_elem => (proj_lane__0 ci_1_16_elem) != none) ci_1_lst →
    Forall (fun ci_2_16_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_16_elem))) != none) ci_2_lst →
    Forall (fun ci_2_16_elem => (proj_lane__0 ci_2_16_elem) != none) ci_2_lst →
    (concat_ iN (Map₂ (fun cj_1_16_elem cj_2_16_elem => [cj_1_16_elem, cj_2_16_elem]) cj_1_lst cj_2_lst)) == (Map₂ (fun ci_1_16_elem ci_2_16_elem => imul_ (lsizenn1 (lanetype_Inn Inn.I32)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_16_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I32)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_16_elem)))))) ci_1_lst ci_2_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) (Map₂ (fun cj_1_17_elem cj_2_17_elem => lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_17_elem cj_2_17_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_18_elem cj_2_18_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I32) (num_.mk_num__0 Inn.I32 (iadd_ (lsizenn1 (lanetype_Inn Inn.I32)) cj_1_18_elem cj_2_18_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I32 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I32 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c
  | fun_vextbinop___case_6 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_1) →
    ci_2_lst == (lanes_ (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) c_2) →
    Forall (fun ci_1_18_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_18_elem))) != none) ci_1_lst →
    Forall (fun ci_1_18_elem => (proj_lane__0 ci_1_18_elem) != none) ci_1_lst →
    Forall (fun ci_2_18_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_18_elem))) != none) ci_2_lst →
    Forall (fun ci_2_18_elem => (proj_lane__0 ci_2_18_elem) != none) ci_2_lst →
    (concat_ iN (Map₂ (fun cj_1_19_elem cj_2_19_elem => [cj_1_19_elem, cj_2_19_elem]) cj_1_lst cj_2_lst)) == (Map₂ (fun ci_1_18_elem ci_2_18_elem => imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_18_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I32)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_18_elem)))))) ci_1_lst ci_2_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun cj_1_20_elem cj_2_20_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_20_elem cj_2_20_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I32) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_21_elem cj_2_21_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_21_elem cj_2_21_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I32 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c
  | fun_vextbinop___case_7 (M_1 : Nat) (M_2 : Nat) (c_1 : uN) (c_2 : uN) (cj_1_lst : List iN) (cj_2_lst : List iN) (M_1_0 : Nat) (ci_1_lst : List lane_) (ci_2_lst : List lane_) (c : vec_) : 
    ci_1_lst == (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_1) →
    ci_2_lst == (lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) c_2) →
    Forall (fun ci_1_20_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_1_20_elem))) != none) ci_1_lst →
    Forall (fun ci_1_20_elem => (proj_lane__0 ci_1_20_elem) != none) ci_1_lst →
    Forall (fun ci_2_20_elem => (proj_num__0 (Option.get! (proj_lane__0 ci_2_20_elem))) != none) ci_2_lst →
    Forall (fun ci_2_20_elem => (proj_lane__0 ci_2_20_elem) != none) ci_2_lst →
    (concat_ iN (Map₂ (fun cj_1_22_elem cj_2_22_elem => [cj_1_22_elem, cj_2_22_elem]) cj_1_lst cj_2_lst)) == (Map₂ (fun ci_1_20_elem ci_2_20_elem => imul_ (lsizenn1 (lanetype_Inn Inn.I64)) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_1_20_elem))))) (extend__ (lsizenn2 (lanetype_Inn Inn.I64)) (lsizenn1 (lanetype_Inn Inn.I64)) sx.S (Option.get! (proj_num__0 (Option.get! (proj_lane__0 ci_2_20_elem)))))) ci_1_lst ci_2_lst) →
    c == (inv_lanes_ (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) (Map₂ (fun cj_1_23_elem cj_2_23_elem => lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_23_elem cj_2_23_elem))) cj_1_lst cj_2_lst)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_2)) →
    wf_shape (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1)) →
    (List.length cj_1_lst) == (List.length cj_2_lst) →
    Forall₂ (fun cj_1_24_elem cj_2_24_elem => wf_lane_ (fun_lanetype (shape.X (lanetype_Inn Inn.I64) (dim.mk_dim M_1))) (lane_.mk_lane__0 (numtype_Inn Inn.I64) (num_.mk_num__0 Inn.I64 (iadd_ (lsizenn1 (lanetype_Inn Inn.I64)) cj_1_24_elem cj_2_24_elem)))) cj_1_lst cj_2_lst →
    M_1 == M_1_0 →
    fun_vextbinop__ (ishape.X Jnn.I64 (dim.mk_dim M_1)) (ishape.X Jnn.I64 (dim.mk_dim M_2)) (vextbinop_.mk_vextbinop__0 Jnn.I64 M_1_0 vextbinop_Jnn_N.DOTS) c_1 c_2 c


inductive vextbinop___is_wf : ishape → ishape → vextbinop_ → vec_ → vec_ → vec_ → Prop where
  | vextbinop___is_wf_0 (ishape_1 : ishape) (ishape_2 : ishape) (v_vextbinop_ : vextbinop_) (v_vec_ : vec_) (vec__0 : vec_) (ret_val : vec_) (var_0 : vec_) : 
    fun_vextbinop__ ishape_1 ishape_2 v_vextbinop_ v_vec_ vec__0 var_0 →
    wf_ishape ishape_1 →
    wf_ishape ishape_2 →
    wf_vextbinop_ ishape_1 v_vextbinop_ →
    wf_uN 128 v_vec_ →
    wf_uN 128 vec__0 →
    ret_val == var_0 →
    wf_uN 128 ret_val →
    vextbinop___is_wf ishape_1 ishape_2 v_vextbinop_ v_vec_ vec__0 ret_val


inductive fun_vshiftop_ : ishape → vshiftop_ → lane_ → u32 → lane_ → Prop where
  | fun_vshiftop__case_0 (v_Jnn : Jnn) (v_M : Nat) (lane : uN) (v_n : Nat) (Jnn_1 : Jnn) (Jnn_0 : Jnn) (M_0 : Nat) : 
    v_Jnn == Jnn_1 →
    v_Jnn == Jnn_0 →
    v_M == M_0 →
    fun_vshiftop_ (ishape.X v_Jnn (dim.mk_dim v_M)) (vshiftop_.mk_vshiftop__0 Jnn_0 M_0 vshiftop_Jnn_N.SHL) (lane_.mk_lane__2 Jnn_1 lane) (.mk_uN v_n) (lane_.mk_lane__2 v_Jnn (ishl_ (lsizenn (lanetype_Jnn v_Jnn)) lane (.mk_uN v_n)))
  | fun_vshiftop__case_1 (v_Jnn : Jnn) (v_M : Nat) (v_sx : sx) (lane : uN) (v_n : Nat) (Jnn_1 : Jnn) (Jnn_0 : Jnn) (M_0 : Nat) : 
    v_Jnn == Jnn_1 →
    v_Jnn == Jnn_0 →
    v_M == M_0 →
    fun_vshiftop_ (ishape.X v_Jnn (dim.mk_dim v_M)) (vshiftop_.mk_vshiftop__0 Jnn_0 M_0 (vshiftop_Jnn_N.SHR v_sx)) (lane_.mk_lane__2 Jnn_1 lane) (.mk_uN v_n) (lane_.mk_lane__2 v_Jnn (ishr_ (lsizenn (lanetype_Jnn v_Jnn)) v_sx lane (.mk_uN v_n)))


inductive vshiftop__is_wf : ishape → vshiftop_ → lane_ → u32 → lane_ → Prop where
  | vshiftop__is_wf_0 (v_ishape : ishape) (v_vshiftop_ : vshiftop_) (v_lane_ : lane_) (v_u32 : u32) (ret_val : lane_) (var_0 : lane_) : 
    fun_vshiftop_ v_ishape v_vshiftop_ v_lane_ v_u32 var_0 →
    wf_ishape v_ishape →
    wf_vshiftop_ v_ishape v_vshiftop_ →
    wf_lane_ (fun_lanetype (shape_ishape v_ishape)) v_lane_ →
    wf_uN 32 v_u32 →
    ret_val == var_0 →
    wf_lane_ (fun_lanetype (shape_ishape v_ishape)) ret_val →
    vshiftop__is_wf v_ishape v_vshiftop_ v_lane_ v_u32 ret_val

