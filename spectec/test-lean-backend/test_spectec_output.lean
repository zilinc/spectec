def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

opaque rat_to_nat (r : Rat) : Nat := by 
  first
     | exact Inhabited.default
     | intros ; assumption


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

def disjoint_ (X : Type) [BEq X] (var_0_lst : List X) : Bool :=
  match var_0_lst with
  | [] => true
  | w :: w'_lst => (! (List.contains w'_lst w)) && (disjoint_ X w'_lst)

inductive Nat_ok : Nat → Nat → Prop where
  | refl (v_n : n) : Nat_ok v_n v_n


inductive Nats_ok : List Nat → List Nat → Prop where
  | all (n_lst : List n) : 
    (∀ v_n_elem ∈ n_lst, Nat_ok v_n_elem v_n_elem) →
    Nats_ok n_lst n_lst


inductive Pair_ok : Nat → Nat → Prop where
  | eq (v_n : n) : Pair_ok v_n v_n


inductive Pairs_ok : List Nat → List Nat → Prop where
  | all (n_lst : List n) (m_lst : List m) : 
    (List.length m_lst) == (List.length n_lst) →
    (∀ __iter_tuple ∈ m_lst |>.zip n_lst, Pair_ok (__iter_tuple.2) (__iter_tuple.1)) →
    Pairs_ok n_lst m_lst


inductive list (X : Type) : Type where
  | mk_list (X_lst : List X) : list X
deriving Inhabited, BEq

inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq

def proj_byte_0 (x : byte) : Nat :=
  match x with
  | byte.mk_byte v_num_0 => (v_num_0)

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

def proj_sN_0 (x : sN) : Int :=
  match x with
  | sN.mk_sN v_num_0 => (v_num_0)

inductive wf_sN : N → sN → Prop where
  | sN_case_0 (v_N : N) (i : Int) : 
    (((i ≥ (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int))) && (i ≤ (- (1 : Int)))) || (i == (0 : Int))) || ((i ≥ (1 : Int)) && (i ≤ (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)))) →
    wf_sN v_N (sN.mk_sN i)


abbrev iN : Type := uN

abbrev u31 : Type := uN

abbrev u32 : Type := uN

abbrev u64 : Type := uN

abbrev i32 : Type := iN

abbrev i64 : Type := iN

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

inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq

def proj_char_0 (x : char) : Nat :=
  match x with
  | char.mk_char v_num_0 => (v_num_0)

inductive wf_char : char → Prop where
  | char_case_0 (i : Nat) : 
    ((i ≥ 0) && (i ≤ 55295)) || ((i ≥ 57344) && (i ≤ 1114111)) →
    wf_char (char.mk_char i)


inductive fun_utf8 : List char → List byte → Prop where
  | fun_utf8_case_0 (ch : char) (b : byte) : 
    ((proj_char_0 ch) < 128) && ((byte.mk_byte (proj_char_0 ch)) == b) →
    wf_byte (byte.mk_byte (proj_char_0 ch)) →
    fun_utf8 [ch] [b]
  | fun_utf8_case_1 (ch : char) (b_1 : byte) (b_2 : byte) : 
    ((128 ≤ (proj_char_0 ch)) && ((proj_char_0 ch) < 2048)) && ((proj_char_0 ch) == (((2 ^ 6) * (Int.toNat (((proj_byte_0 b_1) : Int) - (192 : Int)))) + (Int.toNat (((proj_byte_0 b_2) : Int) - (128 : Int))))) →
    fun_utf8 [ch] [b_1, b_2]
  | fun_utf8_case_2 (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) : 
    (((2048 ≤ (proj_char_0 ch)) && ((proj_char_0 ch) < 55296)) || ((57344 ≤ (proj_char_0 ch)) && ((proj_char_0 ch) < 65536))) && ((proj_char_0 ch) == ((((2 ^ 12) * (Int.toNat (((proj_byte_0 b_1) : Int) - (224 : Int)))) + ((2 ^ 6) * (Int.toNat (((proj_byte_0 b_2) : Int) - (128 : Int))))) + (Int.toNat (((proj_byte_0 b_3) : Int) - (128 : Int))))) →
    fun_utf8 [ch] [b_1, b_2, b_3]
  | fun_utf8_case_3 (ch : char) (b_1 : byte) (b_2 : byte) (b_3 : byte) (b_4 : byte) : 
    ((65536 ≤ (proj_char_0 ch)) && ((proj_char_0 ch) < 69632)) && ((proj_char_0 ch) == (((((2 ^ 18) * (Int.toNat (((proj_byte_0 b_1) : Int) - (240 : Int)))) + ((2 ^ 12) * (Int.toNat (((proj_byte_0 b_2) : Int) - (128 : Int))))) + ((2 ^ 6) * (Int.toNat (((proj_byte_0 b_3) : Int) - (128 : Int))))) + (Int.toNat (((proj_byte_0 b_4) : Int) - (128 : Int))))) →
    fun_utf8 [ch] [b_1, b_2, b_3, b_4]
  | fun_utf8_case_4 (ch_lst : List char) (var_0_lst : List (List byte)) : 
    (List.length var_0_lst) == (List.length ch_lst) →
    (∀ __iter_tuple ∈ var_0_lst |>.zip ch_lst, fun_utf8 [__iter_tuple.2] (__iter_tuple.1)) →
    fun_utf8 ch_lst (concat_ byte var_0_lst)


inductive utf8_is_wf : List char → List byte → Prop where
  | utf8_is_wf_0 (var_0_lst : List char) (ret_val_lst : List byte) (var_0 : List byte) : 
    fun_utf8 var_0_lst var_0 →
    (∀ var_0_elem ∈ var_0_lst, wf_char var_0_elem) →
    ret_val_lst == var_0 →
    (∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem) →
    utf8_is_wf var_0_lst ret_val_lst


inductive name : Type where
  | mk_name (char_lst : List char) : name
deriving Inhabited, BEq

def proj_name_0 (x : name) : List char :=
  match x with
  | name.mk_name v_char_list_0 => (v_char_list_0)

inductive wf_name : name → Prop where
  | name_case_0 (char_lst : List char) (var_0 : List byte) : 
    fun_utf8 char_lst var_0 →
    (∀ v_char_elem ∈ char_lst, wf_char v_char_elem) →
    (List.length var_0) < (2 ^ 32) →
    wf_name (name.mk_name char_lst)


abbrev idx : Type := u32

abbrev typeidx : Type := idx

abbrev funcidx : Type := idx

abbrev globalidx : Type := idx

abbrev tableidx : Type := idx

abbrev memidx : Type := idx

abbrev labelidx : Type := idx

abbrev localidx : Type := idx

inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
deriving Inhabited, BEq

inductive Inn : Type where
  | I32 : Inn
  | I64 : Inn
deriving Inhabited, BEq

def valtype_Inn (var_0 : Inn) : valtype :=
  match var_0 with
  | Inn.I32 => valtype.I32
  | Inn.I64 => valtype.I64

inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq

def valtype_Fnn (var_0 : Fnn) : valtype :=
  match var_0 with
  | Fnn.F32 => valtype.F32
  | Fnn.F64 => valtype.F64

abbrev resulttype : Type := Option valtype

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
  | mk_functype (valtype_lst_0 : List valtype) (valtype_lst_1 : List valtype) : functype
deriving Inhabited, BEq

abbrev tabletype : Type := limits

abbrev memtype : Type := limits

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
    wf_limits v_tabletype →
    wf_externtype (externtype.TABLE v_tabletype)
  | externtype_case_3 (v_memtype : memtype) : 
    wf_limits v_memtype →
    wf_externtype (externtype.MEM v_memtype)


def size (v_valtype : valtype) : Nat :=
  match v_valtype with
  | valtype.I32 => 32
  | valtype.I64 => 64
  | valtype.F32 => 32
  | valtype.F64 => 64

inductive val_ : Type where
  | mk_val__0 (v_Inn : Inn) (var_x : iN) : val_
  | mk_val__1 (v_Fnn : Fnn) (var_x : fN) : val_
deriving Inhabited, BEq

inductive wf_val_ : valtype → val_ → Prop where
  | val__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : iN) : 
    wf_uN (size (valtype_Inn v_Inn)) var_x →
    v_valtype == (valtype_Inn v_Inn) →
    wf_val_ v_valtype (val_.mk_val__0 v_Inn var_x)
  | val__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : fN) : 
    wf_fN (size (valtype_Fnn v_Fnn)) var_x →
    v_valtype == (valtype_Fnn v_Fnn) →
    wf_val_ v_valtype (val_.mk_val__1 v_Fnn var_x)


def proj_val__0 (var_x : val_) : Option iN :=
  match var_x with
  | val_.mk_val__0 v_Inn var_x => some var_x
  | _ => none

def proj_val__1 (var_x : val_) : Option fN :=
  match var_x with
  | val_.mk_val__1 v_Fnn var_x => some var_x
  | _ => none

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

inductive wf_unop_ : valtype → unop_ → Prop where
  | unop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : unop_Inn) : 
    v_valtype == (valtype_Inn v_Inn) →
    wf_unop_ v_valtype (unop_.mk_unop__0 v_Inn var_x)
  | unop__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : unop_Fnn) : 
    v_valtype == (valtype_Fnn v_Fnn) →
    wf_unop_ v_valtype (unop_.mk_unop__1 v_Fnn var_x)


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

inductive wf_binop_ : valtype → binop_ → Prop where
  | binop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : binop_Inn) : 
    v_valtype == (valtype_Inn v_Inn) →
    wf_binop_ v_valtype (binop_.mk_binop__0 v_Inn var_x)
  | binop__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : binop_Fnn) : 
    v_valtype == (valtype_Fnn v_Fnn) →
    wf_binop_ v_valtype (binop_.mk_binop__1 v_Fnn var_x)


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

inductive wf_testop_ : valtype → testop_ → Prop where
  | testop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : testop_Inn) : 
    v_valtype == (valtype_Inn v_Inn) →
    wf_testop_ v_valtype (testop_.mk_testop__0 v_Inn var_x)


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

inductive wf_relop_ : valtype → relop_ → Prop where
  | relop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : relop_Inn) : 
    v_valtype == (valtype_Inn v_Inn) →
    wf_relop_ v_valtype (relop_.mk_relop__0 v_Inn var_x)
  | relop__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : relop_Fnn) : 
    v_valtype == (valtype_Fnn v_Fnn) →
    wf_relop_ v_valtype (relop_.mk_relop__1 v_Fnn var_x)


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
  | PROMOTE : cvtop
  | DEMOTE : cvtop
  | REINTERPRET : cvtop
deriving Inhabited, BEq

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
    (proj_sz_0 v_sz) < (size (valtype_Inn v_Inn)) →
    wf_loadop_Inn v_Inn (loadop_Inn.mk_loadop_Inn v_sz v_sx)


inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq

inductive wf_loadop_ : valtype → loadop_ → Prop where
  | loadop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : loadop_Inn) : 
    wf_loadop_Inn v_Inn var_x →
    v_valtype == (valtype_Inn v_Inn) →
    wf_loadop_ v_valtype (loadop_.mk_loadop__0 v_Inn var_x)


def proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
  match var_x with
  | loadop_.mk_loadop__0 v_Inn var_x => var_x

abbrev blocktype : Type := Option valtype

inductive instr : Type where
  | NOP : instr
  | UNREACHABLE : instr
  | DROP : instr
  | SELECT : instr
  | BLOCK (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | LOOP (v_blocktype : blocktype) (instr_lst : List instr) : instr
  | IFELSE (v_blocktype : blocktype) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : instr
  | BR (v_labelidx : labelidx) : instr
  | BR_IF (v_labelidx : labelidx) : instr
  | BR_TABLE (labelidx_lst : List labelidx) (v_labelidx : labelidx) : instr
  | CALL (v_funcidx : funcidx) : instr
  | CALL_INDIRECT (v_typeidx : typeidx) : instr
  | RETURN : instr
  | CONST (v_valtype : valtype) (_ : val_) : instr
  | UNOP (v_valtype : valtype) (_ : unop_) : instr
  | BINOP (v_valtype : valtype) (_ : binop_) : instr
  | TESTOP (v_valtype : valtype) (_ : testop_) : instr
  | RELOP (v_valtype : valtype) (_ : relop_) : instr
  | CVTOP (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | LOCAL_TEE (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
  | LOAD (v_valtype : valtype) (_ : Option loadop_) (v_memarg : memarg) : instr
  | STORE (v_valtype : valtype) (sz_opt : Option sz) (v_memarg : memarg) : instr
  | MEMORY_SIZE : instr
  | MEMORY_GROW : instr
deriving Inhabited, BEq

inductive wf_instr : instr → Prop where
  | instr_case_0 : wf_instr instr.NOP
  | instr_case_1 : wf_instr instr.UNREACHABLE
  | instr_case_2 : wf_instr instr.DROP
  | instr_case_3 : wf_instr instr.SELECT
  | instr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    wf_instr (instr.BLOCK v_blocktype instr_lst)
  | instr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    wf_instr (instr.LOOP v_blocktype instr_lst)
  | instr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    (∀ instr_lst_0_elem ∈ instr_lst_0_lst, wf_instr instr_lst_0_elem) →
    wf_instr (instr.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | instr_case_7 (v_labelidx : labelidx) : 
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR v_labelidx)
  | instr_case_8 (v_labelidx : labelidx) : 
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_IF v_labelidx)
  | instr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) : 
    (∀ v_labelidx_elem ∈ labelidx_lst, wf_uN 32 v_labelidx_elem) →
    wf_uN 32 v_labelidx →
    wf_instr (instr.BR_TABLE labelidx_lst v_labelidx)
  | instr_case_10 (v_funcidx : funcidx) : 
    wf_uN 32 v_funcidx →
    wf_instr (instr.CALL v_funcidx)
  | instr_case_11 (v_typeidx : typeidx) : 
    wf_uN 32 v_typeidx →
    wf_instr (instr.CALL_INDIRECT v_typeidx)
  | instr_case_12 : wf_instr instr.RETURN
  | instr_case_13 (v_valtype : valtype) (var_0 : val_) : 
    wf_val_ v_valtype var_0 →
    wf_instr (instr.CONST v_valtype var_0)
  | instr_case_14 (v_valtype : valtype) (var_0 : unop_) : 
    wf_unop_ v_valtype var_0 →
    wf_instr (instr.UNOP v_valtype var_0)
  | instr_case_15 (v_valtype : valtype) (var_0 : binop_) : 
    wf_binop_ v_valtype var_0 →
    wf_instr (instr.BINOP v_valtype var_0)
  | instr_case_16 (v_valtype : valtype) (var_0 : testop_) : 
    wf_testop_ v_valtype var_0 →
    wf_instr (instr.TESTOP v_valtype var_0)
  | instr_case_17 (v_valtype : valtype) (var_0 : relop_) : 
    wf_relop_ v_valtype var_0 →
    wf_instr (instr.RELOP v_valtype var_0)
  | instr_case_18 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : 
    valtype_1 != valtype_2 →
    wf_instr (instr.CVTOP valtype_1 valtype_2 v_cvtop)
  | instr_case_19 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_GET v_localidx)
  | instr_case_20 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_SET v_localidx)
  | instr_case_21 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_instr (instr.LOCAL_TEE v_localidx)
  | instr_case_22 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_GET v_globalidx)
  | instr_case_23 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_instr (instr.GLOBAL_SET v_globalidx)
  | instr_case_24 (v_valtype : valtype) (var_0_opt : Option loadop_) (v_memarg : memarg) : 
    (∀ var_0_elem ∈ Option.toList var_0_opt, wf_loadop_ v_valtype var_0_elem) →
    wf_memarg v_memarg →
    wf_instr (instr.LOAD v_valtype var_0_opt v_memarg)
  | instr_case_25 (Inn_opt : Option Inn) (valtype_opt : Option valtype) (v_valtype : valtype) (sz_opt : Option sz) (v_memarg : memarg) : 
    (∀ v_sz_elem ∈ Option.toList sz_opt, wf_sz v_sz_elem) →
    wf_memarg v_memarg →
    ((Inn_opt == none) ↔ (sz_opt == none)) →
    ((Inn_opt == none) ↔ (valtype_opt == none)) →
    (∀ __iter_tuple ∈ Option.toList Inn_opt |>.zip (Option.toList sz_opt) |>.zip (Option.toList valtype_opt), ((__iter_tuple.2) == (valtype_Inn (__iter_tuple.1.1))) && ((proj_sz_0 (__iter_tuple.1.2)) < (size (valtype_Inn (__iter_tuple.1.1))))) →
    wf_instr (instr.STORE v_valtype sz_opt v_memarg)
  | instr_case_26 : wf_instr instr.MEMORY_SIZE
  | instr_case_27 : wf_instr instr.MEMORY_GROW


abbrev expr : Type := List instr

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
    (∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem) →
    wf_func (func.FUNC v_typeidx local_lst v_expr)


inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq

inductive wf_global : global → Prop where
  | global_case_0 (v_globaltype : globaltype) (v_expr : expr) : 
    (∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem) →
    wf_global (global.GLOBAL v_globaltype v_expr)


inductive table : Type where
  | TABLE (v_tabletype : tabletype) : table
deriving Inhabited, BEq

inductive wf_table : table → Prop where
  | table_case_0 (v_tabletype : tabletype) : 
    wf_limits v_tabletype →
    wf_table (table.TABLE v_tabletype)


inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq

inductive wf_mem : mem → Prop where
  | mem_case_0 (v_memtype : memtype) : 
    wf_limits v_memtype →
    wf_mem (mem.MEMORY v_memtype)


inductive elem : Type where
  | ELEM (v_expr : expr) (funcidx_lst : List funcidx) : elem
deriving Inhabited, BEq

inductive wf_elem : elem → Prop where
  | elem_case_0 (v_expr : expr) (funcidx_lst : List funcidx) : 
    (∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem) →
    (∀ v_funcidx_elem ∈ funcidx_lst, wf_uN 32 v_funcidx_elem) →
    wf_elem (elem.ELEM v_expr funcidx_lst)


inductive data : Type where
  | DATA (v_expr : expr) (byte_lst : List byte) : data
deriving Inhabited, BEq

inductive wf_data : data → Prop where
  | data_case_0 (v_expr : expr) (byte_lst : List byte) : 
    (∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem) →
    (∀ v_byte_elem ∈ byte_lst, wf_byte v_byte_elem) →
    wf_data (data.DATA v_expr byte_lst)


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
    (∀ v_import_elem ∈ import_lst, wf_import v_import_elem) →
    (∀ v_func_elem ∈ func_lst, wf_func v_func_elem) →
    (∀ v_global_elem ∈ global_lst, wf_global v_global_elem) →
    (∀ v_table_elem ∈ table_lst, wf_table v_table_elem) →
    (∀ v_mem_elem ∈ mem_lst, wf_mem v_mem_elem) →
    (∀ v_elem_elem ∈ elem_lst, wf_elem v_elem_elem) →
    (∀ v_data_elem ∈ data_lst, wf_data v_data_elem) →
    (∀ v_start_elem ∈ Option.toList start_opt, wf_start v_start_elem) →
    (∀ v_export_elem ∈ export_lst, wf_export v_export_elem) →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)


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
  | fun_tablesxt_case_1 (tt : limits) (xt_lst : List externtype) (var_0 : List tabletype) : 
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([externtype.TABLE tt] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List tabletype) : 
    fun_tablesxt xt_lst var_0 →
    fun_tablesxt ([v_externtype] ++ xt_lst) var_0


inductive tablesxt_is_wf : List externtype → List tabletype → Prop where
  | tablesxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List tabletype) (var_0 : List tabletype) : 
    fun_tablesxt var_0_lst var_0 →
    (∀ var_0_elem ∈ var_0_lst, wf_externtype var_0_elem) →
    ret_val_lst == var_0 →
    (∀ ret_val_elem ∈ ret_val_lst, wf_limits ret_val_elem) →
    tablesxt_is_wf var_0_lst ret_val_lst


inductive fun_memsxt : List externtype → List memtype → Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 (mt : limits) (xt_lst : List externtype) (var_0 : List memtype) : 
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([externtype.MEM mt] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List memtype) : 
    fun_memsxt xt_lst var_0 →
    fun_memsxt ([v_externtype] ++ xt_lst) var_0


inductive memsxt_is_wf : List externtype → List memtype → Prop where
  | memsxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List memtype) (var_0 : List memtype) : 
    fun_memsxt var_0_lst var_0 →
    (∀ var_0_elem ∈ var_0_lst, wf_externtype var_0_elem) →
    ret_val_lst == var_0 →
    (∀ ret_val_elem ∈ ret_val_lst, wf_limits ret_val_elem) →
    memsxt_is_wf var_0_lst ret_val_lst


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


opaque fabs_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fabs__is_wf : N → fN → List fN → Prop where
  | fabs__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fabs_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    fabs__is_wf v_N v_fN ret_val_lst


opaque fceil_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fceil__is_wf : N → fN → List fN → Prop where
  | fceil__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fceil_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    fceil__is_wf v_N v_fN ret_val_lst


opaque ffloor_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ffloor__is_wf : N → fN → List fN → Prop where
  | ffloor__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (ffloor_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    ffloor__is_wf v_N v_fN ret_val_lst


opaque fnearest_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fnearest__is_wf : N → fN → List fN → Prop where
  | fnearest__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fnearest_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    fnearest__is_wf v_N v_fN ret_val_lst


opaque fneg_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fneg__is_wf : N → fN → List fN → Prop where
  | fneg__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fneg_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    fneg__is_wf v_N v_fN ret_val_lst


opaque fsqrt_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsqrt__is_wf : N → fN → List fN → Prop where
  | fsqrt__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fsqrt_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    fsqrt__is_wf v_N v_fN ret_val_lst


opaque ftrunc_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ftrunc__is_wf : N → fN → List fN → Prop where
  | ftrunc__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    ret_val_lst == (ftrunc_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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


def fun_unop_ (v_valtype : valtype) (v_unop_ : unop_) (v_val_ : val_) : Option (List val_) :=
  match v_valtype, v_unop_, v_val_ with
  | valtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.CLZ, val_.mk_val__0 Inn.I32 v_iN => some [val_.mk_val__0 Inn.I32 (iclz_ (size (valtype_Inn Inn.I32)) v_iN)]
  | valtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.CLZ, val_.mk_val__0 Inn.I64 v_iN => some [val_.mk_val__0 Inn.I64 (iclz_ (size (valtype_Inn Inn.I64)) v_iN)]
  | valtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.CTZ, val_.mk_val__0 Inn.I32 v_iN => some [val_.mk_val__0 Inn.I32 (ictz_ (size (valtype_Inn Inn.I32)) v_iN)]
  | valtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.CTZ, val_.mk_val__0 Inn.I64 v_iN => some [val_.mk_val__0 Inn.I64 (ictz_ (size (valtype_Inn Inn.I64)) v_iN)]
  | valtype.I32, unop_.mk_unop__0 Inn.I32 unop_Inn.POPCNT, val_.mk_val__0 Inn.I32 v_iN => some [val_.mk_val__0 Inn.I32 (ipopcnt_ (size (valtype_Inn Inn.I32)) v_iN)]
  | valtype.I64, unop_.mk_unop__0 Inn.I64 unop_Inn.POPCNT, val_.mk_val__0 Inn.I64 v_iN => some [val_.mk_val__0 Inn.I64 (ipopcnt_ (size (valtype_Inn Inn.I64)) v_iN)]
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.ABS, val_.mk_val__1 Fnn.F32 v_fN => some (fabs_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_1_elem => val_.mk_val__1 Fnn.F32 iter_0_1_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.ABS, val_.mk_val__1 Fnn.F64 v_fN => some (fabs_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_2_elem => val_.mk_val__1 Fnn.F64 iter_0_2_elem))
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEG, val_.mk_val__1 Fnn.F32 v_fN => some (fneg_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_3_elem => val_.mk_val__1 Fnn.F32 iter_0_3_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEG, val_.mk_val__1 Fnn.F64 v_fN => some (fneg_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_4_elem => val_.mk_val__1 Fnn.F64 iter_0_4_elem))
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.SQRT, val_.mk_val__1 Fnn.F32 v_fN => some (fsqrt_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_5_elem => val_.mk_val__1 Fnn.F32 iter_0_5_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.SQRT, val_.mk_val__1 Fnn.F64 v_fN => some (fsqrt_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_6_elem => val_.mk_val__1 Fnn.F64 iter_0_6_elem))
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.CEIL, val_.mk_val__1 Fnn.F32 v_fN => some (fceil_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_7_elem => val_.mk_val__1 Fnn.F32 iter_0_7_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.CEIL, val_.mk_val__1 Fnn.F64 v_fN => some (fceil_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_8_elem => val_.mk_val__1 Fnn.F64 iter_0_8_elem))
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.FLOOR, val_.mk_val__1 Fnn.F32 v_fN => some (ffloor_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_9_elem => val_.mk_val__1 Fnn.F32 iter_0_9_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.FLOOR, val_.mk_val__1 Fnn.F64 v_fN => some (ffloor_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_10_elem => val_.mk_val__1 Fnn.F64 iter_0_10_elem))
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.TRUNC, val_.mk_val__1 Fnn.F32 v_fN => some (ftrunc_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_11_elem => val_.mk_val__1 Fnn.F32 iter_0_11_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.TRUNC, val_.mk_val__1 Fnn.F64 v_fN => some (ftrunc_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_12_elem => val_.mk_val__1 Fnn.F64 iter_0_12_elem))
  | valtype.F32, unop_.mk_unop__1 Fnn.F32 unop_Fnn.NEAREST, val_.mk_val__1 Fnn.F32 v_fN => some (fnearest_ (size (valtype_Fnn Fnn.F32)) v_fN |>.map (fun iter_0_13_elem => val_.mk_val__1 Fnn.F32 iter_0_13_elem))
  | valtype.F64, unop_.mk_unop__1 Fnn.F64 unop_Fnn.NEAREST, val_.mk_val__1 Fnn.F64 v_fN => some (fnearest_ (size (valtype_Fnn Fnn.F64)) v_fN |>.map (fun iter_0_14_elem => val_.mk_val__1 Fnn.F64 iter_0_14_elem))
  | _, _, _ => none

inductive unop__is_wf : valtype → unop_ → val_ → List val_ → Prop where
  | unop__is_wf_0 (v_valtype : valtype) (v_unop_ : unop_) (v_val_ : val_) (ret_val_lst : List val_) : 
    wf_unop_ v_valtype v_unop_ →
    wf_val_ v_valtype v_val_ →
    (fun_unop_ v_valtype v_unop_ v_val_) != none →
    ret_val_lst == (Option.get! (fun_unop_ v_valtype v_unop_ v_val_)) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_val_ v_valtype ret_val_elem) →
    unop__is_wf v_valtype v_unop_ v_val_ ret_val_lst


opaque fadd_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fadd__is_wf : N → fN → fN → List fN → Prop where
  | fadd__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : 
    wf_fN v_N v_fN →
    wf_fN v_N fN_0 →
    ret_val_lst == (fadd_ v_N v_fN fN_0) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ Option.toList ret_val_opt, wf_uN v_N ret_val_elem) →
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
    (∀ ret_val_elem ∈ Option.toList ret_val_opt, wf_uN v_N ret_val_elem) →
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


inductive fun_binop_ : valtype → binop_ → val_ → val_ → List val_ → Prop where
  | fun_binop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ADD) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (iadd_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ADD) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (iadd_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.SUB) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (isub_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.SUB) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (isub_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_4 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.MUL) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (imul_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_5 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.MUL) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (imul_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_idiv_ (size (valtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.DIV v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_15_elem => val_.mk_val__0 Inn.I32 iter_0_15_elem)))
  | fun_binop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_idiv_ (size (valtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.DIV v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_16_elem => val_.mk_val__0 Inn.I64 iter_0_16_elem)))
  | fun_binop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_irem_ (size (valtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.REM v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_17_elem => val_.mk_val__0 Inn.I32 iter_0_17_elem)))
  | fun_binop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : 
    fun_irem_ (size (valtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.REM v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_18_elem => val_.mk_val__0 Inn.I64 iter_0_18_elem)))
  | fun_binop__case_10 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.AND) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (iand_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_11 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.AND) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (iand_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_12 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.OR) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (ior_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_13 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.OR) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (ior_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_14 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.XOR) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (ixor_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_15 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.XOR) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (ixor_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_16 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.SHL) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (ishl_ (size (valtype_Inn Inn.I32)) iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_17 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.SHL) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (ishl_ (size (valtype_Inn Inn.I64)) iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_18 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 (binop_Inn.SHR v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (ishr_ (size (valtype_Inn Inn.I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_19 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 (binop_Inn.SHR v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (ishr_ (size (valtype_Inn Inn.I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_20 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ROTL) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (irotl_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_21 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ROTL) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (irotl_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_22 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I32 (binop_.mk_binop__0 Inn.I32 binop_Inn.ROTR) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) [val_.mk_val__0 Inn.I32 (irotr_ (size (valtype_Inn Inn.I32)) iN_1 iN_2)]
  | fun_binop__case_23 (iN_1 : uN) (iN_2 : uN) : fun_binop_ valtype.I64 (binop_.mk_binop__0 Inn.I64 binop_Inn.ROTR) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) [val_.mk_val__0 Inn.I64 (irotr_ (size (valtype_Inn Inn.I64)) iN_1 iN_2)]
  | fun_binop__case_24 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.ADD) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fadd_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_19_elem => val_.mk_val__1 Fnn.F32 iter_0_19_elem))
  | fun_binop__case_25 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.ADD) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fadd_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_20_elem => val_.mk_val__1 Fnn.F64 iter_0_20_elem))
  | fun_binop__case_26 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.SUB) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fsub_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_21_elem => val_.mk_val__1 Fnn.F32 iter_0_21_elem))
  | fun_binop__case_27 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.SUB) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fsub_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_22_elem => val_.mk_val__1 Fnn.F64 iter_0_22_elem))
  | fun_binop__case_28 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MUL) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fmul_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_23_elem => val_.mk_val__1 Fnn.F32 iter_0_23_elem))
  | fun_binop__case_29 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MUL) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fmul_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_24_elem => val_.mk_val__1 Fnn.F64 iter_0_24_elem))
  | fun_binop__case_30 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.DIV) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fdiv_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_25_elem => val_.mk_val__1 Fnn.F32 iter_0_25_elem))
  | fun_binop__case_31 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.DIV) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fdiv_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_26_elem => val_.mk_val__1 Fnn.F64 iter_0_26_elem))
  | fun_binop__case_32 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MIN) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fmin_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_27_elem => val_.mk_val__1 Fnn.F32 iter_0_27_elem))
  | fun_binop__case_33 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MIN) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fmin_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_28_elem => val_.mk_val__1 Fnn.F64 iter_0_28_elem))
  | fun_binop__case_34 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.MAX) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fmax_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_29_elem => val_.mk_val__1 Fnn.F32 iter_0_29_elem))
  | fun_binop__case_35 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.MAX) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fmax_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_30_elem => val_.mk_val__1 Fnn.F64 iter_0_30_elem))
  | fun_binop__case_36 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F32 (binop_.mk_binop__1 Fnn.F32 binop_Fnn.COPYSIGN) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (fcopysign_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2 |>.map (fun iter_0_31_elem => val_.mk_val__1 Fnn.F32 iter_0_31_elem))
  | fun_binop__case_37 (fN_1 : fN) (fN_2 : fN) : fun_binop_ valtype.F64 (binop_.mk_binop__1 Fnn.F64 binop_Fnn.COPYSIGN) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (fcopysign_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2 |>.map (fun iter_0_32_elem => val_.mk_val__1 Fnn.F64 iter_0_32_elem))


inductive binop__is_wf : valtype → binop_ → val_ → val_ → List val_ → Prop where
  | binop__is_wf_0 (v_valtype : valtype) (v_binop_ : binop_) (v_val_ : val_) (val__0 : val_) (ret_val_lst : List val_) (var_0 : List val_) : 
    fun_binop_ v_valtype v_binop_ v_val_ val__0 var_0 →
    wf_binop_ v_valtype v_binop_ →
    wf_val_ v_valtype v_val_ →
    wf_val_ v_valtype val__0 →
    ret_val_lst == var_0 →
    (∀ ret_val_elem ∈ ret_val_lst, wf_val_ v_valtype ret_val_elem) →
    binop__is_wf v_valtype v_binop_ v_val_ val__0 ret_val_lst


def ieqz_ (v_N : N) (v_iN : iN) : u32 :=
  .mk_uN (nat_of_bool ((proj_uN_0 v_iN) == 0))

inductive ieqz__is_wf : N → iN → u32 → Prop where
  | ieqz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) : 
    wf_uN v_N v_iN →
    ret_val == (ieqz_ v_N v_iN) →
    wf_uN 32 ret_val →
    ieqz__is_wf v_N v_iN ret_val


def fun_testop_ (v_valtype : valtype) (v_testop_ : testop_) (v_val_ : val_) : Option val_ :=
  match v_valtype, v_testop_, v_val_ with
  | valtype.I32, testop_.mk_testop__0 Inn.I32 testop_Inn.EQZ, val_.mk_val__0 Inn.I32 v_iN => some (val_.mk_val__0 Inn.I32 (ieqz_ (size (valtype_Inn Inn.I32)) v_iN))
  | valtype.I64, testop_.mk_testop__0 Inn.I64 testop_Inn.EQZ, val_.mk_val__0 Inn.I64 v_iN => some (val_.mk_val__0 Inn.I32 (ieqz_ (size (valtype_Inn Inn.I64)) v_iN))
  | _, _, _ => none

inductive testop__is_wf : valtype → testop_ → val_ → val_ → Prop where
  | testop__is_wf_0 (v_valtype : valtype) (v_testop_ : testop_) (v_val_ : val_) (ret_val : val_) : 
    wf_testop_ v_valtype v_testop_ →
    wf_val_ v_valtype v_val_ →
    (fun_testop_ v_valtype v_testop_ v_val_) != none →
    ret_val == (Option.get! (fun_testop_ v_valtype v_testop_ v_val_)) →
    wf_val_ valtype.I32 ret_val →
    testop__is_wf v_valtype v_testop_ v_val_ ret_val


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


inductive fun_relop_ : valtype → relop_ → val_ → val_ → val_ → Prop where
  | fun_relop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_relop_ valtype.I32 (relop_.mk_relop__0 Inn.I32 relop_Inn.EQ) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (val_.mk_val__0 Inn.I32 (ieq_ (size (valtype_Inn Inn.I32)) iN_1 iN_2))
  | fun_relop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_relop_ valtype.I64 (relop_.mk_relop__0 Inn.I64 relop_Inn.EQ) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (val_.mk_val__0 Inn.I32 (ieq_ (size (valtype_Inn Inn.I64)) iN_1 iN_2))
  | fun_relop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_relop_ valtype.I32 (relop_.mk_relop__0 Inn.I32 relop_Inn.NE) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (val_.mk_val__0 Inn.I32 (ine_ (size (valtype_Inn Inn.I32)) iN_1 iN_2))
  | fun_relop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_relop_ valtype.I64 (relop_.mk_relop__0 Inn.I64 relop_Inn.NE) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (val_.mk_val__0 Inn.I32 (ine_ (size (valtype_Inn Inn.I64)) iN_1 iN_2))
  | fun_relop__case_4 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ilt_ (size (valtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.LT v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_5 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ilt_ (size (valtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.LT v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_igt_ (size (valtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.GT v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_igt_ (size (valtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.GT v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ile_ (size (valtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.LE v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ile_ (size (valtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.LE v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_10 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ige_ (size (valtype_Inn Inn.I32)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I32 (relop_.mk_relop__0 Inn.I32 (relop_Inn.GE v_sx)) (val_.mk_val__0 Inn.I32 iN_1) (val_.mk_val__0 Inn.I32 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_11 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : 
    fun_ige_ (size (valtype_Inn Inn.I64)) v_sx iN_1 iN_2 var_0 →
    fun_relop_ valtype.I64 (relop_.mk_relop__0 Inn.I64 (relop_Inn.GE v_sx)) (val_.mk_val__0 Inn.I64 iN_1) (val_.mk_val__0 Inn.I64 iN_2) (val_.mk_val__0 Inn.I32 var_0)
  | fun_relop__case_12 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.EQ) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (val_.mk_val__0 Inn.I32 (feq_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_13 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.EQ) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (val_.mk_val__0 Inn.I32 (feq_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_14 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.NE) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (val_.mk_val__0 Inn.I32 (fne_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_15 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.NE) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (val_.mk_val__0 Inn.I32 (fne_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_16 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.LT) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (val_.mk_val__0 Inn.I32 (flt_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_17 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.LT) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (val_.mk_val__0 Inn.I32 (flt_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_18 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.GT) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (val_.mk_val__0 Inn.I32 (fgt_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_19 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.GT) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (val_.mk_val__0 Inn.I32 (fgt_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_20 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.LE) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (val_.mk_val__0 Inn.I32 (fle_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_21 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.LE) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (val_.mk_val__0 Inn.I32 (fle_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2))
  | fun_relop__case_22 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F32 (relop_.mk_relop__1 Fnn.F32 relop_Fnn.GE) (val_.mk_val__1 Fnn.F32 fN_1) (val_.mk_val__1 Fnn.F32 fN_2) (val_.mk_val__0 Inn.I32 (fge_ (size (valtype_Fnn Fnn.F32)) fN_1 fN_2))
  | fun_relop__case_23 (fN_1 : fN) (fN_2 : fN) : fun_relop_ valtype.F64 (relop_.mk_relop__1 Fnn.F64 relop_Fnn.GE) (val_.mk_val__1 Fnn.F64 fN_1) (val_.mk_val__1 Fnn.F64 fN_2) (val_.mk_val__0 Inn.I32 (fge_ (size (valtype_Fnn Fnn.F64)) fN_1 fN_2))


inductive relop__is_wf : valtype → relop_ → val_ → val_ → val_ → Prop where
  | relop__is_wf_0 (v_valtype : valtype) (v_relop_ : relop_) (v_val_ : val_) (val__0 : val_) (ret_val : val_) (var_0 : val_) : 
    fun_relop_ v_valtype v_relop_ v_val_ val__0 var_0 →
    wf_relop_ v_valtype v_relop_ →
    wf_val_ v_valtype v_val_ →
    wf_val_ v_valtype val__0 →
    ret_val == var_0 →
    wf_val_ valtype.I32 ret_val →
    relop__is_wf v_valtype v_relop_ v_val_ val__0 ret_val


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
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    demote___is_wf v_M v_N v_fN ret_val_lst


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


opaque promote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive promote___is_wf : M → N → fN → List fN → Prop where
  | promote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : 
    wf_fN v_M v_fN →
    ret_val_lst == (promote__ v_M v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem) →
    promote___is_wf v_M v_N v_fN ret_val_lst


opaque reinterpret__ (valtype_1 : valtype) (valtype_2 : valtype) (v_val_ : val_) : val_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive reinterpret___is_wf : valtype → valtype → val_ → val_ → Prop where
  | reinterpret___is_wf_0 (valtype_1 : valtype) (valtype_2 : valtype) (v_val_ : val_) (ret_val : val_) : 
    wf_val_ valtype_1 v_val_ →
    ret_val == (reinterpret__ valtype_1 valtype_2 v_val_) →
    wf_val_ valtype_2 ret_val →
    reinterpret___is_wf valtype_1 valtype_2 v_val_ ret_val


opaque trunc__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive trunc___is_wf : M → N → sx → fN → Option iN → Prop where
  | trunc___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) : 
    wf_fN v_M v_fN →
    ret_val_opt == (trunc__ v_M v_N v_sx v_fN) →
    (∀ ret_val_elem ∈ Option.toList ret_val_opt, wf_uN v_N ret_val_elem) →
    trunc___is_wf v_M v_N v_sx v_fN ret_val_opt


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


inductive fun_cvtop__ : valtype → valtype → cvtop → val_ → List val_ → Prop where
  | fun_cvtop___case_0 (v_sx : sx) (v_iN : uN) : fun_cvtop__ valtype.I32 valtype.I64 (cvtop.EXTEND v_sx) (val_.mk_val__0 Inn.I32 v_iN) [val_.mk_val__0 Inn.I64 (extend__ 32 64 v_sx v_iN)]
  | fun_cvtop___case_1 (v_iN : uN) : fun_cvtop__ valtype.I64 valtype.I32 cvtop.WRAP (val_.mk_val__0 Inn.I64 v_iN) [val_.mk_val__0 Inn.I32 (wrap__ 64 32 v_iN)]
  | fun_cvtop___case_2 (v_sx : sx) (v_fN : fN) : fun_cvtop__ valtype.F32 valtype.I32 (cvtop.TRUNC v_sx) (val_.mk_val__1 Fnn.F32 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn Fnn.F32)) (size (valtype_Inn Inn.I32)) v_sx v_fN |>.map (fun iter_0_33_elem => val_.mk_val__0 Inn.I32 iter_0_33_elem)))
  | fun_cvtop___case_3 (v_sx : sx) (v_fN : fN) : fun_cvtop__ valtype.F64 valtype.I32 (cvtop.TRUNC v_sx) (val_.mk_val__1 Fnn.F64 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn Fnn.F64)) (size (valtype_Inn Inn.I32)) v_sx v_fN |>.map (fun iter_0_34_elem => val_.mk_val__0 Inn.I32 iter_0_34_elem)))
  | fun_cvtop___case_4 (v_sx : sx) (v_fN : fN) : fun_cvtop__ valtype.F32 valtype.I64 (cvtop.TRUNC v_sx) (val_.mk_val__1 Fnn.F32 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn Fnn.F32)) (size (valtype_Inn Inn.I64)) v_sx v_fN |>.map (fun iter_0_35_elem => val_.mk_val__0 Inn.I64 iter_0_35_elem)))
  | fun_cvtop___case_5 (v_sx : sx) (v_fN : fN) : fun_cvtop__ valtype.F64 valtype.I64 (cvtop.TRUNC v_sx) (val_.mk_val__1 Fnn.F64 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn Fnn.F64)) (size (valtype_Inn Inn.I64)) v_sx v_fN |>.map (fun iter_0_36_elem => val_.mk_val__0 Inn.I64 iter_0_36_elem)))
  | fun_cvtop___case_6 (v_fN : fN) : fun_cvtop__ valtype.F32 valtype.F64 cvtop.PROMOTE (val_.mk_val__1 Fnn.F32 v_fN) (promote__ 32 64 v_fN |>.map (fun iter_0_elem => val_.mk_val__1 Fnn.F64 iter_0_elem))
  | fun_cvtop___case_7 (v_fN : fN) : fun_cvtop__ valtype.F64 valtype.F32 cvtop.DEMOTE (val_.mk_val__1 Fnn.F64 v_fN) (demote__ 64 32 v_fN |>.map (fun iter_0_elem => val_.mk_val__1 Fnn.F32 iter_0_elem))
  | fun_cvtop___case_8 (v_sx : sx) (v_iN : uN) : fun_cvtop__ valtype.I32 valtype.F32 (cvtop.CONVERT v_sx) (val_.mk_val__0 Inn.I32 v_iN) [val_.mk_val__1 Fnn.F32 (convert__ (size (valtype_Inn Inn.I32)) (size (valtype_Fnn Fnn.F32)) v_sx v_iN)]
  | fun_cvtop___case_9 (v_sx : sx) (v_iN : uN) : fun_cvtop__ valtype.I64 valtype.F32 (cvtop.CONVERT v_sx) (val_.mk_val__0 Inn.I64 v_iN) [val_.mk_val__1 Fnn.F32 (convert__ (size (valtype_Inn Inn.I64)) (size (valtype_Fnn Fnn.F32)) v_sx v_iN)]
  | fun_cvtop___case_10 (v_sx : sx) (v_iN : uN) : fun_cvtop__ valtype.I32 valtype.F64 (cvtop.CONVERT v_sx) (val_.mk_val__0 Inn.I32 v_iN) [val_.mk_val__1 Fnn.F64 (convert__ (size (valtype_Inn Inn.I32)) (size (valtype_Fnn Fnn.F64)) v_sx v_iN)]
  | fun_cvtop___case_11 (v_sx : sx) (v_iN : uN) : fun_cvtop__ valtype.I64 valtype.F64 (cvtop.CONVERT v_sx) (val_.mk_val__0 Inn.I64 v_iN) [val_.mk_val__1 Fnn.F64 (convert__ (size (valtype_Inn Inn.I64)) (size (valtype_Fnn Fnn.F64)) v_sx v_iN)]
  | fun_cvtop___case_12 (v_iN : uN) : 
    (size (valtype_Inn Inn.I32)) == (size (valtype_Fnn Fnn.F32)) →
    fun_cvtop__ valtype.I32 valtype.F32 cvtop.REINTERPRET (val_.mk_val__0 Inn.I32 v_iN) [reinterpret__ (valtype_Inn Inn.I32) (valtype_Fnn Fnn.F32) (val_.mk_val__0 Inn.I32 v_iN)]
  | fun_cvtop___case_13 (v_iN : uN) : 
    (size (valtype_Inn Inn.I64)) == (size (valtype_Fnn Fnn.F32)) →
    fun_cvtop__ valtype.I64 valtype.F32 cvtop.REINTERPRET (val_.mk_val__0 Inn.I64 v_iN) [reinterpret__ (valtype_Inn Inn.I64) (valtype_Fnn Fnn.F32) (val_.mk_val__0 Inn.I64 v_iN)]
  | fun_cvtop___case_14 (v_iN : uN) : 
    (size (valtype_Inn Inn.I32)) == (size (valtype_Fnn Fnn.F64)) →
    fun_cvtop__ valtype.I32 valtype.F64 cvtop.REINTERPRET (val_.mk_val__0 Inn.I32 v_iN) [reinterpret__ (valtype_Inn Inn.I32) (valtype_Fnn Fnn.F64) (val_.mk_val__0 Inn.I32 v_iN)]
  | fun_cvtop___case_15 (v_iN : uN) : 
    (size (valtype_Inn Inn.I64)) == (size (valtype_Fnn Fnn.F64)) →
    fun_cvtop__ valtype.I64 valtype.F64 cvtop.REINTERPRET (val_.mk_val__0 Inn.I64 v_iN) [reinterpret__ (valtype_Inn Inn.I64) (valtype_Fnn Fnn.F64) (val_.mk_val__0 Inn.I64 v_iN)]
  | fun_cvtop___case_16 (v_fN : fN) : 
    (size (valtype_Inn Inn.I32)) == (size (valtype_Fnn Fnn.F32)) →
    fun_cvtop__ valtype.F32 valtype.I32 cvtop.REINTERPRET (val_.mk_val__1 Fnn.F32 v_fN) [reinterpret__ (valtype_Fnn Fnn.F32) (valtype_Inn Inn.I32) (val_.mk_val__1 Fnn.F32 v_fN)]
  | fun_cvtop___case_17 (v_fN : fN) : 
    (size (valtype_Inn Inn.I32)) == (size (valtype_Fnn Fnn.F64)) →
    fun_cvtop__ valtype.F64 valtype.I32 cvtop.REINTERPRET (val_.mk_val__1 Fnn.F64 v_fN) [reinterpret__ (valtype_Fnn Fnn.F64) (valtype_Inn Inn.I32) (val_.mk_val__1 Fnn.F64 v_fN)]
  | fun_cvtop___case_18 (v_fN : fN) : 
    (size (valtype_Inn Inn.I64)) == (size (valtype_Fnn Fnn.F32)) →
    fun_cvtop__ valtype.F32 valtype.I64 cvtop.REINTERPRET (val_.mk_val__1 Fnn.F32 v_fN) [reinterpret__ (valtype_Fnn Fnn.F32) (valtype_Inn Inn.I64) (val_.mk_val__1 Fnn.F32 v_fN)]
  | fun_cvtop___case_19 (v_fN : fN) : 
    (size (valtype_Inn Inn.I64)) == (size (valtype_Fnn Fnn.F64)) →
    fun_cvtop__ valtype.F64 valtype.I64 cvtop.REINTERPRET (val_.mk_val__1 Fnn.F64 v_fN) [reinterpret__ (valtype_Fnn Fnn.F64) (valtype_Inn Inn.I64) (val_.mk_val__1 Fnn.F64 v_fN)]


inductive cvtop___is_wf : valtype → valtype → cvtop → val_ → List val_ → Prop where
  | cvtop___is_wf_0 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) (v_val_ : val_) (ret_val_lst : List val_) (var_0 : List val_) : 
    fun_cvtop__ valtype_1 valtype_2 v_cvtop v_val_ var_0 →
    wf_val_ valtype_1 v_val_ →
    ret_val_lst == var_0 →
    (∀ ret_val_elem ∈ ret_val_lst, wf_val_ valtype_2 ret_val_elem) →
    cvtop___is_wf valtype_1 valtype_2 v_cvtop v_val_ ret_val_lst


opaque ibytes_ (v_N : N) (v_iN : iN) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibytes__is_wf : N → iN → List byte → Prop where
  | ibytes__is_wf_0 (v_N : N) (v_iN : iN) (ret_val_lst : List byte) : 
    wf_uN v_N v_iN →
    ret_val_lst == (ibytes_ v_N v_iN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem) →
    ibytes__is_wf v_N v_iN ret_val_lst


opaque fbytes_ (v_N : N) (v_fN : fN) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fbytes__is_wf : N → fN → List byte → Prop where
  | fbytes__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List byte) : 
    wf_fN v_N v_fN →
    ret_val_lst == (fbytes_ v_N v_fN) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem) →
    fbytes__is_wf v_N v_fN ret_val_lst


opaque bytes_ (v_valtype : valtype) (v_val_ : val_) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive bytes__is_wf : valtype → val_ → List byte → Prop where
  | bytes__is_wf_0 (v_valtype : valtype) (v_val_ : val_) (ret_val_lst : List byte) : 
    wf_val_ v_valtype v_val_ →
    ret_val_lst == (bytes_ v_valtype v_val_) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem) →
    bytes__is_wf v_valtype v_val_ ret_val_lst


opaque inv_ibytes_ (v_N : N) (var_0_lst : List byte) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_ibytes__is_wf : N → List byte → iN → Prop where
  | inv_ibytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : iN) : 
    (∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem) →
    ret_val == (inv_ibytes_ v_N var_0_lst) →
    wf_uN v_N ret_val →
    inv_ibytes__is_wf v_N var_0_lst ret_val


opaque inv_fbytes_ (v_N : N) (var_0_lst : List byte) : fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_fbytes__is_wf : N → List byte → fN → Prop where
  | inv_fbytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : fN) : 
    (∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem) →
    ret_val == (inv_fbytes_ v_N var_0_lst) →
    wf_fN v_N ret_val →
    inv_fbytes__is_wf v_N var_0_lst ret_val


opaque inv_bytes_ (v_valtype : valtype) (var_0_lst : List byte) : val_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_bytes__is_wf : valtype → List byte → val_ → Prop where
  | inv_bytes__is_wf_0 (v_valtype : valtype) (var_0_lst : List byte) (ret_val : val_) : 
    (∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem) →
    ret_val == (inv_bytes_ v_valtype var_0_lst) →
    wf_val_ v_valtype ret_val →
    inv_bytes__is_wf v_valtype var_0_lst ret_val


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


def inez_ (v_N : N) (v_iN : iN) : u32 :=
  .mk_uN (nat_of_bool ((proj_uN_0 v_iN) != 0))

inductive inez__is_wf : N → iN → u32 → Prop where
  | inez__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) : 
    wf_uN v_N v_iN →
    ret_val == (inez_ v_N v_iN) →
    wf_uN 32 ret_val →
    inez__is_wf v_N v_iN ret_val


abbrev addr : Type := Nat

abbrev funcaddr : Type := addr

abbrev globaladdr : Type := addr

abbrev tableaddr : Type := addr

abbrev memaddr : Type := addr

inductive externaddr : Type where
  | FUNC (v_funcaddr : funcaddr) : externaddr
  | GLOBAL (v_globaladdr : globaladdr) : externaddr
  | TABLE (v_tableaddr : tableaddr) : externaddr
  | MEM (v_memaddr : memaddr) : externaddr
deriving Inhabited, BEq

inductive val : Type where
  | CONST (v_valtype : valtype) (_ : val_) : val
deriving Inhabited, BEq

inductive wf_val : val → Prop where
  | val_case_0 (v_valtype : valtype) (var_0 : val_) : 
    wf_val_ v_valtype var_0 →
    wf_val (val.CONST v_valtype var_0)


inductive result : Type where
  | _VALS (val_lst : List val) : result
  | TRAP : result
deriving Inhabited, BEq

inductive wf_result : result → Prop where
  | result_case_0 (val_lst : List val) : 
    (∀ v_val_elem ∈ val_lst, wf_val v_val_elem) →
    wf_result (result._VALS val_lst)
  | result_case_1 : wf_result result.TRAP


structure exportinst where
  MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

inductive wf_exportinst : exportinst → Prop where
  | exportinst_case_ (var_0 : name) (var_1 : externaddr) : 
    wf_name var_0 →
    wf_exportinst ({
      NAME := var_0
      ADDR := var_1 : exportinst
    })


structure moduleinst where
  MKmoduleinst ::
  TYPES : List functype
  FUNCS : List funcaddr
  GLOBALS : List globaladdr
  TABLES : List tableaddr
  MEMS : List memaddr
  EXPORTS : List exportinst
deriving Inhabited, BEq

inductive wf_moduleinst : moduleinst → Prop where
  | moduleinst_case_ (var_0_lst : List functype) (var_1_lst : List funcaddr) (var_2_lst : List globaladdr) (var_3_lst : List tableaddr) (var_4_lst : List memaddr) (var_5_lst : List exportinst) : 
    (∀ var_5_elem ∈ var_5_lst, wf_exportinst var_5_elem) →
    wf_moduleinst ({
      TYPES := var_0_lst
      FUNCS := var_1_lst
      GLOBALS := var_2_lst
      TABLES := var_3_lst
      MEMS := var_4_lst
      EXPORTS := var_5_lst : moduleinst
    })


structure funcinst where
  MKfuncinst ::
  TYPE : functype
  MODULE : moduleinst
  CODE : func
deriving Inhabited, BEq

inductive wf_funcinst : funcinst → Prop where
  | funcinst_case_ (var_0 : functype) (var_1 : moduleinst) (var_2 : func) : 
    wf_moduleinst var_1 →
    wf_func var_2 →
    wf_funcinst ({
      TYPE := var_0
      MODULE := var_1
      CODE := var_2 : funcinst
    })


structure globalinst where
  MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

inductive wf_globalinst : globalinst → Prop where
  | globalinst_case_ (var_0 : globaltype) (var_1 : val) : 
    wf_val var_1 →
    wf_globalinst ({
      TYPE := var_0
      VALUE := var_1 : globalinst
    })


structure tableinst where
  MKtableinst ::
  TYPE : tabletype
  REFS : List (Option funcaddr)
deriving Inhabited, BEq

inductive wf_tableinst : tableinst → Prop where
  | tableinst_case_ (var_0 : tabletype) (var_1_opt_lst : List (Option funcaddr)) : 
    wf_limits var_0 →
    wf_tableinst ({
      TYPE := var_0
      REFS := var_1_opt_lst : tableinst
    })


structure meminst where
  MKmeminst ::
  TYPE : memtype
  BYTES : List byte
deriving Inhabited, BEq

inductive wf_meminst : meminst → Prop where
  | meminst_case_ (var_0 : memtype) (var_1_lst : List byte) : 
    wf_limits var_0 →
    (∀ var_1_elem ∈ var_1_lst, wf_byte var_1_elem) →
    wf_meminst ({
      TYPE := var_0
      BYTES := var_1_lst : meminst
    })


structure store where
  MKstore ::
  FUNCS : List funcinst
  GLOBALS : List globalinst
  TABLES : List tableinst
  MEMS : List meminst
deriving Inhabited, BEq

inductive wf_store : store → Prop where
  | store_case_ (var_0_lst : List funcinst) (var_1_lst : List globalinst) (var_2_lst : List tableinst) (var_3_lst : List meminst) : 
    (∀ var_0_elem ∈ var_0_lst, wf_funcinst var_0_elem) →
    (∀ var_1_elem ∈ var_1_lst, wf_globalinst var_1_elem) →
    (∀ var_2_elem ∈ var_2_lst, wf_tableinst var_2_elem) →
    (∀ var_3_elem ∈ var_3_lst, wf_meminst var_3_elem) →
    wf_store ({
      FUNCS := var_0_lst
      GLOBALS := var_1_lst
      TABLES := var_2_lst
      MEMS := var_3_lst : store
    })


structure frame where
  MKframe ::
  LOCALS : List val
  MODULE : moduleinst
deriving Inhabited, BEq

inductive wf_frame : frame → Prop where
  | frame_case_ (var_0_lst : List val) (var_1 : moduleinst) : 
    (∀ var_0_elem ∈ var_0_lst, wf_val var_0_elem) →
    wf_moduleinst var_1 →
    wf_frame ({
      LOCALS := var_0_lst
      MODULE := var_1 : frame
    })


inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq

inductive wf_state : state → Prop where
  | state_case_0 (v_store : store) (v_frame : frame) : 
    wf_store v_store →
    wf_frame v_frame →
    wf_state (state.mk_state v_store v_frame)


inductive admininstr : Type where
  | NOP : admininstr
  | UNREACHABLE : admininstr
  | DROP : admininstr
  | SELECT : admininstr
  | BLOCK (v_blocktype : blocktype) (instr_lst : List instr) : admininstr
  | LOOP (v_blocktype : blocktype) (instr_lst : List instr) : admininstr
  | IFELSE (v_blocktype : blocktype) (instr_lst_0 : List instr) (instr_lst_1 : List instr) : admininstr
  | BR (v_labelidx : labelidx) : admininstr
  | BR_IF (v_labelidx : labelidx) : admininstr
  | BR_TABLE (labelidx_lst : List labelidx) (v_labelidx : labelidx) : admininstr
  | CALL (v_funcidx : funcidx) : admininstr
  | CALL_INDIRECT (v_typeidx : typeidx) : admininstr
  | RETURN : admininstr
  | CONST (v_valtype : valtype) (_ : val_) : admininstr
  | UNOP (v_valtype : valtype) (_ : unop_) : admininstr
  | BINOP (v_valtype : valtype) (_ : binop_) : admininstr
  | TESTOP (v_valtype : valtype) (_ : testop_) : admininstr
  | RELOP (v_valtype : valtype) (_ : relop_) : admininstr
  | CVTOP (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : admininstr
  | LOCAL_GET (v_localidx : localidx) : admininstr
  | LOCAL_SET (v_localidx : localidx) : admininstr
  | LOCAL_TEE (v_localidx : localidx) : admininstr
  | GLOBAL_GET (v_globalidx : globalidx) : admininstr
  | GLOBAL_SET (v_globalidx : globalidx) : admininstr
  | LOAD (v_valtype : valtype) (_ : Option loadop_) (v_memarg : memarg) : admininstr
  | STORE (v_valtype : valtype) (sz_opt : Option sz) (v_memarg : memarg) : admininstr
  | MEMORY_SIZE : admininstr
  | MEMORY_GROW : admininstr
  | CALL_ADDR (v_funcaddr : funcaddr) : admininstr
  | LABEL_ (v_n : n) (instr_lst : List instr) (admininstr_lst : List admininstr) : admininstr
  | FRAME_ (v_n : n) (v_frame : frame) (admininstr_lst : List admininstr) : admininstr
  | TRAP : admininstr
deriving Inhabited, BEq

def admininstr_instr (var_0 : instr) : admininstr :=
  match var_0 with
  | instr.NOP => admininstr.NOP
  | instr.UNREACHABLE => admininstr.UNREACHABLE
  | instr.DROP => admininstr.DROP
  | instr.SELECT => admininstr.SELECT
  | instr.BLOCK x0 x1 => admininstr.BLOCK x0 x1
  | instr.LOOP x0 x1 => admininstr.LOOP x0 x1
  | instr.IFELSE x0 x1 x2 => admininstr.IFELSE x0 x1 x2
  | instr.BR x0 => admininstr.BR x0
  | instr.BR_IF x0 => admininstr.BR_IF x0
  | instr.BR_TABLE x0 x1 => admininstr.BR_TABLE x0 x1
  | instr.CALL x0 => admininstr.CALL x0
  | instr.CALL_INDIRECT x0 => admininstr.CALL_INDIRECT x0
  | instr.RETURN => admininstr.RETURN
  | instr.CONST x0 x1 => admininstr.CONST x0 x1
  | instr.UNOP x0 x1 => admininstr.UNOP x0 x1
  | instr.BINOP x0 x1 => admininstr.BINOP x0 x1
  | instr.TESTOP x0 x1 => admininstr.TESTOP x0 x1
  | instr.RELOP x0 x1 => admininstr.RELOP x0 x1
  | instr.CVTOP x0 x1 x2 => admininstr.CVTOP x0 x1 x2
  | instr.LOCAL_GET x0 => admininstr.LOCAL_GET x0
  | instr.LOCAL_SET x0 => admininstr.LOCAL_SET x0
  | instr.LOCAL_TEE x0 => admininstr.LOCAL_TEE x0
  | instr.GLOBAL_GET x0 => admininstr.GLOBAL_GET x0
  | instr.GLOBAL_SET x0 => admininstr.GLOBAL_SET x0
  | instr.LOAD x0 x1 x2 => admininstr.LOAD x0 x1 x2
  | instr.STORE x0 x1 x2 => admininstr.STORE x0 x1 x2
  | instr.MEMORY_SIZE => admininstr.MEMORY_SIZE
  | instr.MEMORY_GROW => admininstr.MEMORY_GROW

def admininstr_val (var_0 : val) : admininstr :=
  match var_0 with
  | val.CONST x0 x1 => admininstr.CONST x0 x1

inductive wf_admininstr : admininstr → Prop where
  | admininstr_case_0 : wf_admininstr admininstr.NOP
  | admininstr_case_1 : wf_admininstr admininstr.UNREACHABLE
  | admininstr_case_2 : wf_admininstr admininstr.DROP
  | admininstr_case_3 : wf_admininstr admininstr.SELECT
  | admininstr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    wf_admininstr (admininstr.BLOCK v_blocktype instr_lst)
  | admininstr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    wf_admininstr (admininstr.LOOP v_blocktype instr_lst)
  | admininstr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    (∀ instr_lst_0_elem ∈ instr_lst_0_lst, wf_instr instr_lst_0_elem) →
    wf_admininstr (admininstr.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | admininstr_case_7 (v_labelidx : labelidx) : 
    wf_uN 32 v_labelidx →
    wf_admininstr (admininstr.BR v_labelidx)
  | admininstr_case_8 (v_labelidx : labelidx) : 
    wf_uN 32 v_labelidx →
    wf_admininstr (admininstr.BR_IF v_labelidx)
  | admininstr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) : 
    (∀ v_labelidx_elem ∈ labelidx_lst, wf_uN 32 v_labelidx_elem) →
    wf_uN 32 v_labelidx →
    wf_admininstr (admininstr.BR_TABLE labelidx_lst v_labelidx)
  | admininstr_case_10 (v_funcidx : funcidx) : 
    wf_uN 32 v_funcidx →
    wf_admininstr (admininstr.CALL v_funcidx)
  | admininstr_case_11 (v_typeidx : typeidx) : 
    wf_uN 32 v_typeidx →
    wf_admininstr (admininstr.CALL_INDIRECT v_typeidx)
  | admininstr_case_12 : wf_admininstr admininstr.RETURN
  | admininstr_case_13 (v_valtype : valtype) (var_0 : val_) : 
    wf_val_ v_valtype var_0 →
    wf_admininstr (admininstr.CONST v_valtype var_0)
  | admininstr_case_14 (v_valtype : valtype) (var_0 : unop_) : 
    wf_unop_ v_valtype var_0 →
    wf_admininstr (admininstr.UNOP v_valtype var_0)
  | admininstr_case_15 (v_valtype : valtype) (var_0 : binop_) : 
    wf_binop_ v_valtype var_0 →
    wf_admininstr (admininstr.BINOP v_valtype var_0)
  | admininstr_case_16 (v_valtype : valtype) (var_0 : testop_) : 
    wf_testop_ v_valtype var_0 →
    wf_admininstr (admininstr.TESTOP v_valtype var_0)
  | admininstr_case_17 (v_valtype : valtype) (var_0 : relop_) : 
    wf_relop_ v_valtype var_0 →
    wf_admininstr (admininstr.RELOP v_valtype var_0)
  | admininstr_case_18 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : 
    valtype_1 != valtype_2 →
    wf_admininstr (admininstr.CVTOP valtype_1 valtype_2 v_cvtop)
  | admininstr_case_19 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_admininstr (admininstr.LOCAL_GET v_localidx)
  | admininstr_case_20 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_admininstr (admininstr.LOCAL_SET v_localidx)
  | admininstr_case_21 (v_localidx : localidx) : 
    wf_uN 32 v_localidx →
    wf_admininstr (admininstr.LOCAL_TEE v_localidx)
  | admininstr_case_22 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_admininstr (admininstr.GLOBAL_GET v_globalidx)
  | admininstr_case_23 (v_globalidx : globalidx) : 
    wf_uN 32 v_globalidx →
    wf_admininstr (admininstr.GLOBAL_SET v_globalidx)
  | admininstr_case_24 (v_valtype : valtype) (var_0_opt : Option loadop_) (v_memarg : memarg) : 
    (∀ var_0_elem ∈ Option.toList var_0_opt, wf_loadop_ v_valtype var_0_elem) →
    wf_memarg v_memarg →
    wf_admininstr (admininstr.LOAD v_valtype var_0_opt v_memarg)
  | admininstr_case_25 (Inn_opt : Option Inn) (valtype_opt : Option valtype) (v_valtype : valtype) (sz_opt : Option sz) (v_memarg : memarg) : 
    (∀ v_sz_elem ∈ Option.toList sz_opt, wf_sz v_sz_elem) →
    wf_memarg v_memarg →
    ((Inn_opt == none) ↔ (sz_opt == none)) →
    ((Inn_opt == none) ↔ (valtype_opt == none)) →
    (∀ __iter_tuple ∈ Option.toList Inn_opt |>.zip (Option.toList sz_opt) |>.zip (Option.toList valtype_opt), ((__iter_tuple.2) == (valtype_Inn (__iter_tuple.1.1))) && ((proj_sz_0 (__iter_tuple.1.2)) < (size (valtype_Inn (__iter_tuple.1.1))))) →
    wf_admininstr (admininstr.STORE v_valtype sz_opt v_memarg)
  | admininstr_case_26 : wf_admininstr admininstr.MEMORY_SIZE
  | admininstr_case_27 : wf_admininstr admininstr.MEMORY_GROW
  | admininstr_case_28 (v_funcaddr : funcaddr) : wf_admininstr (admininstr.CALL_ADDR v_funcaddr)
  | admininstr_case_29 (v_n : n) (instr_lst : List instr) (admininstr_lst : List admininstr) : 
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    (∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem) →
    wf_admininstr (admininstr.LABEL_ v_n instr_lst admininstr_lst)
  | admininstr_case_30 (v_n : n) (v_frame : frame) (admininstr_lst : List admininstr) : 
    wf_frame v_frame →
    (∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem) →
    wf_admininstr (admininstr.FRAME_ v_n v_frame admininstr_lst)
  | admininstr_case_31 : wf_admininstr admininstr.TRAP


inductive config : Type where
  | mk_config (v_state : state) (admininstr_lst : List admininstr) : config
deriving Inhabited, BEq

inductive wf_config : config → Prop where
  | config_case_0 (v_state : state) (admininstr_lst : List admininstr) : 
    wf_state v_state →
    (∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem) →
    wf_config (config.mk_config v_state admininstr_lst)


def default_ (v_valtype : valtype) : val :=
  match v_valtype with
  | valtype.I32 => val.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN 0))
  | valtype.I64 => val.CONST valtype.I64 (val_.mk_val__0 Inn.I64 (uN.mk_uN 0))
  | valtype.F32 => val.CONST valtype.F32 (val_.mk_val__1 Fnn.F32 (fzero 32))
  | valtype.F64 => val.CONST valtype.F64 (val_.mk_val__1 Fnn.F64 (fzero 64))

inductive default__is_wf : valtype → val → Prop where
  | default__is_wf_0 (v_valtype : valtype) (ret_val : val) : 
    ret_val == (default_ v_valtype) →
    wf_val ret_val →
    default__is_wf v_valtype ret_val


inductive fun_funcsxa : List externaddr → List funcaddr → Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 (fa : Nat) (xv_lst : List externaddr) (var_0 : List funcaddr) : 
    fun_funcsxa xv_lst var_0 →
    fun_funcsxa ([externaddr.FUNC fa] ++ xv_lst) ([fa] ++ var_0)
  | fun_funcsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List funcaddr) : 
    fun_funcsxa xv_lst var_0 →
    fun_funcsxa ([v_externaddr] ++ xv_lst) var_0


inductive fun_globalsxa : List externaddr → List globaladdr → Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 (ga : Nat) (xv_lst : List externaddr) (var_0 : List globaladdr) : 
    fun_globalsxa xv_lst var_0 →
    fun_globalsxa ([externaddr.GLOBAL ga] ++ xv_lst) ([ga] ++ var_0)
  | fun_globalsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List globaladdr) : 
    fun_globalsxa xv_lst var_0 →
    fun_globalsxa ([v_externaddr] ++ xv_lst) var_0


inductive fun_tablesxa : List externaddr → List tableaddr → Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 (ta : Nat) (xv_lst : List externaddr) (var_0 : List tableaddr) : 
    fun_tablesxa xv_lst var_0 →
    fun_tablesxa ([externaddr.TABLE ta] ++ xv_lst) ([ta] ++ var_0)
  | fun_tablesxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List tableaddr) : 
    fun_tablesxa xv_lst var_0 →
    fun_tablesxa ([v_externaddr] ++ xv_lst) var_0


inductive fun_memsxa : List externaddr → List memaddr → Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 (ma : Nat) (xv_lst : List externaddr) (var_0 : List memaddr) : 
    fun_memsxa xv_lst var_0 →
    fun_memsxa ([externaddr.MEM ma] ++ xv_lst) ([ma] ++ var_0)
  | fun_memsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List memaddr) : 
    fun_memsxa xv_lst var_0 →
    fun_memsxa ([v_externaddr] ++ xv_lst) var_0


def fun_store (v_state : state) : store :=
  match v_state with
  | state.mk_state s f => s

inductive store_is_wf : state → store → Prop where
  | store_is_wf_0 (v_state : state) (ret_val : store) : 
    wf_state v_state →
    ret_val == (fun_store v_state) →
    wf_store ret_val →
    store_is_wf v_state ret_val


def fun_frame (v_state : state) : frame :=
  match v_state with
  | state.mk_state s f => f

inductive frame_is_wf : state → frame → Prop where
  | frame_is_wf_0 (v_state : state) (ret_val : frame) : 
    wf_state v_state →
    ret_val == (fun_frame v_state) →
    wf_frame ret_val →
    frame_is_wf v_state ret_val


def fun_funcaddr (v_state : state) : List funcaddr :=
  match v_state with
  | state.mk_state s f => f.MODULE.FUNCS

def fun_funcinst (v_state : state) : List funcinst :=
  match v_state with
  | state.mk_state s f => s.FUNCS

inductive funcinst_is_wf : state → List funcinst → Prop where
  | funcinst_is_wf_0 (v_state : state) (ret_val_lst : List funcinst) : 
    wf_state v_state →
    ret_val_lst == (fun_funcinst v_state) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_funcinst ret_val_elem) →
    funcinst_is_wf v_state ret_val_lst


def fun_globalinst (v_state : state) : List globalinst :=
  match v_state with
  | state.mk_state s f => s.GLOBALS

inductive globalinst_is_wf : state → List globalinst → Prop where
  | globalinst_is_wf_0 (v_state : state) (ret_val_lst : List globalinst) : 
    wf_state v_state →
    ret_val_lst == (fun_globalinst v_state) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_globalinst ret_val_elem) →
    globalinst_is_wf v_state ret_val_lst


def fun_tableinst (v_state : state) : List tableinst :=
  match v_state with
  | state.mk_state s f => s.TABLES

inductive tableinst_is_wf : state → List tableinst → Prop where
  | tableinst_is_wf_0 (v_state : state) (ret_val_lst : List tableinst) : 
    wf_state v_state →
    ret_val_lst == (fun_tableinst v_state) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_tableinst ret_val_elem) →
    tableinst_is_wf v_state ret_val_lst


def fun_meminst (v_state : state) : List meminst :=
  match v_state with
  | state.mk_state s f => s.MEMS

inductive meminst_is_wf : state → List meminst → Prop where
  | meminst_is_wf_0 (v_state : state) (ret_val_lst : List meminst) : 
    wf_state v_state →
    ret_val_lst == (fun_meminst v_state) →
    (∀ ret_val_elem ∈ ret_val_lst, wf_meminst ret_val_elem) →
    meminst_is_wf v_state ret_val_lst


def fun_moduleinst (v_state : state) : moduleinst :=
  match v_state with
  | state.mk_state s f => f.MODULE

inductive moduleinst_is_wf : state → moduleinst → Prop where
  | moduleinst_is_wf_0 (v_state : state) (ret_val : moduleinst) : 
    wf_state v_state →
    ret_val == (fun_moduleinst v_state) →
    wf_moduleinst ret_val →
    moduleinst_is_wf v_state ret_val


def fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
  match v_state with
  | state.mk_state s f => (f.MODULE.TYPES)[proj_uN_0 v_typeidx]!

def fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
  match v_state with
  | state.mk_state s f => (s.FUNCS)[(f.MODULE.FUNCS)[proj_uN_0 v_funcidx]!]!

inductive func_is_wf : state → funcidx → funcinst → Prop where
  | func_is_wf_0 (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst) : 
    wf_state v_state →
    wf_uN 32 v_funcidx →
    ret_val == (fun_func v_state v_funcidx) →
    wf_funcinst ret_val →
    func_is_wf v_state v_funcidx ret_val


def fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
  match v_state with
  | state.mk_state s f => (s.GLOBALS)[(f.MODULE.GLOBALS)[proj_uN_0 v_globalidx]!]!

inductive global_is_wf : state → globalidx → globalinst → Prop where
  | global_is_wf_0 (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst) : 
    wf_state v_state →
    wf_uN 32 v_globalidx →
    ret_val == (fun_global v_state v_globalidx) →
    wf_globalinst ret_val →
    global_is_wf v_state v_globalidx ret_val


def fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
  match v_state with
  | state.mk_state s f => (s.TABLES)[(f.MODULE.TABLES)[proj_uN_0 v_tableidx]!]!

inductive table_is_wf : state → tableidx → tableinst → Prop where
  | table_is_wf_0 (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst) : 
    wf_state v_state →
    wf_uN 32 v_tableidx →
    ret_val == (fun_table v_state v_tableidx) →
    wf_tableinst ret_val →
    table_is_wf v_state v_tableidx ret_val


def fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
  match v_state with
  | state.mk_state s f => (s.MEMS)[(f.MODULE.MEMS)[proj_uN_0 v_memidx]!]!

inductive mem_is_wf : state → memidx → meminst → Prop where
  | mem_is_wf_0 (v_state : state) (v_memidx : memidx) (ret_val : meminst) : 
    wf_state v_state →
    wf_uN 32 v_memidx →
    ret_val == (fun_mem v_state v_memidx) →
    wf_meminst ret_val →
    mem_is_wf v_state v_memidx ret_val


def fun_local (v_state : state) (v_localidx : localidx) : val :=
  match v_state with
  | state.mk_state s f => (f.LOCALS)[proj_uN_0 v_localidx]!

inductive local_is_wf : state → localidx → val → Prop where
  | local_is_wf_0 (v_state : state) (v_localidx : localidx) (ret_val : val) : 
    wf_state v_state →
    wf_uN 32 v_localidx →
    ret_val == (fun_local v_state v_localidx) →
    wf_val ret_val →
    local_is_wf v_state v_localidx ret_val


def with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state s ({
    f with 
    LOCALS := List.modify (f.LOCALS) (proj_uN_0 v_localidx) (fun elem_1 => v_val)
  })

inductive with_local_is_wf : state → localidx → val → state → Prop where
  | with_local_is_wf_0 (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state) : 
    wf_state v_state →
    wf_uN 32 v_localidx →
    wf_val v_val →
    ret_val == (with_local v_state v_localidx v_val) →
    wf_state ret_val →
    with_local_is_wf v_state v_localidx v_val ret_val


def with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with 
    GLOBALS := List.modify (s.GLOBALS) ((f.MODULE.GLOBALS)[proj_uN_0 v_globalidx]!) (fun elem_1 => {
      elem_1 with 
      VALUE := v_val
    })
  }) f

inductive with_global_is_wf : state → globalidx → val → state → Prop where
  | with_global_is_wf_0 (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state) : 
    wf_state v_state →
    wf_uN 32 v_globalidx →
    wf_val v_val →
    ret_val == (with_global v_state v_globalidx v_val) →
    wf_state ret_val →
    with_global_is_wf v_state v_globalidx v_val ret_val


def with_table (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_funcaddr : funcaddr) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with 
    TABLES := List.modify (s.TABLES) ((f.MODULE.TABLES)[proj_uN_0 v_tableidx]!) (fun elem_1 => {
      elem_1 with 
      REFS := List.modify (elem_1.REFS) nat (fun elem_2 => some v_funcaddr)
    })
  }) f

inductive with_table_is_wf : state → tableidx → Nat → funcaddr → state → Prop where
  | with_table_is_wf_0 (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_funcaddr : funcaddr) (ret_val : state) : 
    wf_state v_state →
    wf_uN 32 v_tableidx →
    ret_val == (with_table v_state v_tableidx nat v_funcaddr) →
    wf_state ret_val →
    with_table_is_wf v_state v_tableidx nat v_funcaddr ret_val


def with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with 
    TABLES := List.modify (s.TABLES) ((f.MODULE.TABLES)[proj_uN_0 v_tableidx]!) (fun elem_1 => v_tableinst)
  }) f

inductive with_tableinst_is_wf : state → tableidx → tableinst → state → Prop where
  | with_tableinst_is_wf_0 (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state) : 
    wf_state v_state →
    wf_uN 32 v_tableidx →
    wf_tableinst v_tableinst →
    ret_val == (with_tableinst v_state v_tableidx v_tableinst) →
    wf_state ret_val →
    with_tableinst_is_wf v_state v_tableidx v_tableinst ret_val


def with_mem (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with 
    MEMS := List.modify (s.MEMS) ((f.MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => {
      elem_1 with 
      BYTES := ((elem_1.BYTES.take nat) ++ var_0_lst) ++ (elem_1.BYTES.drop (nat + nat_0))
    })
  }) f

inductive with_mem_is_wf : state → memidx → Nat → Nat → List byte → state → Prop where
  | with_mem_is_wf_0 (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) (ret_val : state) : 
    wf_state v_state →
    wf_uN 32 v_memidx →
    (∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem) →
    ret_val == (with_mem v_state v_memidx nat nat_0 var_0_lst) →
    wf_state ret_val →
    with_mem_is_wf v_state v_memidx nat nat_0 var_0_lst ret_val


def with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with 
    MEMS := List.modify (s.MEMS) ((f.MODULE.MEMS)[proj_uN_0 v_memidx]!) (fun elem_1 => v_meminst)
  }) f

inductive with_meminst_is_wf : state → memidx → meminst → state → Prop where
  | with_meminst_is_wf_0 (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state) : 
    wf_state v_state →
    wf_uN 32 v_memidx →
    wf_meminst v_meminst →
    ret_val == (with_meminst v_state v_memidx v_meminst) →
    wf_state ret_val →
    with_meminst_is_wf v_state v_memidx v_meminst ret_val


def with_mems_elem (v_state : state) (nat : Nat) (nat_0 : Nat) (nat_1 : Nat) (v_meminst : meminst) : state :=
  match v_state with
  | state.mk_state s f => state.mk_state ({
    s with 
    MEMS := ((s.MEMS.take nat) ++ (List.modify ((s.MEMS.drop nat).take nat_0) nat_1 (fun elem_1 => v_meminst))) ++ (s.MEMS.drop (nat + nat_0))
  }) f

inductive with_mems_elem_is_wf : state → Nat → Nat → Nat → meminst → state → Prop where
  | with_mems_elem_is_wf_0 (v_state : state) (nat : Nat) (nat_0 : Nat) (nat_1 : Nat) (v_meminst : meminst) (ret_val : state) : 
    wf_state v_state →
    wf_meminst v_meminst →
    ret_val == (with_mems_elem v_state nat nat_0 nat_1 v_meminst) →
    wf_state ret_val →
    with_mems_elem_is_wf v_state nat nat_0 nat_1 v_meminst ret_val


inductive fun_growtable_before_fun_growtable_case_1 : tableinst → Nat → Prop where
  | fun_growtable_case_0 (ti : tableinst) (v_n : Nat) (ti' : tableinst) (i : uN) (j_opt : Option u32) (a_lst : List addr) (i' : Nat) : 
    ti == ({
      TYPE := .mk_limits i j_opt
      REFS := a_lst |>.map (fun a_1_elem => some a_1_elem) : tableinst
    }) →
    i' == ((List.length a_lst) + v_n) →
    ti' == ({
      TYPE := .mk_limits (.mk_uN i') j_opt
      REFS := (a_lst |>.map (fun a_3_elem => some a_3_elem)) ++ (List.replicate v_n none) : tableinst
    }) →
    (∀ j_3_elem ∈ Option.toList j_opt, i' ≤ (proj_uN_0 j_3_elem)) →
    wf_tableinst ({
      TYPE := .mk_limits i j_opt
      REFS := a_lst |>.map (fun a_4_elem => some a_4_elem) : tableinst
    }) →
    wf_tableinst ({
      TYPE := .mk_limits (.mk_uN i') j_opt
      REFS := (a_lst |>.map (fun a_5_elem => some a_5_elem)) ++ (List.replicate v_n none) : tableinst
    }) →
    fun_growtable_before_fun_growtable_case_1 ti v_n


inductive fun_growtable : tableinst → Nat → Option tableinst → Prop where
  | fun_growtable_case_0 (ti : tableinst) (v_n : Nat) (ti' : tableinst) (i : uN) (j_opt : Option u32) (a_lst : List addr) (i' : Nat) : 
    ti == ({
      TYPE := .mk_limits i j_opt
      REFS := a_lst |>.map (fun a_1_elem => some a_1_elem) : tableinst
    }) →
    i' == ((List.length a_lst) + v_n) →
    ti' == ({
      TYPE := .mk_limits (.mk_uN i') j_opt
      REFS := (a_lst |>.map (fun a_3_elem => some a_3_elem)) ++ (List.replicate v_n none) : tableinst
    }) →
    (∀ j_3_elem ∈ Option.toList j_opt, i' ≤ (proj_uN_0 j_3_elem)) →
    wf_tableinst ({
      TYPE := .mk_limits i j_opt
      REFS := a_lst |>.map (fun a_4_elem => some a_4_elem) : tableinst
    }) →
    wf_tableinst ({
      TYPE := .mk_limits (.mk_uN i') j_opt
      REFS := (a_lst |>.map (fun a_5_elem => some a_5_elem)) ++ (List.replicate v_n none) : tableinst
    }) →
    fun_growtable ti v_n (some ti')
  | fun_growtable_case_1 (x0 : tableinst) (x1 : Nat) : 
    ¬ fun_growtable_before_fun_growtable_case_1 x0 x1 →
    fun_growtable x0 x1 none


inductive growtable_is_wf : tableinst → Nat → tableinst → Prop where
  | growtable_is_wf_0 (v_tableinst : tableinst) (nat : Nat) (ret_val : tableinst) (var_0 : Option tableinst) : 
    fun_growtable v_tableinst nat var_0 →
    wf_tableinst v_tableinst →
    var_0 != none →
    ret_val == (Option.get! var_0) →
    wf_tableinst ret_val →
    growtable_is_wf v_tableinst nat ret_val


inductive fun_growmemory_before_fun_growmemory_case_1 : meminst → Nat → Prop where
  | fun_growmemory_case_0 (mi : meminst) (v_n : Nat) (mi' : meminst) (i : u32) (j_opt : Option u32) (b_lst : List byte) (i' : Rat) : 
    ({
      TYPE := .mk_limits i j_opt
      BYTES := b_lst : meminst
    }) == mi →
    i' == ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) →
    mi' == ({
      TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    (∀ j_8_elem ∈ Option.toList j_opt, i' ≤ ((proj_uN_0 j_8_elem) : Rat)) →
    wf_meminst ({
      TYPE := .mk_limits i j_opt
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    fun_growmemory_before_fun_growmemory_case_1 mi v_n


inductive fun_growmemory : meminst → Nat → Option meminst → Prop where
  | fun_growmemory_case_0 (mi : meminst) (v_n : Nat) (mi' : meminst) (i : u32) (j_opt : Option u32) (b_lst : List byte) (i' : Rat) : 
    ({
      TYPE := .mk_limits i j_opt
      BYTES := b_lst : meminst
    }) == mi →
    i' == ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) →
    mi' == ({
      TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    (∀ j_8_elem ∈ Option.toList j_opt, i' ≤ ((proj_uN_0 j_8_elem) : Rat)) →
    wf_meminst ({
      TYPE := .mk_limits i j_opt
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
      BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (byte.mk_byte 0)) : meminst
    }) →
    fun_growmemory mi v_n (some mi')
  | fun_growmemory_case_1 (x0 : meminst) (x1 : Nat) : 
    ¬ fun_growmemory_before_fun_growmemory_case_1 x0 x1 →
    fun_growmemory x0 x1 none


inductive growmemory_is_wf : meminst → Nat → meminst → Prop where
  | growmemory_is_wf_0 (v_meminst : meminst) (nat : Nat) (ret_val : meminst) (var_0 : Option meminst) : 
    fun_growmemory v_meminst nat var_0 →
    wf_meminst v_meminst →
    var_0 != none →
    ret_val == (Option.get! var_0) →
    wf_meminst ret_val →
    growmemory_is_wf v_meminst nat ret_val


structure context where
  MKcontext ::
  TYPES : List functype
  FUNCS : List functype
  GLOBALS : List globaltype
  TABLES : List tabletype
  MEMS : List memtype
  LOCALS : List valtype
  LABELS : List resulttype
  RETURN : Option resulttype
deriving Inhabited, BEq

def append_context (arg1 arg2 : context) : context where
  TYPES := (arg1.TYPES) ++ (arg2.TYPES)
  FUNCS := (arg1.FUNCS) ++ (arg2.FUNCS)
  GLOBALS := (arg1.GLOBALS) ++ (arg2.GLOBALS)
  TABLES := (arg1.TABLES) ++ (arg2.TABLES)
  MEMS := (arg1.MEMS) ++ (arg2.MEMS)
  LOCALS := (arg1.LOCALS) ++ (arg2.LOCALS)
  LABELS := (arg1.LABELS) ++ (arg2.LABELS)
  RETURN := Option.orElse (arg1.RETURN) (fun _ => arg2.RETURN)

instance  : Append context where
  append := append_context

inductive wf_context : context → Prop where
  | context_case_ (var_0_lst : List functype) (var_1_lst : List functype) (var_2_lst : List globaltype) (var_3_lst : List tabletype) (var_4_lst : List memtype) (var_5_lst : List valtype) (var_6_lst : List resulttype) (var_7_opt : Option resulttype) : 
    (∀ var_3_elem ∈ var_3_lst, wf_limits var_3_elem) →
    (∀ var_4_elem ∈ var_4_lst, wf_limits var_4_elem) →
    wf_context ({
      TYPES := var_0_lst
      FUNCS := var_1_lst
      GLOBALS := var_2_lst
      TABLES := var_3_lst
      MEMS := var_4_lst
      LOCALS := var_5_lst
      LABELS := var_6_lst
      RETURN := var_7_opt : context
    })


inductive Limits_ok : limits → Nat → Prop where
  | mk_Limits_ok (v_n : n) (m_opt : Option m) (k : Nat) : 
    v_n ≤ k →
    (∀ v_m_elem ∈ Option.toList m_opt, (v_n ≤ v_m_elem) && (v_m_elem ≤ k)) →
    wf_limits (limits.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))) →
    Limits_ok (limits.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))) k


inductive Functype_ok : functype → Prop where
  | mk_Functype_ok (t_1_lst : List valtype) (t_2_opt : Option valtype) : Functype_ok (functype.mk_functype t_1_lst (Option.toList t_2_opt))


inductive Globaltype_ok : globaltype → Prop where
  | mk_Globaltype_ok (t : valtype) : Globaltype_ok (globaltype.mk_globaltype (some r_MUT.MUT) t)


inductive Tabletype_ok : tabletype → Prop where
  | mk_Tabletype_ok (v_limits : limits) : 
    Limits_ok v_limits (Int.toNat (((2 ^ 32) : Int) - (1 : Int))) →
    wf_limits v_limits →
    Tabletype_ok v_limits


inductive Memtype_ok : memtype → Prop where
  | mk_Memtype_ok (v_limits : limits) : 
    Limits_ok v_limits (2 ^ 16) →
    wf_limits v_limits →
    Memtype_ok v_limits


inductive Externtype_ok : externtype → Prop where
  | func (v_functype : functype) : 
    Functype_ok v_functype →
    wf_externtype (externtype.FUNC v_functype) →
    Externtype_ok (externtype.FUNC v_functype)
  | global (v_globaltype : globaltype) : 
    Globaltype_ok v_globaltype →
    wf_externtype (externtype.GLOBAL v_globaltype) →
    Externtype_ok (externtype.GLOBAL v_globaltype)
  | table (v_tabletype : tabletype) : 
    Tabletype_ok v_tabletype →
    wf_externtype (externtype.TABLE v_tabletype) →
    Externtype_ok (externtype.TABLE v_tabletype)
  | mem (v_memtype : memtype) : 
    Memtype_ok v_memtype →
    wf_externtype (externtype.MEM v_memtype) →
    Externtype_ok (externtype.MEM v_memtype)


inductive Limits_sub : limits → limits → Prop where
  | mk_Limits_sub (n_11 : n) (n_12 : n) (n_21 : n) (n_22 : n) : 
    n_11 ≥ n_21 →
    n_12 ≤ n_22 →
    wf_limits (limits.mk_limits (.mk_uN n_11) (some (.mk_uN n_12))) →
    wf_limits (limits.mk_limits (.mk_uN n_21) (some (.mk_uN n_22))) →
    Limits_sub (limits.mk_limits (.mk_uN n_11) (some (.mk_uN n_12))) (limits.mk_limits (.mk_uN n_21) (some (.mk_uN n_22)))


inductive Functype_sub : functype → functype → Prop where
  | mk_Functype_sub (ft : functype) : Functype_sub ft ft


inductive Globaltype_sub : globaltype → globaltype → Prop where
  | mk_Globaltype_sub (gt : globaltype) : Globaltype_sub gt gt


inductive Tabletype_sub : tabletype → tabletype → Prop where
  | mk_Tabletype_sub (lim_1 : limits) (lim_2 : limits) : 
    Limits_sub lim_1 lim_2 →
    wf_limits lim_1 →
    wf_limits lim_2 →
    Tabletype_sub lim_1 lim_2


inductive Memtype_sub : memtype → memtype → Prop where
  | mk_Memtype_sub (lim_1 : limits) (lim_2 : limits) : 
    Limits_sub lim_1 lim_2 →
    wf_limits lim_1 →
    wf_limits lim_2 →
    Memtype_sub lim_1 lim_2


inductive Externtype_sub : externtype → externtype → Prop where
  | func (ft_1 : functype) (ft_2 : functype) : 
    Functype_sub ft_1 ft_2 →
    wf_externtype (externtype.FUNC ft_1) →
    wf_externtype (externtype.FUNC ft_2) →
    Externtype_sub (externtype.FUNC ft_1) (externtype.FUNC ft_2)
  | global (gt_1 : globaltype) (gt_2 : globaltype) : 
    Globaltype_sub gt_1 gt_2 →
    wf_externtype (externtype.GLOBAL gt_1) →
    wf_externtype (externtype.GLOBAL gt_2) →
    Externtype_sub (externtype.GLOBAL gt_1) (externtype.GLOBAL gt_2)
  | table (tt_1 : tabletype) (tt_2 : tabletype) : 
    Tabletype_sub tt_1 tt_2 →
    wf_externtype (externtype.TABLE tt_1) →
    wf_externtype (externtype.TABLE tt_2) →
    Externtype_sub (externtype.TABLE tt_1) (externtype.TABLE tt_2)
  | mem (mt_1 : memtype) (mt_2 : memtype) : 
    Memtype_sub mt_1 mt_2 →
    wf_externtype (externtype.MEM mt_1) →
    wf_externtype (externtype.MEM mt_2) →
    Externtype_sub (externtype.MEM mt_1) (externtype.MEM mt_2)


mutual
inductive Instr_ok : context → instr → functype → Prop where
  | nop (C : context) : 
    wf_context C →
    wf_instr instr.NOP →
    Instr_ok C instr.NOP (functype.mk_functype [] [])
  | unreachable (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    wf_context C →
    wf_instr instr.UNREACHABLE →
    Instr_ok C instr.UNREACHABLE (functype.mk_functype t_1_lst t_2_lst)
  | drop (C : context) (t : valtype) : 
    wf_context C →
    wf_instr instr.DROP →
    Instr_ok C instr.DROP (functype.mk_functype [t] [])
  | select (C : context) (t : valtype) : 
    wf_context C →
    wf_instr instr.SELECT →
    Instr_ok C instr.SELECT (functype.mk_functype [t, t, valtype.I32] [t])
  | block (C : context) (t_opt : Option valtype) (instr_lst : List instr) : 
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t_opt]
      RETURN := none : context
    }) ++ C) instr_lst (functype.mk_functype [] (Option.toList t_opt)) →
    wf_context C →
    wf_instr (instr.BLOCK t_opt instr_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t_opt]
      RETURN := none : context
    }) →
    Instr_ok C (instr.BLOCK t_opt instr_lst) (functype.mk_functype [] (Option.toList t_opt))
  | loop (C : context) (t_opt : Option valtype) (instr_lst : List instr) : 
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [none]
      RETURN := none : context
    }) ++ C) instr_lst (functype.mk_functype [] []) →
    wf_context C →
    wf_instr (instr.LOOP t_opt instr_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [none]
      RETURN := none : context
    }) →
    Instr_ok C (instr.LOOP t_opt instr_lst) (functype.mk_functype [] (Option.toList t_opt))
  | if (C : context) (t_opt : Option valtype) (instr_1_lst : List instr) (instr_2_lst : List instr) : 
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t_opt]
      RETURN := none : context
    }) ++ C) instr_1_lst (functype.mk_functype [] (Option.toList t_opt)) →
    Instrs_ok (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t_opt]
      RETURN := none : context
    }) ++ C) instr_2_lst (functype.mk_functype [] (Option.toList t_opt)) →
    wf_context C →
    wf_instr (instr.IFELSE t_opt instr_1_lst instr_2_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t_opt]
      RETURN := none : context
    }) →
    Instr_ok C (instr.IFELSE t_opt instr_1_lst instr_2_lst) (functype.mk_functype [valtype.I32] (Option.toList t_opt))
  | br (C : context) (l : labelidx) (t_1_lst : List valtype) (t_opt : Option valtype) (t_2_lst : List valtype) : 
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    ((C.LABELS)[proj_uN_0 l]!) == t_opt →
    wf_context C →
    wf_instr (instr.BR l) →
    Instr_ok C (instr.BR l) (functype.mk_functype (t_1_lst ++ (Option.toList t_opt)) t_2_lst)
  | br_if (C : context) (l : labelidx) (t_opt : Option valtype) : 
    (proj_uN_0 l) < (List.length (C.LABELS)) →
    ((C.LABELS)[proj_uN_0 l]!) == t_opt →
    wf_context C →
    wf_instr (instr.BR_IF l) →
    Instr_ok C (instr.BR_IF l) (functype.mk_functype ((Option.toList t_opt) ++ [valtype.I32]) (Option.toList t_opt))
  | br_table (C : context) (l_lst : List labelidx) (l' : labelidx) (t_1_lst : List valtype) (t_opt : Option valtype) (t_2_lst : List valtype) : 
    (proj_uN_0 l') < (List.length (C.LABELS)) →
    t_opt == ((C.LABELS)[proj_uN_0 l']!) →
    (∀ l_elem ∈ l_lst, (proj_uN_0 l_elem) < (List.length (C.LABELS))) →
    (∀ l_elem ∈ l_lst, t_opt == ((C.LABELS)[proj_uN_0 l_elem]!)) →
    wf_context C →
    wf_instr (instr.BR_TABLE l_lst l') →
    Instr_ok C (instr.BR_TABLE l_lst l') (functype.mk_functype (t_1_lst ++ ((Option.toList t_opt) ++ [valtype.I32])) t_2_lst)
  | call (C : context) (x : idx) (t_1_lst : List valtype) (t_2_opt : Option valtype) : 
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) == (functype.mk_functype t_1_lst (Option.toList t_2_opt)) →
    wf_context C →
    wf_instr (instr.CALL x) →
    Instr_ok C (instr.CALL x) (functype.mk_functype t_1_lst (Option.toList t_2_opt))
  | call_indirect (C : context) (x : idx) (t_1_lst : List valtype) (t_2_opt : Option valtype) : 
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    ((C.TYPES)[proj_uN_0 x]!) == (functype.mk_functype t_1_lst (Option.toList t_2_opt)) →
    wf_context C →
    wf_instr (instr.CALL_INDIRECT x) →
    Instr_ok C (instr.CALL_INDIRECT x) (functype.mk_functype (t_1_lst ++ [valtype.I32]) (Option.toList t_2_opt))
  | return (C : context) (t_1_lst : List valtype) (t_opt : Option valtype) (t_2_lst : List valtype) : 
    (C.RETURN) == (some t_opt) →
    wf_context C →
    wf_instr instr.RETURN →
    Instr_ok C instr.RETURN (functype.mk_functype (t_1_lst ++ (Option.toList t_opt)) t_2_lst)
  | const (C : context) (t : valtype) (c_t : val_) : 
    wf_context C →
    wf_instr (instr.CONST t c_t) →
    Instr_ok C (instr.CONST t c_t) (functype.mk_functype [] [t])
  | unop (C : context) (t : valtype) (unop_t : unop_) : 
    wf_context C →
    wf_instr (instr.UNOP t unop_t) →
    Instr_ok C (instr.UNOP t unop_t) (functype.mk_functype [t] [t])
  | binop (C : context) (t : valtype) (binop_t : binop_) : 
    wf_context C →
    wf_instr (instr.BINOP t binop_t) →
    Instr_ok C (instr.BINOP t binop_t) (functype.mk_functype [t, t] [t])
  | testop (C : context) (t : valtype) (testop_t : testop_) : 
    wf_context C →
    wf_instr (instr.TESTOP t testop_t) →
    Instr_ok C (instr.TESTOP t testop_t) (functype.mk_functype [t] [valtype.I32])
  | relop (C : context) (t : valtype) (relop_t : relop_) : 
    wf_context C →
    wf_instr (instr.RELOP t relop_t) →
    Instr_ok C (instr.RELOP t relop_t) (functype.mk_functype [t, t] [valtype.I32])
  | cvtop_reinterpret (C : context) (nt_1 : valtype) (nt_2 : valtype) : 
    (size nt_1) == (size nt_2) →
    wf_context C →
    wf_instr (instr.CVTOP nt_1 nt_2 cvtop.REINTERPRET) →
    Instr_ok C (instr.CVTOP nt_1 nt_2 cvtop.REINTERPRET) (functype.mk_functype [nt_2] [nt_1])
  | cvtop_convert (C : context) (nt_1 : valtype) (nt_2 : valtype) (v_cvtop : cvtop) : 
    wf_context C →
    wf_instr (instr.CVTOP nt_1 nt_2 v_cvtop) →
    Instr_ok C (instr.CVTOP nt_1 nt_2 v_cvtop) (functype.mk_functype [nt_2] [nt_1])
  | local_get (C : context) (x : idx) (t : valtype) : 
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) == t →
    wf_context C →
    wf_instr (instr.LOCAL_GET x) →
    Instr_ok C (instr.LOCAL_GET x) (functype.mk_functype [] [t])
  | local_set (C : context) (x : idx) (t : valtype) : 
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) == t →
    wf_context C →
    wf_instr (instr.LOCAL_SET x) →
    Instr_ok C (instr.LOCAL_SET x) (functype.mk_functype [t] [])
  | local_tee (C : context) (x : idx) (t : valtype) : 
    (proj_uN_0 x) < (List.length (C.LOCALS)) →
    ((C.LOCALS)[proj_uN_0 x]!) == t →
    wf_context C →
    wf_instr (instr.LOCAL_TEE x) →
    Instr_ok C (instr.LOCAL_TEE x) (functype.mk_functype [t] [t])
  | global_get (C : context) (x : idx) (t : valtype) (v_mut : «mut») : 
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) == (globaltype.mk_globaltype v_mut t) →
    wf_context C →
    wf_instr (instr.GLOBAL_GET x) →
    Instr_ok C (instr.GLOBAL_GET x) (functype.mk_functype [] [t])
  | global_set (C : context) (x : idx) (t : valtype) : 
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) == (globaltype.mk_globaltype (some r_MUT.MUT) t) →
    wf_context C →
    wf_instr (instr.GLOBAL_SET x) →
    Instr_ok C (instr.GLOBAL_SET x) (functype.mk_functype [t] [])
  | memory_size (C : context) (mt : memtype) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == mt →
    wf_context C →
    wf_limits mt →
    wf_instr instr.MEMORY_SIZE →
    Instr_ok C instr.MEMORY_SIZE (functype.mk_functype [] [valtype.I32])
  | memory_grow (C : context) (mt : memtype) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == mt →
    wf_context C →
    wf_limits mt →
    wf_instr instr.MEMORY_GROW →
    Instr_ok C instr.MEMORY_GROW (functype.mk_functype [valtype.I32] [valtype.I32])
  | load_val (C : context) (t : valtype) (v_memarg : memarg) (mt : memtype) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((size t) : Rat) / (8 : Rat)) →
    wf_context C →
    wf_limits mt →
    wf_instr (instr.LOAD t none v_memarg) →
    Instr_ok C (instr.LOAD t none v_memarg) (functype.mk_functype [valtype.I32] [t])
  | load_pack (C : context) (v_Inn : Inn) (v_M : M) (v_sx : sx) (v_memarg : memarg) (mt : memtype) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_M : Rat) / (8 : Rat)) →
    wf_context C →
    wf_limits mt →
    wf_instr (instr.LOAD (valtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) v_memarg) →
    Instr_ok C (instr.LOAD (valtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_M) v_sx))) v_memarg) (functype.mk_functype [valtype.I32] [valtype_Inn v_Inn])
  | store_val (C : context) (t : valtype) (v_memarg : memarg) (mt : memtype) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ (((size t) : Rat) / (8 : Rat)) →
    wf_context C →
    wf_limits mt →
    wf_instr (instr.STORE t none v_memarg) →
    Instr_ok C (instr.STORE t none v_memarg) (functype.mk_functype [valtype.I32, t] [])
  | store_pack (C : context) (v_Inn : Inn) (v_M : M) (v_memarg : memarg) (mt : memtype) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == mt →
    ((2 ^ (proj_uN_0 (v_memarg.ALIGN))) : Rat) ≤ ((v_M : Rat) / (8 : Rat)) →
    wf_context C →
    wf_limits mt →
    wf_instr (instr.STORE (valtype_Inn v_Inn) (some (sz.mk_sz v_M)) v_memarg) →
    Instr_ok C (instr.STORE (valtype_Inn v_Inn) (some (sz.mk_sz v_M)) v_memarg) (functype.mk_functype [valtype.I32, valtype_Inn v_Inn] [])

inductive Instrs_ok : context → List instr → functype → Prop where
  | empty (C : context) : 
    wf_context C →
    Instrs_ok C [] (functype.mk_functype [] [])
  | seq (C : context) (instr_1 : instr) (instr_2_lst : List instr) (t_1_lst : List valtype) (t_3_lst : List valtype) (t_2_lst : List valtype) : 
    Instr_ok C instr_1 (functype.mk_functype t_1_lst t_2_lst) →
    Instrs_ok C instr_2_lst (functype.mk_functype t_2_lst t_3_lst) →
    wf_context C →
    wf_instr instr_1 →
    (∀ instr_2_elem ∈ instr_2_lst, wf_instr instr_2_elem) →
    Instrs_ok C ([instr_1] ++ instr_2_lst) (functype.mk_functype t_1_lst t_3_lst)
  | frame (C : context) (instr_lst : List instr) (t_lst : List valtype) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    Instrs_ok C instr_lst (functype.mk_functype t_1_lst t_2_lst) →
    wf_context C →
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    Instrs_ok C instr_lst (functype.mk_functype (t_lst ++ t_1_lst) (t_lst ++ t_2_lst))


end

inductive Expr_ok : context → expr → resulttype → Prop where
  | mk_Expr_ok (C : context) (instr_lst : List instr) (t_opt : Option valtype) : 
    Instrs_ok C instr_lst (functype.mk_functype [] (Option.toList t_opt)) →
    wf_context C →
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    Expr_ok C instr_lst t_opt


inductive Instr_const : context → instr → Prop where
  | const (C : context) (t : valtype) (c : val_) : 
    wf_context C →
    wf_instr (instr.CONST t c) →
    Instr_const C (instr.CONST t c)
  | global_get (C : context) (x : idx) (t : valtype) : 
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) == (globaltype.mk_globaltype none t) →
    wf_context C →
    wf_instr (instr.GLOBAL_GET x) →
    Instr_const C (instr.GLOBAL_GET x)


inductive Expr_const : context → expr → Prop where
  | mk_Expr_const (C : context) (instr_lst : List instr) : 
    (∀ v_instr_elem ∈ instr_lst, Instr_const C v_instr_elem) →
    wf_context C →
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    Expr_const C instr_lst


inductive Expr_ok_const : context → expr → Option valtype → Prop where
  | mk_Expr_ok_const (C : context) (v_expr : expr) (t_opt : Option valtype) : 
    Expr_ok C v_expr t_opt →
    Expr_const C v_expr →
    wf_context C →
    (∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem) →
    Expr_ok_const C v_expr t_opt


inductive Type_ok : type → functype → Prop where
  | mk_Type_ok (ft : functype) : 
    Functype_ok ft →
    Type_ok (type.TYPE ft) ft


inductive Func_ok : context → func → functype → Prop where
  | mk_Func_ok (C : context) (x : idx) (t_lst : List valtype) (v_expr : expr) (t_1_lst : List valtype) (t_2_opt : Option valtype) : 
    (proj_uN_0 x) < (List.length (C.TYPES)) →
    ((C.TYPES)[proj_uN_0 x]!) == (functype.mk_functype t_1_lst (Option.toList t_2_opt)) →
    Expr_ok (C ++ ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := t_1_lst ++ t_lst
      LABELS := [t_2_opt]
      RETURN := some t_2_opt : context
    })) v_expr t_2_opt →
    wf_context C →
    wf_func (func.FUNC x (t_lst |>.map (fun t_elem => local.LOCAL t_elem)) v_expr) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := t_1_lst ++ t_lst
      LABELS := [t_2_opt]
      RETURN := some t_2_opt : context
    }) →
    Func_ok C (func.FUNC x (t_lst |>.map (fun t_elem => local.LOCAL t_elem)) v_expr) (functype.mk_functype t_1_lst (Option.toList t_2_opt))


inductive Global_ok : context → global → globaltype → Prop where
  | mk_Global_ok (C : context) (gt : globaltype) (v_expr : expr) (v_mut : «mut») (t : valtype) : 
    Globaltype_ok gt →
    gt == (globaltype.mk_globaltype v_mut t) →
    Expr_ok_const C v_expr (some t) →
    wf_context C →
    wf_global (global.GLOBAL gt v_expr) →
    Global_ok C (global.GLOBAL gt v_expr) gt


inductive Table_ok : context → table → tabletype → Prop where
  | mk_Table_ok (C : context) (tt : tabletype) : 
    Tabletype_ok tt →
    wf_context C →
    wf_table (table.TABLE tt) →
    Table_ok C (table.TABLE tt) tt


inductive Mem_ok : context → mem → memtype → Prop where
  | mk_Mem_ok (C : context) (mt : memtype) : 
    Memtype_ok mt →
    wf_context C →
    wf_mem (mem.MEMORY mt) →
    Mem_ok C (mem.MEMORY mt) mt


inductive Elem_ok : context → elem → Prop where
  | mk_Elem_ok (C : context) (v_expr : expr) (x_lst : List idx) (lim : limits) (ft_lst : List functype) : 
    0 < (List.length (C.TABLES)) →
    ((C.TABLES)[0]!) == lim →
    Expr_ok_const C v_expr (some valtype.I32) →
    (List.length ft_lst) == (List.length x_lst) →
    (∀ x_elem ∈ x_lst, (proj_uN_0 x_elem) < (List.length (C.FUNCS))) →
    (∀ __iter_tuple ∈ ft_lst |>.zip x_lst, ((C.FUNCS)[proj_uN_0 (__iter_tuple.2)]!) == (__iter_tuple.1)) →
    wf_context C →
    wf_limits lim →
    wf_elem (elem.ELEM v_expr x_lst) →
    Elem_ok C (elem.ELEM v_expr x_lst)


inductive Data_ok : context → data → Prop where
  | mk_Data_ok (C : context) (v_expr : expr) (b_lst : List byte) (lim : limits) : 
    0 < (List.length (C.MEMS)) →
    ((C.MEMS)[0]!) == lim →
    Expr_ok_const C v_expr (some valtype.I32) →
    wf_context C →
    wf_limits lim →
    wf_data (data.DATA v_expr b_lst) →
    Data_ok C (data.DATA v_expr b_lst)


inductive Start_ok : context → start → Prop where
  | mk_Start_ok (C : context) (x : idx) : 
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) == (functype.mk_functype [] []) →
    wf_context C →
    wf_start (start.START x) →
    Start_ok C (start.START x)


inductive Import_ok : context → «import» → externtype → Prop where
  | mk_Import_ok (C : context) (name_1 : name) (name_2 : name) (xt : externtype) : 
    Externtype_ok xt →
    wf_context C →
    wf_import (import.IMPORT name_1 name_2 xt) →
    Import_ok C (import.IMPORT name_1 name_2 xt) xt


inductive Externidx_ok : context → externidx → externtype → Prop where
  | func (C : context) (x : idx) (ft : functype) : 
    (proj_uN_0 x) < (List.length (C.FUNCS)) →
    ((C.FUNCS)[proj_uN_0 x]!) == ft →
    wf_context C →
    wf_externidx (externidx.FUNC x) →
    wf_externtype (externtype.FUNC ft) →
    Externidx_ok C (externidx.FUNC x) (externtype.FUNC ft)
  | global (C : context) (x : idx) (gt : globaltype) : 
    (proj_uN_0 x) < (List.length (C.GLOBALS)) →
    ((C.GLOBALS)[proj_uN_0 x]!) == gt →
    wf_context C →
    wf_externidx (externidx.GLOBAL x) →
    wf_externtype (externtype.GLOBAL gt) →
    Externidx_ok C (externidx.GLOBAL x) (externtype.GLOBAL gt)
  | table (C : context) (x : idx) (tt : tabletype) : 
    (proj_uN_0 x) < (List.length (C.TABLES)) →
    ((C.TABLES)[proj_uN_0 x]!) == tt →
    wf_context C →
    wf_externidx (externidx.TABLE x) →
    wf_externtype (externtype.TABLE tt) →
    Externidx_ok C (externidx.TABLE x) (externtype.TABLE tt)
  | mem (C : context) (x : idx) (mt : memtype) : 
    (proj_uN_0 x) < (List.length (C.MEMS)) →
    ((C.MEMS)[proj_uN_0 x]!) == mt →
    wf_context C →
    wf_externidx (externidx.MEM x) →
    wf_externtype (externtype.MEM mt) →
    Externidx_ok C (externidx.MEM x) (externtype.MEM mt)


inductive Export_ok : context → «export» → externtype → Prop where
  | mk_Export_ok (C : context) (v_name : name) (v_externidx : externidx) (xt : externtype) : 
    Externidx_ok C v_externidx xt →
    wf_context C →
    wf_externtype xt →
    wf_export (export.EXPORT v_name v_externidx) →
    Export_ok C (export.EXPORT v_name v_externidx) xt


inductive Module_ok : module → Prop where
  | mk_Module_ok (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») (ft'_lst : List functype) (ixt_lst : List externtype) (C' : context) (gt_lst : List globaltype) (C : context) (ft_lst : List functype) (tt_lst : List tabletype) (mt_lst : List memtype) (xt_lst : List externtype) (ift_lst : List functype) (igt_lst : List globaltype) (itt_lst : List tabletype) (imt_lst : List memtype) (var_3 : List memtype) (var_2 : List tabletype) (var_1 : List globaltype) (var_0 : List functype) : 
    fun_memsxt ixt_lst var_3 →
    fun_tablesxt ixt_lst var_2 →
    fun_globalsxt ixt_lst var_1 →
    fun_funcsxt ixt_lst var_0 →
    (List.length ft'_lst) == (List.length type_lst) →
    (∀ __iter_tuple ∈ ft'_lst |>.zip type_lst, Type_ok (__iter_tuple.2) (__iter_tuple.1)) →
    (List.length import_lst) == (List.length ixt_lst) →
    (∀ __iter_tuple ∈ import_lst |>.zip ixt_lst, Import_ok ({
      TYPES := ft'_lst
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length global_lst) == (List.length gt_lst) →
    (∀ __iter_tuple ∈ global_lst |>.zip gt_lst, Global_ok C' (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length ft_lst) == (List.length func_lst) →
    (∀ __iter_tuple ∈ ft_lst |>.zip func_lst, Func_ok C (__iter_tuple.2) (__iter_tuple.1)) →
    (List.length table_lst) == (List.length tt_lst) →
    (∀ __iter_tuple ∈ table_lst |>.zip tt_lst, Table_ok C (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length mem_lst) == (List.length mt_lst) →
    (∀ __iter_tuple ∈ mem_lst |>.zip mt_lst, Mem_ok C (__iter_tuple.1) (__iter_tuple.2)) →
    (∀ v_elem_elem ∈ elem_lst, Elem_ok C v_elem_elem) →
    (∀ v_data_elem ∈ data_lst, Data_ok C v_data_elem) →
    (∀ v_start_elem ∈ Option.toList start_opt, Start_ok C v_start_elem) →
    (List.length export_lst) == (List.length xt_lst) →
    (∀ __iter_tuple ∈ export_lst |>.zip xt_lst, Export_ok C (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length tt_lst) ≤ 1 →
    (List.length mt_lst) ≤ 1 →
    C == ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst ++ gt_lst
      TABLES := itt_lst ++ tt_lst
      MEMS := imt_lst ++ mt_lst
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    C' == ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    ift_lst == var_0 →
    igt_lst == var_1 →
    itt_lst == var_2 →
    imt_lst == var_3 →
    (∀ ixt_elem ∈ ixt_lst, wf_externtype ixt_elem) →
    wf_context C' →
    wf_context C →
    (∀ xt_elem ∈ xt_lst, wf_externtype xt_elem) →
    (∀ iter_elem ∈ var_2, wf_limits iter_elem) →
    (∀ iter_elem ∈ var_3, wf_limits iter_elem) →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) →
    wf_context ({
      TYPES := ft'_lst
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    wf_context ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst ++ gt_lst
      TABLES := itt_lst ++ tt_lst
      MEMS := imt_lst ++ mt_lst
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    wf_context ({
      TYPES := ft'_lst
      FUNCS := ift_lst ++ ft_lst
      GLOBALS := igt_lst
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    Module_ok (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)


inductive Step_pure : List admininstr → List admininstr → Prop where
  | unreachable : 
    wf_admininstr admininstr.UNREACHABLE →
    wf_admininstr admininstr.TRAP →
    Step_pure [admininstr.UNREACHABLE] [admininstr.TRAP]
  | nop : 
    wf_admininstr admininstr.NOP →
    Step_pure [admininstr.NOP] []
  | drop (v_val : val) : 
    wf_val v_val →
    wf_admininstr admininstr.DROP →
    Step_pure [admininstr_val v_val, admininstr.DROP] []
  | select_true (val_1 : val) (val_2 : val) (c : val_) : 
    (proj_val__0 c) != none →
    (proj_uN_0 (Option.get! (proj_val__0 c))) != 0 →
    wf_val val_1 →
    wf_val val_2 →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    wf_admininstr admininstr.SELECT →
    Step_pure [admininstr_val val_1, admininstr_val val_2, admininstr.CONST valtype.I32 c, admininstr.SELECT] [admininstr_val val_1]
  | select_false (val_1 : val) (val_2 : val) (c : val_) : 
    (proj_val__0 c) != none →
    (proj_uN_0 (Option.get! (proj_val__0 c))) == 0 →
    wf_val val_1 →
    wf_val val_2 →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    wf_admininstr admininstr.SELECT →
    Step_pure [admininstr_val val_1, admininstr_val val_2, admininstr.CONST valtype.I32 c, admininstr.SELECT] [admininstr_val val_2]
  | if_true (c : val_) (t_opt : Option valtype) (instr_1_lst : List instr) (instr_2_lst : List instr) : 
    (proj_val__0 c) != none →
    (proj_uN_0 (Option.get! (proj_val__0 c))) != 0 →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    wf_admininstr (admininstr.IFELSE t_opt instr_1_lst instr_2_lst) →
    wf_admininstr (admininstr.BLOCK t_opt instr_1_lst) →
    Step_pure [admininstr.CONST valtype.I32 c, admininstr.IFELSE t_opt instr_1_lst instr_2_lst] [admininstr.BLOCK t_opt instr_1_lst]
  | if_false (c : val_) (t_opt : Option valtype) (instr_1_lst : List instr) (instr_2_lst : List instr) : 
    (proj_val__0 c) != none →
    (proj_uN_0 (Option.get! (proj_val__0 c))) == 0 →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    wf_admininstr (admininstr.IFELSE t_opt instr_1_lst instr_2_lst) →
    wf_admininstr (admininstr.BLOCK t_opt instr_2_lst) →
    Step_pure [admininstr.CONST valtype.I32 c, admininstr.IFELSE t_opt instr_1_lst instr_2_lst] [admininstr.BLOCK t_opt instr_2_lst]
  | label_vals (v_n : n) (instr_lst : List instr) (val_lst : List val) : 
    wf_admininstr (admininstr.LABEL_ v_n instr_lst (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) →
    Step_pure [admininstr.LABEL_ v_n instr_lst (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))] (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))
  | br_zero (v_n : n) (instr'_lst : List instr) (val'_lst : List val) (val_lst : List val) (instr_lst : List instr) : 
    wf_admininstr (admininstr.LABEL_ v_n instr'_lst ((((val'_lst |>.map (fun val'_elem => admininstr_val val'_elem)) ++ (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) ++ [admininstr.BR (.mk_uN 0)]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))) →
    v_n == (List.length val_lst) →
    Step_pure [admininstr.LABEL_ v_n instr'_lst ((((val'_lst |>.map (fun val'_elem => admininstr_val val'_elem)) ++ (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) ++ [admininstr.BR (.mk_uN 0)]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))] ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ (instr'_lst |>.map (fun instr'_elem => admininstr_instr instr'_elem)))
  | br_succ (v_n : n) (instr'_lst : List instr) (val_lst : List val) (l : labelidx) (instr_lst : List instr) : 
    wf_admininstr (admininstr.LABEL_ v_n instr'_lst (((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.BR (.mk_uN ((proj_uN_0 l) + 1))]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))) →
    wf_admininstr (admininstr.BR l) →
    Step_pure [admininstr.LABEL_ v_n instr'_lst (((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.BR (.mk_uN ((proj_uN_0 l) + 1))]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))] ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.BR l])
  | br_if_true (c : val_) (l : labelidx) : 
    (proj_val__0 c) != none →
    (proj_uN_0 (Option.get! (proj_val__0 c))) != 0 →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    wf_admininstr (admininstr.BR_IF l) →
    wf_admininstr (admininstr.BR l) →
    Step_pure [admininstr.CONST valtype.I32 c, admininstr.BR_IF l] [admininstr.BR l]
  | br_if_false (c : val_) (l : labelidx) : 
    (proj_val__0 c) != none →
    (proj_uN_0 (Option.get! (proj_val__0 c))) == 0 →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    wf_admininstr (admininstr.BR_IF l) →
    Step_pure [admininstr.CONST valtype.I32 c, admininstr.BR_IF l] []
  | br_table_lt (i : val_) (l_lst : List labelidx) (l' : labelidx) : 
    (proj_uN_0 (Option.get! (proj_val__0 i))) < (List.length l_lst) →
    (proj_val__0 i) != none →
    wf_admininstr (admininstr.CONST valtype.I32 i) →
    wf_admininstr (admininstr.BR_TABLE l_lst l') →
    wf_admininstr (admininstr.BR ((l_lst)[proj_uN_0 (Option.get! (proj_val__0 i))]!)) →
    Step_pure [admininstr.CONST valtype.I32 i, admininstr.BR_TABLE l_lst l'] [admininstr.BR ((l_lst)[proj_uN_0 (Option.get! (proj_val__0 i))]!)]
  | br_table_ge (i : val_) (l_lst : List labelidx) (l' : labelidx) : 
    (proj_val__0 i) != none →
    (proj_uN_0 (Option.get! (proj_val__0 i))) ≥ (List.length l_lst) →
    wf_admininstr (admininstr.CONST valtype.I32 i) →
    wf_admininstr (admininstr.BR_TABLE l_lst l') →
    wf_admininstr (admininstr.BR l') →
    Step_pure [admininstr.CONST valtype.I32 i, admininstr.BR_TABLE l_lst l'] [admininstr.BR l']
  | frame_vals (v_n : n) (f : frame) (val_lst : List val) : 
    wf_admininstr (admininstr.FRAME_ v_n f (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) →
    v_n == (List.length val_lst) →
    Step_pure [admininstr.FRAME_ v_n f (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))] (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))
  | return_frame (v_n : n) (f : frame) (val'_lst : List val) (val_lst : List val) (instr_lst : List instr) : 
    wf_admininstr (admininstr.FRAME_ v_n f ((((val'_lst |>.map (fun val'_elem => admininstr_val val'_elem)) ++ (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) ++ [admininstr.RETURN]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))) →
    v_n == (List.length val_lst) →
    Step_pure [admininstr.FRAME_ v_n f ((((val'_lst |>.map (fun val'_elem => admininstr_val val'_elem)) ++ (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) ++ [admininstr.RETURN]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))] (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))
  | return_label (v_n : n) (instr'_lst : List instr) (val_lst : List val) (instr_lst : List instr) : 
    wf_admininstr (admininstr.LABEL_ v_n instr'_lst (((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.RETURN]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))) →
    wf_admininstr admininstr.RETURN →
    Step_pure [admininstr.LABEL_ v_n instr'_lst (((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.RETURN]) ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))] ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.RETURN])
  | trap_vals (val_lst : List val) (instr_lst : List instr) : 
    (val_lst != []) || (instr_lst != []) →
    (∀ v_val_elem ∈ val_lst, wf_val v_val_elem) →
    (∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem) →
    wf_admininstr admininstr.TRAP →
    Step_pure ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ ([admininstr.TRAP] ++ (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem)))) [admininstr.TRAP]
  | trap_label (v_n : n) (instr'_lst : List instr) : 
    wf_admininstr (admininstr.LABEL_ v_n instr'_lst [admininstr.TRAP]) →
    wf_admininstr admininstr.TRAP →
    Step_pure [admininstr.LABEL_ v_n instr'_lst [admininstr.TRAP]] [admininstr.TRAP]
  | trap_frame (v_n : n) (f : frame) : 
    wf_admininstr (admininstr.FRAME_ v_n f [admininstr.TRAP]) →
    wf_admininstr admininstr.TRAP →
    Step_pure [admininstr.FRAME_ v_n f [admininstr.TRAP]] [admininstr.TRAP]
  | unop_val (t : valtype) (c_1 : val_) (unop : unop_) (c : val_) : 
    (List.length (Option.get! (fun_unop_ t unop c_1))) > 0 →
    (fun_unop_ t unop c_1) != none →
    List.contains (Option.get! (fun_unop_ t unop c_1)) c →
    (∀ iter_elem ∈ Option.get! (fun_unop_ t unop c_1), wf_val_ t iter_elem) →
    wf_admininstr (admininstr.CONST t c_1) →
    wf_admininstr (admininstr.UNOP t unop) →
    wf_admininstr (admininstr.CONST t c) →
    Step_pure [admininstr.CONST t c_1, admininstr.UNOP t unop] [admininstr.CONST t c]
  | unop_trap (t : valtype) (c_1 : val_) (unop : unop_) : 
    (fun_unop_ t unop c_1) != none →
    (Option.get! (fun_unop_ t unop c_1)) == [] →
    (∀ iter_elem ∈ Option.get! (fun_unop_ t unop c_1), wf_val_ t iter_elem) →
    wf_admininstr (admininstr.CONST t c_1) →
    wf_admininstr (admininstr.UNOP t unop) →
    wf_admininstr admininstr.TRAP →
    Step_pure [admininstr.CONST t c_1, admininstr.UNOP t unop] [admininstr.TRAP]
  | binop_val (t : valtype) (c_1 : val_) (c_2 : val_) (binop : binop_) (c : val_) (var_0 : List val_) : 
    fun_binop_ t binop c_1 c_2 var_0 →
    (List.length var_0) > 0 →
    List.contains var_0 c →
    (∀ iter_elem ∈ var_0, wf_val_ t iter_elem) →
    wf_admininstr (admininstr.CONST t c_1) →
    wf_admininstr (admininstr.CONST t c_2) →
    wf_admininstr (admininstr.BINOP t binop) →
    wf_admininstr (admininstr.CONST t c) →
    Step_pure [admininstr.CONST t c_1, admininstr.CONST t c_2, admininstr.BINOP t binop] [admininstr.CONST t c]
  | binop_trap (t : valtype) (c_1 : val_) (c_2 : val_) (binop : binop_) (var_0 : List val_) : 
    fun_binop_ t binop c_1 c_2 var_0 →
    var_0 == [] →
    (∀ iter_elem ∈ var_0, wf_val_ t iter_elem) →
    wf_admininstr (admininstr.CONST t c_1) →
    wf_admininstr (admininstr.CONST t c_2) →
    wf_admininstr (admininstr.BINOP t binop) →
    wf_admininstr admininstr.TRAP →
    Step_pure [admininstr.CONST t c_1, admininstr.CONST t c_2, admininstr.BINOP t binop] [admininstr.TRAP]
  | testop (t : valtype) (c_1 : val_) (testop : testop_) (c : val_) : 
    (fun_testop_ t testop c_1) != none →
    c == (Option.get! (fun_testop_ t testop c_1)) →
    wf_val_ valtype.I32 (Option.get! (fun_testop_ t testop c_1)) →
    wf_admininstr (admininstr.CONST t c_1) →
    wf_admininstr (admininstr.TESTOP t testop) →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    Step_pure [admininstr.CONST t c_1, admininstr.TESTOP t testop] [admininstr.CONST valtype.I32 c]
  | relop (t : valtype) (c_1 : val_) (c_2 : val_) (relop : relop_) (c : val_) (var_0 : val_) : 
    fun_relop_ t relop c_1 c_2 var_0 →
    c == var_0 →
    wf_val_ valtype.I32 var_0 →
    wf_admininstr (admininstr.CONST t c_1) →
    wf_admininstr (admininstr.CONST t c_2) →
    wf_admininstr (admininstr.RELOP t relop) →
    wf_admininstr (admininstr.CONST valtype.I32 c) →
    Step_pure [admininstr.CONST t c_1, admininstr.CONST t c_2, admininstr.RELOP t relop] [admininstr.CONST valtype.I32 c]
  | cvtop_val (t_1 : valtype) (c_1 : val_) (t_2 : valtype) (v_cvtop : cvtop) (c : val_) (var_0 : List val_) : 
    fun_cvtop__ t_1 t_2 v_cvtop c_1 var_0 →
    (List.length var_0) > 0 →
    List.contains var_0 c →
    (∀ iter_elem ∈ var_0, wf_val_ t_2 iter_elem) →
    wf_admininstr (admininstr.CONST t_1 c_1) →
    wf_admininstr (admininstr.CVTOP t_2 t_1 v_cvtop) →
    wf_admininstr (admininstr.CONST t_2 c) →
    Step_pure [admininstr.CONST t_1 c_1, admininstr.CVTOP t_2 t_1 v_cvtop] [admininstr.CONST t_2 c]
  | cvtop_trap (t_1 : valtype) (c_1 : val_) (t_2 : valtype) (v_cvtop : cvtop) (var_0 : List val_) : 
    fun_cvtop__ t_1 t_2 v_cvtop c_1 var_0 →
    var_0 == [] →
    (∀ iter_elem ∈ var_0, wf_val_ t_2 iter_elem) →
    wf_admininstr (admininstr.CONST t_1 c_1) →
    wf_admininstr (admininstr.CVTOP t_2 t_1 v_cvtop) →
    wf_admininstr admininstr.TRAP →
    Step_pure [admininstr.CONST t_1 c_1, admininstr.CVTOP t_2 t_1 v_cvtop] [admininstr.TRAP]
  | local_tee (v_val : val) (x : idx) : 
    wf_val v_val →
    wf_admininstr (admininstr.LOCAL_TEE x) →
    wf_admininstr (admininstr.LOCAL_SET x) →
    Step_pure [admininstr_val v_val, admininstr.LOCAL_TEE x] [admininstr_val v_val, admininstr_val v_val, admininstr.LOCAL_SET x]


inductive Step_read_before_call_indirect_trap : config → Prop where
  | call_indirect_call_0 (z : state) (i : val_) (x : idx) (a : addr) : 
    (proj_uN_0 (Option.get! (proj_val__0 i))) < (List.length ((fun_table z (.mk_uN 0)).REFS)) →
    (proj_val__0 i) != none →
    (((fun_table z (.mk_uN 0)).REFS)[proj_uN_0 (Option.get! (proj_val__0 i))]!) == (some a) →
    a < (List.length (fun_funcinst z)) →
    (fun_type z x) == (((fun_funcinst z)[a]!).TYPE) →
    wf_tableinst (fun_table z (.mk_uN 0)) →
    (∀ iter_elem ∈ fun_funcinst z, wf_funcinst iter_elem) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x]) →
    wf_admininstr (admininstr.CALL_ADDR a) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read_before_call_indirect_trap (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x])


inductive Step_read : config → List admininstr → Prop where
  | block (z : state) (t_opt : Option valtype) (instr_lst : List instr) (v_n : n) : 
    ((t_opt == none) && (v_n == 0)) || ((t_opt != none) && (v_n == 1)) →
    wf_config (config.mk_config z [admininstr.BLOCK t_opt instr_lst]) →
    wf_admininstr (admininstr.LABEL_ v_n [] (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))) →
    Step_read (config.mk_config z [admininstr.BLOCK t_opt instr_lst]) [admininstr.LABEL_ v_n [] (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))]
  | loop (z : state) (t_opt : Option valtype) (instr_lst : List instr) : 
    wf_config (config.mk_config z [admininstr.LOOP t_opt instr_lst]) →
    wf_admininstr (admininstr.LABEL_ 0 [instr.LOOP t_opt instr_lst] (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))) →
    Step_read (config.mk_config z [admininstr.LOOP t_opt instr_lst]) [admininstr.LABEL_ 0 [instr.LOOP t_opt instr_lst] (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))]
  | call (z : state) (x : idx) : 
    (proj_uN_0 x) < (List.length (fun_funcaddr z)) →
    wf_config (config.mk_config z [admininstr.CALL x]) →
    wf_admininstr (admininstr.CALL_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)) →
    Step_read (config.mk_config z [admininstr.CALL x]) [admininstr.CALL_ADDR ((fun_funcaddr z)[proj_uN_0 x]!)]
  | call_indirect_call (z : state) (i : val_) (x : idx) (a : addr) : 
    (proj_uN_0 (Option.get! (proj_val__0 i))) < (List.length ((fun_table z (.mk_uN 0)).REFS)) →
    (proj_val__0 i) != none →
    (((fun_table z (.mk_uN 0)).REFS)[proj_uN_0 (Option.get! (proj_val__0 i))]!) == (some a) →
    a < (List.length (fun_funcinst z)) →
    (fun_type z x) == (((fun_funcinst z)[a]!).TYPE) →
    wf_tableinst (fun_table z (.mk_uN 0)) →
    (∀ iter_elem ∈ fun_funcinst z, wf_funcinst iter_elem) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x]) →
    wf_admininstr (admininstr.CALL_ADDR a) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x]) [admininstr.CALL_ADDR a]
  | call_indirect_trap (z : state) (i : val_) (x : idx) : 
    ¬ Step_read_before_call_indirect_trap (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x]) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x]) →
    wf_admininstr admininstr.TRAP →
    Step_read (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CALL_INDIRECT x]) [admininstr.TRAP]
  | call_addr (z : state) (k : Nat) (val_lst : List val) (a : addr) (v_n : n) (f : frame) (instr_lst : List instr) (t_1_lst : List valtype) (t_2_lst : List valtype) (mm : moduleinst) (v_func : func) (x : idx) (t_lst : List valtype) : 
    a < (List.length (fun_funcinst z)) →
    ((fun_funcinst z)[a]!) == ({
      TYPE := functype.mk_functype t_1_lst t_2_lst
      MODULE := mm
      CODE := v_func : funcinst
    }) →
    v_func == (func.FUNC x (t_lst |>.map (fun t_elem => local.LOCAL t_elem)) instr_lst) →
    f == ({
      LOCALS := val_lst ++ (t_lst |>.map (fun t_elem => default_ t_elem))
      MODULE := mm : frame
    }) →
    (∀ iter_elem ∈ fun_funcinst z, wf_funcinst iter_elem) →
    wf_config (config.mk_config z ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.CALL_ADDR a])) →
    wf_admininstr (admininstr.FRAME_ v_n f [admininstr.LABEL_ v_n [] (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))]) →
    wf_funcinst ({
      TYPE := functype.mk_functype t_1_lst t_2_lst
      MODULE := mm
      CODE := v_func : funcinst
    }) →
    wf_func (func.FUNC x (t_lst |>.map (fun t_elem => local.LOCAL t_elem)) instr_lst) →
    wf_frame ({
      LOCALS := val_lst ++ (t_lst |>.map (fun t_elem => default_ t_elem))
      MODULE := mm : frame
    }) →
    k == (List.length val_lst) →
    k == (List.length t_1_lst) →
    v_n == (List.length t_2_lst) →
    Step_read (config.mk_config z ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.CALL_ADDR a])) [admininstr.FRAME_ v_n f [admininstr.LABEL_ v_n [] (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))]]
  | local_get (z : state) (x : idx) : 
    wf_val (fun_local z x) →
    wf_config (config.mk_config z [admininstr.LOCAL_GET x]) →
    Step_read (config.mk_config z [admininstr.LOCAL_GET x]) [admininstr_val (fun_local z x)]
  | global_get (z : state) (x : idx) : 
    wf_globalinst (fun_global z x) →
    wf_config (config.mk_config z [admininstr.GLOBAL_GET x]) →
    Step_read (config.mk_config z [admininstr.GLOBAL_GET x]) [admininstr_val ((fun_global z x).VALUE)]
  | load_num_trap (z : state) (i : val_) (t : valtype) (ao : memarg) : 
    (proj_val__0 i) != none →
    (((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((size t) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD t none ao]) →
    wf_admininstr admininstr.TRAP →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD t none ao]) [admininstr.TRAP]
  | load_num_val (z : state) (i : val_) (t : valtype) (ao : memarg) (c : val_) : 
    (proj_val__0 i) != none →
    (bytes_ t c) == (List.take (rat_to_nat (((size t) : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (.mk_uN 0)).BYTES))) →
    (∀ iter_elem ∈ bytes_ t c, wf_byte iter_elem) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD t none ao]) →
    wf_admininstr (admininstr.CONST t c) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD t none ao]) [admininstr.CONST t c]
  | load_pack_trap (z : state) (i : val_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) : 
    (proj_val__0 i) != none →
    (((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD (valtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) →
    wf_admininstr admininstr.TRAP →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD (valtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) [admininstr.TRAP]
  | load_pack_val (z : state) (i : val_) (v_Inn : Inn) (v_n : n) (v_sx : sx) (ao : memarg) (c : iN) : 
    (proj_val__0 i) != none →
    (ibytes_ v_n c) == (List.take (rat_to_nat ((v_n : Rat) / (8 : Rat))) (List.drop ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) ((fun_mem z (.mk_uN 0)).BYTES))) →
    (∀ iter_elem ∈ ibytes_ v_n c, wf_byte iter_elem) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD (valtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) →
    wf_admininstr (admininstr.CONST (valtype_Inn v_Inn) (val_.mk_val__0 v_Inn (extend__ v_n (size (valtype_Inn v_Inn)) v_sx c))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.LOAD (valtype_Inn v_Inn) (some (loadop_.mk_loadop__0 v_Inn (loadop_Inn.mk_loadop_Inn (sz.mk_sz v_n) v_sx))) ao]) [admininstr.CONST (valtype_Inn v_Inn) (val_.mk_val__0 v_Inn (extend__ v_n (size (valtype_Inn v_Inn)) v_sx c))]
  | memory_size (z : state) (v_n : n) : 
    ((v_n * 64) * Ki) == (List.length ((fun_mem z (.mk_uN 0)).BYTES)) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.MEMORY_SIZE]) →
    wf_admininstr (admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN v_n))) →
    wf_uN 32 (uN.mk_uN 0) →
    Step_read (config.mk_config z [admininstr.MEMORY_SIZE]) [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN v_n))]


inductive Step : config → config → Prop where
  | pure (z : state) (admininstr_lst : List admininstr) (admininstr'_lst : List admininstr) : 
    Step_pure admininstr_lst admininstr'_lst →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z admininstr'_lst) →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | read (z : state) (admininstr_lst : List admininstr) (admininstr'_lst : List admininstr) : 
    Step_read (config.mk_config z admininstr_lst) admininstr'_lst →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z admininstr'_lst) →
    Step (config.mk_config z admininstr_lst) (config.mk_config z admininstr'_lst)
  | ctxt_label (z : state) (v_n : n) (instr_0_lst : List instr) (admininstr_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) : 
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    wf_config (config.mk_config z [admininstr.LABEL_ v_n instr_0_lst admininstr_lst]) →
    wf_config (config.mk_config z' [admininstr.LABEL_ v_n instr_0_lst admininstr'_lst]) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Step (config.mk_config z [admininstr.LABEL_ v_n instr_0_lst admininstr_lst]) (config.mk_config z' [admininstr.LABEL_ v_n instr_0_lst admininstr'_lst])
  | ctxt_frame (s : store) (f : frame) (v_n : n) (f' : frame) (admininstr_lst : List admininstr) (s' : store) (f'' : frame) (admininstr'_lst : List admininstr) : 
    Step (config.mk_config (state.mk_state s f') admininstr_lst) (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    wf_config (config.mk_config (state.mk_state s f) [admininstr.FRAME_ v_n f' admininstr_lst]) →
    wf_config (config.mk_config (state.mk_state s' f) [admininstr.FRAME_ v_n f'' admininstr'_lst]) →
    wf_config (config.mk_config (state.mk_state s f') admininstr_lst) →
    wf_config (config.mk_config (state.mk_state s' f'') admininstr'_lst) →
    Step (config.mk_config (state.mk_state s f) [admininstr.FRAME_ v_n f' admininstr_lst]) (config.mk_config (state.mk_state s' f) [admininstr.FRAME_ v_n f'' admininstr'_lst])
  | ctxt_instrs (z : state) (val_lst : List val) (admininstr_lst : List admininstr) (admininstr_1_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) : 
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    (val_lst != []) || (admininstr_1_lst != []) →
    wf_config (config.mk_config z ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ (admininstr_lst ++ admininstr_1_lst))) →
    wf_config (config.mk_config z' ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ (admininstr'_lst ++ admininstr_1_lst))) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Step (config.mk_config z ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ (admininstr_lst ++ admininstr_1_lst))) (config.mk_config z' ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ (admininstr'_lst ++ admininstr_1_lst)))
  | local_set (z : state) (v_val : val) (x : idx) : 
    wf_config (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]) →
    wf_config (config.mk_config (with_local z x v_val) []) →
    Step (config.mk_config z [admininstr_val v_val, admininstr.LOCAL_SET x]) (config.mk_config (with_local z x v_val) [])
  | global_set (z : state) (v_val : val) (x : idx) : 
    wf_config (config.mk_config z [admininstr_val v_val, admininstr.GLOBAL_SET x]) →
    wf_config (config.mk_config (with_global z x v_val) []) →
    Step (config.mk_config z [admininstr_val v_val, admininstr.GLOBAL_SET x]) (config.mk_config (with_global z x v_val) [])
  | store_num_trap (z : state) (i : val_) (t : valtype) (c : val_) (ao : memarg) : 
    (proj_val__0 i) != none →
    (((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat (((size t) : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST t c, admininstr.STORE t none ao]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST t c, admininstr.STORE t none ao]) (config.mk_config z [admininstr.TRAP])
  | store_num_val (z : state) (i : val_) (t : valtype) (c : val_) (ao : memarg) (b_lst : List byte) : 
    (proj_val__0 i) != none →
    b_lst == (bytes_ t c) →
    (∀ iter_elem ∈ bytes_ t c, wf_byte iter_elem) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST t c, admininstr.STORE t none ao]) →
    wf_config (config.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((size t) : Rat) / (8 : Rat))) b_lst) []) →
    Step (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST t c, admininstr.STORE t none ao]) (config.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat (((size t) : Rat) / (8 : Rat))) b_lst) [])
  | store_pack_trap (z : state) (i : val_) (v_Inn : Inn) (c : val_) (v_n : n) (ao : memarg) : 
    (proj_val__0 i) != none →
    (((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) + (rat_to_nat ((v_n : Rat) / (8 : Rat)))) > (List.length ((fun_mem z (.mk_uN 0)).BYTES)) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST (valtype_Inn v_Inn) c, admininstr.STORE (valtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) →
    wf_config (config.mk_config z [admininstr.TRAP]) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST (valtype_Inn v_Inn) c, admininstr.STORE (valtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config z [admininstr.TRAP])
  | store_pack_val (z : state) (i : val_) (v_Inn : Inn) (c : val_) (v_n : n) (ao : memarg) (b_lst : List byte) : 
    (proj_val__0 i) != none →
    (proj_val__0 c) != none →
    b_lst == (ibytes_ v_n (wrap__ (size (valtype_Inn v_Inn)) v_n (Option.get! (proj_val__0 c)))) →
    (∀ iter_elem ∈ ibytes_ v_n (wrap__ (size (valtype_Inn v_Inn)) v_n (Option.get! (proj_val__0 c))), wf_byte iter_elem) →
    wf_uN v_n (wrap__ (size (valtype_Inn v_Inn)) v_n (Option.get! (proj_val__0 c))) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST (valtype_Inn v_Inn) c, admininstr.STORE (valtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) →
    wf_config (config.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_n : Rat) / (8 : Rat))) b_lst) []) →
    Step (config.mk_config z [admininstr.CONST valtype.I32 i, admininstr.CONST (valtype_Inn v_Inn) c, admininstr.STORE (valtype_Inn v_Inn) (some (sz.mk_sz v_n)) ao]) (config.mk_config (with_mem z (.mk_uN 0) ((proj_uN_0 (Option.get! (proj_val__0 i))) + (proj_uN_0 (ao.OFFSET))) (rat_to_nat ((v_n : Rat) / (8 : Rat))) b_lst) [])
  | memory_grow_succeed (z : state) (v_n : n) (mi : meminst) (var_0 : Option meminst) : 
    fun_growmemory (fun_mem z (.mk_uN 0)) v_n var_0 →
    var_0 != none →
    (Option.get! var_0) == mi →
    wf_meminst (Option.get! var_0) →
    wf_meminst (fun_mem z (.mk_uN 0)) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) →
    wf_config (config.mk_config (with_meminst z (.mk_uN 0) mi) [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN (rat_to_nat (((List.length ((fun_mem z (.mk_uN 0)).BYTES)) : Rat) / ((64 * Ki) : Rat)))))]) →
    wf_uN 32 (uN.mk_uN 0) →
    Step (config.mk_config z [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) (config.mk_config (with_meminst z (.mk_uN 0) mi) [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN (rat_to_nat (((List.length ((fun_mem z (.mk_uN 0)).BYTES)) : Rat) / ((64 * Ki) : Rat)))))])
  | memory_grow_fail (z : state) (v_n : n) (var_0 : Nat) : 
    fun_inv_signed_ 32 (- (1 : Int)) var_0 →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) →
    wf_config (config.mk_config z [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN var_0))]) →
    Step (config.mk_config z [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN v_n)), admininstr.MEMORY_GROW]) (config.mk_config z [admininstr.CONST valtype.I32 (val_.mk_val__0 Inn.I32 (uN.mk_uN var_0))])


inductive Steps : config → config → Prop where
  | refl (z : state) (admininstr_lst : List admininstr) : 
    wf_config (config.mk_config z admininstr_lst) →
    Steps (config.mk_config z admininstr_lst) (config.mk_config z admininstr_lst)
  | trans (z : state) (admininstr_lst : List admininstr) (z'' : state) (admininstr''_lst : List admininstr) (z' : state) (admininstr'_lst : List admininstr) : 
    Step (config.mk_config z admininstr_lst) (config.mk_config z' admininstr'_lst) →
    Steps (config.mk_config z' admininstr'_lst) (config.mk_config z'' admininstr''_lst) →
    wf_config (config.mk_config z admininstr_lst) →
    wf_config (config.mk_config z'' admininstr''_lst) →
    wf_config (config.mk_config z' admininstr'_lst) →
    Steps (config.mk_config z admininstr_lst) (config.mk_config z'' admininstr''_lst)


inductive Eval_expr : state → expr → state → List val → Prop where
  | mk_Eval_expr (z : state) (instr_lst : List instr) (z' : state) (val_lst : List val) : 
    Steps (config.mk_config z (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))) (config.mk_config z' (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) →
    wf_config (config.mk_config z (instr_lst |>.map (fun v_instr_elem => admininstr_instr v_instr_elem))) →
    wf_config (config.mk_config z' (val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem))) →
    Eval_expr z instr_lst z' val_lst


inductive fun_funcs : List externaddr → List funcaddr → Prop where
  | fun_funcs_case_0 : fun_funcs [] []
  | fun_funcs_case_1 (fa : Nat) (externaddr'_lst : List externaddr) (var_0 : List funcaddr) : 
    fun_funcs externaddr'_lst var_0 →
    fun_funcs ([externaddr.FUNC fa] ++ externaddr'_lst) ([fa] ++ var_0)
  | fun_funcs_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List funcaddr) : 
    fun_funcs externaddr'_lst var_0 →
    fun_funcs ([v_externaddr] ++ externaddr'_lst) var_0


inductive fun_globals : List externaddr → List globaladdr → Prop where
  | fun_globals_case_0 : fun_globals [] []
  | fun_globals_case_1 (ga : Nat) (externaddr'_lst : List externaddr) (var_0 : List globaladdr) : 
    fun_globals externaddr'_lst var_0 →
    fun_globals ([externaddr.GLOBAL ga] ++ externaddr'_lst) ([ga] ++ var_0)
  | fun_globals_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List globaladdr) : 
    fun_globals externaddr'_lst var_0 →
    fun_globals ([v_externaddr] ++ externaddr'_lst) var_0


inductive fun_tables : List externaddr → List tableaddr → Prop where
  | fun_tables_case_0 : fun_tables [] []
  | fun_tables_case_1 (ta : Nat) (externaddr'_lst : List externaddr) (var_0 : List tableaddr) : 
    fun_tables externaddr'_lst var_0 →
    fun_tables ([externaddr.TABLE ta] ++ externaddr'_lst) ([ta] ++ var_0)
  | fun_tables_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List tableaddr) : 
    fun_tables externaddr'_lst var_0 →
    fun_tables ([v_externaddr] ++ externaddr'_lst) var_0


inductive fun_mems : List externaddr → List memaddr → Prop where
  | fun_mems_case_0 : fun_mems [] []
  | fun_mems_case_1 (ma : Nat) (externaddr'_lst : List externaddr) (var_0 : List memaddr) : 
    fun_mems externaddr'_lst var_0 →
    fun_mems ([externaddr.MEM ma] ++ externaddr'_lst) ([ma] ++ var_0)
  | fun_mems_case_2 (v_externaddr : externaddr) (externaddr'_lst : List externaddr) (var_0 : List memaddr) : 
    fun_mems externaddr'_lst var_0 →
    fun_mems ([v_externaddr] ++ externaddr'_lst) var_0


inductive fun_allocfunc : store → moduleinst → func → store × funcaddr → Prop where
  | fun_allocfunc_case_0 (s : store) (v_moduleinst : moduleinst) (v_func : func) (fi : funcinst) (x : uN) (local_lst : List «local») (v_expr : List instr) : 
    (proj_uN_0 x) < (List.length (v_moduleinst.TYPES)) →
    fi == ({
      TYPE := (v_moduleinst.TYPES)[proj_uN_0 x]!
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) →
    v_func == (func.FUNC x local_lst v_expr) →
    wf_funcinst ({
      TYPE := (v_moduleinst.TYPES)[proj_uN_0 x]!
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) →
    wf_func (func.FUNC x local_lst v_expr) →
    fun_allocfunc s v_moduleinst v_func (({
      s with 
      FUNCS := (s.FUNCS) ++ [fi]
    }, List.length (s.FUNCS)))


inductive allocfunc_is_wf : store → moduleinst → func → store × funcaddr → Prop where
  | allocfunc_is_wf_0 (v_store : store) (v_moduleinst : moduleinst) (v_func : func) (ret_val : store × funcaddr) (var_0 : store × funcaddr) : 
    fun_allocfunc v_store v_moduleinst v_func var_0 →
    wf_store v_store →
    wf_moduleinst v_moduleinst →
    wf_func v_func →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    allocfunc_is_wf v_store v_moduleinst v_func ret_val


inductive fun_allocfuncs : store → moduleinst → List func → store × List funcaddr → Prop where
  | fun_allocfuncs_case_0 (s : store) (v_moduleinst : moduleinst) : fun_allocfuncs s v_moduleinst [] ((s, []))
  | fun_allocfuncs_case_1 (s : store) (v_moduleinst : moduleinst) (v_func : func) (func'_lst : List func) (fa : funcaddr) (s_1 : store) (s_2 : store) (fa'_lst : List funcaddr) (var_1 : store × List funcaddr) (var_0 : store × funcaddr) : 
    fun_allocfuncs s_1 v_moduleinst func'_lst var_1 →
    fun_allocfunc s v_moduleinst v_func var_0 →
    ((s_1, fa)) == var_0 →
    ((s_2, fa'_lst)) == var_1 →
    fun_allocfuncs s v_moduleinst ([v_func] ++ func'_lst) ((s_2, [fa] ++ fa'_lst))


inductive allocfuncs_is_wf : store → moduleinst → List func → store × List funcaddr → Prop where
  | allocfuncs_is_wf_0 (v_store : store) (v_moduleinst : moduleinst) (var_0_lst : List func) (ret_val : store × List funcaddr) (var_0 : store × List funcaddr) : 
    fun_allocfuncs v_store v_moduleinst var_0_lst var_0 →
    wf_store v_store →
    wf_moduleinst v_moduleinst →
    (∀ var_0_elem ∈ var_0_lst, wf_func var_0_elem) →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    allocfuncs_is_wf v_store v_moduleinst var_0_lst ret_val


inductive fun_allocglobal : store → globaltype → val → store × globaladdr → Prop where
  | fun_allocglobal_case_0 (s : store) (v_globaltype : globaltype) (v_val : val) (gi : globalinst) : 
    gi == ({
      TYPE := v_globaltype
      VALUE := v_val : globalinst
    }) →
    wf_globalinst ({
      TYPE := v_globaltype
      VALUE := v_val : globalinst
    }) →
    fun_allocglobal s v_globaltype v_val (({
      s with 
      GLOBALS := (s.GLOBALS) ++ [gi]
    }, List.length (s.GLOBALS)))


inductive allocglobal_is_wf : store → globaltype → val → store × globaladdr → Prop where
  | allocglobal_is_wf_0 (v_store : store) (v_globaltype : globaltype) (v_val : val) (ret_val : store × globaladdr) (var_0 : store × globaladdr) : 
    fun_allocglobal v_store v_globaltype v_val var_0 →
    wf_store v_store →
    wf_val v_val →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    allocglobal_is_wf v_store v_globaltype v_val ret_val


inductive fun_allocglobals : store → List globaltype → List val → store × List globaladdr → Prop where
  | fun_allocglobals_case_0 (s : store) : fun_allocglobals s [] [] ((s, []))
  | fun_allocglobals_case_1 (s : store) (v_globaltype : globaltype) (globaltype'_lst : List globaltype) (v_val : val) (val'_lst : List val) (ga : globaladdr) (s_1 : store) (s_2 : store) (ga'_lst : List globaladdr) (var_1 : store × List globaladdr) (var_0 : store × globaladdr) : 
    fun_allocglobals s_1 globaltype'_lst val'_lst var_1 →
    fun_allocglobal s v_globaltype v_val var_0 →
    ((s_1, ga)) == var_0 →
    ((s_2, ga'_lst)) == var_1 →
    fun_allocglobals s ([v_globaltype] ++ globaltype'_lst) ([v_val] ++ val'_lst) ((s_2, [ga] ++ ga'_lst))


inductive allocglobals_is_wf : store → List globaltype → List val → store × List globaladdr → Prop where
  | allocglobals_is_wf_0 (v_store : store) (var_0_lst : List globaltype) (var_1_lst : List val) (ret_val : store × List globaladdr) (var_0 : store × List globaladdr) : 
    fun_allocglobals v_store var_0_lst var_1_lst var_0 →
    wf_store v_store →
    (∀ var_1_elem ∈ var_1_lst, wf_val var_1_elem) →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    allocglobals_is_wf v_store var_0_lst var_1_lst ret_val


inductive fun_alloctable : store → tabletype → store × tableaddr → Prop where
  | fun_alloctable_case_0 (s : store) (i : uN) (j_opt : Option u32) (ti : tableinst) : 
    ti == ({
      TYPE := .mk_limits i j_opt
      REFS := List.replicate (proj_uN_0 i) none : tableinst
    }) →
    wf_tableinst ({
      TYPE := .mk_limits i j_opt
      REFS := List.replicate (proj_uN_0 i) none : tableinst
    }) →
    fun_alloctable s (.mk_limits i j_opt) (({
      s with 
      TABLES := (s.TABLES) ++ [ti]
    }, List.length (s.TABLES)))


inductive alloctable_is_wf : store → tabletype → store × tableaddr → Prop where
  | alloctable_is_wf_0 (v_store : store) (v_tabletype : tabletype) (ret_val : store × tableaddr) (var_0 : store × tableaddr) : 
    fun_alloctable v_store v_tabletype var_0 →
    wf_store v_store →
    wf_limits v_tabletype →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    alloctable_is_wf v_store v_tabletype ret_val


inductive fun_alloctables : store → List tabletype → store × List tableaddr → Prop where
  | fun_alloctables_case_0 (s : store) : fun_alloctables s [] ((s, []))
  | fun_alloctables_case_1 (s : store) (v_tabletype : limits) (tabletype'_lst : List tabletype) (ta : tableaddr) (s_1 : store) (s_2 : store) (ta'_lst : List tableaddr) (var_1 : store × List tableaddr) (var_0 : store × tableaddr) : 
    fun_alloctables s_1 tabletype'_lst var_1 →
    fun_alloctable s v_tabletype var_0 →
    ((s_1, ta)) == var_0 →
    ((s_2, ta'_lst)) == var_1 →
    fun_alloctables s ([v_tabletype] ++ tabletype'_lst) ((s_2, [ta] ++ ta'_lst))


inductive alloctables_is_wf : store → List tabletype → store × List tableaddr → Prop where
  | alloctables_is_wf_0 (v_store : store) (var_0_lst : List tabletype) (ret_val : store × List tableaddr) (var_0 : store × List tableaddr) : 
    fun_alloctables v_store var_0_lst var_0 →
    wf_store v_store →
    (∀ var_0_elem ∈ var_0_lst, wf_limits var_0_elem) →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    alloctables_is_wf v_store var_0_lst ret_val


inductive fun_allocmem : store → memtype → store × memaddr → Prop where
  | fun_allocmem_case_0 (s : store) (i : uN) (j_opt : Option u32) (mi : meminst) : 
    mi == ({
      TYPE := .mk_limits i j_opt
      BYTES := List.replicate ((proj_uN_0 i) * (64 * Ki)) (byte.mk_byte 0) : meminst
    }) →
    wf_meminst ({
      TYPE := .mk_limits i j_opt
      BYTES := List.replicate ((proj_uN_0 i) * (64 * Ki)) (byte.mk_byte 0) : meminst
    }) →
    fun_allocmem s (.mk_limits i j_opt) (({
      s with 
      MEMS := (s.MEMS) ++ [mi]
    }, List.length (s.MEMS)))


inductive allocmem_is_wf : store → memtype → store × memaddr → Prop where
  | allocmem_is_wf_0 (v_store : store) (v_memtype : memtype) (ret_val : store × memaddr) (var_0 : store × memaddr) : 
    fun_allocmem v_store v_memtype var_0 →
    wf_store v_store →
    wf_limits v_memtype →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    allocmem_is_wf v_store v_memtype ret_val


inductive fun_allocmems : store → List memtype → store × List memaddr → Prop where
  | fun_allocmems_case_0 (s : store) : fun_allocmems s [] ((s, []))
  | fun_allocmems_case_1 (s : store) (v_memtype : limits) (memtype'_lst : List memtype) (ma : memaddr) (s_1 : store) (s_2 : store) (ma'_lst : List memaddr) (var_1 : store × List memaddr) (var_0 : store × memaddr) : 
    fun_allocmems s_1 memtype'_lst var_1 →
    fun_allocmem s v_memtype var_0 →
    ((s_1, ma)) == var_0 →
    ((s_2, ma'_lst)) == var_1 →
    fun_allocmems s ([v_memtype] ++ memtype'_lst) ((s_2, [ma] ++ ma'_lst))


inductive allocmems_is_wf : store → List memtype → store × List memaddr → Prop where
  | allocmems_is_wf_0 (v_store : store) (var_0_lst : List memtype) (ret_val : store × List memaddr) (var_0 : store × List memaddr) : 
    fun_allocmems v_store var_0_lst var_0 →
    wf_store v_store →
    (∀ var_0_elem ∈ var_0_lst, wf_limits var_0_elem) →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    allocmems_is_wf v_store var_0_lst ret_val


def instexport (var_0_lst : List funcaddr) (var_1_lst : List globaladdr) (var_2_lst : List tableaddr) (var_3_lst : List memaddr) (v_export : «export») : exportinst :=
  match v_export with
  | export.EXPORT v_name (externidx.FUNC x) => {
    NAME := v_name
    ADDR := externaddr.FUNC ((var_0_lst)[proj_uN_0 x]!) : exportinst
  }
  | export.EXPORT v_name (externidx.GLOBAL x) => {
    NAME := v_name
    ADDR := externaddr.GLOBAL ((var_1_lst)[proj_uN_0 x]!) : exportinst
  }
  | export.EXPORT v_name (externidx.TABLE x) => {
    NAME := v_name
    ADDR := externaddr.TABLE ((var_2_lst)[proj_uN_0 x]!) : exportinst
  }
  | export.EXPORT v_name (externidx.MEM x) => {
    NAME := v_name
    ADDR := externaddr.MEM ((var_3_lst)[proj_uN_0 x]!) : exportinst
  }

inductive instexport_is_wf : List funcaddr → List globaladdr → List tableaddr → List memaddr → «export» → exportinst → Prop where
  | instexport_is_wf_0 (var_0_lst : List funcaddr) (var_1_lst : List globaladdr) (var_2_lst : List tableaddr) (var_3_lst : List memaddr) (v_export : «export») (ret_val : exportinst) : 
    wf_export v_export →
    ret_val == (instexport var_0_lst var_1_lst var_2_lst var_3_lst v_export) →
    wf_exportinst ret_val →
    instexport_is_wf var_0_lst var_1_lst var_2_lst var_3_lst v_export ret_val


inductive fun_allocmodule : store → module → List externaddr → List val → store × moduleinst → Prop where
  | fun_allocmodule_case_0 (s : store) (v_module : module) (externaddr_lst : List externaddr) (val_lst : List val) (s_4 : store) (v_moduleinst : moduleinst) (ft_lst : List functype) (import_lst : List «import») (n_func : Nat) (func_lst : List func) (n_global : Nat) (expr_1_lst : List expr) (globaltype_lst : List globaltype) (n_table : Nat) (tabletype_lst : List tabletype) (n_mem : Nat) (memtype_lst : List memtype) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») (s_1 : store) (s_2 : store) (s_3 : store) (fa_ex_lst : List funcaddr) (ga_ex_lst : List globaladdr) (ta_ex_lst : List tableaddr) (ma_ex_lst : List memaddr) (fa_lst : List funcaddr) (ga_lst : List globaladdr) (ta_lst : List tableaddr) (ma_lst : List memaddr) (xi_lst : List exportinst) (var_7 : store × List memaddr) (var_6 : store × List tableaddr) (var_5 : store × List globaladdr) (var_4 : store × List funcaddr) (var_3 : List memaddr) (var_2 : List tableaddr) (var_1 : List globaladdr) (var_0 : List funcaddr) : 
    fun_allocmems s_3 memtype_lst var_7 →
    fun_alloctables s_2 tabletype_lst var_6 →
    fun_allocglobals s_1 globaltype_lst val_lst var_5 →
    fun_allocfuncs s v_moduleinst func_lst var_4 →
    fun_mems externaddr_lst var_3 →
    fun_tables externaddr_lst var_2 →
    fun_globals externaddr_lst var_1 →
    fun_funcs externaddr_lst var_0 →
    v_module == (module.MODULE (ft_lst |>.map (fun ft_1_elem => type.TYPE ft_1_elem)) import_lst func_lst (expr_1_lst |>.map (fun expr_1_1_elem globaltype_195_elem => global.GLOBAL globaltype_195_elem expr_1_1_elem) |>.ap globaltype_lst) (tabletype_lst |>.map (fun tabletype_241_elem => table.TABLE tabletype_241_elem)) (memtype_lst |>.map (fun memtype_293_elem => mem.MEMORY memtype_293_elem)) elem_lst data_lst start_opt export_lst) →
    fa_ex_lst == var_0 →
    ga_ex_lst == var_1 →
    ta_ex_lst == var_2 →
    ma_ex_lst == var_3 →
    fa_lst == (List.range n_func |>.map (fun i_func_1 => (List.length (s.FUNCS)) + i_func_1)) →
    ga_lst == (List.range n_global |>.map (fun i_global_1 => (List.length (s.GLOBALS)) + i_global_1)) →
    ta_lst == (List.range n_table |>.map (fun i_table_1 => (List.length (s.TABLES)) + i_table_1)) →
    ma_lst == (List.range n_mem |>.map (fun i_mem_1 => (List.length (s.MEMS)) + i_mem_1)) →
    xi_lst == (export_lst |>.map (fun export_2_elem => instexport (fa_ex_lst ++ fa_lst) (ga_ex_lst ++ ga_lst) (ta_ex_lst ++ ta_lst) (ma_ex_lst ++ ma_lst) export_2_elem)) →
    v_moduleinst == ({
      TYPES := ft_lst
      FUNCS := fa_ex_lst ++ fa_lst
      GLOBALS := ga_ex_lst ++ ga_lst
      TABLES := ta_ex_lst ++ ta_lst
      MEMS := ma_ex_lst ++ ma_lst
      EXPORTS := xi_lst : moduleinst
    }) →
    ((s_1, fa_lst)) == var_4 →
    ((s_2, ga_lst)) == var_5 →
    ((s_3, ta_lst)) == var_6 →
    ((s_4, ma_lst)) == var_7 →
    wf_store s_1 →
    wf_store s_2 →
    wf_store s_3 →
    wf_module (module.MODULE (ft_lst |>.map (fun ft_3_elem => type.TYPE ft_3_elem)) import_lst func_lst (expr_1_lst |>.map (fun expr_1_2_elem globaltype_198_elem => global.GLOBAL globaltype_198_elem expr_1_2_elem) |>.ap globaltype_lst) (tabletype_lst |>.map (fun tabletype_244_elem => table.TABLE tabletype_244_elem)) (memtype_lst |>.map (fun memtype_296_elem => mem.MEMORY memtype_296_elem)) elem_lst data_lst start_opt export_lst) →
    wf_moduleinst ({
      TYPES := ft_lst
      FUNCS := fa_ex_lst ++ fa_lst
      GLOBALS := ga_ex_lst ++ ga_lst
      TABLES := ta_ex_lst ++ ta_lst
      MEMS := ma_ex_lst ++ ma_lst
      EXPORTS := xi_lst : moduleinst
    }) →
    fun_allocmodule s v_module externaddr_lst val_lst ((s_4, v_moduleinst))


inductive allocmodule_is_wf : store → module → List externaddr → List val → store × moduleinst → Prop where
  | allocmodule_is_wf_0 (v_store : store) (v_module : module) (var_0_lst : List externaddr) (var_1_lst : List val) (ret_val : store × moduleinst) (var_0 : store × moduleinst) : 
    fun_allocmodule v_store v_module var_0_lst var_1_lst var_0 →
    wf_store v_store →
    wf_module v_module →
    (∀ var_1_elem ∈ var_1_lst, wf_val var_1_elem) →
    ret_val == var_0 →
    wf_store (ret_val.1) →
    wf_moduleinst (ret_val.2) →
    allocmodule_is_wf v_store v_module var_0_lst var_1_lst ret_val


inductive fun_initelem : store → moduleinst → List u32 → List (List funcaddr) → store → Prop where
  | fun_initelem_case_0 (s : store) (v_moduleinst : moduleinst) : fun_initelem s v_moduleinst [] [] s
  | fun_initelem_case_1 (s : store) (v_moduleinst : moduleinst) (i : uN) (i'_lst : List u32) (a_lst : List addr) (a'_lst_lst : List (List addr)) (s_1 : store) (s_2 : store) (var_0 : store) : 
    fun_initelem s_1 v_moduleinst i'_lst a'_lst_lst var_0 →
    0 < (List.length (v_moduleinst.TABLES)) →
    s_1 == ({
      s with 
      TABLES := List.modify (s.TABLES) ((v_moduleinst.TABLES)[0]!) (fun elem_1 => {
        elem_1 with 
        REFS := ((elem_1.REFS.take (proj_uN_0 i)) ++ (a_lst |>.map (fun a_7_elem => some a_7_elem))) ++ (elem_1.REFS.drop ((proj_uN_0 i) + (List.length a_lst)))
      })
    }) →
    s_2 == var_0 →
    wf_store s_1 →
    fun_initelem s v_moduleinst ([i] ++ i'_lst) ([a_lst] ++ a'_lst_lst) s_2


inductive initelem_is_wf : store → moduleinst → List u32 → List (List funcaddr) → store → Prop where
  | initelem_is_wf_0 (v_store : store) (v_moduleinst : moduleinst) (var_0_lst : List u32) (var_1_lst_lst : List (List funcaddr)) (ret_val : store) (var_0 : store) : 
    fun_initelem v_store v_moduleinst var_0_lst var_1_lst_lst var_0 →
    wf_store v_store →
    wf_moduleinst v_moduleinst →
    (∀ var_0_elem ∈ var_0_lst, wf_uN 32 var_0_elem) →
    ret_val == var_0 →
    wf_store ret_val →
    initelem_is_wf v_store v_moduleinst var_0_lst var_1_lst_lst ret_val


inductive fun_initdata : store → moduleinst → List u32 → List (List byte) → store → Prop where
  | fun_initdata_case_0 (s : store) (v_moduleinst : moduleinst) : fun_initdata s v_moduleinst [] [] s
  | fun_initdata_case_1 (s : store) (v_moduleinst : moduleinst) (i : uN) (i'_lst : List u32) (b_lst : List byte) (b'_lst_lst : List (List byte)) (s_1 : store) (s_2 : store) (var_0 : store) : 
    fun_initdata s_1 v_moduleinst i'_lst b'_lst_lst var_0 →
    0 < (List.length (v_moduleinst.MEMS)) →
    s_1 == ({
      s with 
      MEMS := List.modify (s.MEMS) ((v_moduleinst.MEMS)[0]!) (fun elem_1 => {
        elem_1 with 
        BYTES := ((elem_1.BYTES.take (proj_uN_0 i)) ++ b_lst) ++ (elem_1.BYTES.drop ((proj_uN_0 i) + (List.length b_lst)))
      })
    }) →
    s_2 == var_0 →
    fun_initdata s v_moduleinst ([i] ++ i'_lst) ([b_lst] ++ b'_lst_lst) s_2


inductive initdata_is_wf : store → moduleinst → List u32 → List (List byte) → store → Prop where
  | initdata_is_wf_0 (v_store : store) (v_moduleinst : moduleinst) (var_0_lst : List u32) (var_1_lst_lst : List (List byte)) (ret_val : store) (var_0 : store) : 
    fun_initdata v_store v_moduleinst var_0_lst var_1_lst_lst var_0 →
    wf_store v_store →
    wf_moduleinst v_moduleinst →
    (∀ var_0_elem ∈ var_0_lst, wf_uN 32 var_0_elem) →
    (∀ var_1_lst_elem ∈ var_1_lst_lst, ∀ var_1_elem ∈ var_1_lst_elem, wf_byte var_1_elem) →
    ret_val == var_0 →
    wf_store ret_val →
    initdata_is_wf v_store v_moduleinst var_0_lst var_1_lst_lst ret_val


inductive fun_instantiate : store → module → List externaddr → config → Prop where
  | fun_instantiate_case_0 (s : store) (v_module : module) (externaddr_lst : List externaddr) (f : frame) (x'_opt : Option idx) (functype_lst : List functype) (expr_G_lst : List expr) (globaltype_lst : List globaltype) (expr_E_lst : List expr) (x_lst_lst : List (List idx)) (b_lst_lst : List (List byte)) (expr_D_lst : List expr) (moduleinst_init : moduleinst) (f_init : frame) (val_lst : List val) (i_E_lst : List val_) (i_D_lst : List val_) (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») (n_F : n) (z : state) (s_1 : store) (v_moduleinst : moduleinst) (s_2 : store) (s_3 : store) (var_6 : List globaladdr) (var_5 : List funcaddr) (var_4 : store) (var_3 : store) (var_2 : store × moduleinst) (var_1 : List globaladdr) (var_0 : List funcaddr) : 
    fun_globals externaddr_lst var_6 →
    fun_funcs externaddr_lst var_5 →
    (∀ i_D_2_elem ∈ i_D_lst, (proj_val__0 i_D_2_elem) != none) →
    fun_initdata s_2 v_moduleinst (i_D_lst |>.map (fun i_D_2_elem => Option.get! (proj_val__0 i_D_2_elem))) b_lst_lst var_4 →
    (∀ i_E_2_elem ∈ i_E_lst, (proj_val__0 i_E_2_elem) != none) →
    (∀ x_lst_2_elem ∈ x_lst_lst, ∀ x_2_elem ∈ x_lst_2_elem, (proj_uN_0 x_2_elem) < (List.length (v_moduleinst.FUNCS))) →
    fun_initelem s_1 v_moduleinst (i_E_lst |>.map (fun i_E_2_elem => Option.get! (proj_val__0 i_E_2_elem))) (x_lst_lst |>.map (fun x_lst_2_elem => x_lst_2_elem |>.map (fun x_2_elem => (v_moduleinst.FUNCS)[proj_uN_0 x_2_elem]!))) var_3 →
    fun_allocmodule s v_module externaddr_lst val_lst var_2 →
    fun_globals externaddr_lst var_1 →
    fun_funcs externaddr_lst var_0 →
    (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) == v_module →
    type_lst == (functype_lst |>.map (fun functype_49_elem => type.TYPE functype_49_elem)) →
    global_lst == (expr_G_lst |>.map (fun expr_G_1_elem globaltype_200_elem => global.GLOBAL globaltype_200_elem expr_G_1_elem) |>.ap globaltype_lst) →
    elem_lst == (expr_E_lst |>.map (fun expr_E_1_elem x_lst_1_elem => elem.ELEM expr_E_1_elem x_lst_1_elem) |>.ap x_lst_lst) →
    data_lst == (b_lst_lst |>.map (fun b_lst_1_elem expr_D_1_elem => data.DATA expr_D_1_elem b_lst_1_elem) |>.ap expr_D_lst) →
    start_opt == (x'_opt |>.map (fun x'_1_elem => start.START x'_1_elem)) →
    n_F == (List.length func_lst) →
    moduleinst_init == ({
      TYPES := functype_lst
      FUNCS := var_0 ++ (List.range n_F |>.map (fun i_F_1 => (List.length (s.FUNCS)) + i_F_1))
      GLOBALS := var_1
      TABLES := []
      MEMS := []
      EXPORTS := [] : moduleinst
    }) →
    f_init == ({
      LOCALS := []
      MODULE := moduleinst_init : frame
    }) →
    z == (state.mk_state s f_init) →
    (List.length expr_G_lst) == (List.length val_lst) →
    (∀ __iter_tuple ∈ expr_G_lst |>.zip val_lst, Eval_expr z (__iter_tuple.1) z [__iter_tuple.2]) →
    (List.length expr_E_lst) == (List.length i_E_lst) →
    (∀ __iter_tuple ∈ expr_E_lst |>.zip i_E_lst, Eval_expr z (__iter_tuple.1) z [val.CONST valtype.I32 (__iter_tuple.2)]) →
    (List.length expr_D_lst) == (List.length i_D_lst) →
    (∀ __iter_tuple ∈ expr_D_lst |>.zip i_D_lst, Eval_expr z (__iter_tuple.1) z [val.CONST valtype.I32 (__iter_tuple.2)]) →
    ((s_1, v_moduleinst)) == var_2 →
    s_2 == var_3 →
    s_3 == var_4 →
    f == ({
      LOCALS := []
      MODULE := v_moduleinst : frame
    }) →
    (∀ val_5_elem ∈ val_lst, wf_val val_5_elem) →
    wf_module (module.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst) →
    (List.length expr_G_lst) == (List.length globaltype_lst) →
    (∀ __iter_tuple ∈ expr_G_lst |>.zip globaltype_lst, wf_global (global.GLOBAL (__iter_tuple.2) (__iter_tuple.1))) →
    (List.length expr_E_lst) == (List.length x_lst_lst) →
    (∀ __iter_tuple ∈ expr_E_lst |>.zip x_lst_lst, wf_elem (elem.ELEM (__iter_tuple.1) (__iter_tuple.2))) →
    (List.length b_lst_lst) == (List.length expr_D_lst) →
    (∀ __iter_tuple ∈ b_lst_lst |>.zip expr_D_lst, wf_data (data.DATA (__iter_tuple.2) (__iter_tuple.1))) →
    (∀ x'_2_elem ∈ Option.toList x'_opt, wf_start (start.START x'_2_elem)) →
    wf_moduleinst ({
      TYPES := functype_lst
      FUNCS := var_5 ++ (List.range n_F |>.map (fun i_F_2 => (List.length (s.FUNCS)) + i_F_2))
      GLOBALS := var_6
      TABLES := []
      MEMS := []
      EXPORTS := [] : moduleinst
    }) →
    wf_frame ({
      LOCALS := []
      MODULE := moduleinst_init : frame
    }) →
    wf_state (state.mk_state s f_init) →
    (∀ i_E_3_elem ∈ i_E_lst, wf_val (val.CONST valtype.I32 i_E_3_elem)) →
    (∀ i_D_3_elem ∈ i_D_lst, wf_val (val.CONST valtype.I32 i_D_3_elem)) →
    wf_frame ({
      LOCALS := []
      MODULE := v_moduleinst : frame
    }) →
    fun_instantiate s v_module externaddr_lst (config.mk_config (state.mk_state s_3 f) (Option.toList (x'_opt |>.map (fun x'_elem => admininstr.CALL x'_elem))))


inductive instantiate_is_wf : store → module → List externaddr → config → Prop where
  | instantiate_is_wf_0 (v_store : store) (v_module : module) (var_0_lst : List externaddr) (ret_val : config) (var_0 : config) : 
    fun_instantiate v_store v_module var_0_lst var_0 →
    wf_store v_store →
    wf_module v_module →
    ret_val == var_0 →
    wf_config ret_val →
    instantiate_is_wf v_store v_module var_0_lst ret_val


inductive fun_invoke : store → funcaddr → List val → config → Prop where
  | fun_invoke_case_0 (s : store) (fa : Nat) (v_n : Nat) (val_lst : List val) (f : frame) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    f == ({
      LOCALS := []
      MODULE := {
        TYPES := []
        FUNCS := []
        GLOBALS := []
        TABLES := []
        MEMS := []
        EXPORTS := [] : moduleinst
      } : frame
    }) →
    fa < (List.length (fun_funcinst (state.mk_state s f))) →
    (((fun_funcinst (state.mk_state s f))[fa]!).TYPE) == (functype.mk_functype t_1_lst t_2_lst) →
    wf_frame ({
      LOCALS := []
      MODULE := {
        TYPES := []
        FUNCS := []
        GLOBALS := []
        TABLES := []
        MEMS := []
        EXPORTS := [] : moduleinst
      } : frame
    }) →
    wf_state (state.mk_state s f) →
    v_n == (List.length val_lst) →
    fun_invoke s fa val_lst (config.mk_config (state.mk_state s f) ((val_lst |>.map (fun v_val_elem => admininstr_val v_val_elem)) ++ [admininstr.CALL_ADDR fa]))


inductive invoke_is_wf : store → funcaddr → List val → config → Prop where
  | invoke_is_wf_0 (v_store : store) (v_funcaddr : funcaddr) (var_0_lst : List val) (ret_val : config) (var_0 : config) : 
    fun_invoke v_store v_funcaddr var_0_lst var_0 →
    wf_store v_store →
    (∀ var_0_elem ∈ var_0_lst, wf_val var_0_elem) →
    ret_val == var_0 →
    wf_config ret_val →
    invoke_is_wf v_store v_funcaddr var_0_lst ret_val


abbrev startopt : Type := List start

abbrev code : Type := List «local» × expr

inductive Context_ok : context → Prop where
  | mk_Context_ok (C : context) (ft_lst : List functype) (ft_2_lst : List functype) (gt_lst : List globaltype) (tt_lst : List tabletype) (mt_lst : List memtype) (lct_lst : List valtype) (rt_lst : List valtype) (rt'_opt : Option valtype) : 
    C == ({
      TYPES := ft_lst
      FUNCS := ft_2_lst
      GLOBALS := gt_lst
      TABLES := tt_lst
      MEMS := mt_lst
      LOCALS := lct_lst
      LABELS := rt_lst |>.map (fun rt_elem => some rt_elem)
      RETURN := some rt'_opt : context
    }) →
    (∀ ft_elem ∈ ft_lst, Functype_ok ft_elem) →
    (∀ gt_elem ∈ gt_lst, Globaltype_ok gt_elem) →
    (∀ mt_elem ∈ mt_lst, Memtype_ok mt_elem) →
    (∀ tt_elem ∈ tt_lst, Tabletype_ok tt_elem) →
    (∀ ft_2_elem ∈ ft_2_lst, Functype_ok ft_2_elem) →
    wf_context C →
    wf_context ({
      TYPES := ft_lst
      FUNCS := ft_2_lst
      GLOBALS := gt_lst
      TABLES := tt_lst
      MEMS := mt_lst
      LOCALS := lct_lst
      LABELS := rt_lst |>.map (fun rt_elem => some rt_elem)
      RETURN := some rt'_opt : context
    }) →
    Context_ok C


inductive Val_ok : val → valtype → Prop where
  | mk_Val_ok (t : valtype) (c_t : val_) : 
    wf_val (val.CONST t c_t) →
    Val_ok (val.CONST t c_t) t


inductive Result_ok : result → List valtype → Prop where
  | result (v_lst : List val) (t_lst : List valtype) : 
    (List.length t_lst) == (List.length v_lst) →
    (∀ __iter_tuple ∈ t_lst |>.zip v_lst, Val_ok (__iter_tuple.2) (__iter_tuple.1)) →
    wf_result (result._VALS v_lst) →
    Result_ok (result._VALS v_lst) t_lst
  | trap (t_lst : List valtype) : 
    wf_result result.TRAP →
    Result_ok result.TRAP t_lst


abbrev adminexpr : Type := List admininstr

inductive Externaddr_ok : store → externaddr → externtype → Prop where
  | global (s : store) (a : addr) (v_globalinst : globalinst) : 
    a < (List.length (s.GLOBALS)) →
    ((s.GLOBALS)[a]!) == v_globalinst →
    wf_store s →
    wf_externtype (externtype.GLOBAL (v_globalinst.TYPE)) →
    Externaddr_ok s (externaddr.GLOBAL a) (externtype.GLOBAL (v_globalinst.TYPE))
  | mem (s : store) (a : addr) (v_meminst : meminst) : 
    a < (List.length (s.MEMS)) →
    ((s.MEMS)[a]!) == v_meminst →
    wf_store s →
    wf_externtype (externtype.MEM (v_meminst.TYPE)) →
    Externaddr_ok s (externaddr.MEM a) (externtype.MEM (v_meminst.TYPE))
  | table (s : store) (a : addr) (v_tableinst : tableinst) : 
    a < (List.length (s.TABLES)) →
    ((s.TABLES)[a]!) == v_tableinst →
    wf_store s →
    wf_externtype (externtype.TABLE (v_tableinst.TYPE)) →
    Externaddr_ok s (externaddr.TABLE a) (externtype.TABLE (v_tableinst.TYPE))
  | func (s : store) (a : addr) (v_funcinst : funcinst) : 
    a < (List.length (s.FUNCS)) →
    ((s.FUNCS)[a]!) == v_funcinst →
    wf_store s →
    wf_externtype (externtype.FUNC (v_funcinst.TYPE)) →
    Externaddr_ok s (externaddr.FUNC a) (externtype.FUNC (v_funcinst.TYPE))
  | sub (s : store) (v_externaddr : externaddr) (xt : externtype) (xt' : externtype) : 
    Externaddr_ok s v_externaddr xt' →
    Externtype_sub xt' xt →
    wf_store s →
    wf_externtype xt →
    wf_externtype xt' →
    Externaddr_ok s v_externaddr xt


inductive Exportinst_ok : store → exportinst → Prop where
  | mk_Exportinst_ok (s : store) (nm : name) (xa : externaddr) (xt : externtype) : 
    Externaddr_ok s xa xt →
    wf_store s →
    wf_externtype xt →
    wf_exportinst ({
      NAME := nm
      ADDR := xa : exportinst
    }) →
    Exportinst_ok s ({
      NAME := nm
      ADDR := xa : exportinst
    })


inductive Moduleinst_ok : store → moduleinst → context → Prop where
  | mk_Moduleinst_ok (s : store) (functype_lst : List functype) (funcaddr_lst : List funcaddr) (globaladdr_lst : List globaladdr) (tableaddr_lst : List tableaddr) (memaddr_lst : List memaddr) (exportinst_lst : List exportinst) (functype_F_lst : List functype) (globaltype_lst : List globaltype) (tabletype_lst : List tabletype) (memtype_lst : List memtype) : 
    (∀ v_functype_elem ∈ functype_lst, Functype_ok v_functype_elem) →
    (List.length globaladdr_lst) == (List.length globaltype_lst) →
    (∀ __iter_tuple ∈ globaladdr_lst |>.zip globaltype_lst, Externaddr_ok s (externaddr.GLOBAL (__iter_tuple.1)) (externtype.GLOBAL (__iter_tuple.2))) →
    (List.length funcaddr_lst) == (List.length functype_F_lst) →
    (∀ __iter_tuple ∈ funcaddr_lst |>.zip functype_F_lst, Externaddr_ok s (externaddr.FUNC (__iter_tuple.1)) (externtype.FUNC (__iter_tuple.2))) →
    (List.length memaddr_lst) == (List.length memtype_lst) →
    (∀ __iter_tuple ∈ memaddr_lst |>.zip memtype_lst, Externaddr_ok s (externaddr.MEM (__iter_tuple.1)) (externtype.MEM (__iter_tuple.2))) →
    (List.length tableaddr_lst) == (List.length tabletype_lst) →
    (∀ __iter_tuple ∈ tableaddr_lst |>.zip tabletype_lst, Externaddr_ok s (externaddr.TABLE (__iter_tuple.1)) (externtype.TABLE (__iter_tuple.2))) →
    (∀ v_exportinst_elem ∈ exportinst_lst, Exportinst_ok s v_exportinst_elem) →
    disjoint_ name (exportinst_lst |>.map (fun v_exportinst_elem => v_exportinst_elem.NAME)) →
    (List.length ((globaladdr_lst |>.map (fun v_globaladdr_elem => externaddr.GLOBAL v_globaladdr_elem)) ++ ((memaddr_lst |>.map (fun v_memaddr_elem => externaddr.MEM v_memaddr_elem)) ++ ((tableaddr_lst |>.map (fun v_tableaddr_elem => externaddr.TABLE v_tableaddr_elem)) ++ (funcaddr_lst |>.map (fun v_funcaddr_elem => externaddr.FUNC v_funcaddr_elem)))))) > 0 →
    (∀ v_exportinst_elem ∈ exportinst_lst, List.contains ((globaladdr_lst |>.map (fun v_globaladdr_elem => externaddr.GLOBAL v_globaladdr_elem)) ++ ((memaddr_lst |>.map (fun v_memaddr_elem => externaddr.MEM v_memaddr_elem)) ++ ((tableaddr_lst |>.map (fun v_tableaddr_elem => externaddr.TABLE v_tableaddr_elem)) ++ (funcaddr_lst |>.map (fun v_funcaddr_elem => externaddr.FUNC v_funcaddr_elem))))) (v_exportinst_elem.ADDR)) →
    wf_store s →
    wf_moduleinst ({
      TYPES := functype_lst
      FUNCS := funcaddr_lst
      GLOBALS := globaladdr_lst
      TABLES := tableaddr_lst
      MEMS := memaddr_lst
      EXPORTS := exportinst_lst : moduleinst
    }) →
    wf_context ({
      TYPES := functype_lst
      FUNCS := functype_F_lst
      GLOBALS := globaltype_lst
      TABLES := tabletype_lst
      MEMS := memtype_lst
      LOCALS := []
      LABELS := []
      RETURN := none : context
    }) →
    (∀ v_globaltype_elem ∈ globaltype_lst, wf_externtype (externtype.GLOBAL v_globaltype_elem)) →
    (∀ functype_F_elem ∈ functype_F_lst, wf_externtype (externtype.FUNC functype_F_elem)) →
    (∀ v_memtype_elem ∈ memtype_lst, wf_externtype (externtype.MEM v_memtype_elem)) →
    (∀ v_tabletype_elem ∈ tabletype_lst, wf_externtype (externtype.TABLE v_tabletype_elem)) →
    Moduleinst_ok s ({
      TYPES := functype_lst
      FUNCS := funcaddr_lst
      GLOBALS := globaladdr_lst
      TABLES := tableaddr_lst
      MEMS := memaddr_lst
      EXPORTS := exportinst_lst : moduleinst
    }) ({
      TYPES := functype_lst
      FUNCS := functype_F_lst
      GLOBALS := globaltype_lst
      TABLES := tabletype_lst
      MEMS := memtype_lst
      LOCALS := []
      LABELS := []
      RETURN := none : context
    })


inductive Frame_ok : store → frame → context → Prop where
  | mk_Frame_ok (s : store) (val_lst : List val) (v_moduleinst : moduleinst) (C : context) (t_lst : List valtype) : 
    Moduleinst_ok s v_moduleinst C →
    (List.length t_lst) == (List.length val_lst) →
    (∀ __iter_tuple ∈ t_lst |>.zip val_lst, Val_ok (__iter_tuple.2) (__iter_tuple.1)) →
    wf_store s →
    wf_context C →
    wf_frame ({
      LOCALS := val_lst
      MODULE := v_moduleinst : frame
    }) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := t_lst
      LABELS := []
      RETURN := none : context
    }) →
    Frame_ok s ({
      LOCALS := val_lst
      MODULE := v_moduleinst : frame
    }) (C ++ ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := t_lst
      LABELS := []
      RETURN := none : context
    }))


mutual
inductive Instr_ok2 : store → context → admininstr → functype → Prop where
  | plain (s : store) (C : context) (v_instr : instr) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    Instr_ok C v_instr (functype.mk_functype t_1_lst t_2_lst) →
    wf_store s →
    wf_context C →
    wf_instr v_instr →
    Instr_ok2 s C (admininstr_instr v_instr) (functype.mk_functype t_1_lst t_2_lst)
  | label (s : store) (C : context) (v_n : n) (instr'_lst : List instr) (admininstr_lst : List admininstr) (t_opt : Option valtype) (t'_opt : Option valtype) : 
    (List.length (Option.toList t'_opt)) == v_n →
    Instrs_ok2 s C (instr'_lst |>.map (fun instr'_elem => admininstr_instr instr'_elem)) (functype.mk_functype (Option.toList t'_opt) (Option.toList t_opt)) →
    Instrs_ok2 s (({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t'_opt]
      RETURN := none : context
    }) ++ C) admininstr_lst (functype.mk_functype [] (Option.toList t_opt)) →
    wf_store s →
    wf_context C →
    wf_admininstr (admininstr.LABEL_ v_n instr'_lst admininstr_lst) →
    wf_context ({
      TYPES := []
      FUNCS := []
      GLOBALS := []
      TABLES := []
      MEMS := []
      LOCALS := []
      LABELS := [t'_opt]
      RETURN := none : context
    }) →
    Instr_ok2 s C (admininstr.LABEL_ v_n instr'_lst admininstr_lst) (functype.mk_functype [] (Option.toList t_opt))
  | frame (s : store) (C : context) (v_n : n) (f : frame) (admininstr_lst : List admininstr) (t_opt : Option valtype) (C' : context) : 
    (List.length (Option.toList t_opt)) == v_n →
    Frame_ok s f C' →
    Expr_ok2 s C' admininstr_lst t_opt →
    wf_store s →
    wf_context C →
    wf_context C' →
    wf_admininstr (admininstr.FRAME_ v_n f admininstr_lst) →
    Instr_ok2 s C (admininstr.FRAME_ v_n f admininstr_lst) (functype.mk_functype [] (Option.toList t_opt))
  | call_addr (s : store) (C : context) (v_funcaddr : funcaddr) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    Externaddr_ok s (externaddr.FUNC v_funcaddr) (externtype.FUNC (functype.mk_functype t_1_lst t_2_lst)) →
    wf_store s →
    wf_context C →
    wf_admininstr (admininstr.CALL_ADDR v_funcaddr) →
    wf_externtype (externtype.FUNC (functype.mk_functype t_1_lst t_2_lst)) →
    Instr_ok2 s C (admininstr.CALL_ADDR v_funcaddr) (functype.mk_functype t_1_lst t_2_lst)
  | trap (s : store) (C : context) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    wf_store s →
    wf_context C →
    wf_admininstr admininstr.TRAP →
    Instr_ok2 s C admininstr.TRAP (functype.mk_functype t_1_lst t_2_lst)

inductive Instrs_ok2 : store → context → List admininstr → functype → Prop where
  | empty (s : store) (C : context) : 
    wf_store s →
    wf_context C →
    Instrs_ok2 s C [] (functype.mk_functype [] [])
  | seq (s : store) (C : context) (admininstr_1 : admininstr) (admininstr_2_lst : List admininstr) (t_1_lst : List valtype) (t_3_lst : List valtype) (t_2_lst : List valtype) : 
    Instr_ok2 s C admininstr_1 (functype.mk_functype t_1_lst t_2_lst) →
    Instrs_ok2 s C admininstr_2_lst (functype.mk_functype t_2_lst t_3_lst) →
    wf_store s →
    wf_context C →
    wf_admininstr admininstr_1 →
    (∀ admininstr_2_elem ∈ admininstr_2_lst, wf_admininstr admininstr_2_elem) →
    Instrs_ok2 s C ([admininstr_1] ++ admininstr_2_lst) (functype.mk_functype t_1_lst t_3_lst)
  | frame (s : store) (C : context) (admininstr_lst : List admininstr) (t_lst : List valtype) (t_1_lst : List valtype) (t_2_lst : List valtype) : 
    Instrs_ok2 s C admininstr_lst (functype.mk_functype t_1_lst t_2_lst) →
    wf_store s →
    wf_context C →
    (∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem) →
    Instrs_ok2 s C admininstr_lst (functype.mk_functype (t_lst ++ t_1_lst) (t_lst ++ t_2_lst))

inductive Expr_ok2 : store → context → adminexpr → resulttype → Prop where
  | mk_Expr_ok2 (s : store) (C : context) (admininstr_lst : List admininstr) (t_opt : Option valtype) : 
    Instrs_ok2 s C admininstr_lst (functype.mk_functype [] (Option.toList t_opt)) →
    wf_store s →
    wf_context C →
    (∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem) →
    Expr_ok2 s C admininstr_lst t_opt


end

inductive Globalinst_ok : store → globalinst → globaltype → Prop where
  | mk_Globalinst_ok (s : store) (v_mut : «mut») (t : valtype) (v_val : val) : 
    Globaltype_ok (globaltype.mk_globaltype v_mut t) →
    Val_ok v_val t →
    wf_store s →
    wf_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) →
    Globalinst_ok s ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) (globaltype.mk_globaltype v_mut t)


inductive Meminst_ok : store → meminst → memtype → Prop where
  | mk_Meminst_ok (s : store) (v_n : n) (m_opt : Option m) (b_lst : List byte) : 
    Memtype_ok (.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))) →
    (List.length b_lst) == (v_n * (64 * Ki)) →
    wf_store s →
    wf_meminst ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      BYTES := b_lst : meminst
    }) →
    wf_limits (limits.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))) →
    Meminst_ok s ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      BYTES := b_lst : meminst
    }) (.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem)))


inductive Tableinst_ok : store → tableinst → tabletype → Prop where
  | mk_Tableinst_ok (s : store) (v_n : n) (m_opt : Option m) (fa_opt_lst : List (Option funcaddr)) (ft_opt_lst : List (Option functype)) : 
    Tabletype_ok (.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))) →
    (List.length fa_opt_lst) == (List.length ft_opt_lst) →
    (∀ __iter_tuple ∈ fa_opt_lst |>.zip ft_opt_lst, ((__iter_tuple.1) == none) ↔ ((__iter_tuple.2) == none)) →
    (∀ __iter_tuple ∈ fa_opt_lst |>.zip ft_opt_lst, ∀ __iter_tuple ∈ Option.toList (__iter_tuple.1) |>.zip (Option.toList (__iter_tuple.2)), Externaddr_ok s (externaddr.FUNC (__iter_tuple.1)) (externtype.FUNC (__iter_tuple.2))) →
    (List.length fa_opt_lst) == v_n →
    wf_store s →
    wf_tableinst ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      REFS := fa_opt_lst : tableinst
    }) →
    wf_limits (limits.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))) →
    (∀ ft_opt_elem ∈ ft_opt_lst, ∀ ft_elem ∈ Option.toList ft_opt_elem, wf_externtype (externtype.FUNC ft_elem)) →
    Tableinst_ok s ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      REFS := fa_opt_lst : tableinst
    }) (.mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem)))


inductive Funcinst_ok : store → funcinst → functype → Prop where
  | mk_Funcinst_ok (s : store) (ft : functype) (v_moduleinst : moduleinst) (v_func : func) (C : context) : 
    Functype_ok ft →
    Moduleinst_ok s v_moduleinst C →
    Func_ok C v_func ft →
    wf_store s →
    wf_context C →
    wf_funcinst ({
      TYPE := ft
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) →
    Funcinst_ok s ({
      TYPE := ft
      MODULE := v_moduleinst
      CODE := v_func : funcinst
    }) ft


inductive Store_ok : store → Prop where
  | mk_Store_ok (s : store) (globalinst_lst : List globalinst) (globaltype_lst : List globaltype) (meminst_lst : List meminst) (memtype_lst : List memtype) (tableinst_lst : List tableinst) (tabletype_lst : List tabletype) (funcinst_lst : List funcinst) (functype_lst : List functype) : 
    (List.length globalinst_lst) == (List.length globaltype_lst) →
    (∀ __iter_tuple ∈ globalinst_lst |>.zip globaltype_lst, Globalinst_ok s (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length meminst_lst) == (List.length memtype_lst) →
    (∀ __iter_tuple ∈ meminst_lst |>.zip memtype_lst, Meminst_ok s (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length tableinst_lst) == (List.length tabletype_lst) →
    (∀ __iter_tuple ∈ tableinst_lst |>.zip tabletype_lst, Tableinst_ok s (__iter_tuple.1) (__iter_tuple.2)) →
    (List.length funcinst_lst) == (List.length functype_lst) →
    (∀ __iter_tuple ∈ funcinst_lst |>.zip functype_lst, Funcinst_ok s (__iter_tuple.1) (__iter_tuple.2)) →
    s == ({
      FUNCS := funcinst_lst
      GLOBALS := globalinst_lst
      TABLES := tableinst_lst
      MEMS := meminst_lst : store
    }) →
    wf_store s →
    (∀ v_memtype_elem ∈ memtype_lst, wf_limits v_memtype_elem) →
    (∀ v_tabletype_elem ∈ tabletype_lst, wf_limits v_tabletype_elem) →
    wf_store ({
      FUNCS := funcinst_lst
      GLOBALS := globalinst_lst
      TABLES := tableinst_lst
      MEMS := meminst_lst : store
    }) →
    Store_ok s


inductive Extend_globalinst : globalinst → globalinst → Prop where
  | mk_Extend_globalinst (v_mut : «mut») (t : valtype) (v_val : val) (val' : val) : 
    (v_mut == (some r_MUT.MUT)) || (v_val == val') →
    wf_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) →
    wf_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := val' : globalinst
    }) →
    Extend_globalinst ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := v_val : globalinst
    }) ({
      TYPE := globaltype.mk_globaltype v_mut t
      VALUE := val' : globalinst
    })


inductive Extend_meminst : meminst → meminst → Prop where
  | mk_Extend_meminst (v_n : n) (m_opt : Option m) (b_lst : List byte) (n' : n) (b'_lst : List byte) : 
    v_n ≤ n' →
    (List.length b_lst) ≤ (List.length b'_lst) →
    wf_meminst ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      BYTES := b_lst : meminst
    }) →
    wf_meminst ({
      TYPE := .mk_limits (.mk_uN n') (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      BYTES := b'_lst : meminst
    }) →
    Extend_meminst ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      BYTES := b_lst : meminst
    }) ({
      TYPE := .mk_limits (.mk_uN n') (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      BYTES := b'_lst : meminst
    })


inductive Extend_tableinst : tableinst → tableinst → Prop where
  | mk_Extend_tableinst (v_n : n) (m_opt : Option m) (ref_lst : List funcaddr) (n' : n) (ref'_lst : List funcaddr) : 
    v_n ≤ n' →
    (List.length ref_lst) ≤ (List.length ref'_lst) →
    wf_tableinst ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      REFS := ref_lst |>.map (fun ref_elem => some ref_elem) : tableinst
    }) →
    wf_tableinst ({
      TYPE := .mk_limits (.mk_uN n') (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      REFS := ref'_lst |>.map (fun ref'_elem => some ref'_elem) : tableinst
    }) →
    Extend_tableinst ({
      TYPE := .mk_limits (.mk_uN v_n) (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      REFS := ref_lst |>.map (fun ref_elem => some ref_elem) : tableinst
    }) ({
      TYPE := .mk_limits (.mk_uN n') (m_opt |>.map (fun v_m_elem => .mk_uN v_m_elem))
      REFS := ref'_lst |>.map (fun ref'_elem => some ref'_elem) : tableinst
    })


inductive Extend_funcinst : funcinst → funcinst → Prop where
  | mk_Extend_funcinst (ft : functype) (mm : moduleinst) (fc : func) : 
    wf_funcinst ({
      TYPE := ft
      MODULE := mm
      CODE := fc : funcinst
    }) →
    Extend_funcinst ({
      TYPE := ft
      MODULE := mm
      CODE := fc : funcinst
    }) ({
      TYPE := ft
      MODULE := mm
      CODE := fc : funcinst
    })


inductive Extend_store : store → store → Prop where
  | mk_Extend_store (s : store) (s' : store) : 
    a < (List.length (s.GLOBALS)) →
    a < (List.length (s'.GLOBALS)) →
    Extend_globalinst ((s.GLOBALS)[a]!) ((s'.GLOBALS)[a]!) →
    a < (List.length (s.MEMS)) →
    a < (List.length (s'.MEMS)) →
    Extend_meminst ((s.MEMS)[a]!) ((s'.MEMS)[a]!) →
    a < (List.length (s.TABLES)) →
    a < (List.length (s'.TABLES)) →
    Extend_tableinst ((s.TABLES)[a]!) ((s'.TABLES)[a]!) →
    a < (List.length (s.FUNCS)) →
    a < (List.length (s'.FUNCS)) →
    Extend_funcinst ((s.FUNCS)[a]!) ((s'.FUNCS)[a]!) →
    wf_store s →
    wf_store s' →
    Extend_store s s'


inductive State_ok : state → context → Prop where
  | mk_State_ok (s : store) (f : frame) (C : context) : 
    Store_ok s →
    Frame_ok s f C →
    wf_context C →
    wf_state (state.mk_state s f) →
    State_ok (state.mk_state s f) C


inductive Config_ok : config → resulttype → Prop where
  | mk_Config_ok (s : store) (f : frame) (admininstr_lst : List admininstr) (t_opt : Option valtype) (C : context) : 
    State_ok (state.mk_state s f) C →
    Expr_ok2 s C admininstr_lst t_opt →
    wf_context C →
    wf_config (config.mk_config (state.mk_state s f) admininstr_lst) →
    wf_state (state.mk_state s f) →
    Config_ok (config.mk_config (state.mk_state s f) admininstr_lst) t_opt

