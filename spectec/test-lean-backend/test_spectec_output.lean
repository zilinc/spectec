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
  | fun_sum_case_1 (v_n : Nat) (n'_lst : List n) (var_0 : Nat) : fun_sum n'_lst var_0 → fun_sum ([v_n] ++ n'_lst) (v_n + var_0)


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
  | all (n_lst : List n) : ∀ v_n_elem ∈ n_lst, Nat_ok v_n_elem v_n_elem → Nats_ok n_lst n_lst


inductive Pair_ok : Nat → Nat → Prop where
  | eq (v_n : n) : Pair_ok v_n v_n


inductive Pairs_ok : List Nat → List Nat → Prop where
  | all (n_lst : List n) (m_lst : List m) : (List.length m_lst) == (List.length n_lst) → ∀ __iter_tuple ∈ m_lst |>.zip n_lst, Pair_ok (__iter_tuple.2) (__iter_tuple.1) → Pairs_ok n_lst m_lst


inductive list (X : Type) : Type where
  | mk_list (X_lst : List X) : list X
deriving Inhabited, BEq

inductive byte : Type where
  | mk_byte (i : Nat) : byte
deriving Inhabited, BEq

inductive wf_byte : byte → Prop where
  | byte_case_0 (i : Nat) : (i ≥ 0) && (i ≤ 255) → wf_byte (.mk_byte i)


inductive uN : Type where
  | mk_uN (i : Nat) : uN
deriving Inhabited, BEq

def proj_uN_0 (x : uN) : Nat :=
  match x with
  | .mk_uN v_num_0 => (v_num_0)

inductive wf_uN : N → uN → Prop where
  | uN_case_0 (v_N : N) (i : Nat) : (i ≥ 0) && (i ≤ (Int.toNat (((2 ^ v_N) : Int) - (1 : Int)))) → wf_uN v_N (.mk_uN i)


inductive sN : Type where
  | mk_sN (i : Int) : sN
deriving Inhabited, BEq

inductive wf_sN : N → sN → Prop where
  | sN_case_0 (v_N : N) (i : Int) : (((i ≥ (- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int))) && (i ≤ (- (1 : Int)))) || (i == (0 : Int))) || ((i ≥ (1 : Int)) && (i ≤ (((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int) - (1 : Int)))) → wf_sN v_N (.mk_sN i)


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
  | fNmag_case_0 (v_N : N) (v_m : m) (v_exp : exp) : (v_m < (2 ^ (fun_M v_N))) && ((((2 : Int) - ((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int)) ≤ v_exp) && (v_exp ≤ (((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int) - (1 : Int)))) → wf_fNmag v_N (.NORM v_m v_exp)
  | fNmag_case_1 (v_N : N) (v_exp : exp) (v_m : m) : (v_m < (2 ^ (fun_M v_N))) && (((2 : Int) - ((2 ^ (Int.toNat (((E v_N) : Int) - (1 : Int)))) : Int)) == v_exp) → wf_fNmag v_N (.SUBNORM v_m)
  | fNmag_case_2 (v_N : N) : wf_fNmag v_N .INF
  | fNmag_case_3 (v_N : N) (v_m : m) : (1 ≤ v_m) && (v_m < (2 ^ (fun_M v_N))) → wf_fNmag v_N (.NAN v_m)


inductive fN : Type where
  | POS (_ : fNmag) : fN
  | NEG (_ : fNmag) : fN
deriving Inhabited, BEq

inductive wf_fN : N → fN → Prop where
  | fN_case_0 (v_N : N) (var_0 : fNmag) : wf_fNmag v_N var_0 → wf_fN v_N (.POS var_0)
  | fN_case_1 (v_N : N) (var_0 : fNmag) : wf_fNmag v_N var_0 → wf_fN v_N (.NEG var_0)


abbrev f32 : Type := fN

abbrev f64 : Type := fN

def fzero (v_N : N) : fN :=
  .POS (.SUBNORM 0)

inductive fzero_is_wf : N → fN → Prop where
  | fzero_is_wf_0 (v_N : N) (ret_val : fN) : ret_val == (fzero v_N) → wf_fN v_N ret_val → fzero_is_wf v_N ret_val


def fone (v_N : N) : fN :=
  .POS (.NORM 1 (0 : Int))

inductive fone_is_wf : N → fN → Prop where
  | fone_is_wf_0 (v_N : N) (ret_val : fN) : ret_val == (fone v_N) → wf_fN v_N ret_val → fone_is_wf v_N ret_val


def canon_ (v_N : N) : Nat :=
  2 ^ (Int.toNat (((Option.get! (signif v_N)) : Int) - (1 : Int)))

inductive char : Type where
  | mk_char (i : Nat) : char
deriving Inhabited, BEq

inductive wf_char : char → Prop where
  | char_case_0 (i : Nat) : ((i ≥ 0) && (i ≤ 55295)) || ((i ≥ 57344) && (i ≤ 1114111)) → wf_char (.mk_char i)


opaque utf8 (var_0_lst : List char) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive utf8_is_wf : List char → List byte → Prop where
  | utf8_is_wf_0 (var_0_lst : List char) (ret_val_lst : List byte) : ∀ var_0_elem ∈ var_0_lst, wf_char var_0_elem → ret_val_lst == (utf8 var_0_lst) → ∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem → utf8_is_wf var_0_lst ret_val_lst


inductive name : Type where
  | mk_name (char_lst : List char) : name
deriving Inhabited, BEq

inductive wf_name : name → Prop where
  | name_case_0 (char_lst : List char) : ∀ v_char_elem ∈ char_lst, wf_char v_char_elem → (List.length (utf8 char_lst)) < (2 ^ 32) → wf_name (.mk_name char_lst)


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
  | .I32 => .I32
  | .I64 => .I64

inductive Fnn : Type where
  | F32 : Fnn
  | F64 : Fnn
deriving Inhabited, BEq

def valtype_Fnn (var_0 : Fnn) : valtype :=
  match var_0 with
  | .F32 => .F32
  | .F64 => .F64

abbrev resulttype : Type := Option valtype

abbrev «mut» : Type := Option r_MUT

inductive limits : Type where
  | mk_limits (v_u32 : u32) (u32_opt : Option u32) : limits
deriving Inhabited, BEq

inductive wf_limits : limits → Prop where
  | limits_case_0 (v_u32 : u32) (u32_opt : Option u32) : wf_uN 32 v_u32 → wf_limits (.mk_limits v_u32 u32_opt)


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
  | externtype_case_0 (v_functype : functype) : wf_externtype (.FUNC v_functype)
  | externtype_case_1 (v_globaltype : globaltype) : wf_externtype (.GLOBAL v_globaltype)
  | externtype_case_2 (v_tabletype : tabletype) : wf_limits v_tabletype → wf_externtype (.TABLE v_tabletype)
  | externtype_case_3 (v_memtype : memtype) : wf_limits v_memtype → wf_externtype (.MEM v_memtype)


def size (v_valtype : valtype) : Nat :=
  match v_valtype with
  | .I32 => 32
  | .I64 => 64
  | .F32 => 32
  | .F64 => 64

inductive val_ : Type where
  | mk_val__0 (v_Inn : Inn) (var_x : iN) : val_
  | mk_val__1 (v_Fnn : Fnn) (var_x : fN) : val_
deriving Inhabited, BEq

inductive wf_val_ : valtype → val_ → Prop where
  | val__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : iN) : wf_uN (size (valtype_Inn v_Inn)) var_x → v_valtype == (valtype_Inn v_Inn) → wf_val_ v_valtype (.mk_val__0 v_Inn var_x)
  | val__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : fN) : wf_fN (size (valtype_Fnn v_Fnn)) var_x → v_valtype == (valtype_Fnn v_Fnn) → wf_val_ v_valtype (.mk_val__1 v_Fnn var_x)


def proj_val__0 (var_x : val_) : Option iN :=
  match var_x with
  | .mk_val__0 v_Inn var_x => some var_x
  | _ => none

def proj_val__1 (var_x : val_) : Option fN :=
  match var_x with
  | .mk_val__1 v_Fnn var_x => some var_x
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
  | .mk_sz v_num_0 => (v_num_0)

inductive wf_sz : sz → Prop where
  | sz_case_0 (i : Nat) : (((i == 8) || (i == 16)) || (i == 32)) || (i == 64) → wf_sz (.mk_sz i)


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
  | unop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : unop_Inn) : v_valtype == (valtype_Inn v_Inn) → wf_unop_ v_valtype (.mk_unop__0 v_Inn var_x)
  | unop__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : unop_Fnn) : v_valtype == (valtype_Fnn v_Fnn) → wf_unop_ v_valtype (.mk_unop__1 v_Fnn var_x)


def proj_unop__0 (var_x : unop_) : Option unop_Inn :=
  match var_x with
  | .mk_unop__0 v_Inn var_x => some var_x
  | _ => none

def proj_unop__1 (var_x : unop_) : Option unop_Fnn :=
  match var_x with
  | .mk_unop__1 v_Fnn var_x => some var_x
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
  | binop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : binop_Inn) : v_valtype == (valtype_Inn v_Inn) → wf_binop_ v_valtype (.mk_binop__0 v_Inn var_x)
  | binop__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : binop_Fnn) : v_valtype == (valtype_Fnn v_Fnn) → wf_binop_ v_valtype (.mk_binop__1 v_Fnn var_x)


def proj_binop__0 (var_x : binop_) : Option binop_Inn :=
  match var_x with
  | .mk_binop__0 v_Inn var_x => some var_x
  | _ => none

def proj_binop__1 (var_x : binop_) : Option binop_Fnn :=
  match var_x with
  | .mk_binop__1 v_Fnn var_x => some var_x
  | _ => none

inductive testop_Inn : Type where
  | EQZ : testop_Inn
deriving Inhabited, BEq

inductive testop_ : Type where
  | mk_testop__0 (v_Inn : Inn) (var_x : testop_Inn) : testop_
deriving Inhabited, BEq

inductive wf_testop_ : valtype → testop_ → Prop where
  | testop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : testop_Inn) : v_valtype == (valtype_Inn v_Inn) → wf_testop_ v_valtype (.mk_testop__0 v_Inn var_x)


def proj_testop__0 (var_x : testop_) : testop_Inn :=
  match var_x with
  | .mk_testop__0 v_Inn var_x => var_x

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
  | relop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : relop_Inn) : v_valtype == (valtype_Inn v_Inn) → wf_relop_ v_valtype (.mk_relop__0 v_Inn var_x)
  | relop__case_1 (v_valtype : valtype) (v_Fnn : Fnn) (var_x : relop_Fnn) : v_valtype == (valtype_Fnn v_Fnn) → wf_relop_ v_valtype (.mk_relop__1 v_Fnn var_x)


def proj_relop__0 (var_x : relop_) : Option relop_Inn :=
  match var_x with
  | .mk_relop__0 v_Inn var_x => some var_x
  | _ => none

def proj_relop__1 (var_x : relop_) : Option relop_Fnn :=
  match var_x with
  | .mk_relop__1 v_Fnn var_x => some var_x
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
  | memarg_case_ (var_0 : u32) (var_1 : u32) : wf_uN 32 var_0 → wf_uN 32 var_1 → wf_memarg ({
    ALIGN := var_0
    OFFSET := var_1
  })


inductive loadop_Inn : Type where
  | mk_loadop_Inn (v_sz : sz) (v_sx : sx) : loadop_Inn
deriving Inhabited, BEq

inductive wf_loadop_Inn : Inn → loadop_Inn → Prop where
  | loadop_Inn_case_0 (v_Inn : Inn) (v_sz : sz) (v_sx : sx) : wf_sz v_sz → (proj_sz_0 v_sz) < (size (valtype_Inn v_Inn)) → wf_loadop_Inn v_Inn (.mk_loadop_Inn v_sz v_sx)


inductive loadop_ : Type where
  | mk_loadop__0 (v_Inn : Inn) (var_x : loadop_Inn) : loadop_
deriving Inhabited, BEq

inductive wf_loadop_ : valtype → loadop_ → Prop where
  | loadop__case_0 (v_valtype : valtype) (v_Inn : Inn) (var_x : loadop_Inn) : wf_loadop_Inn v_Inn var_x → v_valtype == (valtype_Inn v_Inn) → wf_loadop_ v_valtype (.mk_loadop__0 v_Inn var_x)


def proj_loadop__0 (var_x : loadop_) : loadop_Inn :=
  match var_x with
  | .mk_loadop__0 v_Inn var_x => var_x

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
  | instr_case_0 : wf_instr .NOP
  | instr_case_1 : wf_instr .UNREACHABLE
  | instr_case_2 : wf_instr .DROP
  | instr_case_3 : wf_instr .SELECT
  | instr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → wf_instr (.BLOCK v_blocktype instr_lst)
  | instr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → wf_instr (.LOOP v_blocktype instr_lst)
  | instr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → ∀ instr_lst_0_elem ∈ instr_lst_0_lst, wf_instr instr_lst_0_elem → wf_instr (.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | instr_case_7 (v_labelidx : labelidx) : wf_uN 32 v_labelidx → wf_instr (.BR v_labelidx)
  | instr_case_8 (v_labelidx : labelidx) : wf_uN 32 v_labelidx → wf_instr (.BR_IF v_labelidx)
  | instr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) : ∀ v_labelidx_elem ∈ labelidx_lst, wf_uN 32 v_labelidx_elem → wf_uN 32 v_labelidx → wf_instr (.BR_TABLE labelidx_lst v_labelidx)
  | instr_case_10 (v_funcidx : funcidx) : wf_uN 32 v_funcidx → wf_instr (.CALL v_funcidx)
  | instr_case_11 (v_typeidx : typeidx) : wf_uN 32 v_typeidx → wf_instr (.CALL_INDIRECT v_typeidx)
  | instr_case_12 : wf_instr .RETURN
  | instr_case_13 (v_valtype : valtype) (var_0 : val_) : wf_val_ v_valtype var_0 → wf_instr (.CONST v_valtype var_0)
  | instr_case_14 (v_valtype : valtype) (var_0 : unop_) : wf_unop_ v_valtype var_0 → wf_instr (.UNOP v_valtype var_0)
  | instr_case_15 (v_valtype : valtype) (var_0 : binop_) : wf_binop_ v_valtype var_0 → wf_instr (.BINOP v_valtype var_0)
  | instr_case_16 (v_valtype : valtype) (var_0 : testop_) : wf_testop_ v_valtype var_0 → wf_instr (.TESTOP v_valtype var_0)
  | instr_case_17 (v_valtype : valtype) (var_0 : relop_) : wf_relop_ v_valtype var_0 → wf_instr (.RELOP v_valtype var_0)
  | instr_case_18 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : valtype_1 != valtype_2 → wf_instr (.CVTOP valtype_1 valtype_2 v_cvtop)
  | instr_case_19 (v_localidx : localidx) : wf_uN 32 v_localidx → wf_instr (.LOCAL_GET v_localidx)
  | instr_case_20 (v_localidx : localidx) : wf_uN 32 v_localidx → wf_instr (.LOCAL_SET v_localidx)
  | instr_case_21 (v_localidx : localidx) : wf_uN 32 v_localidx → wf_instr (.LOCAL_TEE v_localidx)
  | instr_case_22 (v_globalidx : globalidx) : wf_uN 32 v_globalidx → wf_instr (.GLOBAL_GET v_globalidx)
  | instr_case_23 (v_globalidx : globalidx) : wf_uN 32 v_globalidx → wf_instr (.GLOBAL_SET v_globalidx)
  | instr_case_24 (v_valtype : valtype) (var_0_opt : Option loadop_) (v_memarg : memarg) : ∀ var_0_elem ∈ Option.toList var_0_opt, wf_loadop_ v_valtype var_0_elem → wf_memarg v_memarg → wf_instr (.LOAD v_valtype var_0_opt v_memarg)
  | instr_case_25 (Inn_opt : Option Inn) (valtype_opt : Option valtype) (v_valtype : valtype) (sz_opt : Option sz) (v_memarg : memarg) : ∀ v_sz_elem ∈ Option.toList sz_opt, wf_sz v_sz_elem → wf_memarg v_memarg → ((Inn_opt == none) ↔ (sz_opt == none)) → ((Inn_opt == none) ↔ (valtype_opt == none)) → ∀ __iter_tuple ∈ Option.toList Inn_opt |>.zip (Option.toList sz_opt) |>.zip (Option.toList valtype_opt), ((__iter_tuple.2) == (valtype_Inn (__iter_tuple.1.1))) && ((proj_sz_0 (__iter_tuple.1.2)) < (size (valtype_Inn (__iter_tuple.1.1)))) → wf_instr (.STORE v_valtype sz_opt v_memarg)
  | instr_case_26 : wf_instr .MEMORY_SIZE
  | instr_case_27 : wf_instr .MEMORY_GROW


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
  | func_case_0 (v_typeidx : typeidx) (local_lst : List «local») (v_expr : expr) : wf_uN 32 v_typeidx → ∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem → wf_func (.FUNC v_typeidx local_lst v_expr)


inductive global : Type where
  | GLOBAL (v_globaltype : globaltype) (v_expr : expr) : global
deriving Inhabited, BEq

inductive wf_global : global → Prop where
  | global_case_0 (v_globaltype : globaltype) (v_expr : expr) : ∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem → wf_global (.GLOBAL v_globaltype v_expr)


inductive table : Type where
  | TABLE (v_tabletype : tabletype) : table
deriving Inhabited, BEq

inductive wf_table : table → Prop where
  | table_case_0 (v_tabletype : tabletype) : wf_limits v_tabletype → wf_table (.TABLE v_tabletype)


inductive mem : Type where
  | MEMORY (v_memtype : memtype) : mem
deriving Inhabited, BEq

inductive wf_mem : mem → Prop where
  | mem_case_0 (v_memtype : memtype) : wf_limits v_memtype → wf_mem (.MEMORY v_memtype)


inductive elem : Type where
  | ELEM (v_expr : expr) (funcidx_lst : List funcidx) : elem
deriving Inhabited, BEq

inductive wf_elem : elem → Prop where
  | elem_case_0 (v_expr : expr) (funcidx_lst : List funcidx) : ∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem → ∀ v_funcidx_elem ∈ funcidx_lst, wf_uN 32 v_funcidx_elem → wf_elem (.ELEM v_expr funcidx_lst)


inductive data : Type where
  | DATA (v_expr : expr) (byte_lst : List byte) : data
deriving Inhabited, BEq

inductive wf_data : data → Prop where
  | data_case_0 (v_expr : expr) (byte_lst : List byte) : ∀ v_expr_elem ∈ v_expr, wf_instr v_expr_elem → ∀ v_byte_elem ∈ byte_lst, wf_byte v_byte_elem → wf_data (.DATA v_expr byte_lst)


inductive start : Type where
  | START (v_funcidx : funcidx) : start
deriving Inhabited, BEq

inductive wf_start : start → Prop where
  | start_case_0 (v_funcidx : funcidx) : wf_uN 32 v_funcidx → wf_start (.START v_funcidx)


inductive externidx : Type where
  | FUNC (v_funcidx : funcidx) : externidx
  | GLOBAL (v_globalidx : globalidx) : externidx
  | TABLE (v_tableidx : tableidx) : externidx
  | MEM (v_memidx : memidx) : externidx
deriving Inhabited, BEq

inductive wf_externidx : externidx → Prop where
  | externidx_case_0 (v_funcidx : funcidx) : wf_uN 32 v_funcidx → wf_externidx (.FUNC v_funcidx)
  | externidx_case_1 (v_globalidx : globalidx) : wf_uN 32 v_globalidx → wf_externidx (.GLOBAL v_globalidx)
  | externidx_case_2 (v_tableidx : tableidx) : wf_uN 32 v_tableidx → wf_externidx (.TABLE v_tableidx)
  | externidx_case_3 (v_memidx : memidx) : wf_uN 32 v_memidx → wf_externidx (.MEM v_memidx)


inductive «export» : Type where
  | EXPORT (v_name : name) (v_externidx : externidx) : «export»
deriving Inhabited, BEq

inductive wf_export : «export» → Prop where
  | export_case_0 (v_name : name) (v_externidx : externidx) : wf_name v_name → wf_externidx v_externidx → wf_export (.EXPORT v_name v_externidx)


inductive «import» : Type where
  | IMPORT (v_name_0 : name) (v_name_1 : name) (v_externtype : externtype) : «import»
deriving Inhabited, BEq

inductive wf_import : «import» → Prop where
  | import_case_0 (v_name : name) (name_0 : name) (v_externtype : externtype) : wf_name v_name → wf_name name_0 → wf_externtype v_externtype → wf_import (.IMPORT v_name name_0 v_externtype)


inductive module : Type where
  | MODULE (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») : module
deriving Inhabited, BEq

inductive wf_module : module → Prop where
  | module_case_0 (type_lst : List type) (import_lst : List «import») (func_lst : List func) (global_lst : List global) (table_lst : List table) (mem_lst : List mem) (elem_lst : List elem) (data_lst : List data) (start_opt : Option start) (export_lst : List «export») : ∀ v_import_elem ∈ import_lst, wf_import v_import_elem → ∀ v_func_elem ∈ func_lst, wf_func v_func_elem → ∀ v_global_elem ∈ global_lst, wf_global v_global_elem → ∀ v_table_elem ∈ table_lst, wf_table v_table_elem → ∀ v_mem_elem ∈ mem_lst, wf_mem v_mem_elem → ∀ v_elem_elem ∈ elem_lst, wf_elem v_elem_elem → ∀ v_data_elem ∈ data_lst, wf_data v_data_elem → ∀ v_start_elem ∈ Option.toList start_opt, wf_start v_start_elem → ∀ v_export_elem ∈ export_lst, wf_export v_export_elem → wf_module (.MODULE type_lst import_lst func_lst global_lst table_lst mem_lst elem_lst data_lst start_opt export_lst)


inductive fun_funcsxt : List externtype → List functype → Prop where
  | fun_funcsxt_case_0 : fun_funcsxt [] []
  | fun_funcsxt_case_1 (ft : functype) (xt_lst : List externtype) (var_0 : List functype) : fun_funcsxt xt_lst var_0 → fun_funcsxt ([.FUNC ft] ++ xt_lst) ([ft] ++ var_0)
  | fun_funcsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List functype) : fun_funcsxt xt_lst var_0 → fun_funcsxt ([v_externtype] ++ xt_lst) var_0


inductive fun_globalsxt : List externtype → List globaltype → Prop where
  | fun_globalsxt_case_0 : fun_globalsxt [] []
  | fun_globalsxt_case_1 (gt : globaltype) (xt_lst : List externtype) (var_0 : List globaltype) : fun_globalsxt xt_lst var_0 → fun_globalsxt ([.GLOBAL gt] ++ xt_lst) ([gt] ++ var_0)
  | fun_globalsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List globaltype) : fun_globalsxt xt_lst var_0 → fun_globalsxt ([v_externtype] ++ xt_lst) var_0


inductive fun_tablesxt : List externtype → List tabletype → Prop where
  | fun_tablesxt_case_0 : fun_tablesxt [] []
  | fun_tablesxt_case_1 (tt : limits) (xt_lst : List externtype) (var_0 : List tabletype) : fun_tablesxt xt_lst var_0 → fun_tablesxt ([.TABLE tt] ++ xt_lst) ([tt] ++ var_0)
  | fun_tablesxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List tabletype) : fun_tablesxt xt_lst var_0 → fun_tablesxt ([v_externtype] ++ xt_lst) var_0


inductive tablesxt_is_wf : List externtype → List tabletype → Prop where
  | tablesxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List tabletype) (var_0 : List tabletype) : fun_tablesxt var_0_lst var_0 → ∀ var_0_elem ∈ var_0_lst, wf_externtype var_0_elem → ret_val_lst == var_0 → ∀ ret_val_elem ∈ ret_val_lst, wf_limits ret_val_elem → tablesxt_is_wf var_0_lst ret_val_lst


inductive fun_memsxt : List externtype → List memtype → Prop where
  | fun_memsxt_case_0 : fun_memsxt [] []
  | fun_memsxt_case_1 (mt : limits) (xt_lst : List externtype) (var_0 : List memtype) : fun_memsxt xt_lst var_0 → fun_memsxt ([.MEM mt] ++ xt_lst) ([mt] ++ var_0)
  | fun_memsxt_case_2 (v_externtype : externtype) (xt_lst : List externtype) (var_0 : List memtype) : fun_memsxt xt_lst var_0 → fun_memsxt ([v_externtype] ++ xt_lst) var_0


inductive memsxt_is_wf : List externtype → List memtype → Prop where
  | memsxt_is_wf_0 (var_0_lst : List externtype) (ret_val_lst : List memtype) (var_0 : List memtype) : fun_memsxt var_0_lst var_0 → ∀ var_0_elem ∈ var_0_lst, wf_externtype var_0_elem → ret_val_lst == var_0 → ∀ ret_val_elem ∈ ret_val_lst, wf_limits ret_val_elem → memsxt_is_wf var_0_lst ret_val_lst


def memarg0 : memarg :=
  {
    ALIGN := .mk_uN 0
    OFFSET := .mk_uN 0
  }

inductive memarg0_is_wf : memarg → Prop where
  | memarg0_is_wf_0 (ret_val : memarg) : ret_val == memarg0 → wf_memarg ret_val → memarg0_is_wf ret_val


def nat_of_bool (v_bool : Bool) : Nat :=
  match v_bool with
  | false => 0
  | true => 1

opaque truncz (rat : Rat) : Int := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fun_signed_ : N → Nat → Int → Prop where
  | fun_signed__case_0 (v_N : Nat) (i : Nat) : i < (2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) → fun_signed_ v_N i (i : Int)
  | fun_signed__case_1 (v_N : Nat) (i : Nat) : ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) ≤ i) && (i < (2 ^ v_N)) → fun_signed_ v_N i ((i : Int) - ((2 ^ v_N) : Int))


inductive fun_inv_signed_ : N → Int → Nat → Prop where
  | fun_inv_signed__case_0 (v_N : Nat) (i : Int) : ((0 : Int) ≤ i) && (i < ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) → fun_inv_signed_ v_N i (Int.toNat i)
  | fun_inv_signed__case_1 (v_N : Nat) (i : Int) : ((- ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Int)) ≤ i) && (i < (0 : Int)) → fun_inv_signed_ v_N i (Int.toNat (i + ((2 ^ v_N) : Int)))


opaque fabs_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fabs__is_wf : N → fN → List fN → Prop where
  | fabs__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (fabs_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fabs__is_wf v_N v_fN ret_val_lst


opaque fceil_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fceil__is_wf : N → fN → List fN → Prop where
  | fceil__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (fceil_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fceil__is_wf v_N v_fN ret_val_lst


opaque ffloor_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ffloor__is_wf : N → fN → List fN → Prop where
  | ffloor__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (ffloor_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → ffloor__is_wf v_N v_fN ret_val_lst


opaque fnearest_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fnearest__is_wf : N → fN → List fN → Prop where
  | fnearest__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (fnearest_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fnearest__is_wf v_N v_fN ret_val_lst


opaque fneg_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fneg__is_wf : N → fN → List fN → Prop where
  | fneg__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (fneg_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fneg__is_wf v_N v_fN ret_val_lst


opaque fsqrt_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsqrt__is_wf : N → fN → List fN → Prop where
  | fsqrt__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (fsqrt_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fsqrt__is_wf v_N v_fN ret_val_lst


opaque ftrunc_ (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ftrunc__is_wf : N → fN → List fN → Prop where
  | ftrunc__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → ret_val_lst == (ftrunc_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → ftrunc__is_wf v_N v_fN ret_val_lst


opaque iclz_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iclz__is_wf : N → iN → iN → Prop where
  | iclz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : wf_uN v_N v_iN → ret_val == (iclz_ v_N v_iN) → wf_uN v_N ret_val → iclz__is_wf v_N v_iN ret_val


opaque ictz_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ictz__is_wf : N → iN → iN → Prop where
  | ictz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : wf_uN v_N v_iN → ret_val == (ictz_ v_N v_iN) → wf_uN v_N ret_val → ictz__is_wf v_N v_iN ret_val


opaque ipopcnt_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ipopcnt__is_wf : N → iN → iN → Prop where
  | ipopcnt__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : wf_uN v_N v_iN → ret_val == (ipopcnt_ v_N v_iN) → wf_uN v_N ret_val → ipopcnt__is_wf v_N v_iN ret_val


def fun_unop_ (v_valtype : valtype) (v_unop_ : unop_) (v_val_ : val_) : Option (List val_) :=
  match v_valtype, v_unop_, v_val_ with
  | .I32, .mk_unop__0 .I32 .CLZ, .mk_val__0 .I32 v_iN => some [.mk_val__0 .I32 (iclz_ (size (valtype_Inn .I32)) v_iN)]
  | .I64, .mk_unop__0 .I64 .CLZ, .mk_val__0 .I64 v_iN => some [.mk_val__0 .I64 (iclz_ (size (valtype_Inn .I64)) v_iN)]
  | .I32, .mk_unop__0 .I32 .CTZ, .mk_val__0 .I32 v_iN => some [.mk_val__0 .I32 (ictz_ (size (valtype_Inn .I32)) v_iN)]
  | .I64, .mk_unop__0 .I64 .CTZ, .mk_val__0 .I64 v_iN => some [.mk_val__0 .I64 (ictz_ (size (valtype_Inn .I64)) v_iN)]
  | .I32, .mk_unop__0 .I32 .POPCNT, .mk_val__0 .I32 v_iN => some [.mk_val__0 .I32 (ipopcnt_ (size (valtype_Inn .I32)) v_iN)]
  | .I64, .mk_unop__0 .I64 .POPCNT, .mk_val__0 .I64 v_iN => some [.mk_val__0 .I64 (ipopcnt_ (size (valtype_Inn .I64)) v_iN)]
  | .F32, .mk_unop__1 .F32 .ABS, .mk_val__1 .F32 v_fN => some (fabs_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_1_elem => .mk_val__1 .F32 iter_0_1_elem))
  | .F64, .mk_unop__1 .F64 .ABS, .mk_val__1 .F64 v_fN => some (fabs_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_2_elem => .mk_val__1 .F64 iter_0_2_elem))
  | .F32, .mk_unop__1 .F32 .NEG, .mk_val__1 .F32 v_fN => some (fneg_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_3_elem => .mk_val__1 .F32 iter_0_3_elem))
  | .F64, .mk_unop__1 .F64 .NEG, .mk_val__1 .F64 v_fN => some (fneg_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_4_elem => .mk_val__1 .F64 iter_0_4_elem))
  | .F32, .mk_unop__1 .F32 .SQRT, .mk_val__1 .F32 v_fN => some (fsqrt_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_5_elem => .mk_val__1 .F32 iter_0_5_elem))
  | .F64, .mk_unop__1 .F64 .SQRT, .mk_val__1 .F64 v_fN => some (fsqrt_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_6_elem => .mk_val__1 .F64 iter_0_6_elem))
  | .F32, .mk_unop__1 .F32 .CEIL, .mk_val__1 .F32 v_fN => some (fceil_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_7_elem => .mk_val__1 .F32 iter_0_7_elem))
  | .F64, .mk_unop__1 .F64 .CEIL, .mk_val__1 .F64 v_fN => some (fceil_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_8_elem => .mk_val__1 .F64 iter_0_8_elem))
  | .F32, .mk_unop__1 .F32 .FLOOR, .mk_val__1 .F32 v_fN => some (ffloor_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_9_elem => .mk_val__1 .F32 iter_0_9_elem))
  | .F64, .mk_unop__1 .F64 .FLOOR, .mk_val__1 .F64 v_fN => some (ffloor_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_10_elem => .mk_val__1 .F64 iter_0_10_elem))
  | .F32, .mk_unop__1 .F32 .TRUNC, .mk_val__1 .F32 v_fN => some (ftrunc_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_11_elem => .mk_val__1 .F32 iter_0_11_elem))
  | .F64, .mk_unop__1 .F64 .TRUNC, .mk_val__1 .F64 v_fN => some (ftrunc_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_12_elem => .mk_val__1 .F64 iter_0_12_elem))
  | .F32, .mk_unop__1 .F32 .NEAREST, .mk_val__1 .F32 v_fN => some (fnearest_ (size (valtype_Fnn .F32)) v_fN |>.map (fun iter_0_13_elem => .mk_val__1 .F32 iter_0_13_elem))
  | .F64, .mk_unop__1 .F64 .NEAREST, .mk_val__1 .F64 v_fN => some (fnearest_ (size (valtype_Fnn .F64)) v_fN |>.map (fun iter_0_14_elem => .mk_val__1 .F64 iter_0_14_elem))
  | _, _, _ => none

inductive unop__is_wf : valtype → unop_ → val_ → List val_ → Prop where
  | unop__is_wf_0 (v_valtype : valtype) (v_unop_ : unop_) (v_val_ : val_) (ret_val_lst : List val_) : wf_unop_ v_valtype v_unop_ → wf_val_ v_valtype v_val_ → (fun_unop_ v_valtype v_unop_ v_val_) != none → ret_val_lst == (Option.get! (fun_unop_ v_valtype v_unop_ v_val_)) → ∀ ret_val_elem ∈ ret_val_lst, wf_val_ v_valtype ret_val_elem → unop__is_wf v_valtype v_unop_ v_val_ ret_val_lst


opaque fadd_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fadd__is_wf : N → fN → fN → List fN → Prop where
  | fadd__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fadd_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fadd__is_wf v_N v_fN fN_0 ret_val_lst


opaque fcopysign_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fcopysign__is_wf : N → fN → fN → List fN → Prop where
  | fcopysign__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fcopysign_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fcopysign__is_wf v_N v_fN fN_0 ret_val_lst


opaque fdiv_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fdiv__is_wf : N → fN → fN → List fN → Prop where
  | fdiv__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fdiv_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fdiv__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmax_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmax__is_wf : N → fN → fN → List fN → Prop where
  | fmax__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fmax_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fmax__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmin_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmin__is_wf : N → fN → fN → List fN → Prop where
  | fmin__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fmin_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fmin__is_wf v_N v_fN fN_0 ret_val_lst


opaque fmul_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fmul__is_wf : N → fN → fN → List fN → Prop where
  | fmul__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fmul_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fmul__is_wf v_N v_fN fN_0 ret_val_lst


opaque fsub_ (v_N : N) (v_fN : fN) (fN_0 : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fsub__is_wf : N → fN → fN → List fN → Prop where
  | fsub__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val_lst : List fN) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val_lst == (fsub_ v_N v_fN fN_0) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → fsub__is_wf v_N v_fN fN_0 ret_val_lst


def iadd_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  .mk_uN (((proj_uN_0 v_iN) + (proj_uN_0 iN_0)) % (2 ^ v_N))

inductive iadd__is_wf : N → iN → iN → iN → Prop where
  | iadd__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (iadd_ v_N v_iN iN_0) → wf_uN v_N ret_val → iadd__is_wf v_N v_iN iN_0 ret_val


opaque iand_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive iand__is_wf : N → iN → iN → iN → Prop where
  | iand__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (iand_ v_N v_iN iN_0) → wf_uN v_N ret_val → iand__is_wf v_N v_iN iN_0 ret_val


inductive fun_idiv_ : N → sx → iN → iN → Option iN → Prop where
  | fun_idiv__case_0 (v_N : Nat) (i_1 : uN) : fun_idiv_ v_N .U i_1 (.mk_uN 0) none
  | fun_idiv__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_idiv_ v_N .U i_1 i_2 (some (.mk_uN (Int.toNat (truncz (((proj_uN_0 i_1) : Rat) / ((proj_uN_0 i_2) : Rat))))))
  | fun_idiv__case_2 (v_N : Nat) (i_1 : uN) : fun_idiv_ v_N .S i_1 (.mk_uN 0) none
  | fun_idiv__case_3 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : fun_signed_ v_N (proj_uN_0 i_2) var_1 → fun_signed_ v_N (proj_uN_0 i_1) var_0 → ((var_0 : Rat) / (var_1 : Rat)) == ((2 ^ (Int.toNat ((v_N : Int) - (1 : Int)))) : Rat) → fun_idiv_ v_N .S i_1 i_2 none
  | fun_idiv__case_4 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_2 : Int) (var_1 : Int) (var_0 : Nat) : fun_signed_ v_N (proj_uN_0 i_2) var_2 → fun_signed_ v_N (proj_uN_0 i_1) var_1 → fun_inv_signed_ v_N (truncz ((var_1 : Rat) / (var_2 : Rat))) var_0 → fun_idiv_ v_N .S i_1 i_2 (some (.mk_uN var_0))


inductive idiv__is_wf : N → sx → iN → iN → Option iN → Prop where
  | idiv__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) : fun_idiv_ v_N v_sx v_iN iN_0 var_0 → wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val_opt == var_0 → ∀ ret_val_elem ∈ Option.toList ret_val_opt, wf_uN v_N ret_val_elem → idiv__is_wf v_N v_sx v_iN iN_0 ret_val_opt


def imul_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  .mk_uN (((proj_uN_0 v_iN) * (proj_uN_0 iN_0)) % (2 ^ v_N))

inductive imul__is_wf : N → iN → iN → iN → Prop where
  | imul__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (imul_ v_N v_iN iN_0) → wf_uN v_N ret_val → imul__is_wf v_N v_iN iN_0 ret_val


opaque ior_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ior__is_wf : N → iN → iN → iN → Prop where
  | ior__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (ior_ v_N v_iN iN_0) → wf_uN v_N ret_val → ior__is_wf v_N v_iN iN_0 ret_val


inductive fun_irem_ : N → sx → iN → iN → Option iN → Prop where
  | fun_irem__case_0 (v_N : Nat) (i_1 : uN) : fun_irem_ v_N .U i_1 (.mk_uN 0) none
  | fun_irem__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_irem_ v_N .U i_1 i_2 (some (.mk_uN (Int.toNat (((proj_uN_0 i_1) : Int) - (((proj_uN_0 i_2) * (Int.toNat (truncz (((proj_uN_0 i_1) : Rat) / ((proj_uN_0 i_2) : Rat))))) : Int)))))
  | fun_irem__case_2 (v_N : Nat) (i_1 : uN) : fun_irem_ v_N .S i_1 (.mk_uN 0) none
  | fun_irem__case_3 (v_N : Nat) (i_1 : uN) (i_2 : uN) (j_1 : Int) (j_2 : Int) (var_2 : Int) (var_1 : Int) (var_0 : Nat) : fun_signed_ v_N (proj_uN_0 i_2) var_2 → fun_signed_ v_N (proj_uN_0 i_1) var_1 → fun_inv_signed_ v_N (j_1 - (j_2 * (truncz ((j_1 : Rat) / (j_2 : Rat))))) var_0 → (j_1 == var_1) && (j_2 == var_2) → fun_irem_ v_N .S i_1 i_2 (some (.mk_uN var_0))


inductive irem__is_wf : N → sx → iN → iN → Option iN → Prop where
  | irem__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val_opt : Option iN) (var_0 : Option iN) : fun_irem_ v_N v_sx v_iN iN_0 var_0 → wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val_opt == var_0 → ∀ ret_val_elem ∈ Option.toList ret_val_opt, wf_uN v_N ret_val_elem → irem__is_wf v_N v_sx v_iN iN_0 ret_val_opt


opaque irotl_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irotl__is_wf : N → iN → iN → iN → Prop where
  | irotl__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (irotl_ v_N v_iN iN_0) → wf_uN v_N ret_val → irotl__is_wf v_N v_iN iN_0 ret_val


opaque irotr_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive irotr__is_wf : N → iN → iN → iN → Prop where
  | irotr__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (irotr_ v_N v_iN iN_0) → wf_uN v_N ret_val → irotr__is_wf v_N v_iN iN_0 ret_val


opaque ishl_ (v_N : N) (v_iN : iN) (v_u32 : u32) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ishl__is_wf : N → iN → u32 → iN → Prop where
  | ishl__is_wf_0 (v_N : N) (v_iN : iN) (v_u32 : u32) (ret_val : iN) : wf_uN v_N v_iN → wf_uN 32 v_u32 → ret_val == (ishl_ v_N v_iN v_u32) → wf_uN v_N ret_val → ishl__is_wf v_N v_iN v_u32 ret_val


opaque ishr_ (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ishr__is_wf : N → sx → iN → u32 → iN → Prop where
  | ishr__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (v_u32 : u32) (ret_val : iN) : wf_uN v_N v_iN → wf_uN 32 v_u32 → ret_val == (ishr_ v_N v_sx v_iN v_u32) → wf_uN v_N ret_val → ishr__is_wf v_N v_sx v_iN v_u32 ret_val


def isub_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN :=
  .mk_uN (Int.toNat (((((2 ^ v_N) + (proj_uN_0 v_iN)) : Int) - ((proj_uN_0 iN_0) : Int)) % ((2 ^ v_N) : Int)))

inductive isub__is_wf : N → iN → iN → iN → Prop where
  | isub__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (isub_ v_N v_iN iN_0) → wf_uN v_N ret_val → isub__is_wf v_N v_iN iN_0 ret_val


opaque ixor_ (v_N : N) (v_iN : iN) (iN_0 : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ixor__is_wf : N → iN → iN → iN → Prop where
  | ixor__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : iN) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (ixor_ v_N v_iN iN_0) → wf_uN v_N ret_val → ixor__is_wf v_N v_iN iN_0 ret_val


inductive fun_binop_ : valtype → binop_ → val_ → val_ → List val_ → Prop where
  | fun_binop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .ADD) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (iadd_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .ADD) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (iadd_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .SUB) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (isub_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .SUB) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (isub_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_4 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .MUL) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (imul_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_5 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .MUL) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (imul_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : fun_idiv_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0 → fun_binop_ .I32 (.mk_binop__0 .I32 (.DIV v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_15_elem => .mk_val__0 .I32 iter_0_15_elem)))
  | fun_binop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : fun_idiv_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0 → fun_binop_ .I64 (.mk_binop__0 .I64 (.DIV v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_16_elem => .mk_val__0 .I64 iter_0_16_elem)))
  | fun_binop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : fun_irem_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0 → fun_binop_ .I32 (.mk_binop__0 .I32 (.REM v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_17_elem => .mk_val__0 .I32 iter_0_17_elem)))
  | fun_binop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : Option iN) : fun_irem_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0 → fun_binop_ .I64 (.mk_binop__0 .I64 (.REM v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (list_ val_ (var_0 |>.map (fun iter_0_18_elem => .mk_val__0 .I64 iter_0_18_elem)))
  | fun_binop__case_10 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .AND) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (iand_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_11 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .AND) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (iand_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_12 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .OR) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (ior_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_13 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .OR) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (ior_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_14 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .XOR) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (ixor_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_15 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .XOR) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (ixor_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_16 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .SHL) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (ishl_ (size (valtype_Inn .I32)) iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_17 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .SHL) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (ishl_ (size (valtype_Inn .I64)) iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_18 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 (.SHR v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (ishr_ (size (valtype_Inn .I32)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_19 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 (.SHR v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (ishr_ (size (valtype_Inn .I64)) v_sx iN_1 (.mk_uN (proj_uN_0 iN_2)))]
  | fun_binop__case_20 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .ROTL) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (irotl_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_21 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .ROTL) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (irotl_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_22 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I32 (.mk_binop__0 .I32 .ROTR) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) [.mk_val__0 .I32 (irotr_ (size (valtype_Inn .I32)) iN_1 iN_2)]
  | fun_binop__case_23 (iN_1 : uN) (iN_2 : uN) : fun_binop_ .I64 (.mk_binop__0 .I64 .ROTR) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) [.mk_val__0 .I64 (irotr_ (size (valtype_Inn .I64)) iN_1 iN_2)]
  | fun_binop__case_24 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .ADD) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fadd_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_19_elem => .mk_val__1 .F32 iter_0_19_elem))
  | fun_binop__case_25 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .ADD) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fadd_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_20_elem => .mk_val__1 .F64 iter_0_20_elem))
  | fun_binop__case_26 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .SUB) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fsub_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_21_elem => .mk_val__1 .F32 iter_0_21_elem))
  | fun_binop__case_27 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .SUB) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fsub_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_22_elem => .mk_val__1 .F64 iter_0_22_elem))
  | fun_binop__case_28 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .MUL) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fmul_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_23_elem => .mk_val__1 .F32 iter_0_23_elem))
  | fun_binop__case_29 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .MUL) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fmul_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_24_elem => .mk_val__1 .F64 iter_0_24_elem))
  | fun_binop__case_30 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .DIV) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fdiv_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_25_elem => .mk_val__1 .F32 iter_0_25_elem))
  | fun_binop__case_31 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .DIV) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fdiv_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_26_elem => .mk_val__1 .F64 iter_0_26_elem))
  | fun_binop__case_32 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .MIN) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fmin_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_27_elem => .mk_val__1 .F32 iter_0_27_elem))
  | fun_binop__case_33 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .MIN) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fmin_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_28_elem => .mk_val__1 .F64 iter_0_28_elem))
  | fun_binop__case_34 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .MAX) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fmax_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_29_elem => .mk_val__1 .F32 iter_0_29_elem))
  | fun_binop__case_35 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .MAX) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fmax_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_30_elem => .mk_val__1 .F64 iter_0_30_elem))
  | fun_binop__case_36 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F32 (.mk_binop__1 .F32 .COPYSIGN) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (fcopysign_ (size (valtype_Fnn .F32)) fN_1 fN_2 |>.map (fun iter_0_31_elem => .mk_val__1 .F32 iter_0_31_elem))
  | fun_binop__case_37 (fN_1 : fN) (fN_2 : fN) : fun_binop_ .F64 (.mk_binop__1 .F64 .COPYSIGN) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (fcopysign_ (size (valtype_Fnn .F64)) fN_1 fN_2 |>.map (fun iter_0_32_elem => .mk_val__1 .F64 iter_0_32_elem))


inductive binop__is_wf : valtype → binop_ → val_ → val_ → List val_ → Prop where
  | binop__is_wf_0 (v_valtype : valtype) (v_binop_ : binop_) (v_val_ : val_) (val__0 : val_) (ret_val_lst : List val_) (var_0 : List val_) : fun_binop_ v_valtype v_binop_ v_val_ val__0 var_0 → wf_binop_ v_valtype v_binop_ → wf_val_ v_valtype v_val_ → wf_val_ v_valtype val__0 → ret_val_lst == var_0 → ∀ ret_val_elem ∈ ret_val_lst, wf_val_ v_valtype ret_val_elem → binop__is_wf v_valtype v_binop_ v_val_ val__0 ret_val_lst


def ieqz_ (v_N : N) (v_iN : iN) : u32 :=
  .mk_uN (nat_of_bool ((proj_uN_0 v_iN) == 0))

inductive ieqz__is_wf : N → iN → u32 → Prop where
  | ieqz__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) : wf_uN v_N v_iN → ret_val == (ieqz_ v_N v_iN) → wf_uN 32 ret_val → ieqz__is_wf v_N v_iN ret_val


def fun_testop_ (v_valtype : valtype) (v_testop_ : testop_) (v_val_ : val_) : Option val_ :=
  match v_valtype, v_testop_, v_val_ with
  | .I32, .mk_testop__0 .I32 .EQZ, .mk_val__0 .I32 v_iN => some (.mk_val__0 .I32 (ieqz_ (size (valtype_Inn .I32)) v_iN))
  | .I64, .mk_testop__0 .I64 .EQZ, .mk_val__0 .I64 v_iN => some (.mk_val__0 .I32 (ieqz_ (size (valtype_Inn .I64)) v_iN))
  | _, _, _ => none

inductive testop__is_wf : valtype → testop_ → val_ → val_ → Prop where
  | testop__is_wf_0 (v_valtype : valtype) (v_testop_ : testop_) (v_val_ : val_) (ret_val : val_) : wf_testop_ v_valtype v_testop_ → wf_val_ v_valtype v_val_ → (fun_testop_ v_valtype v_testop_ v_val_) != none → ret_val == (Option.get! (fun_testop_ v_valtype v_testop_ v_val_)) → wf_val_ .I32 ret_val → testop__is_wf v_valtype v_testop_ v_val_ ret_val


opaque feq_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive feq__is_wf : N → fN → fN → u32 → Prop where
  | feq__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val == (feq_ v_N v_fN fN_0) → wf_uN 32 ret_val → feq__is_wf v_N v_fN fN_0 ret_val


opaque fge_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fge__is_wf : N → fN → fN → u32 → Prop where
  | fge__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val == (fge_ v_N v_fN fN_0) → wf_uN 32 ret_val → fge__is_wf v_N v_fN fN_0 ret_val


opaque fgt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fgt__is_wf : N → fN → fN → u32 → Prop where
  | fgt__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val == (fgt_ v_N v_fN fN_0) → wf_uN 32 ret_val → fgt__is_wf v_N v_fN fN_0 ret_val


opaque fle_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fle__is_wf : N → fN → fN → u32 → Prop where
  | fle__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val == (fle_ v_N v_fN fN_0) → wf_uN 32 ret_val → fle__is_wf v_N v_fN fN_0 ret_val


opaque flt_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive flt__is_wf : N → fN → fN → u32 → Prop where
  | flt__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val == (flt_ v_N v_fN fN_0) → wf_uN 32 ret_val → flt__is_wf v_N v_fN fN_0 ret_val


opaque fne_ (v_N : N) (v_fN : fN) (fN_0 : fN) : u32 := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fne__is_wf : N → fN → fN → u32 → Prop where
  | fne__is_wf_0 (v_N : N) (v_fN : fN) (fN_0 : fN) (ret_val : u32) : wf_fN v_N v_fN → wf_fN v_N fN_0 → ret_val == (fne_ v_N v_fN fN_0) → wf_uN 32 ret_val → fne__is_wf v_N v_fN fN_0 ret_val


def ieq_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  .mk_uN (nat_of_bool (v_iN == iN_0))

inductive ieq__is_wf : N → iN → iN → u32 → Prop where
  | ieq__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (ieq_ v_N v_iN iN_0) → wf_uN 32 ret_val → ieq__is_wf v_N v_iN iN_0 ret_val


inductive fun_ige_ : N → sx → iN → iN → u32 → Prop where
  | fun_ige__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ige_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) ≥ (proj_uN_0 i_2))))
  | fun_ige__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : fun_signed_ v_N (proj_uN_0 i_2) var_1 → fun_signed_ v_N (proj_uN_0 i_1) var_0 → fun_ige_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 ≥ var_1)))


inductive ige__is_wf : N → sx → iN → iN → u32 → Prop where
  | ige__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : fun_ige_ v_N v_sx v_iN iN_0 var_0 → wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == var_0 → wf_uN 32 ret_val → ige__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_igt_ : N → sx → iN → iN → u32 → Prop where
  | fun_igt__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_igt_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) > (proj_uN_0 i_2))))
  | fun_igt__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : fun_signed_ v_N (proj_uN_0 i_2) var_1 → fun_signed_ v_N (proj_uN_0 i_1) var_0 → fun_igt_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 > var_1)))


inductive igt__is_wf : N → sx → iN → iN → u32 → Prop where
  | igt__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : fun_igt_ v_N v_sx v_iN iN_0 var_0 → wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == var_0 → wf_uN 32 ret_val → igt__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_ile_ : N → sx → iN → iN → u32 → Prop where
  | fun_ile__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ile_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) ≤ (proj_uN_0 i_2))))
  | fun_ile__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : fun_signed_ v_N (proj_uN_0 i_2) var_1 → fun_signed_ v_N (proj_uN_0 i_1) var_0 → fun_ile_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 ≤ var_1)))


inductive ile__is_wf : N → sx → iN → iN → u32 → Prop where
  | ile__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : fun_ile_ v_N v_sx v_iN iN_0 var_0 → wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == var_0 → wf_uN 32 ret_val → ile__is_wf v_N v_sx v_iN iN_0 ret_val


inductive fun_ilt_ : N → sx → iN → iN → u32 → Prop where
  | fun_ilt__case_0 (v_N : Nat) (i_1 : uN) (i_2 : uN) : fun_ilt_ v_N .U i_1 i_2 (.mk_uN (nat_of_bool ((proj_uN_0 i_1) < (proj_uN_0 i_2))))
  | fun_ilt__case_1 (v_N : Nat) (i_1 : uN) (i_2 : uN) (var_1 : Int) (var_0 : Int) : fun_signed_ v_N (proj_uN_0 i_2) var_1 → fun_signed_ v_N (proj_uN_0 i_1) var_0 → fun_ilt_ v_N .S i_1 i_2 (.mk_uN (nat_of_bool (var_0 < var_1)))


inductive ilt__is_wf : N → sx → iN → iN → u32 → Prop where
  | ilt__is_wf_0 (v_N : N) (v_sx : sx) (v_iN : iN) (iN_0 : iN) (ret_val : u32) (var_0 : u32) : fun_ilt_ v_N v_sx v_iN iN_0 var_0 → wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == var_0 → wf_uN 32 ret_val → ilt__is_wf v_N v_sx v_iN iN_0 ret_val


def ine_ (v_N : N) (v_iN : iN) (iN_0 : iN) : u32 :=
  .mk_uN (nat_of_bool (v_iN != iN_0))

inductive ine__is_wf : N → iN → iN → u32 → Prop where
  | ine__is_wf_0 (v_N : N) (v_iN : iN) (iN_0 : iN) (ret_val : u32) : wf_uN v_N v_iN → wf_uN v_N iN_0 → ret_val == (ine_ v_N v_iN iN_0) → wf_uN 32 ret_val → ine__is_wf v_N v_iN iN_0 ret_val


inductive fun_relop_ : valtype → relop_ → val_ → val_ → val_ → Prop where
  | fun_relop__case_0 (iN_1 : uN) (iN_2 : uN) : fun_relop_ .I32 (.mk_relop__0 .I32 .EQ) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 (ieq_ (size (valtype_Inn .I32)) iN_1 iN_2))
  | fun_relop__case_1 (iN_1 : uN) (iN_2 : uN) : fun_relop_ .I64 (.mk_relop__0 .I64 .EQ) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 (ieq_ (size (valtype_Inn .I64)) iN_1 iN_2))
  | fun_relop__case_2 (iN_1 : uN) (iN_2 : uN) : fun_relop_ .I32 (.mk_relop__0 .I32 .NE) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 (ine_ (size (valtype_Inn .I32)) iN_1 iN_2))
  | fun_relop__case_3 (iN_1 : uN) (iN_2 : uN) : fun_relop_ .I64 (.mk_relop__0 .I64 .NE) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 (ine_ (size (valtype_Inn .I64)) iN_1 iN_2))
  | fun_relop__case_4 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_ilt_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I32 (.mk_relop__0 .I32 (.LT v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_5 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_ilt_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I64 (.mk_relop__0 .I64 (.LT v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_6 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_igt_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I32 (.mk_relop__0 .I32 (.GT v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_7 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_igt_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I64 (.mk_relop__0 .I64 (.GT v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_8 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_ile_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I32 (.mk_relop__0 .I32 (.LE v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_9 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_ile_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I64 (.mk_relop__0 .I64 (.LE v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_10 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_ige_ (size (valtype_Inn .I32)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I32 (.mk_relop__0 .I32 (.GE v_sx)) (.mk_val__0 .I32 iN_1) (.mk_val__0 .I32 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_11 (v_sx : sx) (iN_1 : uN) (iN_2 : uN) (var_0 : uN) : fun_ige_ (size (valtype_Inn .I64)) v_sx iN_1 iN_2 var_0 → fun_relop_ .I64 (.mk_relop__0 .I64 (.GE v_sx)) (.mk_val__0 .I64 iN_1) (.mk_val__0 .I64 iN_2) (.mk_val__0 .I32 var_0)
  | fun_relop__case_12 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F32 (.mk_relop__1 .F32 .EQ) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (feq_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_13 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F64 (.mk_relop__1 .F64 .EQ) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (feq_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_14 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F32 (.mk_relop__1 .F32 .NE) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fne_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_15 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F64 (.mk_relop__1 .F64 .NE) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fne_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_16 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F32 (.mk_relop__1 .F32 .LT) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (flt_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_17 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F64 (.mk_relop__1 .F64 .LT) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (flt_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_18 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F32 (.mk_relop__1 .F32 .GT) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fgt_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_19 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F64 (.mk_relop__1 .F64 .GT) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fgt_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_20 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F32 (.mk_relop__1 .F32 .LE) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fle_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_21 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F64 (.mk_relop__1 .F64 .LE) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fle_ (size (valtype_Fnn .F64)) fN_1 fN_2))
  | fun_relop__case_22 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F32 (.mk_relop__1 .F32 .GE) (.mk_val__1 .F32 fN_1) (.mk_val__1 .F32 fN_2) (.mk_val__0 .I32 (fge_ (size (valtype_Fnn .F32)) fN_1 fN_2))
  | fun_relop__case_23 (fN_1 : fN) (fN_2 : fN) : fun_relop_ .F64 (.mk_relop__1 .F64 .GE) (.mk_val__1 .F64 fN_1) (.mk_val__1 .F64 fN_2) (.mk_val__0 .I32 (fge_ (size (valtype_Fnn .F64)) fN_1 fN_2))


inductive relop__is_wf : valtype → relop_ → val_ → val_ → val_ → Prop where
  | relop__is_wf_0 (v_valtype : valtype) (v_relop_ : relop_) (v_val_ : val_) (val__0 : val_) (ret_val : val_) (var_0 : val_) : fun_relop_ v_valtype v_relop_ v_val_ val__0 var_0 → wf_relop_ v_valtype v_relop_ → wf_val_ v_valtype v_val_ → wf_val_ v_valtype val__0 → ret_val == var_0 → wf_val_ .I32 ret_val → relop__is_wf v_valtype v_relop_ v_val_ val__0 ret_val


opaque convert__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive convert___is_wf : M → N → sx → iN → fN → Prop where
  | convert___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : fN) : wf_uN v_M v_iN → ret_val == (convert__ v_M v_N v_sx v_iN) → wf_fN v_N ret_val → convert___is_wf v_M v_N v_sx v_iN ret_val


opaque demote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive demote___is_wf : M → N → fN → List fN → Prop where
  | demote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_M v_fN → ret_val_lst == (demote__ v_M v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → demote___is_wf v_M v_N v_fN ret_val_lst


opaque extend__ (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive extend___is_wf : M → N → sx → iN → iN → Prop where
  | extend___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_iN : iN) (ret_val : iN) : wf_uN v_M v_iN → ret_val == (extend__ v_M v_N v_sx v_iN) → wf_uN v_N ret_val → extend___is_wf v_M v_N v_sx v_iN ret_val


opaque promote__ (v_M : M) (v_N : N) (v_fN : fN) : List fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive promote___is_wf : M → N → fN → List fN → Prop where
  | promote___is_wf_0 (v_M : M) (v_N : N) (v_fN : fN) (ret_val_lst : List fN) : wf_fN v_M v_fN → ret_val_lst == (promote__ v_M v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_fN v_N ret_val_elem → promote___is_wf v_M v_N v_fN ret_val_lst


opaque reinterpret__ (valtype_1 : valtype) (valtype_2 : valtype) (v_val_ : val_) : val_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive reinterpret___is_wf : valtype → valtype → val_ → val_ → Prop where
  | reinterpret___is_wf_0 (valtype_1 : valtype) (valtype_2 : valtype) (v_val_ : val_) (ret_val : val_) : wf_val_ valtype_1 v_val_ → ret_val == (reinterpret__ valtype_1 valtype_2 v_val_) → wf_val_ valtype_2 ret_val → reinterpret___is_wf valtype_1 valtype_2 v_val_ ret_val


opaque trunc__ (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) : Option iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive trunc___is_wf : M → N → sx → fN → Option iN → Prop where
  | trunc___is_wf_0 (v_M : M) (v_N : N) (v_sx : sx) (v_fN : fN) (ret_val_opt : Option iN) : wf_fN v_M v_fN → ret_val_opt == (trunc__ v_M v_N v_sx v_fN) → ∀ ret_val_elem ∈ Option.toList ret_val_opt, wf_uN v_N ret_val_elem → trunc___is_wf v_M v_N v_sx v_fN ret_val_opt


opaque wrap__ (v_M : M) (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive wrap___is_wf : M → N → iN → iN → Prop where
  | wrap___is_wf_0 (v_M : M) (v_N : N) (v_iN : iN) (ret_val : iN) : wf_uN v_M v_iN → ret_val == (wrap__ v_M v_N v_iN) → wf_uN v_N ret_val → wrap___is_wf v_M v_N v_iN ret_val


inductive fun_cvtop__ : valtype → valtype → cvtop → val_ → List val_ → Prop where
  | fun_cvtop___case_0 (v_sx : sx) (v_iN : uN) : fun_cvtop__ .I32 .I64 (.EXTEND v_sx) (.mk_val__0 .I32 v_iN) [.mk_val__0 .I64 (extend__ 32 64 v_sx v_iN)]
  | fun_cvtop___case_1 (v_iN : uN) : fun_cvtop__ .I64 .I32 .WRAP (.mk_val__0 .I64 v_iN) [.mk_val__0 .I32 (wrap__ 64 32 v_iN)]
  | fun_cvtop___case_2 (v_sx : sx) (v_fN : fN) : fun_cvtop__ .F32 .I32 (.TRUNC v_sx) (.mk_val__1 .F32 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn .F32)) (size (valtype_Inn .I32)) v_sx v_fN |>.map (fun iter_0_33_elem => .mk_val__0 .I32 iter_0_33_elem)))
  | fun_cvtop___case_3 (v_sx : sx) (v_fN : fN) : fun_cvtop__ .F64 .I32 (.TRUNC v_sx) (.mk_val__1 .F64 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn .F64)) (size (valtype_Inn .I32)) v_sx v_fN |>.map (fun iter_0_34_elem => .mk_val__0 .I32 iter_0_34_elem)))
  | fun_cvtop___case_4 (v_sx : sx) (v_fN : fN) : fun_cvtop__ .F32 .I64 (.TRUNC v_sx) (.mk_val__1 .F32 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn .F32)) (size (valtype_Inn .I64)) v_sx v_fN |>.map (fun iter_0_35_elem => .mk_val__0 .I64 iter_0_35_elem)))
  | fun_cvtop___case_5 (v_sx : sx) (v_fN : fN) : fun_cvtop__ .F64 .I64 (.TRUNC v_sx) (.mk_val__1 .F64 v_fN) (list_ val_ (trunc__ (size (valtype_Fnn .F64)) (size (valtype_Inn .I64)) v_sx v_fN |>.map (fun iter_0_36_elem => .mk_val__0 .I64 iter_0_36_elem)))
  | fun_cvtop___case_6 (v_fN : fN) : fun_cvtop__ .F32 .F64 .PROMOTE (.mk_val__1 .F32 v_fN) (promote__ 32 64 v_fN |>.map (fun iter_0_elem => .mk_val__1 .F64 iter_0_elem))
  | fun_cvtop___case_7 (v_fN : fN) : fun_cvtop__ .F64 .F32 .DEMOTE (.mk_val__1 .F64 v_fN) (demote__ 64 32 v_fN |>.map (fun iter_0_elem => .mk_val__1 .F32 iter_0_elem))
  | fun_cvtop___case_8 (v_sx : sx) (v_iN : uN) : fun_cvtop__ .I32 .F32 (.CONVERT v_sx) (.mk_val__0 .I32 v_iN) [.mk_val__1 .F32 (convert__ (size (valtype_Inn .I32)) (size (valtype_Fnn .F32)) v_sx v_iN)]
  | fun_cvtop___case_9 (v_sx : sx) (v_iN : uN) : fun_cvtop__ .I64 .F32 (.CONVERT v_sx) (.mk_val__0 .I64 v_iN) [.mk_val__1 .F32 (convert__ (size (valtype_Inn .I64)) (size (valtype_Fnn .F32)) v_sx v_iN)]
  | fun_cvtop___case_10 (v_sx : sx) (v_iN : uN) : fun_cvtop__ .I32 .F64 (.CONVERT v_sx) (.mk_val__0 .I32 v_iN) [.mk_val__1 .F64 (convert__ (size (valtype_Inn .I32)) (size (valtype_Fnn .F64)) v_sx v_iN)]
  | fun_cvtop___case_11 (v_sx : sx) (v_iN : uN) : fun_cvtop__ .I64 .F64 (.CONVERT v_sx) (.mk_val__0 .I64 v_iN) [.mk_val__1 .F64 (convert__ (size (valtype_Inn .I64)) (size (valtype_Fnn .F64)) v_sx v_iN)]
  | fun_cvtop___case_12 (v_iN : uN) : (size (valtype_Inn .I32)) == (size (valtype_Fnn .F32)) → fun_cvtop__ .I32 .F32 .REINTERPRET (.mk_val__0 .I32 v_iN) [reinterpret__ (valtype_Inn .I32) (valtype_Fnn .F32) (.mk_val__0 .I32 v_iN)]
  | fun_cvtop___case_13 (v_iN : uN) : (size (valtype_Inn .I64)) == (size (valtype_Fnn .F32)) → fun_cvtop__ .I64 .F32 .REINTERPRET (.mk_val__0 .I64 v_iN) [reinterpret__ (valtype_Inn .I64) (valtype_Fnn .F32) (.mk_val__0 .I64 v_iN)]
  | fun_cvtop___case_14 (v_iN : uN) : (size (valtype_Inn .I32)) == (size (valtype_Fnn .F64)) → fun_cvtop__ .I32 .F64 .REINTERPRET (.mk_val__0 .I32 v_iN) [reinterpret__ (valtype_Inn .I32) (valtype_Fnn .F64) (.mk_val__0 .I32 v_iN)]
  | fun_cvtop___case_15 (v_iN : uN) : (size (valtype_Inn .I64)) == (size (valtype_Fnn .F64)) → fun_cvtop__ .I64 .F64 .REINTERPRET (.mk_val__0 .I64 v_iN) [reinterpret__ (valtype_Inn .I64) (valtype_Fnn .F64) (.mk_val__0 .I64 v_iN)]
  | fun_cvtop___case_16 (v_fN : fN) : (size (valtype_Inn .I32)) == (size (valtype_Fnn .F32)) → fun_cvtop__ .F32 .I32 .REINTERPRET (.mk_val__1 .F32 v_fN) [reinterpret__ (valtype_Fnn .F32) (valtype_Inn .I32) (.mk_val__1 .F32 v_fN)]
  | fun_cvtop___case_17 (v_fN : fN) : (size (valtype_Inn .I32)) == (size (valtype_Fnn .F64)) → fun_cvtop__ .F64 .I32 .REINTERPRET (.mk_val__1 .F64 v_fN) [reinterpret__ (valtype_Fnn .F64) (valtype_Inn .I32) (.mk_val__1 .F64 v_fN)]
  | fun_cvtop___case_18 (v_fN : fN) : (size (valtype_Inn .I64)) == (size (valtype_Fnn .F32)) → fun_cvtop__ .F32 .I64 .REINTERPRET (.mk_val__1 .F32 v_fN) [reinterpret__ (valtype_Fnn .F32) (valtype_Inn .I64) (.mk_val__1 .F32 v_fN)]
  | fun_cvtop___case_19 (v_fN : fN) : (size (valtype_Inn .I64)) == (size (valtype_Fnn .F64)) → fun_cvtop__ .F64 .I64 .REINTERPRET (.mk_val__1 .F64 v_fN) [reinterpret__ (valtype_Fnn .F64) (valtype_Inn .I64) (.mk_val__1 .F64 v_fN)]


inductive cvtop___is_wf : valtype → valtype → cvtop → val_ → List val_ → Prop where
  | cvtop___is_wf_0 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) (v_val_ : val_) (ret_val_lst : List val_) (var_0 : List val_) : fun_cvtop__ valtype_1 valtype_2 v_cvtop v_val_ var_0 → wf_val_ valtype_1 v_val_ → ret_val_lst == var_0 → ∀ ret_val_elem ∈ ret_val_lst, wf_val_ valtype_2 ret_val_elem → cvtop___is_wf valtype_1 valtype_2 v_cvtop v_val_ ret_val_lst


opaque ibytes_ (v_N : N) (v_iN : iN) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive ibytes__is_wf : N → iN → List byte → Prop where
  | ibytes__is_wf_0 (v_N : N) (v_iN : iN) (ret_val_lst : List byte) : wf_uN v_N v_iN → ret_val_lst == (ibytes_ v_N v_iN) → ∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem → ibytes__is_wf v_N v_iN ret_val_lst


opaque fbytes_ (v_N : N) (v_fN : fN) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive fbytes__is_wf : N → fN → List byte → Prop where
  | fbytes__is_wf_0 (v_N : N) (v_fN : fN) (ret_val_lst : List byte) : wf_fN v_N v_fN → ret_val_lst == (fbytes_ v_N v_fN) → ∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem → fbytes__is_wf v_N v_fN ret_val_lst


opaque bytes_ (v_valtype : valtype) (v_val_ : val_) : List byte := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive bytes__is_wf : valtype → val_ → List byte → Prop where
  | bytes__is_wf_0 (v_valtype : valtype) (v_val_ : val_) (ret_val_lst : List byte) : wf_val_ v_valtype v_val_ → ret_val_lst == (bytes_ v_valtype v_val_) → ∀ ret_val_elem ∈ ret_val_lst, wf_byte ret_val_elem → bytes__is_wf v_valtype v_val_ ret_val_lst


opaque inv_ibytes_ (v_N : N) (var_0_lst : List byte) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_ibytes__is_wf : N → List byte → iN → Prop where
  | inv_ibytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : iN) : ∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem → ret_val == (inv_ibytes_ v_N var_0_lst) → wf_uN v_N ret_val → inv_ibytes__is_wf v_N var_0_lst ret_val


opaque inv_fbytes_ (v_N : N) (var_0_lst : List byte) : fN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_fbytes__is_wf : N → List byte → fN → Prop where
  | inv_fbytes__is_wf_0 (v_N : N) (var_0_lst : List byte) (ret_val : fN) : ∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem → ret_val == (inv_fbytes_ v_N var_0_lst) → wf_fN v_N ret_val → inv_fbytes__is_wf v_N var_0_lst ret_val


opaque inv_bytes_ (v_valtype : valtype) (var_0_lst : List byte) : val_ := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inv_bytes__is_wf : valtype → List byte → val_ → Prop where
  | inv_bytes__is_wf_0 (v_valtype : valtype) (var_0_lst : List byte) (ret_val : val_) : ∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem → ret_val == (inv_bytes_ v_valtype var_0_lst) → wf_val_ v_valtype ret_val → inv_bytes__is_wf v_valtype var_0_lst ret_val


opaque inot_ (v_N : N) (v_iN : iN) : iN := by 
  first
     | exact Inhabited.default
     | intros ; assumption


inductive inot__is_wf : N → iN → iN → Prop where
  | inot__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : iN) : wf_uN v_N v_iN → ret_val == (inot_ v_N v_iN) → wf_uN v_N ret_val → inot__is_wf v_N v_iN ret_val


def inez_ (v_N : N) (v_iN : iN) : u32 :=
  .mk_uN (nat_of_bool ((proj_uN_0 v_iN) != 0))

inductive inez__is_wf : N → iN → u32 → Prop where
  | inez__is_wf_0 (v_N : N) (v_iN : iN) (ret_val : u32) : wf_uN v_N v_iN → ret_val == (inez_ v_N v_iN) → wf_uN 32 ret_val → inez__is_wf v_N v_iN ret_val


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
  | val_case_0 (v_valtype : valtype) (var_0 : val_) : wf_val_ v_valtype var_0 → wf_val (.CONST v_valtype var_0)


inductive result : Type where
  | _VALS (val_lst : List val) : result
  | TRAP : result
deriving Inhabited, BEq

inductive wf_result : result → Prop where
  | result_case_0 (val_lst : List val) : ∀ v_val_elem ∈ val_lst, wf_val v_val_elem → wf_result (._VALS val_lst)
  | result_case_1 : wf_result .TRAP


structure exportinst where
  MKexportinst ::
  NAME : name
  ADDR : externaddr
deriving Inhabited, BEq

inductive wf_exportinst : exportinst → Prop where
  | exportinst_case_ (var_0 : name) (var_1 : externaddr) : wf_name var_0 → wf_exportinst ({
    NAME := var_0
    ADDR := var_1
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
  | moduleinst_case_ (var_0_lst : List functype) (var_1_lst : List funcaddr) (var_2_lst : List globaladdr) (var_3_lst : List tableaddr) (var_4_lst : List memaddr) (var_5_lst : List exportinst) : ∀ var_5_elem ∈ var_5_lst, wf_exportinst var_5_elem → wf_moduleinst ({
    TYPES := var_0_lst
    FUNCS := var_1_lst
    GLOBALS := var_2_lst
    TABLES := var_3_lst
    MEMS := var_4_lst
    EXPORTS := var_5_lst
  })


structure funcinst where
  MKfuncinst ::
  TYPE : functype
  MODULE : moduleinst
  CODE : func
deriving Inhabited, BEq

inductive wf_funcinst : funcinst → Prop where
  | funcinst_case_ (var_0 : functype) (var_1 : moduleinst) (var_2 : func) : wf_moduleinst var_1 → wf_func var_2 → wf_funcinst ({
    TYPE := var_0
    MODULE := var_1
    CODE := var_2
  })


structure globalinst where
  MKglobalinst ::
  TYPE : globaltype
  VALUE : val
deriving Inhabited, BEq

inductive wf_globalinst : globalinst → Prop where
  | globalinst_case_ (var_0 : globaltype) (var_1 : val) : wf_val var_1 → wf_globalinst ({
    TYPE := var_0
    VALUE := var_1
  })


structure tableinst where
  MKtableinst ::
  TYPE : tabletype
  REFS : List (Option funcaddr)
deriving Inhabited, BEq

inductive wf_tableinst : tableinst → Prop where
  | tableinst_case_ (var_0 : tabletype) (var_1_opt_lst : List (Option funcaddr)) : wf_limits var_0 → wf_tableinst ({
    TYPE := var_0
    REFS := var_1_opt_lst
  })


structure meminst where
  MKmeminst ::
  TYPE : memtype
  BYTES : List byte
deriving Inhabited, BEq

inductive wf_meminst : meminst → Prop where
  | meminst_case_ (var_0 : memtype) (var_1_lst : List byte) : wf_limits var_0 → ∀ var_1_elem ∈ var_1_lst, wf_byte var_1_elem → wf_meminst ({
    TYPE := var_0
    BYTES := var_1_lst
  })


structure store where
  MKstore ::
  FUNCS : List funcinst
  GLOBALS : List globalinst
  TABLES : List tableinst
  MEMS : List meminst
deriving Inhabited, BEq

inductive wf_store : store → Prop where
  | store_case_ (var_0_lst : List funcinst) (var_1_lst : List globalinst) (var_2_lst : List tableinst) (var_3_lst : List meminst) : ∀ var_0_elem ∈ var_0_lst, wf_funcinst var_0_elem → ∀ var_1_elem ∈ var_1_lst, wf_globalinst var_1_elem → ∀ var_2_elem ∈ var_2_lst, wf_tableinst var_2_elem → ∀ var_3_elem ∈ var_3_lst, wf_meminst var_3_elem → wf_store ({
    FUNCS := var_0_lst
    GLOBALS := var_1_lst
    TABLES := var_2_lst
    MEMS := var_3_lst
  })


structure frame where
  MKframe ::
  LOCALS : List val
  MODULE : moduleinst
deriving Inhabited, BEq

inductive wf_frame : frame → Prop where
  | frame_case_ (var_0_lst : List val) (var_1 : moduleinst) : ∀ var_0_elem ∈ var_0_lst, wf_val var_0_elem → wf_moduleinst var_1 → wf_frame ({
    LOCALS := var_0_lst
    MODULE := var_1
  })


inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq

inductive wf_state : state → Prop where
  | state_case_0 (v_store : store) (v_frame : frame) : wf_store v_store → wf_frame v_frame → wf_state (.mk_state v_store v_frame)


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

inductive wf_admininstr : admininstr → Prop where
  | admininstr_case_0 : wf_admininstr .NOP
  | admininstr_case_1 : wf_admininstr .UNREACHABLE
  | admininstr_case_2 : wf_admininstr .DROP
  | admininstr_case_3 : wf_admininstr .SELECT
  | admininstr_case_4 (v_blocktype : blocktype) (instr_lst : List instr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → wf_admininstr (.BLOCK v_blocktype instr_lst)
  | admininstr_case_5 (v_blocktype : blocktype) (instr_lst : List instr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → wf_admininstr (.LOOP v_blocktype instr_lst)
  | admininstr_case_6 (v_blocktype : blocktype) (instr_lst : List instr) (instr_lst_0_lst : List instr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → ∀ instr_lst_0_elem ∈ instr_lst_0_lst, wf_instr instr_lst_0_elem → wf_admininstr (.IFELSE v_blocktype instr_lst instr_lst_0_lst)
  | admininstr_case_7 (v_labelidx : labelidx) : wf_uN 32 v_labelidx → wf_admininstr (.BR v_labelidx)
  | admininstr_case_8 (v_labelidx : labelidx) : wf_uN 32 v_labelidx → wf_admininstr (.BR_IF v_labelidx)
  | admininstr_case_9 (labelidx_lst : List labelidx) (v_labelidx : labelidx) : ∀ v_labelidx_elem ∈ labelidx_lst, wf_uN 32 v_labelidx_elem → wf_uN 32 v_labelidx → wf_admininstr (.BR_TABLE labelidx_lst v_labelidx)
  | admininstr_case_10 (v_funcidx : funcidx) : wf_uN 32 v_funcidx → wf_admininstr (.CALL v_funcidx)
  | admininstr_case_11 (v_typeidx : typeidx) : wf_uN 32 v_typeidx → wf_admininstr (.CALL_INDIRECT v_typeidx)
  | admininstr_case_12 : wf_admininstr .RETURN
  | admininstr_case_13 (v_valtype : valtype) (var_0 : val_) : wf_val_ v_valtype var_0 → wf_admininstr (.CONST v_valtype var_0)
  | admininstr_case_14 (v_valtype : valtype) (var_0 : unop_) : wf_unop_ v_valtype var_0 → wf_admininstr (.UNOP v_valtype var_0)
  | admininstr_case_15 (v_valtype : valtype) (var_0 : binop_) : wf_binop_ v_valtype var_0 → wf_admininstr (.BINOP v_valtype var_0)
  | admininstr_case_16 (v_valtype : valtype) (var_0 : testop_) : wf_testop_ v_valtype var_0 → wf_admininstr (.TESTOP v_valtype var_0)
  | admininstr_case_17 (v_valtype : valtype) (var_0 : relop_) : wf_relop_ v_valtype var_0 → wf_admininstr (.RELOP v_valtype var_0)
  | admininstr_case_18 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : valtype_1 != valtype_2 → wf_admininstr (.CVTOP valtype_1 valtype_2 v_cvtop)
  | admininstr_case_19 (v_localidx : localidx) : wf_uN 32 v_localidx → wf_admininstr (.LOCAL_GET v_localidx)
  | admininstr_case_20 (v_localidx : localidx) : wf_uN 32 v_localidx → wf_admininstr (.LOCAL_SET v_localidx)
  | admininstr_case_21 (v_localidx : localidx) : wf_uN 32 v_localidx → wf_admininstr (.LOCAL_TEE v_localidx)
  | admininstr_case_22 (v_globalidx : globalidx) : wf_uN 32 v_globalidx → wf_admininstr (.GLOBAL_GET v_globalidx)
  | admininstr_case_23 (v_globalidx : globalidx) : wf_uN 32 v_globalidx → wf_admininstr (.GLOBAL_SET v_globalidx)
  | admininstr_case_24 (v_valtype : valtype) (var_0_opt : Option loadop_) (v_memarg : memarg) : ∀ var_0_elem ∈ Option.toList var_0_opt, wf_loadop_ v_valtype var_0_elem → wf_memarg v_memarg → wf_admininstr (.LOAD v_valtype var_0_opt v_memarg)
  | admininstr_case_25 (Inn_opt : Option Inn) (valtype_opt : Option valtype) (v_valtype : valtype) (sz_opt : Option sz) (v_memarg : memarg) : ∀ v_sz_elem ∈ Option.toList sz_opt, wf_sz v_sz_elem → wf_memarg v_memarg → ((Inn_opt == none) ↔ (sz_opt == none)) → ((Inn_opt == none) ↔ (valtype_opt == none)) → ∀ __iter_tuple ∈ Option.toList Inn_opt |>.zip (Option.toList sz_opt) |>.zip (Option.toList valtype_opt), ((__iter_tuple.2) == (valtype_Inn (__iter_tuple.1.1))) && ((proj_sz_0 (__iter_tuple.1.2)) < (size (valtype_Inn (__iter_tuple.1.1)))) → wf_admininstr (.STORE v_valtype sz_opt v_memarg)
  | admininstr_case_26 : wf_admininstr .MEMORY_SIZE
  | admininstr_case_27 : wf_admininstr .MEMORY_GROW
  | admininstr_case_28 (v_funcaddr : funcaddr) : wf_admininstr (.CALL_ADDR v_funcaddr)
  | admininstr_case_29 (v_n : n) (instr_lst : List instr) (admininstr_lst : List admininstr) : ∀ v_instr_elem ∈ instr_lst, wf_instr v_instr_elem → ∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem → wf_admininstr (.LABEL_ v_n instr_lst admininstr_lst)
  | admininstr_case_30 (v_n : n) (v_frame : frame) (admininstr_lst : List admininstr) : wf_frame v_frame → ∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem → wf_admininstr (.FRAME_ v_n v_frame admininstr_lst)
  | admininstr_case_31 : wf_admininstr .TRAP


inductive config : Type where
  | mk_config (v_state : state) (admininstr_lst : List admininstr) : config
deriving Inhabited, BEq

inductive wf_config : config → Prop where
  | config_case_0 (v_state : state) (admininstr_lst : List admininstr) : wf_state v_state → ∀ v_admininstr_elem ∈ admininstr_lst, wf_admininstr v_admininstr_elem → wf_config (.mk_config v_state admininstr_lst)


def default_ (v_valtype : valtype) : val :=
  match v_valtype with
  | .I32 => .CONST .I32 (.mk_val__0 .I32 (.mk_uN 0))
  | .I64 => .CONST .I64 (.mk_val__0 .I64 (.mk_uN 0))
  | .F32 => .CONST .F32 (.mk_val__1 .F32 (fzero 32))
  | .F64 => .CONST .F64 (.mk_val__1 .F64 (fzero 64))

inductive default__is_wf : valtype → val → Prop where
  | default__is_wf_0 (v_valtype : valtype) (ret_val : val) : ret_val == (default_ v_valtype) → wf_val ret_val → default__is_wf v_valtype ret_val


inductive fun_funcsxa : List externaddr → List funcaddr → Prop where
  | fun_funcsxa_case_0 : fun_funcsxa [] []
  | fun_funcsxa_case_1 (fa : Nat) (xv_lst : List externaddr) (var_0 : List funcaddr) : fun_funcsxa xv_lst var_0 → fun_funcsxa ([.FUNC fa] ++ xv_lst) ([fa] ++ var_0)
  | fun_funcsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List funcaddr) : fun_funcsxa xv_lst var_0 → fun_funcsxa ([v_externaddr] ++ xv_lst) var_0


inductive fun_globalsxa : List externaddr → List globaladdr → Prop where
  | fun_globalsxa_case_0 : fun_globalsxa [] []
  | fun_globalsxa_case_1 (ga : Nat) (xv_lst : List externaddr) (var_0 : List globaladdr) : fun_globalsxa xv_lst var_0 → fun_globalsxa ([.GLOBAL ga] ++ xv_lst) ([ga] ++ var_0)
  | fun_globalsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List globaladdr) : fun_globalsxa xv_lst var_0 → fun_globalsxa ([v_externaddr] ++ xv_lst) var_0


inductive fun_tablesxa : List externaddr → List tableaddr → Prop where
  | fun_tablesxa_case_0 : fun_tablesxa [] []
  | fun_tablesxa_case_1 (ta : Nat) (xv_lst : List externaddr) (var_0 : List tableaddr) : fun_tablesxa xv_lst var_0 → fun_tablesxa ([.TABLE ta] ++ xv_lst) ([ta] ++ var_0)
  | fun_tablesxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List tableaddr) : fun_tablesxa xv_lst var_0 → fun_tablesxa ([v_externaddr] ++ xv_lst) var_0


inductive fun_memsxa : List externaddr → List memaddr → Prop where
  | fun_memsxa_case_0 : fun_memsxa [] []
  | fun_memsxa_case_1 (ma : Nat) (xv_lst : List externaddr) (var_0 : List memaddr) : fun_memsxa xv_lst var_0 → fun_memsxa ([.MEM ma] ++ xv_lst) ([ma] ++ var_0)
  | fun_memsxa_case_2 (v_externaddr : externaddr) (xv_lst : List externaddr) (var_0 : List memaddr) : fun_memsxa xv_lst var_0 → fun_memsxa ([v_externaddr] ++ xv_lst) var_0


def fun_store (v_state : state) : store :=
  match v_state with
  | .mk_state s f => s

inductive store_is_wf : state → store → Prop where
  | store_is_wf_0 (v_state : state) (ret_val : store) : wf_state v_state → ret_val == (fun_store v_state) → wf_store ret_val → store_is_wf v_state ret_val


def fun_frame (v_state : state) : frame :=
  match v_state with
  | .mk_state s f => f

inductive frame_is_wf : state → frame → Prop where
  | frame_is_wf_0 (v_state : state) (ret_val : frame) : wf_state v_state → ret_val == (fun_frame v_state) → wf_frame ret_val → frame_is_wf v_state ret_val


def fun_funcaddr (v_state : state) : List funcaddr :=
  match v_state with
  | .mk_state s f => f.MODULE.FUNCS

def fun_funcinst (v_state : state) : List funcinst :=
  match v_state with
  | .mk_state s f => s.FUNCS

inductive funcinst_is_wf : state → List funcinst → Prop where
  | funcinst_is_wf_0 (v_state : state) (ret_val_lst : List funcinst) : wf_state v_state → ret_val_lst == (fun_funcinst v_state) → ∀ ret_val_elem ∈ ret_val_lst, wf_funcinst ret_val_elem → funcinst_is_wf v_state ret_val_lst


def fun_globalinst (v_state : state) : List globalinst :=
  match v_state with
  | .mk_state s f => s.GLOBALS

inductive globalinst_is_wf : state → List globalinst → Prop where
  | globalinst_is_wf_0 (v_state : state) (ret_val_lst : List globalinst) : wf_state v_state → ret_val_lst == (fun_globalinst v_state) → ∀ ret_val_elem ∈ ret_val_lst, wf_globalinst ret_val_elem → globalinst_is_wf v_state ret_val_lst


def fun_tableinst (v_state : state) : List tableinst :=
  match v_state with
  | .mk_state s f => s.TABLES

inductive tableinst_is_wf : state → List tableinst → Prop where
  | tableinst_is_wf_0 (v_state : state) (ret_val_lst : List tableinst) : wf_state v_state → ret_val_lst == (fun_tableinst v_state) → ∀ ret_val_elem ∈ ret_val_lst, wf_tableinst ret_val_elem → tableinst_is_wf v_state ret_val_lst


def fun_meminst (v_state : state) : List meminst :=
  match v_state with
  | .mk_state s f => s.MEMS

inductive meminst_is_wf : state → List meminst → Prop where
  | meminst_is_wf_0 (v_state : state) (ret_val_lst : List meminst) : wf_state v_state → ret_val_lst == (fun_meminst v_state) → ∀ ret_val_elem ∈ ret_val_lst, wf_meminst ret_val_elem → meminst_is_wf v_state ret_val_lst


def fun_moduleinst (v_state : state) : moduleinst :=
  match v_state with
  | .mk_state s f => f.MODULE

inductive moduleinst_is_wf : state → moduleinst → Prop where
  | moduleinst_is_wf_0 (v_state : state) (ret_val : moduleinst) : wf_state v_state → ret_val == (fun_moduleinst v_state) → wf_moduleinst ret_val → moduleinst_is_wf v_state ret_val


def fun_type (v_state : state) (v_typeidx : typeidx) : functype :=
  match v_state with
  | .mk_state s f => f.MODULE.TYPES[proj_uN_0 v_typeidx]!

def fun_func (v_state : state) (v_funcidx : funcidx) : funcinst :=
  match v_state with
  | .mk_state s f => s.FUNCS[f.MODULE.FUNCS[proj_uN_0 v_funcidx]!]!

inductive func_is_wf : state → funcidx → funcinst → Prop where
  | func_is_wf_0 (v_state : state) (v_funcidx : funcidx) (ret_val : funcinst) : wf_state v_state → wf_uN 32 v_funcidx → ret_val == (fun_func v_state v_funcidx) → wf_funcinst ret_val → func_is_wf v_state v_funcidx ret_val


def fun_global (v_state : state) (v_globalidx : globalidx) : globalinst :=
  match v_state with
  | .mk_state s f => s.GLOBALS[f.MODULE.GLOBALS[proj_uN_0 v_globalidx]!]!

inductive global_is_wf : state → globalidx → globalinst → Prop where
  | global_is_wf_0 (v_state : state) (v_globalidx : globalidx) (ret_val : globalinst) : wf_state v_state → wf_uN 32 v_globalidx → ret_val == (fun_global v_state v_globalidx) → wf_globalinst ret_val → global_is_wf v_state v_globalidx ret_val


def fun_table (v_state : state) (v_tableidx : tableidx) : tableinst :=
  match v_state with
  | .mk_state s f => s.TABLES[f.MODULE.TABLES[proj_uN_0 v_tableidx]!]!

inductive table_is_wf : state → tableidx → tableinst → Prop where
  | table_is_wf_0 (v_state : state) (v_tableidx : tableidx) (ret_val : tableinst) : wf_state v_state → wf_uN 32 v_tableidx → ret_val == (fun_table v_state v_tableidx) → wf_tableinst ret_val → table_is_wf v_state v_tableidx ret_val


def fun_mem (v_state : state) (v_memidx : memidx) : meminst :=
  match v_state with
  | .mk_state s f => s.MEMS[f.MODULE.MEMS[proj_uN_0 v_memidx]!]!

inductive mem_is_wf : state → memidx → meminst → Prop where
  | mem_is_wf_0 (v_state : state) (v_memidx : memidx) (ret_val : meminst) : wf_state v_state → wf_uN 32 v_memidx → ret_val == (fun_mem v_state v_memidx) → wf_meminst ret_val → mem_is_wf v_state v_memidx ret_val


def fun_local (v_state : state) (v_localidx : localidx) : val :=
  match v_state with
  | .mk_state s f => f.LOCALS[proj_uN_0 v_localidx]!

inductive local_is_wf : state → localidx → val → Prop where
  | local_is_wf_0 (v_state : state) (v_localidx : localidx) (ret_val : val) : wf_state v_state → wf_uN 32 v_localidx → ret_val == (fun_local v_state v_localidx) → wf_val ret_val → local_is_wf v_state v_localidx ret_val


def with_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
  match v_state with
  | .mk_state s f => .mk_state s ({
    f with 
    LOCALS := List.modify (f.LOCALS) (proj_uN_0 v_localidx) (fun elem_1 => v_val)
  })

inductive with_local_is_wf : state → localidx → val → state → Prop where
  | with_local_is_wf_0 (v_state : state) (v_localidx : localidx) (v_val : val) (ret_val : state) : wf_state v_state → wf_uN 32 v_localidx → wf_val v_val → ret_val == (with_local v_state v_localidx v_val) → wf_state ret_val → with_local_is_wf v_state v_localidx v_val ret_val


def with_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
  match v_state with
  | .mk_state s f => .mk_state ({
    s with 
    GLOBALS := List.modify (s.GLOBALS) (f.MODULE.GLOBALS[proj_uN_0 v_globalidx]!) (fun elem_1 => {
      elem_1 with 
      VALUE := v_val
    })
  }) f

inductive with_global_is_wf : state → globalidx → val → state → Prop where
  | with_global_is_wf_0 (v_state : state) (v_globalidx : globalidx) (v_val : val) (ret_val : state) : wf_state v_state → wf_uN 32 v_globalidx → wf_val v_val → ret_val == (with_global v_state v_globalidx v_val) → wf_state ret_val → with_global_is_wf v_state v_globalidx v_val ret_val


def with_table (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_funcaddr : funcaddr) : state :=
  match v_state with
  | .mk_state s f => .mk_state ({
    s with 
    TABLES := List.modify (s.TABLES) (f.MODULE.TABLES[proj_uN_0 v_tableidx]!) (fun elem_1 => {
      elem_1 with 
      REFS := List.modify (elem_1.REFS) nat (fun elem_2 => some v_funcaddr)
    })
  }) f

inductive with_table_is_wf : state → tableidx → Nat → funcaddr → state → Prop where
  | with_table_is_wf_0 (v_state : state) (v_tableidx : tableidx) (nat : Nat) (v_funcaddr : funcaddr) (ret_val : state) : wf_state v_state → wf_uN 32 v_tableidx → ret_val == (with_table v_state v_tableidx nat v_funcaddr) → wf_state ret_val → with_table_is_wf v_state v_tableidx nat v_funcaddr ret_val


def with_tableinst (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) : state :=
  match v_state with
  | .mk_state s f => .mk_state ({
    s with 
    TABLES := List.modify (s.TABLES) (f.MODULE.TABLES[proj_uN_0 v_tableidx]!) (fun elem_1 => v_tableinst)
  }) f

inductive with_tableinst_is_wf : state → tableidx → tableinst → state → Prop where
  | with_tableinst_is_wf_0 (v_state : state) (v_tableidx : tableidx) (v_tableinst : tableinst) (ret_val : state) : wf_state v_state → wf_uN 32 v_tableidx → wf_tableinst v_tableinst → ret_val == (with_tableinst v_state v_tableidx v_tableinst) → wf_state ret_val → with_tableinst_is_wf v_state v_tableidx v_tableinst ret_val


def with_mem (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) : state :=
  match v_state with
  | .mk_state s f => .mk_state ({
    s with 
    MEMS := List.modify (s.MEMS) (f.MODULE.MEMS[proj_uN_0 v_memidx]!) (fun elem_1 => {
      elem_1 with 
      BYTES := ((elem_1.BYTES.take nat) ++ var_0_lst) ++ (elem_1.BYTES.drop (nat + nat_0))
    })
  }) f

inductive with_mem_is_wf : state → memidx → Nat → Nat → List byte → state → Prop where
  | with_mem_is_wf_0 (v_state : state) (v_memidx : memidx) (nat : Nat) (nat_0 : Nat) (var_0_lst : List byte) (ret_val : state) : wf_state v_state → wf_uN 32 v_memidx → ∀ var_0_elem ∈ var_0_lst, wf_byte var_0_elem → ret_val == (with_mem v_state v_memidx nat nat_0 var_0_lst) → wf_state ret_val → with_mem_is_wf v_state v_memidx nat nat_0 var_0_lst ret_val


def with_meminst (v_state : state) (v_memidx : memidx) (v_meminst : meminst) : state :=
  match v_state with
  | .mk_state s f => .mk_state ({
    s with 
    MEMS := List.modify (s.MEMS) (f.MODULE.MEMS[proj_uN_0 v_memidx]!) (fun elem_1 => v_meminst)
  }) f

inductive with_meminst_is_wf : state → memidx → meminst → state → Prop where
  | with_meminst_is_wf_0 (v_state : state) (v_memidx : memidx) (v_meminst : meminst) (ret_val : state) : wf_state v_state → wf_uN 32 v_memidx → wf_meminst v_meminst → ret_val == (with_meminst v_state v_memidx v_meminst) → wf_state ret_val → with_meminst_is_wf v_state v_memidx v_meminst ret_val


def with_mems_elem (v_state : state) (nat : Nat) (nat_0 : Nat) (nat_1 : Nat) (v_meminst : meminst) : state :=
  match v_state with
  | .mk_state s f => .mk_state ({
    s with 
    MEMS := ((s.MEMS.take nat) ++ (List.modify ((s.MEMS.drop nat).take nat_0) nat_1 (fun elem_1 => v_meminst))) ++ (s.MEMS.drop (nat + nat_0))
  }) f

inductive with_mems_elem_is_wf : state → Nat → Nat → Nat → meminst → state → Prop where
  | with_mems_elem_is_wf_0 (v_state : state) (nat : Nat) (nat_0 : Nat) (nat_1 : Nat) (v_meminst : meminst) (ret_val : state) : wf_state v_state → wf_meminst v_meminst → ret_val == (with_mems_elem v_state nat nat_0 nat_1 v_meminst) → wf_state ret_val → with_mems_elem_is_wf v_state nat nat_0 nat_1 v_meminst ret_val


inductive fun_growtable_before_fun_growtable_case_1 : tableinst → Nat → Prop where
  | fun_growtable_case_0 (ti : tableinst) (v_n : Nat) (ti' : tableinst) (i : uN) (j_opt : Option u32) (a_lst : List addr) (i' : Nat) : ti == ({
    TYPE := .mk_limits i j_opt
    REFS := a_lst |>.map (fun a_1_elem => some a_1_elem)
  }) → i' == ((List.length a_lst) + v_n) → ti' == ({
    TYPE := .mk_limits (.mk_uN i') j_opt
    REFS := (a_lst |>.map (fun a_3_elem => some a_3_elem)) ++ (List.replicate v_n none)
  }) → ∀ j_3_elem ∈ Option.toList j_opt, i' ≤ (proj_uN_0 j_3_elem) → wf_tableinst ({
    TYPE := .mk_limits i j_opt
    REFS := a_lst |>.map (fun a_4_elem => some a_4_elem)
  }) → wf_tableinst ({
    TYPE := .mk_limits (.mk_uN i') j_opt
    REFS := (a_lst |>.map (fun a_5_elem => some a_5_elem)) ++ (List.replicate v_n none)
  }) → fun_growtable_before_fun_growtable_case_1 ti v_n


inductive fun_growtable : tableinst → Nat → Option tableinst → Prop where
  | fun_growtable_case_0 (ti : tableinst) (v_n : Nat) (ti' : tableinst) (i : uN) (j_opt : Option u32) (a_lst : List addr) (i' : Nat) : ti == ({
    TYPE := .mk_limits i j_opt
    REFS := a_lst |>.map (fun a_1_elem => some a_1_elem)
  }) → i' == ((List.length a_lst) + v_n) → ti' == ({
    TYPE := .mk_limits (.mk_uN i') j_opt
    REFS := (a_lst |>.map (fun a_3_elem => some a_3_elem)) ++ (List.replicate v_n none)
  }) → ∀ j_3_elem ∈ Option.toList j_opt, i' ≤ (proj_uN_0 j_3_elem) → wf_tableinst ({
    TYPE := .mk_limits i j_opt
    REFS := a_lst |>.map (fun a_4_elem => some a_4_elem)
  }) → wf_tableinst ({
    TYPE := .mk_limits (.mk_uN i') j_opt
    REFS := (a_lst |>.map (fun a_5_elem => some a_5_elem)) ++ (List.replicate v_n none)
  }) → fun_growtable ti v_n (some ti')
  | fun_growtable_case_1 (x0 : tableinst) (x1 : Nat) : ¬ fun_growtable_before_fun_growtable_case_1 x0 x1 → fun_growtable x0 x1 none


inductive growtable_is_wf : tableinst → Nat → tableinst → Prop where
  | growtable_is_wf_0 (v_tableinst : tableinst) (nat : Nat) (ret_val : tableinst) (var_0 : Option tableinst) : fun_growtable v_tableinst nat var_0 → wf_tableinst v_tableinst → var_0 != none → ret_val == (Option.get! var_0) → wf_tableinst ret_val → growtable_is_wf v_tableinst nat ret_val


inductive fun_growmemory_before_fun_growmemory_case_1 : meminst → Nat → Prop where
  | fun_growmemory_case_0 (mi : meminst) (v_n : Nat) (mi' : meminst) (i : u32) (j_opt : Option u32) (b_lst : List byte) (i' : Rat) : ({
    TYPE := .mk_limits i j_opt
    BYTES := b_lst
  }) == mi → i' == ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) → mi' == ({
    TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
    BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (.mk_byte 0))
  }) → ∀ j_8_elem ∈ Option.toList j_opt, i' ≤ ((proj_uN_0 j_8_elem) : Rat) → wf_meminst ({
    TYPE := .mk_limits i j_opt
    BYTES := b_lst
  }) → wf_meminst ({
    TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
    BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (.mk_byte 0))
  }) → fun_growmemory_before_fun_growmemory_case_1 mi v_n


inductive fun_growmemory : meminst → Nat → Option meminst → Prop where
  | fun_growmemory_case_0 (mi : meminst) (v_n : Nat) (mi' : meminst) (i : u32) (j_opt : Option u32) (b_lst : List byte) (i' : Rat) : ({
    TYPE := .mk_limits i j_opt
    BYTES := b_lst
  }) == mi → i' == ((((List.length b_lst) : Rat) / ((64 * Ki) : Rat)) + (v_n : Rat)) → mi' == ({
    TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
    BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (.mk_byte 0))
  }) → ∀ j_8_elem ∈ Option.toList j_opt, i' ≤ ((proj_uN_0 j_8_elem) : Rat) → wf_meminst ({
    TYPE := .mk_limits i j_opt
    BYTES := b_lst
  }) → wf_meminst ({
    TYPE := .mk_limits (.mk_uN (rat_to_nat i')) j_opt
    BYTES := b_lst ++ (List.replicate (v_n * (64 * Ki)) (.mk_byte 0))
  }) → fun_growmemory mi v_n (some mi')
  | fun_growmemory_case_1 (x0 : meminst) (x1 : Nat) : ¬ fun_growmemory_before_fun_growmemory_case_1 x0 x1 → fun_growmemory x0 x1 none


inductive growmemory_is_wf : meminst → Nat → meminst → Prop where
  | growmemory_is_wf_0 (v_meminst : meminst) (nat : Nat) (ret_val : meminst) (var_0 : Option meminst) : fun_growmemory v_meminst nat var_0 → wf_meminst v_meminst → var_0 != none → ret_val == (Option.get! var_0) → wf_meminst ret_val → growmemory_is_wf v_meminst nat ret_val

