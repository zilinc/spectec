def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

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


opaque size (v_valtype : valtype) : Nat := by
  first
     | exact Inhabited.default
     | intros ; assumption


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
  | instr_case_18 (valtype_1 : valtype) (valtype_2 : valtype) (v_cvtop : cvtop) : valtype_1 ≠ valtype_2 → wf_instr (.CVTOP valtype_1 valtype_2 v_cvtop)
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
