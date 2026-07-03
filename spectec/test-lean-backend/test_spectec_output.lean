def List.ap (fs : List (α → β)) (xs : List α) : List β :=
  List.zipWith ((· ·)) fs xs

def Option.ap (f : Option (α → β)) (x : Option α) : Option β :=
  f.bind (fun f => x.map f)

abbrev localidx : Type := Nat

abbrev globalidx : Type := Nat

inductive «mut» : Type where
  | MUT : «mut»
deriving Inhabited, BEq

inductive valtype : Type where
  | I32 : valtype
  | I64 : valtype
  | F32 : valtype
  | F64 : valtype
deriving Inhabited, BEq

inductive functype : Type where
  | mk_functype (valtype_lst_0 : List valtype) (valtype_lst_1 : List valtype) : functype
deriving Inhabited, BEq

inductive globaltype : Type where
  | mk_globaltype (mut_opt : Option «mut») (v_valtype : valtype) : globaltype
deriving Inhabited, BEq

abbrev const : Type := Nat

inductive instr : Type where
  | NOP : instr
  | DROP : instr
  | SELECT : instr
  | CONST (v_valtype : valtype) (v_const : const) : instr
  | LOCAL_GET (v_localidx : localidx) : instr
  | LOCAL_SET (v_localidx : localidx) : instr
  | GLOBAL_GET (v_globalidx : globalidx) : instr
  | GLOBAL_SET (v_globalidx : globalidx) : instr
deriving Inhabited, BEq

structure context where
  MKcontext ::
  GLOBALS : List globaltype
  LOCALS : List valtype
deriving Inhabited, BEq

inductive Instr_ok : context → instr → functype → Prop where
  | nop (C : context) : Instr_ok C .NOP (.mk_functype [] [])
  | drop (C : context) (t : valtype) : Instr_ok C .DROP (.mk_functype [t] [])
  | select (C : context) (t : valtype) : Instr_ok C .SELECT (.mk_functype [t, t, .I32] [t])
  | const (C : context) (t : valtype) (c : const) : Instr_ok C (.CONST t c) (.mk_functype [] [t])
  | local_get (C : context) (x : localidx) (t : valtype) : x < (List.length (C.LOCALS)) → (C.LOCALS[x]!) == t → Instr_ok C (.LOCAL_GET x) (.mk_functype [] [t])
  | local_set (C : context) (x : localidx) (t : valtype) : x < (List.length (C.LOCALS)) → (C.LOCALS[x]!) == t → Instr_ok C (.LOCAL_SET x) (.mk_functype [t] [])
  | global_get (C : context) (x : globalidx) (t : valtype) : x < (List.length (C.GLOBALS)) → (C.GLOBALS[x]!) == (.mk_globaltype (some .MUT) t) → Instr_ok C (.GLOBAL_GET x) (.mk_functype [] [t])
  | global_set (C : context) (x : globalidx) (t : valtype) : x < (List.length (C.GLOBALS)) → (C.GLOBALS[x]!) == (.mk_globaltype (some .MUT) t) → Instr_ok C (.GLOBAL_GET x) (.mk_functype [t] [])


abbrev addr : Type := Nat

structure moduleinst where
  MKmoduleinst ::
  GLOBALS : List addr
deriving Inhabited, BEq

inductive val : Type where
  | CONST (v_valtype : valtype) (v_const : const) : val
deriving Inhabited, BEq

def instr_val (var_0 : val) : instr :=
  match var_0 with
  | .CONST x0 x1 => .CONST x0 x1

structure store where
  MKstore ::
  GLOBALS : List val
deriving Inhabited, BEq

structure frame where
  MKframe ::
  LOCALS : List val
  MODULE : moduleinst
deriving Inhabited, BEq

inductive state : Type where
  | mk_state (v_store : store) (v_frame : frame) : state
deriving Inhabited, BEq

inductive config : Type where
  | mk_config (v_state : state) (instr_lst : List instr) : config
deriving Inhabited, BEq

def «local» (v_state : state) (v_localidx : localidx) : val :=
  match v_state, v_localidx with
  | .mk_state s f, x => f.LOCALS[x]!

def global (v_state : state) (v_globalidx : globalidx) : val :=
  match v_state, v_globalidx with
  | .mk_state s f, x => s.GLOBALS[f.MODULE.GLOBALS[x]!]!

def update_local (v_state : state) (v_localidx : localidx) (v_val : val) : state :=
  match v_state, v_localidx, v_val with
  | .mk_state s f, x, v => .mk_state s ({
    f with
    LOCALS := List.modify (f.LOCALS) x (fun elem_1 => v)
  })

def update_global (v_state : state) (v_globalidx : globalidx) (v_val : val) : state :=
  match v_state, v_globalidx, v_val with
  | .mk_state s f, x, v => .mk_state ({
    s with
    GLOBALS := List.modify (s.GLOBALS) (f.MODULE.GLOBALS[x]!) (fun elem_1 => v)
  }) f

inductive Step_pure : List instr → List instr → Prop where
  | nop : Step_pure [.NOP] []
  | drop (v_val : val) : Step_pure [instr_val v_val, .DROP] []
  | select_true (val_1 : val) (val_2 : val) (c : const) : c ≠ 0 → Step_pure [instr_val val_1, instr_val val_2, .CONST .I32 c, .SELECT] [instr_val val_1]
  | select_false (val_1 : val) (val_2 : val) (c : const) : c == 0 → Step_pure [instr_val val_1, instr_val val_2, .CONST .I32 c, .SELECT] [instr_val val_2]


inductive Step : config → config → Prop where
  | pure (z : state) (instr_lst : List instr) (instr'_lst : List instr) : Step_pure instr_lst instr'_lst → Step (.mk_config z instr_lst) (.mk_config z instr'_lst)
  | local_get (z : state) (x : localidx) (v_val : val) : v_val == («local» z x) → Step (.mk_config z [.LOCAL_GET x]) (.mk_config z [instr_val v_val])
  | local_set (z : state) (v_val : val) (x : localidx) (z' : state) : z' == (update_local z x v_val) → Step (.mk_config z [instr_val v_val, .LOCAL_SET x]) (.mk_config z' [])
  | global_get (z : state) (x : globalidx) (v_val : val) : v_val == (global z x) → Step (.mk_config z [.GLOBAL_GET x]) (.mk_config z [instr_val v_val])
  | global_set (z : state) (v_val : val) (x : globalidx) (z' : state) : z' == (update_global z x v_val) → Step (.mk_config z [instr_val v_val, .GLOBAL_SET x]) (.mk_config z' [])


opaque float (nat : Nat) (var_0_lst : List Nat) : const := by
  first
     | exact Inhabited.default
     | intros ; assumption
