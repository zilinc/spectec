     abbrev localidx  : Type := Nat

     abbrev globalidx  : Type := Nat

     inductive «mut»  : Type where
  |      MUT  : «mut»
deriving Inhabited, BEq

     inductive valtype  : Type where
  |      I32  : valtype
|      I64  : valtype
|      F32  : valtype
|      F64  : valtype
deriving Inhabited, BEq

     inductive functype  : Type where
  |      mk_functype (valtype_lst : List (valtype)) (valtype_lst : List (valtype)) : functype
deriving Inhabited, BEq

     inductive globaltype  : Type where
  |      mk_globaltype (mut_opt : Option («mut»)) (v_valtype : valtype) : globaltype
deriving Inhabited, BEq

     abbrev const  : Type := Nat

     inductive instr  : Type where
  |      NOP  : instr
|      DROP  : instr
|      SELECT  : instr
|      CONST (v_valtype : valtype) (v_const : const) : instr
|      LOCAL_GET (v_localidx : localidx) : instr
|      LOCAL_SET (v_localidx : localidx) : instr
|      GLOBAL_GET (v_globalidx : globalidx) : instr
|      GLOBAL_SET (v_globalidx : globalidx) : instr
deriving Inhabited, BEq

     structure context   where     MKcontext::
      GLOBALS  : List (globaltype)
      LOCALS  : List (valtype)
 deriving Inhabited, BEq

     inductive Instr_ok  : context -> instr -> functype -> Prop where
  |      nop (C : context) : Instr_ok (C) (.NOP) (.mk_functype ([]) ([]))
|      drop (C : context) (t : valtype) : Instr_ok (C) (.DROP) (.mk_functype ([t]) ([]))
|      select (C : context) (t : valtype) : Instr_ok (C) (.SELECT) (.mk_functype ([t, t, .I32]) ([t]))
|      const (C : context) (t : valtype) (c : const) : Instr_ok (C) (.CONST (t) (c)) (.mk_functype ([]) ([t]))
|      local_get (C : context) (x : localidx) (t : valtype) : (x) < (List.length (C.LOCALS)) -> (C.LOCALS[x]!) == (t) -> Instr_ok (C) (.LOCAL_GET (x)) (.mk_functype ([]) ([t]))
|      local_set (C : context) (x : localidx) (t : valtype) : (x) < (List.length (C.LOCALS)) -> (C.LOCALS[x]!) == (t) -> Instr_ok (C) (.LOCAL_SET (x)) (.mk_functype ([t]) ([]))
|      global_get (C : context) (x : globalidx) (t : valtype) : (x) < (List.length (C.GLOBALS)) -> (C.GLOBALS[x]!) == (.mk_globaltype (some (.MUT)) (t)) -> Instr_ok (C) (.GLOBAL_GET (x)) (.mk_functype ([]) ([t]))
|      global_set (C : context) (x : globalidx) (t : valtype) : (x) < (List.length (C.GLOBALS)) -> (C.GLOBALS[x]!) == (.mk_globaltype (some (.MUT)) (t)) -> Instr_ok (C) (.GLOBAL_GET (x)) (.mk_functype ([t]) ([]))
