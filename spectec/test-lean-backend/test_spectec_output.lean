     abbrev localidx  : Type := Nat

     abbrev globalidx  : Type := Nat

     inductive «mut»  : Type where
  |      MUT  : «mut»


     inductive valtype  : Type where
  |      I32  : valtype
|      I64  : valtype
|      F32  : valtype
|      F64  : valtype


     inductive functype  : Type where
  |      mk_functype (valtype_lst : List valtype) (valtype_lst : List valtype) : functype


     inductive globaltype  : Type where
  |      mk_globaltype (mut_opt : Option «mut») (v_valtype : valtype) : globaltype


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


     structure context   where     MKcontext::  
      GLOBALS  : List globaltype
     LOCALS  : List valtype 
 
