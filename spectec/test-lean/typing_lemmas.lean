import «wasm2.0»
open functype list

notation tf1 ":->" tf2 => functype.mk_functype (list.mk_list tf1) (list.mk_list tf2)

def ai_principal_typing
    (store      : store)
    (context    : context)
    (admininstr : admininstr)
    (functype   : functype)
    : Prop :=
    match admininstr with
        | admininstr.NOP => functype = ([] :-> [])
        | admininstr.UNREACHABLE => true

def instr_principal_typing
    (context : context) (instruction : instr) (functype : functype) : Prop :=
    sorry

-- theorem instr_typing_inversion
--     (context : context) (instruction : instr) (t1 : valtype) (t2 : valtype) :
--     Instr_ok context instruction (t1 :-> t2) →
--     instr_principal_typing context instruction (t1 :-> t2) :=
