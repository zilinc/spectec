import «wasm2.0»
import «custom_notation»
open functype list

def ai_principal_typing
    (p_store      : store)
    (p_context    : context)
    (p_admininstr : admininstr)
    (p_functype   : functype)
    : Prop :=
    match p_admininstr with
        | admininstr.NOP            => p_functype = ([] f-> [])
        | admininstr.UNREACHABLE    => true -- this is equivalent to the spec, which has no effective additonal constraints
        | admininstr.DROP           => ∃ (t : valtype),
                                           p_functype = ([t] f-> [])
        | admininstr.SELECT
            (some [(t : valtype)])  => p_functype = ([t, t, valtype.I32] f-> [t])
        | admininstr.SELECT
            none                    => ∃ (t t' : valtype),
                                           p_functype = ([t, t, valtype.I32] f-> [t])
                                         ∧ t sub< t'
                                         ∧ (
                                              ∃ (nt : numtype), t' = valtype_numtype nt
                                            ∨ ∃ (vt : vectype), t' = valtype_vectype vt
                                           )
        | admininstr.SELECT
            _                       => false
        | admininstr.BLOCK
            (bt : blocktype)
            (instrs : List instr)   => ∃ (t1s t2s : List valtype),
                                           p_functype = (t1s f-> t2s)
                                         ∧ Blocktype_ok p_context bt (t1s f-> t2s)
                                         ∧ Instrs_ok
                                               {p_context with LABELS := (list.mk_list t2s) :: p_context.LABELS}
                                               instrs
                                               (t1s f-> t2s)


def instr_principal_typing
    (context : context) (instruction : instr) (functype : functype) : Prop :=
    sorry

-- theorem instr_typing_inversion
--     (context : context) (instruction : instr) (t1 : valtype) (t2 : valtype) :
--     Instr_ok context instruction (t1 :-> t2) →
--     instr_principal_typing context instruction (t1 :-> t2) :=
