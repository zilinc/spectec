import «wasm2.0»
def mkFunctype (tf1 tf2 : List valtype) : functype :=
    functype.mk_functype (list.mk_list tf1) (list.mk_list tf2)

infix:67 "f->" => mkFunctype
infix:50 "sub<" => Valtype_sub

def prepend_label (C : context) (t : resulttype) : context :=
    { C with LABELS := t :: C.LABELS }
