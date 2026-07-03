(TypD "localidx" (InstD (AliasT nat)))
(TypD "globalidx" (InstD (AliasT nat)))
(TypD "mut" (InstD (VariantT (typcase (Atom MUT) (TupT)))))
(TypD
  "valtype"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom F32) (TupT))
      (typcase (Atom F64) (TupT))
    )
  )
)
(TypD
  "functype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_functype) Arg Arg)
        (TupT
          (typbind "valtype_lst" (IterT (VarT "valtype") List))
          (typbind "valtype_lst" (IterT (VarT "valtype") List))
        )
      )
    )
  )
)
(TypD
  "globaltype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_globaltype) Arg Arg)
        (TupT
          (typbind "mut_opt" (IterT (VarT "mut") Opt))
          (typbind "v_valtype" (VarT "valtype"))
        )
      )
    )
  )
)
(TypD "const" (InstD (AliasT nat)))
(TypD
  "instr"
  (InstD
    (VariantT
      (typcase (Atom NOP) (TupT))
      (typcase (Atom DROP) (TupT))
      (typcase (Atom SELECT) (TupT))
      (typcase
        (Seq (Atom CONST) Arg Arg)
        (TupT
          (typbind "v_valtype" (VarT "valtype"))
          (typbind "v_const" (VarT "const"))
        )
      )
      (typcase
        (Seq (Atom LOCAL_GET) Arg)
        (TupT (typbind "v_localidx" (VarT "localidx")))
      )
      (typcase
        (Seq (Atom LOCAL_SET) Arg)
        (TupT (typbind "v_localidx" (VarT "localidx")))
      )
      (typcase
        (Seq (Atom GLOBAL_GET) Arg)
        (TupT (typbind "v_globalidx" (VarT "globalidx")))
      )
      (typcase
        (Seq (Atom GLOBAL_SET) Arg)
        (TupT (typbind "v_globalidx" (VarT "globalidx")))
      )
    )
  )
)
(TypD
  "context"
  (InstD
    (StructT
      (typfield (Atom GLOBALS) (IterT (VarT "globaltype") List))
      (typfield (Atom LOCALS) (IterT (VarT "valtype") List))
    )
  )
)
(RelD
  "Instr_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "instr"))
    (typbind "_" (VarT "functype"))
  )
  (RuleD
    "nop"
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Atom NOP) (TupE))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE)))
    )
  )
  (RuleD
    "drop"
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Atom DROP) (TupE))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE (VarE "t")) (ListE)))
    )
  )
  (RuleD
    "select"
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Atom SELECT) (TupE))
      (CaseE
        (Seq (Atom mk_functype) Arg Arg)
        (TupE
          (ListE (VarE "t") (VarE "t") (CaseE (Atom I32) (TupE)))
          (ListE (VarE "t"))
        )
      )
    )
  )
  (RuleD
    "const"
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (ExpP "c" (VarT "const"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "t") (VarE "c")))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE (VarE "t"))))
    )
  )
  (RuleD
    "local_get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE (VarE "t"))))
    )
    (IfPr (CmpE LtOp nat (VarE "x") (LenE (DotE (VarE "C") (Atom LOCALS)))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom LOCALS)) (VarE "x"))
        (VarE "t")
      )
    )
  )
  (RuleD
    "local_set"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE (VarE "t")) (ListE)))
    )
    (IfPr (CmpE LtOp nat (VarE "x") (LenE (DotE (VarE "C") (Atom LOCALS)))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom LOCALS)) (VarE "x"))
        (VarE "t")
      )
    )
  )
  (RuleD
    "global_get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE) (ListE (VarE "t"))))
    )
    (IfPr (CmpE LtOp nat (VarE "x") (LenE (DotE (VarE "C") (Atom GLOBALS)))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom GLOBALS)) (VarE "x"))
        (CaseE
          (Seq (Atom mk_globaltype) Arg Arg)
          (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t"))
        )
      )
    )
  )
  (RuleD
    "global_set"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom mk_functype) Arg Arg) (TupE (ListE (VarE "t")) (ListE)))
    )
    (IfPr (CmpE LtOp nat (VarE "x") (LenE (DotE (VarE "C") (Atom GLOBALS)))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom GLOBALS)) (VarE "x"))
        (CaseE
          (Seq (Atom mk_globaltype) Arg Arg)
          (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t"))
        )
      )
    )
  )
)
(TypD "addr" (InstD (AliasT nat)))
(TypD
  "moduleinst"
  (InstD (StructT (typfield (Atom GLOBALS) (IterT (VarT "addr") List))))
)
(TypD
  "val"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom CONST) Arg Arg)
        (TupT
          (typbind "v_valtype" (VarT "valtype"))
          (typbind "v_const" (VarT "const"))
        )
      )
    )
  )
)
(DecD
  "instr_val"
  (ExpP "var_0" (VarT "val"))
  (VarT "instr")
  (DefD
    (ExpP "x0" (VarT "valtype"))
    (ExpP "x1" (VarT "const"))
    (ExpA (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "x0") (VarE "x1"))))
    (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "x0") (VarE "x1")))
  )
)
(TypD
  "store"
  (InstD (StructT (typfield (Atom GLOBALS) (IterT (VarT "val") List))))
)
(TypD
  "frame"
  (InstD
    (StructT
      (typfield (Atom LOCALS) (IterT (VarT "val") List))
      (typfield (Atom MODULE) (VarT "moduleinst"))
    )
  )
)
(TypD
  "state"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_state) Arg Arg)
        (TupT
          (typbind "v_store" (VarT "store"))
          (typbind "v_frame" (VarT "frame"))
        )
      )
    )
  )
)
(TypD
  "config"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_config) Arg Arg)
        (TupT
          (typbind "v_state" (VarT "state"))
          (typbind "instr_lst" (IterT (VarT "instr") List))
        )
      )
    )
  )
)
(DecD
  "local"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_localidx" (VarT "localidx"))
  (VarT "val")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
  )
)
(DecD
  "global"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_globalidx" (VarT "globalidx"))
  (VarT "val")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "s") (Atom GLOBALS))
      (IdxE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS)) (VarE "x"))
    )
  )
)
(DecD
  "update_local"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_localidx" (VarT "localidx"))
  (ExpP "v_val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpP "v" (VarT "val"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Seq (Atom mk_state) Arg Arg)
      (TupE
        (VarE "s")
        (UpdE
          (VarE "f")
          (IdxP (DotP RootP (Atom LOCALS)) (VarE "x"))
          (VarE "v")
        )
      )
    )
  )
)
(DecD
  "update_global"
  (ExpP "v_state" (VarT "state"))
  (ExpP "v_globalidx" (VarT "globalidx"))
  (ExpP "v_val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpP "v" (VarT "val"))
    (ExpA (CaseE (Seq (Atom mk_state) Arg Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Seq (Atom mk_state) Arg Arg)
      (TupE
        (UpdE
          (VarE "s")
          (IdxP
            (DotP RootP (Atom GLOBALS))
            (IdxE
              (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS))
              (VarE "x")
            )
          )
          (VarE "v")
        )
        (VarE "f")
      )
    )
  )
)
HintD
(RelD
  "Step_pure"
  (Infix Arg ~> Arg)
  (TupT
    (typbind "_" (IterT (VarT "instr") List))
    (typbind "_" (IterT (VarT "instr") List))
  )
  (RuleD
    "nop"
    (Infix Arg ~> Arg)
    (TupE (ListE (CaseE (Atom NOP) (TupE))) (ListE))
  )
  (RuleD
    "drop"
    (ExpP "v_val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "instr_val" (ExpA (VarE "v_val")))
        (CaseE (Atom DROP) (TupE))
      )
      (ListE)
    )
  )
  (RuleD
    "select_true"
    (ExpP "val_1" (VarT "val"))
    (ExpP "val_2" (VarT "val"))
    (ExpP "c" (VarT "const"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "instr_val" (ExpA (VarE "val_1")))
        (CallE "instr_val" (ExpA (VarE "val_2")))
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Atom SELECT) (TupE))
      )
      (ListE (CallE "instr_val" (ExpA (VarE "val_1"))))
    )
    (IfPr (CmpE NeOp bool (VarE "c") (NumE (Nat 0))))
  )
  (RuleD
    "select_false"
    (ExpP "val_1" (VarT "val"))
    (ExpP "val_2" (VarT "val"))
    (ExpP "c" (VarT "const"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (CallE "instr_val" (ExpA (VarE "val_1")))
        (CallE "instr_val" (ExpA (VarE "val_2")))
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Atom SELECT) (TupE))
      )
      (ListE (CallE "instr_val" (ExpA (VarE "val_2"))))
    )
    (IfPr (CmpE EqOp bool (VarE "c") (NumE (Nat 0))))
  )
)
(RelD
  "Step"
  (Infix Arg ~> Arg)
  (TupT (typbind "_" (VarT "config")) (typbind "_" (VarT "config")))
  (RuleD
    "pure"
    (ExpP "z" (VarT "state"))
    (ExpP "instr_lst" (IterT (VarT "instr") List))
    (ExpP "instr'_lst" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE (VarE "z") (VarE "instr_lst"))
      )
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE (VarE "z") (VarE "instr'_lst"))
      )
    )
    (RulePr
      "Step_pure"
      (Infix Arg ~> Arg)
      (TupE (VarE "instr_lst") (VarE "instr'_lst"))
    )
  )
  (RuleD
    "local_get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "v_val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x"))))
        )
      )
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE (VarE "z") (ListE (CallE "instr_val" (ExpA (VarE "v_val")))))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_val")
        (CallE "local" (ExpA (VarE "z")) (ExpA (VarE "x")))
      )
    )
  )
  (RuleD
    "local_set"
    (ExpP "z" (VarT "state"))
    (ExpP "v_val" (VarT "val"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "z'" (VarT "state"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE
            (CallE "instr_val" (ExpA (VarE "v_val")))
            (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
          )
        )
      )
      (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "z'") (ListE)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "z'")
        (CallE
          "update_local"
          (ExpA (VarE "z"))
          (ExpA (VarE "x"))
          (ExpA (VarE "v_val"))
        )
      )
    )
  )
  (RuleD
    "global_get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "v_val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x"))))
        )
      )
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE (VarE "z") (ListE (CallE "instr_val" (ExpA (VarE "v_val")))))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "v_val")
        (CallE "global" (ExpA (VarE "z")) (ExpA (VarE "x")))
      )
    )
  )
  (RuleD
    "global_set"
    (ExpP "z" (VarT "state"))
    (ExpP "v_val" (VarT "val"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "z'" (VarT "state"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Seq (Atom mk_config) Arg Arg)
        (TupE
          (VarE "z")
          (ListE
            (CallE "instr_val" (ExpA (VarE "v_val")))
            (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x")))
          )
        )
      )
      (CaseE (Seq (Atom mk_config) Arg Arg) (TupE (VarE "z'") (ListE)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "z'")
        (CallE
          "update_global"
          (ExpA (VarE "z"))
          (ExpA (VarE "x"))
          (ExpA (VarE "v_val"))
        )
      )
    )
  )
)
HintD
HintD
(DecD
  "float"
  (ExpP "nat" nat)
  (ExpP "var_0_lst" (IterT nat List))
  (VarT "const")
)
(GramD
  "Bbyte"
  nat
  (ProdD
    (ExpP "<implicit_prod_result>" nat)
    (AttrG (VarE "<implicit_prod_result>") (RangeG (NumG 0x00) (NumG 0xFF)))
    (VarE "<implicit_prod_result>")
  )
)
(RecD
  (GramD
    "Bu"
    (ExpP "N" nat)
    nat
    (ProdD
      (ExpP "n" nat)
      (AttrG (VarE "n") (VarG "Bbyte"))
      (VarE "n")
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            LtOp
            nat
            (VarE "n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE LtOp nat (VarE "n") (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
        )
      )
    )
    (ProdD
      (ExpP "m" nat)
      (ExpP "n" nat)
      (SeqG
        (SeqG (AttrG (VarE "n") (VarG "Bbyte")))
        (SeqG
          (AttrG
            (VarE "m")
            (VarG
              "Bu"
              (ExpA
                (CvtE
                  int
                  nat
                  (BinE
                    SubOp
                    int
                    (CvtE nat int (VarE "N"))
                    (CvtE nat int (NumE (Nat 7)))
                  )
                )
              )
            )
          )
        )
      )
      (BinE
        AddOp
        nat
        (BinE
          MulOp
          nat
          (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          (VarE "m")
        )
        (CvtE
          int
          nat
          (BinE
            SubOp
            int
            (CvtE nat int (VarE "n"))
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7))))
          )
        )
      )
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE
            GeOp
            nat
            (VarE "n")
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 7)))
          )
          (CmpE GtOp nat (VarE "N") (NumE (Nat 7)))
        )
      )
    )
  )
)
(GramD
  "Bu32"
  (VarT "const")
  (ProdD
    (ExpP "<implicit_prod_result>" nat)
    (AttrG (VarE "<implicit_prod_result>") (VarG "Bu" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bu64"
  (VarT "const")
  (ProdD
    (ExpP "<implicit_prod_result>" nat)
    (AttrG (VarE "<implicit_prod_result>") (VarG "Bu" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bf"
  (ExpP "N" nat)
  nat
  (ProdD
    (ExpP "b_lst" (IterT nat List))
    (AttrG
      (VarE "b_lst")
      (IterG
        (VarG "Bbyte")
        (ListN
          (CvtE
            rat
            nat
            (BinE
              DivOp
              rat
              (CvtE nat rat (VarE "N"))
              (CvtE nat rat (NumE (Nat 8)))
            )
          )
        )
      )
    )
    (CallE "float" (ExpA (VarE "N")) (ExpA (VarE "b_lst")))
  )
)
(GramD
  "Bf32"
  (VarT "const")
  (ProdD
    (ExpP "<implicit_prod_result>" nat)
    (AttrG (VarE "<implicit_prod_result>") (VarG "Bf" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bf64"
  (VarT "const")
  (ProdD
    (ExpP "<implicit_prod_result>" nat)
    (AttrG (VarE "<implicit_prod_result>") (VarG "Bf" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit_prod_result>")
  )
)
(GramD
  "Bvaltype"
  (VarT "valtype")
  (ProdD (NumG 0x7F) (CaseE (Atom I32) (TupE)))
  (ProdD (NumG 0x7E) (CaseE (Atom I64) (TupE)))
  (ProdD (NumG 0x7D) (CaseE (Atom F32) (TupE)))
  (ProdD (NumG 0x7C) (CaseE (Atom F64) (TupE)))
)
(GramD
  "Bmut"
  (IterT (VarT "mut") Opt)
  (ProdD (NumG 0x00) (OptE))
  (ProdD (NumG 0x01) (OptE (CaseE (Atom MUT) (TupE))))
)
(GramD
  "Bglobaltype"
  (VarT "globaltype")
  (ProdD
    (ExpP "v_mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (SeqG
      (SeqG (AttrG (VarE "t") (VarG "Bvaltype")))
      (SeqG (AttrG (OptE (VarE "v_mut")) (VarG "Bmut")))
    )
    (CaseE
      (Seq (Atom mk_globaltype) Arg Arg)
      (TupE (OptE (VarE "v_mut")) (VarE "t"))
    )
  )
)
(GramD
  "Bresulttype"
  (IterT (VarT "valtype") List)
  (ProdD
    (ExpP "n" nat)
    (ExpP "t_lst" (IterT (VarT "valtype") List))
    (SeqG
      (SeqG (AttrG (VarE "n") (VarG "Bu32")))
      (SeqG
        (IterG
          (AttrG (VarE "t") (VarG "Bvaltype"))
          (ListN (VarE "n"))
          (iterexp "t" (VarE "t_lst"))
        )
      )
    )
    (VarE "t_lst")
  )
)
(GramD
  "Bfunctype"
  (VarT "functype")
  (ProdD
    (ExpP "t_1_lst" (IterT (VarT "valtype") List))
    (ExpP "t_2_lst" (IterT (VarT "valtype") List))
    (SeqG
      (SeqG (NumG 0x60))
      (SeqG (AttrG (VarE "t_1_lst") (VarG "Bresulttype")))
      (SeqG (AttrG (VarE "t_2_lst") (VarG "Bresulttype")))
    )
    (CaseE
      (Seq (Atom mk_functype) Arg Arg)
      (TupE (VarE "t_1_lst") (VarE "t_2_lst"))
    )
  )
)
(GramD
  "Bglobalidx"
  (VarT "globalidx")
  (ProdD (ExpP "x" nat) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Blocalidx"
  (VarT "localidx")
  (ProdD (ExpP "x" nat) (AttrG (VarE "x") (VarG "Bu32")) (VarE "x"))
)
(GramD
  "Binstr"
  (VarT "instr")
  (ProdD (NumG 0x01) (CaseE (Atom NOP) (TupE)))
  (ProdD (NumG 0x1A) (CaseE (Atom DROP) (TupE)))
  (ProdD (NumG 0x1B) (CaseE (Atom SELECT) (TupE)))
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x20)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
    (CaseE (Seq (Atom LOCAL_GET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x21)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
    (CaseE (Seq (Atom LOCAL_SET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x23)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
    (CaseE (Seq (Atom GLOBAL_GET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x24)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
    (CaseE (Seq (Atom GLOBAL_SET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "n" nat)
    (SeqG (SeqG (NumG 0x41)) (SeqG (AttrG (VarE "n") (VarG "Bu32"))))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE (CaseE (Atom I32) (TupE)) (VarE "n"))
    )
  )
  (ProdD
    (ExpP "n" nat)
    (SeqG (SeqG (NumG 0x42)) (SeqG (AttrG (VarE "n") (VarG "Bu64"))))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE (CaseE (Atom I64) (TupE)) (VarE "n"))
    )
  )
  (ProdD
    (ExpP "p" nat)
    (SeqG (SeqG (NumG 0x43)) (SeqG (AttrG (VarE "p") (VarG "Bf32"))))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE (CaseE (Atom F32) (TupE)) (VarE "p"))
    )
  )
  (ProdD
    (ExpP "p" nat)
    (SeqG (SeqG (NumG 0x44)) (SeqG (AttrG (VarE "p") (VarG "Bf64"))))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE (CaseE (Atom F64) (TupE)) (VarE "p"))
    )
  )
)

