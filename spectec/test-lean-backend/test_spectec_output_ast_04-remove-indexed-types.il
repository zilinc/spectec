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
        (Infix Arg -> Arg)
        (TupT
          (typbind "valtype*" (IterT (VarT "valtype") List))
          (typbind "valtype*" (IterT (VarT "valtype") List))
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
        (Seq Arg Arg)
        (TupT
          (typbind "mut?" (IterT (VarT "mut") Opt))
          (typbind "valtype" (VarT "valtype"))
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
          (typbind "valtype" (VarT "valtype"))
          (typbind "const" (VarT "const"))
        )
      )
      (typcase
        (Seq (Atom LOCAL.GET) Arg)
        (TupT (typbind "localidx" (VarT "localidx")))
      )
      (typcase
        (Seq (Atom LOCAL.SET) Arg)
        (TupT (typbind "localidx" (VarT "localidx")))
      )
      (typcase
        (Seq (Atom GLOBAL.GET) Arg)
        (TupT (typbind "globalidx" (VarT "globalidx")))
      )
      (typcase
        (Seq (Atom GLOBAL.SET) Arg)
        (TupT (typbind "globalidx" (VarT "globalidx")))
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
      (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE)))
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
      (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE)))
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
        (Infix Arg -> Arg)
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
      (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE (VarE "t"))))
    )
  )
  (RuleD
    "local.get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x")))
      (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE (VarE "t"))))
    )
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
    "local.set"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
      (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE)))
    )
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
    "global.get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x")))
      (CaseE (Infix Arg -> Arg) (TupE (ListE) (ListE (VarE "t"))))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom GLOBALS)) (VarE "x"))
        (CaseE (Seq Arg Arg) (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t")))
      )
    )
  )
  (RuleD
    "global.set"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x")))
      (CaseE (Infix Arg -> Arg) (TupE (ListE (VarE "t")) (ListE)))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom GLOBALS)) (VarE "x"))
        (CaseE (Seq Arg Arg) (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t")))
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
          (typbind "valtype" (VarT "valtype"))
          (typbind "const" (VarT "const"))
        )
      )
    )
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
        (Infix Arg ; Arg)
        (TupT (typbind "store" (VarT "store")) (typbind "frame" (VarT "frame")))
      )
    )
  )
)
(TypD
  "config"
  (InstD
    (VariantT
      (typcase
        (Infix Arg ; Arg)
        (TupT
          (typbind "state" (VarT "state"))
          (typbind "instr*" (IterT (VarT "instr") List))
        )
      )
    )
  )
)
(DecD
  "local"
  (ExpP "state" (VarT "state"))
  (ExpP "localidx" (VarT "localidx"))
  (VarT "val")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE (DotE (VarE "f") (Atom LOCALS)) (VarE "x"))
  )
)
(DecD
  "global"
  (ExpP "state" (VarT "state"))
  (ExpP "globalidx" (VarT "globalidx"))
  (VarT "val")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (VarE "s") (Atom GLOBALS))
      (IdxE (DotE (DotE (VarE "f") (Atom MODULE)) (Atom GLOBALS)) (VarE "x"))
    )
  )
)
(DecD
  "update_local"
  (ExpP "state" (VarT "state"))
  (ExpP "localidx" (VarT "localidx"))
  (ExpP "val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpP "v" (VarT "val"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Infix Arg ; Arg)
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
  (ExpP "state" (VarT "state"))
  (ExpP "globalidx" (VarT "globalidx"))
  (ExpP "val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpP "x" nat)
    (ExpP "v" (VarT "val"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Infix Arg ; Arg)
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
    (ExpP "val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (SubE (VarT "val") (VarT "instr") (VarE "val"))
        (CaseE (Atom DROP) (TupE))
      )
      (ListE)
    )
  )
  (RuleD
    "select-true"
    (ExpP "val_1" (VarT "val"))
    (ExpP "val_2" (VarT "val"))
    (ExpP "c" (VarT "const"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (SubE (VarT "val") (VarT "instr") (VarE "val_1"))
        (SubE (VarT "val") (VarT "instr") (VarE "val_2"))
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Atom SELECT) (TupE))
      )
      (ListE (SubE (VarT "val") (VarT "instr") (VarE "val_1")))
    )
    (IfPr (CmpE NeOp bool (VarE "c") (NumE (Nat 0))))
  )
  (RuleD
    "select-false"
    (ExpP "val_1" (VarT "val"))
    (ExpP "val_2" (VarT "val"))
    (ExpP "c" (VarT "const"))
    (Infix Arg ~> Arg)
    (TupE
      (ListE
        (SubE (VarT "val") (VarT "instr") (VarE "val_1"))
        (SubE (VarT "val") (VarT "instr") (VarE "val_2"))
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
        )
        (CaseE (Atom SELECT) (TupE))
      )
      (ListE (SubE (VarT "val") (VarT "instr") (VarE "val_2")))
    )
    ElsePr
  )
)
(RelD
  "Step"
  (Infix Arg ~> Arg)
  (TupT (typbind "_" (VarT "config")) (typbind "_" (VarT "config")))
  (RuleD
    "pure"
    (ExpP "z" (VarT "state"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "instr'*" (IterT (VarT "instr") List))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        )
      )
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
        )
      )
    )
    (RulePr
      "Step_pure"
      (Infix Arg ~> Arg)
      (TupE
        (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        (IterE (VarE "instr'") List (iterexp "instr'" (VarE "instr'*")))
      )
    )
  )
  (RuleD
    "local.get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x"))))
        )
      )
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (SubE (VarT "val") (VarT "instr") (VarE "val")))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "val")
        (CallE "local" (ExpA (VarE "z")) (ExpA (VarE "x")))
      )
    )
  )
  (RuleD
    "local.set"
    (ExpP "z" (VarT "state"))
    (ExpP "val" (VarT "val"))
    (ExpP "x" (VarT "localidx"))
    (ExpP "z'" (VarT "state"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (SubE (VarT "val") (VarT "instr") (VarE "val"))
            (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
          )
        )
      )
      (CaseE (Infix Arg ; Arg) (TupE (VarE "z'") (ListE)))
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
          (ExpA (VarE "val"))
        )
      )
    )
  )
  (RuleD
    "global.get"
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "val" (VarT "val"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
        )
      )
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE (SubE (VarT "val") (VarT "instr") (VarE "val")))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "val")
        (CallE "global" (ExpA (VarE "z")) (ExpA (VarE "x")))
      )
    )
  )
  (RuleD
    "global.set"
    (ExpP "z" (VarT "state"))
    (ExpP "val" (VarT "val"))
    (ExpP "x" (VarT "globalidx"))
    (ExpP "z'" (VarT "state"))
    (Infix Arg ~> Arg)
    (TupE
      (CaseE
        (Infix Arg ; Arg)
        (TupE
          (VarE "z")
          (ListE
            (SubE (VarT "val") (VarT "instr") (VarE "val"))
            (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
          )
        )
      )
      (CaseE (Infix Arg ; Arg) (TupE (VarE "z'") (ListE)))
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
          (ExpA (VarE "val"))
        )
      )
    )
  )
)
HintD
HintD
(DecD "float" (ExpP "nat" nat) (ExpP "_" (IterT nat List)) (VarT "const"))
(GramD
  "Bbyte"
  nat
  (ProdD
    (ExpP "<implicit-prod-result>" nat)
    (AttrG (VarE "<implicit-prod-result>") (RangeG (NumG 0x00) (NumG 0xFF)))
    (VarE "<implicit-prod-result>")
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
    (ExpP "<implicit-prod-result>" nat)
    (AttrG (VarE "<implicit-prod-result>") (VarG "Bu" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bu64"
  (VarT "const")
  (ProdD
    (ExpP "<implicit-prod-result>" nat)
    (AttrG (VarE "<implicit-prod-result>") (VarG "Bu" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bf"
  (ExpP "N" nat)
  nat
  (ProdD
    (ExpP "b*" (IterT nat List))
    (AttrG
      (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
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
    (CallE
      "float"
      (ExpA (VarE "N"))
      (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
    )
  )
)
(GramD
  "Bf32"
  (VarT "const")
  (ProdD
    (ExpP "<implicit-prod-result>" nat)
    (AttrG (VarE "<implicit-prod-result>") (VarG "Bf" (ExpA (NumE (Nat 32)))))
    (VarE "<implicit-prod-result>")
  )
)
(GramD
  "Bf64"
  (VarT "const")
  (ProdD
    (ExpP "<implicit-prod-result>" nat)
    (AttrG (VarE "<implicit-prod-result>") (VarG "Bf" (ExpA (NumE (Nat 64)))))
    (VarE "<implicit-prod-result>")
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
    (ExpP "mut" (VarT "mut"))
    (ExpP "t" (VarT "valtype"))
    (SeqG
      (SeqG (AttrG (VarE "t") (VarG "Bvaltype")))
      (SeqG (AttrG (OptE (VarE "mut")) (VarG "Bmut")))
    )
    (CaseE (Seq Arg Arg) (TupE (OptE (VarE "mut")) (VarE "t")))
  )
)
(GramD
  "Bresulttype"
  (IterT (VarT "valtype") List)
  (ProdD
    (ExpP "n" nat)
    (ExpP "t*" (IterT (VarT "valtype") List))
    (SeqG
      (SeqG (AttrG (VarE "n") (VarG "Bu32")))
      (SeqG
        (IterG
          (AttrG (VarE "t") (VarG "Bvaltype"))
          (ListN (VarE "n"))
          (iterexp "t" (VarE "t*"))
        )
      )
    )
    (IterE (VarE "t") (ListN (VarE "n")) (iterexp "t" (VarE "t*")))
  )
)
(GramD
  "Bfunctype"
  (VarT "functype")
  (ProdD
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (SeqG
      (SeqG (NumG 0x60))
      (SeqG
        (AttrG
          (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
          (VarG "Bresulttype")
        )
      )
      (SeqG
        (AttrG
          (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
          (VarG "Bresulttype")
        )
      )
    )
    (CaseE
      (Infix Arg -> Arg)
      (TupE
        (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
        (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
      )
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
    (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x21)) (SeqG (AttrG (VarE "x") (VarG "Blocalidx"))))
    (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x23)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
    (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x")))
  )
  (ProdD
    (ExpP "x" nat)
    (SeqG (SeqG (NumG 0x24)) (SeqG (AttrG (VarE "x") (VarG "Bglobalidx"))))
    (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
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

