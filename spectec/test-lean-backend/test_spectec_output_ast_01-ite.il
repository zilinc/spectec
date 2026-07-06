(TypD "MUT" (InstD (VariantT (typcase (Atom MUT) (TupT)))))
HintD
(TypD "N" (InstD (AliasT nat)))
HintD
(TypD "M" (InstD (AliasT nat)))
HintD
(TypD "n" (InstD (AliasT nat)))
HintD
(TypD "m" (InstD (AliasT nat)))
HintD
(DecD "Ki" nat (DefD (NumE (Nat 1024))))
(DecD
  "min"
  (ExpP "nat" nat)
  (ExpP "nat" nat)
  nat
  (DefD
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpA (VarE "i"))
    (ExpA (VarE "j"))
    (IfE (CmpE LeOp nat (VarE "i") (VarE "j")) (VarE "i") (VarE "j"))
  )
)
(RecD
  (DecD
    "sum"
    (ExpP "_" (IterT nat List))
    nat
    (DefD (ExpA (ListE)) (NumE (Nat 0)))
    (DefD
      (ExpP "n" (VarT "n"))
      (ExpP "n'*" (IterT (VarT "n") List))
      (ExpA
        (CatE
          (ListE (VarE "n"))
          (IterE (VarE "n'") List (iterexp "n'" (VarE "n'*")))
        )
      )
      (BinE
        AddOp
        nat
        (VarE "n")
        (CallE
          "sum"
          (ExpA (IterE (VarE "n'") List (iterexp "n'" (VarE "n'*"))))
        )
      )
    )
  )
)
(DecD
  "opt_"
  (TypP "X")
  (ExpP "_" (IterT (VarT "X") List))
  (IterT (VarT "X") Opt)
  (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (OptE))
  (DefD
    (TypP "X")
    (ExpP "w" (VarT "X"))
    (TypA (VarT "X"))
    (ExpA (ListE (VarE "w")))
    (OptE (VarE "w"))
  )
)
HintD
(DecD
  "list_"
  (TypP "X")
  (ExpP "_" (IterT (VarT "X") Opt))
  (IterT (VarT "X") List)
  (DefD (TypP "X") (TypA (VarT "X")) (ExpA (OptE)) (ListE))
  (DefD
    (TypP "X")
    (ExpP "w" (VarT "X"))
    (TypA (VarT "X"))
    (ExpA (OptE (VarE "w")))
    (ListE (VarE "w"))
  )
)
HintD
(RecD
  (DecD
    "concat_"
    (TypP "X")
    (ExpP "_" (IterT (IterT (VarT "X") List) List))
    (IterT (VarT "X") List)
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (ListE))
    (DefD
      (TypP "X")
      (ExpP "w*" (IterT (VarT "X") List))
      (ExpP "w'**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (IterE (VarE "w") List (iterexp "w" (VarE "w*"))))
          (IterE
            (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
            List
            (iterexp "w'*" (VarE "w'**"))
          )
        )
      )
      (CatE
        (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
        (CallE
          "concat_"
          (TypA (VarT "X"))
          (ExpA
            (IterE
              (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
              List
              (iterexp "w'*" (VarE "w'**"))
            )
          )
        )
      )
    )
  )
)
HintD
(RecD
  (DecD
    "disjoint_"
    (TypP "X")
    (ExpP "_" (IterT (VarT "X") List))
    BoolT
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (BoolE true))
    (DefD
      (TypP "X")
      (ExpP "w" (VarT "X"))
      (ExpP "w'*" (IterT (VarT "X") List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (VarE "w"))
          (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
        )
      )
      (BinE
        AndOp
        bool
        (UnE
          NotOp
          bool
          (MemE (VarE "w") (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
        )
        (CallE
          "disjoint_"
          (TypA (VarT "X"))
          (ExpA (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
        )
      )
    )
  )
)
HintD
(RelD
  "Nat_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" nat) (typbind "_" nat))
  (RuleD
    "refl"
    (ExpP "n" (VarT "n"))
    (Infix Arg |- Arg)
    (TupE (VarE "n") (VarE "n"))
  )
)
(RelD
  "Nats_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" (IterT nat List)) (typbind "_" (IterT nat List)))
  (RuleD
    "all"
    (ExpP "n*" (IterT (VarT "n") List))
    (Infix Arg |- Arg)
    (TupE
      (IterE (VarE "n") List (iterexp "n" (VarE "n*")))
      (IterE (VarE "n") List (iterexp "n" (VarE "n*")))
    )
    (IterPr
      (RulePr "Nat_ok" (Infix Arg |- Arg) (TupE (VarE "n") (VarE "n")))
      List
      (iterexp "n" (VarE "n*"))
    )
  )
)
(RelD
  "Pair_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" nat) (typbind "_" nat))
  (RuleD
    "eq"
    (ExpP "n" (VarT "n"))
    (Infix Arg |- Arg)
    (TupE (VarE "n") (VarE "n"))
  )
)
(RelD
  "Pairs_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" (IterT nat List)) (typbind "_" (IterT nat List)))
  (RuleD
    "all"
    (ExpP "n*" (IterT (VarT "n") List))
    (ExpP "m*" (IterT (VarT "m") List))
    (Infix Arg |- Arg)
    (TupE
      (IterE (VarE "n") List (iterexp "n" (VarE "n*")))
      (IterE (VarE "m") List (iterexp "m" (VarE "m*")))
    )
    (IterPr
      (RulePr "Pair_ok" (Infix Arg |- Arg) (TupE (VarE "n") (VarE "m")))
      List
      (iterexp "m" (VarE "m*"))
      (iterexp "n" (VarE "n*"))
    )
  )
)
(TypD
  "list"
  (TypP "X")
  (InstD
    (TypP "X")
    (TypA (VarT "X"))
    (VariantT
      (typcase
        Arg
        (TupT (typbind "X*" (IterT (VarT "X") List)))
        (IfPr
          (CmpE
            LtOp
            nat
            (LenE (IterE (VarE "X") List (iterexp "X" (VarE "X*"))))
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32)))
          )
        )
      )
    )
  )
)
(TypD
  "byte"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" nat))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE GeOp nat (VarE "i") (NumE (Nat 0)))
            (CmpE LeOp nat (VarE "i") (NumE (Nat 255)))
          )
        )
      )
    )
  )
)
HintD
(TypD
  "uN"
  (ExpP "N" (VarT "N"))
  (InstD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" nat))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE GeOp nat (VarE "i") (NumE (Nat 0)))
            (CmpE
              LeOp
              nat
              (VarE "i")
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
    )
  )
)
HintD
(TypD
  "sN"
  (ExpP "N" (VarT "N"))
  (InstD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" int))
        (IfPr
          (BinE
            OrOp
            bool
            (BinE
              OrOp
              bool
              (BinE
                AndOp
                bool
                (CmpE
                  GeOp
                  int
                  (VarE "i")
                  (UnE
                    MinusOp
                    int
                    (CvtE
                      nat
                      int
                      (BinE
                        PowOp
                        nat
                        (NumE (Nat 2))
                        (CvtE
                          int
                          nat
                          (BinE
                            SubOp
                            int
                            (CvtE nat int (VarE "N"))
                            (CvtE nat int (NumE (Nat 1)))
                          )
                        )
                      )
                    )
                  )
                )
                (CmpE
                  LeOp
                  int
                  (VarE "i")
                  (UnE MinusOp int (CvtE nat int (NumE (Nat 1))))
                )
              )
              (CmpE EqOp bool (VarE "i") (CvtE nat int (NumE (Nat 0))))
            )
            (BinE
              AndOp
              bool
              (CmpE
                GeOp
                int
                (VarE "i")
                (UnE PlusOp int (CvtE nat int (NumE (Nat 1))))
              )
              (CmpE
                LeOp
                int
                (VarE "i")
                (BinE
                  SubOp
                  int
                  (CvtE
                    nat
                    int
                    (BinE
                      PowOp
                      nat
                      (NumE (Nat 2))
                      (CvtE
                        int
                        nat
                        (BinE
                          SubOp
                          int
                          (CvtE nat int (VarE "N"))
                          (CvtE nat int (NumE (Nat 1)))
                        )
                      )
                    )
                  )
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
    )
  )
)
HintD
(TypD
  "iN"
  (ExpP "N" (VarT "N"))
  (InstD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (AliasT (VarT "uN" (ExpA (VarE "N"))))
  )
)
HintD
(TypD "u31" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 31)))))))
(TypD "u32" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 32)))))))
(TypD "u64" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 64)))))))
(TypD "i32" (InstD (AliasT (VarT "iN" (ExpA (NumE (Nat 32)))))))
(TypD "i64" (InstD (AliasT (VarT "iN" (ExpA (NumE (Nat 64)))))))
(DecD
  "signif"
  (ExpP "N" (VarT "N"))
  nat
  (DefD (ExpA (NumE (Nat 32))) (NumE (Nat 23)))
  (DefD (ExpA (NumE (Nat 64))) (NumE (Nat 52)))
)
HintD
(DecD
  "expon"
  (ExpP "N" (VarT "N"))
  nat
  (DefD (ExpA (NumE (Nat 32))) (NumE (Nat 8)))
  (DefD (ExpA (NumE (Nat 64))) (NumE (Nat 11)))
)
HintD
(DecD
  "M"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (CallE "signif" (ExpA (VarE "N")))
  )
)
HintD
(DecD
  "E"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (CallE "expon" (ExpA (VarE "N")))
  )
)
HintD
(TypD "exp" (InstD (AliasT int)))
(TypD
  "fNmag"
  (ExpP "N" (VarT "N"))
  (InstD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (VariantT
      (typcase
        (Seq (Atom NORM) Arg Arg)
        (TupT (typbind "m" (VarT "m")) (typbind "exp" (VarT "exp")))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              LtOp
              nat
              (VarE "m")
              (BinE PowOp nat (NumE (Nat 2)) (CallE "M" (ExpA (VarE "N"))))
            )
            (BinE
              AndOp
              bool
              (CmpE
                LeOp
                int
                (BinE
                  SubOp
                  int
                  (CvtE nat int (NumE (Nat 2)))
                  (CvtE
                    nat
                    int
                    (BinE
                      PowOp
                      nat
                      (NumE (Nat 2))
                      (CvtE
                        int
                        nat
                        (BinE
                          SubOp
                          int
                          (CvtE nat int (CallE "E" (ExpA (VarE "N"))))
                          (CvtE nat int (NumE (Nat 1)))
                        )
                      )
                    )
                  )
                )
                (VarE "exp")
              )
              (CmpE
                LeOp
                int
                (VarE "exp")
                (BinE
                  SubOp
                  int
                  (CvtE
                    nat
                    int
                    (BinE
                      PowOp
                      nat
                      (NumE (Nat 2))
                      (CvtE
                        int
                        nat
                        (BinE
                          SubOp
                          int
                          (CvtE nat int (CallE "E" (ExpA (VarE "N"))))
                          (CvtE nat int (NumE (Nat 1)))
                        )
                      )
                    )
                  )
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom SUBNORM) Arg)
        (TupT (typbind "m" (VarT "m")))
        (ExpP "exp" (VarT "exp"))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              LtOp
              nat
              (VarE "m")
              (BinE PowOp nat (NumE (Nat 2)) (CallE "M" (ExpA (VarE "N"))))
            )
            (CmpE
              EqOp
              bool
              (BinE
                SubOp
                int
                (CvtE nat int (NumE (Nat 2)))
                (CvtE
                  nat
                  int
                  (BinE
                    PowOp
                    nat
                    (NumE (Nat 2))
                    (CvtE
                      int
                      nat
                      (BinE
                        SubOp
                        int
                        (CvtE nat int (CallE "E" (ExpA (VarE "N"))))
                        (CvtE nat int (NumE (Nat 1)))
                      )
                    )
                  )
                )
              )
              (VarE "exp")
            )
          )
        )
      )
      (typcase (Atom INF) (TupT))
      (typcase
        (Seq (Atom NAN) Arg)
        (TupT (typbind "m" (VarT "m")))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE LeOp nat (NumE (Nat 1)) (VarE "m"))
            (CmpE
              LtOp
              nat
              (VarE "m")
              (BinE PowOp nat (NumE (Nat 2)) (CallE "M" (ExpA (VarE "N"))))
            )
          )
        )
      )
    )
  )
)
(TypD
  "fN"
  (ExpP "N" (VarT "N"))
  (InstD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (VariantT
      (typcase
        (Seq (Atom POS) Arg)
        (TupT (typbind "_" (VarT "fNmag" (ExpA (VarE "N")))))
      )
      (typcase
        (Seq (Atom NEG) Arg)
        (TupT (typbind "_" (VarT "fNmag" (ExpA (VarE "N")))))
      )
    )
  )
)
HintD
HintD
HintD
(TypD "f32" (InstD (AliasT (VarT "fN" (ExpA (NumE (Nat 32)))))))
(TypD "f64" (InstD (AliasT (VarT "fN" (ExpA (NumE (Nat 64)))))))
(DecD
  "fzero"
  (ExpP "N" (VarT "N"))
  (VarT "fN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (CaseE
      (Seq (Atom POS) Arg)
      (TupE (CaseE (Seq (Atom SUBNORM) Arg) (TupE (NumE (Nat 0)))))
    )
  )
)
HintD
(DecD
  "fone"
  (ExpP "N" (VarT "N"))
  (VarT "fN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (CaseE
      (Seq (Atom POS) Arg)
      (TupE
        (CaseE
          (Seq (Atom NORM) Arg Arg)
          (TupE (NumE (Nat 1)) (CvtE nat int (NumE (Nat 0))))
        )
      )
    )
  )
)
HintD
(DecD
  "canon_"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (BinE
      PowOp
      nat
      (NumE (Nat 2))
      (CvtE
        int
        nat
        (BinE
          SubOp
          int
          (CvtE nat int (CallE "signif" (ExpA (VarE "N"))))
          (CvtE nat int (NumE (Nat 1)))
        )
      )
    )
  )
)
(TypD
  "char"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" nat))
        (IfPr
          (BinE
            OrOp
            bool
            (BinE
              AndOp
              bool
              (CmpE GeOp nat (VarE "i") (NumE (Nat 0)))
              (CmpE LeOp nat (VarE "i") (NumE (Nat 55295)))
            )
            (BinE
              AndOp
              bool
              (CmpE GeOp nat (VarE "i") (NumE (Nat 57344)))
              (CmpE LeOp nat (VarE "i") (NumE (Nat 1114111)))
            )
          )
        )
      )
    )
  )
)
HintD
(DecD "utf8" (ExpP "_" (IterT (VarT "char") List)) (IterT (VarT "byte") List))
(TypD
  "name"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "char*" (IterT (VarT "char") List)))
        (IfPr
          (CmpE
            LtOp
            nat
            (LenE
              (CallE
                "utf8"
                (ExpA
                  (IterE (VarE "char") List (iterexp "char" (VarE "char*")))
                )
              )
            )
            (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32)))
          )
        )
      )
    )
  )
)
HintD
(TypD "idx" (InstD (AliasT (VarT "u32"))))
HintD
(TypD "typeidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "funcidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "globalidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "tableidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "memidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "labelidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "localidx" (InstD (AliasT (VarT "idx"))))
HintD
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
HintD
(TypD
  "Inn"
  (InstD (VariantT (typcase (Atom I32) (TupT)) (typcase (Atom I64) (TupT))))
)
HintD
(TypD
  "Fnn"
  (InstD (VariantT (typcase (Atom F32) (TupT)) (typcase (Atom F64) (TupT))))
)
HintD
(TypD "resulttype" (InstD (AliasT (IterT (VarT "valtype") Opt))))
HintD
(TypD "mut" (InstD (AliasT (IterT (VarT "MUT") Opt))))
(TypD
  "limits"
  (InstD
    (VariantT
      (typcase
        (Brack [ (Infix Arg .. Arg) ])
        (TupT
          (typbind "u32" (VarT "u32"))
          (typbind "u32?" (IterT (VarT "u32") Opt))
        )
      )
    )
  )
)
HintD
(TypD
  "globaltype"
  (InstD
    (VariantT
      (typcase
        (Seq Arg Arg)
        (TupT (typbind "mut" (VarT "mut")) (typbind "valtype" (VarT "valtype")))
      )
    )
  )
)
HintD
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
HintD
(TypD "tabletype" (InstD (AliasT (VarT "limits"))))
HintD
(TypD "memtype" (InstD (AliasT (VarT "limits"))))
HintD
(TypD
  "externtype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "functype" (VarT "functype")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globaltype" (VarT "globaltype")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tabletype" (VarT "tabletype")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memtype" (VarT "memtype"))))
    )
  )
)
HintD
(DecD "size" (ExpP "valtype" (VarT "valtype")) nat)
HintD
(TypD
  "val_"
  (ExpP "valtype" (VarT "valtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
    (AliasT
      (VarT
        "iN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
          )
        )
      )
    )
  )
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "valtype") (VarE "Fnn")))
    (AliasT
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "valtype") (VarE "Fnn")))
          )
        )
      )
    )
  )
)
(TypD
  "sx"
  (InstD (VariantT (typcase (Atom U) (TupT)) (typcase (Atom S) (TupT))))
)
HintD
(TypD
  "sz"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" nat))
        (IfPr
          (BinE
            OrOp
            bool
            (BinE
              OrOp
              bool
              (BinE
                OrOp
                bool
                (CmpE EqOp bool (VarE "i") (NumE (Nat 8)))
                (CmpE EqOp bool (VarE "i") (NumE (Nat 16)))
              )
              (CmpE EqOp bool (VarE "i") (NumE (Nat 32)))
            )
            (CmpE EqOp bool (VarE "i") (NumE (Nat 64)))
          )
        )
      )
    )
  )
)
HintD
(TypD
  "unop_"
  (ExpP "valtype" (VarT "valtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
    (VariantT
      (typcase (Atom CLZ) (TupT))
      (typcase (Atom CTZ) (TupT))
      (typcase (Atom POPCNT) (TupT))
    )
  )
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "valtype") (VarE "Fnn")))
    (VariantT
      (typcase (Atom ABS) (TupT))
      (typcase (Atom NEG) (TupT))
      (typcase (Atom SQRT) (TupT))
      (typcase (Atom CEIL) (TupT))
      (typcase (Atom FLOOR) (TupT))
      (typcase (Atom TRUNC) (TupT))
      (typcase (Atom NEAREST) (TupT))
    )
  )
)
(TypD
  "binop_"
  (ExpP "valtype" (VarT "valtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
    (VariantT
      (typcase (Atom ADD) (TupT))
      (typcase (Atom SUB) (TupT))
      (typcase (Atom MUL) (TupT))
      (typcase (Seq (Atom DIV) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom REM) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom AND) (TupT))
      (typcase (Atom OR) (TupT))
      (typcase (Atom XOR) (TupT))
      (typcase (Atom SHL) (TupT))
      (typcase (Seq (Atom SHR) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom ROTL) (TupT))
      (typcase (Atom ROTR) (TupT))
    )
  )
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "valtype") (VarE "Fnn")))
    (VariantT
      (typcase (Atom ADD) (TupT))
      (typcase (Atom SUB) (TupT))
      (typcase (Atom MUL) (TupT))
      (typcase (Atom DIV) (TupT))
      (typcase (Atom MIN) (TupT))
      (typcase (Atom MAX) (TupT))
      (typcase (Atom COPYSIGN) (TupT))
    )
  )
)
(TypD
  "testop_"
  (ExpP "valtype" (VarT "valtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
    (VariantT (typcase (Atom EQZ) (TupT)))
  )
)
(TypD
  "relop_"
  (ExpP "valtype" (VarT "valtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
    (VariantT
      (typcase (Atom EQ) (TupT))
      (typcase (Atom NE) (TupT))
      (typcase (Seq (Atom LT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom GT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom LE) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom GE) Arg) (TupT (typbind "sx" (VarT "sx"))))
    )
  )
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "valtype") (VarE "Fnn")))
    (VariantT
      (typcase (Atom EQ) (TupT))
      (typcase (Atom NE) (TupT))
      (typcase (Atom LT) (TupT))
      (typcase (Atom GT) (TupT))
      (typcase (Atom LE) (TupT))
      (typcase (Atom GE) (TupT))
    )
  )
)
(TypD
  "cvtop"
  (InstD
    (VariantT
      (typcase (Seq (Atom EXTEND) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom WRAP) (TupT))
      (typcase (Seq (Atom CONVERT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom TRUNC) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Atom PROMOTE) (TupT))
      (typcase (Atom DEMOTE) (TupT))
      (typcase (Atom REINTERPRET) (TupT))
    )
  )
)
(TypD
  "memarg"
  (InstD
    (StructT
      (typfield (Atom ALIGN) (VarT "u32"))
      (typfield (Atom OFFSET) (VarT "u32"))
    )
  )
)
HintD
(TypD
  "loadop_"
  (ExpP "valtype" (VarT "valtype"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
    (VariantT
      (typcase
        (Seq Arg (Atom _) Arg)
        (TupT (typbind "sz" (VarT "sz")) (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (UncaseE (VarE "sz") Arg) 0)
            (CallE
              "size"
              (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
            )
          )
        )
      )
    )
  )
)
(TypD "blocktype" (InstD (AliasT (IterT (VarT "valtype") Opt))))
HintD
(RecD
  (TypD
    "instr"
    (InstD
      (VariantT
        (typcase (Atom NOP) (TupT))
        (typcase (Atom UNREACHABLE) (TupT))
        (typcase (Atom DROP) (TupT))
        (typcase (Atom SELECT) (TupT))
        (typcase
          (Seq (Atom BLOCK) Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom LOOP) Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "instr*" (IterT (VarT "instr") List))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom BR) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_IF) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupT
            (typbind "labelidx*" (IterT (VarT "labelidx") List))
            (typbind "labelidx" (VarT "labelidx"))
          )
        )
        (typcase
          (Seq (Atom CALL) Arg)
          (TupT (typbind "funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom CALL_INDIRECT) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase (Atom RETURN) (TupT))
        (typcase
          (Seq (Atom CONST) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "val_" (ExpA (VarE "valtype"))))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "unop_" (ExpA (VarE "valtype"))))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "binop_" (ExpA (VarE "valtype"))))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "testop_" (ExpA (VarE "valtype"))))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "relop_" (ExpA (VarE "valtype"))))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "valtype_1" (VarT "valtype"))
            (typbind "valtype_2" (VarT "valtype"))
            (typbind "cvtop" (VarT "cvtop"))
          )
          (IfPr (CmpE NeOp bool (VarE "valtype_1") (VarE "valtype_2")))
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
          (Seq (Atom LOCAL.TEE) Arg)
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
        (typcase
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (IterT (VarT "loadop_" (ExpA (VarE "valtype"))) Opt))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom STORE) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "sz?" (IterT (VarT "sz") Opt))
            (typbind "memarg" (VarT "memarg"))
          )
          (ExpP "Inn?" (IterT (VarT "Inn") Opt))
          (ExpP "valtype?" (IterT (VarT "valtype") Opt))
          (IterPr
            (IfPr
              (BinE
                AndOp
                bool
                (CmpE
                  EqOp
                  bool
                  (VarE "valtype")
                  (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn"))
                )
                (CmpE
                  LtOp
                  nat
                  (ProjE (UncaseE (VarE "sz") Arg) 0)
                  (CallE
                    "size"
                    (ExpA (SubE (VarT "Inn") (VarT "valtype") (VarE "Inn")))
                  )
                )
              )
            )
            Opt
            (iterexp "Inn" (VarE "Inn?"))
            (iterexp "sz" (VarE "sz?"))
            (iterexp "valtype" (VarE "valtype?"))
          )
        )
        (typcase (Atom MEMORY.SIZE) (TupT))
        (typcase (Atom MEMORY.GROW) (TupT))
      )
    )
  )
)
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(TypD "expr" (InstD (AliasT (IterT (VarT "instr") List))))
HintD
HintD
(TypD
  "type"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom TYPE) Arg)
        (TupT (typbind "functype" (VarT "functype")))
      )
    )
  )
)
HintD
(TypD
  "local"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom LOCAL) Arg)
        (TupT (typbind "valtype" (VarT "valtype")))
      )
    )
  )
)
HintD
(TypD
  "func"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupT
          (typbind "typeidx" (VarT "typeidx"))
          (typbind "local*" (IterT (VarT "local") List))
          (typbind "expr" (VarT "expr"))
        )
      )
    )
  )
)
HintD
(TypD
  "global"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom GLOBAL) Arg Arg)
        (TupT
          (typbind "globaltype" (VarT "globaltype"))
          (typbind "expr" (VarT "expr"))
        )
      )
    )
  )
)
HintD
(TypD
  "table"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tabletype" (VarT "tabletype")))
      )
    )
  )
)
HintD
(TypD
  "mem"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom MEMORY) Arg)
        (TupT (typbind "memtype" (VarT "memtype")))
      )
    )
  )
)
HintD
(TypD
  "elem"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom ELEM) Arg Arg)
        (TupT
          (typbind "expr" (VarT "expr"))
          (typbind "funcidx*" (IterT (VarT "funcidx") List))
        )
      )
    )
  )
)
HintD
(TypD
  "data"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom DATA) Arg Arg)
        (TupT
          (typbind "expr" (VarT "expr"))
          (typbind "byte*" (IterT (VarT "byte") List))
        )
      )
    )
  )
)
HintD
(TypD
  "start"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom START) Arg)
        (TupT (typbind "funcidx" (VarT "funcidx")))
      )
    )
  )
)
HintD
(TypD
  "externidx"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "funcidx" (VarT "funcidx")))
      )
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globalidx" (VarT "globalidx")))
      )
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tableidx" (VarT "tableidx")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memidx" (VarT "memidx"))))
    )
  )
)
HintD
(TypD
  "export"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom EXPORT) Arg Arg)
        (TupT
          (typbind "name" (VarT "name"))
          (typbind "externidx" (VarT "externidx"))
        )
      )
    )
  )
)
HintD
(TypD
  "import"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupT
          (typbind "name" (VarT "name"))
          (typbind "name" (VarT "name"))
          (typbind "externtype" (VarT "externtype"))
        )
      )
    )
  )
)
HintD
(TypD
  "module"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupT
          (typbind "type*" (IterT (VarT "type") List))
          (typbind "import*" (IterT (VarT "import") List))
          (typbind "func*" (IterT (VarT "func") List))
          (typbind "global*" (IterT (VarT "global") List))
          (typbind "table*" (IterT (VarT "table") List))
          (typbind "mem*" (IterT (VarT "mem") List))
          (typbind "elem*" (IterT (VarT "elem") List))
          (typbind "data*" (IterT (VarT "data") List))
          (typbind "start?" (IterT (VarT "start") Opt))
          (typbind "export*" (IterT (VarT "export") List))
        )
      )
    )
  )
)
HintD

