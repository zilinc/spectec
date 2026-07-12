(TypD "N" (InstD (AliasT nat)))
HintD
(TypD "M" (InstD (AliasT nat)))
HintD
(TypD "K" (InstD (AliasT nat)))
HintD
(TypD "n" (InstD (AliasT nat)))
HintD
(TypD "m" (InstD (AliasT nat)))
HintD
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
      (ExpP "n" nat)
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
HintD
(RecD
  (DecD
    "prod"
    (ExpP "_" (IterT nat List))
    nat
    (DefD (ExpA (ListE)) (NumE (Nat 1)))
    (DefD
      (ExpP "n" nat)
      (ExpP "n'*" (IterT (VarT "n") List))
      (ExpA
        (CatE
          (ListE (VarE "n"))
          (IterE (VarE "n'") List (iterexp "n'" (VarE "n'*")))
        )
      )
      (BinE
        MulOp
        nat
        (VarE "n")
        (CallE
          "prod"
          (ExpA (IterE (VarE "n'") List (iterexp "n'" (VarE "n'*"))))
        )
      )
    )
  )
)
HintD
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
    "concatn_"
    (TypP "X")
    (ExpP "_" (IterT (IterT (VarT "X") List) List))
    (ExpP "nat" nat)
    (IterT (VarT "X") List)
    (DefD
      (TypP "X")
      (ExpP "n" nat)
      (TypA (VarT "X"))
      (ExpA (ListE))
      (ExpA (VarE "n"))
      (ListE)
    )
    (DefD
      (TypP "X")
      (ExpP "n" nat)
      (ExpP "w*" (IterT (VarT "X") List))
      (ExpP "w'**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE
            (IterE (VarE "w") (ListN (VarE "n")) (iterexp "w" (VarE "w*")))
          )
          (IterE
            (IterE (VarE "w'") (ListN (VarE "n")) (iterexp "w'" (VarE "w'*")))
            List
            (iterexp "w'*" (VarE "w'**"))
          )
        )
      )
      (ExpA (VarE "n"))
      (CatE
        (IterE (VarE "w") (ListN (VarE "n")) (iterexp "w" (VarE "w*")))
        (CallE
          "concatn_"
          (TypA (VarT "X"))
          (ExpA
            (IterE
              (IterE (VarE "w'") (ListN (VarE "n")) (iterexp "w'" (VarE "w'*")))
              List
              (iterexp "w'*" (VarE "w'**"))
            )
          )
          (ExpA (VarE "n"))
        )
      )
    )
  )
)
HintD
(DecD
  "concatopt_"
  (TypP "X")
  (ExpP "_" (IterT (IterT (VarT "X") Opt) List))
  (IterT (VarT "X") List)
  (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (ListE))
  (DefD
    (TypP "X")
    (ExpP "w?" (IterT (VarT "X") Opt))
    (ExpP "w'?*" (IterT (IterT (VarT "X") Opt) List))
    (TypA (VarT "X"))
    (ExpA
      (CatE
        (ListE (IterE (VarE "w") Opt (iterexp "w" (VarE "w?"))))
        (IterE
          (IterE (VarE "w'") Opt (iterexp "w'" (VarE "w'?")))
          List
          (iterexp "w'?" (VarE "w'?*"))
        )
      )
    )
    (CatE
      (LiftE (IterE (VarE "w") Opt (iterexp "w" (VarE "w?"))))
      (CallE
        "concat_"
        (TypA (VarT "X"))
        (ExpA
          (IterE
            (LiftE (IterE (VarE "w'") Opt (iterexp "w'" (VarE "w'?"))))
            List
            (iterexp "w'?" (VarE "w'?*"))
          )
        )
      )
    )
  )
)
HintD
(DecD
  "inv_concat_"
  (TypP "X")
  (ExpP "_" (IterT (VarT "X") List))
  (IterT (IterT (VarT "X") List) List)
)
HintD
(DecD
  "inv_concatn_"
  (TypP "X")
  (ExpP "nat" nat)
  (ExpP "_" (IterT (VarT "X") List))
  (IterT (IterT (VarT "X") List) List)
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
(RecD
  (DecD
    "setminus1_"
    (TypP "X")
    (ExpP "X" (VarT "X"))
    (ExpP "_" (IterT (VarT "X") List))
    (IterT (VarT "X") List)
    (DefD
      (TypP "X")
      (ExpP "w" (VarT "X"))
      (TypA (VarT "X"))
      (ExpA (VarE "w"))
      (ExpA (ListE))
      (ListE (VarE "w"))
    )
    (DefD
      (TypP "X")
      (ExpP "w" (VarT "X"))
      (ExpP "w_1" (VarT "X"))
      (ExpP "w'*" (IterT (VarT "X") List))
      (TypA (VarT "X"))
      (ExpA (VarE "w"))
      (ExpA
        (CatE
          (ListE (VarE "w_1"))
          (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
        )
      )
      (IfE
        (CmpE EqOp bool (VarE "w") (VarE "w_1"))
        (ListE)
        (CallE
          "setminus1_"
          (TypA (VarT "X"))
          (ExpA (VarE "w"))
          (ExpA (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
        )
      )
    )
  )
)
(RecD
  (DecD
    "setminus_"
    (TypP "X")
    (ExpP "_" (IterT (VarT "X") List))
    (ExpP "_" (IterT (VarT "X") List))
    (IterT (VarT "X") List)
    (DefD
      (TypP "X")
      (ExpP "w*" (IterT (VarT "X") List))
      (TypA (VarT "X"))
      (ExpA (ListE))
      (ExpA (IterE (VarE "w") List (iterexp "w" (VarE "w*"))))
      (ListE)
    )
    (DefD
      (TypP "X")
      (ExpP "w_1" (VarT "X"))
      (ExpP "w'*" (IterT (VarT "X") List))
      (ExpP "w*" (IterT (VarT "X") List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (VarE "w_1"))
          (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
        )
      )
      (ExpA (IterE (VarE "w") List (iterexp "w" (VarE "w*"))))
      (CatE
        (CallE
          "setminus1_"
          (TypA (VarT "X"))
          (ExpA (VarE "w_1"))
          (ExpA (IterE (VarE "w") List (iterexp "w" (VarE "w*"))))
        )
        (CallE
          "setminus_"
          (TypA (VarT "X"))
          (ExpA (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
          (ExpA (IterE (VarE "w") List (iterexp "w" (VarE "w*"))))
        )
      )
    )
  )
)
HintD
(RecD
  (DecD
    "setproduct2_"
    (TypP "X")
    (ExpP "X" (VarT "X"))
    (ExpP "_" (IterT (IterT (VarT "X") List) List))
    (IterT (IterT (VarT "X") List) List)
    (DefD
      (TypP "X")
      (ExpP "w_1" (VarT "X"))
      (TypA (VarT "X"))
      (ExpA (VarE "w_1"))
      (ExpA (ListE))
      (ListE)
    )
    (DefD
      (TypP "X")
      (ExpP "w_1" (VarT "X"))
      (ExpP "w'*" (IterT (VarT "X") List))
      (ExpP "w**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA (VarE "w_1"))
      (ExpA
        (CatE
          (ListE (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
          (IterE
            (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
            List
            (iterexp "w*" (VarE "w**"))
          )
        )
      )
      (CatE
        (ListE
          (CatE
            (ListE (VarE "w_1"))
            (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
          )
        )
        (CallE
          "setproduct2_"
          (TypA (VarT "X"))
          (ExpA (VarE "w_1"))
          (ExpA
            (IterE
              (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
              List
              (iterexp "w*" (VarE "w**"))
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "setproduct1_"
    (TypP "X")
    (ExpP "_" (IterT (VarT "X") List))
    (ExpP "_" (IterT (IterT (VarT "X") List) List))
    (IterT (IterT (VarT "X") List) List)
    (DefD
      (TypP "X")
      (ExpP "w**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA (ListE))
      (ExpA
        (IterE
          (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
          List
          (iterexp "w*" (VarE "w**"))
        )
      )
      (ListE)
    )
    (DefD
      (TypP "X")
      (ExpP "w_1" (VarT "X"))
      (ExpP "w'*" (IterT (VarT "X") List))
      (ExpP "w**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (VarE "w_1"))
          (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*")))
        )
      )
      (ExpA
        (IterE
          (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
          List
          (iterexp "w*" (VarE "w**"))
        )
      )
      (CatE
        (CallE
          "setproduct2_"
          (TypA (VarT "X"))
          (ExpA (VarE "w_1"))
          (ExpA
            (IterE
              (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
              List
              (iterexp "w*" (VarE "w**"))
            )
          )
        )
        (CallE
          "setproduct1_"
          (TypA (VarT "X"))
          (ExpA (IterE (VarE "w'") List (iterexp "w'" (VarE "w'*"))))
          (ExpA
            (IterE
              (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
              List
              (iterexp "w*" (VarE "w**"))
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "setproduct_"
    (TypP "X")
    (ExpP "_" (IterT (IterT (VarT "X") List) List))
    (IterT (IterT (VarT "X") List) List)
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (ListE (ListE)))
    (DefD
      (TypP "X")
      (ExpP "w_1*" (IterT (VarT "X") List))
      (ExpP "w**" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA
        (CatE
          (ListE (IterE (VarE "w_1") List (iterexp "w_1" (VarE "w_1*"))))
          (IterE
            (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
            List
            (iterexp "w*" (VarE "w**"))
          )
        )
      )
      (CallE
        "setproduct1_"
        (TypA (VarT "X"))
        (ExpA (IterE (VarE "w_1") List (iterexp "w_1" (VarE "w_1*"))))
        (ExpA
          (CallE
            "setproduct_"
            (TypA (VarT "X"))
            (ExpA
              (IterE
                (IterE (VarE "w") List (iterexp "w" (VarE "w*")))
                List
                (iterexp "w*" (VarE "w**"))
              )
            )
          )
        )
      )
    )
  )
)
HintD
(DecD "ND" BoolT)
HintD
(TypD
  "bit"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" nat))
        (IfPr
          (BinE
            OrOp
            bool
            (CmpE EqOp bool (VarE "i") (NumE (Nat 0)))
            (CmpE EqOp bool (VarE "i") (NumE (Nat 1)))
          )
        )
      )
    )
  )
)
HintD
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
                  (UnE
                    PlusOp
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
(TypD "u8" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 8)))))))
(TypD "u16" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 16)))))))
(TypD "u31" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 31)))))))
(TypD "u32" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 32)))))))
(TypD "u64" (InstD (AliasT (VarT "uN" (ExpA (NumE (Nat 64)))))))
(TypD "s33" (InstD (AliasT (VarT "sN" (ExpA (NumE (Nat 33)))))))
(TypD "i32" (InstD (AliasT (VarT "iN" (ExpA (NumE (Nat 32)))))))
(TypD "i64" (InstD (AliasT (VarT "iN" (ExpA (NumE (Nat 64)))))))
(TypD "i128" (InstD (AliasT (VarT "iN" (ExpA (NumE (Nat 128)))))))
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
  (DefD (ExpP "N" nat) (ExpA (VarE "N")) (CallE "signif" (ExpA (VarE "N"))))
)
HintD
(DecD
  "E"
  (ExpP "N" (VarT "N"))
  nat
  (DefD (ExpP "N" nat) (ExpA (VarE "N")) (CallE "expon" (ExpA (VarE "N"))))
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
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (CaseE
      (Seq (Atom POS) Arg)
      (TupE (CaseE (Seq (Atom SUBNORM) Arg) (TupE (NumE (Nat 0)))))
    )
  )
)
HintD
(DecD
  "fnat"
  (ExpP "N" (VarT "N"))
  (ExpP "nat" nat)
  (VarT "fN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "n" nat)
    (ExpA (VarE "N"))
    (ExpA (VarE "n"))
    (CaseE
      (Seq (Atom POS) Arg)
      (TupE
        (CaseE
          (Seq (Atom NORM) Arg Arg)
          (TupE (VarE "n") (CvtE nat int (NumE (Nat 0))))
        )
      )
    )
  )
)
HintD
(DecD
  "fone"
  (ExpP "N" (VarT "N"))
  (VarT "fN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
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
    (ExpP "N" nat)
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
  "vN"
  (ExpP "N" (VarT "N"))
  (InstD
    (ExpP "N" (VarT "N"))
    (ExpA (VarE "N"))
    (AliasT (VarT "uN" (ExpA (VarE "N"))))
  )
)
HintD
(TypD "v128" (InstD (AliasT (VarT "vN" (ExpA (NumE (Nat 128)))))))
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
(TypD "laneidx" (InstD (AliasT (VarT "u8"))))
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
(TypD "tagidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "elemidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "dataidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "labelidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "localidx" (InstD (AliasT (VarT "idx"))))
HintD
(TypD "fieldidx" (InstD (AliasT (VarT "idx"))))
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
      (typcase (Seq (Atom TAG) Arg) (TupT (typbind "tagidx" (VarT "tagidx"))))
    )
  )
)
HintD
(RecD
  (DecD
    "funcsxx"
    (ExpP "_" (IterT (VarT "externidx") List))
    (IterT (VarT "typeidx") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x"))))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CatE
        (ListE (VarE "x"))
        (CallE
          "funcsxx"
          (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
        )
      )
    )
    (DefD
      (ExpP "externidx" (VarT "externidx"))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (VarE "externidx"))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CallE
        "funcsxx"
        (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "globalsxx"
    (ExpP "_" (IterT (VarT "externidx") List))
    (IterT (VarT "globalidx") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x"))))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CatE
        (ListE (VarE "x"))
        (CallE
          "globalsxx"
          (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
        )
      )
    )
    (DefD
      (ExpP "externidx" (VarT "externidx"))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (VarE "externidx"))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CallE
        "globalsxx"
        (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "tablesxx"
    (ExpP "_" (IterT (VarT "externidx") List))
    (IterT (VarT "tableidx") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x"))))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CatE
        (ListE (VarE "x"))
        (CallE
          "tablesxx"
          (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
        )
      )
    )
    (DefD
      (ExpP "externidx" (VarT "externidx"))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (VarE "externidx"))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CallE
        "tablesxx"
        (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "memsxx"
    (ExpP "_" (IterT (VarT "externidx") List))
    (IterT (VarT "memidx") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x"))))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CatE
        (ListE (VarE "x"))
        (CallE
          "memsxx"
          (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
        )
      )
    )
    (DefD
      (ExpP "externidx" (VarT "externidx"))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (VarE "externidx"))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CallE
        "memsxx"
        (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "tagsxx"
    (ExpP "_" (IterT (VarT "externidx") List))
    (IterT (VarT "tagidx") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "x"))))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CatE
        (ListE (VarE "x"))
        (CallE
          "tagsxx"
          (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
        )
      )
    )
    (DefD
      (ExpP "externidx" (VarT "externidx"))
      (ExpP "xx*" (IterT (VarT "externidx") List))
      (ExpA
        (CatE
          (ListE (VarE "externidx"))
          (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*")))
        )
      )
      (CallE
        "tagsxx"
        (ExpA (IterE (VarE "xx") List (iterexp "xx" (VarE "xx*"))))
      )
    )
  )
)
HintD
(TypD
  "free"
  (InstD
    (StructT
      (typfield (Atom TYPES) (IterT (VarT "typeidx") List))
      (typfield (Atom FUNCS) (IterT (VarT "funcidx") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globalidx") List))
      (typfield (Atom TABLES) (IterT (VarT "tableidx") List))
      (typfield (Atom MEMS) (IterT (VarT "memidx") List))
      (typfield (Atom ELEMS) (IterT (VarT "elemidx") List))
      (typfield (Atom DATAS) (IterT (VarT "dataidx") List))
      (typfield (Atom LOCALS) (IterT (VarT "localidx") List))
      (typfield (Atom LABELS) (IterT (VarT "labelidx") List))
      (typfield (Atom TAGS) (IterT (VarT "tagidx") List))
    )
  )
)
(DecD
  "free_opt"
  (ExpP "_" (IterT (VarT "free") Opt))
  (VarT "free")
  (DefD
    (ExpA (OptE))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
  (DefD (ExpP "free" (VarT "free")) (ExpA (OptE (VarE "free"))) (VarE "free"))
)
(RecD
  (DecD
    "free_list"
    (ExpP "_" (IterT (VarT "free") List))
    (VarT "free")
    (DefD
      (ExpA (ListE))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "free" (VarT "free"))
      (ExpP "free'*" (IterT (VarT "free") List))
      (ExpA
        (CatE
          (ListE (VarE "free"))
          (IterE (VarE "free'") List (iterexp "free'" (VarE "free'*")))
        )
      )
      (CompE
        (VarE "free")
        (CallE
          "free_list"
          (ExpA (IterE (VarE "free'") List (iterexp "free'" (VarE "free'*"))))
        )
      )
    )
  )
)
(DecD
  "free_typeidx"
  (ExpP "typeidx" (VarT "typeidx"))
  (VarT "free")
  (DefD
    (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "typeidx"))
    (StrE
      (expfield (Atom TYPES) (ListE (VarE "typeidx")))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_funcidx"
  (ExpP "funcidx" (VarT "funcidx"))
  (VarT "free")
  (DefD
    (ExpP "funcidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "funcidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE (VarE "funcidx")))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_globalidx"
  (ExpP "globalidx" (VarT "globalidx"))
  (VarT "free")
  (DefD
    (ExpP "globalidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "globalidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE (VarE "globalidx")))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_tableidx"
  (ExpP "tableidx" (VarT "tableidx"))
  (VarT "free")
  (DefD
    (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "tableidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE (VarE "tableidx")))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_memidx"
  (ExpP "memidx" (VarT "memidx"))
  (VarT "free")
  (DefD
    (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "memidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE (VarE "memidx")))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_elemidx"
  (ExpP "elemidx" (VarT "elemidx"))
  (VarT "free")
  (DefD
    (ExpP "elemidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "elemidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE (VarE "elemidx")))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_dataidx"
  (ExpP "dataidx" (VarT "dataidx"))
  (VarT "free")
  (DefD
    (ExpP "dataidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "dataidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE (VarE "dataidx")))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_localidx"
  (ExpP "localidx" (VarT "localidx"))
  (VarT "free")
  (DefD
    (ExpP "localidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "localidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE (VarE "localidx")))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_labelidx"
  (ExpP "labelidx" (VarT "labelidx"))
  (VarT "free")
  (DefD
    (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "labelidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE (VarE "labelidx")))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_tagidx"
  (ExpP "tagidx" (VarT "tagidx"))
  (VarT "free")
  (DefD
    (ExpP "tagidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "tagidx"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE (VarE "tagidx")))
    )
  )
)
(DecD
  "free_externidx"
  (ExpP "externidx" (VarT "externidx"))
  (VarT "free")
  (DefD
    (ExpP "funcidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "funcidx"))))
    (CallE "free_funcidx" (ExpA (VarE "funcidx")))
  )
  (DefD
    (ExpP "globalidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globalidx"))))
    (CallE "free_globalidx" (ExpA (VarE "globalidx")))
  )
  (DefD
    (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tableidx"))))
    (CallE "free_tableidx" (ExpA (VarE "tableidx")))
  )
  (DefD
    (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memidx"))))
    (CallE "free_memidx" (ExpA (VarE "memidx")))
  )
  (DefD
    (ExpP "tagidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagidx"))))
    (CallE "free_tagidx" (ExpA (VarE "tagidx")))
  )
)
(TypD "null" (InstD (VariantT (typcase (Atom NULL) (TupT)))))
HintD
(TypD
  "addrtype"
  (InstD (VariantT (typcase (Atom I32) (TupT)) (typcase (Atom I64) (TupT))))
)
HintD
(TypD
  "numtype"
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
(TypD "vectype" (InstD (VariantT (typcase (Atom V128) (TupT)))))
HintD
(TypD
  "consttype"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom F32) (TupT))
      (typcase (Atom F64) (TupT))
      (typcase (Atom V128) (TupT))
    )
  )
)
HintD
(TypD
  "absheaptype"
  (InstD
    (VariantT
      (typcase (Atom ANY) (TupT))
      (typcase (Atom EQ) (TupT))
      (typcase (Atom I31) (TupT))
      (typcase (Atom STRUCT) (TupT))
      (typcase (Atom ARRAY) (TupT))
      (typcase (Atom NONE) (TupT))
      (typcase (Atom FUNC) (TupT))
      (typcase (Atom NOFUNC) (TupT))
      (typcase (Atom EXN) (TupT))
      (typcase (Atom NOEXN) (TupT))
      (typcase (Atom EXTERN) (TupT))
      (typcase (Atom NOEXTERN) (TupT))
      (typcase (Atom BOT) (TupT))
    )
  )
)
HintD
(TypD "mut" (InstD (VariantT (typcase (Atom MUT) (TupT)))))
(TypD "final" (InstD (VariantT (typcase (Atom FINAL) (TupT)))))
(RecD
  (TypD
    "typeuse"
    (InstD
      (VariantT
        (typcase
          (Seq (Atom _IDX) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom _DEF) Arg Arg)
          (TupT (typbind "rectype" (VarT "rectype")) (typbind "n" (VarT "n")))
        )
        (typcase (Seq (Atom REC) Arg) (TupT (typbind "n" (VarT "n"))))
      )
    )
  )
  (TypD
    "heaptype"
    (InstD
      (VariantT
        (typcase (Atom ANY) (TupT))
        (typcase (Atom EQ) (TupT))
        (typcase (Atom I31) (TupT))
        (typcase (Atom STRUCT) (TupT))
        (typcase (Atom ARRAY) (TupT))
        (typcase (Atom NONE) (TupT))
        (typcase (Atom FUNC) (TupT))
        (typcase (Atom NOFUNC) (TupT))
        (typcase (Atom EXN) (TupT))
        (typcase (Atom NOEXN) (TupT))
        (typcase (Atom EXTERN) (TupT))
        (typcase (Atom NOEXTERN) (TupT))
        (typcase (Atom BOT) (TupT))
        (typcase
          (Seq (Atom _IDX) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom _DEF) Arg Arg)
          (TupT (typbind "rectype" (VarT "rectype")) (typbind "n" (VarT "n")))
        )
        (typcase (Seq (Atom REC) Arg) (TupT (typbind "n" (VarT "n"))))
      )
    )
  )
  (TypD
    "valtype"
    (InstD
      (VariantT
        (typcase (Atom I32) (TupT))
        (typcase (Atom I64) (TupT))
        (typcase (Atom F32) (TupT))
        (typcase (Atom F64) (TupT))
        (typcase (Atom V128) (TupT))
        (typcase
          (Seq (Atom REF) Arg Arg)
          (TupT
            (typbind "null?" (IterT (VarT "null") Opt))
            (typbind "heaptype" (VarT "heaptype"))
          )
        )
        (typcase (Atom BOT) (TupT))
      )
    )
  )
  (TypD
    "storagetype"
    (InstD
      (VariantT
        (typcase (Atom I32) (TupT))
        (typcase (Atom I64) (TupT))
        (typcase (Atom F32) (TupT))
        (typcase (Atom F64) (TupT))
        (typcase (Atom V128) (TupT))
        (typcase
          (Seq (Atom REF) Arg Arg)
          (TupT
            (typbind "null?" (IterT (VarT "null") Opt))
            (typbind "heaptype" (VarT "heaptype"))
          )
        )
        (typcase (Atom BOT) (TupT))
        (typcase (Atom I8) (TupT))
        (typcase (Atom I16) (TupT))
      )
    )
  )
  (TypD "resulttype" (InstD (AliasT (VarT "list" (TypA (VarT "valtype"))))))
  (TypD
    "fieldtype"
    (InstD
      (VariantT
        (typcase
          (Seq Arg Arg)
          (TupT
            (typbind "mut?" (IterT (VarT "mut") Opt))
            (typbind "storagetype" (VarT "storagetype"))
          )
        )
      )
    )
  )
  (TypD
    "comptype"
    (InstD
      (VariantT
        (typcase
          (Seq (Atom STRUCT) Arg)
          (TupT (typbind "_" (VarT "list" (TypA (VarT "fieldtype")))))
        )
        (typcase
          (Seq (Atom ARRAY) Arg)
          (TupT (typbind "fieldtype" (VarT "fieldtype")))
        )
        (typcase
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupT
            (typbind "resulttype" (VarT "resulttype"))
            (typbind "resulttype" (VarT "resulttype"))
          )
        )
      )
    )
  )
  (TypD
    "subtype"
    (InstD
      (VariantT
        (typcase
          (Seq (Atom SUB) Arg Arg Arg)
          (TupT
            (typbind "final?" (IterT (VarT "final") Opt))
            (typbind "typeuse*" (IterT (VarT "typeuse") List))
            (typbind "comptype" (VarT "comptype"))
          )
        )
      )
    )
  )
  (TypD
    "rectype"
    (InstD
      (VariantT
        (typcase
          (Seq (Atom REC) Arg)
          (TupT (typbind "_" (VarT "list" (TypA (VarT "subtype")))))
        )
      )
    )
  )
)
HintD
(TypD
  "deftype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom _DEF) Arg Arg)
        (TupT (typbind "rectype" (VarT "rectype")) (typbind "n" (VarT "n")))
      )
    )
  )
)
HintD
HintD
(TypD
  "typevar"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom _IDX) Arg)
        (TupT (typbind "typeidx" (VarT "typeidx")))
      )
      (typcase (Seq (Atom REC) Arg) (TupT (typbind "n" (VarT "n"))))
    )
  )
)
HintD
HintD
(TypD
  "reftype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom REF) Arg Arg)
        (TupT
          (typbind "null?" (IterT (VarT "null") Opt))
          (typbind "heaptype" (VarT "heaptype"))
        )
      )
    )
  )
)
HintD
HintD
(TypD "Inn" (InstD (AliasT (VarT "addrtype"))))
HintD
(TypD
  "Fnn"
  (InstD (VariantT (typcase (Atom F32) (TupT)) (typcase (Atom F64) (TupT))))
)
HintD
(TypD "Vnn" (InstD (AliasT (VarT "vectype"))))
HintD
(TypD
  "Cnn"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom F32) (TupT))
      (typcase (Atom F64) (TupT))
      (typcase (Atom V128) (TupT))
    )
  )
)
HintD
(DecD
  "ANYREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom ANY) (TupE)))
    )
  )
)
HintD
(DecD
  "EQREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom EQ) (TupE)))
    )
  )
)
HintD
(DecD
  "I31REF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom I31) (TupE)))
    )
  )
)
HintD
(DecD
  "STRUCTREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom STRUCT) (TupE)))
    )
  )
)
HintD
(DecD
  "ARRAYREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom ARRAY) (TupE)))
    )
  )
)
HintD
(DecD
  "FUNCREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom FUNC) (TupE)))
    )
  )
)
HintD
(DecD
  "EXNREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom EXN) (TupE)))
    )
  )
)
HintD
(DecD
  "EXTERNREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom EXTERN) (TupE)))
    )
  )
)
HintD
(DecD
  "NULLREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom NONE) (TupE)))
    )
  )
)
HintD
(DecD
  "NULLFUNCREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom NOFUNC) (TupE)))
    )
  )
)
HintD
(DecD
  "NULLEXNREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom NOEXN) (TupE)))
    )
  )
)
HintD
(DecD
  "NULLEXTERNREF"
  (VarT "reftype")
  (DefD
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom NOEXTERN) (TupE)))
    )
  )
)
HintD
(TypD
  "packtype"
  (InstD (VariantT (typcase (Atom I8) (TupT)) (typcase (Atom I16) (TupT))))
)
HintD
(TypD
  "lanetype"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom F32) (TupT))
      (typcase (Atom F64) (TupT))
      (typcase (Atom I8) (TupT))
      (typcase (Atom I16) (TupT))
    )
  )
)
HintD
HintD
(TypD "Pnn" (InstD (AliasT (VarT "packtype"))))
HintD
(TypD
  "Jnn"
  (InstD
    (VariantT
      (typcase (Atom I32) (TupT))
      (typcase (Atom I64) (TupT))
      (typcase (Atom I8) (TupT))
      (typcase (Atom I16) (TupT))
    )
  )
)
HintD
(TypD "Lnn" (InstD (AliasT (VarT "lanetype"))))
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(TypD
  "limits"
  (InstD
    (VariantT
      (typcase
        (Brack [ (Infix Arg .. Arg) ])
        (TupT
          (typbind "u64" (VarT "u64"))
          (typbind "u64?" (IterT (VarT "u64") Opt))
        )
      )
    )
  )
)
HintD
(TypD "tagtype" (InstD (AliasT (VarT "typeuse"))))
HintD
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
HintD
(TypD
  "memtype"
  (InstD
    (VariantT
      (typcase
        (Seq Arg Arg (Atom PAGE))
        (TupT
          (typbind "addrtype" (VarT "addrtype"))
          (typbind "limits" (VarT "limits"))
        )
      )
    )
  )
)
HintD
(TypD
  "tabletype"
  (InstD
    (VariantT
      (typcase
        (Seq Arg Arg Arg)
        (TupT
          (typbind "addrtype" (VarT "addrtype"))
          (typbind "limits" (VarT "limits"))
          (typbind "reftype" (VarT "reftype"))
        )
      )
    )
  )
)
HintD
(TypD "datatype" (InstD (VariantT (typcase (Atom OK) (TupT)))))
HintD
(TypD "elemtype" (InstD (AliasT (VarT "reftype"))))
HintD
(TypD
  "externtype"
  (InstD
    (VariantT
      (typcase (Seq (Atom TAG) Arg) (TupT (typbind "tagtype" (VarT "tagtype"))))
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globaltype" (VarT "globaltype")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memtype" (VarT "memtype"))))
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tabletype" (VarT "tabletype")))
      )
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "typeuse" (VarT "typeuse")))
      )
    )
  )
)
HintD
(TypD
  "moduletype"
  (InstD
    (VariantT
      (typcase
        (Infix Arg -> Arg)
        (TupT
          (typbind "externtype*" (IterT (VarT "externtype") List))
          (typbind "externtype*" (IterT (VarT "externtype") List))
        )
      )
    )
  )
)
HintD
(DecD
  "IN"
  (ExpP "N" (VarT "N"))
  (VarT "Inn")
  (DefD (ExpA (NumE (Nat 32))) (CaseE (Atom I32) (TupE)))
  (DefD (ExpA (NumE (Nat 64))) (CaseE (Atom I64) (TupE)))
)
HintD
(DecD
  "FN"
  (ExpP "N" (VarT "N"))
  (VarT "Fnn")
  (DefD (ExpA (NumE (Nat 32))) (CaseE (Atom F32) (TupE)))
  (DefD (ExpA (NumE (Nat 64))) (CaseE (Atom F64) (TupE)))
)
HintD
(DecD
  "JN"
  (ExpP "N" (VarT "N"))
  (VarT "Jnn")
  (DefD (ExpA (NumE (Nat 8))) (CaseE (Atom I8) (TupE)))
  (DefD (ExpA (NumE (Nat 16))) (CaseE (Atom I16) (TupE)))
  (DefD (ExpA (NumE (Nat 32))) (CaseE (Atom I32) (TupE)))
  (DefD (ExpA (NumE (Nat 64))) (CaseE (Atom I64) (TupE)))
)
HintD
(DecD
  "size"
  (ExpP "numtype" (VarT "numtype"))
  nat
  (DefD (ExpA (CaseE (Atom I32) (TupE))) (NumE (Nat 32)))
  (DefD (ExpA (CaseE (Atom I64) (TupE))) (NumE (Nat 64)))
  (DefD (ExpA (CaseE (Atom F32) (TupE))) (NumE (Nat 32)))
  (DefD (ExpA (CaseE (Atom F64) (TupE))) (NumE (Nat 64)))
)
HintD
(DecD
  "vsize"
  (ExpP "vectype" (VarT "vectype"))
  nat
  (DefD (ExpA (CaseE (Atom V128) (TupE))) (NumE (Nat 128)))
)
HintD
(DecD
  "psize"
  (ExpP "packtype" (VarT "packtype"))
  nat
  (DefD (ExpA (CaseE (Atom I8) (TupE))) (NumE (Nat 8)))
  (DefD (ExpA (CaseE (Atom I16) (TupE))) (NumE (Nat 16)))
)
HintD
(DecD
  "lsize"
  (ExpP "lanetype" (VarT "lanetype"))
  nat
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
    (CallE "size" (ExpA (VarE "numtype")))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
    (CallE "psize" (ExpA (VarE "packtype")))
  )
)
HintD
(DecD
  "zsize"
  (ExpP "storagetype" (VarT "storagetype"))
  nat
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (SubE (VarT "numtype") (VarT "storagetype") (VarE "numtype")))
    (CallE "size" (ExpA (VarE "numtype")))
  )
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpA (SubE (VarT "vectype") (VarT "storagetype") (VarE "vectype")))
    (CallE "vsize" (ExpA (VarE "vectype")))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (CallE "psize" (ExpA (VarE "packtype")))
  )
)
HintD
(DecD
  "isize"
  (ExpP "Inn" (VarT "Inn"))
  nat
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpA (VarE "Inn"))
    (CallE "size" (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))))
  )
)
HintD
(DecD
  "jsize"
  (ExpP "Jnn" (VarT "Jnn"))
  nat
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpA (VarE "Jnn"))
    (CallE "lsize" (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))))
  )
)
HintD
(DecD
  "fsize"
  (ExpP "Fnn" (VarT "Fnn"))
  nat
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (VarE "Fnn"))
    (CallE "size" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
  )
)
HintD
(DecD
  "inv_isize"
  (ExpP "nat" nat)
  (VarT "Inn")
  (DefD (ExpA (NumE (Nat 32))) (CaseE (Atom I32) (TupE)))
  (DefD (ExpA (NumE (Nat 64))) (CaseE (Atom I64) (TupE)))
)
HintD
(DecD
  "inv_jsize"
  (ExpP "nat" nat)
  (VarT "Jnn")
  (DefD (ExpA (NumE (Nat 8))) (CaseE (Atom I8) (TupE)))
  (DefD (ExpA (NumE (Nat 16))) (CaseE (Atom I16) (TupE)))
  (DefD
    (ExpP "n" nat)
    (ExpA (VarE "n"))
    (SubE (VarT "addrtype") (VarT "Jnn") (CallE "inv_isize" (ExpA (VarE "n"))))
  )
)
HintD
(DecD
  "inv_fsize"
  (ExpP "nat" nat)
  (VarT "Fnn")
  (DefD (ExpA (NumE (Nat 32))) (CaseE (Atom F32) (TupE)))
  (DefD (ExpA (NumE (Nat 64))) (CaseE (Atom F64) (TupE)))
)
HintD
(DecD
  "sizenn"
  (ExpP "numtype" (VarT "numtype"))
  nat
  (DefD
    (ExpP "nt" (VarT "numtype"))
    (ExpA (VarE "nt"))
    (CallE "size" (ExpA (VarE "nt")))
  )
)
HintD
(DecD
  "sizenn1"
  (ExpP "numtype" (VarT "numtype"))
  nat
  (DefD
    (ExpP "nt" (VarT "numtype"))
    (ExpA (VarE "nt"))
    (CallE "size" (ExpA (VarE "nt")))
  )
)
HintD
(DecD
  "sizenn2"
  (ExpP "numtype" (VarT "numtype"))
  nat
  (DefD
    (ExpP "nt" (VarT "numtype"))
    (ExpA (VarE "nt"))
    (CallE "size" (ExpA (VarE "nt")))
  )
)
HintD
(DecD
  "vsizenn"
  (ExpP "vectype" (VarT "vectype"))
  nat
  (DefD
    (ExpP "vt" (VarT "vectype"))
    (ExpA (VarE "vt"))
    (CallE "vsize" (ExpA (VarE "vt")))
  )
)
HintD
(DecD
  "psizenn"
  (ExpP "packtype" (VarT "packtype"))
  nat
  (DefD
    (ExpP "pt" (VarT "packtype"))
    (ExpA (VarE "pt"))
    (CallE "psize" (ExpA (VarE "pt")))
  )
)
HintD
(DecD
  "lsizenn"
  (ExpP "lanetype" (VarT "lanetype"))
  nat
  (DefD
    (ExpP "lt" (VarT "lanetype"))
    (ExpA (VarE "lt"))
    (CallE "lsize" (ExpA (VarE "lt")))
  )
)
HintD
(DecD
  "lsizenn1"
  (ExpP "lanetype" (VarT "lanetype"))
  nat
  (DefD
    (ExpP "lt" (VarT "lanetype"))
    (ExpA (VarE "lt"))
    (CallE "lsize" (ExpA (VarE "lt")))
  )
)
HintD
(DecD
  "lsizenn2"
  (ExpP "lanetype" (VarT "lanetype"))
  nat
  (DefD
    (ExpP "lt" (VarT "lanetype"))
    (ExpA (VarE "lt"))
    (CallE "lsize" (ExpA (VarE "lt")))
  )
)
HintD
(DecD
  "jsizenn"
  (ExpP "Jnn" (VarT "Jnn"))
  nat
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpA (VarE "Jnn"))
    (CallE "lsize" (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))))
  )
)
HintD
(DecD
  "inv_jsizenn"
  (ExpP "nat" nat)
  (VarT "Jnn")
  (DefD (ExpP "n" nat) (ExpA (VarE "n")) (CallE "inv_jsize" (ExpA (VarE "n"))))
)
HintD
(DecD
  "lunpack"
  (ExpP "lanetype" (VarT "lanetype"))
  (VarT "numtype")
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
    (VarE "numtype")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
    (CaseE (Atom I32) (TupE))
  )
)
HintD
(DecD
  "unpack"
  (ExpP "storagetype" (VarT "storagetype"))
  (VarT "valtype")
  (DefD
    (ExpP "valtype" (VarT "valtype"))
    (ExpA (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype")))
    (VarE "valtype")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (CaseE (Atom I32) (TupE))
  )
)
(DecD
  "nunpack"
  (ExpP "storagetype" (VarT "storagetype"))
  (VarT "numtype")
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (SubE (VarT "numtype") (VarT "storagetype") (VarE "numtype")))
    (VarE "numtype")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (CaseE (Atom I32) (TupE))
  )
)
HintD
(DecD
  "vunpack"
  (ExpP "storagetype" (VarT "storagetype"))
  (VarT "vectype")
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpA (SubE (VarT "vectype") (VarT "storagetype") (VarE "vectype")))
    (VarE "vectype")
  )
)
HintD
(DecD
  "cunpack"
  (ExpP "storagetype" (VarT "storagetype"))
  (VarT "consttype")
  (DefD
    (ExpP "consttype" (VarT "consttype"))
    (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
    (VarE "consttype")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (CaseE (Atom I32) (TupE))
  )
  (DefD
    (ExpP "lanetype" (VarT "lanetype"))
    (ExpA (SubE (VarT "lanetype") (VarT "storagetype") (VarE "lanetype")))
    (SubE
      (VarT "numtype")
      (VarT "consttype")
      (CallE "lunpack" (ExpA (VarE "lanetype")))
    )
  )
)
HintD
(DecD
  "minat"
  (ExpP "addrtype" (VarT "addrtype"))
  (ExpP "addrtype" (VarT "addrtype"))
  (VarT "addrtype")
  (DefD
    (ExpP "at_1" (VarT "addrtype"))
    (ExpP "at_2" (VarT "addrtype"))
    (ExpA (VarE "at_1"))
    (ExpA (VarE "at_2"))
    (IfE
      (CmpE
        LeOp
        nat
        (CallE
          "size"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "at_1")))
        )
        (CallE
          "size"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "at_2")))
        )
      )
      (VarE "at_1")
      (VarE "at_2")
    )
  )
)
HintD
(DecD
  "diffrt"
  (ExpP "reftype" (VarT "reftype"))
  (ExpP "reftype" (VarT "reftype"))
  (VarT "reftype")
  (DefD
    (ExpP "null_1?" (IterT (VarT "null") Opt))
    (ExpP "ht_1" (VarT "heaptype"))
    (ExpP "ht_2" (VarT "heaptype"))
    (ExpA
      (CaseE
        (Seq (Atom REF) Arg Arg)
        (TupE
          (IterE (VarE "null_1") Opt (iterexp "null_1" (VarE "null_1?")))
          (VarE "ht_1")
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom REF) Arg Arg)
        (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht_2"))
      )
    )
    (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht_1")))
  )
  (DefD
    (ExpP "null_1?" (IterT (VarT "null") Opt))
    (ExpP "ht_1" (VarT "heaptype"))
    (ExpP "ht_2" (VarT "heaptype"))
    (ExpA
      (CaseE
        (Seq (Atom REF) Arg Arg)
        (TupE
          (IterE (VarE "null_1") Opt (iterexp "null_1" (VarE "null_1?")))
          (VarE "ht_1")
        )
      )
    )
    (ExpA (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht_2"))))
    (CaseE
      (Seq (Atom REF) Arg Arg)
      (TupE
        (IterE (VarE "null_1") Opt (iterexp "null_1" (VarE "null_1?")))
        (VarE "ht_1")
      )
    )
  )
)
HintD
(DecD
  "as_deftype"
  (ExpP "typeuse" (VarT "typeuse"))
  (VarT "deftype")
  (DefD
    (ExpP "dt" (VarT "deftype"))
    (ExpA (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt")))
    (VarE "dt")
  )
)
HintD
(RecD
  (DecD
    "tagsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "tagtype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "jt" (VarT "typeuse"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "jt"))))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "jt"))
        (CallE
          "tagsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CallE
        "tagsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "globalsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "globaltype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "gt" (VarT "globaltype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt"))))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "gt"))
        (CallE
          "globalsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CallE
        "globalsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "memsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "memtype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "mt" (VarT "memtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt"))))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "mt"))
        (CallE
          "memsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CallE
        "memsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "tablesxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "tabletype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "tt" (VarT "tabletype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt"))))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "tt"))
        (CallE
          "tablesxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CallE
        "tablesxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "funcsxt"
    (ExpP "_" (IterT (VarT "externtype") List))
    (IterT (VarT "deftype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "dt" (VarT "deftype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE
            (CaseE
              (Seq (Atom FUNC) Arg)
              (TupE (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt")))
            )
          )
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CatE
        (ListE (VarE "dt"))
        (CallE
          "funcsxt"
          (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
        )
      )
    )
    (DefD
      (ExpP "externtype" (VarT "externtype"))
      (ExpP "xt*" (IterT (VarT "externtype") List))
      (ExpA
        (CatE
          (ListE (VarE "externtype"))
          (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*")))
        )
      )
      (CallE
        "funcsxt"
        (ExpA (IterE (VarE "xt") List (iterexp "xt" (VarE "xt*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "subst_typevar"
    (ExpP "typevar" (VarT "typevar"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "typeuse")
    (DefD
      (ExpP "tv" (VarT "typevar"))
      (ExpA (VarE "tv"))
      (ExpA (ListE))
      (ExpA (ListE))
      (SubE (VarT "typevar") (VarT "typeuse") (VarE "tv"))
    )
    (DefD
      (ExpP "tv" (VarT "typevar"))
      (ExpP "tv_1" (VarT "typevar"))
      (ExpP "tv'*" (IterT (VarT "typevar") List))
      (ExpP "tu_1" (VarT "typeuse"))
      (ExpP "tu'*" (IterT (VarT "typeuse") List))
      (ExpA (VarE "tv"))
      (ExpA
        (CatE
          (ListE (VarE "tv_1"))
          (IterE (VarE "tv'") List (iterexp "tv'" (VarE "tv'*")))
        )
      )
      (ExpA
        (CatE
          (ListE (VarE "tu_1"))
          (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*")))
        )
      )
      (IfE
        (CmpE EqOp bool (VarE "tv") (VarE "tv_1"))
        (VarE "tu_1")
        (CallE
          "subst_typevar"
          (ExpA (VarE "tv"))
          (ExpA (IterE (VarE "tv'") List (iterexp "tv'" (VarE "tv'*"))))
          (ExpA (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*"))))
        )
      )
    )
  )
)
HintD
(RecD
  (DecD
    "minus_recs"
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (TupT
      (typbind "_" (IterT (VarT "typevar") List))
      (typbind "_" (IterT (VarT "typeuse") List))
    )
    (DefD (ExpA (ListE)) (ExpA (ListE)) (TupE (ListE) (ListE)))
    (DefD
      (ExpP "n" nat)
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu_1" (VarT "typeuse"))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom REC) Arg) (TupE (VarE "n"))))
          (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*")))
        )
      )
      (ExpA
        (CatE
          (ListE (VarE "tu_1"))
          (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*")))
        )
      )
      (CallE
        "minus_recs"
        (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
        (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      )
    )
    (DefD
      (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu_1" (VarT "typeuse"))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x"))))
          (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*")))
        )
      )
      (ExpA
        (CatE
          (ListE (VarE "tu_1"))
          (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*")))
        )
      )
      (TupE
        (CatE
          (ListE (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x"))))
          (IterE (VarE "tv'") List (iterexp "tv'" (VarE "tv'*")))
        )
        (CatE
          (ListE (VarE "tu_1"))
          (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*")))
        )
      )
      (LetPr
        (TupE
          (IterE (VarE "tv'") List (iterexp "tv'" (VarE "tv'*")))
          (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*")))
        )
        (CallE
          "minus_recs"
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
)
(DecD
  "subst_packtype"
  (ExpP "packtype" (VarT "packtype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "packtype")
  (DefD
    (ExpP "pt" (VarT "packtype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (VarE "pt"))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (VarE "pt")
  )
)
(DecD
  "subst_numtype"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "numtype")
  (DefD
    (ExpP "nt" (VarT "numtype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (VarE "nt"))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (VarE "nt")
  )
)
(DecD
  "subst_vectype"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "vectype")
  (DefD
    (ExpP "vt" (VarT "vectype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (VarE "vt"))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (VarE "vt")
  )
)
(RecD
  (DecD
    "subst_typeuse"
    (ExpP "typeuse" (VarT "typeuse"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "typeuse")
    (DefD
      (ExpP "tv'" (VarT "typevar"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "typevar") (VarT "typeuse") (VarE "tv'")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CallE
        "subst_typevar"
        (ExpA (VarE "tv'"))
        (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
        (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      )
    )
    (DefD
      (ExpP "dt" (VarT "deftype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "deftype")
        (VarT "typeuse")
        (CallE
          "subst_deftype"
          (ExpA (VarE "dt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DecD
    "subst_heaptype"
    (ExpP "heaptype" (VarT "heaptype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "heaptype")
    (DefD
      (ExpP "tv'" (VarT "typevar"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "typevar") (VarT "heaptype") (VarE "tv'")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "typeuse")
        (VarT "heaptype")
        (CallE
          "subst_typevar"
          (ExpA (VarE "tv'"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
    (DefD
      (ExpP "dt" (VarT "deftype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "deftype") (VarT "heaptype") (VarE "dt")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "deftype")
        (VarT "heaptype")
        (CallE
          "subst_deftype"
          (ExpA (VarE "dt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
    (DefD
      (ExpP "ht" (VarT "heaptype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (VarE "ht"))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (VarE "ht")
    )
  )
  (DecD
    "subst_reftype"
    (ExpP "reftype" (VarT "reftype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "reftype")
    (DefD
      (ExpP "null?" (IterT (VarT "null") Opt))
      (ExpP "ht" (VarT "heaptype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE
            (IterE (VarE "null") Opt (iterexp "null" (VarE "null?")))
            (VarE "ht")
          )
        )
      )
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq (Atom REF) Arg Arg)
        (TupE
          (IterE (VarE "null") Opt (iterexp "null" (VarE "null?")))
          (CallE
            "subst_heaptype"
            (ExpA (VarE "ht"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
        )
      )
    )
  )
  (DecD
    "subst_valtype"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "valtype")
    (DefD
      (ExpP "nt" (VarT "numtype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "numtype")
        (VarT "valtype")
        (CallE
          "subst_numtype"
          (ExpA (VarE "nt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
    (DefD
      (ExpP "vt" (VarT "vectype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "vectype") (VarT "valtype") (VarE "vt")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "vectype")
        (VarT "valtype")
        (CallE
          "subst_vectype"
          (ExpA (VarE "vt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
    (DefD
      (ExpP "rt" (VarT "reftype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "reftype") (VarT "valtype") (VarE "rt")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "reftype")
        (VarT "valtype")
        (CallE
          "subst_reftype"
          (ExpA (VarE "rt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
    (DefD
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (CaseE (Atom BOT) (TupE)))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE (Atom BOT) (TupE))
    )
  )
  (DecD
    "subst_storagetype"
    (ExpP "storagetype" (VarT "storagetype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "storagetype")
    (DefD
      (ExpP "t" (VarT "valtype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "valtype") (VarT "storagetype") (VarE "t")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "valtype")
        (VarT "storagetype")
        (CallE
          "subst_valtype"
          (ExpA (VarE "t"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
    (DefD
      (ExpP "pt" (VarT "packtype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "pt")))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (SubE
        (VarT "packtype")
        (VarT "storagetype")
        (CallE
          "subst_packtype"
          (ExpA (VarE "pt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DecD
    "subst_fieldtype"
    (ExpP "fieldtype" (VarT "fieldtype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "fieldtype")
    (DefD
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CaseE
          (Seq Arg Arg)
          (TupE
            (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
            (VarE "zt")
          )
        )
      )
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq Arg Arg)
        (TupE
          (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
          (CallE
            "subst_storagetype"
            (ExpA (VarE "zt"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
        )
      )
    )
  )
  (DecD
    "subst_comptype"
    (ExpP "comptype" (VarT "comptype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "comptype")
    (DefD
      (ExpP "ft*" (IterT (VarT "fieldtype") List))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CaseE
          (Seq (Atom STRUCT) Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*"))))
            )
          )
        )
      )
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq (Atom STRUCT) Arg)
        (TupE
          (CaseE
            Arg
            (TupE
              (IterE
                (CallE
                  "subst_fieldtype"
                  (ExpA (VarE "ft"))
                  (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
                  (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
                )
                List
                (iterexp "ft" (VarE "ft*"))
              )
            )
          )
        )
      )
    )
    (DefD
      (ExpP "ft" (VarT "fieldtype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "ft"))))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq (Atom ARRAY) Arg)
        (TupE
          (CallE
            "subst_fieldtype"
            (ExpA (VarE "ft"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
        )
      )
    )
    (DefD
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Infix (Seq (Atom FUNC) Arg) -> Arg)
        (TupE
          (CaseE
            Arg
            (TupE
              (IterE
                (CallE
                  "subst_valtype"
                  (ExpA (VarE "t_1"))
                  (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
                  (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
                )
                List
                (iterexp "t_1" (VarE "t_1*"))
              )
            )
          )
          (CaseE
            Arg
            (TupE
              (IterE
                (CallE
                  "subst_valtype"
                  (ExpA (VarE "t_2"))
                  (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
                  (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
                )
                List
                (iterexp "t_2" (VarE "t_2*"))
              )
            )
          )
        )
      )
    )
  )
  (DecD
    "subst_subtype"
    (ExpP "subtype" (VarT "subtype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "subtype")
    (DefD
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "tu'*" (IterT (VarT "typeuse") List))
      (ExpP "ct" (VarT "comptype"))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CaseE
          (Seq (Atom SUB) Arg Arg Arg)
          (TupE
            (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
            (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*")))
            (VarE "ct")
          )
        )
      )
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq (Atom SUB) Arg Arg Arg)
        (TupE
          (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
          (IterE
            (CallE
              "subst_typeuse"
              (ExpA (VarE "tu'"))
              (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
              (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
            )
            List
            (iterexp "tu'" (VarE "tu'*"))
          )
          (CallE
            "subst_comptype"
            (ExpA (VarE "ct"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
        )
      )
    )
  )
  (DecD
    "subst_rectype"
    (ExpP "rectype" (VarT "rectype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "rectype")
    (DefD
      (ExpP "st*" (IterT (VarT "subtype") List))
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "st") List (iterexp "st" (VarE "st*"))))
            )
          )
        )
      )
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq (Atom REC) Arg)
        (TupE
          (CaseE
            Arg
            (TupE
              (IterE
                (CallE
                  "subst_subtype"
                  (ExpA (VarE "st"))
                  (ExpA (IterE (VarE "tv'") List (iterexp "tv'" (VarE "tv'*"))))
                  (ExpA (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*"))))
                )
                List
                (iterexp "st" (VarE "st*"))
              )
            )
          )
        )
      )
      (LetPr
        (TupE
          (IterE (VarE "tv'") List (iterexp "tv'" (VarE "tv'*")))
          (IterE (VarE "tu'") List (iterexp "tu'" (VarE "tu'*")))
        )
        (CallE
          "minus_recs"
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DecD
    "subst_deftype"
    (ExpP "deftype" (VarT "deftype"))
    (ExpP "_" (IterT (VarT "typevar") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (VarT "deftype")
    (DefD
      (ExpP "qt" (VarT "rectype"))
      (ExpP "i" nat)
      (ExpP "tv*" (IterT (VarT "typevar") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (CaseE (Seq (Atom _DEF) Arg Arg) (TupE (VarE "qt") (VarE "i"))))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CaseE
        (Seq (Atom _DEF) Arg Arg)
        (TupE
          (CallE
            "subst_rectype"
            (ExpA (VarE "qt"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
          (VarE "i")
        )
      )
    )
  )
)
HintD
(DecD
  "subst_addrtype"
  (ExpP "addrtype" (VarT "addrtype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "addrtype")
  (DefD
    (ExpP "at" (VarT "addrtype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (VarE "at"))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (VarE "at")
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
HintD
HintD
HintD
HintD
HintD
(DecD
  "subst_tagtype"
  (ExpP "tagtype" (VarT "tagtype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "tagtype")
  (DefD
    (ExpP "tu'" (VarT "typeuse"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (VarE "tu'"))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_typeuse"
      (ExpA (VarE "tu'"))
      (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_globaltype"
  (ExpP "globaltype" (VarT "globaltype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "globaltype")
  (DefD
    (ExpP "mut?" (IterT (VarT "mut") Opt))
    (ExpP "t" (VarT "valtype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA
      (CaseE
        (Seq Arg Arg)
        (TupE (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?"))) (VarE "t"))
      )
    )
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq Arg Arg)
      (TupE
        (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
        (CallE
          "subst_valtype"
          (ExpA (VarE "t"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
)
HintD
(DecD
  "subst_memtype"
  (ExpP "memtype" (VarT "memtype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "memtype")
  (DefD
    (ExpP "at" (VarT "addrtype"))
    (ExpP "lim" (VarT "limits"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
  )
)
HintD
(DecD
  "subst_tabletype"
  (ExpP "tabletype" (VarT "tabletype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "tabletype")
  (DefD
    (ExpP "at" (VarT "addrtype"))
    (ExpP "lim" (VarT "limits"))
    (ExpP "rt" (VarT "reftype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq Arg Arg Arg)
      (TupE
        (VarE "at")
        (VarE "lim")
        (CallE
          "subst_reftype"
          (ExpA (VarE "rt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
)
HintD
(DecD
  "subst_externtype"
  (ExpP "externtype" (VarT "externtype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "externtype")
  (DefD
    (ExpP "jt" (VarT "typeuse"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "jt"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq (Atom TAG) Arg)
      (TupE
        (CallE
          "subst_tagtype"
          (ExpA (VarE "jt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DefD
    (ExpP "gt" (VarT "globaltype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq (Atom GLOBAL) Arg)
      (TupE
        (CallE
          "subst_globaltype"
          (ExpA (VarE "gt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DefD
    (ExpP "tt" (VarT "tabletype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq (Atom TABLE) Arg)
      (TupE
        (CallE
          "subst_tabletype"
          (ExpA (VarE "tt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DefD
    (ExpP "mt" (VarT "memtype"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq (Atom MEM) Arg)
      (TupE
        (CallE
          "subst_memtype"
          (ExpA (VarE "mt"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
  (DefD
    (ExpP "tu'" (VarT "typeuse"))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "tu'"))))
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Seq (Atom FUNC) Arg)
      (TupE
        (CallE
          "subst_typeuse"
          (ExpA (VarE "tu'"))
          (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
)
HintD
(DecD
  "subst_moduletype"
  (ExpP "moduletype" (VarT "moduletype"))
  (ExpP "_" (IterT (VarT "typevar") List))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "moduletype")
  (DefD
    (ExpP "xt_1*" (IterT (VarT "externtype") List))
    (ExpP "xt_2*" (IterT (VarT "externtype") List))
    (ExpP "tv*" (IterT (VarT "typevar") List))
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpA
      (CaseE
        (Infix Arg -> Arg)
        (TupE
          (IterE (VarE "xt_1") List (iterexp "xt_1" (VarE "xt_1*")))
          (IterE (VarE "xt_2") List (iterexp "xt_2" (VarE "xt_2*")))
        )
      )
    )
    (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
    (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
    (CaseE
      (Infix Arg -> Arg)
      (TupE
        (IterE
          (CallE
            "subst_externtype"
            (ExpA (VarE "xt_1"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
          List
          (iterexp "xt_1" (VarE "xt_1*"))
        )
        (IterE
          (CallE
            "subst_externtype"
            (ExpA (VarE "xt_2"))
            (ExpA (IterE (VarE "tv") List (iterexp "tv" (VarE "tv*"))))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
          List
          (iterexp "xt_2" (VarE "xt_2*"))
        )
      )
    )
  )
)
HintD
HintD
(DecD
  "subst_all_valtype"
  (ExpP "valtype" (VarT "valtype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "valtype")
  (DefD
    (ExpP "t" (VarT "valtype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "t"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_valtype"
      (ExpA (VarE "t"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_reftype"
  (ExpP "reftype" (VarT "reftype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "reftype")
  (DefD
    (ExpP "rt" (VarT "reftype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "rt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_reftype"
      (ExpA (VarE "rt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_deftype"
  (ExpP "deftype" (VarT "deftype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "deftype")
  (DefD
    (ExpP "dt" (VarT "deftype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "dt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_deftype"
      (ExpA (VarE "dt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_tagtype"
  (ExpP "tagtype" (VarT "tagtype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "tagtype")
  (DefD
    (ExpP "jt" (VarT "typeuse"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "jt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_tagtype"
      (ExpA (VarE "jt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_globaltype"
  (ExpP "globaltype" (VarT "globaltype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "globaltype")
  (DefD
    (ExpP "gt" (VarT "globaltype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "gt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_globaltype"
      (ExpA (VarE "gt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_memtype"
  (ExpP "memtype" (VarT "memtype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "memtype")
  (DefD
    (ExpP "mt" (VarT "memtype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "mt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_memtype"
      (ExpA (VarE "mt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_tabletype"
  (ExpP "tabletype" (VarT "tabletype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "tabletype")
  (DefD
    (ExpP "tt" (VarT "tabletype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "tt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_tabletype"
      (ExpA (VarE "tt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_externtype"
  (ExpP "externtype" (VarT "externtype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "externtype")
  (DefD
    (ExpP "xt" (VarT "externtype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "xt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_externtype"
      (ExpA (VarE "xt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(DecD
  "subst_all_moduletype"
  (ExpP "moduletype" (VarT "moduletype"))
  (ExpP "_" (IterT (VarT "typeuse") List))
  (VarT "moduletype")
  (DefD
    (ExpP "mmt" (VarT "moduletype"))
    (ExpP "n" nat)
    (ExpP "tu*" (IterT (VarT "typeuse") List))
    (ExpP "i" nat)
    (ExpA (VarE "mmt"))
    (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    (CallE
      "subst_moduletype"
      (ExpA (VarE "mmt"))
      (ExpA
        (IterE
          (CaseE (Seq (Atom _IDX) Arg) (TupE (CaseE Arg (TupE (VarE "i")))))
          (ListN (VarE "n") "i")
        )
      )
      (ExpA (IterE (VarE "tu") (ListN (VarE "n")) (iterexp "tu" (VarE "tu*"))))
    )
  )
)
HintD
(RecD
  (DecD
    "subst_all_deftypes"
    (ExpP "_" (IterT (VarT "deftype") List))
    (ExpP "_" (IterT (VarT "typeuse") List))
    (IterT (VarT "deftype") List)
    (DefD
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA (ListE))
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (ListE)
    )
    (DefD
      (ExpP "dt_1" (VarT "deftype"))
      (ExpP "dt*" (IterT (VarT "deftype") List))
      (ExpP "tu*" (IterT (VarT "typeuse") List))
      (ExpA
        (CatE
          (ListE (VarE "dt_1"))
          (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
        )
      )
      (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
      (CatE
        (ListE
          (CallE
            "subst_all_deftype"
            (ExpA (VarE "dt_1"))
            (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
          )
        )
        (CallE
          "subst_all_deftypes"
          (ExpA (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*"))))
          (ExpA (IterE (VarE "tu") List (iterexp "tu" (VarE "tu*"))))
        )
      )
    )
  )
)
HintD
(DecD
  "rollrt"
  (ExpP "typeidx" (VarT "typeidx"))
  (ExpP "rectype" (VarT "rectype"))
  (VarT "rectype")
  (DefD
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "rectype" (VarT "rectype"))
    (ExpP "i" nat)
    (ExpP "n" nat)
    (ExpP "subtype*" (IterT (VarT "subtype") List))
    (ExpA (VarE "x"))
    (ExpA (VarE "rectype"))
    (CaseE
      (Seq (Atom REC) Arg)
      (TupE
        (CaseE
          Arg
          (TupE
            (IterE
              (CallE
                "subst_subtype"
                (ExpA (VarE "subtype"))
                (ExpA
                  (IterE
                    (CaseE
                      (Seq (Atom _IDX) Arg)
                      (TupE
                        (CaseE
                          Arg
                          (TupE
                            (BinE
                              AddOp
                              nat
                              (ProjE (UncaseE (VarE "x") Arg) 0)
                              (VarE "i")
                            )
                          )
                        )
                      )
                    )
                    (ListN (VarE "n") "i")
                  )
                )
                (ExpA
                  (IterE
                    (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i")))
                    (ListN (VarE "n") "i")
                  )
                )
              )
              (ListN (VarE "n"))
              (iterexp "subtype" (VarE "subtype*"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "rectype")
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (VarE "subtype")
                  (ListN (VarE "n"))
                  (iterexp "subtype" (VarE "subtype*"))
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
(DecD
  "unrollrt"
  (ExpP "rectype" (VarT "rectype"))
  (VarT "rectype")
  (DefD
    (ExpP "rectype" (VarT "rectype"))
    (ExpP "i" nat)
    (ExpP "n" nat)
    (ExpP "subtype*" (IterT (VarT "subtype") List))
    (ExpA (VarE "rectype"))
    (CaseE
      (Seq (Atom REC) Arg)
      (TupE
        (CaseE
          Arg
          (TupE
            (IterE
              (CallE
                "subst_subtype"
                (ExpA (VarE "subtype"))
                (ExpA
                  (IterE
                    (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i")))
                    (ListN (VarE "n") "i")
                  )
                )
                (ExpA
                  (IterE
                    (CaseE
                      (Seq (Atom _DEF) Arg Arg)
                      (TupE (VarE "rectype") (VarE "i"))
                    )
                    (ListN (VarE "n") "i")
                  )
                )
              )
              (ListN (VarE "n"))
              (iterexp "subtype" (VarE "subtype*"))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "rectype")
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (VarE "subtype")
                  (ListN (VarE "n"))
                  (iterexp "subtype" (VarE "subtype*"))
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
(DecD
  "rolldt"
  (ExpP "typeidx" (VarT "typeidx"))
  (ExpP "rectype" (VarT "rectype"))
  (IterT (VarT "deftype") List)
  (DefD
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "rectype" (VarT "rectype"))
    (ExpP "n" nat)
    (ExpP "subtype*" (IterT (VarT "subtype") List))
    (ExpA (VarE "x"))
    (ExpA (VarE "rectype"))
    (IterE
      (CaseE
        (Seq (Atom _DEF) Arg Arg)
        (TupE
          (CaseE
            (Seq (Atom REC) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (VarE "subtype")
                    (ListN (VarE "n"))
                    (iterexp "subtype" (VarE "subtype*"))
                  )
                )
              )
            )
          )
          (VarE "i")
        )
      )
      (ListN (VarE "n") "i")
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "rollrt" (ExpA (VarE "x")) (ExpA (VarE "rectype")))
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (VarE "subtype")
                  (ListN (VarE "n"))
                  (iterexp "subtype" (VarE "subtype*"))
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
(DecD
  "unrolldt"
  (ExpP "deftype" (VarT "deftype"))
  (VarT "subtype")
  (DefD
    (ExpP "rectype" (VarT "rectype"))
    (ExpP "i" nat)
    (ExpA (CaseE (Seq (Atom _DEF) Arg Arg) (TupE (VarE "rectype") (VarE "i"))))
    (IdxE
      (IterE (VarE "subtype") List (iterexp "subtype" (VarE "subtype*")))
      (VarE "i")
    )
    (LetPr
      (CaseE
        (Seq (Atom REC) Arg)
        (TupE
          (CaseE
            Arg
            (TupE
              (IterE
                (VarE "subtype")
                List
                (iterexp "subtype" (VarE "subtype*"))
              )
            )
          )
        )
      )
      (CallE "unrollrt" (ExpA (VarE "rectype")))
    )
  )
)
HintD
(DecD
  "free_addrtype"
  (ExpP "addrtype" (VarT "addrtype"))
  (VarT "free")
  (DefD
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpA (VarE "addrtype"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_numtype"
  (ExpP "numtype" (VarT "numtype"))
  (VarT "free")
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_packtype"
  (ExpP "packtype" (VarT "packtype"))
  (VarT "free")
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (VarE "packtype"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_lanetype"
  (ExpP "lanetype" (VarT "lanetype"))
  (VarT "free")
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
    (CallE "free_numtype" (ExpA (VarE "numtype")))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
    (CallE "free_packtype" (ExpA (VarE "packtype")))
  )
)
(DecD
  "free_vectype"
  (ExpP "vectype" (VarT "vectype"))
  (VarT "free")
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpA (VarE "vectype"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_consttype"
  (ExpP "consttype" (VarT "consttype"))
  (VarT "free")
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (SubE (VarT "numtype") (VarT "consttype") (VarE "numtype")))
    (CallE "free_numtype" (ExpA (VarE "numtype")))
  )
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpA (SubE (VarT "vectype") (VarT "consttype") (VarE "vectype")))
    (CallE "free_vectype" (ExpA (VarE "vectype")))
  )
)
(DecD
  "free_absheaptype"
  (ExpP "absheaptype" (VarT "absheaptype"))
  (VarT "free")
  (DefD
    (ExpP "absheaptype" (VarT "absheaptype"))
    (ExpA (VarE "absheaptype"))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_typevar"
  (ExpP "typevar" (VarT "typevar"))
  (VarT "free")
  (DefD
    (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx"))))
    (CallE "free_typeidx" (ExpA (VarE "typeidx")))
  )
  (DefD
    (ExpP "n" nat)
    (ExpA (CaseE (Seq (Atom REC) Arg) (TupE (VarE "n"))))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(RecD
  (DecD
    "free_heaptype"
    (ExpP "heaptype" (VarT "heaptype"))
    (VarT "free")
    (DefD
      (ExpP "absheaptype" (VarT "absheaptype"))
      (ExpA (SubE (VarT "absheaptype") (VarT "heaptype") (VarE "absheaptype")))
      (CallE "free_absheaptype" (ExpA (VarE "absheaptype")))
    )
    (DefD
      (ExpP "typeuse" (VarT "typeuse"))
      (ExpA (SubE (VarT "typeuse") (VarT "heaptype") (VarE "typeuse")))
      (CallE "free_typeuse" (ExpA (VarE "typeuse")))
    )
  )
  (DecD
    "free_reftype"
    (ExpP "reftype" (VarT "reftype"))
    (VarT "free")
    (DefD
      (ExpP "null?" (IterT (VarT "null") Opt))
      (ExpP "heaptype" (VarT "heaptype"))
      (ExpA
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE
            (IterE (VarE "null") Opt (iterexp "null" (VarE "null?")))
            (VarE "heaptype")
          )
        )
      )
      (CallE "free_heaptype" (ExpA (VarE "heaptype")))
    )
  )
  (DecD
    "free_typeuse"
    (ExpP "typeuse" (VarT "typeuse"))
    (VarT "free")
    (DefD
      (ExpP "typevar" (VarT "typevar"))
      (ExpA (SubE (VarT "typevar") (VarT "typeuse") (VarE "typevar")))
      (CallE "free_typevar" (ExpA (VarE "typevar")))
    )
    (DefD
      (ExpP "deftype" (VarT "deftype"))
      (ExpA (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype")))
      (CallE "free_deftype" (ExpA (VarE "deftype")))
    )
  )
  (DecD
    "free_valtype"
    (ExpP "valtype" (VarT "valtype"))
    (VarT "free")
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpA (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype")))
      (CallE "free_numtype" (ExpA (VarE "numtype")))
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpA (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype")))
      (CallE "free_vectype" (ExpA (VarE "vectype")))
    )
    (DefD
      (ExpP "reftype" (VarT "reftype"))
      (ExpA (SubE (VarT "reftype") (VarT "valtype") (VarE "reftype")))
      (CallE "free_reftype" (ExpA (VarE "reftype")))
    )
    (DefD
      (ExpA (CaseE (Atom BOT) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
  )
  (DecD
    "free_resulttype"
    (ExpP "resulttype" (VarT "resulttype"))
    (VarT "free")
    (DefD
      (ExpP "valtype*" (IterT (VarT "valtype") List))
      (ExpA
        (CaseE
          Arg
          (TupE
            (IterE (VarE "valtype") List (iterexp "valtype" (VarE "valtype*")))
          )
        )
      )
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_valtype" (ExpA (VarE "valtype")))
            List
            (iterexp "valtype" (VarE "valtype*"))
          )
        )
      )
    )
  )
  (DecD
    "free_storagetype"
    (ExpP "storagetype" (VarT "storagetype"))
    (VarT "free")
    (DefD
      (ExpP "valtype" (VarT "valtype"))
      (ExpA (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype")))
      (CallE "free_valtype" (ExpA (VarE "valtype")))
    )
    (DefD
      (ExpP "packtype" (VarT "packtype"))
      (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
      (CallE "free_packtype" (ExpA (VarE "packtype")))
    )
  )
  (DecD
    "free_fieldtype"
    (ExpP "fieldtype" (VarT "fieldtype"))
    (VarT "free")
    (DefD
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (ExpP "storagetype" (VarT "storagetype"))
      (ExpA
        (CaseE
          (Seq Arg Arg)
          (TupE
            (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
            (VarE "storagetype")
          )
        )
      )
      (CallE "free_storagetype" (ExpA (VarE "storagetype")))
    )
  )
  (DecD
    "free_comptype"
    (ExpP "comptype" (VarT "comptype"))
    (VarT "free")
    (DefD
      (ExpP "fieldtype*" (IterT (VarT "fieldtype") List))
      (ExpA
        (CaseE
          (Seq (Atom STRUCT) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (VarE "fieldtype")
                  List
                  (iterexp "fieldtype" (VarE "fieldtype*"))
                )
              )
            )
          )
        )
      )
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_fieldtype" (ExpA (VarE "fieldtype")))
            List
            (iterexp "fieldtype" (VarE "fieldtype*"))
          )
        )
      )
    )
    (DefD
      (ExpP "fieldtype" (VarT "fieldtype"))
      (ExpA (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "fieldtype"))))
      (CallE "free_fieldtype" (ExpA (VarE "fieldtype")))
    )
    (DefD
      (ExpP "resulttype_1" (VarT "list" (TypA (VarT "valtype"))))
      (ExpP "resulttype_2" (VarT "list" (TypA (VarT "valtype"))))
      (ExpA
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE (VarE "resulttype_1") (VarE "resulttype_2"))
        )
      )
      (CompE
        (CallE "free_resulttype" (ExpA (VarE "resulttype_1")))
        (CallE "free_resulttype" (ExpA (VarE "resulttype_2")))
      )
    )
  )
  (DecD
    "free_subtype"
    (ExpP "subtype" (VarT "subtype"))
    (VarT "free")
    (DefD
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "typeuse*" (IterT (VarT "typeuse") List))
      (ExpP "comptype" (VarT "comptype"))
      (ExpA
        (CaseE
          (Seq (Atom SUB) Arg Arg Arg)
          (TupE
            (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
            (IterE (VarE "typeuse") List (iterexp "typeuse" (VarE "typeuse*")))
            (VarE "comptype")
          )
        )
      )
      (CompE
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_typeuse" (ExpA (VarE "typeuse")))
              List
              (iterexp "typeuse" (VarE "typeuse*"))
            )
          )
        )
        (CallE "free_comptype" (ExpA (VarE "comptype")))
      )
    )
  )
  (DecD
    "free_rectype"
    (ExpP "rectype" (VarT "rectype"))
    (VarT "free")
    (DefD
      (ExpP "subtype*" (IterT (VarT "subtype") List))
      (ExpA
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (VarE "subtype")
                  List
                  (iterexp "subtype" (VarE "subtype*"))
                )
              )
            )
          )
        )
      )
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_subtype" (ExpA (VarE "subtype")))
            List
            (iterexp "subtype" (VarE "subtype*"))
          )
        )
      )
    )
  )
  (DecD
    "free_deftype"
    (ExpP "deftype" (VarT "deftype"))
    (VarT "free")
    (DefD
      (ExpP "rectype" (VarT "rectype"))
      (ExpP "n" nat)
      (ExpA
        (CaseE (Seq (Atom _DEF) Arg Arg) (TupE (VarE "rectype") (VarE "n")))
      )
      (CallE "free_rectype" (ExpA (VarE "rectype")))
    )
  )
)
(DecD
  "free_tagtype"
  (ExpP "tagtype" (VarT "tagtype"))
  (VarT "free")
  (DefD
    (ExpP "deftype" (VarT "deftype"))
    (ExpA (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype")))
    (CallE "free_deftype" (ExpA (VarE "deftype")))
  )
)
(DecD
  "free_globaltype"
  (ExpP "globaltype" (VarT "globaltype"))
  (VarT "free")
  (DefD
    (ExpP "mut?" (IterT (VarT "mut") Opt))
    (ExpP "valtype" (VarT "valtype"))
    (ExpA
      (CaseE
        (Seq Arg Arg)
        (TupE
          (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
          (VarE "valtype")
        )
      )
    )
    (CallE "free_valtype" (ExpA (VarE "valtype")))
  )
)
(DecD
  "free_memtype"
  (ExpP "memtype" (VarT "memtype"))
  (VarT "free")
  (DefD
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpP "limits" (VarT "limits"))
    (ExpA
      (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "addrtype") (VarE "limits")))
    )
    (CallE "free_addrtype" (ExpA (VarE "addrtype")))
  )
)
(DecD
  "free_tabletype"
  (ExpP "tabletype" (VarT "tabletype"))
  (VarT "free")
  (DefD
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpP "limits" (VarT "limits"))
    (ExpP "reftype" (VarT "reftype"))
    (ExpA
      (CaseE
        (Seq Arg Arg Arg)
        (TupE (VarE "addrtype") (VarE "limits") (VarE "reftype"))
      )
    )
    (CompE
      (CallE "free_addrtype" (ExpA (VarE "addrtype")))
      (CallE "free_reftype" (ExpA (VarE "reftype")))
    )
  )
)
(DecD
  "free_datatype"
  (ExpP "datatype" (VarT "datatype"))
  (VarT "free")
  (DefD
    (ExpA (CaseE (Atom OK) (TupE)))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_elemtype"
  (ExpP "elemtype" (VarT "elemtype"))
  (VarT "free")
  (DefD
    (ExpP "reftype" (VarT "reftype"))
    (ExpA (VarE "reftype"))
    (CallE "free_reftype" (ExpA (VarE "reftype")))
  )
)
(DecD
  "free_externtype"
  (ExpP "externtype" (VarT "externtype"))
  (VarT "free")
  (DefD
    (ExpP "tagtype" (VarT "typeuse"))
    (ExpA (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagtype"))))
    (CallE "free_tagtype" (ExpA (VarE "tagtype")))
  )
  (DefD
    (ExpP "globaltype" (VarT "globaltype"))
    (ExpA (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype"))))
    (CallE "free_globaltype" (ExpA (VarE "globaltype")))
  )
  (DefD
    (ExpP "memtype" (VarT "memtype"))
    (ExpA (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype"))))
    (CallE "free_memtype" (ExpA (VarE "memtype")))
  )
  (DefD
    (ExpP "tabletype" (VarT "tabletype"))
    (ExpA (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    (CallE "free_tabletype" (ExpA (VarE "tabletype")))
  )
  (DefD
    (ExpP "typeuse" (VarT "typeuse"))
    (ExpA (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "typeuse"))))
    (CallE "free_typeuse" (ExpA (VarE "typeuse")))
  )
)
(DecD
  "free_moduletype"
  (ExpP "moduletype" (VarT "moduletype"))
  (VarT "free")
  (DefD
    (ExpP "externtype_1*" (IterT (VarT "externtype") List))
    (ExpP "externtype_2*" (IterT (VarT "externtype") List))
    (ExpA
      (CaseE
        (Infix Arg -> Arg)
        (TupE
          (IterE
            (VarE "externtype_1")
            List
            (iterexp "externtype_1" (VarE "externtype_1*"))
          )
          (IterE
            (VarE "externtype_2")
            List
            (iterexp "externtype_2" (VarE "externtype_2*"))
          )
        )
      )
    )
    (CompE
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_externtype" (ExpA (VarE "externtype_1")))
            List
            (iterexp "externtype_1" (VarE "externtype_1*"))
          )
        )
      )
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_externtype" (ExpA (VarE "externtype_2")))
            List
            (iterexp "externtype_2" (VarE "externtype_2*"))
          )
        )
      )
    )
  )
)
(TypD
  "num_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_num__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind
            "var_x"
            (VarT
              "iN"
              (ExpA
                (CallE
                  "sizenn"
                  (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
                )
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_num__1) Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind
            "var_x"
            (VarT
              "fN"
              (ExpA
                (CallE
                  "sizenn"
                  (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
                )
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_num__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT "num_" (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))))
  )
  (IterT
    (VarT
      "iN"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
    )
    Opt
  )
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "iN"
        (ExpA
          (CallE
            "sizenn"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "num_"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
      )
    )
    (ExpA (VarE "Inn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_num__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT "num_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
  )
  (IterT
    (VarT
      "fN"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
    )
    Opt
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT
        "fN"
        (ExpA
          (CallE
            "sizenn"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (VarE "Fnn"))
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "num_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
(TypD
  "pack_"
  (ExpP "Pnn" (VarT "Pnn"))
  (InstD
    (ExpP "Pnn" (VarT "Pnn"))
    (ExpA (VarE "Pnn"))
    (AliasT (VarT "iN" (ExpA (CallE "psizenn" (ExpA (VarE "Pnn"))))))
  )
)
(TypD
  "lane_"
  (ExpP "lanetype" (VarT "lanetype"))
  (InstD
    (ExpP "lanetype" (VarT "lanetype"))
    (ExpA (VarE "lanetype"))
    (VariantT
      (typcase
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupT
          (typbind "numtype" (VarT "numtype"))
          (typbind "var_x" (VarT "num_" (ExpA (VarE "numtype"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "lanetype")
            (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_lane__1) Arg Arg)
        (TupT
          (typbind "packtype" (VarT "packtype"))
          (typbind "var_x" (VarT "pack_" (ExpA (VarE "packtype"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "lanetype")
            (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_lane__2) Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind
            "var_x"
            (VarT
              "iN"
              (ExpA
                (CallE
                  "lsize"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
                )
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "lanetype")
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_lane__0"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP
    "var_x"
    (VarT
      "lane_"
      (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
    )
  )
  (IterT (VarT "num_" (ExpA (VarE "numtype"))) Opt)
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "var_x" (VarT "num_" (ExpA (VarE "numtype"))))
    (ExpA (VarE "numtype"))
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE (VarE "numtype") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP
      "var_x"
      (VarT
        "lane_"
        (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
      )
    )
    (ExpA (VarE "numtype"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_lane__1"
  (ExpP "packtype" (VarT "packtype"))
  (ExpP
    "var_x"
    (VarT
      "lane_"
      (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
    )
  )
  (IterT (VarT "pack_" (ExpA (VarE "packtype"))) Opt)
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "var_x" (VarT "pack_" (ExpA (VarE "packtype"))))
    (ExpA (VarE "packtype"))
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__1) Arg Arg)
        (TupE (VarE "packtype") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP
      "var_x"
      (VarT
        "lane_"
        (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
      )
    )
    (ExpA (VarE "packtype"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_lane__2"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP
    "var_x"
    (VarT "lane_" (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))))
  )
  (IterT
    (VarT
      "iN"
      (ExpA
        (CallE
          "lsize"
          (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
        )
      )
    )
    Opt
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP
      "var_x"
      (VarT
        "iN"
        (ExpA
          (CallE
            "lsize"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
          )
        )
      )
    )
    (ExpA (VarE "Jnn"))
    (ExpA
      (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP
      "var_x"
      (VarT "lane_" (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))))
    )
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
(TypD
  "vec_"
  (ExpP "Vnn" (VarT "Vnn"))
  (InstD
    (ExpP "Vnn" (VarT "Vnn"))
    (ExpA (VarE "Vnn"))
    (AliasT (VarT "vN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
  )
)
(TypD
  "lit_"
  (ExpP "storagetype" (VarT "storagetype"))
  (InstD
    (ExpP "storagetype" (VarT "storagetype"))
    (ExpA (VarE "storagetype"))
    (VariantT
      (typcase
        (Seq (Atom mk_lit__0) Arg Arg)
        (TupT
          (typbind "numtype" (VarT "numtype"))
          (typbind "var_x" (VarT "num_" (ExpA (VarE "numtype"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "storagetype")
            (SubE (VarT "numtype") (VarT "storagetype") (VarE "numtype"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_lit__1) Arg Arg)
        (TupT
          (typbind "vectype" (VarT "vectype"))
          (typbind "var_x" (VarT "vec_" (ExpA (VarE "vectype"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "storagetype")
            (SubE (VarT "vectype") (VarT "storagetype") (VarE "vectype"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_lit__2) Arg Arg)
        (TupT
          (typbind "packtype" (VarT "packtype"))
          (typbind "var_x" (VarT "pack_" (ExpA (VarE "packtype"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "storagetype")
            (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_lit__0"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP
    "var_x"
    (VarT
      "lit_"
      (ExpA (SubE (VarT "numtype") (VarT "storagetype") (VarE "numtype")))
    )
  )
  (IterT (VarT "num_" (ExpA (VarE "numtype"))) Opt)
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "var_x" (VarT "num_" (ExpA (VarE "numtype"))))
    (ExpA (VarE "numtype"))
    (ExpA
      (CaseE
        (Seq (Atom mk_lit__0) Arg Arg)
        (TupE (VarE "numtype") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP
      "var_x"
      (VarT
        "lit_"
        (ExpA (SubE (VarT "numtype") (VarT "storagetype") (VarE "numtype")))
      )
    )
    (ExpA (VarE "numtype"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_lit__1"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP
    "var_x"
    (VarT
      "lit_"
      (ExpA (SubE (VarT "vectype") (VarT "storagetype") (VarE "vectype")))
    )
  )
  (IterT (VarT "vec_" (ExpA (VarE "vectype"))) Opt)
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpP "var_x" (VarT "vec_" (ExpA (VarE "vectype"))))
    (ExpA (VarE "vectype"))
    (ExpA
      (CaseE
        (Seq (Atom mk_lit__1) Arg Arg)
        (TupE (VarE "vectype") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpP
      "var_x"
      (VarT
        "lit_"
        (ExpA (SubE (VarT "vectype") (VarT "storagetype") (VarE "vectype")))
      )
    )
    (ExpA (VarE "vectype"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_lit__2"
  (ExpP "packtype" (VarT "packtype"))
  (ExpP
    "var_x"
    (VarT
      "lit_"
      (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    )
  )
  (IterT (VarT "pack_" (ExpA (VarE "packtype"))) Opt)
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "var_x" (VarT "pack_" (ExpA (VarE "packtype"))))
    (ExpA (VarE "packtype"))
    (ExpA
      (CaseE
        (Seq (Atom mk_lit__2) Arg Arg)
        (TupE (VarE "packtype") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP
      "var_x"
      (VarT
        "lit_"
        (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
      )
    )
    (ExpA (VarE "packtype"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
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
  "sx"
  (InstD (VariantT (typcase (Atom U) (TupT)) (typcase (Atom S) (TupT))))
)
HintD
(TypD
  "unop_Inn"
  (ExpP "Inn" (VarT "Inn"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (VarE "Inn"))
    (VariantT
      (typcase (Atom CLZ) (TupT))
      (typcase (Atom CTZ) (TupT))
      (typcase (Atom POPCNT) (TupT))
      (typcase
        (Seq (Atom EXTEND) Arg)
        (TupT (typbind "sz" (VarT "sz")))
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (UncaseE (VarE "sz") Arg) 0)
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "unop_Fnn"
  (ExpP "Fnn" (VarT "Fnn"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (VarE "Fnn"))
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
  "unop_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "unop_Inn" (ExpA (VarE "Inn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "var_x" (VarT "unop_Fnn" (ExpA (VarE "Fnn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_unop__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT "unop_" (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))))
  )
  (IterT (VarT "unop_Inn" (ExpA (VarE "Inn"))) Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn" (ExpA (VarE "Inn"))))
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE (Seq (Atom mk_unop__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "unop_"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
      )
    )
    (ExpA (VarE "Inn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_unop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT "unop_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
  )
  (IterT (VarT "unop_Fnn" (ExpA (VarE "Fnn"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn" (ExpA (VarE "Fnn"))))
    (ExpA (VarE "Fnn"))
    (ExpA
      (CaseE (Seq (Atom mk_unop__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "unop_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
(TypD
  "binop_Inn"
  (ExpP "Inn" (VarT "Inn"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (VarE "Inn"))
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
)
(TypD
  "binop_Fnn"
  (ExpP "Fnn" (VarT "Fnn"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (VarE "Fnn"))
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
  "binop_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "binop_Inn" (ExpA (VarE "Inn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "var_x" (VarT "binop_Fnn" (ExpA (VarE "Fnn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_binop__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "binop_"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    )
  )
  (IterT (VarT "binop_Inn" (ExpA (VarE "Inn"))) Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn" (ExpA (VarE "Inn"))))
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "binop_"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
      )
    )
    (ExpA (VarE "Inn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_binop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT "binop_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
  )
  (IterT (VarT "binop_Fnn" (ExpA (VarE "Fnn"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn" (ExpA (VarE "Fnn"))))
    (ExpA (VarE "Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "binop_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
(TypD
  "testop_Inn"
  (ExpP "Inn" (VarT "Inn"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (VarE "Inn"))
    (VariantT (typcase (Atom EQZ) (TupT)))
  )
)
(TypD
  "testop_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "testop_Inn" (ExpA (VarE "Inn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_testop__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "testop_"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    )
  )
  (VarT "testop_Inn" (ExpA (VarE "Inn")))
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn" (ExpA (VarE "Inn"))))
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
(TypD
  "relop_Inn"
  (ExpP "Inn" (VarT "Inn"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (VarE "Inn"))
    (VariantT
      (typcase (Atom EQ) (TupT))
      (typcase (Atom NE) (TupT))
      (typcase (Seq (Atom LT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom GT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom LE) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom GE) Arg) (TupT (typbind "sx" (VarT "sx"))))
    )
  )
)
(TypD
  "relop_Fnn"
  (ExpP "Fnn" (VarT "Fnn"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (VarE "Fnn"))
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
  "relop_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "relop_Inn" (ExpA (VarE "Inn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "var_x" (VarT "relop_Fnn" (ExpA (VarE "Fnn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_relop__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "relop_"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    )
  )
  (IterT (VarT "relop_Inn" (ExpA (VarE "Inn"))) Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn" (ExpA (VarE "Inn"))))
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "relop_"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
      )
    )
    (ExpA (VarE "Inn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_relop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT "relop_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
  )
  (IterT (VarT "relop_Fnn" (ExpA (VarE "Fnn"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn" (ExpA (VarE "Fnn"))))
    (ExpA (VarE "Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "relop_" (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))))
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
(TypD
  "cvtop__Inn_1_Inn_2"
  (ExpP "Inn_1" (VarT "Inn"))
  (ExpP "Inn_2" (VarT "Inn"))
  (InstD
    (ExpP "Inn_1" (VarT "Inn"))
    (ExpP "Inn_2" (VarT "Inn"))
    (ExpA (VarE "Inn_1"))
    (ExpA (VarE "Inn_2"))
    (VariantT
      (typcase
        (Seq (Atom EXTEND) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            LtOp
            nat
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
            )
          )
        )
      )
      (typcase
        (Atom WRAP)
        (TupT)
        (IfPr
          (CmpE
            GtOp
            nat
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "cvtop__Inn_1_Fnn_2"
  (ExpP "Inn_1" (VarT "Inn"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (InstD
    (ExpP "Inn_1" (VarT "Inn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpA (VarE "Inn_1"))
    (ExpA (VarE "Fnn_2"))
    (VariantT
      (typcase (Seq (Atom CONVERT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase
        (Atom REINTERPRET)
        (TupT)
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "cvtop__Fnn_1_Inn_2"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "Inn_2" (VarT "Inn"))
  (InstD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Inn_2" (VarT "Inn"))
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "Inn_2"))
    (VariantT
      (typcase (Seq (Atom TRUNC) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase (Seq (Atom TRUNC_SAT) Arg) (TupT (typbind "sx" (VarT "sx"))))
      (typcase
        (Atom REINTERPRET)
        (TupT)
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "cvtop__Fnn_1_Fnn_2"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (InstD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "Fnn_2"))
    (VariantT
      (typcase
        (Atom PROMOTE)
        (TupT)
        (IfPr
          (CmpE
            LtOp
            nat
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
            )
          )
        )
      )
      (typcase
        (Atom DEMOTE)
        (TupT)
        (IfPr
          (CmpE
            GtOp
            nat
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "cvtop__"
  (ExpP "numtype_1" (VarT "numtype"))
  (ExpP "numtype_2" (VarT "numtype"))
  (InstD
    (ExpP "numtype_1" (VarT "numtype"))
    (ExpP "numtype_2" (VarT "numtype"))
    (ExpA (VarE "numtype_1"))
    (ExpA (VarE "numtype_2"))
    (VariantT
      (typcase
        (Seq (Atom mk_cvtop___0) Arg Arg Arg)
        (TupT
          (typbind "Inn_1" (VarT "Inn"))
          (typbind "Inn_2" (VarT "Inn"))
          (typbind
            "var_x"
            (VarT
              "cvtop__Inn_1_Inn_2"
              (ExpA (VarE "Inn_1"))
              (ExpA (VarE "Inn_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_1")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1"))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_2")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_cvtop___1) Arg Arg Arg)
        (TupT
          (typbind "Inn_1" (VarT "Inn"))
          (typbind "Fnn_2" (VarT "Fnn"))
          (typbind
            "var_x"
            (VarT
              "cvtop__Inn_1_Fnn_2"
              (ExpA (VarE "Inn_1"))
              (ExpA (VarE "Fnn_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_1")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1"))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_2")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_cvtop___2) Arg Arg Arg)
        (TupT
          (typbind "Fnn_1" (VarT "Fnn"))
          (typbind "Inn_2" (VarT "Inn"))
          (typbind
            "var_x"
            (VarT
              "cvtop__Fnn_1_Inn_2"
              (ExpA (VarE "Fnn_1"))
              (ExpA (VarE "Inn_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_1")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1"))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_2")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2"))
          )
        )
      )
      (typcase
        (Seq (Atom mk_cvtop___3) Arg Arg Arg)
        (TupT
          (typbind "Fnn_1" (VarT "Fnn"))
          (typbind "Fnn_2" (VarT "Fnn"))
          (typbind
            "var_x"
            (VarT
              "cvtop__Fnn_1_Fnn_2"
              (ExpA (VarE "Fnn_1"))
              (ExpA (VarE "Fnn_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_1")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1"))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype_2")
            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_cvtop___0"
  (ExpP "Inn_1" (VarT "Inn"))
  (ExpP "Inn_2" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "cvtop__"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    )
  )
  (IterT
    (VarT "cvtop__Inn_1_Inn_2" (ExpA (VarE "Inn_1")) (ExpA (VarE "Inn_2")))
    Opt
  )
  (DefD
    (ExpP "Inn_1" (VarT "Inn"))
    (ExpP "Inn_2" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT "cvtop__Inn_1_Inn_2" (ExpA (VarE "Inn_1")) (ExpA (VarE "Inn_2")))
    )
    (ExpA (VarE "Inn_1"))
    (ExpA (VarE "Inn_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___0) Arg Arg Arg)
        (TupE (VarE "Inn_1") (VarE "Inn_2") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn_1" (VarT "Inn"))
    (ExpP "Inn_2" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "cvtop__"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
      )
    )
    (ExpA (VarE "Inn_1"))
    (ExpA (VarE "Inn_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_cvtop___1"
  (ExpP "Inn_1" (VarT "Inn"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT
      "cvtop__"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
    )
  )
  (IterT
    (VarT "cvtop__Inn_1_Fnn_2" (ExpA (VarE "Inn_1")) (ExpA (VarE "Fnn_2")))
    Opt
  )
  (DefD
    (ExpP "Inn_1" (VarT "Inn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "cvtop__Inn_1_Fnn_2" (ExpA (VarE "Inn_1")) (ExpA (VarE "Fnn_2")))
    )
    (ExpA (VarE "Inn_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___1) Arg Arg Arg)
        (TupE (VarE "Inn_1") (VarE "Fnn_2") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Inn_1" (VarT "Inn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT
        "cvtop__"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
        (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
      )
    )
    (ExpA (VarE "Inn_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_cvtop___2"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "Inn_2" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "cvtop__"
      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    )
  )
  (IterT
    (VarT "cvtop__Fnn_1_Inn_2" (ExpA (VarE "Fnn_1")) (ExpA (VarE "Inn_2")))
    Opt
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Inn_2" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT "cvtop__Fnn_1_Inn_2" (ExpA (VarE "Fnn_1")) (ExpA (VarE "Inn_2")))
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "Inn_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___2) Arg Arg Arg)
        (TupE (VarE "Fnn_1") (VarE "Inn_2") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Inn_2" (VarT "Inn"))
    (ExpP
      "var_x"
      (VarT
        "cvtop__"
        (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
      )
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "Inn_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_cvtop___3"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (ExpP
    "var_x"
    (VarT
      "cvtop__"
      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
    )
  )
  (IterT
    (VarT "cvtop__Fnn_1_Fnn_2" (ExpA (VarE "Fnn_1")) (ExpA (VarE "Fnn_2")))
    Opt
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT "cvtop__Fnn_1_Fnn_2" (ExpA (VarE "Fnn_1")) (ExpA (VarE "Fnn_2")))
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___3) Arg Arg Arg)
        (TupE (VarE "Fnn_1") (VarE "Fnn_2") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "var_x"
      (VarT
        "cvtop__"
        (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
        (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
      )
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
HintD
(TypD
  "dim"
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
                (BinE
                  OrOp
                  bool
                  (CmpE EqOp bool (VarE "i") (NumE (Nat 1)))
                  (CmpE EqOp bool (VarE "i") (NumE (Nat 2)))
                )
                (CmpE EqOp bool (VarE "i") (NumE (Nat 4)))
              )
              (CmpE EqOp bool (VarE "i") (NumE (Nat 8)))
            )
            (CmpE EqOp bool (VarE "i") (NumE (Nat 16)))
          )
        )
      )
    )
  )
)
HintD
(TypD
  "shape"
  (InstD
    (VariantT
      (typcase
        (Seq Arg (Atom X) Arg)
        (TupT
          (typbind "lanetype" (VarT "lanetype"))
          (typbind "dim" (VarT "dim"))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (BinE
              MulOp
              nat
              (CallE "lsize" (ExpA (VarE "lanetype")))
              (ProjE (UncaseE (VarE "dim") Arg) 0)
            )
            (NumE (Nat 128))
          )
        )
      )
    )
  )
)
HintD
(DecD
  "dim"
  (ExpP "shape" (VarT "shape"))
  (VarT "dim")
  (DefD
    (ExpP "Lnn" (VarT "lanetype"))
    (ExpP "N" nat)
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn") (CaseE Arg (TupE (VarE "N"))))
      )
    )
    (CaseE Arg (TupE (VarE "N")))
  )
)
HintD
(DecD
  "lanetype"
  (ExpP "shape" (VarT "shape"))
  (VarT "lanetype")
  (DefD
    (ExpP "Lnn" (VarT "lanetype"))
    (ExpP "N" nat)
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn") (CaseE Arg (TupE (VarE "N"))))
      )
    )
    (VarE "Lnn")
  )
)
HintD
(DecD
  "unpackshape"
  (ExpP "shape" (VarT "shape"))
  (VarT "numtype")
  (DefD
    (ExpP "Lnn" (VarT "lanetype"))
    (ExpP "N" nat)
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn") (CaseE Arg (TupE (VarE "N"))))
      )
    )
    (CallE "lunpack" (ExpA (VarE "Lnn")))
  )
)
HintD
(TypD
  "ishape"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "shape" (VarT "shape")))
        (ExpP "Jnn" (VarT "Jnn"))
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE "lanetype" (ExpA (VarE "shape")))
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          )
        )
      )
    )
  )
)
HintD
(TypD
  "bshape"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "shape" (VarT "shape")))
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE "lanetype" (ExpA (VarE "shape")))
            (CaseE (Atom I8) (TupE))
          )
        )
      )
    )
  )
)
HintD
(TypD "zero" (InstD (VariantT (typcase (Atom ZERO) (TupT)))))
(TypD
  "half"
  (InstD (VariantT (typcase (Atom LOW) (TupT)) (typcase (Atom HIGH) (TupT))))
)
(TypD "vvunop" (InstD (VariantT (typcase (Atom NOT) (TupT)))))
HintD
(TypD
  "vvbinop"
  (InstD
    (VariantT
      (typcase (Atom AND) (TupT))
      (typcase (Atom ANDNOT) (TupT))
      (typcase (Atom OR) (TupT))
      (typcase (Atom XOR) (TupT))
    )
  )
)
HintD
(TypD "vvternop" (InstD (VariantT (typcase (Atom BITSELECT) (TupT)))))
HintD
(TypD "vvtestop" (InstD (VariantT (typcase (Atom ANY_TRUE) (TupT)))))
HintD
(TypD
  "vunop_Jnn_M"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom ABS) (TupT))
      (typcase (Atom NEG) (TupT))
      (typcase
        (Atom POPCNT)
        (TupT)
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 8))
          )
        )
      )
    )
  )
)
(TypD
  "vunop_Fnn_M"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
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
  "vunop_"
  (ExpP "shape" (VarT "shape"))
  (InstD
    (ExpP "shape" (VarT "shape"))
    (ExpA (VarE "shape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vunop__0) Arg Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vunop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vunop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vunop__0"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vunop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vunop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vunop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vunop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vunop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vunop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vunop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
(TypD
  "vbinop_Jnn_M"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom ADD) (TupT))
      (typcase (Atom SUB) (TupT))
      (typcase
        (Seq (Atom ADD_SAT) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            LeOp
            nat
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 16))
          )
        )
      )
      (typcase
        (Seq (Atom SUB_SAT) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            LeOp
            nat
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 16))
          )
        )
      )
      (typcase
        (Atom MUL)
        (TupT)
        (IfPr
          (CmpE
            GeOp
            nat
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 16))
          )
        )
      )
      (typcase
        (Seq (Atom AVGR) (Atom U))
        (TupT)
        (IfPr
          (CmpE
            LeOp
            nat
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 16))
          )
        )
      )
      (typcase
        (Seq (Atom Q15MULR_SAT) (Atom S))
        (TupT)
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 16))
          )
        )
      )
      (typcase
        (Seq (Atom RELAXED_Q15MULR) (Atom S))
        (TupT)
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 16))
          )
        )
      )
      (typcase
        (Seq (Atom MIN) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            LeOp
            nat
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 32))
          )
        )
      )
      (typcase
        (Seq (Atom MAX) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            LeOp
            nat
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
            (NumE (Nat 32))
          )
        )
      )
    )
  )
)
(TypD
  "vbinop_Fnn_M"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom ADD) (TupT))
      (typcase (Atom SUB) (TupT))
      (typcase (Atom MUL) (TupT))
      (typcase (Atom DIV) (TupT))
      (typcase (Atom MIN) (TupT))
      (typcase (Atom MAX) (TupT))
      (typcase (Atom PMIN) (TupT))
      (typcase (Atom PMAX) (TupT))
      (typcase (Atom RELAXED_MIN) (TupT))
      (typcase (Atom RELAXED_MAX) (TupT))
    )
  )
)
(TypD
  "vbinop_"
  (ExpP "shape" (VarT "shape"))
  (InstD
    (ExpP "shape" (VarT "shape"))
    (ExpA (VarE "shape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vbinop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vbinop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vbinop__0"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vbinop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vbinop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vbinop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vbinop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vbinop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vbinop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vbinop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
(TypD
  "vternop_Jnn_M"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (VariantT (typcase (Atom RELAXED_LANESELECT) (TupT)))
  )
)
(TypD
  "vternop_Fnn_M"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom RELAXED_MADD) (TupT))
      (typcase (Atom RELAXED_NMADD) (TupT))
    )
  )
)
(TypD
  "vternop_"
  (ExpP "shape" (VarT "shape"))
  (InstD
    (ExpP "shape" (VarT "shape"))
    (ExpA (VarE "shape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vternop__0) Arg Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vternop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vternop__1) Arg Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vternop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vternop__0"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vternop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vternop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vternop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vternop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vternop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vternop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vternop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vternop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vternop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vternop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vternop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
(TypD
  "vtestop_Jnn_M"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (VariantT (typcase (Atom ALL_TRUE) (TupT)))
  )
)
(TypD
  "vtestop_"
  (ExpP "shape" (VarT "shape"))
  (InstD
    (ExpP "shape" (VarT "shape"))
    (ExpA (VarE "shape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vtestop__0) Arg Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vtestop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vtestop__0"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vtestop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (VarT "vtestop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vtestop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vtestop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
HintD
(TypD
  "vrelop_Jnn_M"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom EQ) (TupT))
      (typcase (Atom NE) (TupT))
      (typcase
        (Seq (Atom LT) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (BinE
            OrOp
            bool
            (CmpE
              NeOp
              bool
              (CallE
                "lsizenn"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
              )
              (NumE (Nat 64))
            )
            (CmpE EqOp bool (VarE "sx") (CaseE (Atom S) (TupE)))
          )
        )
      )
      (typcase
        (Seq (Atom GT) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (BinE
            OrOp
            bool
            (CmpE
              NeOp
              bool
              (CallE
                "lsizenn"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
              )
              (NumE (Nat 64))
            )
            (CmpE EqOp bool (VarE "sx") (CaseE (Atom S) (TupE)))
          )
        )
      )
      (typcase
        (Seq (Atom LE) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (BinE
            OrOp
            bool
            (CmpE
              NeOp
              bool
              (CallE
                "lsizenn"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
              )
              (NumE (Nat 64))
            )
            (CmpE EqOp bool (VarE "sx") (CaseE (Atom S) (TupE)))
          )
        )
      )
      (typcase
        (Seq (Atom GE) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (BinE
            OrOp
            bool
            (CmpE
              NeOp
              bool
              (CallE
                "lsizenn"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
              )
              (NumE (Nat 64))
            )
            (CmpE EqOp bool (VarE "sx") (CaseE (Atom S) (TupE)))
          )
        )
      )
    )
  )
)
(TypD
  "vrelop_Fnn_M"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
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
  "vrelop_"
  (ExpP "shape" (VarT "shape"))
  (InstD
    (ExpP "shape" (VarT "shape"))
    (ExpA (VarE "shape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vrelop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupT
          (typbind "Fnn" (VarT "Fnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vrelop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vrelop__0"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vrelop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vrelop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vrelop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vrelop__1"
  (ExpP "Fnn" (VarT "Fnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
    )
  )
  (IterT (VarT "vrelop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))) Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vrelop_Fnn_M" (ExpA (VarE "Fnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vrelop_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Fnn"))
    (ExpA (VarE "M"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
(TypD
  "vshiftop_Jnn_M"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom SHL) (TupT))
      (typcase (Seq (Atom SHR) Arg) (TupT (typbind "sx" (VarT "sx"))))
    )
  )
)
(TypD
  "vshiftop_"
  (ExpP "ishape" (VarT "ishape"))
  (InstD
    (ExpP "ishape" (VarT "ishape"))
    (ExpA (VarE "ishape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vshiftop__0) Arg Arg Arg)
        (TupT
          (typbind "Jnn" (VarT "Jnn"))
          (typbind "M" (VarT "M"))
          (typbind
            "var_x"
            (VarT "vshiftop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                    (CaseE Arg (TupE (VarE "M")))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vshiftop__0"
  (ExpP "Jnn" (VarT "Jnn"))
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vshiftop_"
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                (CaseE Arg (TupE (VarE "M")))
              )
            )
          )
        )
      )
    )
  )
  (VarT "vshiftop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M")))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vshiftop_Jnn_M" (ExpA (VarE "Jnn")) (ExpA (VarE "M"))))
    (ExpA (VarE "Jnn"))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vshiftop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
HintD
(TypD
  "vswizzlop_M"
  (ExpP "M" (VarT "M"))
  (InstD
    (ExpP "M" (VarT "M"))
    (ExpA (VarE "M"))
    (VariantT
      (typcase (Atom SWIZZLE) (TupT))
      (typcase (Atom RELAXED_SWIZZLE) (TupT))
    )
  )
)
(TypD
  "vswizzlop_"
  (ExpP "bshape" (VarT "bshape"))
  (InstD
    (ExpP "bshape" (VarT "bshape"))
    (ExpA (VarE "bshape"))
    (VariantT
      (typcase
        (Seq (Atom mk_vswizzlop__0) Arg Arg)
        (TupT
          (typbind "M" (VarT "M"))
          (typbind "var_x" (VarT "vswizzlop_M" (ExpA (VarE "M"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "bshape")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vswizzlop__0"
  (ExpP "M" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vswizzlop_"
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
            )
          )
        )
      )
    )
  )
  (VarT "vswizzlop_M" (ExpA (VarE "M")))
  (DefD
    (ExpP "M" (VarT "M"))
    (ExpP "var_x" (VarT "vswizzlop_M" (ExpA (VarE "M"))))
    (ExpA (VarE "M"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vswizzlop__0) Arg Arg)
        (TupE (VarE "M") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
HintD
(TypD
  "vextunop__Jnn_1_M_1_Jnn_2_M_2"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom EXTADD_PAIRWISE) Arg)
        (TupT (typbind "sx" (VarT "sx")))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              LeOp
              nat
              (NumE (Nat 16))
              (BinE
                MulOp
                nat
                (NumE (Nat 2))
                (CallE
                  "lsizenn1"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                )
              )
            )
            (BinE
              AndOp
              bool
              (CmpE
                EqOp
                bool
                (BinE
                  MulOp
                  nat
                  (NumE (Nat 2))
                  (CallE
                    "lsizenn1"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                  )
                )
                (CallE
                  "lsizenn2"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                )
              )
              (CmpE
                LeOp
                nat
                (CallE
                  "lsizenn2"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                )
                (NumE (Nat 32))
              )
            )
          )
        )
      )
    )
  )
)
(TypD
  "vextunop__"
  (ExpP "ishape_1" (VarT "ishape"))
  (ExpP "ishape_2" (VarT "ishape"))
  (InstD
    (ExpP "ishape_1" (VarT "ishape"))
    (ExpP "ishape_2" (VarT "ishape"))
    (ExpA (VarE "ishape_1"))
    (ExpA (VarE "ishape_2"))
    (VariantT
      (typcase
        (Seq (Atom mk_vextunop___0) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Jnn_1" (VarT "Jnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Jnn_2" (VarT "Jnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vextunop__Jnn_1_M_1_Jnn_2_M_2"
              (ExpA (VarE "Jnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Jnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape_1")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                    (CaseE Arg (TupE (VarE "M_1")))
                  )
                )
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape_2")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                    (CaseE Arg (TupE (VarE "M_2")))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vextunop___0"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vextunop__"
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
      )
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
    )
  )
  (VarT
    "vextunop__Jnn_1_M_1_Jnn_2_M_2"
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vextunop__Jnn_1_M_1_Jnn_2_M_2"
        (ExpA (VarE "Jnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Jnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vextunop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
HintD
(TypD
  "vextbinop__Jnn_1_M_1_Jnn_2_M_2"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom EXTMUL) Arg Arg)
        (TupT (typbind "half" (VarT "half")) (typbind "sx" (VarT "sx")))
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (BinE
                MulOp
                nat
                (NumE (Nat 2))
                (CallE
                  "lsizenn1"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                )
              )
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
            )
            (CmpE
              GeOp
              nat
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
              (NumE (Nat 16))
            )
          )
        )
      )
      (typcase
        (Seq (Atom DOT) (Atom S))
        (TupT)
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (BinE
                MulOp
                nat
                (NumE (Nat 2))
                (CallE
                  "lsizenn1"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                )
              )
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
            )
            (CmpE
              EqOp
              bool
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
              (NumE (Nat 32))
            )
          )
        )
      )
      (typcase
        (Seq (Atom RELAXED_DOT) (Atom S))
        (TupT)
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (BinE
                MulOp
                nat
                (NumE (Nat 2))
                (CallE
                  "lsizenn1"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                )
              )
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
            )
            (CmpE
              EqOp
              bool
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
              (NumE (Nat 16))
            )
          )
        )
      )
    )
  )
)
(TypD
  "vextbinop__"
  (ExpP "ishape_1" (VarT "ishape"))
  (ExpP "ishape_2" (VarT "ishape"))
  (InstD
    (ExpP "ishape_1" (VarT "ishape"))
    (ExpP "ishape_2" (VarT "ishape"))
    (ExpA (VarE "ishape_1"))
    (ExpA (VarE "ishape_2"))
    (VariantT
      (typcase
        (Seq (Atom mk_vextbinop___0) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Jnn_1" (VarT "Jnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Jnn_2" (VarT "Jnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vextbinop__Jnn_1_M_1_Jnn_2_M_2"
              (ExpA (VarE "Jnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Jnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape_1")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                    (CaseE Arg (TupE (VarE "M_1")))
                  )
                )
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape_2")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                    (CaseE Arg (TupE (VarE "M_2")))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vextbinop___0"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vextbinop__"
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
      )
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
    )
  )
  (VarT
    "vextbinop__Jnn_1_M_1_Jnn_2_M_2"
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vextbinop__Jnn_1_M_1_Jnn_2_M_2"
        (ExpA (VarE "Jnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Jnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vextbinop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
HintD
(TypD
  "vextternop__Jnn_1_M_1_Jnn_2_M_2"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom RELAXED_DOT_ADD) (Atom S))
        (TupT)
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (BinE
                MulOp
                nat
                (NumE (Nat 4))
                (CallE
                  "lsizenn1"
                  (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                )
              )
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
            )
            (CmpE
              EqOp
              bool
              (CallE
                "lsizenn2"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
              )
              (NumE (Nat 32))
            )
          )
        )
      )
    )
  )
)
(TypD
  "vextternop__"
  (ExpP "ishape_1" (VarT "ishape"))
  (ExpP "ishape_2" (VarT "ishape"))
  (InstD
    (ExpP "ishape_1" (VarT "ishape"))
    (ExpP "ishape_2" (VarT "ishape"))
    (ExpA (VarE "ishape_1"))
    (ExpA (VarE "ishape_2"))
    (VariantT
      (typcase
        (Seq (Atom mk_vextternop___0) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Jnn_1" (VarT "Jnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Jnn_2" (VarT "Jnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vextternop__Jnn_1_M_1_Jnn_2_M_2"
              (ExpA (VarE "Jnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Jnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape_1")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                    (CaseE Arg (TupE (VarE "M_1")))
                  )
                )
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "ishape_2")
            (CaseE
              Arg
              (TupE
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE
                    (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                    (CaseE Arg (TupE (VarE "M_2")))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vextternop___0"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vextternop__"
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
      )
      (ExpA
        (CaseE
          Arg
          (TupE
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
    )
  )
  (VarT
    "vextternop__Jnn_1_M_1_Jnn_2_M_2"
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vextternop__Jnn_1_M_1_Jnn_2_M_2"
        (ExpA (VarE "Jnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Jnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vextternop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
HintD
(TypD
  "vcvtop__Jnn_1_M_1_Jnn_2_M_2"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom EXTEND) Arg Arg)
        (TupT (typbind "half" (VarT "half")) (typbind "sx" (VarT "sx")))
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "lsizenn2"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
            )
            (BinE
              MulOp
              nat
              (NumE (Nat 2))
              (CallE
                "lsizenn1"
                (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
              )
            )
          )
        )
      )
    )
  )
)
(TypD
  "vcvtop__Jnn_1_M_1_Fnn_2_M_2"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom CONVERT) Arg Arg)
        (TupT
          (typbind "half?" (IterT (VarT "half") Opt))
          (typbind "sx" (VarT "sx"))
        )
        (IfPr
          (BinE
            OrOp
            bool
            (BinE
              AndOp
              bool
              (BinE
                AndOp
                bool
                (CmpE
                  EqOp
                  bool
                  (CallE
                    "sizenn2"
                    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
                  )
                  (CallE
                    "lsizenn1"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                  )
                )
                (CmpE
                  EqOp
                  bool
                  (CallE
                    "lsizenn1"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                  )
                  (NumE (Nat 32))
                )
              )
              (CmpE
                EqOp
                bool
                (IterE (VarE "half") Opt (iterexp "half" (VarE "half?")))
                (OptE)
              )
            )
            (BinE
              AndOp
              bool
              (CmpE
                EqOp
                bool
                (CallE
                  "sizenn2"
                  (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
                )
                (BinE
                  MulOp
                  nat
                  (NumE (Nat 2))
                  (CallE
                    "lsizenn1"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
                  )
                )
              )
              (CmpE
                EqOp
                bool
                (IterE (VarE "half") Opt (iterexp "half" (VarE "half?")))
                (OptE (CaseE (Atom LOW) (TupE)))
              )
            )
          )
        )
      )
    )
  )
)
(TypD
  "vcvtop__Fnn_1_M_1_Jnn_2_M_2"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom TRUNC_SAT) Arg Arg)
        (TupT
          (typbind "sx" (VarT "sx"))
          (typbind "zero?" (IterT (VarT "zero") Opt))
        )
        (IfPr
          (BinE
            OrOp
            bool
            (BinE
              AndOp
              bool
              (BinE
                AndOp
                bool
                (CmpE
                  EqOp
                  bool
                  (CallE
                    "sizenn1"
                    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
                  )
                  (CallE
                    "lsizenn2"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                  )
                )
                (CmpE
                  EqOp
                  bool
                  (CallE
                    "lsizenn2"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                  )
                  (NumE (Nat 32))
                )
              )
              (CmpE
                EqOp
                bool
                (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
                (OptE)
              )
            )
            (BinE
              AndOp
              bool
              (CmpE
                EqOp
                bool
                (CallE
                  "sizenn1"
                  (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
                )
                (BinE
                  MulOp
                  nat
                  (NumE (Nat 2))
                  (CallE
                    "lsizenn2"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                  )
                )
              )
              (CmpE
                EqOp
                bool
                (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
                (OptE (CaseE (Atom ZERO) (TupE)))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom RELAXED_TRUNC) Arg Arg)
        (TupT
          (typbind "sx" (VarT "sx"))
          (typbind "zero?" (IterT (VarT "zero") Opt))
        )
        (IfPr
          (BinE
            OrOp
            bool
            (BinE
              AndOp
              bool
              (BinE
                AndOp
                bool
                (CmpE
                  EqOp
                  bool
                  (CallE
                    "sizenn1"
                    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
                  )
                  (CallE
                    "lsizenn2"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                  )
                )
                (CmpE
                  EqOp
                  bool
                  (CallE
                    "lsizenn2"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                  )
                  (NumE (Nat 32))
                )
              )
              (CmpE
                EqOp
                bool
                (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
                (OptE)
              )
            )
            (BinE
              AndOp
              bool
              (CmpE
                EqOp
                bool
                (CallE
                  "sizenn1"
                  (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
                )
                (BinE
                  MulOp
                  nat
                  (NumE (Nat 2))
                  (CallE
                    "lsizenn2"
                    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
                  )
                )
              )
              (CmpE
                EqOp
                bool
                (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
                (OptE (CaseE (Atom ZERO) (TupE)))
              )
            )
          )
        )
      )
    )
  )
)
(TypD
  "vcvtop__Fnn_1_M_1_Fnn_2_M_2"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (ExpP "M_2" (VarT "M"))
  (InstD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "M_2"))
    (VariantT
      (typcase
        (Seq (Atom DEMOTE) Arg)
        (TupT (typbind "zero" (VarT "zero")))
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
            )
            (BinE
              MulOp
              nat
              (NumE (Nat 2))
              (CallE
                "sizenn2"
                (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom PROMOTE) (Atom LOW))
        (TupT)
        (IfPr
          (CmpE
            EqOp
            bool
            (BinE
              MulOp
              nat
              (NumE (Nat 2))
              (CallE
                "sizenn1"
                (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
              )
            )
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "vcvtop__"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (InstD
    (ExpP "shape_1" (VarT "shape"))
    (ExpP "shape_2" (VarT "shape"))
    (ExpA (VarE "shape_1"))
    (ExpA (VarE "shape_2"))
    (VariantT
      (typcase
        (Seq (Atom mk_vcvtop___0) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Jnn_1" (VarT "Jnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Jnn_2" (VarT "Jnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vcvtop__Jnn_1_M_1_Jnn_2_M_2"
              (ExpA (VarE "Jnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Jnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_1")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_2")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vcvtop___1) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Jnn_1" (VarT "Jnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Fnn_2" (VarT "Fnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vcvtop__Jnn_1_M_1_Fnn_2_M_2"
              (ExpA (VarE "Jnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Fnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_1")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_2")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Fnn_1" (VarT "Fnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Jnn_2" (VarT "Jnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vcvtop__Fnn_1_M_1_Jnn_2_M_2"
              (ExpA (VarE "Fnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Jnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_1")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_2")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
      (typcase
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupT
          (typbind "Fnn_1" (VarT "Fnn"))
          (typbind "M_1" (VarT "M"))
          (typbind "Fnn_2" (VarT "Fnn"))
          (typbind "M_2" (VarT "M"))
          (typbind
            "var_x"
            (VarT
              "vcvtop__Fnn_1_M_1_Fnn_2_M_2"
              (ExpA (VarE "Fnn_1"))
              (ExpA (VarE "M_1"))
              (ExpA (VarE "Fnn_2"))
              (ExpA (VarE "M_2"))
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_1")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "shape_2")
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "proj_vcvtop___0"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vcvtop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
    )
  )
  (IterT
    (VarT
      "vcvtop__Jnn_1_M_1_Jnn_2_M_2"
      (ExpA (VarE "Jnn_1"))
      (ExpA (VarE "M_1"))
      (ExpA (VarE "Jnn_2"))
      (ExpA (VarE "M_2"))
    )
    Opt
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__Jnn_1_M_1_Jnn_2_M_2"
        (ExpA (VarE "Jnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Jnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vcvtop___1"
  (ExpP "Jnn_1" (VarT "Jnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vcvtop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
    )
  )
  (IterT
    (VarT
      "vcvtop__Jnn_1_M_1_Fnn_2_M_2"
      (ExpA (VarE "Jnn_1"))
      (ExpA (VarE "M_1"))
      (ExpA (VarE "Fnn_2"))
      (ExpA (VarE "M_2"))
    )
    Opt
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__Jnn_1_M_1_Fnn_2_M_2"
        (ExpA (VarE "Jnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Fnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___1) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Jnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vcvtop___2"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Jnn_2" (VarT "Jnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vcvtop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
    )
  )
  (IterT
    (VarT
      "vcvtop__Fnn_1_M_1_Jnn_2_M_2"
      (ExpA (VarE "Fnn_1"))
      (ExpA (VarE "M_1"))
      (ExpA (VarE "Jnn_2"))
      (ExpA (VarE "M_2"))
    )
    Opt
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__Fnn_1_M_1_Jnn_2_M_2"
        (ExpA (VarE "Fnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Jnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Jnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
(DecD
  "proj_vcvtop___3"
  (ExpP "Fnn_1" (VarT "Fnn"))
  (ExpP "M_1" (VarT "M"))
  (ExpP "Fnn_2" (VarT "Fnn"))
  (ExpP "M_2" (VarT "M"))
  (ExpP
    "var_x"
    (VarT
      "vcvtop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
    )
  )
  (IterT
    (VarT
      "vcvtop__Fnn_1_M_1_Fnn_2_M_2"
      (ExpA (VarE "Fnn_1"))
      (ExpA (VarE "M_1"))
      (ExpA (VarE "Fnn_2"))
      (ExpA (VarE "M_2"))
    )
    Opt
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__Fnn_1_M_1_Fnn_2_M_2"
        (ExpA (VarE "Fnn_1"))
        (ExpA (VarE "M_1"))
        (ExpA (VarE "Fnn_2"))
        (ExpA (VarE "M_2"))
      )
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (VarE "var_x")
        )
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" (VarT "M"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" (VarT "M"))
    (ExpP
      "var_x"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA (VarE "Fnn_1"))
    (ExpA (VarE "M_1"))
    (ExpA (VarE "Fnn_2"))
    (ExpA (VarE "M_2"))
    (ExpA (VarE "var_x"))
    (OptE)
  )
)
HintD
HintD
HintD
HintD
HintD
HintD
(TypD
  "memarg"
  (InstD
    (StructT
      (typfield (Atom ALIGN) (VarT "u32"))
      (typfield (Atom OFFSET) (VarT "u64"))
    )
  )
)
HintD
(TypD
  "loadop_Inn"
  (ExpP "Inn" (VarT "Inn"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (VarE "Inn"))
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
              "sizenn"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "loadop_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "loadop_Inn" (ExpA (VarE "Inn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_loadop__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "loadop_"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    )
  )
  (VarT "loadop_Inn" (ExpA (VarE "Inn")))
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn" (ExpA (VarE "Inn"))))
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
(TypD
  "storeop_Inn"
  (ExpP "Inn" (VarT "Inn"))
  (InstD
    (ExpP "Inn" (VarT "Inn"))
    (ExpA (VarE "Inn"))
    (VariantT
      (typcase
        Arg
        (TupT (typbind "sz" (VarT "sz")))
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (UncaseE (VarE "sz") Arg) 0)
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
            )
          )
        )
      )
    )
  )
)
(TypD
  "storeop_"
  (ExpP "numtype" (VarT "numtype"))
  (InstD
    (ExpP "numtype" (VarT "numtype"))
    (ExpA (VarE "numtype"))
    (VariantT
      (typcase
        (Seq (Atom mk_storeop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "storeop_Inn" (ExpA (VarE "Inn"))))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (VarE "numtype")
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          )
        )
      )
    )
  )
)
(DecD
  "proj_storeop__0"
  (ExpP "Inn" (VarT "Inn"))
  (ExpP
    "var_x"
    (VarT
      "storeop_"
      (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    )
  )
  (VarT "storeop_Inn" (ExpA (VarE "Inn")))
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "storeop_Inn" (ExpA (VarE "Inn"))))
    (ExpA (VarE "Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_storeop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (VarE "var_x")
  )
)
HintD
HintD
(TypD
  "vloadop_"
  (ExpP "vectype" (VarT "vectype"))
  (InstD
    (ExpP "vectype" (VarT "vectype"))
    (ExpA (VarE "vectype"))
    (VariantT
      (typcase
        (Seq (Atom SHAPE) Arg (Atom X) Arg (Atom _) Arg)
        (TupT
          (typbind "sz" (VarT "sz"))
          (typbind "M" (VarT "M"))
          (typbind "sx" (VarT "sx"))
        )
        (IfPr
          (CmpE
            EqOp
            bool
            (CvtE
              nat
              rat
              (BinE MulOp nat (ProjE (UncaseE (VarE "sz") Arg) 0) (VarE "M"))
            )
            (BinE
              DivOp
              rat
              (CvtE nat rat (CallE "vsize" (ExpA (VarE "vectype"))))
              (CvtE nat rat (NumE (Nat 2)))
            )
          )
        )
      )
      (typcase (Seq (Atom SPLAT) Arg) (TupT (typbind "sz" (VarT "sz"))))
      (typcase
        (Seq (Atom ZERO) Arg)
        (TupT (typbind "sz" (VarT "sz")))
        (IfPr
          (CmpE GeOp nat (ProjE (UncaseE (VarE "sz") Arg) 0) (NumE (Nat 32)))
        )
      )
    )
  )
)
HintD
(TypD
  "blocktype"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom _RESULT) Arg)
        (TupT (typbind "valtype?" (IterT (VarT "valtype") Opt)))
      )
      (typcase
        (Seq (Atom _IDX) Arg)
        (TupT (typbind "typeidx" (VarT "typeidx")))
      )
    )
  )
)
HintD
(TypD "addr" (InstD (AliasT nat)))
(TypD "arrayaddr" (InstD (AliasT (VarT "addr"))))
(TypD
  "catch"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom CATCH) Arg Arg)
        (TupT
          (typbind "tagidx" (VarT "tagidx"))
          (typbind "labelidx" (VarT "labelidx"))
        )
      )
      (typcase
        (Seq (Atom CATCH_REF) Arg Arg)
        (TupT
          (typbind "tagidx" (VarT "tagidx"))
          (typbind "labelidx" (VarT "labelidx"))
        )
      )
      (typcase
        (Seq (Atom CATCH_ALL) Arg)
        (TupT (typbind "labelidx" (VarT "labelidx")))
      )
      (typcase
        (Seq (Atom CATCH_ALL_REF) Arg)
        (TupT (typbind "labelidx" (VarT "labelidx")))
      )
    )
  )
)
(TypD "exnaddr" (InstD (AliasT (VarT "addr"))))
(TypD "dataaddr" (InstD (AliasT (VarT "addr"))))
(TypD "elemaddr" (InstD (AliasT (VarT "addr"))))
(TypD "funcaddr" (InstD (AliasT (VarT "addr"))))
(TypD "globaladdr" (InstD (AliasT (VarT "addr"))))
(TypD "memaddr" (InstD (AliasT (VarT "addr"))))
(TypD "tableaddr" (InstD (AliasT (VarT "addr"))))
(TypD "tagaddr" (InstD (AliasT (VarT "addr"))))
(TypD
  "externaddr"
  (InstD
    (VariantT
      (typcase (Seq (Atom TAG) Arg) (TupT (typbind "tagaddr" (VarT "tagaddr"))))
      (typcase
        (Seq (Atom GLOBAL) Arg)
        (TupT (typbind "globaladdr" (VarT "globaladdr")))
      )
      (typcase (Seq (Atom MEM) Arg) (TupT (typbind "memaddr" (VarT "memaddr"))))
      (typcase
        (Seq (Atom TABLE) Arg)
        (TupT (typbind "tableaddr" (VarT "tableaddr")))
      )
      (typcase
        (Seq (Atom FUNC) Arg)
        (TupT (typbind "funcaddr" (VarT "funcaddr")))
      )
    )
  )
)
(TypD
  "exportinst"
  (InstD
    (StructT
      (typfield (Atom NAME) (VarT "name"))
      (typfield (Atom ADDR) (VarT "externaddr"))
    )
  )
)
(TypD
  "moduleinst"
  (InstD
    (StructT
      (typfield (Atom TYPES) (IterT (VarT "deftype") List))
      (typfield (Atom TAGS) (IterT (VarT "tagaddr") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globaladdr") List))
      (typfield (Atom MEMS) (IterT (VarT "memaddr") List))
      (typfield (Atom TABLES) (IterT (VarT "tableaddr") List))
      (typfield (Atom FUNCS) (IterT (VarT "funcaddr") List))
      (typfield (Atom DATAS) (IterT (VarT "dataaddr") List))
      (typfield (Atom ELEMS) (IterT (VarT "elemaddr") List))
      (typfield (Atom EXPORTS) (IterT (VarT "exportinst") List))
    )
  )
)
(TypD "hostaddr" (InstD (AliasT (VarT "addr"))))
(TypD "structaddr" (InstD (AliasT (VarT "addr"))))
(RecD
  (TypD
    "ref"
    (InstD
      (VariantT
        (typcase
          (Seq (Atom REF.I31_NUM) Arg)
          (TupT (typbind "u31" (VarT "u31")))
        )
        (typcase (Atom REF.NULL_ADDR) (TupT))
        (typcase
          (Seq (Atom REF.STRUCT_ADDR) Arg)
          (TupT (typbind "structaddr" (VarT "structaddr")))
        )
        (typcase
          (Seq (Atom REF.ARRAY_ADDR) Arg)
          (TupT (typbind "arrayaddr" (VarT "arrayaddr")))
        )
        (typcase
          (Seq (Atom REF.FUNC_ADDR) Arg)
          (TupT (typbind "funcaddr" (VarT "funcaddr")))
        )
        (typcase
          (Seq (Atom REF.EXN_ADDR) Arg)
          (TupT (typbind "exnaddr" (VarT "exnaddr")))
        )
        (typcase
          (Seq (Atom REF.HOST_ADDR) Arg)
          (TupT (typbind "hostaddr" (VarT "hostaddr")))
        )
        (typcase
          (Seq (Atom REF.EXTERN) Arg)
          (TupT (typbind "ref" (VarT "ref")))
        )
      )
    )
  )
)
(TypD
  "val"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom CONST) Arg Arg)
        (TupT
          (typbind "numtype" (VarT "numtype"))
          (typbind "_" (VarT "num_" (ExpA (VarE "numtype"))))
        )
      )
      (typcase
        (Seq (Atom VCONST) Arg Arg)
        (TupT
          (typbind "vectype" (VarT "vectype"))
          (typbind "_" (VarT "vec_" (ExpA (VarE "vectype"))))
        )
      )
      (typcase (Seq (Atom REF.I31_NUM) Arg) (TupT (typbind "u31" (VarT "u31"))))
      (typcase (Atom REF.NULL_ADDR) (TupT))
      (typcase
        (Seq (Atom REF.STRUCT_ADDR) Arg)
        (TupT (typbind "structaddr" (VarT "structaddr")))
      )
      (typcase
        (Seq (Atom REF.ARRAY_ADDR) Arg)
        (TupT (typbind "arrayaddr" (VarT "arrayaddr")))
      )
      (typcase
        (Seq (Atom REF.FUNC_ADDR) Arg)
        (TupT (typbind "funcaddr" (VarT "funcaddr")))
      )
      (typcase
        (Seq (Atom REF.EXN_ADDR) Arg)
        (TupT (typbind "exnaddr" (VarT "exnaddr")))
      )
      (typcase
        (Seq (Atom REF.HOST_ADDR) Arg)
        (TupT (typbind "hostaddr" (VarT "hostaddr")))
      )
      (typcase (Seq (Atom REF.EXTERN) Arg) (TupT (typbind "ref" (VarT "ref"))))
    )
  )
)
(TypD
  "frame"
  (InstD
    (StructT
      (typfield (Atom LOCALS) (IterT (IterT (VarT "val") Opt) List))
      (typfield (Atom MODULE) (VarT "moduleinst"))
    )
  )
)
(RecD
  (TypD
    "instr"
    (InstD
      (VariantT
        (typcase (Atom NOP) (TupT))
        (typcase (Atom UNREACHABLE) (TupT))
        (typcase (Atom DROP) (TupT))
        (typcase
          (Seq (Atom SELECT) Arg)
          (TupT (typbind "valtype*?" (IterT (IterT (VarT "valtype") List) Opt)))
        )
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
          (Seq (Atom BR_ON_NULL) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_ON_NON_NULL) Arg)
          (TupT (typbind "labelidx" (VarT "labelidx")))
        )
        (typcase
          (Seq (Atom BR_ON_CAST) Arg Arg Arg)
          (TupT
            (typbind "labelidx" (VarT "labelidx"))
            (typbind "reftype" (VarT "reftype"))
            (typbind "reftype" (VarT "reftype"))
          )
        )
        (typcase
          (Seq (Atom BR_ON_CAST_FAIL) Arg Arg Arg)
          (TupT
            (typbind "labelidx" (VarT "labelidx"))
            (typbind "reftype" (VarT "reftype"))
            (typbind "reftype" (VarT "reftype"))
          )
        )
        (typcase
          (Seq (Atom CALL) Arg)
          (TupT (typbind "funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom CALL_REF) Arg)
          (TupT (typbind "typeuse" (VarT "typeuse")))
        )
        (typcase
          (Seq (Atom CALL_INDIRECT) Arg Arg)
          (TupT
            (typbind "tableidx" (VarT "tableidx"))
            (typbind "typeuse" (VarT "typeuse"))
          )
        )
        (typcase (Atom RETURN) (TupT))
        (typcase
          (Seq (Atom RETURN_CALL) Arg)
          (TupT (typbind "funcidx" (VarT "funcidx")))
        )
        (typcase
          (Seq (Atom RETURN_CALL_REF) Arg)
          (TupT (typbind "typeuse" (VarT "typeuse")))
        )
        (typcase
          (Seq (Atom RETURN_CALL_INDIRECT) Arg Arg)
          (TupT
            (typbind "tableidx" (VarT "tableidx"))
            (typbind "typeuse" (VarT "typeuse"))
          )
        )
        (typcase
          (Seq (Atom THROW) Arg)
          (TupT (typbind "tagidx" (VarT "tagidx")))
        )
        (typcase (Atom THROW_REF) (TupT))
        (typcase
          (Seq (Atom TRY_TABLE) Arg Arg Arg)
          (TupT
            (typbind "blocktype" (VarT "blocktype"))
            (typbind "_" (VarT "list" (TypA (VarT "catch"))))
            (typbind "instr*" (IterT (VarT "instr") List))
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
          (Seq (Atom TABLE.GET) Arg)
          (TupT (typbind "tableidx" (VarT "tableidx")))
        )
        (typcase
          (Seq (Atom TABLE.SET) Arg)
          (TupT (typbind "tableidx" (VarT "tableidx")))
        )
        (typcase
          (Seq (Atom TABLE.SIZE) Arg)
          (TupT (typbind "tableidx" (VarT "tableidx")))
        )
        (typcase
          (Seq (Atom TABLE.GROW) Arg)
          (TupT (typbind "tableidx" (VarT "tableidx")))
        )
        (typcase
          (Seq (Atom TABLE.FILL) Arg)
          (TupT (typbind "tableidx" (VarT "tableidx")))
        )
        (typcase
          (Seq (Atom TABLE.COPY) Arg Arg)
          (TupT
            (typbind "tableidx" (VarT "tableidx"))
            (typbind "tableidx" (VarT "tableidx"))
          )
        )
        (typcase
          (Seq (Atom TABLE.INIT) Arg Arg)
          (TupT
            (typbind "tableidx" (VarT "tableidx"))
            (typbind "elemidx" (VarT "elemidx"))
          )
        )
        (typcase
          (Seq (Atom ELEM.DROP) Arg)
          (TupT (typbind "elemidx" (VarT "elemidx")))
        )
        (typcase
          (Seq (Atom LOAD) Arg Arg Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (IterT (VarT "loadop_" (ExpA (VarE "numtype"))) Opt))
            (typbind "memidx" (VarT "memidx"))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom STORE) Arg Arg Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (IterT (VarT "storeop_" (ExpA (VarE "numtype"))) Opt))
            (typbind "memidx" (VarT "memidx"))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom VLOAD) Arg Arg Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "_" (IterT (VarT "vloadop_" (ExpA (VarE "vectype"))) Opt))
            (typbind "memidx" (VarT "memidx"))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom VLOAD_LANE) Arg Arg Arg Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "sz" (VarT "sz"))
            (typbind "memidx" (VarT "memidx"))
            (typbind "memarg" (VarT "memarg"))
            (typbind "laneidx" (VarT "laneidx"))
          )
        )
        (typcase
          (Seq (Atom VSTORE) Arg Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "memidx" (VarT "memidx"))
            (typbind "memarg" (VarT "memarg"))
          )
        )
        (typcase
          (Seq (Atom VSTORE_LANE) Arg Arg Arg Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "sz" (VarT "sz"))
            (typbind "memidx" (VarT "memidx"))
            (typbind "memarg" (VarT "memarg"))
            (typbind "laneidx" (VarT "laneidx"))
          )
        )
        (typcase
          (Seq (Atom MEMORY.SIZE) Arg)
          (TupT (typbind "memidx" (VarT "memidx")))
        )
        (typcase
          (Seq (Atom MEMORY.GROW) Arg)
          (TupT (typbind "memidx" (VarT "memidx")))
        )
        (typcase
          (Seq (Atom MEMORY.FILL) Arg)
          (TupT (typbind "memidx" (VarT "memidx")))
        )
        (typcase
          (Seq (Atom MEMORY.COPY) Arg Arg)
          (TupT
            (typbind "memidx" (VarT "memidx"))
            (typbind "memidx" (VarT "memidx"))
          )
        )
        (typcase
          (Seq (Atom MEMORY.INIT) Arg Arg)
          (TupT
            (typbind "memidx" (VarT "memidx"))
            (typbind "dataidx" (VarT "dataidx"))
          )
        )
        (typcase
          (Seq (Atom DATA.DROP) Arg)
          (TupT (typbind "dataidx" (VarT "dataidx")))
        )
        (typcase
          (Seq (Atom REF.NULL) Arg)
          (TupT (typbind "heaptype" (VarT "heaptype")))
        )
        (typcase (Atom REF.IS_NULL) (TupT))
        (typcase (Atom REF.AS_NON_NULL) (TupT))
        (typcase (Atom REF.EQ) (TupT))
        (typcase
          (Seq (Atom REF.TEST) Arg)
          (TupT (typbind "reftype" (VarT "reftype")))
        )
        (typcase
          (Seq (Atom REF.CAST) Arg)
          (TupT (typbind "reftype" (VarT "reftype")))
        )
        (typcase
          (Seq (Atom REF.FUNC) Arg)
          (TupT (typbind "funcidx" (VarT "funcidx")))
        )
        (typcase (Atom REF.I31) (TupT))
        (typcase (Seq (Atom I31.GET) Arg) (TupT (typbind "sx" (VarT "sx"))))
        (typcase
          (Seq (Atom STRUCT.NEW) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom STRUCT.NEW_DEFAULT) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom STRUCT.GET) Arg Arg Arg)
          (TupT
            (typbind "sx?" (IterT (VarT "sx") Opt))
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "fieldidx" (VarT "fieldidx"))
          )
        )
        (typcase
          (Seq (Atom STRUCT.SET) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "fieldidx" (VarT "fieldidx"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.NEW) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom ARRAY.NEW_DEFAULT) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom ARRAY.NEW_FIXED) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "u32" (VarT "u32"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.NEW_DATA) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "dataidx" (VarT "dataidx"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.NEW_ELEM) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "elemidx" (VarT "elemidx"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.GET) Arg Arg)
          (TupT
            (typbind "sx?" (IterT (VarT "sx") Opt))
            (typbind "typeidx" (VarT "typeidx"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.SET) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase (Atom ARRAY.LEN) (TupT))
        (typcase
          (Seq (Atom ARRAY.FILL) Arg)
          (TupT (typbind "typeidx" (VarT "typeidx")))
        )
        (typcase
          (Seq (Atom ARRAY.COPY) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "typeidx" (VarT "typeidx"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.INIT_DATA) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "dataidx" (VarT "dataidx"))
          )
        )
        (typcase
          (Seq (Atom ARRAY.INIT_ELEM) Arg Arg)
          (TupT
            (typbind "typeidx" (VarT "typeidx"))
            (typbind "elemidx" (VarT "elemidx"))
          )
        )
        (typcase (Atom EXTERN.CONVERT_ANY) (TupT))
        (typcase (Atom ANY.CONVERT_EXTERN) (TupT))
        (typcase
          (Seq (Atom CONST) Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (VarT "num_" (ExpA (VarE "numtype"))))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (VarT "unop_" (ExpA (VarE "numtype"))))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (VarT "binop_" (ExpA (VarE "numtype"))))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (VarT "testop_" (ExpA (VarE "numtype"))))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "numtype" (VarT "numtype"))
            (typbind "_" (VarT "relop_" (ExpA (VarE "numtype"))))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "numtype_1" (VarT "numtype"))
            (typbind "numtype_2" (VarT "numtype"))
            (typbind
              "_"
              (VarT
                "cvtop__"
                (ExpA (VarE "numtype_2"))
                (ExpA (VarE "numtype_1"))
              )
            )
          )
        )
        (typcase
          (Seq (Atom VCONST) Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "_" (VarT "vec_" (ExpA (VarE "vectype"))))
          )
        )
        (typcase
          (Seq (Atom VVUNOP) Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "vvunop" (VarT "vvunop"))
          )
        )
        (typcase
          (Seq (Atom VVBINOP) Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "vvbinop" (VarT "vvbinop"))
          )
        )
        (typcase
          (Seq (Atom VVTERNOP) Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "vvternop" (VarT "vvternop"))
          )
        )
        (typcase
          (Seq (Atom VVTESTOP) Arg Arg)
          (TupT
            (typbind "vectype" (VarT "vectype"))
            (typbind "vvtestop" (VarT "vvtestop"))
          )
        )
        (typcase
          (Seq (Atom VUNOP) Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "_" (VarT "vunop_" (ExpA (VarE "shape"))))
          )
        )
        (typcase
          (Seq (Atom VBINOP) Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "_" (VarT "vbinop_" (ExpA (VarE "shape"))))
          )
        )
        (typcase
          (Seq (Atom VTERNOP) Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "_" (VarT "vternop_" (ExpA (VarE "shape"))))
          )
        )
        (typcase
          (Seq (Atom VTESTOP) Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "_" (VarT "vtestop_" (ExpA (VarE "shape"))))
          )
        )
        (typcase
          (Seq (Atom VRELOP) Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "_" (VarT "vrelop_" (ExpA (VarE "shape"))))
          )
        )
        (typcase
          (Seq (Atom VSHIFTOP) Arg Arg)
          (TupT
            (typbind "ishape" (VarT "ishape"))
            (typbind "_" (VarT "vshiftop_" (ExpA (VarE "ishape"))))
          )
        )
        (typcase
          (Seq (Atom VBITMASK) Arg)
          (TupT (typbind "ishape" (VarT "ishape")))
        )
        (typcase
          (Seq (Atom VSWIZZLOP) Arg Arg)
          (TupT
            (typbind "bshape" (VarT "bshape"))
            (typbind "_" (VarT "vswizzlop_" (ExpA (VarE "bshape"))))
          )
        )
        (typcase
          (Seq (Atom VSHUFFLE) Arg Arg)
          (TupT
            (typbind "bshape" (VarT "bshape"))
            (typbind "laneidx*" (IterT (VarT "laneidx") List))
          )
          (IfPr
            (CmpE
              EqOp
              bool
              (CaseE
                Arg
                (TupE
                  (LenE
                    (IterE
                      (VarE "laneidx")
                      List
                      (iterexp "laneidx" (VarE "laneidx*"))
                    )
                  )
                )
              )
              (CallE "dim" (ExpA (ProjE (UncaseE (VarE "bshape") Arg) 0)))
            )
          )
        )
        (typcase
          (Seq (Atom VEXTUNOP) Arg Arg Arg)
          (TupT
            (typbind "ishape_1" (VarT "ishape"))
            (typbind "ishape_2" (VarT "ishape"))
            (typbind
              "_"
              (VarT
                "vextunop__"
                (ExpA (VarE "ishape_2"))
                (ExpA (VarE "ishape_1"))
              )
            )
          )
        )
        (typcase
          (Seq (Atom VEXTBINOP) Arg Arg Arg)
          (TupT
            (typbind "ishape_1" (VarT "ishape"))
            (typbind "ishape_2" (VarT "ishape"))
            (typbind
              "_"
              (VarT
                "vextbinop__"
                (ExpA (VarE "ishape_2"))
                (ExpA (VarE "ishape_1"))
              )
            )
          )
        )
        (typcase
          (Seq (Atom VEXTTERNOP) Arg Arg Arg)
          (TupT
            (typbind "ishape_1" (VarT "ishape"))
            (typbind "ishape_2" (VarT "ishape"))
            (typbind
              "_"
              (VarT
                "vextternop__"
                (ExpA (VarE "ishape_2"))
                (ExpA (VarE "ishape_1"))
              )
            )
          )
        )
        (typcase
          (Seq (Atom VNARROW) Arg Arg Arg)
          (TupT
            (typbind "ishape_1" (VarT "ishape"))
            (typbind "ishape_2" (VarT "ishape"))
            (typbind "sx" (VarT "sx"))
          )
          (IfPr
            (BinE
              AndOp
              bool
              (CmpE
                EqOp
                bool
                (CallE
                  "lsize"
                  (ExpA
                    (CallE
                      "lanetype"
                      (ExpA (ProjE (UncaseE (VarE "ishape_2") Arg) 0))
                    )
                  )
                )
                (BinE
                  MulOp
                  nat
                  (NumE (Nat 2))
                  (CallE
                    "lsize"
                    (ExpA
                      (CallE
                        "lanetype"
                        (ExpA (ProjE (UncaseE (VarE "ishape_1") Arg) 0))
                      )
                    )
                  )
                )
              )
              (CmpE
                LeOp
                nat
                (BinE
                  MulOp
                  nat
                  (NumE (Nat 2))
                  (CallE
                    "lsize"
                    (ExpA
                      (CallE
                        "lanetype"
                        (ExpA (ProjE (UncaseE (VarE "ishape_1") Arg) 0))
                      )
                    )
                  )
                )
                (NumE (Nat 32))
              )
            )
          )
        )
        (typcase
          (Seq (Atom VCVTOP) Arg Arg Arg)
          (TupT
            (typbind "shape_1" (VarT "shape"))
            (typbind "shape_2" (VarT "shape"))
            (typbind
              "_"
              (VarT "vcvtop__" (ExpA (VarE "shape_2")) (ExpA (VarE "shape_1")))
            )
          )
        )
        (typcase
          (Seq (Atom VSPLAT) Arg)
          (TupT (typbind "shape" (VarT "shape")))
        )
        (typcase
          (Seq (Atom VEXTRACT_LANE) Arg Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "sx?" (IterT (VarT "sx") Opt))
            (typbind "laneidx" (VarT "laneidx"))
          )
          (IfPr
            (BinE
              EquivOp
              bool
              (CmpE
                EqOp
                bool
                (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
                (OptE)
              )
              (MemE
                (CallE "lanetype" (ExpA (VarE "shape")))
                (ListE
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I64) (TupE))
                  (CaseE (Atom F32) (TupE))
                  (CaseE (Atom F64) (TupE))
                )
              )
            )
          )
        )
        (typcase
          (Seq (Atom VREPLACE_LANE) Arg Arg)
          (TupT
            (typbind "shape" (VarT "shape"))
            (typbind "laneidx" (VarT "laneidx"))
          )
        )
        (typcase
          (Seq (Atom REF.I31_NUM) Arg)
          (TupT (typbind "u31" (VarT "u31")))
        )
        (typcase (Atom REF.NULL_ADDR) (TupT))
        (typcase
          (Seq (Atom REF.STRUCT_ADDR) Arg)
          (TupT (typbind "structaddr" (VarT "structaddr")))
        )
        (typcase
          (Seq (Atom REF.ARRAY_ADDR) Arg)
          (TupT (typbind "arrayaddr" (VarT "arrayaddr")))
        )
        (typcase
          (Seq (Atom REF.FUNC_ADDR) Arg)
          (TupT (typbind "funcaddr" (VarT "funcaddr")))
        )
        (typcase
          (Seq (Atom REF.EXN_ADDR) Arg)
          (TupT (typbind "exnaddr" (VarT "exnaddr")))
        )
        (typcase
          (Seq (Atom REF.HOST_ADDR) Arg)
          (TupT (typbind "hostaddr" (VarT "hostaddr")))
        )
        (typcase
          (Seq (Atom REF.EXTERN) Arg)
          (TupT (typbind "ref" (VarT "ref")))
        )
        (typcase
          (Seq (Atom LABEL_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "n" (VarT "n"))
            (typbind "instr*" (IterT (VarT "instr") List))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom FRAME_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "n" (VarT "n"))
            (typbind "frame" (VarT "frame"))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase
          (Seq (Atom HANDLER_) Arg (Brack { Arg }) Arg)
          (TupT
            (typbind "n" (VarT "n"))
            (typbind "catch*" (IterT (VarT "catch") List))
            (typbind "instr*" (IterT (VarT "instr") List))
          )
        )
        (typcase (Atom TRAP) (TupT))
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
HintD
HintD
HintD
HintD
HintD
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
(DecD
  "memarg0"
  (VarT "memarg")
  (DefD
    (StrE
      (expfield (Atom ALIGN) (CaseE Arg (TupE (NumE (Nat 0)))))
      (expfield (Atom OFFSET) (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
)
HintD
(DecD
  "const"
  (ExpP "consttype" (VarT "consttype"))
  (ExpP
    "lit_"
    (VarT
      "lit_"
      (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
    )
  )
  (VarT "instr")
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "c" (VarT "num_" (ExpA (VarE "numtype"))))
    (ExpA (SubE (VarT "numtype") (VarT "consttype") (VarE "numtype")))
    (ExpA
      (CaseE (Seq (Atom mk_lit__0) Arg Arg) (TupE (VarE "numtype") (VarE "c")))
    )
    (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "numtype") (VarE "c")))
  )
  (DefD
    (ExpP "vectype" (VarT "vectype"))
    (ExpP "c" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "vectype"))))))
    (ExpA (SubE (VarT "vectype") (VarT "consttype") (VarE "vectype")))
    (ExpA
      (CaseE (Seq (Atom mk_lit__1) Arg Arg) (TupE (VarE "vectype") (VarE "c")))
    )
    (CaseE (Seq (Atom VCONST) Arg Arg) (TupE (VarE "vectype") (VarE "c")))
  )
)
HintD
(DecD
  "free_shape"
  (ExpP "shape" (VarT "shape"))
  (VarT "free")
  (DefD
    (ExpP "lanetype" (VarT "lanetype"))
    (ExpP "dim" (VarT "dim"))
    (ExpA (CaseE (Seq Arg (Atom X) Arg) (TupE (VarE "lanetype") (VarE "dim"))))
    (CallE "free_lanetype" (ExpA (VarE "lanetype")))
  )
)
(DecD
  "free_blocktype"
  (ExpP "blocktype" (VarT "blocktype"))
  (VarT "free")
  (DefD
    (ExpP "valtype?" (IterT (VarT "valtype") Opt))
    (ExpA
      (CaseE
        (Seq (Atom _RESULT) Arg)
        (TupE
          (IterE (VarE "valtype") Opt (iterexp "valtype" (VarE "valtype?")))
        )
      )
    )
    (CallE
      "free_opt"
      (ExpA
        (IterE
          (CallE "free_valtype" (ExpA (VarE "valtype")))
          Opt
          (iterexp "valtype" (VarE "valtype?"))
        )
      )
    )
  )
  (DefD
    (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx"))))
    (CallE "free_typeidx" (ExpA (VarE "typeidx")))
  )
)
(DecD
  "free_catch"
  (ExpP "catch" (VarT "catch"))
  (VarT "free")
  (DefD
    (ExpP "tagidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        (Seq (Atom CATCH) Arg Arg)
        (TupE (VarE "tagidx") (VarE "labelidx"))
      )
    )
    (CompE
      (CallE "free_tagidx" (ExpA (VarE "tagidx")))
      (CallE "free_labelidx" (ExpA (VarE "labelidx")))
    )
  )
  (DefD
    (ExpP "tagidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        (Seq (Atom CATCH_REF) Arg Arg)
        (TupE (VarE "tagidx") (VarE "labelidx"))
      )
    )
    (CompE
      (CallE "free_tagidx" (ExpA (VarE "tagidx")))
      (CallE "free_labelidx" (ExpA (VarE "labelidx")))
    )
  )
  (DefD
    (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom CATCH_ALL) Arg) (TupE (VarE "labelidx"))))
    (CallE "free_labelidx" (ExpA (VarE "labelidx")))
  )
  (DefD
    (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom CATCH_ALL_REF) Arg) (TupE (VarE "labelidx"))))
    (CallE "free_labelidx" (ExpA (VarE "labelidx")))
  )
)
(RecD
  (DecD
    "shift_labelidxs"
    (ExpP "_" (IterT (VarT "labelidx") List))
    (IterT (VarT "labelidx") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "labelidx'*" (IterT (VarT "labelidx") List))
      (ExpA
        (CatE
          (ListE (CaseE Arg (TupE (NumE (Nat 0)))))
          (IterE
            (VarE "labelidx'")
            List
            (iterexp "labelidx'" (VarE "labelidx'*"))
          )
        )
      )
      (CallE
        "shift_labelidxs"
        (ExpA
          (IterE
            (VarE "labelidx'")
            List
            (iterexp "labelidx'" (VarE "labelidx'*"))
          )
        )
      )
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "labelidx'*" (IterT (VarT "labelidx") List))
      (ExpA
        (CatE
          (ListE (VarE "labelidx"))
          (IterE
            (VarE "labelidx'")
            List
            (iterexp "labelidx'" (VarE "labelidx'*"))
          )
        )
      )
      (CatE
        (ListE
          (CaseE
            Arg
            (TupE
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE nat int (ProjE (UncaseE (VarE "labelidx") Arg) 0))
                  (CvtE nat int (NumE (Nat 1)))
                )
              )
            )
          )
        )
        (CallE
          "shift_labelidxs"
          (ExpA
            (IterE
              (VarE "labelidx'")
              List
              (iterexp "labelidx'" (VarE "labelidx'*"))
            )
          )
        )
      )
    )
  )
)
(RecD
  (DecD
    "free_instr"
    (ExpP "instr" (VarT "instr"))
    (VarT "free")
    (DefD
      (ExpA (CaseE (Atom NOP) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpA (CaseE (Atom UNREACHABLE) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpA (CaseE (Atom DROP) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "valtype*?" (IterT (IterT (VarT "valtype") List) Opt))
      (ExpA
        (CaseE
          (Seq (Atom SELECT) Arg)
          (TupE
            (IterE
              (IterE
                (VarE "valtype")
                List
                (iterexp "valtype" (VarE "valtype*"))
              )
              Opt
              (iterexp "valtype*" (VarE "valtype*?"))
            )
          )
        )
      )
      (CallE
        "free_opt"
        (ExpA
          (IterE
            (CallE
              "free_list"
              (ExpA
                (IterE
                  (CallE "free_valtype" (ExpA (VarE "valtype")))
                  List
                  (iterexp "valtype" (VarE "valtype*"))
                )
              )
            )
            Opt
            (iterexp "valtype*" (VarE "valtype*?"))
          )
        )
      )
    )
    (DefD
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpA
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (VarE "blocktype")
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
      )
      (CompE
        (CallE "free_blocktype" (ExpA (VarE "blocktype")))
        (CallE
          "free_block"
          (ExpA (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*"))))
        )
      )
    )
    (DefD
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpA
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE
            (VarE "blocktype")
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
      )
      (CompE
        (CallE "free_blocktype" (ExpA (VarE "blocktype")))
        (CallE
          "free_block"
          (ExpA (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*"))))
        )
      )
    )
    (DefD
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr_1*" (IterT (VarT "instr") List))
      (ExpP "instr_2*" (IterT (VarT "instr") List))
      (ExpA
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (VarE "blocktype")
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
      (CompE
        (CompE
          (CallE "free_blocktype" (ExpA (VarE "blocktype")))
          (CallE
            "free_block"
            (ExpA
              (IterE
                (VarE "instr_1")
                List
                (iterexp "instr_1" (VarE "instr_1*"))
              )
            )
          )
        )
        (CallE
          "free_block"
          (ExpA
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
      )
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom BR) Arg) (TupE (VarE "labelidx"))))
      (CallE "free_labelidx" (ExpA (VarE "labelidx")))
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "labelidx"))))
      (CallE "free_labelidx" (ExpA (VarE "labelidx")))
    )
    (DefD
      (ExpP "labelidx*" (IterT (VarT "labelidx") List))
      (ExpP "labelidx'" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE
            (IterE
              (VarE "labelidx")
              List
              (iterexp "labelidx" (VarE "labelidx*"))
            )
            (VarE "labelidx'")
          )
        )
      )
      (CompE
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_labelidx" (ExpA (VarE "labelidx")))
              List
              (iterexp "labelidx" (VarE "labelidx*"))
            )
          )
        )
        (CallE "free_labelidx" (ExpA (VarE "labelidx'")))
      )
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom BR_ON_NULL) Arg) (TupE (VarE "labelidx"))))
      (CallE "free_labelidx" (ExpA (VarE "labelidx")))
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom BR_ON_NON_NULL) Arg) (TupE (VarE "labelidx"))))
      (CallE "free_labelidx" (ExpA (VarE "labelidx")))
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "reftype_1" (VarT "reftype"))
      (ExpP "reftype_2" (VarT "reftype"))
      (ExpA
        (CaseE
          (Seq (Atom BR_ON_CAST) Arg Arg Arg)
          (TupE (VarE "labelidx") (VarE "reftype_1") (VarE "reftype_2"))
        )
      )
      (CompE
        (CompE
          (CallE "free_labelidx" (ExpA (VarE "labelidx")))
          (CallE "free_reftype" (ExpA (VarE "reftype_1")))
        )
        (CallE "free_reftype" (ExpA (VarE "reftype_2")))
      )
    )
    (DefD
      (ExpP "labelidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "reftype_1" (VarT "reftype"))
      (ExpP "reftype_2" (VarT "reftype"))
      (ExpA
        (CaseE
          (Seq (Atom BR_ON_CAST_FAIL) Arg Arg Arg)
          (TupE (VarE "labelidx") (VarE "reftype_1") (VarE "reftype_2"))
        )
      )
      (CompE
        (CompE
          (CallE "free_labelidx" (ExpA (VarE "labelidx")))
          (CallE "free_reftype" (ExpA (VarE "reftype_1")))
        )
        (CallE "free_reftype" (ExpA (VarE "reftype_2")))
      )
    )
    (DefD
      (ExpP "funcidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "funcidx"))))
      (CallE "free_funcidx" (ExpA (VarE "funcidx")))
    )
    (DefD
      (ExpP "typeuse" (VarT "typeuse"))
      (ExpA (CaseE (Seq (Atom CALL_REF) Arg) (TupE (VarE "typeuse"))))
      (CallE "free_typeuse" (ExpA (VarE "typeuse")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "typeuse" (VarT "typeuse"))
      (ExpA
        (CaseE
          (Seq (Atom CALL_INDIRECT) Arg Arg)
          (TupE (VarE "tableidx") (VarE "typeuse"))
        )
      )
      (CompE
        (CallE "free_tableidx" (ExpA (VarE "tableidx")))
        (CallE "free_typeuse" (ExpA (VarE "typeuse")))
      )
    )
    (DefD
      (ExpA (CaseE (Atom RETURN) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "funcidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom RETURN_CALL) Arg) (TupE (VarE "funcidx"))))
      (CallE "free_funcidx" (ExpA (VarE "funcidx")))
    )
    (DefD
      (ExpP "typeuse" (VarT "typeuse"))
      (ExpA (CaseE (Seq (Atom RETURN_CALL_REF) Arg) (TupE (VarE "typeuse"))))
      (CallE "free_typeuse" (ExpA (VarE "typeuse")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "typeuse" (VarT "typeuse"))
      (ExpA
        (CaseE
          (Seq (Atom RETURN_CALL_INDIRECT) Arg Arg)
          (TupE (VarE "tableidx") (VarE "typeuse"))
        )
      )
      (CompE
        (CallE "free_tableidx" (ExpA (VarE "tableidx")))
        (CallE "free_typeuse" (ExpA (VarE "typeuse")))
      )
    )
    (DefD
      (ExpP "tagidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom THROW) Arg) (TupE (VarE "tagidx"))))
      (CallE "free_tagidx" (ExpA (VarE "tagidx")))
    )
    (DefD
      (ExpA (CaseE (Atom THROW_REF) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "catch*" (IterT (VarT "catch") List))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpA
        (CaseE
          (Seq (Atom TRY_TABLE) Arg Arg Arg)
          (TupE
            (VarE "blocktype")
            (CaseE
              Arg
              (TupE
                (IterE (VarE "catch") List (iterexp "catch" (VarE "catch*")))
              )
            )
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
      )
      (CompE
        (CompE
          (CallE "free_blocktype" (ExpA (VarE "blocktype")))
          (CallE
            "free_list"
            (ExpA
              (IterE
                (CallE "free_catch" (ExpA (VarE "catch")))
                List
                (iterexp "catch" (VarE "catch*"))
              )
            )
          )
        )
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "numlit" (VarT "num_" (ExpA (VarE "numtype"))))
      (ExpA
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (VarE "numtype") (VarE "numlit"))
        )
      )
      (CallE "free_numtype" (ExpA (VarE "numtype")))
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "unop" (VarT "unop_" (ExpA (VarE "numtype"))))
      (ExpA
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "numtype") (VarE "unop")))
      )
      (CallE "free_numtype" (ExpA (VarE "numtype")))
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "binop" (VarT "binop_" (ExpA (VarE "numtype"))))
      (ExpA
        (CaseE
          (Seq (Atom BINOP) Arg Arg)
          (TupE (VarE "numtype") (VarE "binop"))
        )
      )
      (CallE "free_numtype" (ExpA (VarE "numtype")))
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "testop" (VarT "testop_" (ExpA (VarE "numtype"))))
      (ExpA
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "numtype") (VarE "testop"))
        )
      )
      (CallE "free_numtype" (ExpA (VarE "numtype")))
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "relop" (VarT "relop_" (ExpA (VarE "numtype"))))
      (ExpA
        (CaseE
          (Seq (Atom RELOP) Arg Arg)
          (TupE (VarE "numtype") (VarE "relop"))
        )
      )
      (CallE "free_numtype" (ExpA (VarE "numtype")))
    )
    (DefD
      (ExpP "numtype_1" (VarT "numtype"))
      (ExpP "numtype_2" (VarT "numtype"))
      (ExpP
        "cvtop"
        (VarT "cvtop__" (ExpA (VarE "numtype_2")) (ExpA (VarE "numtype_1")))
      )
      (ExpA
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "numtype_1") (VarE "numtype_2") (VarE "cvtop"))
        )
      )
      (CompE
        (CallE "free_numtype" (ExpA (VarE "numtype_1")))
        (CallE "free_numtype" (ExpA (VarE "numtype_2")))
      )
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "veclit" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "vectype"))))))
      (ExpA
        (CaseE
          (Seq (Atom VCONST) Arg Arg)
          (TupE (VarE "vectype") (VarE "veclit"))
        )
      )
      (CallE "free_vectype" (ExpA (VarE "vectype")))
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "vvunop" (VarT "vvunop"))
      (ExpA
        (CaseE
          (Seq (Atom VVUNOP) Arg Arg)
          (TupE (VarE "vectype") (VarE "vvunop"))
        )
      )
      (CallE "free_vectype" (ExpA (VarE "vectype")))
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "vvbinop" (VarT "vvbinop"))
      (ExpA
        (CaseE
          (Seq (Atom VVBINOP) Arg Arg)
          (TupE (VarE "vectype") (VarE "vvbinop"))
        )
      )
      (CallE "free_vectype" (ExpA (VarE "vectype")))
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "vvternop" (VarT "vvternop"))
      (ExpA
        (CaseE
          (Seq (Atom VVTERNOP) Arg Arg)
          (TupE (VarE "vectype") (VarE "vvternop"))
        )
      )
      (CallE "free_vectype" (ExpA (VarE "vectype")))
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "vvtestop" (VarT "vvtestop"))
      (ExpA
        (CaseE
          (Seq (Atom VVTESTOP) Arg Arg)
          (TupE (VarE "vectype") (VarE "vvtestop"))
        )
      )
      (CallE "free_vectype" (ExpA (VarE "vectype")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "vunop" (VarT "vunop_" (ExpA (VarE "shape"))))
      (ExpA
        (CaseE (Seq (Atom VUNOP) Arg Arg) (TupE (VarE "shape") (VarE "vunop")))
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "vbinop" (VarT "vbinop_" (ExpA (VarE "shape"))))
      (ExpA
        (CaseE
          (Seq (Atom VBINOP) Arg Arg)
          (TupE (VarE "shape") (VarE "vbinop"))
        )
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "vternop" (VarT "vternop_" (ExpA (VarE "shape"))))
      (ExpA
        (CaseE
          (Seq (Atom VTERNOP) Arg Arg)
          (TupE (VarE "shape") (VarE "vternop"))
        )
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "vtestop" (VarT "vtestop_" (ExpA (VarE "shape"))))
      (ExpA
        (CaseE
          (Seq (Atom VTESTOP) Arg Arg)
          (TupE (VarE "shape") (VarE "vtestop"))
        )
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "vrelop" (VarT "vrelop_" (ExpA (VarE "shape"))))
      (ExpA
        (CaseE
          (Seq (Atom VRELOP) Arg Arg)
          (TupE (VarE "shape") (VarE "vrelop"))
        )
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "ishape" (VarT "ishape"))
      (ExpP "vshiftop" (VarT "vshiftop_" (ExpA (VarE "ishape"))))
      (ExpA
        (CaseE
          (Seq (Atom VSHIFTOP) Arg Arg)
          (TupE (VarE "ishape") (VarE "vshiftop"))
        )
      )
      (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape") Arg) 0)))
    )
    (DefD
      (ExpP "ishape" (VarT "ishape"))
      (ExpA (CaseE (Seq (Atom VBITMASK) Arg) (TupE (VarE "ishape"))))
      (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape") Arg) 0)))
    )
    (DefD
      (ExpP "bshape" (VarT "bshape"))
      (ExpP "vswizzlop" (VarT "vswizzlop_" (ExpA (VarE "bshape"))))
      (ExpA
        (CaseE
          (Seq (Atom VSWIZZLOP) Arg Arg)
          (TupE (VarE "bshape") (VarE "vswizzlop"))
        )
      )
      (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "bshape") Arg) 0)))
    )
    (DefD
      (ExpP "bshape" (VarT "bshape"))
      (ExpP "laneidx*" (IterT (VarT "laneidx") List))
      (ExpA
        (CaseE
          (Seq (Atom VSHUFFLE) Arg Arg)
          (TupE
            (VarE "bshape")
            (IterE (VarE "laneidx") List (iterexp "laneidx" (VarE "laneidx*")))
          )
        )
      )
      (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "bshape") Arg) 0)))
    )
    (DefD
      (ExpP "ishape_1" (VarT "ishape"))
      (ExpP "ishape_2" (VarT "ishape"))
      (ExpP
        "vextunop"
        (VarT "vextunop__" (ExpA (VarE "ishape_2")) (ExpA (VarE "ishape_1")))
      )
      (ExpA
        (CaseE
          (Seq (Atom VEXTUNOP) Arg Arg Arg)
          (TupE (VarE "ishape_1") (VarE "ishape_2") (VarE "vextunop"))
        )
      )
      (CompE
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_1") Arg) 0)))
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_2") Arg) 0)))
      )
    )
    (DefD
      (ExpP "ishape_1" (VarT "ishape"))
      (ExpP "ishape_2" (VarT "ishape"))
      (ExpP
        "vextbinop"
        (VarT "vextbinop__" (ExpA (VarE "ishape_2")) (ExpA (VarE "ishape_1")))
      )
      (ExpA
        (CaseE
          (Seq (Atom VEXTBINOP) Arg Arg Arg)
          (TupE (VarE "ishape_1") (VarE "ishape_2") (VarE "vextbinop"))
        )
      )
      (CompE
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_1") Arg) 0)))
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_2") Arg) 0)))
      )
    )
    (DefD
      (ExpP "ishape_1" (VarT "ishape"))
      (ExpP "ishape_2" (VarT "ishape"))
      (ExpP
        "vextternop"
        (VarT "vextternop__" (ExpA (VarE "ishape_2")) (ExpA (VarE "ishape_1")))
      )
      (ExpA
        (CaseE
          (Seq (Atom VEXTTERNOP) Arg Arg Arg)
          (TupE (VarE "ishape_1") (VarE "ishape_2") (VarE "vextternop"))
        )
      )
      (CompE
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_1") Arg) 0)))
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_2") Arg) 0)))
      )
    )
    (DefD
      (ExpP "ishape_1" (VarT "ishape"))
      (ExpP "ishape_2" (VarT "ishape"))
      (ExpP "sx" (VarT "sx"))
      (ExpA
        (CaseE
          (Seq (Atom VNARROW) Arg Arg Arg)
          (TupE (VarE "ishape_1") (VarE "ishape_2") (VarE "sx"))
        )
      )
      (CompE
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_1") Arg) 0)))
        (CallE "free_shape" (ExpA (ProjE (UncaseE (VarE "ishape_2") Arg) 0)))
      )
    )
    (DefD
      (ExpP "shape_1" (VarT "shape"))
      (ExpP "shape_2" (VarT "shape"))
      (ExpP
        "vcvtop"
        (VarT "vcvtop__" (ExpA (VarE "shape_2")) (ExpA (VarE "shape_1")))
      )
      (ExpA
        (CaseE
          (Seq (Atom VCVTOP) Arg Arg Arg)
          (TupE (VarE "shape_1") (VarE "shape_2") (VarE "vcvtop"))
        )
      )
      (CompE
        (CallE "free_shape" (ExpA (VarE "shape_1")))
        (CallE "free_shape" (ExpA (VarE "shape_2")))
      )
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpA (CaseE (Seq (Atom VSPLAT) Arg) (TupE (VarE "shape"))))
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "sx?" (IterT (VarT "sx") Opt))
      (ExpP "laneidx" (VarT "uN" (ExpA (NumE (Nat 8)))))
      (ExpA
        (CaseE
          (Seq (Atom VEXTRACT_LANE) Arg Arg Arg)
          (TupE
            (VarE "shape")
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (VarE "laneidx")
          )
        )
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "shape" (VarT "shape"))
      (ExpP "laneidx" (VarT "uN" (ExpA (NumE (Nat 8)))))
      (ExpA
        (CaseE
          (Seq (Atom VREPLACE_LANE) Arg Arg)
          (TupE (VarE "shape") (VarE "laneidx"))
        )
      )
      (CallE "free_shape" (ExpA (VarE "shape")))
    )
    (DefD
      (ExpP "heaptype" (VarT "heaptype"))
      (ExpA (CaseE (Seq (Atom REF.NULL) Arg) (TupE (VarE "heaptype"))))
      (CallE "free_heaptype" (ExpA (VarE "heaptype")))
    )
    (DefD
      (ExpA (CaseE (Atom REF.IS_NULL) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpA (CaseE (Atom REF.AS_NON_NULL) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpA (CaseE (Atom REF.EQ) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "reftype" (VarT "reftype"))
      (ExpA (CaseE (Seq (Atom REF.TEST) Arg) (TupE (VarE "reftype"))))
      (CallE "free_reftype" (ExpA (VarE "reftype")))
    )
    (DefD
      (ExpP "reftype" (VarT "reftype"))
      (ExpA (CaseE (Seq (Atom REF.CAST) Arg) (TupE (VarE "reftype"))))
      (CallE "free_reftype" (ExpA (VarE "reftype")))
    )
    (DefD
      (ExpP "funcidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom REF.FUNC) Arg) (TupE (VarE "funcidx"))))
      (CallE "free_funcidx" (ExpA (VarE "funcidx")))
    )
    (DefD
      (ExpA (CaseE (Atom REF.I31) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "sx" (VarT "sx"))
      (ExpA (CaseE (Seq (Atom I31.GET) Arg) (TupE (VarE "sx"))))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom STRUCT.NEW) Arg) (TupE (VarE "typeidx"))))
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom STRUCT.NEW_DEFAULT) Arg) (TupE (VarE "typeidx"))))
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "sx?" (IterT (VarT "sx") Opt))
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "u32" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom STRUCT.GET) Arg Arg Arg)
          (TupE
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (VarE "typeidx")
            (VarE "u32")
          )
        )
      )
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "u32" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom STRUCT.SET) Arg Arg)
          (TupE (VarE "typeidx") (VarE "u32"))
        )
      )
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom ARRAY.NEW) Arg) (TupE (VarE "typeidx"))))
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom ARRAY.NEW_DEFAULT) Arg) (TupE (VarE "typeidx"))))
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "u32" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.NEW_FIXED) Arg Arg)
          (TupE (VarE "typeidx") (VarE "u32"))
        )
      )
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "dataidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.NEW_DATA) Arg Arg)
          (TupE (VarE "typeidx") (VarE "dataidx"))
        )
      )
      (CompE
        (CallE "free_typeidx" (ExpA (VarE "typeidx")))
        (CallE "free_dataidx" (ExpA (VarE "dataidx")))
      )
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "elemidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.NEW_ELEM) Arg Arg)
          (TupE (VarE "typeidx") (VarE "elemidx"))
        )
      )
      (CompE
        (CallE "free_typeidx" (ExpA (VarE "typeidx")))
        (CallE "free_elemidx" (ExpA (VarE "elemidx")))
      )
    )
    (DefD
      (ExpP "sx?" (IterT (VarT "sx") Opt))
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.GET) Arg Arg)
          (TupE
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (VarE "typeidx")
          )
        )
      )
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom ARRAY.SET) Arg) (TupE (VarE "typeidx"))))
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpA (CaseE (Atom ARRAY.LEN) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom ARRAY.FILL) Arg) (TupE (VarE "typeidx"))))
      (CallE "free_typeidx" (ExpA (VarE "typeidx")))
    )
    (DefD
      (ExpP "typeidx_1" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "typeidx_2" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.COPY) Arg Arg)
          (TupE (VarE "typeidx_1") (VarE "typeidx_2"))
        )
      )
      (CompE
        (CallE "free_typeidx" (ExpA (VarE "typeidx_1")))
        (CallE "free_typeidx" (ExpA (VarE "typeidx_2")))
      )
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "dataidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.INIT_DATA) Arg Arg)
          (TupE (VarE "typeidx") (VarE "dataidx"))
        )
      )
      (CompE
        (CallE "free_typeidx" (ExpA (VarE "typeidx")))
        (CallE "free_dataidx" (ExpA (VarE "dataidx")))
      )
    )
    (DefD
      (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "elemidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom ARRAY.INIT_ELEM) Arg Arg)
          (TupE (VarE "typeidx") (VarE "elemidx"))
        )
      )
      (CompE
        (CallE "free_typeidx" (ExpA (VarE "typeidx")))
        (CallE "free_elemidx" (ExpA (VarE "elemidx")))
      )
    )
    (DefD
      (ExpA (CaseE (Atom EXTERN.CONVERT_ANY) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpA (CaseE (Atom ANY.CONVERT_EXTERN) (TupE)))
      (StrE
        (expfield (Atom TYPES) (ListE))
        (expfield (Atom FUNCS) (ListE))
        (expfield (Atom GLOBALS) (ListE))
        (expfield (Atom TABLES) (ListE))
        (expfield (Atom MEMS) (ListE))
        (expfield (Atom ELEMS) (ListE))
        (expfield (Atom DATAS) (ListE))
        (expfield (Atom LOCALS) (ListE))
        (expfield (Atom LABELS) (ListE))
        (expfield (Atom TAGS) (ListE))
      )
    )
    (DefD
      (ExpP "localidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "localidx"))))
      (CallE "free_localidx" (ExpA (VarE "localidx")))
    )
    (DefD
      (ExpP "localidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "localidx"))))
      (CallE "free_localidx" (ExpA (VarE "localidx")))
    )
    (DefD
      (ExpP "localidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "localidx"))))
      (CallE "free_localidx" (ExpA (VarE "localidx")))
    )
    (DefD
      (ExpP "globalidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "globalidx"))))
      (CallE "free_globalidx" (ExpA (VarE "globalidx")))
    )
    (DefD
      (ExpP "globalidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "globalidx"))))
      (CallE "free_globalidx" (ExpA (VarE "globalidx")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom TABLE.GET) Arg) (TupE (VarE "tableidx"))))
      (CallE "free_tableidx" (ExpA (VarE "tableidx")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom TABLE.SET) Arg) (TupE (VarE "tableidx"))))
      (CallE "free_tableidx" (ExpA (VarE "tableidx")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom TABLE.SIZE) Arg) (TupE (VarE "tableidx"))))
      (CallE "free_tableidx" (ExpA (VarE "tableidx")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom TABLE.GROW) Arg) (TupE (VarE "tableidx"))))
      (CallE "free_tableidx" (ExpA (VarE "tableidx")))
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom TABLE.FILL) Arg) (TupE (VarE "tableidx"))))
      (CallE "free_tableidx" (ExpA (VarE "tableidx")))
    )
    (DefD
      (ExpP "tableidx_1" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "tableidx_2" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom TABLE.COPY) Arg Arg)
          (TupE (VarE "tableidx_1") (VarE "tableidx_2"))
        )
      )
      (CompE
        (CallE "free_tableidx" (ExpA (VarE "tableidx_1")))
        (CallE "free_tableidx" (ExpA (VarE "tableidx_2")))
      )
    )
    (DefD
      (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "elemidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom TABLE.INIT) Arg Arg)
          (TupE (VarE "tableidx") (VarE "elemidx"))
        )
      )
      (CompE
        (CallE "free_tableidx" (ExpA (VarE "tableidx")))
        (CallE "free_elemidx" (ExpA (VarE "elemidx")))
      )
    )
    (DefD
      (ExpP "elemidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom ELEM.DROP) Arg) (TupE (VarE "elemidx"))))
      (CallE "free_elemidx" (ExpA (VarE "elemidx")))
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "loadop?" (IterT (VarT "loadop_" (ExpA (VarE "numtype"))) Opt))
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memarg" (VarT "memarg"))
      (ExpA
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg Arg)
          (TupE
            (VarE "numtype")
            (IterE (VarE "loadop") Opt (iterexp "loadop" (VarE "loadop?")))
            (VarE "memidx")
            (VarE "memarg")
          )
        )
      )
      (CompE
        (CallE "free_numtype" (ExpA (VarE "numtype")))
        (CallE "free_memidx" (ExpA (VarE "memidx")))
      )
    )
    (DefD
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "storeop?" (IterT (VarT "storeop_" (ExpA (VarE "numtype"))) Opt))
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memarg" (VarT "memarg"))
      (ExpA
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg Arg)
          (TupE
            (VarE "numtype")
            (IterE (VarE "storeop") Opt (iterexp "storeop" (VarE "storeop?")))
            (VarE "memidx")
            (VarE "memarg")
          )
        )
      )
      (CompE
        (CallE "free_numtype" (ExpA (VarE "numtype")))
        (CallE "free_memidx" (ExpA (VarE "memidx")))
      )
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "vloadop?" (IterT (VarT "vloadop_" (ExpA (VarE "vectype"))) Opt))
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memarg" (VarT "memarg"))
      (ExpA
        (CaseE
          (Seq (Atom VLOAD) Arg Arg Arg Arg)
          (TupE
            (VarE "vectype")
            (IterE (VarE "vloadop") Opt (iterexp "vloadop" (VarE "vloadop?")))
            (VarE "memidx")
            (VarE "memarg")
          )
        )
      )
      (CompE
        (CallE "free_vectype" (ExpA (VarE "vectype")))
        (CallE "free_memidx" (ExpA (VarE "memidx")))
      )
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "sz" (VarT "sz"))
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "laneidx" (VarT "uN" (ExpA (NumE (Nat 8)))))
      (ExpA
        (CaseE
          (Seq (Atom VLOAD_LANE) Arg Arg Arg Arg Arg)
          (TupE
            (VarE "vectype")
            (VarE "sz")
            (VarE "memidx")
            (VarE "memarg")
            (VarE "laneidx")
          )
        )
      )
      (CompE
        (CallE "free_vectype" (ExpA (VarE "vectype")))
        (CallE "free_memidx" (ExpA (VarE "memidx")))
      )
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memarg" (VarT "memarg"))
      (ExpA
        (CaseE
          (Seq (Atom VSTORE) Arg Arg Arg)
          (TupE (VarE "vectype") (VarE "memidx") (VarE "memarg"))
        )
      )
      (CompE
        (CallE "free_vectype" (ExpA (VarE "vectype")))
        (CallE "free_memidx" (ExpA (VarE "memidx")))
      )
    )
    (DefD
      (ExpP "vectype" (VarT "vectype"))
      (ExpP "sz" (VarT "sz"))
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "laneidx" (VarT "uN" (ExpA (NumE (Nat 8)))))
      (ExpA
        (CaseE
          (Seq (Atom VSTORE_LANE) Arg Arg Arg Arg Arg)
          (TupE
            (VarE "vectype")
            (VarE "sz")
            (VarE "memidx")
            (VarE "memarg")
            (VarE "laneidx")
          )
        )
      )
      (CompE
        (CallE "free_vectype" (ExpA (VarE "vectype")))
        (CallE "free_memidx" (ExpA (VarE "memidx")))
      )
    )
    (DefD
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom MEMORY.SIZE) Arg) (TupE (VarE "memidx"))))
      (CallE "free_memidx" (ExpA (VarE "memidx")))
    )
    (DefD
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom MEMORY.GROW) Arg) (TupE (VarE "memidx"))))
      (CallE "free_memidx" (ExpA (VarE "memidx")))
    )
    (DefD
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom MEMORY.FILL) Arg) (TupE (VarE "memidx"))))
      (CallE "free_memidx" (ExpA (VarE "memidx")))
    )
    (DefD
      (ExpP "memidx_1" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "memidx_2" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom MEMORY.COPY) Arg Arg)
          (TupE (VarE "memidx_1") (VarE "memidx_2"))
        )
      )
      (CompE
        (CallE "free_memidx" (ExpA (VarE "memidx_1")))
        (CallE "free_memidx" (ExpA (VarE "memidx_2")))
      )
    )
    (DefD
      (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "dataidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA
        (CaseE
          (Seq (Atom MEMORY.INIT) Arg Arg)
          (TupE (VarE "memidx") (VarE "dataidx"))
        )
      )
      (CompE
        (CallE "free_memidx" (ExpA (VarE "memidx")))
        (CallE "free_dataidx" (ExpA (VarE "dataidx")))
      )
    )
    (DefD
      (ExpP "dataidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpA (CaseE (Seq (Atom DATA.DROP) Arg) (TupE (VarE "dataidx"))))
      (CallE "free_dataidx" (ExpA (VarE "dataidx")))
    )
  )
  (DecD
    "free_block"
    (ExpP "_" (IterT (VarT "instr") List))
    (VarT "free")
    (DefD
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpA (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*"))))
      (UpdE
        (VarE "free")
        (DotP RootP (Atom LABELS))
        (CallE "shift_labelidxs" (ExpA (DotE (VarE "free") (Atom LABELS))))
      )
      (LetPr
        (VarE "free")
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_instr" (ExpA (VarE "instr")))
              List
              (iterexp "instr" (VarE "instr*"))
            )
          )
        )
      )
    )
  )
)
(DecD
  "free_expr"
  (ExpP "expr" (VarT "expr"))
  (VarT "free")
  (DefD
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpA (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*"))))
    (CallE
      "free_list"
      (ExpA
        (IterE
          (CallE "free_instr" (ExpA (VarE "instr")))
          List
          (iterexp "instr" (VarE "instr*"))
        )
      )
    )
  )
)
(TypD
  "elemmode"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom ACTIVE) Arg Arg)
        (TupT
          (typbind "tableidx" (VarT "tableidx"))
          (typbind "expr" (VarT "expr"))
        )
      )
      (typcase (Atom PASSIVE) (TupT))
      (typcase (Atom DECLARE) (TupT))
    )
  )
)
HintD
(TypD
  "datamode"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom ACTIVE) Arg Arg)
        (TupT (typbind "memidx" (VarT "memidx")) (typbind "expr" (VarT "expr")))
      )
      (typcase (Atom PASSIVE) (TupT))
    )
  )
)
HintD
(TypD
  "type"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom TYPE) Arg)
        (TupT (typbind "rectype" (VarT "rectype")))
      )
    )
  )
)
HintD
(TypD
  "tag"
  (InstD
    (VariantT
      (typcase (Seq (Atom TAG) Arg) (TupT (typbind "tagtype" (VarT "tagtype"))))
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
  "table"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom TABLE) Arg Arg)
        (TupT
          (typbind "tabletype" (VarT "tabletype"))
          (typbind "expr" (VarT "expr"))
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
          (typbind "byte*" (IterT (VarT "byte") List))
          (typbind "datamode" (VarT "datamode"))
        )
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
  "elem"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom ELEM) Arg Arg Arg)
        (TupT
          (typbind "reftype" (VarT "reftype"))
          (typbind "expr*" (IterT (VarT "expr") List))
          (typbind "elemmode" (VarT "elemmode"))
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
  "module"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupT
          (typbind "_" (VarT "list" (TypA (VarT "type"))))
          (typbind "_" (VarT "list" (TypA (VarT "import"))))
          (typbind "_" (VarT "list" (TypA (VarT "tag"))))
          (typbind "_" (VarT "list" (TypA (VarT "global"))))
          (typbind "_" (VarT "list" (TypA (VarT "mem"))))
          (typbind "_" (VarT "list" (TypA (VarT "table"))))
          (typbind "_" (VarT "list" (TypA (VarT "func"))))
          (typbind "_" (VarT "list" (TypA (VarT "data"))))
          (typbind "_" (VarT "list" (TypA (VarT "elem"))))
          (typbind "start?" (IterT (VarT "start") Opt))
          (typbind "_" (VarT "list" (TypA (VarT "export"))))
        )
      )
    )
  )
)
HintD
(DecD
  "free_type"
  (ExpP "type" (VarT "type"))
  (VarT "free")
  (DefD
    (ExpP "rectype" (VarT "rectype"))
    (ExpA (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "rectype"))))
    (CallE "free_rectype" (ExpA (VarE "rectype")))
  )
)
(DecD
  "free_tag"
  (ExpP "tag" (VarT "tag"))
  (VarT "free")
  (DefD
    (ExpP "tagtype" (VarT "typeuse"))
    (ExpA (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagtype"))))
    (CallE "free_tagtype" (ExpA (VarE "tagtype")))
  )
)
(DecD
  "free_global"
  (ExpP "global" (VarT "global"))
  (VarT "free")
  (DefD
    (ExpP "globaltype" (VarT "globaltype"))
    (ExpP "expr" (IterT (VarT "instr") List))
    (ExpA
      (CaseE
        (Seq (Atom GLOBAL) Arg Arg)
        (TupE (VarE "globaltype") (VarE "expr"))
      )
    )
    (CompE
      (CallE "free_globaltype" (ExpA (VarE "globaltype")))
      (CallE "free_expr" (ExpA (VarE "expr")))
    )
  )
)
(DecD
  "free_mem"
  (ExpP "mem" (VarT "mem"))
  (VarT "free")
  (DefD
    (ExpP "memtype" (VarT "memtype"))
    (ExpA (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype"))))
    (CallE "free_memtype" (ExpA (VarE "memtype")))
  )
)
(DecD
  "free_table"
  (ExpP "table" (VarT "table"))
  (VarT "free")
  (DefD
    (ExpP "tabletype" (VarT "tabletype"))
    (ExpP "expr" (IterT (VarT "instr") List))
    (ExpA
      (CaseE (Seq (Atom TABLE) Arg Arg) (TupE (VarE "tabletype") (VarE "expr")))
    )
    (CompE
      (CallE "free_tabletype" (ExpA (VarE "tabletype")))
      (CallE "free_expr" (ExpA (VarE "expr")))
    )
  )
)
(DecD
  "free_local"
  (ExpP "local" (VarT "local"))
  (VarT "free")
  (DefD
    (ExpP "t" (VarT "valtype"))
    (ExpA (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t"))))
    (CallE "free_valtype" (ExpA (VarE "t")))
  )
)
(DecD
  "free_func"
  (ExpP "func" (VarT "func"))
  (VarT "free")
  (DefD
    (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "local*" (IterT (VarT "local") List))
    (ExpP "expr" (IterT (VarT "instr") List))
    (ExpA
      (CaseE
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupE
          (VarE "typeidx")
          (IterE (VarE "local") List (iterexp "local" (VarE "local*")))
          (VarE "expr")
        )
      )
    )
    (CompE
      (CompE
        (CallE "free_typeidx" (ExpA (VarE "typeidx")))
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_local" (ExpA (VarE "local")))
              List
              (iterexp "local" (VarE "local*"))
            )
          )
        )
      )
      (UpdE
        (CallE "free_block" (ExpA (VarE "expr")))
        (DotP RootP (Atom LOCALS))
        (ListE)
      )
    )
  )
)
(DecD
  "free_datamode"
  (ExpP "datamode" (VarT "datamode"))
  (VarT "free")
  (DefD
    (ExpP "memidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "expr" (IterT (VarT "instr") List))
    (ExpA
      (CaseE (Seq (Atom ACTIVE) Arg Arg) (TupE (VarE "memidx") (VarE "expr")))
    )
    (CompE
      (CallE "free_memidx" (ExpA (VarE "memidx")))
      (CallE "free_expr" (ExpA (VarE "expr")))
    )
  )
  (DefD
    (ExpA (CaseE (Atom PASSIVE) (TupE)))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_data"
  (ExpP "data" (VarT "data"))
  (VarT "free")
  (DefD
    (ExpP "byte*" (IterT (VarT "byte") List))
    (ExpP "datamode" (VarT "datamode"))
    (ExpA
      (CaseE
        (Seq (Atom DATA) Arg Arg)
        (TupE
          (IterE (VarE "byte") List (iterexp "byte" (VarE "byte*")))
          (VarE "datamode")
        )
      )
    )
    (CallE "free_datamode" (ExpA (VarE "datamode")))
  )
)
(DecD
  "free_elemmode"
  (ExpP "elemmode" (VarT "elemmode"))
  (VarT "free")
  (DefD
    (ExpP "tableidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "expr" (IterT (VarT "instr") List))
    (ExpA
      (CaseE (Seq (Atom ACTIVE) Arg Arg) (TupE (VarE "tableidx") (VarE "expr")))
    )
    (CompE
      (CallE "free_tableidx" (ExpA (VarE "tableidx")))
      (CallE "free_expr" (ExpA (VarE "expr")))
    )
  )
  (DefD
    (ExpA (CaseE (Atom PASSIVE) (TupE)))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
  (DefD
    (ExpA (CaseE (Atom DECLARE) (TupE)))
    (StrE
      (expfield (Atom TYPES) (ListE))
      (expfield (Atom FUNCS) (ListE))
      (expfield (Atom GLOBALS) (ListE))
      (expfield (Atom TABLES) (ListE))
      (expfield (Atom MEMS) (ListE))
      (expfield (Atom ELEMS) (ListE))
      (expfield (Atom DATAS) (ListE))
      (expfield (Atom LOCALS) (ListE))
      (expfield (Atom LABELS) (ListE))
      (expfield (Atom TAGS) (ListE))
    )
  )
)
(DecD
  "free_elem"
  (ExpP "elem" (VarT "elem"))
  (VarT "free")
  (DefD
    (ExpP "reftype" (VarT "reftype"))
    (ExpP "expr*" (IterT (VarT "expr") List))
    (ExpP "elemmode" (VarT "elemmode"))
    (ExpA
      (CaseE
        (Seq (Atom ELEM) Arg Arg Arg)
        (TupE
          (VarE "reftype")
          (IterE (VarE "expr") List (iterexp "expr" (VarE "expr*")))
          (VarE "elemmode")
        )
      )
    )
    (CompE
      (CompE
        (CallE "free_reftype" (ExpA (VarE "reftype")))
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_expr" (ExpA (VarE "expr")))
              List
              (iterexp "expr" (VarE "expr*"))
            )
          )
        )
      )
      (CallE "free_elemmode" (ExpA (VarE "elemmode")))
    )
  )
)
(DecD
  "free_start"
  (ExpP "start" (VarT "start"))
  (VarT "free")
  (DefD
    (ExpP "funcidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (CaseE (Seq (Atom START) Arg) (TupE (VarE "funcidx"))))
    (CallE "free_funcidx" (ExpA (VarE "funcidx")))
  )
)
(DecD
  "free_import"
  (ExpP "import" (VarT "import"))
  (VarT "free")
  (DefD
    (ExpP "name_1" (VarT "name"))
    (ExpP "name_2" (VarT "name"))
    (ExpP "externtype" (VarT "externtype"))
    (ExpA
      (CaseE
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupE (VarE "name_1") (VarE "name_2") (VarE "externtype"))
      )
    )
    (CallE "free_externtype" (ExpA (VarE "externtype")))
  )
)
(DecD
  "free_export"
  (ExpP "export" (VarT "export"))
  (VarT "free")
  (DefD
    (ExpP "name" (VarT "name"))
    (ExpP "externidx" (VarT "externidx"))
    (ExpA
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (VarE "externidx"))
      )
    )
    (CallE "free_externidx" (ExpA (VarE "externidx")))
  )
)
(DecD
  "free_module"
  (ExpP "module" (VarT "module"))
  (VarT "free")
  (DefD
    (ExpP "type*" (IterT (VarT "type") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "tag*" (IterT (VarT "tag") List))
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (ExpA
      (CaseE
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupE
          (CaseE
            Arg
            (TupE (IterE (VarE "type") List (iterexp "type" (VarE "type*"))))
          )
          (CaseE
            Arg
            (TupE
              (IterE (VarE "import") List (iterexp "import" (VarE "import*")))
            )
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "tag") List (iterexp "tag" (VarE "tag*"))))
          )
          (CaseE
            Arg
            (TupE
              (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
            )
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "table") List (iterexp "table" (VarE "table*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "func") List (iterexp "func" (VarE "func*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "data") List (iterexp "data" (VarE "data*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*"))))
          )
          (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
          (CaseE
            Arg
            (TupE
              (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
            )
          )
        )
      )
    )
    (CompE
      (CompE
        (CompE
          (CompE
            (CompE
              (CompE
                (CompE
                  (CompE
                    (CompE
                      (CompE
                        (CallE
                          "free_list"
                          (ExpA
                            (IterE
                              (CallE "free_type" (ExpA (VarE "type")))
                              List
                              (iterexp "type" (VarE "type*"))
                            )
                          )
                        )
                        (CallE
                          "free_list"
                          (ExpA
                            (IterE
                              (CallE "free_tag" (ExpA (VarE "tag")))
                              List
                              (iterexp "tag" (VarE "tag*"))
                            )
                          )
                        )
                      )
                      (CallE
                        "free_list"
                        (ExpA
                          (IterE
                            (CallE "free_global" (ExpA (VarE "global")))
                            List
                            (iterexp "global" (VarE "global*"))
                          )
                        )
                      )
                    )
                    (CallE
                      "free_list"
                      (ExpA
                        (IterE
                          (CallE "free_mem" (ExpA (VarE "mem")))
                          List
                          (iterexp "mem" (VarE "mem*"))
                        )
                      )
                    )
                  )
                  (CallE
                    "free_list"
                    (ExpA
                      (IterE
                        (CallE "free_table" (ExpA (VarE "table")))
                        List
                        (iterexp "table" (VarE "table*"))
                      )
                    )
                  )
                )
                (CallE
                  "free_list"
                  (ExpA
                    (IterE
                      (CallE "free_func" (ExpA (VarE "func")))
                      List
                      (iterexp "func" (VarE "func*"))
                    )
                  )
                )
              )
              (CallE
                "free_list"
                (ExpA
                  (IterE
                    (CallE "free_data" (ExpA (VarE "data")))
                    List
                    (iterexp "data" (VarE "data*"))
                  )
                )
              )
            )
            (CallE
              "free_list"
              (ExpA
                (IterE
                  (CallE "free_elem" (ExpA (VarE "elem")))
                  List
                  (iterexp "elem" (VarE "elem*"))
                )
              )
            )
          )
          (CallE
            "free_opt"
            (ExpA
              (IterE
                (CallE "free_start" (ExpA (VarE "start")))
                Opt
                (iterexp "start" (VarE "start?"))
              )
            )
          )
        )
        (CallE
          "free_list"
          (ExpA
            (IterE
              (CallE "free_import" (ExpA (VarE "import")))
              List
              (iterexp "import" (VarE "import*"))
            )
          )
        )
      )
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_export" (ExpA (VarE "export")))
            List
            (iterexp "export" (VarE "export*"))
          )
        )
      )
    )
  )
)
(DecD
  "funcidx_module"
  (ExpP "module" (VarT "module"))
  (IterT (VarT "funcidx") List)
  (DefD
    (ExpP "module" (VarT "module"))
    (ExpA (VarE "module"))
    (DotE (CallE "free_module" (ExpA (VarE "module"))) (Atom FUNCS))
  )
)
HintD
(DecD
  "dataidx_funcs"
  (ExpP "_" (IterT (VarT "func") List))
  (IterT (VarT "dataidx") List)
  (DefD
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpA (IterE (VarE "func") List (iterexp "func" (VarE "func*"))))
    (DotE
      (CallE
        "free_list"
        (ExpA
          (IterE
            (CallE "free_func" (ExpA (VarE "func")))
            List
            (iterexp "func" (VarE "func*"))
          )
        )
      )
      (Atom DATAS)
    )
  )
)
HintD
(TypD
  "init"
  (InstD (VariantT (typcase (Atom SET) (TupT)) (typcase (Atom UNSET) (TupT))))
)
HintD
(TypD
  "localtype"
  (InstD
    (VariantT
      (typcase
        (Seq Arg Arg)
        (TupT
          (typbind "init" (VarT "init"))
          (typbind "valtype" (VarT "valtype"))
        )
      )
    )
  )
)
HintD
(TypD
  "instrtype"
  (InstD
    (VariantT
      (typcase
        (Infix Arg ->_ (Seq Arg Arg))
        (TupT
          (typbind "resulttype" (VarT "resulttype"))
          (typbind "localidx*" (IterT (VarT "localidx") List))
          (typbind "resulttype" (VarT "resulttype"))
        )
      )
    )
  )
)
HintD
(TypD
  "context"
  (InstD
    (StructT
      (typfield (Atom TYPES) (IterT (VarT "deftype") List))
      (typfield (Atom TAGS) (IterT (VarT "tagtype") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globaltype") List))
      (typfield (Atom MEMS) (IterT (VarT "memtype") List))
      (typfield (Atom TABLES) (IterT (VarT "tabletype") List))
      (typfield (Atom FUNCS) (IterT (VarT "deftype") List))
      (typfield (Atom DATAS) (IterT (VarT "datatype") List))
      (typfield (Atom ELEMS) (IterT (VarT "elemtype") List))
      (typfield (Atom LOCALS) (IterT (VarT "localtype") List))
      (typfield (Atom LABELS) (IterT (VarT "resulttype") List))
      (typfield (Atom RETURN) (IterT (VarT "resulttype") Opt))
      (typfield (Atom REFS) (IterT (VarT "funcidx") List))
      (typfield (Atom RECS) (IterT (VarT "subtype") List))
    )
  )
)
HintD
HintD
(RecD
  (DecD
    "with_locals"
    (ExpP "context" (VarT "context"))
    (ExpP "_" (IterT (VarT "localidx") List))
    (ExpP "_" (IterT (VarT "localtype") List))
    (VarT "context")
    (DefD
      (ExpP "C" (VarT "context"))
      (ExpA (VarE "C"))
      (ExpA (ListE))
      (ExpA (ListE))
      (VarE "C")
    )
    (DefD
      (ExpP "C" (VarT "context"))
      (ExpP "x_1" (VarT "uN" (ExpA (NumE (Nat 32)))))
      (ExpP "x*" (IterT (VarT "idx") List))
      (ExpP "lct_1" (VarT "localtype"))
      (ExpP "lct*" (IterT (VarT "localtype") List))
      (ExpA (VarE "C"))
      (ExpA
        (CatE
          (ListE (VarE "x_1"))
          (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
        )
      )
      (ExpA
        (CatE
          (ListE (VarE "lct_1"))
          (IterE (VarE "lct") List (iterexp "lct" (VarE "lct*")))
        )
      )
      (CallE
        "with_locals"
        (ExpA
          (UpdE
            (VarE "C")
            (IdxP
              (DotP RootP (Atom LOCALS))
              (ProjE (UncaseE (VarE "x_1") Arg) 0)
            )
            (VarE "lct_1")
          )
        )
        (ExpA (IterE (VarE "x") List (iterexp "x" (VarE "x*"))))
        (ExpA (IterE (VarE "lct") List (iterexp "lct" (VarE "lct*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "clos_deftypes"
    (ExpP "_" (IterT (VarT "deftype") List))
    (IterT (VarT "deftype") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "dt*" (IterT (VarT "deftype") List))
      (ExpP "dt_n" (VarT "deftype"))
      (ExpA
        (CatE
          (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
          (ListE (VarE "dt_n"))
        )
      )
      (CatE
        (IterE (VarE "dt'") List (iterexp "dt'" (VarE "dt'*")))
        (ListE
          (CallE
            "subst_all_deftype"
            (ExpA (VarE "dt_n"))
            (ExpA
              (IterE
                (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt'"))
                List
                (iterexp "dt'" (VarE "dt'*"))
              )
            )
          )
        )
      )
      (LetPr
        (IterE (VarE "dt'") List (iterexp "dt'" (VarE "dt'*")))
        (CallE
          "clos_deftypes"
          (ExpA (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*"))))
        )
      )
    )
  )
)
(DecD
  "clos_valtype"
  (ExpP "context" (VarT "context"))
  (ExpP "valtype" (VarT "valtype"))
  (VarT "valtype")
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (ExpA (VarE "C"))
    (ExpA (VarE "t"))
    (CallE
      "subst_all_valtype"
      (ExpA (VarE "t"))
      (ExpA
        (IterE
          (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt"))
          List
          (iterexp "dt" (VarE "dt*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
      (CallE "clos_deftypes" (ExpA (DotE (VarE "C") (Atom TYPES))))
    )
  )
)
HintD
(DecD
  "clos_deftype"
  (ExpP "context" (VarT "context"))
  (ExpP "deftype" (VarT "deftype"))
  (VarT "deftype")
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "dt" (VarT "deftype"))
    (ExpA (VarE "C"))
    (ExpA (VarE "dt"))
    (CallE
      "subst_all_deftype"
      (ExpA (VarE "dt"))
      (ExpA
        (IterE
          (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt'"))
          List
          (iterexp "dt'" (VarE "dt'*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "dt'") List (iterexp "dt'" (VarE "dt'*")))
      (CallE "clos_deftypes" (ExpA (DotE (VarE "C") (Atom TYPES))))
    )
  )
)
HintD
(DecD
  "clos_tagtype"
  (ExpP "context" (VarT "context"))
  (ExpP "tagtype" (VarT "tagtype"))
  (VarT "tagtype")
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "jt" (VarT "typeuse"))
    (ExpA (VarE "C"))
    (ExpA (VarE "jt"))
    (CallE
      "subst_all_tagtype"
      (ExpA (VarE "jt"))
      (ExpA
        (IterE
          (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt"))
          List
          (iterexp "dt" (VarE "dt*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
      (CallE "clos_deftypes" (ExpA (DotE (VarE "C") (Atom TYPES))))
    )
  )
)
HintD
(DecD
  "clos_externtype"
  (ExpP "context" (VarT "context"))
  (ExpP "externtype" (VarT "externtype"))
  (VarT "externtype")
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "xt" (VarT "externtype"))
    (ExpA (VarE "C"))
    (ExpA (VarE "xt"))
    (CallE
      "subst_all_externtype"
      (ExpA (VarE "xt"))
      (ExpA
        (IterE
          (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt"))
          List
          (iterexp "dt" (VarE "dt*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
      (CallE "clos_deftypes" (ExpA (DotE (VarE "C") (Atom TYPES))))
    )
  )
)
HintD
(DecD
  "clos_moduletype"
  (ExpP "context" (VarT "context"))
  (ExpP "moduletype" (VarT "moduletype"))
  (VarT "moduletype")
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "mmt" (VarT "moduletype"))
    (ExpA (VarE "C"))
    (ExpA (VarE "mmt"))
    (CallE
      "subst_all_moduletype"
      (ExpA (VarE "mmt"))
      (ExpA
        (IterE
          (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt"))
          List
          (iterexp "dt" (VarE "dt*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
      (CallE "clos_deftypes" (ExpA (DotE (VarE "C") (Atom TYPES))))
    )
  )
)
HintD
HintD
(RelD
  "Numtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "numtype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "numtype" (VarT "numtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (VarE "numtype"))
  )
)
HintD
(RelD
  "Vectype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "vectype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "vectype" (VarT "vectype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (VarE "vectype"))
  )
)
HintD
(TypD
  "oktypenat"
  (InstD (VariantT (typcase (Seq (Atom OK) Arg) (TupT (typbind "_" nat)))))
)
(RelD
  "Packtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "packtype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "packtype" (VarT "packtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (VarE "packtype"))
  )
)
(RelD
  "Packtype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "packtype"))
    (typbind "_" (VarT "packtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "packtype" (VarT "packtype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE (VarE "C") (VarE "packtype") (VarE "packtype"))
  )
)
(RelD
  "Numtype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "numtype"))
    (typbind "_" (VarT "numtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "numtype" (VarT "numtype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE (VarE "C") (VarE "numtype") (VarE "numtype"))
  )
)
(RelD
  "Expand"
  (Infix Arg ~~ Arg)
  (TupT (typbind "_" (VarT "deftype")) (typbind "_" (VarT "comptype")))
  (RuleD
    ""
    (ExpP "deftype" (VarT "deftype"))
    (ExpP "comptype" (VarT "comptype"))
    (ExpP "final?" (IterT (VarT "final") Opt))
    (ExpP "typeuse*" (IterT (VarT "typeuse") List))
    (Infix Arg ~~ Arg)
    (TupE (VarE "deftype") (VarE "comptype"))
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "unrolldt" (ExpA (VarE "deftype")))
        (CaseE
          (Seq (Atom SUB) Arg Arg Arg)
          (TupE
            (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
            (IterE (VarE "typeuse") List (iterexp "typeuse" (VarE "typeuse*")))
            (VarE "comptype")
          )
        )
      )
    )
  )
)
(RelD
  "Vectype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "vectype"))
    (typbind "_" (VarT "vectype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "vectype" (VarT "vectype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE (VarE "C") (VarE "vectype") (VarE "vectype"))
  )
)
(DecD
  "before"
  (ExpP "typeuse" (VarT "typeuse"))
  (ExpP "nat" nat)
  BoolT
  (DefD
    (ExpP "j" nat)
    (ExpP "i" nat)
    (ExpA (CaseE (Seq (Atom REC) Arg) (TupE (VarE "j"))))
    (ExpA (VarE "i"))
    (CmpE LtOp nat (VarE "j") (VarE "i"))
  )
  (DefD
    (ExpP "typeuse" (VarT "typeuse"))
    (ExpP "i" nat)
    (ExpA (VarE "typeuse"))
    (ExpA (VarE "i"))
    (BoolE true)
  )
)
(DecD
  "unrollht_"
  (ExpP "context" (VarT "context"))
  (ExpP "heaptype" (VarT "heaptype"))
  (VarT "subtype")
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "deftype" (VarT "deftype"))
    (ExpA (VarE "C"))
    (ExpA (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype")))
    (CallE "unrolldt" (ExpA (VarE "deftype")))
  )
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "typeidx" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "C"))
    (ExpA (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx"))))
    (CallE
      "unrolldt"
      (ExpA
        (IdxE
          (DotE (VarE "C") (Atom TYPES))
          (ProjE (UncaseE (VarE "typeidx") Arg) 0)
        )
      )
    )
  )
  (DefD
    (ExpP "C" (VarT "context"))
    (ExpP "i" nat)
    (ExpA (VarE "C"))
    (ExpA (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i"))))
    (IdxE (DotE (VarE "C") (Atom RECS)) (VarE "i"))
  )
)
(RecD
  (RelD
    "Heaptype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "heaptype")))
    (RuleD
      "abs"
      (ExpP "C" (VarT "context"))
      (ExpP "absheaptype" (VarT "absheaptype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "absheaptype") (VarT "heaptype") (VarE "absheaptype"))
      )
    )
    (RuleD
      "typeuse"
      (ExpP "C" (VarT "context"))
      (ExpP "typeuse" (VarT "typeuse"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "typeuse") (VarT "heaptype") (VarE "typeuse"))
      )
      (RulePr
        "Typeuse_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "typeuse"))
      )
    )
    (RuleD
      "bot"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (CaseE (Atom BOT) (TupE)))
    )
  )
  (RelD
    "Reftype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "reftype")))
    (RuleD
      ""
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (IterE (CaseE (Atom NULL) (TupE)) Opt) (VarE "heaptype"))
        )
      )
      (RulePr
        "Heaptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "heaptype"))
      )
    )
  )
  (RelD
    "Valtype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "valtype")))
    (RuleD
      "num"
      (ExpP "C" (VarT "context"))
      (ExpP "numtype" (VarT "numtype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype"))
      )
      (RulePr
        "Numtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "numtype"))
      )
    )
    (RuleD
      "vec"
      (ExpP "C" (VarT "context"))
      (ExpP "vectype" (VarT "vectype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype"))
      )
      (RulePr
        "Vectype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "vectype"))
      )
    )
    (RuleD
      "ref"
      (ExpP "C" (VarT "context"))
      (ExpP "reftype" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "reftype") (VarT "valtype") (VarE "reftype"))
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "reftype"))
      )
    )
    (RuleD
      "bot"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (CaseE (Atom BOT) (TupE)))
    )
  )
  (RelD
    "Typeuse_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "typeuse")))
    (RuleD
      "typeidx"
      (ExpP "C" (VarT "context"))
      (ExpP "typeidx" (VarT "typeidx"))
      (ExpP "dt" (VarT "deftype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx"))))
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "typeidx") Arg) 0)
          )
          (VarE "dt")
        )
      )
    )
    (RuleD
      "rec"
      (ExpP "C" (VarT "context"))
      (ExpP "i" (VarT "n"))
      (ExpP "st" (VarT "subtype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i"))))
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom RECS)) (VarE "i"))
          (VarE "st")
        )
      )
    )
    (RuleD
      "deftype"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype" (VarT "deftype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype"))
      )
      (RulePr
        "Deftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "deftype"))
      )
    )
  )
  (RelD
    "Resulttype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "resulttype")))
    (RuleD
      ""
      (ExpP "C" (VarT "context"))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
      )
      (IterPr
        (RulePr
          "Valtype_ok"
          (Infix Arg |- (Infix Arg : (Atom OK)))
          (TupE (VarE "C") (VarE "t"))
        )
        List
        (iterexp "t" (VarE "t*"))
      )
    )
  )
  (RelD
    "Fieldtype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "fieldtype")))
    (RuleD
      ""
      (ExpP "C" (VarT "context"))
      (ExpP "storagetype" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE
          (Seq Arg Arg)
          (TupE (IterE (CaseE (Atom MUT) (TupE)) Opt) (VarE "storagetype"))
        )
      )
      (RulePr
        "Storagetype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "storagetype"))
      )
    )
  )
  (RelD
    "Storagetype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "storagetype")))
    (RuleD
      "val"
      (ExpP "C" (VarT "context"))
      (ExpP "valtype" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype"))
      )
      (RulePr
        "Valtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "valtype"))
      )
    )
    (RuleD
      "pack"
      (ExpP "C" (VarT "context"))
      (ExpP "packtype" (VarT "packtype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype"))
      )
      (RulePr
        "Packtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "packtype"))
      )
    )
  )
  (RelD
    "Comptype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "comptype")))
    (RuleD
      "struct"
      (ExpP "C" (VarT "context"))
      (ExpP "fieldtype*" (IterT (VarT "fieldtype") List))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STRUCT) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (VarE "fieldtype")
                  List
                  (iterexp "fieldtype" (VarE "fieldtype*"))
                )
              )
            )
          )
        )
      )
      (IterPr
        (RulePr
          "Fieldtype_ok"
          (Infix Arg |- (Infix Arg : (Atom OK)))
          (TupE (VarE "C") (VarE "fieldtype"))
        )
        List
        (iterexp "fieldtype" (VarE "fieldtype*"))
      )
    )
    (RuleD
      "array"
      (ExpP "C" (VarT "context"))
      (ExpP "fieldtype" (VarT "fieldtype"))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "fieldtype"))))
      (RulePr
        "Fieldtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "fieldtype"))
      )
    )
    (RuleD
      "func"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Resulttype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
          )
        )
      )
      (RulePr
        "Resulttype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
          )
        )
      )
    )
  )
  (RelD
    "Subtype_ok2"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "subtype"))
      (typbind "_" (VarT "oktypenat"))
    )
    (RuleD
      ""
      (ExpP "C" (VarT "context"))
      (ExpP "typeuse*" (IterT (VarT "typeuse") List))
      (ExpP "comptype" (VarT "comptype"))
      (ExpP "i" nat)
      (ExpP "comptype'*" (IterT (VarT "comptype") List))
      (ExpP "typeuse'**" (IterT (IterT (VarT "typeuse") List) List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom SUB) Arg Arg Arg)
          (TupE
            (IterE (CaseE (Atom FINAL) (TupE)) Opt)
            (IterE (VarE "typeuse") List (iterexp "typeuse" (VarE "typeuse*")))
            (VarE "comptype")
          )
        )
        (CaseE (Seq (Atom OK) Arg) (TupE (VarE "i")))
      )
      (IfPr
        (CmpE
          LeOp
          nat
          (LenE
            (IterE (VarE "typeuse") List (iterexp "typeuse" (VarE "typeuse*")))
          )
          (NumE (Nat 1))
        )
      )
      (IterPr
        (RulePr
          "Typeuse_ok"
          (Infix Arg |- (Infix Arg : (Atom OK)))
          (TupE (VarE "C") (VarE "typeuse"))
        )
        List
        (iterexp "typeuse" (VarE "typeuse*"))
      )
      (IterPr
        (IfPr (CallE "before" (ExpA (VarE "typeuse")) (ExpA (VarE "i"))))
        List
        (iterexp "typeuse" (VarE "typeuse*"))
      )
      (IterPr
        (IfPr
          (CmpE
            EqOp
            bool
            (CallE
              "unrollht_"
              (ExpA (VarE "C"))
              (ExpA (SubE (VarT "typeuse") (VarT "heaptype") (VarE "typeuse")))
            )
            (CaseE
              (Seq (Atom SUB) Arg Arg Arg)
              (TupE
                (OptE)
                (IterE
                  (VarE "typeuse'")
                  List
                  (iterexp "typeuse'" (VarE "typeuse'*"))
                )
                (VarE "comptype'")
              )
            )
          )
        )
        List
        (iterexp "comptype'" (VarE "comptype'*"))
        (iterexp "typeuse" (VarE "typeuse*"))
        (iterexp "typeuse'*" (VarE "typeuse'**"))
      )
      (RulePr
        "Comptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "comptype"))
      )
      (IterPr
        (RulePr
          "Comptype_sub"
          (Infix Arg |- (Infix Arg <: Arg))
          (TupE (VarE "C") (VarE "comptype") (VarE "comptype'"))
        )
        List
        (iterexp "comptype'" (VarE "comptype'*"))
      )
    )
  )
  (RelD
    "Rectype_ok2"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "rectype"))
      (typbind "_" (VarT "oktypenat"))
    )
    (RuleD
      "empty"
      (ExpP "C" (VarT "context"))
      (ExpP "i" nat)
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REC) Arg) (TupE (CaseE Arg (TupE (ListE)))))
        (CaseE (Seq (Atom OK) Arg) (TupE (VarE "i")))
      )
    )
    (RuleD
      "cons"
      (ExpP "C" (VarT "context"))
      (ExpP "subtype_1" (VarT "subtype"))
      (ExpP "subtype*" (IterT (VarT "subtype") List))
      (ExpP "i" nat)
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (ListE (VarE "subtype_1"))
                  (IterE
                    (VarE "subtype")
                    List
                    (iterexp "subtype" (VarE "subtype*"))
                  )
                )
              )
            )
          )
        )
        (CaseE (Seq (Atom OK) Arg) (TupE (VarE "i")))
      )
      (RulePr
        "Subtype_ok2"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "subtype_1")
          (CaseE (Seq (Atom OK) Arg) (TupE (VarE "i")))
        )
      )
      (RulePr
        "Rectype_ok2"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (CaseE
            (Seq (Atom REC) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (VarE "subtype")
                    List
                    (iterexp "subtype" (VarE "subtype*"))
                  )
                )
              )
            )
          )
          (CaseE
            (Seq (Atom OK) Arg)
            (TupE (BinE AddOp nat (VarE "i") (NumE (Nat 1))))
          )
        )
      )
    )
  )
  (RelD
    "Deftype_ok"
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "deftype")))
    (RuleD
      ""
      (ExpP "C" (VarT "context"))
      (ExpP "rectype" (VarT "rectype"))
      (ExpP "i" (VarT "n"))
      (ExpP "n" (VarT "n"))
      (ExpP "subtype*" (IterT (VarT "subtype") List))
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom _DEF) Arg Arg) (TupE (VarE "rectype") (VarE "i")))
      )
      (RulePr
        "Rectype_ok2"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield (Atom LABELS) (ListE))
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield
                (Atom RECS)
                (IterE
                  (VarE "subtype")
                  (ListN (VarE "n"))
                  (iterexp "subtype" (VarE "subtype*"))
                )
              )
            )
            (VarE "C")
          )
          (VarE "rectype")
          (CaseE (Seq (Atom OK) Arg) (TupE (NumE (Nat 0))))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (VarE "rectype")
          (CaseE
            (Seq (Atom REC) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (VarE "subtype")
                    (ListN (VarE "n"))
                    (iterexp "subtype" (VarE "subtype*"))
                  )
                )
              )
            )
          )
        )
      )
      (IfPr (CmpE LtOp nat (VarE "i") (VarE "n")))
    )
  )
  (RelD
    "Comptype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "comptype"))
      (typbind "_" (VarT "comptype"))
    )
    (RuleD
      "struct"
      (ExpP "C" (VarT "context"))
      (ExpP "ft_1*" (IterT (VarT "fieldtype") List))
      (ExpP "ft'_1*" (IterT (VarT "fieldtype") List))
      (ExpP "ft_2*" (IterT (VarT "fieldtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STRUCT) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "ft_1") List (iterexp "ft_1" (VarE "ft_1*")))
                  (IterE (VarE "ft'_1") List (iterexp "ft'_1" (VarE "ft'_1*")))
                )
              )
            )
          )
        )
        (CaseE
          (Seq (Atom STRUCT) Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "ft_2") List (iterexp "ft_2" (VarE "ft_2*"))))
            )
          )
        )
      )
      (IterPr
        (RulePr
          "Fieldtype_sub"
          (Infix Arg |- (Infix Arg <: Arg))
          (TupE (VarE "C") (VarE "ft_1") (VarE "ft_2"))
        )
        List
        (iterexp "ft_1" (VarE "ft_1*"))
        (iterexp "ft_2" (VarE "ft_2*"))
      )
    )
    (RuleD
      "array"
      (ExpP "C" (VarT "context"))
      (ExpP "ft_1" (VarT "fieldtype"))
      (ExpP "ft_2" (VarT "fieldtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "ft_1")))
        (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "ft_2")))
      )
      (RulePr
        "Fieldtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "ft_1") (VarE "ft_2"))
      )
    )
    (RuleD
      "func"
      (ExpP "C" (VarT "context"))
      (ExpP "t_11*" (IterT (VarT "valtype") List))
      (ExpP "t_12*" (IterT (VarT "valtype") List))
      (ExpP "t_21*" (IterT (VarT "valtype") List))
      (ExpP "t_22*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_11") List (iterexp "t_11" (VarE "t_11*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_12") List (iterexp "t_12" (VarE "t_12*"))))
            )
          )
        )
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_21") List (iterexp "t_21" (VarE "t_21*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_22") List (iterexp "t_22" (VarE "t_22*"))))
            )
          )
        )
      )
      (RulePr
        "Resulttype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_21") List (iterexp "t_21" (VarE "t_21*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "t_11") List (iterexp "t_11" (VarE "t_11*"))))
          )
        )
      )
      (RulePr
        "Resulttype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_12") List (iterexp "t_12" (VarE "t_12*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "t_22") List (iterexp "t_22" (VarE "t_22*"))))
          )
        )
      )
    )
  )
  (RelD
    "Deftype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "deftype"))
      (typbind "_" (VarT "deftype"))
    )
    (RuleD
      "refl"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype_1" (VarT "deftype"))
      (ExpP "deftype_2" (VarT "deftype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "deftype_1") (VarE "deftype_2"))
      (IfPr
        (CmpE
          EqOp
          bool
          (CallE "clos_deftype" (ExpA (VarE "C")) (ExpA (VarE "deftype_1")))
          (CallE "clos_deftype" (ExpA (VarE "C")) (ExpA (VarE "deftype_2")))
        )
      )
    )
    (RuleD
      "super"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype_1" (VarT "deftype"))
      (ExpP "deftype_2" (VarT "deftype"))
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "typeuse*" (IterT (VarT "typeuse") List))
      (ExpP "ct" (VarT "comptype"))
      (ExpP "i" nat)
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "deftype_1") (VarE "deftype_2"))
      (IfPr
        (CmpE
          EqOp
          bool
          (CallE "unrolldt" (ExpA (VarE "deftype_1")))
          (CaseE
            (Seq (Atom SUB) Arg Arg Arg)
            (TupE
              (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
              (IterE
                (VarE "typeuse")
                List
                (iterexp "typeuse" (VarE "typeuse*"))
              )
              (VarE "ct")
            )
          )
        )
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (SubE
            (VarT "typeuse")
            (VarT "heaptype")
            (IdxE
              (IterE
                (VarE "typeuse")
                List
                (iterexp "typeuse" (VarE "typeuse*"))
              )
              (VarE "i")
            )
          )
          (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype_2"))
        )
      )
    )
  )
  (RelD
    "Heaptype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "heaptype"))
      (typbind "_" (VarT "heaptype"))
    )
    (RuleD
      "refl"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "heaptype") (VarE "heaptype"))
    )
    (RuleD
      "trans"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype_1" (VarT "heaptype"))
      (ExpP "heaptype_2" (VarT "heaptype"))
      (ExpP "heaptype'" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "heaptype_1") (VarE "heaptype_2"))
      (RulePr
        "Heaptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "heaptype'"))
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "heaptype_1") (VarE "heaptype'"))
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "heaptype'") (VarE "heaptype_2"))
      )
    )
    (RuleD
      "eq-any"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom EQ) (TupE)) (CaseE (Atom ANY) (TupE)))
    )
    (RuleD
      "i31-eq"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom I31) (TupE)) (CaseE (Atom EQ) (TupE)))
    )
    (RuleD
      "struct-eq"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom STRUCT) (TupE)) (CaseE (Atom EQ) (TupE)))
    )
    (RuleD
      "array-eq"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom ARRAY) (TupE)) (CaseE (Atom EQ) (TupE)))
    )
    (RuleD
      "struct"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype" (VarT "deftype"))
      (ExpP "fieldtype*" (IterT (VarT "fieldtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype"))
        (CaseE (Atom STRUCT) (TupE))
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (VarE "deftype")
          (CaseE
            (Seq (Atom STRUCT) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (VarE "fieldtype")
                    List
                    (iterexp "fieldtype" (VarE "fieldtype*"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "array"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype" (VarT "deftype"))
      (ExpP "fieldtype" (VarT "fieldtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype"))
        (CaseE (Atom ARRAY) (TupE))
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (VarE "deftype")
          (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "fieldtype")))
        )
      )
    )
    (RuleD
      "func"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype" (VarT "deftype"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype"))
        (CaseE (Atom FUNC) (TupE))
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (VarE "deftype")
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "def"
      (ExpP "C" (VarT "context"))
      (ExpP "deftype_1" (VarT "deftype"))
      (ExpP "deftype_2" (VarT "deftype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype_1"))
        (SubE (VarT "deftype") (VarT "heaptype") (VarE "deftype_2"))
      )
      (RulePr
        "Deftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "deftype_1") (VarE "deftype_2"))
      )
    )
    (RuleD
      "typeidx-l"
      (ExpP "C" (VarT "context"))
      (ExpP "typeidx" (VarT "typeidx"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx")))
        (VarE "heaptype")
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (SubE
            (VarT "deftype")
            (VarT "heaptype")
            (IdxE
              (DotE (VarE "C") (Atom TYPES))
              (ProjE (UncaseE (VarE "typeidx") Arg) 0)
            )
          )
          (VarE "heaptype")
        )
      )
    )
    (RuleD
      "typeidx-r"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (ExpP "typeidx" (VarT "typeidx"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (VarE "heaptype")
        (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx")))
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (VarE "heaptype")
          (SubE
            (VarT "deftype")
            (VarT "heaptype")
            (IdxE
              (DotE (VarE "C") (Atom TYPES))
              (ProjE (UncaseE (VarE "typeidx") Arg) 0)
            )
          )
        )
      )
    )
    (RuleD
      "rec-struct"
      (ExpP "C" (VarT "context"))
      (ExpP "i" (VarT "n"))
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "fieldtype*" (IterT (VarT "fieldtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i")))
        (CaseE (Atom STRUCT) (TupE))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom RECS)) (VarE "i"))
          (CaseE
            (Seq (Atom SUB) Arg Arg Arg)
            (TupE
              (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
              (ListE)
              (CaseE
                (Seq (Atom STRUCT) Arg)
                (TupE
                  (CaseE
                    Arg
                    (TupE
                      (IterE
                        (VarE "fieldtype")
                        List
                        (iterexp "fieldtype" (VarE "fieldtype*"))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "rec-array"
      (ExpP "C" (VarT "context"))
      (ExpP "i" (VarT "n"))
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "fieldtype" (VarT "fieldtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i")))
        (CaseE (Atom ARRAY) (TupE))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom RECS)) (VarE "i"))
          (CaseE
            (Seq (Atom SUB) Arg Arg Arg)
            (TupE
              (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
              (ListE)
              (CaseE (Seq (Atom ARRAY) Arg) (TupE (VarE "fieldtype")))
            )
          )
        )
      )
    )
    (RuleD
      "rec-func"
      (ExpP "C" (VarT "context"))
      (ExpP "i" (VarT "n"))
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i")))
        (CaseE (Atom FUNC) (TupE))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom RECS)) (VarE "i"))
          (CaseE
            (Seq (Atom SUB) Arg Arg Arg)
            (TupE
              (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
              (ListE)
              (CaseE
                (Infix (Seq (Atom FUNC) Arg) -> Arg)
                (TupE
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                    )
                  )
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "rec-sub"
      (ExpP "C" (VarT "context"))
      (ExpP "i" (VarT "n"))
      (ExpP "typeuse*" (IterT (VarT "typeuse") List))
      (ExpP "j" nat)
      (ExpP "final?" (IterT (VarT "final") Opt))
      (ExpP "ct" (VarT "comptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REC) Arg) (TupE (VarE "i")))
        (SubE
          (VarT "typeuse")
          (VarT "heaptype")
          (IdxE
            (IterE (VarE "typeuse") List (iterexp "typeuse" (VarE "typeuse*")))
            (VarE "j")
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "C") (Atom RECS)) (VarE "i"))
          (CaseE
            (Seq (Atom SUB) Arg Arg Arg)
            (TupE
              (IterE (VarE "final") Opt (iterexp "final" (VarE "final?")))
              (IterE
                (VarE "typeuse")
                List
                (iterexp "typeuse" (VarE "typeuse*"))
              )
              (VarE "ct")
            )
          )
        )
      )
    )
    (RuleD
      "none"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom NONE) (TupE)) (VarE "heaptype"))
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "heaptype") (CaseE (Atom ANY) (TupE)))
      )
      (IfPr (CmpE NeOp bool (VarE "heaptype") (CaseE (Atom BOT) (TupE))))
    )
    (RuleD
      "nofunc"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom NOFUNC) (TupE)) (VarE "heaptype"))
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "heaptype") (CaseE (Atom FUNC) (TupE)))
      )
      (IfPr (CmpE NeOp bool (VarE "heaptype") (CaseE (Atom BOT) (TupE))))
    )
    (RuleD
      "noexn"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom NOEXN) (TupE)) (VarE "heaptype"))
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "heaptype") (CaseE (Atom EXN) (TupE)))
      )
      (IfPr (CmpE NeOp bool (VarE "heaptype") (CaseE (Atom BOT) (TupE))))
    )
    (RuleD
      "noextern"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom NOEXTERN) (TupE)) (VarE "heaptype"))
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "heaptype") (CaseE (Atom EXTERN) (TupE)))
      )
      (IfPr (CmpE NeOp bool (VarE "heaptype") (CaseE (Atom BOT) (TupE))))
    )
    (RuleD
      "bot"
      (ExpP "C" (VarT "context"))
      (ExpP "heaptype" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom BOT) (TupE)) (VarE "heaptype"))
    )
  )
  (RelD
    "Reftype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "reftype"))
      (typbind "_" (VarT "reftype"))
    )
    (RuleD
      "nonnull"
      (ExpP "C" (VarT "context"))
      (ExpP "ht_1" (VarT "heaptype"))
      (ExpP "ht_2" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht_1")))
        (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht_2")))
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "ht_1") (VarE "ht_2"))
      )
    )
    (RuleD
      "null"
      (ExpP "C" (VarT "context"))
      (ExpP "ht_1" (VarT "heaptype"))
      (ExpP "ht_2" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (IterE (CaseE (Atom NULL) (TupE)) Opt) (VarE "ht_1"))
        )
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht_2"))
        )
      )
      (RulePr
        "Heaptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "ht_1") (VarE "ht_2"))
      )
    )
  )
  (RelD
    "Valtype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "valtype"))
      (typbind "_" (VarT "valtype"))
    )
    (RuleD
      "num"
      (ExpP "C" (VarT "context"))
      (ExpP "numtype_1" (VarT "numtype"))
      (ExpP "numtype_2" (VarT "numtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype_1"))
        (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype_2"))
      )
      (RulePr
        "Numtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "numtype_1") (VarE "numtype_2"))
      )
    )
    (RuleD
      "vec"
      (ExpP "C" (VarT "context"))
      (ExpP "vectype_1" (VarT "vectype"))
      (ExpP "vectype_2" (VarT "vectype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype_1"))
        (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype_2"))
      )
      (RulePr
        "Vectype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "vectype_1") (VarE "vectype_2"))
      )
    )
    (RuleD
      "ref"
      (ExpP "C" (VarT "context"))
      (ExpP "reftype_1" (VarT "reftype"))
      (ExpP "reftype_2" (VarT "reftype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "reftype") (VarT "valtype") (VarE "reftype_1"))
        (SubE (VarT "reftype") (VarT "valtype") (VarE "reftype_2"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "reftype_1") (VarE "reftype_2"))
      )
    )
    (RuleD
      "bot"
      (ExpP "C" (VarT "context"))
      (ExpP "valtype" (VarT "valtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (CaseE (Atom BOT) (TupE)) (VarE "valtype"))
    )
  )
  (RelD
    "Resulttype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "resulttype"))
      (typbind "_" (VarT "resulttype"))
    )
    (RuleD
      ""
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
        )
        (CaseE
          Arg
          (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
        )
      )
      (IterPr
        (RulePr
          "Valtype_sub"
          (Infix Arg |- (Infix Arg <: Arg))
          (TupE (VarE "C") (VarE "t_1") (VarE "t_2"))
        )
        List
        (iterexp "t_1" (VarE "t_1*"))
        (iterexp "t_2" (VarE "t_2*"))
      )
    )
  )
  (RelD
    "Storagetype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "storagetype"))
      (typbind "_" (VarT "storagetype"))
    )
    (RuleD
      "val"
      (ExpP "C" (VarT "context"))
      (ExpP "valtype_1" (VarT "valtype"))
      (ExpP "valtype_2" (VarT "valtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype_1"))
        (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype_2"))
      )
      (RulePr
        "Valtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "valtype_1") (VarE "valtype_2"))
      )
    )
    (RuleD
      "pack"
      (ExpP "C" (VarT "context"))
      (ExpP "packtype_1" (VarT "packtype"))
      (ExpP "packtype_2" (VarT "packtype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype_1"))
        (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype_2"))
      )
      (RulePr
        "Packtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "packtype_1") (VarE "packtype_2"))
      )
    )
  )
  (RelD
    "Fieldtype_sub"
    (Infix Arg |- (Infix Arg <: Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "fieldtype"))
      (typbind "_" (VarT "fieldtype"))
    )
    (RuleD
      "const"
      (ExpP "C" (VarT "context"))
      (ExpP "zt_1" (VarT "storagetype"))
      (ExpP "zt_2" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq Arg Arg) (TupE (OptE) (VarE "zt_1")))
        (CaseE (Seq Arg Arg) (TupE (OptE) (VarE "zt_2")))
      )
      (RulePr
        "Storagetype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "zt_1") (VarE "zt_2"))
      )
    )
    (RuleD
      "var"
      (ExpP "C" (VarT "context"))
      (ExpP "zt_1" (VarT "storagetype"))
      (ExpP "zt_2" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq Arg Arg)
          (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt_1"))
        )
        (CaseE
          (Seq Arg Arg)
          (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt_2"))
        )
      )
      (RulePr
        "Storagetype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "zt_1") (VarE "zt_2"))
      )
      (RulePr
        "Storagetype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "zt_2") (VarE "zt_1"))
      )
    )
  )
)
HintD
HintD
HintD
HintD
(RelD
  "Localtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "localtype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "init" (VarT "init"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq Arg Arg) (TupE (VarE "init") (VarE "t"))))
    (RulePr
      "Valtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "t"))
    )
  )
)
HintD
HintD
(RelD
  "Instrtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "instrtype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "x*" (IterT (VarT "idx") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (ExpP "lct*" (IterT (VarT "localtype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE
        (Infix Arg ->_ (Seq Arg Arg))
        (TupE
          (CaseE
            Arg
            (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
          )
          (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
          (CaseE
            Arg
            (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
          )
        )
      )
    )
    (RulePr
      "Resulttype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
        )
      )
    )
    (RulePr
      "Resulttype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
        )
      )
    )
    (IterPr
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (VarE "lct")
        )
      )
      List
      (iterexp "lct" (VarE "lct*"))
      (iterexp "x" (VarE "x*"))
    )
  )
)
HintD
HintD
(RelD
  "Expand_use"
  (Infix Arg ~~_ (Seq Arg Arg))
  (TupT
    (typbind "_" (VarT "typeuse"))
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "comptype"))
  )
  (RuleD
    "deftype"
    (ExpP "deftype" (VarT "deftype"))
    (ExpP "C" (VarT "context"))
    (ExpP "comptype" (VarT "comptype"))
    (Infix Arg ~~_ (Seq Arg Arg))
    (TupE
      (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype"))
      (VarE "C")
      (VarE "comptype")
    )
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE (VarE "deftype") (VarE "comptype"))
    )
  )
  (RuleD
    "typeidx"
    (ExpP "typeidx" (VarT "typeidx"))
    (ExpP "C" (VarT "context"))
    (ExpP "comptype" (VarT "comptype"))
    (Infix Arg ~~_ (Seq Arg Arg))
    (TupE
      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx")))
      (VarE "C")
      (VarE "comptype")
    )
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE
        (IdxE
          (DotE (VarE "C") (Atom TYPES))
          (ProjE (UncaseE (VarE "typeidx") Arg) 0)
        )
        (VarE "comptype")
      )
    )
  )
)
HintD
(TypD
  "oktypeidx"
  (InstD
    (VariantT
      (typcase (Seq (Atom OK) Arg) (TupT (typbind "typeidx" (VarT "typeidx"))))
    )
  )
)
HintD
HintD
HintD
HintD
HintD
HintD
(RelD
  "Subtype_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "subtype"))
    (typbind "_" (VarT "oktypeidx"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "x*" (IterT (VarT "idx") List))
    (ExpP "comptype" (VarT "comptype"))
    (ExpP "x_0" (VarT "idx"))
    (ExpP "comptype'*" (IterT (VarT "comptype") List))
    (ExpP "yy**" (IterT (IterT (VarT "typeuse") List) List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom SUB) Arg Arg Arg)
        (TupE
          (IterE (CaseE (Atom FINAL) (TupE)) Opt)
          (IterE
            (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
            List
            (iterexp "x" (VarE "x*"))
          )
          (VarE "comptype")
        )
      )
      (CaseE (Seq (Atom OK) Arg) (TupE (VarE "x_0")))
    )
    (IfPr
      (CmpE
        LeOp
        nat
        (LenE (IterE (VarE "x") List (iterexp "x" (VarE "x*"))))
        (NumE (Nat 1))
      )
    )
    (IterPr
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (UncaseE (VarE "x") Arg) 0)
          (ProjE (UncaseE (VarE "x_0") Arg) 0)
        )
      )
      List
      (iterexp "x" (VarE "x*"))
    )
    (IterPr
      (IfPr
        (CmpE
          EqOp
          bool
          (CallE
            "unrolldt"
            (ExpA
              (IdxE
                (DotE (VarE "C") (Atom TYPES))
                (ProjE (UncaseE (VarE "x") Arg) 0)
              )
            )
          )
          (CaseE
            (Seq (Atom SUB) Arg Arg Arg)
            (TupE
              (OptE)
              (IterE (VarE "yy") List (iterexp "yy" (VarE "yy*")))
              (VarE "comptype'")
            )
          )
        )
      )
      List
      (iterexp "comptype'" (VarE "comptype'*"))
      (iterexp "x" (VarE "x*"))
      (iterexp "yy*" (VarE "yy**"))
    )
    (RulePr
      "Comptype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "comptype"))
    )
    (IterPr
      (RulePr
        "Comptype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "comptype") (VarE "comptype'"))
      )
      List
      (iterexp "comptype'" (VarE "comptype'*"))
    )
  )
)
HintD
(RecD
  (RelD
    "Rectype_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "rectype"))
      (typbind "_" (VarT "oktypeidx"))
    )
    (RuleD
      "empty"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REC) Arg) (TupE (CaseE Arg (TupE (ListE)))))
        (CaseE (Seq (Atom OK) Arg) (TupE (VarE "x")))
      )
    )
    (RuleD
      "cons"
      (ExpP "C" (VarT "context"))
      (ExpP "subtype_1" (VarT "subtype"))
      (ExpP "subtype*" (IterT (VarT "subtype") List))
      (ExpP "x" (VarT "idx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom REC) Arg)
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (ListE (VarE "subtype_1"))
                  (IterE
                    (VarE "subtype")
                    List
                    (iterexp "subtype" (VarE "subtype*"))
                  )
                )
              )
            )
          )
        )
        (CaseE (Seq (Atom OK) Arg) (TupE (VarE "x")))
      )
      (RulePr
        "Subtype_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "subtype_1")
          (CaseE (Seq (Atom OK) Arg) (TupE (VarE "x")))
        )
      )
      (RulePr
        "Rectype_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (CaseE
            (Seq (Atom REC) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (VarE "subtype")
                    List
                    (iterexp "subtype" (VarE "subtype*"))
                  )
                )
              )
            )
          )
          (CaseE
            (Seq (Atom OK) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (BinE
                    AddOp
                    nat
                    (ProjE (UncaseE (VarE "x") Arg) 0)
                    (NumE (Nat 1))
                  )
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
HintD
HintD
HintD
HintD
HintD
HintD
(RelD
  "Limits_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "limits"))
    (typbind "_" nat)
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "n" (VarT "n"))
    (ExpP "m?" (IterT (VarT "m") Opt))
    (ExpP "k" nat)
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n")))
          (IterE (CaseE Arg (TupE (VarE "m"))) Opt (iterexp "m" (VarE "m?")))
        )
      )
      (VarE "k")
    )
    (IfPr (CmpE LeOp nat (VarE "n") (VarE "k")))
    (IterPr
      (IfPr
        (BinE
          AndOp
          bool
          (CmpE LeOp nat (VarE "n") (VarE "m"))
          (CmpE LeOp nat (VarE "m") (VarE "k"))
        )
      )
      Opt
      (iterexp "m" (VarE "m?"))
    )
  )
)
HintD
(RelD
  "Tagtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "tagtype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "typeuse" (VarT "typeuse"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (VarE "typeuse"))
    (RulePr
      "Typeuse_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "typeuse"))
    )
    (RulePr
      "Expand_use"
      (Infix Arg ~~_ (Seq Arg Arg))
      (TupE
        (VarE "typeuse")
        (VarE "C")
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
    )
  )
)
HintD
(RelD
  "Globaltype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "globaltype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq Arg Arg)
        (TupE (IterE (CaseE (Atom MUT) (TupE)) Opt) (VarE "t"))
      )
    )
    (RulePr
      "Valtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "t"))
    )
  )
)
HintD
(RelD
  "Memtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "memtype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpP "limits" (VarT "limits"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "addrtype") (VarE "limits")))
    )
    (RulePr
      "Limits_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (VarE "limits")
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
              (CvtE
                nat
                int
                (CallE
                  "size"
                  (ExpA
                    (SubE (VarT "addrtype") (VarT "numtype") (VarE "addrtype"))
                  )
                )
              )
              (CvtE nat int (NumE (Nat 16)))
            )
          )
        )
      )
    )
  )
)
HintD
(RelD
  "Tabletype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "tabletype")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpP "limits" (VarT "limits"))
    (ExpP "reftype" (VarT "reftype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq Arg Arg Arg)
        (TupE (VarE "addrtype") (VarE "limits") (VarE "reftype"))
      )
    )
    (RulePr
      "Limits_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (VarE "limits")
        (CvtE
          int
          nat
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
                (CallE
                  "size"
                  (ExpA
                    (SubE (VarT "addrtype") (VarT "numtype") (VarE "addrtype"))
                  )
                )
              )
            )
            (CvtE nat int (NumE (Nat 1)))
          )
        )
      )
    )
    (RulePr
      "Reftype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "reftype"))
    )
  )
)
HintD
(RelD
  "Externtype_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "externtype")))
  (RuleD
    "tag"
    (ExpP "C" (VarT "context"))
    (ExpP "tagtype" (VarT "tagtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagtype"))))
    (RulePr
      "Tagtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "tagtype"))
    )
  )
  (RuleD
    "global"
    (ExpP "C" (VarT "context"))
    (ExpP "globaltype" (VarT "globaltype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype"))))
    (RulePr
      "Globaltype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "globaltype"))
    )
  )
  (RuleD
    "mem"
    (ExpP "C" (VarT "context"))
    (ExpP "memtype" (VarT "memtype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype"))))
    (RulePr
      "Memtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "memtype"))
    )
  )
  (RuleD
    "table"
    (ExpP "C" (VarT "context"))
    (ExpP "tabletype" (VarT "tabletype"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    (RulePr
      "Tabletype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "tabletype"))
    )
  )
  (RuleD
    "func"
    (ExpP "C" (VarT "context"))
    (ExpP "typeuse" (VarT "typeuse"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "typeuse"))))
    (RulePr
      "Typeuse_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "typeuse"))
    )
    (RulePr
      "Expand_use"
      (Infix Arg ~~_ (Seq Arg Arg))
      (TupE
        (VarE "typeuse")
        (VarE "C")
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
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
(RelD
  "Instrtype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "instrtype"))
    (typbind "_" (VarT "instrtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "t_11*" (IterT (VarT "valtype") List))
    (ExpP "x_1*" (IterT (VarT "idx") List))
    (ExpP "t_12*" (IterT (VarT "valtype") List))
    (ExpP "t_21*" (IterT (VarT "valtype") List))
    (ExpP "x_2*" (IterT (VarT "idx") List))
    (ExpP "t_22*" (IterT (VarT "valtype") List))
    (ExpP "x*" (IterT (VarT "idx") List))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Infix Arg ->_ (Seq Arg Arg))
        (TupE
          (CaseE
            Arg
            (TupE (IterE (VarE "t_11") List (iterexp "t_11" (VarE "t_11*"))))
          )
          (IterE (VarE "x_1") List (iterexp "x_1" (VarE "x_1*")))
          (CaseE
            Arg
            (TupE (IterE (VarE "t_12") List (iterexp "t_12" (VarE "t_12*"))))
          )
        )
      )
      (CaseE
        (Infix Arg ->_ (Seq Arg Arg))
        (TupE
          (CaseE
            Arg
            (TupE (IterE (VarE "t_21") List (iterexp "t_21" (VarE "t_21*"))))
          )
          (IterE (VarE "x_2") List (iterexp "x_2" (VarE "x_2*")))
          (CaseE
            Arg
            (TupE (IterE (VarE "t_22") List (iterexp "t_22" (VarE "t_22*"))))
          )
        )
      )
    )
    (RulePr
      "Resulttype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE (IterE (VarE "t_21") List (iterexp "t_21" (VarE "t_21*"))))
        )
        (CaseE
          Arg
          (TupE (IterE (VarE "t_11") List (iterexp "t_11" (VarE "t_11*"))))
        )
      )
    )
    (RulePr
      "Resulttype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE (IterE (VarE "t_12") List (iterexp "t_12" (VarE "t_12*"))))
        )
        (CaseE
          Arg
          (TupE (IterE (VarE "t_22") List (iterexp "t_22" (VarE "t_22*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
        (CallE
          "setminus_"
          (TypA (VarT "localidx"))
          (ExpA (IterE (VarE "x_2") List (iterexp "x_2" (VarE "x_2*"))))
          (ExpA (IterE (VarE "x_1") List (iterexp "x_1" (VarE "x_1*"))))
        )
      )
    )
    (IterPr
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg) (TupE (CaseE (Atom SET) (TupE)) (VarE "t")))
        )
      )
      List
      (iterexp "t" (VarE "t*"))
      (iterexp "x" (VarE "x*"))
    )
  )
)
HintD
HintD
HintD
HintD
(RelD
  "Limits_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "limits"))
    (typbind "_" (VarT "limits"))
  )
  (RuleD
    "max"
    (ExpP "C" (VarT "context"))
    (ExpP "n_1" (VarT "n"))
    (ExpP "m_1" (VarT "m"))
    (ExpP "n_2" (VarT "n"))
    (ExpP "m_2?" (IterT (VarT "m") Opt))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n_1")))
          (OptE (CaseE Arg (TupE (VarE "m_1"))))
        )
      )
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE
          (CaseE Arg (TupE (VarE "n_2")))
          (IterE
            (CaseE Arg (TupE (VarE "m_2")))
            Opt
            (iterexp "m_2" (VarE "m_2?"))
          )
        )
      )
    )
    (IfPr (CmpE GeOp nat (VarE "n_1") (VarE "n_2")))
    (IterPr
      (IfPr (CmpE LeOp nat (VarE "m_1") (VarE "m_2")))
      Opt
      (iterexp "m_2" (VarE "m_2?"))
    )
  )
  (RuleD
    "eps"
    (ExpP "C" (VarT "context"))
    (ExpP "n_1" (VarT "n"))
    (ExpP "n_2" (VarT "n"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE (CaseE Arg (TupE (VarE "n_1"))) (OptE))
      )
      (CaseE
        (Brack [ (Infix Arg .. Arg) ])
        (TupE (CaseE Arg (TupE (VarE "n_2"))) (OptE))
      )
    )
    (IfPr (CmpE GeOp nat (VarE "n_1") (VarE "n_2")))
  )
)
HintD
(RelD
  "Tagtype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "tagtype"))
    (typbind "_" (VarT "tagtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "deftype_1" (VarT "deftype"))
    (ExpP "deftype_2" (VarT "deftype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype_1"))
      (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype_2"))
    )
    (RulePr
      "Deftype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "deftype_1") (VarE "deftype_2"))
    )
    (RulePr
      "Deftype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "deftype_2") (VarE "deftype_1"))
    )
  )
)
HintD
(RelD
  "Globaltype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "globaltype"))
    (typbind "_" (VarT "globaltype"))
  )
  (RuleD
    "const"
    (ExpP "C" (VarT "context"))
    (ExpP "valtype_1" (VarT "valtype"))
    (ExpP "valtype_2" (VarT "valtype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq Arg Arg) (TupE (OptE) (VarE "valtype_1")))
      (CaseE (Seq Arg Arg) (TupE (OptE) (VarE "valtype_2")))
    )
    (RulePr
      "Valtype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "valtype_1") (VarE "valtype_2"))
    )
  )
  (RuleD
    "var"
    (ExpP "C" (VarT "context"))
    (ExpP "valtype_1" (VarT "valtype"))
    (ExpP "valtype_2" (VarT "valtype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq Arg Arg)
        (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "valtype_1"))
      )
      (CaseE
        (Seq Arg Arg)
        (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "valtype_2"))
      )
    )
    (RulePr
      "Valtype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "valtype_1") (VarE "valtype_2"))
    )
    (RulePr
      "Valtype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "valtype_2") (VarE "valtype_1"))
    )
  )
)
HintD
(RelD
  "Memtype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "memtype"))
    (typbind "_" (VarT "memtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpP "limits_1" (VarT "limits"))
    (ExpP "limits_2" (VarT "limits"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq Arg Arg (Atom PAGE))
        (TupE (VarE "addrtype") (VarE "limits_1"))
      )
      (CaseE
        (Seq Arg Arg (Atom PAGE))
        (TupE (VarE "addrtype") (VarE "limits_2"))
      )
    )
    (RulePr
      "Limits_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "limits_1") (VarE "limits_2"))
    )
  )
)
HintD
(RelD
  "Tabletype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "tabletype"))
    (typbind "_" (VarT "tabletype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "addrtype" (VarT "addrtype"))
    (ExpP "limits_1" (VarT "limits"))
    (ExpP "reftype_1" (VarT "reftype"))
    (ExpP "limits_2" (VarT "limits"))
    (ExpP "reftype_2" (VarT "reftype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq Arg Arg Arg)
        (TupE (VarE "addrtype") (VarE "limits_1") (VarE "reftype_1"))
      )
      (CaseE
        (Seq Arg Arg Arg)
        (TupE (VarE "addrtype") (VarE "limits_2") (VarE "reftype_2"))
      )
    )
    (RulePr
      "Limits_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "limits_1") (VarE "limits_2"))
    )
    (RulePr
      "Reftype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "reftype_1") (VarE "reftype_2"))
    )
    (RulePr
      "Reftype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "reftype_2") (VarE "reftype_1"))
    )
  )
)
HintD
(RelD
  "Externtype_sub"
  (Infix Arg |- (Infix Arg <: Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "externtype"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    "tag"
    (ExpP "C" (VarT "context"))
    (ExpP "tagtype_1" (VarT "tagtype"))
    (ExpP "tagtype_2" (VarT "tagtype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagtype_1")))
      (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagtype_2")))
    )
    (RulePr
      "Tagtype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "tagtype_1") (VarE "tagtype_2"))
    )
  )
  (RuleD
    "global"
    (ExpP "C" (VarT "context"))
    (ExpP "globaltype_1" (VarT "globaltype"))
    (ExpP "globaltype_2" (VarT "globaltype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype_1")))
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype_2")))
    )
    (RulePr
      "Globaltype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "globaltype_1") (VarE "globaltype_2"))
    )
  )
  (RuleD
    "mem"
    (ExpP "C" (VarT "context"))
    (ExpP "memtype_1" (VarT "memtype"))
    (ExpP "memtype_2" (VarT "memtype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype_1")))
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype_2")))
    )
    (RulePr
      "Memtype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "memtype_1") (VarE "memtype_2"))
    )
  )
  (RuleD
    "table"
    (ExpP "C" (VarT "context"))
    (ExpP "tabletype_1" (VarT "tabletype"))
    (ExpP "tabletype_2" (VarT "tabletype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype_1")))
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype_2")))
    )
    (RulePr
      "Tabletype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "tabletype_1") (VarE "tabletype_2"))
    )
  )
  (RuleD
    "func"
    (ExpP "C" (VarT "context"))
    (ExpP "deftype_1" (VarT "deftype"))
    (ExpP "deftype_2" (VarT "deftype"))
    (Infix Arg |- (Infix Arg <: Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom FUNC) Arg)
        (TupE (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype_1")))
      )
      (CaseE
        (Seq (Atom FUNC) Arg)
        (TupE (SubE (VarT "deftype") (VarT "typeuse") (VarE "deftype_2")))
      )
    )
    (RulePr
      "Deftype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "deftype_1") (VarE "deftype_2"))
    )
  )
)
HintD
(RelD
  "Blocktype_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "blocktype"))
    (typbind "_" (VarT "instrtype"))
  )
  (RuleD
    "valtype"
    (ExpP "C" (VarT "context"))
    (ExpP "valtype?" (IterT (VarT "valtype") Opt))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom _RESULT) Arg)
        (TupE
          (IterE (VarE "valtype") Opt (iterexp "valtype" (VarE "valtype?")))
        )
      )
      (CaseE
        (Infix Arg ->_ (Seq Arg Arg))
        (TupE
          (CaseE Arg (TupE (ListE)))
          (ListE)
          (CaseE
            Arg
            (TupE
              (LiftE
                (IterE
                  (VarE "valtype")
                  Opt
                  (iterexp "valtype" (VarE "valtype?"))
                )
              )
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "Valtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "valtype"))
      )
      Opt
      (iterexp "valtype" (VarE "valtype?"))
    )
  )
  (RuleD
    "typeidx"
    (ExpP "C" (VarT "context"))
    (ExpP "typeidx" (VarT "typeidx"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "typeidx")))
      (CaseE
        (Infix Arg ->_ (Seq Arg Arg))
        (TupE
          (CaseE
            Arg
            (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
          )
          (ListE)
          (CaseE
            Arg
            (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
          )
        )
      )
    )
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE
        (IdxE
          (DotE (VarE "C") (Atom TYPES))
          (ProjE (UncaseE (VarE "typeidx") Arg) 0)
        )
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
    )
  )
)
(RelD
  "Catch_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "catch")))
  (RuleD
    "catch"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "l" (VarT "labelidx"))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom CATCH) Arg Arg) (TupE (VarE "x") (VarE "l")))
    )
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE
        (CallE
          "as_deftype"
          (ExpA
            (IdxE
              (DotE (VarE "C") (Atom TAGS))
              (ProjE (UncaseE (VarE "x") Arg) 0)
            )
          )
        )
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
    )
    (RulePr
      "Resulttype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
        (IdxE
          (DotE (VarE "C") (Atom LABELS))
          (ProjE (UncaseE (VarE "l") Arg) 0)
        )
      )
    )
  )
  (RuleD
    "catch_ref"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "l" (VarT "labelidx"))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom CATCH_REF) Arg Arg) (TupE (VarE "x") (VarE "l")))
    )
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE
        (CallE
          "as_deftype"
          (ExpA
            (IdxE
              (DotE (VarE "C") (Atom TAGS))
              (ProjE (UncaseE (VarE "x") Arg) 0)
            )
          )
        )
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
    )
    (RulePr
      "Resulttype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE
            (CatE
              (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
              (ListE
                (CaseE
                  (Seq (Atom REF) Arg Arg)
                  (TupE (OptE) (CaseE (Atom EXN) (TupE)))
                )
              )
            )
          )
        )
        (IdxE
          (DotE (VarE "C") (Atom LABELS))
          (ProjE (UncaseE (VarE "l") Arg) 0)
        )
      )
    )
  )
  (RuleD
    "catch_all"
    (ExpP "C" (VarT "context"))
    (ExpP "l" (VarT "labelidx"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom CATCH_ALL) Arg) (TupE (VarE "l"))))
    (RulePr
      "Resulttype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE Arg (TupE (ListE)))
        (IdxE
          (DotE (VarE "C") (Atom LABELS))
          (ProjE (UncaseE (VarE "l") Arg) 0)
        )
      )
    )
  )
  (RuleD
    "catch_all_ref"
    (ExpP "C" (VarT "context"))
    (ExpP "l" (VarT "labelidx"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom CATCH_ALL_REF) Arg) (TupE (VarE "l"))))
    (RulePr
      "Resulttype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE
        (VarE "C")
        (CaseE
          Arg
          (TupE
            (ListE
              (CaseE
                (Seq (Atom REF) Arg Arg)
                (TupE (OptE) (CaseE (Atom EXN) (TupE)))
              )
            )
          )
        )
        (IdxE
          (DotE (VarE "C") (Atom LABELS))
          (ProjE (UncaseE (VarE "l") Arg) 0)
        )
      )
    )
  )
)
(DecD
  "default_"
  (ExpP "valtype" (VarT "valtype"))
  (IterT (VarT "val") Opt)
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpA (SubE (VarT "addrtype") (VarT "valtype") (VarE "Inn")))
    (OptE
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          (CaseE
            (Seq (Atom mk_num__0) Arg Arg)
            (TupE (VarE "Inn") (CaseE Arg (TupE (NumE (Nat 0)))))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "valtype") (VarE "Fnn")))
    (OptE
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE
              (VarE "Fnn")
              (CallE
                "fzero"
                (ExpA
                  (CallE
                    "size"
                    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpA (SubE (VarT "vectype") (VarT "valtype") (VarE "Vnn")))
    (OptE
      (CaseE
        (Seq (Atom VCONST) Arg Arg)
        (TupE (VarE "Vnn") (CaseE Arg (TupE (NumE (Nat 0)))))
      )
    )
  )
  (DefD
    (ExpP "ht" (VarT "heaptype"))
    (ExpA
      (CaseE
        (Seq (Atom REF) Arg Arg)
        (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht"))
      )
    )
    (OptE (CaseE (Atom REF.NULL_ADDR) (TupE)))
  )
  (DefD
    (ExpP "ht" (VarT "heaptype"))
    (ExpA (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht"))))
    (OptE)
  )
)
(RelD
  "Defaultable"
  (Infix (Seq) |- (Seq Arg (Atom DEFAULTABLE)))
  (VarT "valtype")
  (RuleD
    ""
    (ExpP "t" (VarT "valtype"))
    (Infix (Seq) |- (Seq Arg (Atom DEFAULTABLE)))
    (VarE "t")
    (IfPr (CmpE NeOp bool (CallE "default_" (ExpA (VarE "t"))) (OptE)))
  )
)
(RelD
  "Memarg_ok"
  (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
  (TupT
    (typbind "_" (VarT "memarg"))
    (typbind "_" (VarT "addrtype"))
    (typbind "_" (VarT "N"))
  )
  (RuleD
    ""
    (ExpP "n" (VarT "n"))
    (ExpP "m" (VarT "m"))
    (ExpP "at" (VarT "addrtype"))
    (ExpP "N" (VarT "N"))
    (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
    (TupE
      (StrE
        (expfield (Atom ALIGN) (CaseE Arg (TupE (VarE "n"))))
        (expfield (Atom OFFSET) (CaseE Arg (TupE (VarE "m"))))
      )
      (VarE "at")
      (VarE "N")
    )
    (IfPr
      (CmpE
        LeOp
        rat
        (CvtE nat rat (BinE PowOp nat (NumE (Nat 2)) (VarE "n")))
        (BinE DivOp rat (CvtE nat rat (VarE "N")) (CvtE nat rat (NumE (Nat 8))))
      )
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (VarE "m")
        (BinE
          PowOp
          nat
          (NumE (Nat 2))
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "at")))
          )
        )
      )
    )
  )
)
(DecD
  "is_packtype"
  (ExpP "storagetype" (VarT "storagetype"))
  BoolT
  (DefD
    (ExpP "zt" (VarT "storagetype"))
    (ExpA (VarE "zt"))
    (CmpE
      NeOp
      bool
      (VarE "zt")
      (SubE
        (VarT "valtype")
        (VarT "storagetype")
        (CallE "unpack" (ExpA (VarE "zt")))
      )
    )
  )
)
(RecD
  (RelD
    "Instr_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (VarT "instr"))
      (typbind "_" (VarT "instrtype"))
    )
    (RuleD
      "nop"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom NOP) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE (CaseE Arg (TupE (ListE))) (ListE) (CaseE Arg (TupE (ListE))))
        )
      )
    )
    (RuleD
      "unreachable"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom UNREACHABLE) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
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
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (VarE "t"))))
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Valtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "t"))
      )
    )
    (RuleD
      "select-expl"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom SELECT) Arg) (TupE (OptE (ListE (VarE "t")))))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (ListE (VarE "t") (VarE "t") (CaseE (Atom I32) (TupE))))
            )
            (ListE)
            (CaseE Arg (TupE (ListE (VarE "t"))))
          )
        )
      )
      (RulePr
        "Valtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "t"))
      )
    )
    (RuleD
      "select-impl"
      (ExpP "C" (VarT "context"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "t'" (VarT "valtype"))
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "vectype" (VarT "vectype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom SELECT) Arg) (TupE (OptE)))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (ListE (VarE "t") (VarE "t") (CaseE (Atom I32) (TupE))))
            )
            (ListE)
            (CaseE Arg (TupE (ListE (VarE "t"))))
          )
        )
      )
      (RulePr
        "Valtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "t"))
      )
      (RulePr
        "Valtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "t") (VarE "t'"))
      )
      (IfPr
        (BinE
          OrOp
          bool
          (CmpE
            EqOp
            bool
            (VarE "t'")
            (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype"))
          )
          (CmpE
            EqOp
            bool
            (VarE "t'")
            (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype"))
          )
        )
      )
    )
    (RuleD
      "block"
      (ExpP "C" (VarT "context"))
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "x*" (IterT (VarT "idx") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE
            (VarE "bt")
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Blocktype_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "bt")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                    )
                  )
                )
              )
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "loop"
      (ExpP "C" (VarT "context"))
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "x*" (IterT (VarT "idx") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE
            (VarE "bt")
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Blocktype_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "bt")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                    )
                  )
                )
              )
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "if"
      (ExpP "C" (VarT "context"))
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "instr_1*" (IterT (VarT "instr") List))
      (ExpP "instr_2*" (IterT (VarT "instr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "x_1*" (IterT (VarT "idx") List))
      (ExpP "x_2*" (IterT (VarT "idx") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE
            (VarE "bt")
            (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
            (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (ListE (CaseE (Atom I32) (TupE)))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Blocktype_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "bt")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                    )
                  )
                )
              )
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr_1") List (iterexp "instr_1" (VarE "instr_1*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x_1") List (iterexp "x_1" (VarE "x_1*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                    )
                  )
                )
              )
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x_2") List (iterexp "x_2" (VarE "x_2*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "br"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR) Arg) (TupE (VarE "l")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (ProjE
            (UncaseE
              (IdxE
                (DotE (VarE "C") (Atom LABELS))
                (ProjE (UncaseE (VarE "l") Arg) 0)
              )
              Arg
            )
            0
          )
          (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "br_if"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "l")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE (CaseE (Atom I32) (TupE)))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (ProjE
            (UncaseE
              (IdxE
                (DotE (VarE "C") (Atom LABELS))
                (ProjE (UncaseE (VarE "l") Arg) 0)
              )
              Arg
            )
            0
          )
          (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
        )
      )
    )
    (RuleD
      "br_table"
      (ExpP "C" (VarT "context"))
      (ExpP "l*" (IterT (VarT "labelidx") List))
      (ExpP "l'" (VarT "labelidx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (IterE (VarE "l") List (iterexp "l" (VarE "l*"))) (VarE "l'"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (CatE
                    (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                    (ListE (CaseE (Atom I32) (TupE)))
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (IterPr
        (RulePr
          "Resulttype_sub"
          (Infix Arg |- (Infix Arg <: Arg))
          (TupE
            (VarE "C")
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
            (IdxE
              (DotE (VarE "C") (Atom LABELS))
              (ProjE (UncaseE (VarE "l") Arg) 0)
            )
          )
        )
        List
        (iterexp "l" (VarE "l*"))
      )
      (RulePr
        "Resulttype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (UncaseE (VarE "l'") Arg) 0)
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE
                  (CatE
                    (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                    (CatE
                      (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                      (ListE (CaseE (Atom I32) (TupE)))
                    )
                  )
                )
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "br_on_null"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "ht" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR_ON_NULL) Arg) (TupE (VarE "l")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE
                    (CaseE
                      (Seq (Atom REF) Arg Arg)
                      (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht"))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE
                    (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht")))
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (ProjE
            (UncaseE
              (IdxE
                (DotE (VarE "C") (Atom LABELS))
                (ProjE (UncaseE (VarE "l") Arg) 0)
              )
              Arg
            )
            0
          )
          (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
        )
      )
      (RulePr
        "Heaptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "ht"))
      )
    )
    (RuleD
      "br_on_non_null"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "ht" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BR_ON_NON_NULL) Arg) (TupE (VarE "l")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE
                    (CaseE
                      (Seq (Atom REF) Arg Arg)
                      (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht"))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (UncaseE (VarE "l") Arg) 0)
          )
          (CaseE
            Arg
            (TupE
              (CatE
                (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE (IterE (CaseE (Atom NULL) (TupE)) Opt) (VarE "ht"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "br_on_cast"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "rt_1" (VarT "reftype"))
      (ExpP "rt_2" (VarT "reftype"))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "rt" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BR_ON_CAST) Arg Arg Arg)
          (TupE (VarE "l") (VarE "rt_1") (VarE "rt_2"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt_1")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE
                    (SubE
                      (VarT "reftype")
                      (VarT "valtype")
                      (CallE "diffrt" (ExpA (VarE "rt_1")) (ExpA (VarE "rt_2")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (UncaseE (VarE "l") Arg) 0)
          )
          (CaseE
            Arg
            (TupE
              (CatE
                (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt")))
              )
            )
          )
        )
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt_1"))
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt_2"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt_2") (VarE "rt_1"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt_2") (VarE "rt"))
      )
    )
    (RuleD
      "br_on_cast_fail"
      (ExpP "C" (VarT "context"))
      (ExpP "l" (VarT "labelidx"))
      (ExpP "rt_1" (VarT "reftype"))
      (ExpP "rt_2" (VarT "reftype"))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "rt" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom BR_ON_CAST_FAIL) Arg Arg Arg)
          (TupE (VarE "l") (VarE "rt_1") (VarE "rt_2"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt_1")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt_2")))
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LABELS))
            (ProjE (UncaseE (VarE "l") Arg) 0)
          )
          (CaseE
            Arg
            (TupE
              (CatE
                (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt")))
              )
            )
          )
        )
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt_1"))
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt_2"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt_2") (VarE "rt_1"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CallE "diffrt" (ExpA (VarE "rt_1")) (ExpA (VarE "rt_2")))
          (VarE "rt")
        )
      )
    )
    (RuleD
      "call"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom FUNCS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "call_ref"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom CALL_REF) Arg)
          (TupE (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x"))))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (ListE
                    (CaseE
                      (Seq (Atom REF) Arg Arg)
                      (TupE
                        (OptE (CaseE (Atom NULL) (TupE)))
                        (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                      )
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "call_indirect"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "lim" (VarT "limits"))
      (ExpP "rt" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom CALL_INDIRECT) Arg Arg)
          (TupE (VarE "x") (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "y"))))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (VarE "rt")
          (CaseE
            (Seq (Atom REF) Arg Arg)
            (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom FUNC) (TupE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "return"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom RETURN) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (VarE "C") (Atom RETURN))
          (OptE
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "return_call"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_3*" (IterT (VarT "valtype") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_4*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "t'_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom RETURN_CALL) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_4") List (iterexp "t_4" (VarE "t_4*"))))
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom FUNCS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (VarE "C") (Atom RETURN))
          (OptE
            (CaseE
              Arg
              (TupE (IterE (VarE "t'_2") List (iterexp "t'_2" (VarE "t'_2*"))))
            )
          )
        )
      )
      (RulePr
        "Resulttype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "t'_2") List (iterexp "t'_2" (VarE "t'_2*"))))
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_4") List (iterexp "t_4" (VarE "t_4*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "return_call_ref"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_3*" (IterT (VarT "valtype") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_4*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "t'_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom RETURN_CALL_REF) Arg)
          (TupE (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x"))))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
                  (CatE
                    (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                    (ListE
                      (CaseE
                        (Seq (Atom REF) Arg Arg)
                        (TupE
                          (OptE (CaseE (Atom NULL) (TupE)))
                          (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                        )
                      )
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_4") List (iterexp "t_4" (VarE "t_4*"))))
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (VarE "C") (Atom RETURN))
          (OptE
            (CaseE
              Arg
              (TupE (IterE (VarE "t'_2") List (iterexp "t'_2" (VarE "t'_2*"))))
            )
          )
        )
      )
      (RulePr
        "Resulttype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "t'_2") List (iterexp "t'_2" (VarE "t'_2*"))))
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_4") List (iterexp "t_4" (VarE "t_4*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "return_call_indirect"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "t_3*" (IterT (VarT "valtype") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "t_4*" (IterT (VarT "valtype") List))
      (ExpP "lim" (VarT "limits"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "t'_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom RETURN_CALL_INDIRECT) Arg Arg)
          (TupE (VarE "x") (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "y"))))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*")))
                  (CatE
                    (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                    (ListE
                      (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_4") List (iterexp "t_4" (VarE "t_4*"))))
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (VarE "rt")
          (CaseE
            (Seq (Atom REF) Arg Arg)
            (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom FUNC) (TupE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (VarE "C") (Atom RETURN))
          (OptE
            (CaseE
              Arg
              (TupE (IterE (VarE "t'_2") List (iterexp "t'_2" (VarE "t'_2*"))))
            )
          )
        )
      )
      (RulePr
        "Resulttype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (CaseE
            Arg
            (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "t'_2") List (iterexp "t'_2" (VarE "t'_2*"))))
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_4") List (iterexp "t_4" (VarE "t_4*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "throw"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom THROW) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (CallE
            "as_deftype"
            (ExpA
              (IdxE
                (DotE (VarE "C") (Atom TAGS))
                (ProjE (UncaseE (VarE "x") Arg) 0)
              )
            )
          )
          (CaseE
            (Infix (Seq (Atom FUNC) Arg) -> Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*"))))
              )
              (CaseE Arg (TupE (ListE)))
            )
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "throw_ref"
      (ExpP "C" (VarT "context"))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom THROW_REF) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                  (ListE
                    (CaseE
                      (Seq (Atom REF) Arg Arg)
                      (TupE
                        (OptE (CaseE (Atom NULL) (TupE)))
                        (CaseE (Atom EXN) (TupE))
                      )
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "try_table"
      (ExpP "C" (VarT "context"))
      (ExpP "bt" (VarT "blocktype"))
      (ExpP "catch*" (IterT (VarT "catch") List))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "x*" (IterT (VarT "idx") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom TRY_TABLE) Arg Arg Arg)
          (TupE
            (VarE "bt")
            (CaseE
              Arg
              (TupE
                (IterE (VarE "catch") List (iterexp "catch" (VarE "catch*")))
              )
            )
            (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
      (RulePr
        "Blocktype_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "bt")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (ListE)
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield
                (Atom LABELS)
                (ListE
                  (CaseE
                    Arg
                    (TupE
                      (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                    )
                  )
                )
              )
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
            (VarE "C")
          )
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (IterPr
        (RulePr
          "Catch_ok"
          (Infix Arg |- (Infix Arg : (Atom OK)))
          (TupE (VarE "C") (VarE "catch"))
        )
        List
        (iterexp "catch" (VarE "catch*"))
      )
    )
    (RuleD
      "ref.null"
      (ExpP "C" (VarT "context"))
      (ExpP "ht" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REF.NULL) Arg) (TupE (VarE "ht")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht"))
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Heaptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "ht"))
      )
    )
    (RuleD
      "ref.func"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "dt" (VarT "deftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REF.FUNC) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (SubE (VarT "deftype") (VarT "heaptype") (VarE "dt"))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom FUNCS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (VarE "dt")
        )
      )
      (IfPr (MemE (VarE "x") (DotE (VarE "C") (Atom REFS))))
    )
    (RuleD
      "ref.i31"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom REF.I31) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE (OptE) (CaseE (Atom I31) (TupE)))
                  )
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "ref.is_null"
      (ExpP "C" (VarT "context"))
      (ExpP "ht" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom REF.IS_NULL) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht"))
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
      (RulePr
        "Heaptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "ht"))
      )
    )
    (RuleD
      "ref.as_non_null"
      (ExpP "C" (VarT "context"))
      (ExpP "ht" (VarT "heaptype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom REF.AS_NON_NULL) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE (OptE (CaseE (Atom NULL) (TupE))) (VarE "ht"))
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (VarE "ht")))
                )
              )
            )
          )
        )
      )
      (RulePr
        "Heaptype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "ht"))
      )
    )
    (RuleD
      "ref.eq"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom REF.EQ) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Atom EQ) (TupE))
                    )
                  )
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Atom EQ) (TupE))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "ref.test"
      (ExpP "C" (VarT "context"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "rt'" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REF.TEST) Arg) (TupE (VarE "rt")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt'")))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt"))
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt'"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt") (VarE "rt'"))
      )
    )
    (RuleD
      "ref.cast"
      (ExpP "C" (VarT "context"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "rt'" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom REF.CAST) Arg) (TupE (VarE "rt")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt'")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt")))
              )
            )
          )
        )
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt"))
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "rt'"))
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt") (VarE "rt'"))
      )
    )
    (RuleD
      "i31.get"
      (ExpP "C" (VarT "context"))
      (ExpP "sx" (VarT "sx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom I31.GET) Arg) (TupE (VarE "sx")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Atom I31) (TupE))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "struct.new"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "zt*" (IterT (VarT "storagetype") List))
      (ExpP "mut?*" (IterT (IterT (VarT "mut") Opt) List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom STRUCT.NEW) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE
                  (CallE "unpack" (ExpA (VarE "zt")))
                  List
                  (iterexp "zt" (VarE "zt*"))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom STRUCT) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (CaseE
                      (Seq Arg Arg)
                      (TupE
                        (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                        (VarE "zt")
                      )
                    )
                    List
                    (iterexp "mut?" (VarE "mut?*"))
                    (iterexp "zt" (VarE "zt*"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "struct.new_default"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "mut?*" (IterT (IterT (VarT "mut") Opt) List))
      (ExpP "zt*" (IterT (VarT "storagetype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom STRUCT.NEW_DEFAULT) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom STRUCT) Arg)
            (TupE
              (CaseE
                Arg
                (TupE
                  (IterE
                    (CaseE
                      (Seq Arg Arg)
                      (TupE
                        (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                        (VarE "zt")
                      )
                    )
                    List
                    (iterexp "mut?" (VarE "mut?*"))
                    (iterexp "zt" (VarE "zt*"))
                  )
                )
              )
            )
          )
        )
      )
      (IterPr
        (RulePr
          "Defaultable"
          (Infix (Seq) |- (Seq Arg (Atom DEFAULTABLE)))
          (CallE "unpack" (ExpA (VarE "zt")))
        )
        List
        (iterexp "zt" (VarE "zt*"))
      )
    )
    (RuleD
      "struct.get"
      (ExpP "C" (VarT "context"))
      (ExpP "sx?" (IterT (VarT "sx") Opt))
      (ExpP "x" (VarT "idx"))
      (ExpP "i" (VarT "fieldidx"))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "ft*" (IterT (VarT "fieldtype") List))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STRUCT.GET) Arg Arg Arg)
          (TupE
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (VarE "x")
            (VarE "i")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CallE "unpack" (ExpA (VarE "zt"))))))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom STRUCT) Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*"))))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
            (ProjE (UncaseE (VarE "i") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg)
            (TupE
              (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
              (VarE "zt")
            )
          )
        )
      )
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE
            NeOp
            bool
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (OptE)
          )
          (CallE "is_packtype" (ExpA (VarE "zt")))
        )
      )
    )
    (RuleD
      "struct.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "i" (VarT "fieldidx"))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "ft*" (IterT (VarT "fieldtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom STRUCT.SET) Arg Arg) (TupE (VarE "x") (VarE "i")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                  (CallE "unpack" (ExpA (VarE "zt")))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom STRUCT) Arg)
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*"))))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (IterE (VarE "ft") List (iterexp "ft" (VarE "ft*")))
            (ProjE (UncaseE (VarE "i") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg)
            (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt"))
          )
        )
      )
    )
    (RuleD
      "array.new"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.NEW) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CallE "unpack" (ExpA (VarE "zt")))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (VarE "zt")
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "array.new_default"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (ExpP "zt" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.NEW_DEFAULT) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (VarE "zt")
                )
              )
            )
          )
        )
      )
      (RulePr
        "Defaultable"
        (Infix (Seq) |- (Seq Arg (Atom DEFAULTABLE)))
        (CallE "unpack" (ExpA (VarE "zt")))
      )
    )
    (RuleD
      "array.new_fixed"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "n" (VarT "n"))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom ARRAY.NEW_FIXED) Arg Arg)
          (TupE (VarE "x") (CaseE Arg (TupE (VarE "n"))))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (IterE (CallE "unpack" (ExpA (VarE "zt"))) (ListN (VarE "n")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (VarE "zt")
                )
              )
            )
          )
        )
      )
    )
    (RuleD
      "array.new_elem"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (ExpP "rt" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.NEW_ELEM) Arg Arg) (TupE (VarE "x") (VarE "y")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (ListE (CaseE (Atom I32) (TupE)) (CaseE (Atom I32) (TupE))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (SubE (VarT "reftype") (VarT "storagetype") (VarE "rt"))
                )
              )
            )
          )
        )
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (IdxE
            (DotE (VarE "C") (Atom ELEMS))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (VarE "rt")
        )
      )
    )
    (RuleD
      "array.new_data"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "vectype" (VarT "vectype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.NEW_DATA) Arg Arg) (TupE (VarE "x") (VarE "y")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (ListE (CaseE (Atom I32) (TupE)) (CaseE (Atom I32) (TupE))))
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE)
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (VarE "zt")
                )
              )
            )
          )
        )
      )
      (IfPr
        (BinE
          OrOp
          bool
          (CmpE
            EqOp
            bool
            (CallE "unpack" (ExpA (VarE "zt")))
            (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype"))
          )
          (CmpE
            EqOp
            bool
            (CallE "unpack" (ExpA (VarE "zt")))
            (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype"))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom DATAS))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (CaseE (Atom OK) (TupE))
        )
      )
    )
    (RuleD
      "array.get"
      (ExpP "C" (VarT "context"))
      (ExpP "sx?" (IterT (VarT "sx") Opt))
      (ExpP "x" (VarT "idx"))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom ARRAY.GET) Arg Arg)
          (TupE (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?"))) (VarE "x"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CallE "unpack" (ExpA (VarE "zt"))))))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (VarE "zt")
                )
              )
            )
          )
        )
      )
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE
            NeOp
            bool
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (OptE)
          )
          (CallE "is_packtype" (ExpA (VarE "zt")))
        )
      )
    )
    (RuleD
      "array.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "zt" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.SET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                  (CallE "unpack" (ExpA (VarE "zt")))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "array.len"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom ARRAY.LEN) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Atom ARRAY) (TupE))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "array.fill"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "zt" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.FILL) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                  (CallE "unpack" (ExpA (VarE "zt")))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt"))
              )
            )
          )
        )
      )
    )
    (RuleD
      "array.copy"
      (ExpP "C" (VarT "context"))
      (ExpP "x_1" (VarT "idx"))
      (ExpP "x_2" (VarT "idx"))
      (ExpP "zt_1" (VarT "storagetype"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (ExpP "zt_2" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ARRAY.COPY) Arg Arg) (TupE (VarE "x_1") (VarE "x_2")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x_1")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x_2")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x_1") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt_1"))
              )
            )
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x_2") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE
                  (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
                  (VarE "zt_2")
                )
              )
            )
          )
        )
      )
      (RulePr
        "Storagetype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "zt_2") (VarE "zt_1"))
      )
    )
    (RuleD
      "array.init_elem"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "zt" (VarT "storagetype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom ARRAY.INIT_ELEM) Arg Arg)
          (TupE (VarE "x") (VarE "y"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt"))
              )
            )
          )
        )
      )
      (RulePr
        "Storagetype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (VarE "C")
          (SubE
            (VarT "reftype")
            (VarT "storagetype")
            (IdxE
              (DotE (VarE "C") (Atom ELEMS))
              (ProjE (UncaseE (VarE "y") Arg) 0)
            )
          )
          (VarE "zt")
        )
      )
    )
    (RuleD
      "array.init_data"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "zt" (VarT "storagetype"))
      (ExpP "numtype" (VarT "numtype"))
      (ExpP "vectype" (VarT "vectype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom ARRAY.INIT_DATA) Arg Arg)
          (TupE (VarE "x") (VarE "y"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (OptE (CaseE (Atom NULL) (TupE)))
                      (CaseE (Seq (Atom _IDX) Arg) (TupE (VarE "x")))
                    )
                  )
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (RulePr
        "Expand"
        (Infix Arg ~~ Arg)
        (TupE
          (IdxE
            (DotE (VarE "C") (Atom TYPES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq (Atom ARRAY) Arg)
            (TupE
              (CaseE
                (Seq Arg Arg)
                (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "zt"))
              )
            )
          )
        )
      )
      (IfPr
        (BinE
          OrOp
          bool
          (CmpE
            EqOp
            bool
            (CallE "unpack" (ExpA (VarE "zt")))
            (SubE (VarT "numtype") (VarT "valtype") (VarE "numtype"))
          )
          (CmpE
            EqOp
            bool
            (CallE "unpack" (ExpA (VarE "zt")))
            (SubE (VarT "vectype") (VarT "valtype") (VarE "vectype"))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom DATAS))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (CaseE (Atom OK) (TupE))
        )
      )
    )
    (RuleD
      "extern.convert_any"
      (ExpP "C" (VarT "context"))
      (ExpP "null_1?" (IterT (VarT "null") Opt))
      (ExpP "null_2?" (IterT (VarT "null") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom EXTERN.CONVERT_ANY) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (IterE
                        (VarE "null_1")
                        Opt
                        (iterexp "null_1" (VarE "null_1?"))
                      )
                      (CaseE (Atom ANY) (TupE))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (IterE
                        (VarE "null_2")
                        Opt
                        (iterexp "null_2" (VarE "null_2?"))
                      )
                      (CaseE (Atom EXTERN) (TupE))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IterE (VarE "null_1") Opt (iterexp "null_1" (VarE "null_1?")))
          (IterE (VarE "null_2") Opt (iterexp "null_2" (VarE "null_2?")))
        )
      )
    )
    (RuleD
      "any.convert_extern"
      (ExpP "C" (VarT "context"))
      (ExpP "null_1?" (IterT (VarT "null") Opt))
      (ExpP "null_2?" (IterT (VarT "null") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Atom ANY.CONVERT_EXTERN) (TupE))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (IterE
                        (VarE "null_1")
                        Opt
                        (iterexp "null_1" (VarE "null_1?"))
                      )
                      (CaseE (Atom EXTERN) (TupE))
                    )
                  )
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE
                    (Seq (Atom REF) Arg Arg)
                    (TupE
                      (IterE
                        (VarE "null_2")
                        Opt
                        (iterexp "null_2" (VarE "null_2?"))
                      )
                      (CaseE (Atom ANY) (TupE))
                    )
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IterE (VarE "null_1") Opt (iterexp "null_1" (VarE "null_1?")))
          (IterE (VarE "null_2") Opt (iterexp "null_2" (VarE "null_2?")))
        )
      )
    )
    (RuleD
      "local.get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE Arg (TupE (ListE (VarE "t"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg) (TupE (CaseE (Atom SET) (TupE)) (VarE "t")))
        )
      )
    )
    (RuleD
      "local.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "init" (VarT "init"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (VarE "t"))))
            (ListE (VarE "x"))
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg) (TupE (VarE "init") (VarE "t")))
        )
      )
    )
    (RuleD
      "local.tee"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "init" (VarT "init"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (VarE "t"))))
            (ListE (VarE "x"))
            (CaseE Arg (TupE (ListE (VarE "t"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom LOCALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg) (TupE (VarE "init") (VarE "t")))
        )
      )
    )
    (RuleD
      "global.get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (ExpP "mut?" (IterT (VarT "mut") Opt))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE Arg (TupE (ListE (VarE "t"))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom GLOBALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg)
            (TupE
              (IterE (VarE "mut") Opt (iterexp "mut" (VarE "mut?")))
              (VarE "t")
            )
          )
        )
      )
    )
    (RuleD
      "global.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "t" (VarT "valtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (VarE "t"))))
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom GLOBALS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg)
            (TupE (OptE (CaseE (Atom MUT) (TupE))) (VarE "t"))
          )
        )
      )
    )
    (RuleD
      "table.get"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.GET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "reftype") (VarT "valtype") (VarE "rt")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
    )
    (RuleD
      "table.set"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.SET) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (SubE (VarT "reftype") (VarT "valtype") (VarE "rt"))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
    )
    (RuleD
      "table.size"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (ExpP "rt" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.SIZE) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
    )
    (RuleD
      "table.grow"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.GROW) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "reftype") (VarT "valtype") (VarE "rt"))
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
    )
    (RuleD
      "table.fill"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.FILL) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (SubE (VarT "reftype") (VarT "valtype") (VarE "rt"))
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
        )
      )
    )
    (RuleD
      "table.copy"
      (ExpP "C" (VarT "context"))
      (ExpP "x_1" (VarT "idx"))
      (ExpP "x_2" (VarT "idx"))
      (ExpP "at_1" (VarT "addrtype"))
      (ExpP "at_2" (VarT "addrtype"))
      (ExpP "lim_1" (VarT "limits"))
      (ExpP "rt_1" (VarT "reftype"))
      (ExpP "lim_2" (VarT "limits"))
      (ExpP "rt_2" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.COPY) Arg Arg) (TupE (VarE "x_1") (VarE "x_2")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at_1"))
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at_2"))
                  (SubE
                    (VarT "addrtype")
                    (VarT "valtype")
                    (CallE "minat" (ExpA (VarE "at_1")) (ExpA (VarE "at_2")))
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x_1") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg Arg)
            (TupE (VarE "at_1") (VarE "lim_1") (VarE "rt_1"))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x_2") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg Arg)
            (TupE (VarE "at_2") (VarE "lim_2") (VarE "rt_2"))
          )
        )
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt_2") (VarE "rt_1"))
      )
    )
    (RuleD
      "table.init"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (ExpP "rt_1" (VarT "reftype"))
      (ExpP "rt_2" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom TABLE.INIT) Arg Arg) (TupE (VarE "x") (VarE "y")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom TABLES))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE
            (Seq Arg Arg Arg)
            (TupE (VarE "at") (VarE "lim") (VarE "rt_1"))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom ELEMS))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (VarE "rt_2")
        )
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "rt_2") (VarE "rt_1"))
      )
    )
    (RuleD
      "elem.drop"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "rt" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom ELEM.DROP) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE (CaseE Arg (TupE (ListE))) (ListE) (CaseE Arg (TupE (ListE))))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom ELEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (VarE "rt")
        )
      )
    )
    (RuleD
      "memory.size"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom MEMORY.SIZE) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
    )
    (RuleD
      "memory.grow"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom MEMORY.GROW) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
    )
    (RuleD
      "memory.fill"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom MEMORY.FILL) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (CaseE (Atom I32) (TupE))
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
    )
    (RuleD
      "memory.copy"
      (ExpP "C" (VarT "context"))
      (ExpP "x_1" (VarT "idx"))
      (ExpP "x_2" (VarT "idx"))
      (ExpP "at_1" (VarT "addrtype"))
      (ExpP "at_2" (VarT "addrtype"))
      (ExpP "lim_1" (VarT "limits"))
      (ExpP "lim_2" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom MEMORY.COPY) Arg Arg)
          (TupE (VarE "x_1") (VarE "x_2"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at_1"))
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at_2"))
                  (SubE
                    (VarT "addrtype")
                    (VarT "valtype")
                    (CallE "minat" (ExpA (VarE "at_1")) (ExpA (VarE "at_2")))
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x_1") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at_1") (VarE "lim_1")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x_2") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at_2") (VarE "lim_2")))
        )
      )
    )
    (RuleD
      "memory.init"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "y" (VarT "idx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom MEMORY.INIT) Arg Arg) (TupE (VarE "x") (VarE "y")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (CaseE (Atom I32) (TupE))
                  (CaseE (Atom I32) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom DATAS))
            (ProjE (UncaseE (VarE "y") Arg) 0)
          )
          (CaseE (Atom OK) (TupE))
        )
      )
    )
    (RuleD
      "data.drop"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom DATA.DROP) Arg) (TupE (VarE "x")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE (CaseE Arg (TupE (ListE))) (ListE) (CaseE Arg (TupE (ListE))))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom DATAS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Atom OK) (TupE))
        )
      )
    )
    (RuleD
      "load-val"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg Arg)
          (TupE (VarE "nt") (OptE) (VarE "x") (VarE "memarg"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (CallE "size" (ExpA (VarE "nt"))))
      )
    )
    (RuleD
      "load-pack"
      (ExpP "C" (VarT "context"))
      (ExpP "Inn" (VarT "Inn"))
      (ExpP "M" (VarT "M"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg Arg)
          (TupE
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
            (OptE
              (CaseE
                (Seq (Atom mk_loadop__0) Arg Arg)
                (TupE
                  (VarE "Inn")
                  (CaseE
                    (Seq Arg (Atom _) Arg)
                    (TupE (CaseE Arg (TupE (VarE "M"))) (VarE "sx"))
                  )
                )
              )
            )
            (VarE "x")
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "Inn")))
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (VarE "M"))
      )
    )
    (RuleD
      "store-val"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg Arg)
          (TupE (VarE "nt") (OptE) (VarE "x") (VarE "memarg"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (SubE (VarT "numtype") (VarT "valtype") (VarE "nt"))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (CallE "size" (ExpA (VarE "nt"))))
      )
    )
    (RuleD
      "store-pack"
      (ExpP "C" (VarT "context"))
      (ExpP "Inn" (VarT "Inn"))
      (ExpP "M" (VarT "M"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg Arg)
          (TupE
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
            (OptE
              (CaseE
                (Seq (Atom mk_storeop__0) Arg Arg)
                (TupE
                  (VarE "Inn")
                  (CaseE Arg (TupE (CaseE Arg (TupE (VarE "M")))))
                )
              )
            )
            (VarE "x")
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "Inn"))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (VarE "M"))
      )
    )
    (RuleD
      "vload-val"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VLOAD) Arg Arg Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (OptE) (VarE "x") (VarE "memarg"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE
          (VarE "memarg")
          (VarE "at")
          (CallE "vsize" (ExpA (CaseE (Atom V128) (TupE))))
        )
      )
    )
    (RuleD
      "vload-pack"
      (ExpP "C" (VarT "context"))
      (ExpP "M" (VarT "M"))
      (ExpP "N" (VarT "N"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VLOAD) Arg Arg Arg Arg)
          (TupE
            (CaseE (Atom V128) (TupE))
            (OptE
              (CaseE
                (Seq (Atom SHAPE) Arg (Atom X) Arg (Atom _) Arg)
                (TupE (CaseE Arg (TupE (VarE "M"))) (VarE "N") (VarE "sx"))
              )
            )
            (VarE "x")
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE
          (VarE "memarg")
          (VarE "at")
          (BinE MulOp nat (VarE "M") (VarE "N"))
        )
      )
    )
    (RuleD
      "vload-splat"
      (ExpP "C" (VarT "context"))
      (ExpP "N" (VarT "N"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VLOAD) Arg Arg Arg Arg)
          (TupE
            (CaseE (Atom V128) (TupE))
            (OptE
              (CaseE
                (Seq (Atom SPLAT) Arg)
                (TupE (CaseE Arg (TupE (VarE "N"))))
              )
            )
            (VarE "x")
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (VarE "N"))
      )
    )
    (RuleD
      "vload-zero"
      (ExpP "C" (VarT "context"))
      (ExpP "N" (VarT "N"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VLOAD) Arg Arg Arg Arg)
          (TupE
            (CaseE (Atom V128) (TupE))
            (OptE
              (CaseE (Seq (Atom ZERO) Arg) (TupE (CaseE Arg (TupE (VarE "N")))))
            )
            (VarE "x")
            (VarE "memarg")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "addrtype") (VarT "valtype") (VarE "at")))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (VarE "N"))
      )
    )
    (RuleD
      "vload_lane"
      (ExpP "C" (VarT "context"))
      (ExpP "N" (VarT "N"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "i" (VarT "laneidx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VLOAD_LANE) Arg Arg Arg Arg Arg)
          (TupE
            (CaseE (Atom V128) (TupE))
            (CaseE Arg (TupE (VarE "N")))
            (VarE "x")
            (VarE "memarg")
            (VarE "i")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (CaseE (Atom V128) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (VarE "N"))
      )
      (IfPr
        (CmpE
          LtOp
          rat
          (CvtE nat rat (ProjE (UncaseE (VarE "i") Arg) 0))
          (BinE
            DivOp
            rat
            (CvtE nat rat (NumE (Nat 128)))
            (CvtE nat rat (VarE "N"))
          )
        )
      )
    )
    (RuleD
      "vstore"
      (ExpP "C" (VarT "context"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VSTORE) Arg Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (VarE "x") (VarE "memarg"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (CaseE (Atom V128) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE
          (VarE "memarg")
          (VarE "at")
          (CallE "vsize" (ExpA (CaseE (Atom V128) (TupE))))
        )
      )
    )
    (RuleD
      "vstore_lane"
      (ExpP "C" (VarT "context"))
      (ExpP "N" (VarT "N"))
      (ExpP "x" (VarT "idx"))
      (ExpP "memarg" (VarT "memarg"))
      (ExpP "i" (VarT "laneidx"))
      (ExpP "at" (VarT "addrtype"))
      (ExpP "lim" (VarT "limits"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VSTORE_LANE) Arg Arg Arg Arg Arg)
          (TupE
            (CaseE (Atom V128) (TupE))
            (CaseE Arg (TupE (VarE "N")))
            (VarE "x")
            (VarE "memarg")
            (VarE "i")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
                  (CaseE (Atom V128) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE)))
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE
            (DotE (VarE "C") (Atom MEMS))
            (ProjE (UncaseE (VarE "x") Arg) 0)
          )
          (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
        )
      )
      (RulePr
        "Memarg_ok"
        (Infix (Seq) |- (Infix Arg : (Infix Arg -> Arg)))
        (TupE (VarE "memarg") (VarE "at") (VarE "N"))
      )
      (IfPr
        (CmpE
          LtOp
          rat
          (CvtE nat rat (ProjE (UncaseE (VarE "i") Arg) 0))
          (BinE
            DivOp
            rat
            (CvtE nat rat (NumE (Nat 128)))
            (CvtE nat rat (VarE "N"))
          )
        )
      )
    )
    (RuleD
      "const"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "c_nt" (VarT "num_" (ExpA (VarE "nt"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "nt") (VarE "c_nt")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
              )
            )
          )
        )
      )
    )
    (RuleD
      "unop"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "unop_nt" (VarT "unop_" (ExpA (VarE "nt"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "nt") (VarE "unop_nt")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
              )
            )
          )
        )
      )
    )
    (RuleD
      "binop"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "binop_nt" (VarT "binop_" (ExpA (VarE "nt"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom BINOP) Arg Arg) (TupE (VarE "nt") (VarE "binop_nt")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "numtype") (VarT "valtype") (VarE "nt"))
                  (SubE (VarT "numtype") (VarT "valtype") (VarE "nt"))
                )
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
              )
            )
          )
        )
      )
    )
    (RuleD
      "testop"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "testop_nt" (VarT "testop_" (ExpA (VarE "nt"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "nt") (VarE "testop_nt"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt")))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "relop"
      (ExpP "C" (VarT "context"))
      (ExpP "nt" (VarT "numtype"))
      (ExpP "relop_nt" (VarT "relop_" (ExpA (VarE "nt"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom RELOP) Arg Arg) (TupE (VarE "nt") (VarE "relop_nt")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE (VarT "numtype") (VarT "valtype") (VarE "nt"))
                  (SubE (VarT "numtype") (VarT "valtype") (VarE "nt"))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "cvtop"
      (ExpP "C" (VarT "context"))
      (ExpP "nt_1" (VarT "numtype"))
      (ExpP "nt_2" (VarT "numtype"))
      (ExpP "cvtop" (VarT "cvtop__" (ExpA (VarE "nt_2")) (ExpA (VarE "nt_1"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "nt_1") (VarE "nt_2") (VarE "cvtop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt_2")))
              )
            )
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE (SubE (VarT "numtype") (VarT "valtype") (VarE "nt_1")))
              )
            )
          )
        )
      )
    )
    (RuleD
      "vconst"
      (ExpP "C" (VarT "context"))
      (ExpP "c" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VCONST) Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (VarE "c"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vvunop"
      (ExpP "C" (VarT "context"))
      (ExpP "vvunop" (VarT "vvunop"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VVUNOP) Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (VarE "vvunop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vvbinop"
      (ExpP "C" (VarT "context"))
      (ExpP "vvbinop" (VarT "vvbinop"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VVBINOP) Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (VarE "vvbinop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vvternop"
      (ExpP "C" (VarT "context"))
      (ExpP "vvternop" (VarT "vvternop"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VVTERNOP) Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (VarE "vvternop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE (Atom V128) (TupE))
                  (CaseE (Atom V128) (TupE))
                  (CaseE (Atom V128) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vvtestop"
      (ExpP "C" (VarT "context"))
      (ExpP "vvtestop" (VarT "vvtestop"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VVTESTOP) Arg Arg)
          (TupE (CaseE (Atom V128) (TupE)) (VarE "vvtestop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vunop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "vunop" (VarT "vunop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VUNOP) Arg Arg) (TupE (VarE "sh") (VarE "vunop")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vbinop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "vbinop" (VarT "vbinop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VBINOP) Arg Arg) (TupE (VarE "sh") (VarE "vbinop")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vternop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "vternop" (VarT "vternop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VTERNOP) Arg Arg) (TupE (VarE "sh") (VarE "vternop")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE (Atom V128) (TupE))
                  (CaseE (Atom V128) (TupE))
                  (CaseE (Atom V128) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vtestop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "vtestop" (VarT "vtestop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VTESTOP) Arg Arg) (TupE (VarE "sh") (VarE "vtestop")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vrelop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "vrelop" (VarT "vrelop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VRELOP) Arg Arg) (TupE (VarE "sh") (VarE "vrelop")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vshiftop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "ishape"))
      (ExpP "vshiftop" (VarT "vshiftop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VSHIFTOP) Arg Arg)
          (TupE (VarE "sh") (VarE "vshiftop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom I32) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vbitmask"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "ishape"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VBITMASK) Arg) (TupE (VarE "sh")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom I32) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vswizzlop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "bshape"))
      (ExpP "vswizzlop" (VarT "vswizzlop_" (ExpA (VarE "sh"))))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VSWIZZLOP) Arg Arg)
          (TupE (VarE "sh") (VarE "vswizzlop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vshuffle"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "bshape"))
      (ExpP "i*" (IterT (VarT "laneidx") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VSHUFFLE) Arg Arg)
          (TupE (VarE "sh") (IterE (VarE "i") List (iterexp "i" (VarE "i*"))))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IterPr
        (IfPr
          (CmpE
            LtOp
            nat
            (ProjE (UncaseE (VarE "i") Arg) 0)
            (BinE
              MulOp
              nat
              (NumE (Nat 2))
              (ProjE
                (UncaseE
                  (CallE "dim" (ExpA (ProjE (UncaseE (VarE "sh") Arg) 0)))
                  Arg
                )
                0
              )
            )
          )
        )
        List
        (iterexp "i" (VarE "i*"))
      )
    )
    (RuleD
      "vsplat"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VSPLAT) Arg) (TupE (VarE "sh")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE
                    (VarT "numtype")
                    (VarT "valtype")
                    (CallE "unpackshape" (ExpA (VarE "sh")))
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vextract_lane"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "sx?" (IterT (VarT "sx") Opt))
      (ExpP "i" (VarT "laneidx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VEXTRACT_LANE) Arg Arg Arg)
          (TupE
            (VarE "sh")
            (IterE (VarE "sx") Opt (iterexp "sx" (VarE "sx?")))
            (VarE "i")
          )
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE
              Arg
              (TupE
                (ListE
                  (SubE
                    (VarT "numtype")
                    (VarT "valtype")
                    (CallE "unpackshape" (ExpA (VarE "sh")))
                  )
                )
              )
            )
          )
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (UncaseE (VarE "i") Arg) 0)
          (ProjE (UncaseE (CallE "dim" (ExpA (VarE "sh"))) Arg) 0)
        )
      )
    )
    (RuleD
      "vreplace_lane"
      (ExpP "C" (VarT "context"))
      (ExpP "sh" (VarT "shape"))
      (ExpP "i" (VarT "laneidx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE (Seq (Atom VREPLACE_LANE) Arg Arg) (TupE (VarE "sh") (VarE "i")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE (Atom V128) (TupE))
                  (SubE
                    (VarT "numtype")
                    (VarT "valtype")
                    (CallE "unpackshape" (ExpA (VarE "sh")))
                  )
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
      (IfPr
        (CmpE
          LtOp
          nat
          (ProjE (UncaseE (VarE "i") Arg) 0)
          (ProjE (UncaseE (CallE "dim" (ExpA (VarE "sh"))) Arg) 0)
        )
      )
    )
    (RuleD
      "vextunop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh_1" (VarT "ishape"))
      (ExpP "sh_2" (VarT "ishape"))
      (ExpP
        "vextunop"
        (VarT "vextunop__" (ExpA (VarE "sh_2")) (ExpA (VarE "sh_1")))
      )
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VEXTUNOP) Arg Arg Arg)
          (TupE (VarE "sh_1") (VarE "sh_2") (VarE "vextunop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vextbinop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh_1" (VarT "ishape"))
      (ExpP "sh_2" (VarT "ishape"))
      (ExpP
        "vextbinop"
        (VarT "vextbinop__" (ExpA (VarE "sh_2")) (ExpA (VarE "sh_1")))
      )
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VEXTBINOP) Arg Arg Arg)
          (TupE (VarE "sh_1") (VarE "sh_2") (VarE "vextbinop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vextternop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh_1" (VarT "ishape"))
      (ExpP "sh_2" (VarT "ishape"))
      (ExpP
        "vextternop"
        (VarT "vextternop__" (ExpA (VarE "sh_2")) (ExpA (VarE "sh_1")))
      )
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VEXTTERNOP) Arg Arg Arg)
          (TupE (VarE "sh_1") (VarE "sh_2") (VarE "vextternop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE
                  (CaseE (Atom V128) (TupE))
                  (CaseE (Atom V128) (TupE))
                  (CaseE (Atom V128) (TupE))
                )
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vnarrow"
      (ExpP "C" (VarT "context"))
      (ExpP "sh_1" (VarT "ishape"))
      (ExpP "sh_2" (VarT "ishape"))
      (ExpP "sx" (VarT "sx"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VNARROW) Arg Arg Arg)
          (TupE (VarE "sh_1") (VarE "sh_2") (VarE "sx"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (ListE (CaseE (Atom V128) (TupE)) (CaseE (Atom V128) (TupE)))
              )
            )
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
    (RuleD
      "vcvtop"
      (ExpP "C" (VarT "context"))
      (ExpP "sh_1" (VarT "shape"))
      (ExpP "sh_2" (VarT "shape"))
      (ExpP
        "vcvtop"
        (VarT "vcvtop__" (ExpA (VarE "sh_2")) (ExpA (VarE "sh_1")))
      )
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CaseE
          (Seq (Atom VCVTOP) Arg Arg Arg)
          (TupE (VarE "sh_1") (VarE "sh_2") (VarE "vcvtop"))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
            (ListE)
            (CaseE Arg (TupE (ListE (CaseE (Atom V128) (TupE)))))
          )
        )
      )
    )
  )
  (RelD
    "Instrs_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (IterT (VarT "instr") List))
      (typbind "_" (VarT "instrtype"))
    )
    (RuleD
      "empty"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (ListE)
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE (CaseE Arg (TupE (ListE))) (ListE) (CaseE Arg (TupE (ListE))))
        )
      )
    )
    (RuleD
      "seq"
      (ExpP "C" (VarT "context"))
      (ExpP "instr_1" (VarT "instr"))
      (ExpP "instr_2*" (IterT (VarT "instr") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "x_1*" (IterT (VarT "idx") List))
      (ExpP "x_2*" (IterT (VarT "idx") List))
      (ExpP "t_3*" (IterT (VarT "valtype") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (ExpP "init*" (IterT (VarT "init") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CatE
          (ListE (VarE "instr_1"))
          (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
        )
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CatE
              (IterE (VarE "x_1") List (iterexp "x_1" (VarE "x_1*")))
              (IterE (VarE "x_2") List (iterexp "x_2" (VarE "x_2*")))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*"))))
            )
          )
        )
      )
      (RulePr
        "Instr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "instr_1")
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x_1") List (iterexp "x_1" (VarE "x_1*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (IterPr
        (IfPr
          (CmpE
            EqOp
            bool
            (IdxE
              (DotE (VarE "C") (Atom LOCALS))
              (ProjE (UncaseE (VarE "x_1") Arg) 0)
            )
            (CaseE (Seq Arg Arg) (TupE (VarE "init") (VarE "t")))
          )
        )
        List
        (iterexp "init" (VarE "init*"))
        (iterexp "t" (VarE "t*"))
        (iterexp "x_1" (VarE "x_1*"))
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CallE
            "with_locals"
            (ExpA (VarE "C"))
            (ExpA (IterE (VarE "x_1") List (iterexp "x_1" (VarE "x_1*"))))
            (ExpA
              (IterE
                (CaseE
                  (Seq Arg Arg)
                  (TupE (CaseE (Atom SET) (TupE)) (VarE "t"))
                )
                List
                (iterexp "t" (VarE "t*"))
              )
            )
          )
          (IterE (VarE "instr_2") List (iterexp "instr_2" (VarE "instr_2*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
              (IterE (VarE "x_2") List (iterexp "x_2" (VarE "x_2*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_3") List (iterexp "t_3" (VarE "t_3*"))))
              )
            )
          )
        )
      )
    )
    (RuleD
      "sub"
      (ExpP "C" (VarT "context"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "it'" (VarT "instrtype"))
      (ExpP "it" (VarT "instrtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        (VarE "it'")
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (VarE "it")
        )
      )
      (RulePr
        "Instrtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE (VarE "C") (VarE "it") (VarE "it'"))
      )
      (RulePr
        "Instrtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "it'"))
      )
    )
    (RuleD
      "frame"
      (ExpP "C" (VarT "context"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "t*" (IterT (VarT "valtype") List))
      (ExpP "t_1*" (IterT (VarT "valtype") List))
      (ExpP "x*" (IterT (VarT "idx") List))
      (ExpP "t_2*" (IterT (VarT "valtype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*")))
                )
              )
            )
            (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
            (CaseE
              Arg
              (TupE
                (CatE
                  (IterE (VarE "t") List (iterexp "t" (VarE "t*")))
                  (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*")))
                )
              )
            )
          )
        )
      )
      (RulePr
        "Instrs_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
          (CaseE
            (Infix Arg ->_ (Seq Arg Arg))
            (TupE
              (CaseE
                Arg
                (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
              )
              (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
              (CaseE
                Arg
                (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
              )
            )
          )
        )
      )
      (RulePr
        "Resulttype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (VarE "C")
          (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
        )
      )
    )
  )
)
HintD
HintD
(RelD
  "Expr_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "expr"))
    (typbind "_" (VarT "resulttype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (ExpP "t*" (IterT (VarT "valtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
      (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
    )
    (RulePr
      "Instrs_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
        (CaseE
          (Infix Arg ->_ (Seq Arg Arg))
          (TupE
            (CaseE Arg (TupE (ListE)))
            (ListE)
            (CaseE Arg (TupE (IterE (VarE "t") List (iterexp "t" (VarE "t*")))))
          )
        )
      )
    )
  )
)
HintD
HintD
(RelD
  "Nondefaultable"
  (Infix (Seq) |- (Seq Arg (Atom NONDEFAULTABLE)))
  (VarT "valtype")
  (RuleD
    ""
    (ExpP "t" (VarT "valtype"))
    (Infix (Seq) |- (Seq Arg (Atom NONDEFAULTABLE)))
    (VarE "t")
    (IfPr (CmpE EqOp bool (CallE "default_" (ExpA (VarE "t"))) (OptE)))
  )
)
HintD
HintD
HintD
HintD
HintD
(RelD
  "Instr_const"
  (Infix Arg |- (Seq Arg (Atom CONST)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "instr")))
  (RuleD
    "const"
    (ExpP "C" (VarT "context"))
    (ExpP "nt" (VarT "numtype"))
    (ExpP "c_nt" (VarT "num_" (ExpA (VarE "nt"))))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "nt") (VarE "c_nt")))
    )
  )
  (RuleD
    "vconst"
    (ExpP "C" (VarT "context"))
    (ExpP "vt" (VarT "vectype"))
    (ExpP "c_vt" (VarT "vec_" (ExpA (VarE "vt"))))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom VCONST) Arg Arg) (TupE (VarE "vt") (VarE "c_vt")))
    )
  )
  (RuleD
    "ref.null"
    (ExpP "C" (VarT "context"))
    (ExpP "ht" (VarT "heaptype"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom REF.NULL) Arg) (TupE (VarE "ht"))))
  )
  (RuleD
    "ref.i31"
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Atom REF.I31) (TupE)))
  )
  (RuleD
    "ref.func"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom REF.FUNC) Arg) (TupE (VarE "x"))))
  )
  (RuleD
    "struct.new"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom STRUCT.NEW) Arg) (TupE (VarE "x"))))
  )
  (RuleD
    "struct.new_default"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom STRUCT.NEW_DEFAULT) Arg) (TupE (VarE "x")))
    )
  )
  (RuleD
    "array.new"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom ARRAY.NEW) Arg) (TupE (VarE "x"))))
  )
  (RuleD
    "array.new_default"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom ARRAY.NEW_DEFAULT) Arg) (TupE (VarE "x")))
    )
  )
  (RuleD
    "array.new_fixed"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "n" (VarT "n"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom ARRAY.NEW_FIXED) Arg Arg)
        (TupE (VarE "x") (CaseE Arg (TupE (VarE "n"))))
      )
    )
  )
  (RuleD
    "any.convert_extern"
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Atom ANY.CONVERT_EXTERN) (TupE)))
  )
  (RuleD
    "extern.convert_any"
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Atom EXTERN.CONVERT_ANY) (TupE)))
  )
  (RuleD
    "global.get"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE (VarE "C") (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "x"))))
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom GLOBALS))
          (ProjE (UncaseE (VarE "x") Arg) 0)
        )
        (CaseE (Seq Arg Arg) (TupE (OptE) (VarE "t")))
      )
    )
  )
  (RuleD
    "binop"
    (ExpP "C" (VarT "context"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP
      "binop"
      (VarT
        "binop_"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
      )
    )
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom BINOP) Arg Arg)
        (TupE
          (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
          (VarE "binop")
        )
      )
    )
    (IfPr
      (MemE
        (VarE "Inn")
        (ListE (CaseE (Atom I32) (TupE)) (CaseE (Atom I64) (TupE)))
      )
    )
    (IfPr
      (MemE
        (VarE "binop")
        (ListE
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (VarE "Inn") (CaseE (Atom ADD) (TupE)))
          )
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (VarE "Inn") (CaseE (Atom SUB) (TupE)))
          )
          (CaseE
            (Seq (Atom mk_binop__0) Arg Arg)
            (TupE (VarE "Inn") (CaseE (Atom MUL) (TupE)))
          )
        )
      )
    )
  )
)
HintD
(RelD
  "Expr_const"
  (Infix Arg |- (Seq Arg (Atom CONST)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "expr")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "instr*" (IterT (VarT "instr") List))
    (Infix Arg |- (Seq Arg (Atom CONST)))
    (TupE
      (VarE "C")
      (IterE (VarE "instr") List (iterexp "instr" (VarE "instr*")))
    )
    (IterPr
      (RulePr
        "Instr_const"
        (Infix Arg |- (Seq Arg (Atom CONST)))
        (TupE (VarE "C") (VarE "instr"))
      )
      List
      (iterexp "instr" (VarE "instr*"))
    )
  )
)
HintD
(RelD
  "Expr_ok_const"
  (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "expr"))
    (typbind "_" (VarT "valtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
    (TupE (VarE "C") (VarE "expr") (VarE "t"))
    (RulePr
      "Expr_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "expr") (CaseE Arg (TupE (ListE (VarE "t")))))
    )
    (RulePr
      "Expr_const"
      (Infix Arg |- (Seq Arg (Atom CONST)))
      (TupE (VarE "C") (VarE "expr"))
    )
  )
)
HintD
(RelD
  "Type_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "type"))
    (typbind "_" (IterT (VarT "deftype") List))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "rectype" (VarT "rectype"))
    (ExpP "dt*" (IterT (VarT "deftype") List))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TYPE) Arg) (TupE (VarE "rectype")))
      (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (ProjE (UncaseE (VarE "x") Arg) 0)
        (LenE (DotE (VarE "C") (Atom TYPES)))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
        (CallE "rolldt" (ExpA (VarE "x")) (ExpA (VarE "rectype")))
      )
    )
    (RulePr
      "Rectype_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (CompE
          (VarE "C")
          (StrE
            (expfield
              (Atom TYPES)
              (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
            )
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
        )
        (VarE "rectype")
        (CaseE (Seq (Atom OK) Arg) (TupE (VarE "x")))
      )
    )
  )
)
HintD
(RelD
  "Tag_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "tag"))
    (typbind "_" (VarT "tagtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "tagtype" (VarT "tagtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "tagtype")))
      (CallE "clos_tagtype" (ExpA (VarE "C")) (ExpA (VarE "tagtype")))
    )
    (RulePr
      "Tagtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "tagtype"))
    )
  )
)
HintD
(RelD
  "Global_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "global"))
    (typbind "_" (VarT "globaltype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "globaltype" (VarT "globaltype"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom GLOBAL) Arg Arg)
        (TupE (VarE "globaltype") (VarE "expr"))
      )
      (VarE "globaltype")
    )
    (RulePr
      "Globaltype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "globaltype"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "globaltype")
        (CaseE
          (Seq Arg Arg)
          (TupE (IterE (CaseE (Atom MUT) (TupE)) Opt) (VarE "t"))
        )
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE (VarE "C") (VarE "expr") (VarE "t"))
    )
  )
)
HintD
(RelD
  "Mem_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "mem"))
    (typbind "_" (VarT "memtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "memtype" (VarT "memtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype")))
      (VarE "memtype")
    )
    (RulePr
      "Memtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "memtype"))
    )
  )
)
HintD
(RelD
  "Table_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "table"))
    (typbind "_" (VarT "tabletype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "tabletype" (VarT "tabletype"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "at" (VarT "addrtype"))
    (ExpP "lim" (VarT "limits"))
    (ExpP "rt" (VarT "reftype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TABLE) Arg Arg) (TupE (VarE "tabletype") (VarE "expr")))
      (VarE "tabletype")
    )
    (RulePr
      "Tabletype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "tabletype"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "tabletype")
        (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt")))
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE
        (VarE "C")
        (VarE "expr")
        (SubE (VarT "reftype") (VarT "valtype") (VarE "rt"))
      )
    )
  )
)
HintD
(RelD
  "Local_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "local"))
    (typbind "_" (VarT "localtype"))
  )
  (RuleD
    "set"
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
      (CaseE (Seq Arg Arg) (TupE (CaseE (Atom SET) (TupE)) (VarE "t")))
    )
    (RulePr
      "Defaultable"
      (Infix (Seq) |- (Seq Arg (Atom DEFAULTABLE)))
      (VarE "t")
    )
  )
  (RuleD
    "unset"
    (ExpP "C" (VarT "context"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom LOCAL) Arg) (TupE (VarE "t")))
      (CaseE (Seq Arg Arg) (TupE (CaseE (Atom UNSET) (TupE)) (VarE "t")))
    )
    (RulePr
      "Nondefaultable"
      (Infix (Seq) |- (Seq Arg (Atom NONDEFAULTABLE)))
      (VarE "t")
    )
  )
)
(RelD
  "Func_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "func"))
    (typbind "_" (VarT "deftype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "local*" (IterT (VarT "local") List))
    (ExpP "expr" (VarT "expr"))
    (ExpP "t_1*" (IterT (VarT "valtype") List))
    (ExpP "t_2*" (IterT (VarT "valtype") List))
    (ExpP "lct*" (IterT (VarT "localtype") List))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupE
          (VarE "x")
          (IterE (VarE "local") List (iterexp "local" (VarE "local*")))
          (VarE "expr")
        )
      )
      (IdxE (DotE (VarE "C") (Atom TYPES)) (ProjE (UncaseE (VarE "x") Arg) 0))
    )
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE
        (IdxE (DotE (VarE "C") (Atom TYPES)) (ProjE (UncaseE (VarE "x") Arg) 0))
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE
            (CaseE
              Arg
              (TupE (IterE (VarE "t_1") List (iterexp "t_1" (VarE "t_1*"))))
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
            )
          )
        )
      )
    )
    (IterPr
      (RulePr
        "Local_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "local") (VarE "lct"))
      )
      List
      (iterexp "lct" (VarE "lct*"))
      (iterexp "local" (VarE "local*"))
    )
    (RulePr
      "Expr_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (CompE
          (VarE "C")
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield
              (Atom LOCALS)
              (CatE
                (IterE
                  (CaseE
                    (Seq Arg Arg)
                    (TupE (CaseE (Atom SET) (TupE)) (VarE "t_1"))
                  )
                  List
                  (iterexp "t_1" (VarE "t_1*"))
                )
                (IterE (VarE "lct") List (iterexp "lct" (VarE "lct*")))
              )
            )
            (expfield
              (Atom LABELS)
              (ListE
                (CaseE
                  Arg
                  (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
                )
              )
            )
            (expfield
              (Atom RETURN)
              (OptE
                (CaseE
                  Arg
                  (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
                )
              )
            )
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
        )
        (VarE "expr")
        (CaseE
          Arg
          (TupE (IterE (VarE "t_2") List (iterexp "t_2" (VarE "t_2*"))))
        )
      )
    )
  )
)
HintD
(RelD
  "Datamode_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "datamode"))
    (typbind "_" (VarT "datatype"))
  )
  (RuleD
    "passive"
    (ExpP "C" (VarT "context"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE (VarE "C") (CaseE (Atom PASSIVE) (TupE)) (CaseE (Atom OK) (TupE)))
  )
  (RuleD
    "active"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "at" (VarT "addrtype"))
    (ExpP "lim" (VarT "limits"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom ACTIVE) Arg Arg) (TupE (VarE "x") (VarE "expr")))
      (CaseE (Atom OK) (TupE))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom MEMS)) (ProjE (UncaseE (VarE "x") Arg) 0))
        (CaseE (Seq Arg Arg (Atom PAGE)) (TupE (VarE "at") (VarE "lim")))
      )
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE
        (VarE "C")
        (VarE "expr")
        (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
      )
    )
  )
)
(RelD
  "Data_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "data"))
    (typbind "_" (VarT "datatype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "b*" (IterT (VarT "byte") List))
    (ExpP "datamode" (VarT "datamode"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom DATA) Arg Arg)
        (TupE
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
          (VarE "datamode")
        )
      )
      (CaseE (Atom OK) (TupE))
    )
    (RulePr
      "Datamode_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "datamode") (CaseE (Atom OK) (TupE)))
    )
  )
)
HintD
(RelD
  "Elemmode_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "elemmode"))
    (typbind "_" (VarT "elemtype"))
  )
  (RuleD
    "passive"
    (ExpP "C" (VarT "context"))
    (ExpP "rt" (VarT "reftype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE (VarE "C") (CaseE (Atom PASSIVE) (TupE)) (VarE "rt"))
  )
  (RuleD
    "declare"
    (ExpP "C" (VarT "context"))
    (ExpP "rt" (VarT "reftype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE (VarE "C") (CaseE (Atom DECLARE) (TupE)) (VarE "rt"))
  )
  (RuleD
    "active"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "expr" (VarT "expr"))
    (ExpP "rt" (VarT "reftype"))
    (ExpP "at" (VarT "addrtype"))
    (ExpP "lim" (VarT "limits"))
    (ExpP "rt'" (VarT "reftype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom ACTIVE) Arg Arg) (TupE (VarE "x") (VarE "expr")))
      (VarE "rt")
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom TABLES))
          (ProjE (UncaseE (VarE "x") Arg) 0)
        )
        (CaseE (Seq Arg Arg Arg) (TupE (VarE "at") (VarE "lim") (VarE "rt'")))
      )
    )
    (RulePr
      "Reftype_sub"
      (Infix Arg |- (Infix Arg <: Arg))
      (TupE (VarE "C") (VarE "rt") (VarE "rt'"))
    )
    (RulePr
      "Expr_ok_const"
      (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
      (TupE
        (VarE "C")
        (VarE "expr")
        (SubE (VarT "addrtype") (VarT "valtype") (VarE "at"))
      )
    )
  )
)
(RelD
  "Elem_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "elem"))
    (typbind "_" (VarT "elemtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "elemtype" (VarT "elemtype"))
    (ExpP "expr*" (IterT (VarT "expr") List))
    (ExpP "elemmode" (VarT "elemmode"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom ELEM) Arg Arg Arg)
        (TupE
          (VarE "elemtype")
          (IterE (VarE "expr") List (iterexp "expr" (VarE "expr*")))
          (VarE "elemmode")
        )
      )
      (VarE "elemtype")
    )
    (RulePr
      "Reftype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "elemtype"))
    )
    (IterPr
      (RulePr
        "Expr_ok_const"
        (Infix Arg |- (Infix Arg : (Seq Arg (Atom CONST))))
        (TupE
          (VarE "C")
          (VarE "expr")
          (SubE (VarT "reftype") (VarT "valtype") (VarE "elemtype"))
        )
      )
      List
      (iterexp "expr" (VarE "expr*"))
    )
    (RulePr
      "Elemmode_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "elemmode") (VarE "elemtype"))
    )
  )
)
HintD
HintD
HintD
(RelD
  "Start_ok"
  (Infix Arg |- (Infix Arg : (Atom OK)))
  (TupT (typbind "_" (VarT "context")) (typbind "_" (VarT "start")))
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (Infix Arg |- (Infix Arg : (Atom OK)))
    (TupE (VarE "C") (CaseE (Seq (Atom START) Arg) (TupE (VarE "x"))))
    (RulePr
      "Expand"
      (Infix Arg ~~ Arg)
      (TupE
        (IdxE (DotE (VarE "C") (Atom FUNCS)) (ProjE (UncaseE (VarE "x") Arg) 0))
        (CaseE
          (Infix (Seq (Atom FUNC) Arg) -> Arg)
          (TupE (CaseE Arg (TupE (ListE))) (CaseE Arg (TupE (ListE))))
        )
      )
    )
  )
)
HintD
HintD
(RelD
  "Import_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "import"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "name_1" (VarT "name"))
    (ExpP "name_2" (VarT "name"))
    (ExpP "xt" (VarT "externtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupE (VarE "name_1") (VarE "name_2") (VarE "xt"))
      )
      (CallE "clos_externtype" (ExpA (VarE "C")) (ExpA (VarE "xt")))
    )
    (RulePr
      "Externtype_ok"
      (Infix Arg |- (Infix Arg : (Atom OK)))
      (TupE (VarE "C") (VarE "xt"))
    )
  )
)
HintD
(RelD
  "Externidx_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "externidx"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    "tag"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "jt" (VarT "tagtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "jt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom TAGS)) (ProjE (UncaseE (VarE "x") Arg) 0))
        (VarE "jt")
      )
    )
  )
  (RuleD
    "global"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "gt" (VarT "globaltype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "gt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom GLOBALS))
          (ProjE (UncaseE (VarE "x") Arg) 0)
        )
        (VarE "gt")
      )
    )
  )
  (RuleD
    "mem"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "mt" (VarT "memtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "mt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom MEMS)) (ProjE (UncaseE (VarE "x") Arg) 0))
        (VarE "mt")
      )
    )
  )
  (RuleD
    "table"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "tt" (VarT "tabletype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "x")))
      (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tt")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE
          (DotE (VarE "C") (Atom TABLES))
          (ProjE (UncaseE (VarE "x") Arg) 0)
        )
        (VarE "tt")
      )
    )
  )
  (RuleD
    "func"
    (ExpP "C" (VarT "context"))
    (ExpP "x" (VarT "idx"))
    (ExpP "dt" (VarT "deftype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "C")
      (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "x")))
      (CaseE
        (Seq (Atom FUNC) Arg)
        (TupE (SubE (VarT "deftype") (VarT "typeuse") (VarE "dt")))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IdxE (DotE (VarE "C") (Atom FUNCS)) (ProjE (UncaseE (VarE "x") Arg) 0))
        (VarE "dt")
      )
    )
  )
)
(RelD
  "Export_ok"
  (Infix Arg |- (Infix Arg : (Seq Arg Arg)))
  (TupT
    (typbind "_" (VarT "context"))
    (typbind "_" (VarT "export"))
    (typbind "_" (VarT "name"))
    (typbind "_" (VarT "externtype"))
  )
  (RuleD
    ""
    (ExpP "C" (VarT "context"))
    (ExpP "name" (VarT "name"))
    (ExpP "externidx" (VarT "externidx"))
    (ExpP "xt" (VarT "externtype"))
    (Infix Arg |- (Infix Arg : (Seq Arg Arg)))
    (TupE
      (VarE "C")
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (VarE "externidx"))
      )
      (VarE "name")
      (VarE "xt")
    )
    (RulePr
      "Externidx_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (VarE "externidx") (VarE "xt"))
    )
  )
)
HintD
HintD
(RecD
  (RelD
    "Globals_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (IterT (VarT "global") List))
      (typbind "_" (IterT (VarT "globaltype") List))
    )
    (RuleD
      "empty"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (ListE) (ListE))
    )
    (RuleD
      "cons"
      (ExpP "C" (VarT "context"))
      (ExpP "global_1" (VarT "global"))
      (ExpP "global*" (IterT (VarT "global") List))
      (ExpP "gt_1" (VarT "globaltype"))
      (ExpP "gt*" (IterT (VarT "globaltype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CatE
          (ListE (VarE "global_1"))
          (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
        )
        (CatE
          (ListE (VarE "gt_1"))
          (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
        )
      )
      (RulePr
        "Global_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "global_1") (VarE "gt_1"))
      )
      (RulePr
        "Globals_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (VarE "C")
            (StrE
              (expfield (Atom TYPES) (ListE))
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE (VarE "gt_1")))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield (Atom LABELS) (ListE))
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
          )
          (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
          (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
        )
      )
    )
  )
)
(RecD
  (RelD
    "Types_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "context"))
      (typbind "_" (IterT (VarT "type") List))
      (typbind "_" (IterT (VarT "deftype") List))
    )
    (RuleD
      "empty"
      (ExpP "C" (VarT "context"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "C") (ListE) (ListE))
    )
    (RuleD
      "cons"
      (ExpP "C" (VarT "context"))
      (ExpP "type_1" (VarT "type"))
      (ExpP "type*" (IterT (VarT "type") List))
      (ExpP "dt_1*" (IterT (VarT "deftype") List))
      (ExpP "dt*" (IterT (VarT "deftype") List))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C")
        (CatE
          (ListE (VarE "type_1"))
          (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
        )
        (CatE
          (IterE (VarE "dt_1") List (iterexp "dt_1" (VarE "dt_1*")))
          (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
        )
      )
      (RulePr
        "Type_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "C")
          (VarE "type_1")
          (IterE (VarE "dt_1") List (iterexp "dt_1" (VarE "dt_1*")))
        )
      )
      (RulePr
        "Types_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (CompE
            (VarE "C")
            (StrE
              (expfield
                (Atom TYPES)
                (IterE (VarE "dt_1") List (iterexp "dt_1" (VarE "dt_1*")))
              )
              (expfield (Atom TAGS) (ListE))
              (expfield (Atom GLOBALS) (ListE))
              (expfield (Atom MEMS) (ListE))
              (expfield (Atom TABLES) (ListE))
              (expfield (Atom FUNCS) (ListE))
              (expfield (Atom DATAS) (ListE))
              (expfield (Atom ELEMS) (ListE))
              (expfield (Atom LOCALS) (ListE))
              (expfield (Atom LABELS) (ListE))
              (expfield (Atom RETURN) (OptE))
              (expfield (Atom REFS) (ListE))
              (expfield (Atom RECS) (ListE))
            )
          )
          (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
          (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
        )
      )
    )
  )
)
(TypD
  "nonfuncs"
  (InstD
    (VariantT
      (typcase
        (Seq Arg Arg Arg Arg Arg Arg)
        (TupT
          (typbind "global*" (IterT (VarT "global") List))
          (typbind "mem*" (IterT (VarT "mem") List))
          (typbind "table*" (IterT (VarT "table") List))
          (typbind "elem*" (IterT (VarT "elem") List))
          (typbind "start?" (IterT (VarT "start") Opt))
          (typbind "export*" (IterT (VarT "export") List))
        )
      )
    )
  )
)
(DecD
  "funcidx_nonfuncs"
  (ExpP "nonfuncs" (VarT "nonfuncs"))
  (IterT (VarT "funcidx") List)
  (DefD
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (ExpA
      (CaseE
        (Seq Arg Arg Arg Arg Arg Arg)
        (TupE
          (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
          (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
          (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
          (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
          (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
          (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
        )
      )
    )
    (CallE
      "funcidx_module"
      (ExpA
        (CaseE
          (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
          (TupE
            (CaseE Arg (TupE (ListE)))
            (CaseE Arg (TupE (ListE)))
            (CaseE Arg (TupE (ListE)))
            (CaseE
              Arg
              (TupE
                (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
              )
            )
            (CaseE
              Arg
              (TupE (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*"))))
            )
            (CaseE
              Arg
              (TupE
                (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
              )
            )
            (CaseE Arg (TupE (ListE)))
            (CaseE Arg (TupE (ListE)))
            (CaseE
              Arg
              (TupE (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*"))))
            )
            (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
            (CaseE
              Arg
              (TupE
                (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
              )
            )
          )
        )
      )
    )
  )
)
(RelD
  "Module_ok"
  (Infix (Seq) |- (Infix Arg : Arg))
  (TupT (typbind "_" (VarT "module")) (typbind "_" (VarT "moduletype")))
  (RuleD
    ""
    (ExpP "type*" (IterT (VarT "type") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "tag*" (IterT (VarT "tag") List))
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (ExpP "C" (VarT "context"))
    (ExpP "xt_I*" (IterT (VarT "externtype") List))
    (ExpP "xt_E*" (IterT (VarT "externtype") List))
    (ExpP "dt'*" (IterT (VarT "deftype") List))
    (ExpP "C'" (VarT "context"))
    (ExpP "jt*" (IterT (VarT "tagtype") List))
    (ExpP "gt*" (IterT (VarT "globaltype") List))
    (ExpP "mt*" (IterT (VarT "memtype") List))
    (ExpP "tt*" (IterT (VarT "tabletype") List))
    (ExpP "dt*" (IterT (VarT "deftype") List))
    (ExpP "ok*" (IterT (VarT "datatype") List))
    (ExpP "rt*" (IterT (VarT "reftype") List))
    (ExpP "nm*" (IterT (VarT "name") List))
    (ExpP "jt_I*" (IterT (VarT "tagtype") List))
    (ExpP "mt_I*" (IterT (VarT "memtype") List))
    (ExpP "tt_I*" (IterT (VarT "tabletype") List))
    (ExpP "gt_I*" (IterT (VarT "globaltype") List))
    (ExpP "dt_I*" (IterT (VarT "deftype") List))
    (ExpP "x*" (IterT (VarT "idx") List))
    (Infix (Seq) |- (Infix Arg : Arg))
    (TupE
      (CaseE
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupE
          (CaseE
            Arg
            (TupE (IterE (VarE "type") List (iterexp "type" (VarE "type*"))))
          )
          (CaseE
            Arg
            (TupE
              (IterE (VarE "import") List (iterexp "import" (VarE "import*")))
            )
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "tag") List (iterexp "tag" (VarE "tag*"))))
          )
          (CaseE
            Arg
            (TupE
              (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
            )
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "table") List (iterexp "table" (VarE "table*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "func") List (iterexp "func" (VarE "func*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "data") List (iterexp "data" (VarE "data*"))))
          )
          (CaseE
            Arg
            (TupE (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*"))))
          )
          (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
          (CaseE
            Arg
            (TupE
              (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
            )
          )
        )
      )
      (CallE
        "clos_moduletype"
        (ExpA (VarE "C"))
        (ExpA
          (CaseE
            (Infix Arg -> Arg)
            (TupE
              (IterE (VarE "xt_I") List (iterexp "xt_I" (VarE "xt_I*")))
              (IterE (VarE "xt_E") List (iterexp "xt_E" (VarE "xt_E*")))
            )
          )
        )
      )
    )
    (RulePr
      "Types_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (StrE
          (expfield (Atom TYPES) (ListE))
          (expfield (Atom TAGS) (ListE))
          (expfield (Atom GLOBALS) (ListE))
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield (Atom FUNCS) (ListE))
          (expfield (Atom DATAS) (ListE))
          (expfield (Atom ELEMS) (ListE))
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
          (expfield (Atom REFS) (ListE))
          (expfield (Atom RECS) (ListE))
        )
        (IterE (VarE "type") List (iterexp "type" (VarE "type*")))
        (IterE (VarE "dt'") List (iterexp "dt'" (VarE "dt'*")))
      )
    )
    (IterPr
      (RulePr
        "Import_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (StrE
            (expfield
              (Atom TYPES)
              (IterE (VarE "dt'") List (iterexp "dt'" (VarE "dt'*")))
            )
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
          (VarE "import")
          (VarE "xt_I")
        )
      )
      List
      (iterexp "import" (VarE "import*"))
      (iterexp "xt_I" (VarE "xt_I*"))
    )
    (IterPr
      (RulePr
        "Tag_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C'") (VarE "tag") (VarE "jt"))
      )
      List
      (iterexp "jt" (VarE "jt*"))
      (iterexp "tag" (VarE "tag*"))
    )
    (RulePr
      "Globals_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "C'")
        (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
        (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
      )
    )
    (IterPr
      (RulePr
        "Mem_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C'") (VarE "mem") (VarE "mt"))
      )
      List
      (iterexp "mem" (VarE "mem*"))
      (iterexp "mt" (VarE "mt*"))
    )
    (IterPr
      (RulePr
        "Table_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C'") (VarE "table") (VarE "tt"))
      )
      List
      (iterexp "table" (VarE "table*"))
      (iterexp "tt" (VarE "tt*"))
    )
    (IterPr
      (RulePr
        "Func_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "func") (VarE "dt"))
      )
      List
      (iterexp "dt" (VarE "dt*"))
      (iterexp "func" (VarE "func*"))
    )
    (IterPr
      (RulePr
        "Data_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "data") (VarE "ok"))
      )
      List
      (iterexp "data" (VarE "data*"))
      (iterexp "ok" (VarE "ok*"))
    )
    (IterPr
      (RulePr
        "Elem_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "C") (VarE "elem") (VarE "rt"))
      )
      List
      (iterexp "elem" (VarE "elem*"))
      (iterexp "rt" (VarE "rt*"))
    )
    (IterPr
      (RulePr
        "Start_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE (VarE "C") (VarE "start"))
      )
      Opt
      (iterexp "start" (VarE "start?"))
    )
    (IterPr
      (RulePr
        "Export_ok"
        (Infix Arg |- (Infix Arg : (Seq Arg Arg)))
        (TupE (VarE "C") (VarE "export") (VarE "nm") (VarE "xt_E"))
      )
      List
      (iterexp "export" (VarE "export*"))
      (iterexp "nm" (VarE "nm*"))
      (iterexp "xt_E" (VarE "xt_E*"))
    )
    (IfPr
      (CallE
        "disjoint_"
        (TypA (VarT "name"))
        (ExpA (IterE (VarE "nm") List (iterexp "nm" (VarE "nm*"))))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C")
        (CompE
          (VarE "C'")
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield
              (Atom TAGS)
              (CatE
                (IterE (VarE "jt_I") List (iterexp "jt_I" (VarE "jt_I*")))
                (IterE (VarE "jt") List (iterexp "jt" (VarE "jt*")))
              )
            )
            (expfield
              (Atom GLOBALS)
              (IterE (VarE "gt") List (iterexp "gt" (VarE "gt*")))
            )
            (expfield
              (Atom MEMS)
              (CatE
                (IterE (VarE "mt_I") List (iterexp "mt_I" (VarE "mt_I*")))
                (IterE (VarE "mt") List (iterexp "mt" (VarE "mt*")))
              )
            )
            (expfield
              (Atom TABLES)
              (CatE
                (IterE (VarE "tt_I") List (iterexp "tt_I" (VarE "tt_I*")))
                (IterE (VarE "tt") List (iterexp "tt" (VarE "tt*")))
              )
            )
            (expfield (Atom FUNCS) (ListE))
            (expfield
              (Atom DATAS)
              (IterE (VarE "ok") List (iterexp "ok" (VarE "ok*")))
            )
            (expfield
              (Atom ELEMS)
              (IterE (VarE "rt") List (iterexp "rt" (VarE "rt*")))
            )
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "C'")
        (StrE
          (expfield
            (Atom TYPES)
            (IterE (VarE "dt'") List (iterexp "dt'" (VarE "dt'*")))
          )
          (expfield (Atom TAGS) (ListE))
          (expfield
            (Atom GLOBALS)
            (IterE (VarE "gt_I") List (iterexp "gt_I" (VarE "gt_I*")))
          )
          (expfield (Atom MEMS) (ListE))
          (expfield (Atom TABLES) (ListE))
          (expfield
            (Atom FUNCS)
            (CatE
              (IterE (VarE "dt_I") List (iterexp "dt_I" (VarE "dt_I*")))
              (IterE (VarE "dt") List (iterexp "dt" (VarE "dt*")))
            )
          )
          (expfield (Atom DATAS) (ListE))
          (expfield (Atom ELEMS) (ListE))
          (expfield (Atom LOCALS) (ListE))
          (expfield (Atom LABELS) (ListE))
          (expfield (Atom RETURN) (OptE))
          (expfield
            (Atom REFS)
            (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
          )
          (expfield (Atom RECS) (ListE))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "x") List (iterexp "x" (VarE "x*")))
        (CallE
          "funcidx_nonfuncs"
          (ExpA
            (CaseE
              (Seq Arg Arg Arg Arg Arg Arg)
              (TupE
                (IterE (VarE "global") List (iterexp "global" (VarE "global*")))
                (IterE (VarE "mem") List (iterexp "mem" (VarE "mem*")))
                (IterE (VarE "table") List (iterexp "table" (VarE "table*")))
                (IterE (VarE "elem") List (iterexp "elem" (VarE "elem*")))
                (IterE (VarE "start") Opt (iterexp "start" (VarE "start?")))
                (IterE (VarE "export") List (iterexp "export" (VarE "export*")))
              )
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "jt_I") List (iterexp "jt_I" (VarE "jt_I*")))
        (CallE
          "tagsxt"
          (ExpA (IterE (VarE "xt_I") List (iterexp "xt_I" (VarE "xt_I*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "gt_I") List (iterexp "gt_I" (VarE "gt_I*")))
        (CallE
          "globalsxt"
          (ExpA (IterE (VarE "xt_I") List (iterexp "xt_I" (VarE "xt_I*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "mt_I") List (iterexp "mt_I" (VarE "mt_I*")))
        (CallE
          "memsxt"
          (ExpA (IterE (VarE "xt_I") List (iterexp "xt_I" (VarE "xt_I*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "tt_I") List (iterexp "tt_I" (VarE "tt_I*")))
        (CallE
          "tablesxt"
          (ExpA (IterE (VarE "xt_I") List (iterexp "xt_I" (VarE "xt_I*"))))
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (IterE (VarE "dt_I") List (iterexp "dt_I" (VarE "dt_I*")))
        (CallE
          "funcsxt"
          (ExpA (IterE (VarE "xt_I") List (iterexp "xt_I" (VarE "xt_I*"))))
        )
      )
    )
  )
)
HintD
HintD
HintD
HintD
(TypD
  "relaxed2"
  (InstD
    (VariantT
      (typcase
        Arg
        (TupT (typbind "i" nat))
        (IfPr
          (BinE
            OrOp
            bool
            (CmpE EqOp bool (VarE "i") (NumE (Nat 0)))
            (CmpE EqOp bool (VarE "i") (NumE (Nat 1)))
          )
        )
      )
    )
  )
)
(TypD
  "relaxed4"
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
                (CmpE EqOp bool (VarE "i") (NumE (Nat 0)))
                (CmpE EqOp bool (VarE "i") (NumE (Nat 1)))
              )
              (CmpE EqOp bool (VarE "i") (NumE (Nat 2)))
            )
            (CmpE EqOp bool (VarE "i") (NumE (Nat 3)))
          )
        )
      )
    )
  )
)
(DecD
  "relaxed2"
  (ExpP "relaxed2" (VarT "relaxed2"))
  (TypP "X")
  (ExpP "X" (VarT "X"))
  (ExpP "X" (VarT "X"))
  (VarT "X")
  (DefD
    (ExpP "i" (VarT "relaxed2"))
    (TypP "X")
    (ExpP "X_1" (VarT "X"))
    (ExpP "X_2" (VarT "X"))
    (ExpA (VarE "i"))
    (TypA (VarT "X"))
    (ExpA (VarE "X_1"))
    (ExpA (VarE "X_2"))
    (IfE
      (CallE "ND")
      (IdxE
        (ListE (VarE "X_1") (VarE "X_2"))
        (ProjE (UncaseE (VarE "i") Arg) 0)
      )
      (IdxE (ListE (VarE "X_1") (VarE "X_2")) (NumE (Nat 0)))
    )
  )
)
HintD
(DecD
  "relaxed4"
  (ExpP "relaxed4" (VarT "relaxed4"))
  (TypP "X")
  (ExpP "X" (VarT "X"))
  (ExpP "X" (VarT "X"))
  (ExpP "X" (VarT "X"))
  (ExpP "X" (VarT "X"))
  (VarT "X")
  (DefD
    (ExpP "i" (VarT "relaxed4"))
    (TypP "X")
    (ExpP "X_1" (VarT "X"))
    (ExpP "X_2" (VarT "X"))
    (ExpP "X_3" (VarT "X"))
    (ExpP "X_4" (VarT "X"))
    (ExpA (VarE "i"))
    (TypA (VarT "X"))
    (ExpA (VarE "X_1"))
    (ExpA (VarE "X_2"))
    (ExpA (VarE "X_3"))
    (ExpA (VarE "X_4"))
    (IfE
      (CallE "ND")
      (IdxE
        (ListE (VarE "X_1") (VarE "X_2") (VarE "X_3") (VarE "X_4"))
        (ProjE (UncaseE (VarE "i") Arg) 0)
      )
      (IdxE
        (ListE (VarE "X_1") (VarE "X_2") (VarE "X_3") (VarE "X_4"))
        (NumE (Nat 0))
      )
    )
  )
)
HintD
(DecD "R_fmadd" (VarT "relaxed2"))
HintD
(DecD "R_fmin" (VarT "relaxed4"))
HintD
(DecD "R_fmax" (VarT "relaxed4"))
HintD
(DecD "R_idot" (VarT "relaxed2"))
HintD
(DecD "R_iq15mulr" (VarT "relaxed2"))
HintD
(DecD "R_trunc_u" (VarT "relaxed4"))
HintD
(DecD "R_trunc_s" (VarT "relaxed2"))
HintD
(DecD "R_swizzle" (VarT "relaxed2"))
HintD
(DecD "R_laneselect" (VarT "relaxed2"))
HintD
(DecD "s33_to_u32" (ExpP "s33" (VarT "s33")) (VarT "u32"))
HintD
(DecD
  "ibits_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (IterT (VarT "bit") List)
)
HintD
(DecD
  "fbits_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "bit") List)
)
HintD
(DecD
  "ibytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (IterT (VarT "byte") List)
)
HintD
(DecD
  "fbytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "byte") List)
)
HintD
(DecD
  "nbytes_"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (IterT (VarT "byte") List)
)
HintD
(DecD
  "vbytes_"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (IterT (VarT "byte") List)
)
HintD
(DecD
  "zbytes_"
  (ExpP "storagetype" (VarT "storagetype"))
  (ExpP "lit_" (VarT "lit_" (ExpA (VarE "storagetype"))))
  (IterT (VarT "byte") List)
)
HintD
(DecD
  "cbytes_"
  (ExpP "Cnn" (VarT "Cnn"))
  (ExpP
    "lit_"
    (VarT "lit_" (ExpA (SubE (VarT "Cnn") (VarT "storagetype") (VarE "Cnn"))))
  )
  (IterT (VarT "byte") List)
)
HintD
(DecD
  "inv_ibits_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "bit") List))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "inv_fbits_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "bit") List))
  (VarT "fN" (ExpA (VarE "N")))
)
HintD
(DecD
  "inv_ibytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "inv_fbytes_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "fN" (ExpA (VarE "N")))
)
HintD
(DecD
  "inv_nbytes_"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "num_" (ExpA (VarE "numtype")))
)
HintD
(DecD
  "inv_vbytes_"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "vec_" (ExpA (VarE "vectype")))
)
HintD
(DecD
  "inv_zbytes_"
  (ExpP "storagetype" (VarT "storagetype"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "lit_" (ExpA (VarE "storagetype")))
)
HintD
(DecD
  "inv_cbytes_"
  (ExpP "Cnn" (VarT "Cnn"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "lit_" (ExpA (SubE (VarT "Cnn") (VarT "storagetype") (VarE "Cnn"))))
)
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(DecD
  "signed_"
  (ExpP "N" (VarT "N"))
  (ExpP "nat" nat)
  int
  (DefD
    (ExpP "N" nat)
    (ExpP "i" nat)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (CvtE nat int (VarE "i"))
    (IfPr
      (CmpE
        LtOp
        nat
        (VarE "i")
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
  (DefD
    (ExpP "N" nat)
    (ExpP "i" nat)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (BinE
      SubOp
      int
      (CvtE nat int (VarE "i"))
      (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LeOp
          nat
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
          (VarE "i")
        )
        (CmpE LtOp nat (VarE "i") (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
      )
    )
  )
)
HintD
(DecD
  "inv_signed_"
  (ExpP "N" (VarT "N"))
  (ExpP "int" int)
  nat
  (DefD
    (ExpP "N" nat)
    (ExpP "i" int)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (CvtE int nat (VarE "i"))
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE LeOp int (CvtE nat int (NumE (Nat 0))) (VarE "i"))
        (CmpE
          LtOp
          int
          (VarE "i")
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
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i" int)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (CvtE
      int
      nat
      (BinE
        AddOp
        int
        (VarE "i")
        (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
      )
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          LeOp
          int
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
          (VarE "i")
        )
        (CmpE LtOp int (VarE "i") (CvtE nat int (NumE (Nat 0))))
      )
    )
  )
)
HintD
(DecD
  "sx"
  (ExpP "storagetype" (VarT "storagetype"))
  (IterT (VarT "sx") Opt)
  (DefD
    (ExpP "consttype" (VarT "consttype"))
    (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
    (OptE)
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (OptE (CaseE (Atom S) (TupE)))
  )
)
HintD
(DecD
  "zero"
  (ExpP "lanetype" (VarT "lanetype"))
  (VarT "lane_" (ExpA (VarE "lanetype")))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
    (CaseE
      (Seq (Atom mk_lane__2) Arg Arg)
      (TupE (VarE "Jnn") (CaseE Arg (TupE (NumE (Nat 0)))))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn")))
    (CaseE
      (Seq (Atom mk_lane__0) Arg Arg)
      (TupE
        (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
        (CaseE
          (Seq (Atom mk_num__1) Arg Arg)
          (TupE
            (VarE "Fnn")
            (CallE
              "fzero"
              (ExpA
                (CallE
                  "size"
                  (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
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
(DecD
  "bool"
  (ExpP "bool" BoolT)
  nat
  (DefD (ExpA (BoolE false)) (NumE (Nat 0)))
  (DefD (ExpA (BoolE true)) (NumE (Nat 1)))
)
(DecD "truncz" (ExpP "rat" rat) int)
HintD
(DecD "ceilz" (ExpP "rat" rat) int)
HintD
HintD
(DecD
  "sat_u_"
  (ExpP "N" (VarT "N"))
  (ExpP "int" int)
  nat
  (DefD
    (ExpP "N" nat)
    (ExpP "i" int)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (IfE
      (CmpE LtOp int (VarE "i") (CvtE nat int (NumE (Nat 0))))
      (NumE (Nat 0))
      (IfE
        (CmpE
          GtOp
          int
          (VarE "i")
          (BinE
            SubOp
            int
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
            (CvtE nat int (NumE (Nat 1)))
          )
        )
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
        (CvtE int nat (VarE "i"))
      )
    )
  )
)
HintD
(DecD
  "sat_s_"
  (ExpP "N" (VarT "N"))
  (ExpP "int" int)
  int
  (DefD
    (ExpP "N" nat)
    (ExpP "i" int)
    (ExpA (VarE "N"))
    (ExpA (VarE "i"))
    (IfE
      (CmpE
        LtOp
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
      (IfE
        (CmpE
          GtOp
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
        (VarE "i")
      )
    )
  )
)
HintD
(DecD
  "ineg_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (CaseE
      Arg
      (TupE
        (CvtE
          int
          nat
          (BinE
            ModOp
            int
            (BinE
              SubOp
              int
              (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
              (CvtE nat int (ProjE (UncaseE (VarE "i_1") Arg) 0))
            )
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
          )
        )
      )
    )
  )
)
(DecD
  "iabs_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (IfE
      (CmpE
        GeOp
        int
        (CallE
          "signed_"
          (ExpA (VarE "N"))
          (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
        )
        (CvtE nat int (NumE (Nat 0)))
      )
      (VarE "i_1")
      (CallE "ineg_" (ExpA (VarE "N")) (ExpA (VarE "i_1")))
    )
  )
)
(DecD
  "iclz_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ictz_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ipopcnt_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "iextend_"
  (ExpP "N" (VarT "N"))
  (ExpP "M" (VarT "M"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "M" nat)
    (ExpP "i" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "M"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i"))
    (CaseE
      Arg
      (TupE
        (BinE
          ModOp
          nat
          (ProjE (UncaseE (VarE "i") Arg) 0)
          (BinE PowOp nat (NumE (Nat 2)) (VarE "M"))
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "M" nat)
    (ExpP "i" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "M"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i"))
    (CaseE
      Arg
      (TupE
        (CallE
          "inv_signed_"
          (ExpA (VarE "N"))
          (ExpA
            (CallE
              "signed_"
              (ExpA (VarE "M"))
              (ExpA
                (BinE
                  ModOp
                  nat
                  (ProjE (UncaseE (VarE "i") Arg) 0)
                  (BinE PowOp nat (NumE (Nat 2)) (VarE "M"))
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
(DecD
  "iadd_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (BinE
          ModOp
          nat
          (BinE
            AddOp
            nat
            (ProjE (UncaseE (VarE "i_1") Arg) 0)
            (ProjE (UncaseE (VarE "i_2") Arg) 0)
          )
          (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
        )
      )
    )
  )
)
(DecD
  "isub_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CvtE
          int
          nat
          (BinE
            ModOp
            int
            (BinE
              SubOp
              int
              (CvtE
                nat
                int
                (BinE
                  AddOp
                  nat
                  (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
                  (ProjE (UncaseE (VarE "i_1") Arg) 0)
                )
              )
              (CvtE nat int (ProjE (UncaseE (VarE "i_2") Arg) 0))
            )
            (CvtE nat int (BinE PowOp nat (NumE (Nat 2)) (VarE "N")))
          )
        )
      )
    )
  )
)
(DecD
  "imul_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (BinE
          ModOp
          nat
          (BinE
            MulOp
            nat
            (ProjE (UncaseE (VarE "i_1") Arg) 0)
            (ProjE (UncaseE (VarE "i_2") Arg) 0)
          )
          (BinE PowOp nat (NumE (Nat 2)) (VarE "N"))
        )
      )
    )
  )
)
(DecD
  "idiv_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) Opt)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CvtE
            int
            nat
            (CallE
              "truncz"
              (ExpA
                (BinE
                  DivOp
                  rat
                  (CvtE nat rat (ProjE (UncaseE (VarE "i_1") Arg) 0))
                  (CvtE nat rat (ProjE (UncaseE (VarE "i_2") Arg) 0))
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE)
    (IfPr
      (CmpE
        EqOp
        bool
        (BinE
          DivOp
          rat
          (CvtE
            int
            rat
            (CallE
              "signed_"
              (ExpA (VarE "N"))
              (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
            )
          )
          (CvtE
            int
            rat
            (CallE
              "signed_"
              (ExpA (VarE "N"))
              (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
            )
          )
        )
        (CvtE
          nat
          rat
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
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CallE
            "inv_signed_"
            (ExpA (VarE "N"))
            (ExpA
              (CallE
                "truncz"
                (ExpA
                  (BinE
                    DivOp
                    rat
                    (CvtE
                      int
                      rat
                      (CallE
                        "signed_"
                        (ExpA (VarE "N"))
                        (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
                      )
                    )
                    (CvtE
                      int
                      rat
                      (CallE
                        "signed_"
                        (ExpA (VarE "N"))
                        (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
                      )
                    )
                  )
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
(DecD
  "irem_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) Opt)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CvtE
            int
            nat
            (BinE
              SubOp
              int
              (CvtE nat int (ProjE (UncaseE (VarE "i_1") Arg) 0))
              (CvtE
                nat
                int
                (BinE
                  MulOp
                  nat
                  (ProjE (UncaseE (VarE "i_2") Arg) 0)
                  (CvtE
                    int
                    nat
                    (CallE
                      "truncz"
                      (ExpA
                        (BinE
                          DivOp
                          rat
                          (CvtE nat rat (ProjE (UncaseE (VarE "i_1") Arg) 0))
                          (CvtE nat rat (ProjE (UncaseE (VarE "i_2") Arg) 0))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
    (OptE)
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "j_1" int)
    (ExpP "j_2" int)
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (OptE
      (CaseE
        Arg
        (TupE
          (CallE
            "inv_signed_"
            (ExpA (VarE "N"))
            (ExpA
              (BinE
                SubOp
                int
                (VarE "j_1")
                (BinE
                  MulOp
                  int
                  (VarE "j_2")
                  (CallE
                    "truncz"
                    (ExpA
                      (BinE
                        DivOp
                        rat
                        (CvtE int rat (VarE "j_1"))
                        (CvtE int rat (VarE "j_2"))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          EqOp
          bool
          (VarE "j_1")
          (CallE
            "signed_"
            (ExpA (VarE "N"))
            (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
          )
        )
        (CmpE
          EqOp
          bool
          (VarE "j_2")
          (CallE
            "signed_"
            (ExpA (VarE "N"))
            (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
          )
        )
      )
    )
  )
)
HintD
(DecD
  "imin_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (VarE "i_1")
    (IfPr
      (CmpE
        LeOp
        nat
        (ProjE (UncaseE (VarE "i_1") Arg) 0)
        (ProjE (UncaseE (VarE "i_2") Arg) 0)
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (VarE "i_2")
    (IfPr
      (CmpE
        GtOp
        nat
        (ProjE (UncaseE (VarE "i_1") Arg) 0)
        (ProjE (UncaseE (VarE "i_2") Arg) 0)
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (IfE
      (CmpE
        LeOp
        int
        (CallE
          "signed_"
          (ExpA (VarE "N"))
          (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
        )
        (CallE
          "signed_"
          (ExpA (VarE "N"))
          (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
        )
      )
      (VarE "i_1")
      (VarE "i_2")
    )
  )
)
HintD
(DecD
  "imax_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (VarE "i_1")
    (IfPr
      (CmpE
        GeOp
        nat
        (ProjE (UncaseE (VarE "i_1") Arg) 0)
        (ProjE (UncaseE (VarE "i_2") Arg) 0)
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (VarE "i_2")
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (UncaseE (VarE "i_1") Arg) 0)
        (ProjE (UncaseE (VarE "i_2") Arg) 0)
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (IfE
      (CmpE
        GeOp
        int
        (CallE
          "signed_"
          (ExpA (VarE "N"))
          (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
        )
        (CallE
          "signed_"
          (ExpA (VarE "N"))
          (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
        )
      )
      (VarE "i_1")
      (VarE "i_2")
    )
  )
)
HintD
(DecD
  "iadd_sat_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "sat_u_"
          (ExpA (VarE "N"))
          (ExpA
            (CvtE
              nat
              int
              (BinE
                AddOp
                nat
                (ProjE (UncaseE (VarE "i_1") Arg) 0)
                (ProjE (UncaseE (VarE "i_2") Arg) 0)
              )
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "inv_signed_"
          (ExpA (VarE "N"))
          (ExpA
            (CallE
              "sat_s_"
              (ExpA (VarE "N"))
              (ExpA
                (BinE
                  AddOp
                  int
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
                  )
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
                  )
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
(DecD
  "isub_sat_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "sat_u_"
          (ExpA (VarE "N"))
          (ExpA
            (BinE
              SubOp
              int
              (CvtE nat int (ProjE (UncaseE (VarE "i_1") Arg) 0))
              (CvtE nat int (ProjE (UncaseE (VarE "i_2") Arg) 0))
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "inv_signed_"
          (ExpA (VarE "N"))
          (ExpA
            (CallE
              "sat_s_"
              (ExpA (VarE "N"))
              (ExpA
                (BinE
                  SubOp
                  int
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
                  )
                  (CallE
                    "signed_"
                    (ExpA (VarE "N"))
                    (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
                  )
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
(DecD
  "iq15mulr_sat_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "irelaxed_q15mulr_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) List)
)
HintD
(DecD
  "iavgr_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "inot_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "irev_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "iand_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "iandnot_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ior_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ixor_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ishl_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "u32" (VarT "u32"))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ishr_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "u32" (VarT "u32"))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "irotl_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "irotr_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "ibitselect_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "irelaxed_laneselect_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) List)
)
(DecD
  "ieqz_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE EqOp bool (ProjE (UncaseE (VarE "i_1") Arg) 0) (NumE (Nat 0)))
          )
        )
      )
    )
  )
)
(DecD
  "inez_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE NeOp bool (ProjE (UncaseE (VarE "i_1") Arg) 0) (NumE (Nat 0)))
          )
        )
      )
    )
  )
)
(DecD
  "ieq_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE (CallE "bool" (ExpA (CmpE EqOp bool (VarE "i_1") (VarE "i_2")))))
    )
  )
)
(DecD
  "ine_"
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE (CallE "bool" (ExpA (CmpE NeOp bool (VarE "i_1") (VarE "i_2")))))
    )
  )
)
(DecD
  "ilt_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LtOp
              nat
              (ProjE (UncaseE (VarE "i_1") Arg) 0)
              (ProjE (UncaseE (VarE "i_2") Arg) 0)
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LtOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
              )
            )
          )
        )
      )
    )
  )
)
HintD
(DecD
  "igt_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GtOp
              nat
              (ProjE (UncaseE (VarE "i_1") Arg) 0)
              (ProjE (UncaseE (VarE "i_2") Arg) 0)
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GtOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
              )
            )
          )
        )
      )
    )
  )
)
HintD
(DecD
  "ile_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LeOp
              nat
              (ProjE (UncaseE (VarE "i_1") Arg) 0)
              (ProjE (UncaseE (VarE "i_2") Arg) 0)
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              LeOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
              )
            )
          )
        )
      )
    )
  )
)
HintD
(DecD
  "ige_"
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "u32")
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom U) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GeOp
              nat
              (ProjE (UncaseE (VarE "i_1") Arg) 0)
              (ProjE (UncaseE (VarE "i_2") Arg) 0)
            )
          )
        )
      )
    )
  )
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1" (VarT "uN" (ExpA (VarE "N"))))
    (ExpP "i_2" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (CaseE (Atom S) (TupE)))
    (ExpA (VarE "i_1"))
    (ExpA (VarE "i_2"))
    (CaseE
      Arg
      (TupE
        (CallE
          "bool"
          (ExpA
            (CmpE
              GeOp
              int
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_1") Arg) 0))
              )
              (CallE
                "signed_"
                (ExpA (VarE "N"))
                (ExpA (ProjE (UncaseE (VarE "i_2") Arg) 0))
              )
            )
          )
        )
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
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(DecD
  "fabs_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fneg_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fsqrt_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fceil_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "ffloor_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "ftrunc_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fnearest_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fadd_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fsub_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fmul_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fdiv_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fmin_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fmax_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fpmin_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "fpmax_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "frelaxed_min_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
HintD
(DecD
  "frelaxed_max_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
HintD
(DecD
  "fcopysign_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "feq_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (VarT "u32")
)
(DecD
  "fne_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (VarT "u32")
)
(DecD
  "flt_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (VarT "u32")
)
(DecD
  "fgt_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (VarT "u32")
)
(DecD
  "fle_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (VarT "u32")
)
(DecD
  "fge_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (VarT "u32")
)
(DecD
  "frelaxed_madd_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
HintD
(DecD
  "frelaxed_nmadd_"
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(DecD
  "wrap__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "M"))))
  (VarT "iN" (ExpA (VarE "N")))
)
(DecD
  "extend__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "M"))))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "trunc__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "M"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) Opt)
)
HintD
(DecD
  "trunc_sat__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "M"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) Opt)
)
HintD
(DecD
  "relaxed_trunc__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "M"))))
  (IterT (VarT "iN" (ExpA (VarE "N"))) Opt)
)
HintD
(DecD
  "demote__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "M"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "promote__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "fN" (VarT "fN" (ExpA (VarE "M"))))
  (IterT (VarT "fN" (ExpA (VarE "N"))) List)
)
(DecD
  "convert__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "M"))))
  (VarT "fN" (ExpA (VarE "N")))
)
HintD
(DecD
  "narrow__"
  (ExpP "M" (VarT "M"))
  (ExpP "N" (VarT "N"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "M"))))
  (VarT "iN" (ExpA (VarE "N")))
)
HintD
(DecD
  "reinterpret__"
  (ExpP "numtype_1" (VarT "numtype"))
  (ExpP "numtype_2" (VarT "numtype"))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype_1"))))
  (VarT "num_" (ExpA (VarE "numtype_2")))
)
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(DecD
  "lpacknum_"
  (ExpP "lanetype" (VarT "lanetype"))
  (ExpP "num_" (VarT "num_" (ExpA (CallE "lunpack" (ExpA (VarE "lanetype"))))))
  (VarT "lane_" (ExpA (VarE "lanetype")))
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "c" (VarT "num_" (ExpA (VarE "numtype"))))
    (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
    (ExpA (VarE "c"))
    (CaseE (Seq (Atom mk_lane__0) Arg Arg) (TupE (VarE "numtype") (VarE "c")))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "c" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
    (ExpA
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
      )
    )
    (CaseE
      (Seq (Atom mk_lane__1) Arg Arg)
      (TupE
        (VarE "packtype")
        (CallE
          "wrap__"
          (ExpA
            (CallE
              "size"
              (ExpA
                (CallE
                  "lunpack"
                  (ExpA
                    (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype"))
                  )
                )
              )
            )
          )
          (ExpA (CallE "psize" (ExpA (VarE "packtype"))))
          (ExpA (VarE "c"))
        )
      )
    )
  )
)
HintD
(DecD
  "cpacknum_"
  (ExpP "storagetype" (VarT "storagetype"))
  (ExpP
    "lit_"
    (VarT
      "lit_"
      (ExpA
        (SubE
          (VarT "consttype")
          (VarT "storagetype")
          (CallE "cunpack" (ExpA (VarE "storagetype")))
        )
      )
    )
  )
  (VarT "lit_" (ExpA (VarE "storagetype")))
  (DefD
    (ExpP "consttype" (VarT "consttype"))
    (ExpP
      "c"
      (VarT
        "lit_"
        (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
      )
    )
    (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
    (ExpA (VarE "c"))
    (VarE "c")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "c" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (ExpA
      (CaseE
        (Seq (Atom mk_lit__0) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_num__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "c"))
          )
        )
      )
    )
    (CaseE
      (Seq (Atom mk_lit__2) Arg Arg)
      (TupE
        (VarE "packtype")
        (CallE
          "wrap__"
          (ExpA
            (CallE
              "size"
              (ExpA
                (CallE
                  "lunpack"
                  (ExpA
                    (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype"))
                  )
                )
              )
            )
          )
          (ExpA (CallE "psize" (ExpA (VarE "packtype"))))
          (ExpA (VarE "c"))
        )
      )
    )
  )
)
HintD
(DecD
  "lunpacknum_"
  (ExpP "lanetype" (VarT "lanetype"))
  (ExpP "lane_" (VarT "lane_" (ExpA (VarE "lanetype"))))
  (VarT "num_" (ExpA (CallE "lunpack" (ExpA (VarE "lanetype")))))
  (DefD
    (ExpP "numtype" (VarT "numtype"))
    (ExpP "c" (VarT "num_" (ExpA (VarE "numtype"))))
    (ExpA (SubE (VarT "numtype") (VarT "lanetype") (VarE "numtype")))
    (ExpA
      (CaseE (Seq (Atom mk_lane__0) Arg Arg) (TupE (VarE "numtype") (VarE "c")))
    )
    (VarE "c")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "c" (VarT "uN" (ExpA (CallE "psize" (ExpA (VarE "packtype"))))))
    (ExpA (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype")))
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__1) Arg Arg)
        (TupE (VarE "packtype") (VarE "c"))
      )
    )
    (CaseE
      (Seq (Atom mk_num__0) Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CallE
          "extend__"
          (ExpA (CallE "psize" (ExpA (VarE "packtype"))))
          (ExpA
            (CallE
              "size"
              (ExpA
                (CallE
                  "lunpack"
                  (ExpA
                    (SubE (VarT "packtype") (VarT "lanetype") (VarE "packtype"))
                  )
                )
              )
            )
          )
          (ExpA (CaseE (Atom U) (TupE)))
          (ExpA (VarE "c"))
        )
      )
    )
  )
)
HintD
(DecD
  "cunpacknum_"
  (ExpP "storagetype" (VarT "storagetype"))
  (ExpP "lit_" (VarT "lit_" (ExpA (VarE "storagetype"))))
  (VarT
    "lit_"
    (ExpA
      (SubE
        (VarT "consttype")
        (VarT "storagetype")
        (CallE "cunpack" (ExpA (VarE "storagetype")))
      )
    )
  )
  (DefD
    (ExpP "consttype" (VarT "consttype"))
    (ExpP
      "c"
      (VarT
        "lit_"
        (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
      )
    )
    (ExpA (SubE (VarT "consttype") (VarT "storagetype") (VarE "consttype")))
    (ExpA (VarE "c"))
    (VarE "c")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "c" (VarT "uN" (ExpA (CallE "psize" (ExpA (VarE "packtype"))))))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (ExpA
      (CaseE (Seq (Atom mk_lit__2) Arg Arg) (TupE (VarE "packtype") (VarE "c")))
    )
    (CaseE
      (Seq (Atom mk_lit__0) Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_num__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "extend__"
              (ExpA (CallE "psize" (ExpA (VarE "packtype"))))
              (ExpA
                (CallE
                  "size"
                  (ExpA
                    (CallE
                      "lunpack"
                      (ExpA
                        (SubE
                          (VarT "packtype")
                          (VarT "lanetype")
                          (VarE "packtype")
                        )
                      )
                    )
                  )
                )
              )
              (ExpA (CaseE (Atom U) (TupE)))
              (ExpA (VarE "c"))
            )
          )
        )
      )
    )
  )
)
HintD
(DecD
  "unop_"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "unop_" (VarT "unop_" (ExpA (VarE "numtype"))))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (IterT (VarT "num_" (ExpA (VarE "numtype"))) List)
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom CLZ) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i"))))
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "iclz_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom CTZ) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i"))))
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "ictz_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom POPCNT) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i"))))
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "ipopcnt_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "M" nat)
    (ExpP
      "i"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CaseE (Seq (Atom EXTEND) Arg) (TupE (CaseE Arg (TupE (VarE "M")))))
        )
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i"))))
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "iextend_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "M"))
            (ExpA (CaseE (Atom S) (TupE)))
            (ExpA (VarE "i"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom ABS) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fabs_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom NEG) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fneg_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom SQRT) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fsqrt_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom CEIL) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fceil_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom FLOOR) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "ffloor_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom TRUNC) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "ftrunc_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom NEAREST) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f"))))
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fnearest_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f"))
        )
      )
    )
  )
)
HintD
(DecD
  "binop_"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "binop_" (VarT "binop_" (ExpA (VarE "numtype"))))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (IterT (VarT "num_" (ExpA (VarE "numtype"))) List)
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "iadd_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "isub_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "imul_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom DIV) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (LiftE
          (CallE
            "idiv_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom REM) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (LiftE
          (CallE
            "irem_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom AND) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "iand_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom OR) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "ior_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom XOR) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "ixor_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom SHL) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "ishl_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (CaseE Arg (TupE (ProjE (UncaseE (VarE "i_2") Arg) 0))))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "ishr_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "i_1"))
            (ExpA (CaseE Arg (TupE (ProjE (UncaseE (VarE "i_2") Arg) 0))))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom ROTL) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "irotl_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom ROTR) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn")
          (CallE
            "irotr_"
            (ExpA
              (CallE
                "sizenn"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
              )
            )
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fadd_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fsub_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fmul_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom DIV) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fdiv_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom MIN) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fmin_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom MAX) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fmax_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom COPYSIGN) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (IterE
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "iter_0")))
      List
      (iterexp
        "iter_0"
        (CallE
          "fcopysign_"
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (VarE "f_1"))
          (ExpA (VarE "f_2"))
        )
      )
    )
  )
)
HintD
(DecD
  "testop_"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "testop_" (VarT "testop_" (ExpA (VarE "numtype"))))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (VarT "u32")
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom EQZ) (TupE)))
      )
    )
    (ExpA (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i"))))
    (CallE
      "ieqz_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "i"))
    )
  )
)
HintD
(DecD
  "relop_"
  (ExpP "numtype" (VarT "numtype"))
  (ExpP "relop_" (VarT "relop_" (ExpA (VarE "numtype"))))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype"))))
  (VarT "u32")
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (CallE
      "ieq_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "i_1"))
      (ExpA (VarE "i_2"))
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (CallE
      "ine_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "i_1"))
      (ExpA (VarE "i_2"))
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom LT) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (CallE
      "ilt_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "sx"))
      (ExpA (VarE "i_1"))
      (ExpA (VarE "i_2"))
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom GT) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (CallE
      "igt_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "sx"))
      (ExpA (VarE "i_1"))
      (ExpA (VarE "i_2"))
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom LE) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (CallE
      "ile_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "sx"))
      (ExpA (VarE "i_1"))
      (ExpA (VarE "i_2"))
    )
  )
  (DefD
    (ExpP "Inn" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpP
      "i_2"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (CaseE (Seq (Atom GE) Arg) (TupE (VarE "sx"))))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn") (VarE "i_2")))
    )
    (CallE
      "ige_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn")))
        )
      )
      (ExpA (VarE "sx"))
      (ExpA (VarE "i_1"))
      (ExpA (VarE "i_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (CallE
      "feq_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
      (ExpA (VarE "f_1"))
      (ExpA (VarE "f_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (CallE
      "fne_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
      (ExpA (VarE "f_1"))
      (ExpA (VarE "f_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom LT) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (CallE
      "flt_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
      (ExpA (VarE "f_1"))
      (ExpA (VarE "f_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom GT) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (CallE
      "fgt_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
      (ExpA (VarE "f_1"))
      (ExpA (VarE "f_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom LE) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (CallE
      "fle_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
      (ExpA (VarE "f_1"))
      (ExpA (VarE "f_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpP
      "f_2"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (CaseE (Atom GE) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_1")))
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn") (VarE "f_2")))
    )
    (CallE
      "fge_"
      (ExpA
        (CallE
          "sizenn"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
        )
      )
      (ExpA (VarE "f_1"))
      (ExpA (VarE "f_2"))
    )
  )
)
HintD
(DecD
  "cvtop__"
  (ExpP "numtype_1" (VarT "numtype"))
  (ExpP "numtype_2" (VarT "numtype"))
  (ExpP
    "cvtop__"
    (VarT "cvtop__" (ExpA (VarE "numtype_1")) (ExpA (VarE "numtype_2")))
  )
  (ExpP "num_" (VarT "num_" (ExpA (VarE "numtype_1"))))
  (IterT (VarT "num_" (ExpA (VarE "numtype_2"))) List)
  (DefD
    (ExpP "Inn_1" (VarT "addrtype"))
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___0) Arg Arg Arg)
        (TupE
          (VarE "Inn_1")
          (VarE "Inn_2")
          (CaseE (Seq (Atom EXTEND) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn_1") (VarE "i_1")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn_2")
          (CallE
            "extend__"
            (ExpA
              (CallE
                "sizenn1"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
              )
            )
            (ExpA
              (CallE
                "sizenn2"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "i_1"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn_1" (VarT "addrtype"))
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___0) Arg Arg Arg)
        (TupE (VarE "Inn_1") (VarE "Inn_2") (CaseE (Atom WRAP) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn_1") (VarE "i_1")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE
          (VarE "Inn_2")
          (CallE
            "wrap__"
            (ExpA
              (CallE
                "sizenn1"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
              )
            )
            (ExpA
              (CallE
                "sizenn2"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
              )
            )
            (ExpA (VarE "i_1"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___2) Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "Inn_2")
          (CaseE (Seq (Atom TRUNC) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn_1") (VarE "f_1")))
    )
    (IterE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE (VarE "Inn_2") (VarE "iter_0"))
      )
      List
      (iterexp
        "iter_0"
        (LiftE
          (CallE
            "trunc__"
            (ExpA
              (CallE
                "sizenn1"
                (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
              )
            )
            (ExpA
              (CallE
                "sizenn2"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "f_1"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___2) Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "Inn_2")
          (CaseE (Seq (Atom TRUNC_SAT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn_1") (VarE "f_1")))
    )
    (IterE
      (CaseE
        (Seq (Atom mk_num__0) Arg Arg)
        (TupE (VarE "Inn_2") (VarE "iter_0"))
      )
      List
      (iterexp
        "iter_0"
        (LiftE
          (CallE
            "trunc_sat__"
            (ExpA
              (CallE
                "sizenn1"
                (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
              )
            )
            (ExpA
              (CallE
                "sizenn2"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "f_1"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Inn_1" (VarT "addrtype"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___1) Arg Arg Arg)
        (TupE
          (VarE "Inn_1")
          (VarE "Fnn_2")
          (CaseE (Seq (Atom CONVERT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn_1") (VarE "i_1")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_num__1) Arg Arg)
        (TupE
          (VarE "Fnn_2")
          (CallE
            "convert__"
            (ExpA
              (CallE
                "sizenn1"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
              )
            )
            (ExpA
              (CallE
                "sizenn2"
                (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
              )
            )
            (ExpA (VarE "sx"))
            (ExpA (VarE "i_1"))
          )
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___3) Arg Arg Arg)
        (TupE (VarE "Fnn_1") (VarE "Fnn_2") (CaseE (Atom PROMOTE) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn_1") (VarE "f_1")))
    )
    (IterE
      (CaseE
        (Seq (Atom mk_num__1) Arg Arg)
        (TupE (VarE "Fnn_2") (VarE "iter_0"))
      )
      List
      (iterexp
        "iter_0"
        (CallE
          "promote__"
          (ExpA
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
            )
          )
          (ExpA
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
            )
          )
          (ExpA (VarE "f_1"))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___3) Arg Arg Arg)
        (TupE (VarE "Fnn_1") (VarE "Fnn_2") (CaseE (Atom DEMOTE) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn_1") (VarE "f_1")))
    )
    (IterE
      (CaseE
        (Seq (Atom mk_num__1) Arg Arg)
        (TupE (VarE "Fnn_2") (VarE "iter_0"))
      )
      List
      (iterexp
        "iter_0"
        (CallE
          "demote__"
          (ExpA
            (CallE
              "sizenn1"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
            )
          )
          (ExpA
            (CallE
              "sizenn2"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
            )
          )
          (ExpA (VarE "f_1"))
        )
      )
    )
  )
  (DefD
    (ExpP "Inn_1" (VarT "addrtype"))
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP
      "i_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___1) Arg Arg Arg)
        (TupE (VarE "Inn_1") (VarE "Fnn_2") (CaseE (Atom REINTERPRET) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__0) Arg Arg) (TupE (VarE "Inn_1") (VarE "i_1")))
    )
    (ListE
      (CallE
        "reinterpret__"
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
        (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
        (ExpA
          (CaseE
            (Seq (Atom mk_num__0) Arg Arg)
            (TupE (VarE "Inn_1") (VarE "i_1"))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_1")))
        )
        (CallE
          "size"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2")))
        )
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP
      "f_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
    (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
    (ExpA
      (CaseE
        (Seq (Atom mk_cvtop___2) Arg Arg Arg)
        (TupE (VarE "Fnn_1") (VarE "Inn_2") (CaseE (Atom REINTERPRET) (TupE)))
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_num__1) Arg Arg) (TupE (VarE "Fnn_1") (VarE "f_1")))
    )
    (ListE
      (CallE
        "reinterpret__"
        (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
        (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
        (ExpA
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_1") (VarE "f_1"))
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "size"
          (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
        )
        (CallE
          "size"
          (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2")))
        )
      )
    )
  )
)
HintD
(DecD
  "lanes_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "lane_" (ExpA (CallE "lanetype" (ExpA (VarE "shape"))))) List)
)
HintD
(DecD
  "inv_lanes_"
  (ExpP "shape" (VarT "shape"))
  (ExpP
    "_"
    (IterT (VarT "lane_" (ExpA (CallE "lanetype" (ExpA (VarE "shape"))))) List)
  )
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
)
HintD
HintD
HintD
(DecD
  "zeroop"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (ExpP
    "vcvtop__"
    (VarT "vcvtop__" (ExpA (VarE "shape_1")) (ExpA (VarE "shape_2")))
  )
  (IterT (VarT "zero") Opt)
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "half" (VarT "half"))
    (ExpP "sx" (VarT "sx"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom EXTEND) Arg Arg) (TupE (VarE "half") (VarE "sx")))
        )
      )
    )
    (OptE)
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP "half?" (IterT (VarT "half") Opt))
    (ExpP "sx" (VarT "sx"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___1) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom CONVERT) Arg Arg)
            (TupE
              (IterE (VarE "half") Opt (iterexp "half" (VarE "half?")))
              (VarE "sx")
            )
          )
        )
      )
    )
    (OptE)
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "zero?" (IterT (VarT "zero") Opt))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom TRUNC_SAT) Arg Arg)
            (TupE
              (VarE "sx")
              (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
            )
          )
        )
      )
    )
    (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "zero?" (IterT (VarT "zero") Opt))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom RELAXED_TRUNC) Arg Arg)
            (TupE
              (VarE "sx")
              (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
            )
          )
        )
      )
    )
    (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP "zero" (VarT "zero"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom DEMOTE) Arg) (TupE (VarE "zero")))
        )
      )
    )
    (OptE (VarE "zero"))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom PROMOTE) (Atom LOW)) (TupE))
        )
      )
    )
    (OptE)
  )
)
(DecD
  "halfop"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (ExpP
    "vcvtop__"
    (VarT "vcvtop__" (ExpA (VarE "shape_1")) (ExpA (VarE "shape_2")))
  )
  (IterT (VarT "half") Opt)
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "half" (VarT "half"))
    (ExpP "sx" (VarT "sx"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom EXTEND) Arg Arg) (TupE (VarE "half") (VarE "sx")))
        )
      )
    )
    (OptE (VarE "half"))
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP "half?" (IterT (VarT "half") Opt))
    (ExpP "sx" (VarT "sx"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___1) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom CONVERT) Arg Arg)
            (TupE
              (IterE (VarE "half") Opt (iterexp "half" (VarE "half?")))
              (VarE "sx")
            )
          )
        )
      )
    )
    (IterE (VarE "half") Opt (iterexp "half" (VarE "half?")))
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "zero?" (IterT (VarT "zero") Opt))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom TRUNC_SAT) Arg Arg)
            (TupE
              (VarE "sx")
              (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
            )
          )
        )
      )
    )
    (OptE)
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "zero?" (IterT (VarT "zero") Opt))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom RELAXED_TRUNC) Arg Arg)
            (TupE
              (VarE "sx")
              (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
            )
          )
        )
      )
    )
    (OptE)
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP "zero" (VarT "zero"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom DEMOTE) Arg) (TupE (VarE "zero")))
        )
      )
    )
    (OptE)
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom PROMOTE) (Atom LOW)) (TupE))
        )
      )
    )
    (OptE (CaseE (Atom LOW) (TupE)))
  )
)
(DecD
  "half"
  (ExpP "half" (VarT "half"))
  (ExpP "nat" nat)
  (ExpP "nat" nat)
  nat
  (DefD
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpA (CaseE (Atom LOW) (TupE)))
    (ExpA (VarE "i"))
    (ExpA (VarE "j"))
    (VarE "i")
  )
  (DefD
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpA (CaseE (Atom HIGH) (TupE)))
    (ExpA (VarE "i"))
    (ExpA (VarE "j"))
    (VarE "j")
  )
)
(DecD
  "iswizzle_lane_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "c*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "i" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
    (ExpA (VarE "i"))
    (IfE
      (CmpE
        LtOp
        nat
        (ProjE (UncaseE (VarE "i") Arg) 0)
        (LenE (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      (IdxE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        (ProjE (UncaseE (VarE "i") Arg) 0)
      )
      (CaseE Arg (TupE (NumE (Nat 0))))
    )
  )
)
(DecD
  "irelaxed_swizzle_lane_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
  (VarT "iN" (ExpA (VarE "N")))
  (DefD
    (ExpP "N" nat)
    (ExpP "c*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "i" (VarT "uN" (ExpA (VarE "N"))))
    (ExpA (VarE "N"))
    (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
    (ExpA (VarE "i"))
    (IfE
      (CmpE
        LtOp
        nat
        (ProjE (UncaseE (VarE "i") Arg) 0)
        (LenE (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      (IdxE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        (ProjE (UncaseE (VarE "i") Arg) 0)
      )
      (IfE
        (CmpE
          LtOp
          int
          (CallE
            "signed_"
            (ExpA (VarE "N"))
            (ExpA (ProjE (UncaseE (VarE "i") Arg) 0))
          )
          (CvtE nat int (NumE (Nat 0)))
        )
        (CaseE Arg (TupE (NumE (Nat 0))))
        (CallE
          "relaxed2"
          (ExpA (CallE "R_swizzle"))
          (TypA (VarT "iN" (ExpA (VarE "N"))))
          (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
          (ExpA
            (IdxE
              (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
              (BinE
                ModOp
                nat
                (ProjE (UncaseE (VarE "i") Arg) 0)
                (LenE (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "ivunop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (VarT "iN" (ExpA (VarE "N")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (VarT "iN" (ExpA (VarE "N")))
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ListE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_lane__2) Arg Arg)
              (TupE (VarE "Jnn") (VarE "c"))
            )
            List
            (iterexp "c" (VarE "c*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "f_"
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_1")))
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
      )
    )
  )
)
HintD
(DecD
  "fvunop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (IterT (VarT "fN" (ExpA (VarE "N"))) List)
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (IterT (VarT "fN" (ExpA (VarE "N"))) List)
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (IterE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      List
      (iterexp "c*" (VarE "c**"))
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA
          (VarT
            "lane_"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn")))
          )
        )
        (ExpA
          (IterE
            (IterE
              (CaseE
                (Seq (Atom mk_lane__0) Arg Arg)
                (TupE
                  (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
                  (CaseE
                    (Seq (Atom mk_num__1) Arg Arg)
                    (TupE (VarE "Fnn") (VarE "iter_0"))
                  )
                )
              )
              List
              (iterexp
                "iter_0"
                (CallE
                  "f_"
                  (ExpA
                    (CallE
                      "sizenn"
                      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_num__1"
                        (ExpA (VarE "Fnn"))
                        (ExpA
                          (TheE
                            (CallE
                              "proj_lane__0"
                              (ExpA
                                (SubE
                                  (VarT "Fnn")
                                  (VarT "numtype")
                                  (VarE "Fnn")
                                )
                              )
                              (ExpA (VarE "c_1"))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
          )
        )
      )
    )
  )
)
(DecD
  "ivbinop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (VarT "iN" (ExpA (VarE "N")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (VarT "iN" (ExpA (VarE "N")))
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ListE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_lane__2) Arg Arg)
              (TupE (VarE "Jnn") (VarE "c"))
            )
            List
            (iterexp "c" (VarE "c*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "f_"
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_1")))
            )
          )
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_2")))
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
  )
)
HintD
(DecD
  "ivbinopsx_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (VarT "iN" (ExpA (VarE "N")))
  )
  (ExpP "sx" (VarT "sx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (VarT "iN" (ExpA (VarE "N")))
    )
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "sx"))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ListE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA
          (IterE
            (CaseE
              (Seq (Atom mk_lane__2) Arg Arg)
              (TupE (VarE "Jnn") (VarE "c"))
            )
            List
            (iterexp "c" (VarE "c*"))
          )
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "f_"
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_1")))
            )
          )
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_2")))
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
  )
)
HintD
(DecD
  "ivbinopsxnd_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  )
  (ExpP "sx" (VarT "sx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (IterT (VarT "iN" (ExpA (VarE "N"))) List)
    )
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "sx"))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (IterE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      List
      (iterexp "c*" (VarE "c**"))
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA
          (VarT
            "lane_"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
          )
        )
        (ExpA
          (IterE
            (IterE
              (CaseE
                (Seq (Atom mk_lane__2) Arg Arg)
                (TupE (VarE "Jnn") (VarE "iter_0"))
              )
              List
              (iterexp
                "iter_0"
                (CallE
                  "f_"
                  (ExpA
                    (CallE
                      "lsizenn"
                      (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
                    )
                  )
                  (ExpA (VarE "sx"))
                  (ExpA
                    (TheE
                      (CallE
                        "proj_lane__2"
                        (ExpA (VarE "Jnn"))
                        (ExpA (VarE "c_1"))
                      )
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_lane__2"
                        (ExpA (VarE "Jnn"))
                        (ExpA (VarE "c_2"))
                      )
                    )
                  )
                )
              )
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
            (iterexp "c_2" (VarE "c_2*"))
          )
        )
      )
    )
  )
)
(DecD
  "fvbinop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (IterT (VarT "fN" (ExpA (VarE "N"))) List)
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (IterT (VarT "fN" (ExpA (VarE "N"))) List)
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (IterE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      List
      (iterexp "c*" (VarE "c**"))
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA
          (VarT
            "lane_"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn")))
          )
        )
        (ExpA
          (IterE
            (IterE
              (CaseE
                (Seq (Atom mk_lane__0) Arg Arg)
                (TupE
                  (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
                  (CaseE
                    (Seq (Atom mk_num__1) Arg Arg)
                    (TupE (VarE "Fnn") (VarE "iter_0"))
                  )
                )
              )
              List
              (iterexp
                "iter_0"
                (CallE
                  "f_"
                  (ExpA
                    (CallE
                      "sizenn"
                      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_num__1"
                        (ExpA (VarE "Fnn"))
                        (ExpA
                          (TheE
                            (CallE
                              "proj_lane__0"
                              (ExpA
                                (SubE
                                  (VarT "Fnn")
                                  (VarT "numtype")
                                  (VarE "Fnn")
                                )
                              )
                              (ExpA (VarE "c_1"))
                            )
                          )
                        )
                      )
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_num__1"
                        (ExpA (VarE "Fnn"))
                        (ExpA
                          (TheE
                            (CallE
                              "proj_lane__0"
                              (ExpA
                                (SubE
                                  (VarT "Fnn")
                                  (VarT "numtype")
                                  (VarE "Fnn")
                                )
                              )
                              (ExpA (VarE "c_2"))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
            (iterexp "c_2" (VarE "c_2*"))
          )
        )
      )
    )
  )
)
(DecD
  "ivternopnd_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (IterT (VarT "iN" (ExpA (VarE "N"))) List)
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_3" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ExpA (VarE "v_3"))
    (IterE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      List
      (iterexp "c*" (VarE "c**"))
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c_3") List (iterexp "c_3" (VarE "c_3*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_3"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA
          (VarT
            "lane_"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
          )
        )
        (ExpA
          (IterE
            (IterE
              (CaseE
                (Seq (Atom mk_lane__2) Arg Arg)
                (TupE (VarE "Jnn") (VarE "iter_0"))
              )
              List
              (iterexp
                "iter_0"
                (CallE
                  "f_"
                  (ExpA
                    (CallE
                      "lsizenn"
                      (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_lane__2"
                        (ExpA (VarE "Jnn"))
                        (ExpA (VarE "c_1"))
                      )
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_lane__2"
                        (ExpA (VarE "Jnn"))
                        (ExpA (VarE "c_2"))
                      )
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_lane__2"
                        (ExpA (VarE "Jnn"))
                        (ExpA (VarE "c_3"))
                      )
                    )
                  )
                )
              )
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
            (iterexp "c_2" (VarE "c_2*"))
            (iterexp "c_3" (VarE "c_3*"))
          )
        )
      )
    )
  )
)
(DecD
  "fvternop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (IterT (VarT "fN" (ExpA (VarE "N"))) List)
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (IterT (VarT "fN" (ExpA (VarE "N"))) List)
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_3" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ExpA (VarE "v_3"))
    (IterE
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
      )
      List
      (iterexp "c*" (VarE "c**"))
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c_3") List (iterexp "c_3" (VarE "c_3*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_3"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA
          (VarT
            "lane_"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn")))
          )
        )
        (ExpA
          (IterE
            (IterE
              (CaseE
                (Seq (Atom mk_lane__0) Arg Arg)
                (TupE
                  (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
                  (CaseE
                    (Seq (Atom mk_num__1) Arg Arg)
                    (TupE (VarE "Fnn") (VarE "iter_0"))
                  )
                )
              )
              List
              (iterexp
                "iter_0"
                (CallE
                  "f_"
                  (ExpA
                    (CallE
                      "sizenn"
                      (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_num__1"
                        (ExpA (VarE "Fnn"))
                        (ExpA
                          (TheE
                            (CallE
                              "proj_lane__0"
                              (ExpA
                                (SubE
                                  (VarT "Fnn")
                                  (VarT "numtype")
                                  (VarE "Fnn")
                                )
                              )
                              (ExpA (VarE "c_1"))
                            )
                          )
                        )
                      )
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_num__1"
                        (ExpA (VarE "Fnn"))
                        (ExpA
                          (TheE
                            (CallE
                              "proj_lane__0"
                              (ExpA
                                (SubE
                                  (VarT "Fnn")
                                  (VarT "numtype")
                                  (VarE "Fnn")
                                )
                              )
                              (ExpA (VarE "c_2"))
                            )
                          )
                        )
                      )
                    )
                  )
                  (ExpA
                    (TheE
                      (CallE
                        "proj_num__1"
                        (ExpA (VarE "Fnn"))
                        (ExpA
                          (TheE
                            (CallE
                              "proj_lane__0"
                              (ExpA
                                (SubE
                                  (VarT "Fnn")
                                  (VarT "numtype")
                                  (VarE "Fnn")
                                )
                              )
                              (ExpA (VarE "c_3"))
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
            (iterexp "c_2" (VarE "c_2*"))
            (iterexp "c_3" (VarE "c_3*"))
          )
        )
      )
    )
  )
)
(DecD
  "ivrelop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (VarT "u32")
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (VarT "u32")
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn") (VarE "c")))
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "extend__"
          (ExpA (NumE (Nat 1)))
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA (CaseE (Atom S) (TupE)))
          (ExpA
            (CaseE
              Arg
              (TupE
                (ProjE
                  (UncaseE
                    (CallE
                      "f_"
                      (ExpA
                        (CallE
                          "lsizenn"
                          (ExpA
                            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                          )
                        )
                      )
                      (ExpA
                        (TheE
                          (CallE
                            "proj_lane__2"
                            (ExpA (VarE "Jnn"))
                            (ExpA (VarE "c_1"))
                          )
                        )
                      )
                      (ExpA
                        (TheE
                          (CallE
                            "proj_lane__2"
                            (ExpA (VarE "Jnn"))
                            (ExpA (VarE "c_2"))
                          )
                        )
                      )
                    )
                    Arg
                  )
                  0
                )
              )
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
  )
)
(DecD
  "ivrelopsx_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (VarT "u32")
  )
  (ExpP "sx" (VarT "sx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (VarT "u32")
    )
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "sx"))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn") (VarE "c")))
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "extend__"
          (ExpA (NumE (Nat 1)))
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA (CaseE (Atom S) (TupE)))
          (ExpA
            (CaseE
              Arg
              (TupE
                (ProjE
                  (UncaseE
                    (CallE
                      "f_"
                      (ExpA
                        (CallE
                          "lsizenn"
                          (ExpA
                            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                          )
                        )
                      )
                      (ExpA (VarE "sx"))
                      (ExpA
                        (TheE
                          (CallE
                            "proj_lane__2"
                            (ExpA (VarE "Jnn"))
                            (ExpA (VarE "c_1"))
                          )
                        )
                      )
                      (ExpA
                        (TheE
                          (CallE
                            "proj_lane__2"
                            (ExpA (VarE "Jnn"))
                            (ExpA (VarE "c_2"))
                          )
                        )
                      )
                    )
                    Arg
                  )
                  0
                )
              )
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
  )
)
(DecD
  "fvrelop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
    (VarT "u32")
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (ExpP "fN" (VarT "fN" (ExpA (VarE "N"))))
      (VarT "u32")
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "Inn" (VarT "addrtype"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "addrtype") (VarT "lanetype") (VarE "Inn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE
            (Seq (Atom mk_lane__0) Arg Arg)
            (TupE
              (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn"))
              (CaseE
                (Seq (Atom mk_num__0) Arg Arg)
                (TupE
                  (VarE "Inn")
                  (CaseE Arg (TupE (ProjE (UncaseE (VarE "c") Arg) 0)))
                )
              )
            )
          )
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "extend__"
          (ExpA (NumE (Nat 1)))
          (ExpA
            (CallE
              "sizenn"
              (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn")))
            )
          )
          (ExpA (CaseE (Atom S) (TupE)))
          (ExpA
            (CaseE
              Arg
              (TupE
                (ProjE
                  (UncaseE
                    (CallE
                      "f_"
                      (ExpA
                        (CallE
                          "sizenn"
                          (ExpA
                            (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn"))
                          )
                        )
                      )
                      (ExpA
                        (TheE
                          (CallE
                            "proj_num__1"
                            (ExpA (VarE "Fnn"))
                            (ExpA
                              (TheE
                                (CallE
                                  "proj_lane__0"
                                  (ExpA
                                    (SubE
                                      (VarT "Fnn")
                                      (VarT "numtype")
                                      (VarE "Fnn")
                                    )
                                  )
                                  (ExpA (VarE "c_1"))
                                )
                              )
                            )
                          )
                        )
                      )
                      (ExpA
                        (TheE
                          (CallE
                            "proj_num__1"
                            (ExpA (VarE "Fnn"))
                            (ExpA
                              (TheE
                                (CallE
                                  "proj_lane__0"
                                  (ExpA
                                    (SubE
                                      (VarT "Fnn")
                                      (VarT "numtype")
                                      (VarE "Fnn")
                                    )
                                  )
                                  (ExpA (VarE "c_2"))
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                    Arg
                  )
                  0
                )
              )
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "isize" (ExpA (VarE "Inn")))
        (CallE "fsize" (ExpA (VarE "Fnn")))
      )
    )
  )
)
(DecD
  "ivshiftop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "u32" (VarT "u32"))
    (VarT "iN" (ExpA (VarE "N")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "u32" (VarT "u32"))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "u32" (VarT "u32"))
      (VarT "iN" (ExpA (VarE "N")))
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "i" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "i"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn") (VarE "c")))
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "f_"
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_1")))
            )
          )
          (ExpA (VarE "i"))
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
      )
    )
  )
)
HintD
(DecD
  "ivshiftopsx_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (ExpP "u32" (VarT "u32"))
    (VarT "iN" (ExpA (VarE "N")))
  )
  (ExpP "sx" (VarT "sx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "u32" (VarT "u32"))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "sx" (VarT "sx"))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (ExpP "u32" (VarT "u32"))
      (VarT "iN" (ExpA (VarE "N")))
    )
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "i" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "sx"))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "i"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn") (VarE "c")))
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "f_"
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_1")))
            )
          )
          (ExpA (VarE "i"))
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
      )
    )
  )
)
HintD
(DecD
  "ivbitmaskop_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "u32")
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "c" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (CallE "irev_" (ExpA (NumE (Nat 32))) (ExpA (VarE "c")))
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "ibits_" (ExpA (NumE (Nat 32))) (ExpA (VarE "c")))
        (CatE
          (IterE
            (CaseE
              Arg
              (TupE
                (ProjE
                  (UncaseE
                    (CallE
                      "ilt_"
                      (ExpA
                        (CallE
                          "lsizenn"
                          (ExpA
                            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                          )
                        )
                      )
                      (ExpA (CaseE (Atom S) (TupE)))
                      (ExpA
                        (TheE
                          (CallE
                            "proj_lane__2"
                            (ExpA (VarE "Jnn"))
                            (ExpA (VarE "c_1"))
                          )
                        )
                      )
                      (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
                    )
                    Arg
                  )
                  0
                )
              )
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
          )
          (IterE
            (CaseE Arg (TupE (NumE (Nat 0))))
            (ListN
              (CvtE
                int
                nat
                (BinE
                  SubOp
                  int
                  (CvtE nat int (NumE (Nat 32)))
                  (CvtE nat int (VarE "M"))
                )
              )
            )
          )
        )
      )
    )
  )
)
(DecD
  "ivswizzlop_"
  (ExpP "shape" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
    (VarT "iN" (ExpA (VarE "N")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
      (ExpP "iN" (VarT "iN" (ExpA (VarE "N"))))
      (VarT "iN" (ExpA (VarE "N")))
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn") (VarE "c")))
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (CallE
          "f_"
          (ExpA
            (CallE
              "lsizenn"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn")))
            )
          )
          (ExpA
            (IterE
              (TheE
                (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_1")))
              )
              List
              (iterexp "c_1" (VarE "c_1*"))
            )
          )
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn")) (ExpA (VarE "c_2")))
            )
          )
        )
        List
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
  )
)
HintD
(DecD
  "ivshufflop_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "_" (IterT (VarT "laneidx") List))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "i*" (IterT (VarT "laneidx") List))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA (IterE (VarE "i") List (iterexp "i" (VarE "i*"))))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (IterE
        (IdxE
          (CatE
            (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
            (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
          )
          (ProjE (UncaseE (VarE "i") Arg) 0)
        )
        List
        (iterexp "i" (VarE "i*"))
      )
    )
  )
)
HintD
(DecD
  "vvunop_"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vvunop" (VarT "vvunop"))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (IterT (VarT "vec_" (ExpA (VarE "vectype"))) List)
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpP "v" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpA (VarE "Vnn"))
    (ExpA (CaseE (Atom NOT) (TupE)))
    (ExpA (VarE "v"))
    (ListE
      (CallE
        "inot_"
        (ExpA (CallE "vsizenn" (ExpA (VarE "Vnn"))))
        (ExpA (VarE "v"))
      )
    )
  )
)
HintD
(DecD
  "vvbinop_"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vvbinop" (VarT "vvbinop"))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (IterT (VarT "vec_" (ExpA (VarE "vectype"))) List)
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpP "v_1" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpP "v_2" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpA (VarE "Vnn"))
    (ExpA (CaseE (Atom AND) (TupE)))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ListE
      (CallE
        "iand_"
        (ExpA (CallE "vsizenn" (ExpA (VarE "Vnn"))))
        (ExpA (VarE "v_1"))
        (ExpA (VarE "v_2"))
      )
    )
  )
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpP "v_1" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpP "v_2" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpA (VarE "Vnn"))
    (ExpA (CaseE (Atom ANDNOT) (TupE)))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ListE
      (CallE
        "iandnot_"
        (ExpA (CallE "vsizenn" (ExpA (VarE "Vnn"))))
        (ExpA (VarE "v_1"))
        (ExpA (VarE "v_2"))
      )
    )
  )
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpP "v_1" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpP "v_2" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpA (VarE "Vnn"))
    (ExpA (CaseE (Atom OR) (TupE)))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ListE
      (CallE
        "ior_"
        (ExpA (CallE "vsizenn" (ExpA (VarE "Vnn"))))
        (ExpA (VarE "v_1"))
        (ExpA (VarE "v_2"))
      )
    )
  )
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpP "v_1" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpP "v_2" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpA (VarE "Vnn"))
    (ExpA (CaseE (Atom XOR) (TupE)))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ListE
      (CallE
        "ixor_"
        (ExpA (CallE "vsizenn" (ExpA (VarE "Vnn"))))
        (ExpA (VarE "v_1"))
        (ExpA (VarE "v_2"))
      )
    )
  )
)
HintD
(DecD
  "vvternop_"
  (ExpP "vectype" (VarT "vectype"))
  (ExpP "vvternop" (VarT "vvternop"))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (VarE "vectype"))))
  (IterT (VarT "vec_" (ExpA (VarE "vectype"))) List)
  (DefD
    (ExpP "Vnn" (VarT "vectype"))
    (ExpP "v_1" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpP "v_2" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpP "v_3" (VarT "uN" (ExpA (CallE "vsize" (ExpA (VarE "Vnn"))))))
    (ExpA (VarE "Vnn"))
    (ExpA (CaseE (Atom BITSELECT) (TupE)))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ExpA (VarE "v_3"))
    (ListE
      (CallE
        "ibitselect_"
        (ExpA (CallE "vsizenn" (ExpA (VarE "Vnn"))))
        (ExpA (VarE "v_1"))
        (ExpA (VarE "v_2"))
        (ExpA (VarE "v_3"))
      )
    )
  )
)
HintD
(DecD
  "vunop_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "vunop_" (VarT "vunop_" (ExpA (VarE "shape"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom ABS) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fabs_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom NEG) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fneg_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom SQRT) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fsqrt_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom CEIL) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fceil_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom FLOOR) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ffloor_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom TRUNC) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ftrunc_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom NEAREST) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "fvunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fnearest_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom ABS) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "ivunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "iabs_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom NEG) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "ivunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ineg_")
      (ExpA (VarE "v"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vunop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom POPCNT) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "ivunop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ipopcnt_")
      (ExpA (VarE "v"))
    )
  )
)
HintD
(DecD
  "vbinop_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "vbinop_" (VarT "vbinop_" (ExpA (VarE "shape"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "iadd_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "isub_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "imul_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom ADD_SAT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "iadd_sat_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom SUB_SAT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "isub_sat_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom MIN) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "imin_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom MAX) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "imax_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Seq (Atom AVGR) (Atom U)) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "iavgr_")
      (ExpA (CaseE (Atom U) (TupE)))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom Q15MULR_SAT) (Atom S)) (TupE))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "iq15mulr_sat_")
      (ExpA (CaseE (Atom S) (TupE)))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom RELAXED_Q15MULR) (Atom S)) (TupE))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivbinopsxnd_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "irelaxed_q15mulr_")
      (ExpA (CaseE (Atom S) (TupE)))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom ADD) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fadd_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom SUB) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fsub_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom MUL) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fmul_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom DIV) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fdiv_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom MIN) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fmin_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom MAX) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fmax_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom PMIN) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fpmin_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom PMAX) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fpmax_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom RELAXED_MIN) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "frelaxed_min_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vbinop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom RELAXED_MAX) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvbinop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "frelaxed_max_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
)
HintD
(DecD
  "vternop_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "vternop_" (VarT "vternop_" (ExpA (VarE "shape"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (IterT (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))) List)
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_3" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vternop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom RELAXED_LANESELECT) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ExpA (VarE "v_3"))
    (CallE
      "ivternopnd_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "irelaxed_laneselect_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
      (ExpA (VarE "v_3"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_3" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vternop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom RELAXED_MADD) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ExpA (VarE "v_3"))
    (CallE
      "fvternop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "frelaxed_madd_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
      (ExpA (VarE "v_3"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_3" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vternop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom RELAXED_NMADD) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (ExpA (VarE "v_3"))
    (CallE
      "fvternop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "frelaxed_nmadd_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
      (ExpA (VarE "v_3"))
    )
  )
)
HintD
(DecD
  "vrelop_"
  (ExpP "shape" (VarT "shape"))
  (ExpP "vrelop_" (VarT "vrelop_" (ExpA (VarE "shape"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ieq_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ine_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom LT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivrelopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ilt_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom GT) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivrelopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "igt_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom LE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivrelopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ile_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom GE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivrelopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ige_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom EQ) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "feq_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom NE) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fne_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom LT) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "flt_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom GT) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fgt_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom LE) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fle_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
          (CaseE Arg (TupE (VarE "M")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vrelop__1) Arg Arg Arg)
        (TupE (VarE "Fnn") (VarE "M") (CaseE (Atom GE) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "fvrelop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "fge_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
)
HintD
(DecD
  "lcvtop__"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (ExpP
    "vcvtop__"
    (VarT "vcvtop__" (ExpA (VarE "shape_1")) (ExpA (VarE "shape_2")))
  )
  (ExpP
    "lane_"
    (VarT "lane_" (ExpA (CallE "lanetype" (ExpA (VarE "shape_1")))))
  )
  (IterT (VarT "lane_" (ExpA (CallE "lanetype" (ExpA (VarE "shape_2"))))) List)
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "half" (VarT "half"))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "c_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "lsize"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom EXTEND) Arg Arg) (TupE (VarE "half") (VarE "sx")))
        )
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn_1") (VarE "c_1")))
    )
    (ListE
      (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn_2") (VarE "c")))
    )
    (LetPr
      (VarE "c")
      (CallE
        "extend__"
        (ExpA
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
          )
        )
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
          )
        )
        (ExpA (VarE "sx"))
        (ExpA (VarE "c_1"))
      )
    )
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP "half?" (IterT (VarT "half") Opt))
    (ExpP "sx" (VarT "sx"))
    (ExpP
      "c_1"
      (VarT
        "uN"
        (ExpA
          (CallE
            "lsize"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___1) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE
            (Seq (Atom CONVERT) Arg Arg)
            (TupE
              (IterE (VarE "half") Opt (iterexp "half" (VarE "half?")))
              (VarE "sx")
            )
          )
        )
      )
    )
    (ExpA
      (CaseE (Seq (Atom mk_lane__2) Arg Arg) (TupE (VarE "Jnn_1") (VarE "c_1")))
    )
    (ListE
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_2") (VarE "c"))
          )
        )
      )
    )
    (LetPr
      (VarE "c")
      (CallE
        "convert__"
        (ExpA
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
          )
        )
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2")))
          )
        )
        (ExpA (VarE "sx"))
        (ExpA (VarE "c_1"))
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "zero?" (IterT (VarT "zero") Opt))
    (ExpP
      "c_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "addrtype") (VarT "lanetype") (VarE "Inn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (SubE (VarT "addrtype") (VarT "Jnn") (VarE "Inn_2"))
          (VarE "M_2")
          (CaseE
            (Seq (Atom TRUNC_SAT) Arg Arg)
            (TupE
              (VarE "sx")
              (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_1") (VarE "c_1"))
          )
        )
      )
    )
    (LiftE
      (IterE
        (CaseE
          (Seq (Atom mk_lane__0) Arg Arg)
          (TupE
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2"))
            (CaseE
              (Seq (Atom mk_num__0) Arg Arg)
              (TupE (VarE "Inn_2") (VarE "c"))
            )
          )
        )
        Opt
        (iterexp "c" (VarE "c?"))
      )
    )
    (LetPr
      (IterE (VarE "c") Opt (iterexp "c" (VarE "c?")))
      (CallE
        "trunc_sat__"
        (ExpA
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1")))
          )
        )
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "addrtype") (VarT "lanetype") (VarE "Inn_2")))
          )
        )
        (ExpA (VarE "sx"))
        (ExpA (VarE "c_1"))
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Inn_2" (VarT "addrtype"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "zero?" (IterT (VarT "zero") Opt))
    (ExpP
      "c_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "addrtype") (VarT "lanetype") (VarE "Inn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___2) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (SubE (VarT "addrtype") (VarT "Jnn") (VarE "Inn_2"))
          (VarE "M_2")
          (CaseE
            (Seq (Atom RELAXED_TRUNC) Arg Arg)
            (TupE
              (VarE "sx")
              (IterE (VarE "zero") Opt (iterexp "zero" (VarE "zero?")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_1") (VarE "c_1"))
          )
        )
      )
    )
    (LiftE
      (IterE
        (CaseE
          (Seq (Atom mk_lane__0) Arg Arg)
          (TupE
            (SubE (VarT "addrtype") (VarT "numtype") (VarE "Inn_2"))
            (CaseE
              (Seq (Atom mk_num__0) Arg Arg)
              (TupE (VarE "Inn_2") (VarE "c"))
            )
          )
        )
        Opt
        (iterexp "c" (VarE "c?"))
      )
    )
    (LetPr
      (IterE (VarE "c") Opt (iterexp "c" (VarE "c?")))
      (CallE
        "relaxed_trunc__"
        (ExpA
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1")))
          )
        )
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "addrtype") (VarT "lanetype") (VarE "Inn_2")))
          )
        )
        (ExpA (VarE "sx"))
        (ExpA (VarE "c_1"))
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP
      "c_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom DEMOTE) Arg) (TupE (CaseE (Atom ZERO) (TupE))))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_1") (VarE "c_1"))
          )
        )
      )
    )
    (IterE
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_2") (VarE "c"))
          )
        )
      )
      List
      (iterexp "c" (VarE "c*"))
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (CallE
        "demote__"
        (ExpA
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1")))
          )
        )
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2")))
          )
        )
        (ExpA (VarE "c_1"))
      )
    )
  )
  (DefD
    (ExpP "Fnn_1" (VarT "Fnn"))
    (ExpP "M_1" nat)
    (ExpP "Fnn_2" (VarT "Fnn"))
    (ExpP "M_2" nat)
    (ExpP
      "c_1"
      (VarT
        "fN"
        (ExpA
          (CallE
            "size"
            (ExpA (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1")))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vcvtop___3) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Fnn_1")
          (VarE "M_1")
          (VarE "Fnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom PROMOTE) (Atom LOW)) (TupE))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_1"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_1") (VarE "c_1"))
          )
        )
      )
    )
    (IterE
      (CaseE
        (Seq (Atom mk_lane__0) Arg Arg)
        (TupE
          (SubE (VarT "Fnn") (VarT "numtype") (VarE "Fnn_2"))
          (CaseE
            (Seq (Atom mk_num__1) Arg Arg)
            (TupE (VarE "Fnn_2") (VarE "c"))
          )
        )
      )
      List
      (iterexp "c" (VarE "c*"))
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (CallE
        "promote__"
        (ExpA
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_1")))
          )
        )
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "Fnn") (VarT "lanetype") (VarE "Fnn_2")))
          )
        )
        (ExpA (VarE "c_1"))
      )
    )
  )
)
HintD
(DecD
  "vcvtop__"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (ExpP
    "vcvtop__"
    (VarT "vcvtop__" (ExpA (VarE "shape_1")) (ExpA (VarE "shape_2")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Lnn_1" (VarT "lanetype"))
    (ExpP "M" nat)
    (ExpP "Lnn_2" (VarT "lanetype"))
    (ExpP
      "vcvtop"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M"))))
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M"))))
          )
        )
      )
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M"))))
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M"))))
      )
    )
    (ExpA (VarE "vcvtop"))
    (ExpA (VarE "v_1"))
    (VarE "v")
    (IfPr
      (BinE
        AndOp
        bool
        (CmpE
          EqOp
          bool
          (CallE
            "halfop"
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M"))))
              )
            )
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M"))))
              )
            )
            (ExpA (VarE "vcvtop"))
          )
          (OptE)
        )
        (CmpE
          EqOp
          bool
          (CallE
            "zeroop"
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M"))))
              )
            )
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M"))))
              )
            )
            (ExpA (VarE "vcvtop"))
          )
          (OptE)
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M"))))
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA (VarT "lane_" (ExpA (VarE "Lnn_2"))))
        (ExpA
          (IterE
            (CallE
              "lcvtop__"
              (ExpA
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M"))))
                )
              )
              (ExpA
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M"))))
                )
              )
              (ExpA (VarE "vcvtop"))
              (ExpA (VarE "c_1"))
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
          )
        )
      )
    )
    (IfPr
      (MemE
        (VarE "v")
        (IterE
          (CallE
            "inv_lanes_"
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M"))))
              )
            )
            (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
          )
          List
          (iterexp "c*" (VarE "c**"))
        )
      )
    )
  )
  (DefD
    (ExpP "Lnn_1" (VarT "lanetype"))
    (ExpP "M_1" nat)
    (ExpP "Lnn_2" (VarT "lanetype"))
    (ExpP "M_2" nat)
    (ExpP
      "vcvtop"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
          )
        )
      )
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "half" (VarT "half"))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
      )
    )
    (ExpA (VarE "vcvtop"))
    (ExpA (VarE "v_1"))
    (VarE "v")
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "halfop"
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
            )
          )
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
            )
          )
          (ExpA (VarE "vcvtop"))
        )
        (OptE (VarE "half"))
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (SliceE
        (CallE
          "lanes_"
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
            )
          )
          (ExpA (VarE "v_1"))
        )
        (CallE
          "half"
          (ExpA (VarE "half"))
          (ExpA (NumE (Nat 0)))
          (ExpA (VarE "M_2"))
        )
        (VarE "M_2")
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA (VarT "lane_" (ExpA (VarE "Lnn_2"))))
        (ExpA
          (IterE
            (CallE
              "lcvtop__"
              (ExpA
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
                )
              )
              (ExpA
                (CaseE
                  (Seq Arg (Atom X) Arg)
                  (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
                )
              )
              (ExpA (VarE "vcvtop"))
              (ExpA (VarE "c_1"))
            )
            List
            (iterexp "c_1" (VarE "c_1*"))
          )
        )
      )
    )
    (IfPr
      (MemE
        (VarE "v")
        (IterE
          (CallE
            "inv_lanes_"
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
              )
            )
            (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
          )
          List
          (iterexp "c*" (VarE "c**"))
        )
      )
    )
  )
  (DefD
    (ExpP "Lnn_1" (VarT "lanetype"))
    (ExpP "M_1" nat)
    (ExpP "Lnn_2" (VarT "lanetype"))
    (ExpP "M_2" nat)
    (ExpP
      "vcvtop"
      (VarT
        "vcvtop__"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
          )
        )
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
          )
        )
      )
    )
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
      )
    )
    (ExpA (VarE "vcvtop"))
    (ExpA (VarE "v_1"))
    (VarE "v")
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "zeroop"
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
            )
          )
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
            )
          )
          (ExpA (VarE "vcvtop"))
        )
        (OptE (CaseE (Atom ZERO) (TupE)))
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE
        (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
        List
        (iterexp "c*" (VarE "c**"))
      )
      (CallE
        "setproduct_"
        (TypA (VarT "lane_" (ExpA (VarE "Lnn_2"))))
        (ExpA
          (CatE
            (IterE
              (CallE
                "lcvtop__"
                (ExpA
                  (CaseE
                    (Seq Arg (Atom X) Arg)
                    (TupE (VarE "Lnn_1") (CaseE Arg (TupE (VarE "M_1"))))
                  )
                )
                (ExpA
                  (CaseE
                    (Seq Arg (Atom X) Arg)
                    (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
                  )
                )
                (ExpA (VarE "vcvtop"))
                (ExpA (VarE "c_1"))
              )
              List
              (iterexp "c_1" (VarE "c_1*"))
            )
            (IterE
              (ListE (CallE "zero" (ExpA (VarE "Lnn_2"))))
              (ListN (VarE "M_1"))
            )
          )
        )
      )
    )
    (IfPr
      (MemE
        (VarE "v")
        (IterE
          (CallE
            "inv_lanes_"
            (ExpA
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE (VarE "Lnn_2") (CaseE Arg (TupE (VarE "M_2"))))
              )
            )
            (ExpA (IterE (VarE "c") List (iterexp "c" (VarE "c*"))))
          )
          List
          (iterexp "c*" (VarE "c**"))
        )
      )
    )
  )
)
HintD
(DecD
  "vshiftop_"
  (ExpP "ishape" (VarT "ishape"))
  (ExpP "vshiftop_" (VarT "vshiftop_" (ExpA (VarE "ishape"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "u32" (VarT "u32"))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "i" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vshiftop__0) Arg Arg Arg)
        (TupE (VarE "Jnn") (VarE "M") (CaseE (Atom SHL) (TupE)))
      )
    )
    (ExpA (VarE "v"))
    (ExpA (VarE "i"))
    (CallE
      "ivshiftop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ishl_")
      (ExpA (VarE "v"))
      (ExpA (VarE "i"))
    )
  )
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "i" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vshiftop__0) Arg Arg Arg)
        (TupE
          (VarE "Jnn")
          (VarE "M")
          (CaseE (Seq (Atom SHR) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v"))
    (ExpA (VarE "i"))
    (CallE
      "ivshiftopsx_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (DefA "ishr_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v"))
      (ExpA (VarE "i"))
    )
  )
)
HintD
(DecD
  "vbitmaskop_"
  (ExpP "ishape" (VarT "ishape"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "u32")
  (DefD
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpP "M" nat)
    (ExpP "v" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
              (CaseE Arg (TupE (VarE "M")))
            )
          )
        )
      )
    )
    (ExpA (VarE "v"))
    (CallE
      "ivbitmaskop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
            (CaseE Arg (TupE (VarE "M")))
          )
        )
      )
      (ExpA (VarE "v"))
    )
  )
)
HintD
(DecD
  "vswizzlop_"
  (ExpP "bshape" (VarT "bshape"))
  (ExpP "vswizzlop_" (VarT "vswizzlop_" (ExpA (VarE "bshape"))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vswizzlop__0) Arg Arg)
        (TupE (VarE "M") (CaseE (Atom SWIZZLE) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivswizzlop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
        )
      )
      (DefA "iswizzle_lane_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "M" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vswizzlop__0) Arg Arg)
        (TupE (VarE "M") (CaseE (Atom RELAXED_SWIZZLE) (TupE)))
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivswizzlop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
        )
      )
      (DefA "irelaxed_swizzle_lane_")
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
)
HintD
(DecD
  "vshufflop_"
  (ExpP "bshape" (VarT "bshape"))
  (ExpP "_" (IterT (VarT "laneidx") List))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "M" nat)
    (ExpP "i*" (IterT (VarT "laneidx") List))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
          )
        )
      )
    )
    (ExpA (IterE (VarE "i") List (iterexp "i" (VarE "i*"))))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivshufflop_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE (CaseE (Atom I8) (TupE)) (CaseE Arg (TupE (VarE "M"))))
        )
      )
      (ExpA (IterE (VarE "i") List (iterexp "i" (VarE "i*"))))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
)
HintD
(DecD
  "vnarrowop__"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (ExpA (VarE "sx"))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (VarE "v")
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA (VarE "v_2"))
      )
    )
    (LetPr
      (IterE (VarE "c'_1") List (iterexp "c'_1" (VarE "c'_1*")))
      (IterE
        (CallE
          "narrow__"
          (ExpA
            (CallE
              "lsize"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
            )
          )
          (ExpA
            (CallE
              "lsize"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn_1")) (ExpA (VarE "c_1")))
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
      )
    )
    (LetPr
      (IterE (VarE "c'_2") List (iterexp "c'_2" (VarE "c'_2*")))
      (IterE
        (CallE
          "narrow__"
          (ExpA
            (CallE
              "lsize"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
            )
          )
          (ExpA
            (CallE
              "lsize"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn_1")) (ExpA (VarE "c_2")))
            )
          )
        )
        List
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
    (LetPr
      (VarE "v")
      (CallE
        "inv_lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
        (ExpA
          (CatE
            (IterE
              (CaseE
                (Seq (Atom mk_lane__2) Arg Arg)
                (TupE (VarE "Jnn_2") (VarE "c'_1"))
              )
              List
              (iterexp "c'_1" (VarE "c'_1*"))
            )
            (IterE
              (CaseE
                (Seq (Atom mk_lane__2) Arg Arg)
                (TupE (VarE "Jnn_2") (VarE "c'_2"))
              )
              List
              (iterexp "c'_2" (VarE "c'_2*"))
            )
          )
        )
      )
    )
  )
)
HintD
(DecD
  "ivadd_pairwise_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  (DefD
    (ExpP "N" nat)
    (ExpP "i*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "j_1*" (IterT (VarT "N") List))
    (ExpP "j_2*" (IterT (VarT "N") List))
    (ExpA (VarE "N"))
    (ExpA (IterE (VarE "i") List (iterexp "i" (VarE "i*"))))
    (IterE
      (CallE
        "iadd_"
        (ExpA (VarE "N"))
        (ExpA (CaseE Arg (TupE (VarE "j_1"))))
        (ExpA (CaseE Arg (TupE (VarE "j_2"))))
      )
      List
      (iterexp "j_1" (VarE "j_1*"))
      (iterexp "j_2" (VarE "j_2*"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "concat_"
          (TypA (VarT "N"))
          (ExpA
            (IterE
              (ListE (VarE "j_1") (VarE "j_2"))
              List
              (iterexp "j_1" (VarE "j_1*"))
              (iterexp "j_2" (VarE "j_2*"))
            )
          )
        )
        (IterE
          (ProjE (UncaseE (VarE "i") Arg) 0)
          List
          (iterexp "i" (VarE "i*"))
        )
      )
    )
  )
)
(DecD
  "ivextunop__"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  )
  (ExpP "sx" (VarT "sx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
      (IterT (VarT "iN" (ExpA (VarE "N"))) List)
    )
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "sx"))
    (ExpA (VarE "v_1"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE
            (Seq (Atom mk_lane__2) Arg Arg)
            (TupE (VarE "Jnn_2") (VarE "c"))
          )
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (CallE
        "lanes_"
        (ExpA
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
        (ExpA (VarE "v_1"))
      )
    )
    (LetPr
      (IterE (VarE "c'_1") List (iterexp "c'_1" (VarE "c'_1*")))
      (IterE
        (CallE
          "extend__"
          (ExpA
            (CallE
              "lsizenn1"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
            )
          )
          (ExpA
            (CallE
              "lsizenn2"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
            )
          )
          (ExpA (VarE "sx"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn_1")) (ExpA (VarE "c_1")))
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (CallE
        "f_"
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
          )
        )
        (ExpA (IterE (VarE "c'_1") List (iterexp "c'_1" (VarE "c'_1*"))))
      )
    )
  )
)
(DecD
  "vextunop__"
  (ExpP "ishape_1" (VarT "ishape"))
  (ExpP "ishape_2" (VarT "ishape"))
  (ExpP
    "vextunop__"
    (VarT "vextunop__" (ExpA (VarE "ishape_1")) (ExpA (VarE "ishape_2")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vextunop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom EXTADD_PAIRWISE) Arg) (TupE (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (CallE
      "ivextunop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
      (DefA "ivadd_pairwise_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "v_1"))
    )
  )
)
HintD
(DecD
  "ivdot_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "i_2*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "j_1*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "j_2*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpA (VarE "N"))
    (ExpA (IterE (VarE "i_1") List (iterexp "i_1" (VarE "i_1*"))))
    (ExpA (IterE (VarE "i_2") List (iterexp "i_2" (VarE "i_2*"))))
    (IterE
      (CallE "iadd_" (ExpA (VarE "N")) (ExpA (VarE "j_1")) (ExpA (VarE "j_2")))
      List
      (iterexp "j_1" (VarE "j_1*"))
      (iterexp "j_2" (VarE "j_2*"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "concat_"
          (TypA (VarT "iN" (ExpA (VarE "N"))))
          (ExpA
            (IterE
              (ListE (VarE "j_1") (VarE "j_2"))
              List
              (iterexp "j_1" (VarE "j_1*"))
              (iterexp "j_2" (VarE "j_2*"))
            )
          )
        )
        (IterE
          (CallE
            "imul_"
            (ExpA (VarE "N"))
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
          List
          (iterexp "i_1" (VarE "i_1*"))
          (iterexp "i_2" (VarE "i_2*"))
        )
      )
    )
  )
)
(DecD
  "ivdot_sat_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "i_2*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "j_1*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "j_2*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpA (VarE "N"))
    (ExpA (IterE (VarE "i_1") List (iterexp "i_1" (VarE "i_1*"))))
    (ExpA (IterE (VarE "i_2") List (iterexp "i_2" (VarE "i_2*"))))
    (IterE
      (CallE
        "iadd_sat_"
        (ExpA (VarE "N"))
        (ExpA (CaseE (Atom S) (TupE)))
        (ExpA (VarE "j_1"))
        (ExpA (VarE "j_2"))
      )
      List
      (iterexp "j_1" (VarE "j_1*"))
      (iterexp "j_2" (VarE "j_2*"))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE
          "concat_"
          (TypA (VarT "iN" (ExpA (VarE "N"))))
          (ExpA
            (IterE
              (ListE (VarE "j_1") (VarE "j_2"))
              List
              (iterexp "j_1" (VarE "j_1*"))
              (iterexp "j_2" (VarE "j_2*"))
            )
          )
        )
        (IterE
          (CallE
            "imul_"
            (ExpA (VarE "N"))
            (ExpA (VarE "i_1"))
            (ExpA (VarE "i_2"))
          )
          List
          (iterexp "i_1" (VarE "i_1*"))
          (iterexp "i_2" (VarE "i_2*"))
        )
      )
    )
  )
)
(DecD
  "ivextbinop__"
  (ExpP "shape_1" (VarT "shape"))
  (ExpP "shape_2" (VarT "shape"))
  (DefP
    "f_"
    (ExpP "N" (VarT "N"))
    (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  )
  (ExpP "sx" (VarT "sx"))
  (ExpP "sx" (VarT "sx"))
  (ExpP "laneidx" (VarT "laneidx"))
  (ExpP "laneidx" (VarT "laneidx"))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (DefP
      "f_"
      (ExpP "N" (VarT "N"))
      (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
      (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
      (IterT (VarT "iN" (ExpA (VarE "N"))) List)
    )
    (ExpP "sx_1" (VarT "sx"))
    (ExpP "sx_2" (VarT "sx"))
    (ExpP "i" (VarT "uN" (ExpA (NumE (Nat 8)))))
    (ExpP "k" (VarT "uN" (ExpA (NumE (Nat 8)))))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
          (CaseE Arg (TupE (VarE "M_1")))
        )
      )
    )
    (ExpA
      (CaseE
        (Seq Arg (Atom X) Arg)
        (TupE
          (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
          (CaseE Arg (TupE (VarE "M_2")))
        )
      )
    )
    (DefA "f_")
    (ExpA (VarE "sx_1"))
    (ExpA (VarE "sx_2"))
    (ExpA (VarE "i"))
    (ExpA (VarE "k"))
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "inv_lanes_"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
      (ExpA
        (IterE
          (CaseE
            (Seq (Atom mk_lane__2) Arg Arg)
            (TupE (VarE "Jnn_2") (VarE "c"))
          )
          List
          (iterexp "c" (VarE "c*"))
        )
      )
    )
    (LetPr
      (IterE (VarE "c_1") List (iterexp "c_1" (VarE "c_1*")))
      (SliceE
        (CallE
          "lanes_"
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
          (ExpA (VarE "v_1"))
        )
        (ProjE (UncaseE (VarE "i") Arg) 0)
        (ProjE (UncaseE (VarE "k") Arg) 0)
      )
    )
    (LetPr
      (IterE (VarE "c_2") List (iterexp "c_2" (VarE "c_2*")))
      (SliceE
        (CallE
          "lanes_"
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                (CaseE Arg (TupE (VarE "M_1")))
              )
            )
          )
          (ExpA (VarE "v_2"))
        )
        (ProjE (UncaseE (VarE "i") Arg) 0)
        (ProjE (UncaseE (VarE "k") Arg) 0)
      )
    )
    (LetPr
      (IterE (VarE "c'_1") List (iterexp "c'_1" (VarE "c'_1*")))
      (IterE
        (CallE
          "extend__"
          (ExpA
            (CallE
              "lsizenn1"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
            )
          )
          (ExpA
            (CallE
              "lsizenn2"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
            )
          )
          (ExpA (VarE "sx_1"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn_1")) (ExpA (VarE "c_1")))
            )
          )
        )
        List
        (iterexp "c_1" (VarE "c_1*"))
      )
    )
    (LetPr
      (IterE (VarE "c'_2") List (iterexp "c'_2" (VarE "c'_2*")))
      (IterE
        (CallE
          "extend__"
          (ExpA
            (CallE
              "lsizenn1"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
            )
          )
          (ExpA
            (CallE
              "lsizenn2"
              (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
            )
          )
          (ExpA (VarE "sx_2"))
          (ExpA
            (TheE
              (CallE "proj_lane__2" (ExpA (VarE "Jnn_1")) (ExpA (VarE "c_2")))
            )
          )
        )
        List
        (iterexp "c_2" (VarE "c_2*"))
      )
    )
    (LetPr
      (IterE (VarE "c") List (iterexp "c" (VarE "c*")))
      (CallE
        "f_"
        (ExpA
          (CallE
            "lsizenn2"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2")))
          )
        )
        (ExpA (IterE (VarE "c'_1") List (iterexp "c'_1" (VarE "c'_1*"))))
        (ExpA (IterE (VarE "c'_2") List (iterexp "c'_2" (VarE "c'_2*"))))
      )
    )
  )
)
(DecD
  "ivmul_"
  (ExpP "N" (VarT "N"))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (ExpP "_" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
  (IterT (VarT "iN" (ExpA (VarE "N"))) List)
  (DefD
    (ExpP "N" nat)
    (ExpP "i_1*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpP "i_2*" (IterT (VarT "iN" (ExpA (VarE "N"))) List))
    (ExpA (VarE "N"))
    (ExpA (IterE (VarE "i_1") List (iterexp "i_1" (VarE "i_1*"))))
    (ExpA (IterE (VarE "i_2") List (iterexp "i_2" (VarE "i_2*"))))
    (IterE
      (CallE "imul_" (ExpA (VarE "N")) (ExpA (VarE "i_1")) (ExpA (VarE "i_2")))
      List
      (iterexp "i_1" (VarE "i_1*"))
      (iterexp "i_2" (VarE "i_2*"))
    )
  )
)
(DecD
  "vextbinop__"
  (ExpP "ishape_1" (VarT "ishape"))
  (ExpP "ishape_2" (VarT "ishape"))
  (ExpP
    "vextbinop__"
    (VarT "vextbinop__" (ExpA (VarE "ishape_1")) (ExpA (VarE "ishape_2")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "half" (VarT "half"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vextbinop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom EXTMUL) Arg Arg) (TupE (VarE "half") (VarE "sx")))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivextbinop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
      (DefA "ivmul_")
      (ExpA (VarE "sx"))
      (ExpA (VarE "sx"))
      (ExpA
        (CaseE
          Arg
          (TupE
            (CallE
              "half"
              (ExpA (VarE "half"))
              (ExpA (NumE (Nat 0)))
              (ExpA (VarE "M_2"))
            )
          )
        )
      )
      (ExpA (CaseE Arg (TupE (VarE "M_2"))))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vextbinop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom DOT) (Atom S)) (TupE))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivextbinop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
      (DefA "ivdot_")
      (ExpA (CaseE (Atom S) (TupE)))
      (ExpA (CaseE (Atom S) (TupE)))
      (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
      (ExpA (CaseE Arg (TupE (VarE "M_1"))))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "v_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "v_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vextbinop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom RELAXED_DOT) (Atom S)) (TupE))
        )
      )
    )
    (ExpA (VarE "v_1"))
    (ExpA (VarE "v_2"))
    (CallE
      "ivextbinop__"
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
            (CaseE Arg (TupE (VarE "M_1")))
          )
        )
      )
      (ExpA
        (CaseE
          (Seq Arg (Atom X) Arg)
          (TupE
            (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
            (CaseE Arg (TupE (VarE "M_2")))
          )
        )
      )
      (DefA "ivdot_sat_")
      (ExpA (CaseE (Atom S) (TupE)))
      (ExpA
        (CallE
          "relaxed2"
          (ExpA (CallE "R_idot"))
          (TypA (VarT "sx"))
          (ExpA (CaseE (Atom S) (TupE)))
          (ExpA (CaseE (Atom U) (TupE)))
        )
      )
      (ExpA (CaseE Arg (TupE (NumE (Nat 0)))))
      (ExpA (CaseE Arg (TupE (VarE "M_1"))))
      (ExpA (VarE "v_1"))
      (ExpA (VarE "v_2"))
    )
  )
)
HintD
(DecD
  "vextternop__"
  (ExpP "ishape_1" (VarT "ishape"))
  (ExpP "ishape_2" (VarT "ishape"))
  (ExpP
    "vextternop__"
    (VarT "vextternop__" (ExpA (VarE "ishape_1")) (ExpA (VarE "ishape_2")))
  )
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (ExpP "vec_" (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE)))))
  (VarT "vec_" (ExpA (CaseE (Atom V128) (TupE))))
  (DefD
    (ExpP "Jnn_1" (VarT "Jnn"))
    (ExpP "M_1" nat)
    (ExpP "Jnn_2" (VarT "Jnn"))
    (ExpP "M_2" nat)
    (ExpP "c_1" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "c_2" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "c_3" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "c" (VarT "uN" (ExpA (NumE (Nat 128)))))
    (ExpP "Jnn" (VarT "Jnn"))
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
              (CaseE Arg (TupE (VarE "M_1")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        Arg
        (TupE
          (CaseE
            (Seq Arg (Atom X) Arg)
            (TupE
              (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
              (CaseE Arg (TupE (VarE "M_2")))
            )
          )
        )
      )
    )
    (ExpA
      (CaseE
        (Seq (Atom mk_vextternop___0) Arg Arg Arg Arg Arg)
        (TupE
          (VarE "Jnn_1")
          (VarE "M_1")
          (VarE "Jnn_2")
          (VarE "M_2")
          (CaseE (Seq (Atom RELAXED_DOT_ADD) (Atom S)) (TupE))
        )
      )
    )
    (ExpA (VarE "c_1"))
    (ExpA (VarE "c_2"))
    (ExpA (VarE "c_3"))
    (VarE "c")
    (IfPr
      (CmpE
        EqOp
        bool
        (CallE "jsizenn" (ExpA (VarE "Jnn")))
        (BinE
          MulOp
          nat
          (NumE (Nat 2))
          (CallE
            "lsizenn1"
            (ExpA (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1")))
          )
        )
      )
    )
    (LetPr (VarE "M") (BinE MulOp nat (NumE (Nat 2)) (VarE "M_2")))
    (LetPr
      (VarE "c'")
      (CallE
        "vextbinop__"
        (ExpA
          (CaseE
            Arg
            (TupE
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE
                  (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_1"))
                  (CaseE Arg (TupE (VarE "M_1")))
                )
              )
            )
          )
        )
        (ExpA
          (CaseE
            Arg
            (TupE
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE
                  (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                  (CaseE Arg (TupE (VarE "M")))
                )
              )
            )
          )
        )
        (ExpA
          (CaseE
            (Seq (Atom mk_vextbinop___0) Arg Arg Arg Arg Arg)
            (TupE
              (VarE "Jnn_1")
              (VarE "M_1")
              (VarE "Jnn")
              (VarE "M")
              (CaseE (Seq (Atom RELAXED_DOT) (Atom S)) (TupE))
            )
          )
        )
        (ExpA (VarE "c_1"))
        (ExpA (VarE "c_2"))
      )
    )
    (LetPr
      (VarE "c''")
      (CallE
        "vextunop__"
        (ExpA
          (CaseE
            Arg
            (TupE
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE
                  (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn"))
                  (CaseE Arg (TupE (VarE "M")))
                )
              )
            )
          )
        )
        (ExpA
          (CaseE
            Arg
            (TupE
              (CaseE
                (Seq Arg (Atom X) Arg)
                (TupE
                  (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                  (CaseE Arg (TupE (VarE "M_2")))
                )
              )
            )
          )
        )
        (ExpA
          (CaseE
            (Seq (Atom mk_vextunop___0) Arg Arg Arg Arg Arg)
            (TupE
              (VarE "Jnn")
              (VarE "M")
              (VarE "Jnn_2")
              (VarE "M_2")
              (CaseE
                (Seq (Atom EXTADD_PAIRWISE) Arg)
                (TupE (CaseE (Atom S) (TupE)))
              )
            )
          )
        )
        (ExpA (VarE "c'"))
      )
    )
    (IfPr
      (MemE
        (VarE "c")
        (CallE
          "vbinop_"
          (ExpA
            (CaseE
              (Seq Arg (Atom X) Arg)
              (TupE
                (SubE (VarT "Jnn") (VarT "lanetype") (VarE "Jnn_2"))
                (CaseE Arg (TupE (VarE "M_2")))
              )
            )
          )
          (ExpA
            (CaseE
              (Seq (Atom mk_vbinop__0) Arg Arg Arg)
              (TupE (VarE "Jnn_2") (VarE "M_2") (CaseE (Atom ADD) (TupE)))
            )
          )
          (ExpA (VarE "c''"))
          (ExpA (VarE "c_3"))
        )
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
HintD
HintD
HintD
HintD
HintD
HintD
HintD
HintD
(TypD
  "num"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom CONST) Arg Arg)
        (TupT
          (typbind "numtype" (VarT "numtype"))
          (typbind "_" (VarT "num_" (ExpA (VarE "numtype"))))
        )
      )
    )
  )
)
HintD
(TypD
  "vec"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom VCONST) Arg Arg)
        (TupT
          (typbind "vectype" (VarT "vectype"))
          (typbind "_" (VarT "vec_" (ExpA (VarE "vectype"))))
        )
      )
    )
  )
)
HintD
HintD
HintD
(TypD
  "result"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom _VALS) Arg)
        (TupT (typbind "val*" (IterT (VarT "val") List)))
      )
      (typcase
        (Seq (Brack ( (Seq (Atom REF.EXN_ADDR) Arg) )) (Atom THROW_REF))
        (TupT (typbind "exnaddr" (VarT "exnaddr")))
      )
      (typcase (Atom TRAP) (TupT))
    )
  )
)
HintD
(TypD "hostfunc" (InstD (VariantT (typcase (Atom ...) (TupT)))))
HintD
(TypD
  "funccode"
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
      (typcase (Atom ...) (TupT))
    )
  )
)
HintD
(TypD "taginst" (InstD (StructT (typfield (Atom TYPE) (VarT "tagtype")))))
HintD
(TypD
  "globalinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "globaltype"))
      (typfield (Atom VALUE) (VarT "val"))
    )
  )
)
HintD
(TypD
  "meminst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "memtype"))
      (typfield (Atom BYTES) (IterT (VarT "byte") List))
    )
  )
)
HintD
(TypD
  "tableinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "tabletype"))
      (typfield (Atom REFS) (IterT (VarT "ref") List))
    )
  )
)
HintD
(TypD
  "funcinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "deftype"))
      (typfield (Atom MODULE) (VarT "moduleinst"))
      (typfield (Atom CODE) (VarT "funccode"))
    )
  )
)
HintD
(TypD
  "datainst"
  (InstD (StructT (typfield (Atom BYTES) (IterT (VarT "byte") List))))
)
HintD
(TypD
  "eleminst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "elemtype"))
      (typfield (Atom REFS) (IterT (VarT "ref") List))
    )
  )
)
HintD
HintD
(TypD
  "packval"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom PACK) Arg Arg)
        (TupT
          (typbind "packtype" (VarT "packtype"))
          (typbind
            "_"
            (VarT "iN" (ExpA (CallE "psizenn" (ExpA (VarE "packtype")))))
          )
        )
      )
    )
  )
)
HintD
(TypD
  "fieldval"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom CONST) Arg Arg)
        (TupT
          (typbind "numtype" (VarT "numtype"))
          (typbind "_" (VarT "num_" (ExpA (VarE "numtype"))))
        )
      )
      (typcase
        (Seq (Atom VCONST) Arg Arg)
        (TupT
          (typbind "vectype" (VarT "vectype"))
          (typbind "_" (VarT "vec_" (ExpA (VarE "vectype"))))
        )
      )
      (typcase (Seq (Atom REF.I31_NUM) Arg) (TupT (typbind "u31" (VarT "u31"))))
      (typcase (Atom REF.NULL_ADDR) (TupT))
      (typcase
        (Seq (Atom REF.STRUCT_ADDR) Arg)
        (TupT (typbind "structaddr" (VarT "structaddr")))
      )
      (typcase
        (Seq (Atom REF.ARRAY_ADDR) Arg)
        (TupT (typbind "arrayaddr" (VarT "arrayaddr")))
      )
      (typcase
        (Seq (Atom REF.FUNC_ADDR) Arg)
        (TupT (typbind "funcaddr" (VarT "funcaddr")))
      )
      (typcase
        (Seq (Atom REF.EXN_ADDR) Arg)
        (TupT (typbind "exnaddr" (VarT "exnaddr")))
      )
      (typcase
        (Seq (Atom REF.HOST_ADDR) Arg)
        (TupT (typbind "hostaddr" (VarT "hostaddr")))
      )
      (typcase (Seq (Atom REF.EXTERN) Arg) (TupT (typbind "ref" (VarT "ref"))))
      (typcase
        (Seq (Atom PACK) Arg Arg)
        (TupT
          (typbind "packtype" (VarT "packtype"))
          (typbind
            "_"
            (VarT "iN" (ExpA (CallE "psizenn" (ExpA (VarE "packtype")))))
          )
        )
      )
    )
  )
)
HintD
(TypD
  "structinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "deftype"))
      (typfield (Atom FIELDS) (IterT (VarT "fieldval") List))
    )
  )
)
HintD
(TypD
  "arrayinst"
  (InstD
    (StructT
      (typfield (Atom TYPE) (VarT "deftype"))
      (typfield (Atom FIELDS) (IterT (VarT "fieldval") List))
    )
  )
)
HintD
(TypD
  "exninst"
  (InstD
    (StructT
      (typfield (Atom TAG) (VarT "tagaddr"))
      (typfield (Atom FIELDS) (IterT (VarT "val") List))
    )
  )
)
HintD
HintD
(TypD
  "store"
  (InstD
    (StructT
      (typfield (Atom TAGS) (IterT (VarT "taginst") List))
      (typfield (Atom GLOBALS) (IterT (VarT "globalinst") List))
      (typfield (Atom MEMS) (IterT (VarT "meminst") List))
      (typfield (Atom TABLES) (IterT (VarT "tableinst") List))
      (typfield (Atom FUNCS) (IterT (VarT "funcinst") List))
      (typfield (Atom DATAS) (IterT (VarT "datainst") List))
      (typfield (Atom ELEMS) (IterT (VarT "eleminst") List))
      (typfield (Atom STRUCTS) (IterT (VarT "structinst") List))
      (typfield (Atom ARRAYS) (IterT (VarT "arrayinst") List))
      (typfield (Atom EXNS) (IterT (VarT "exninst") List))
    )
  )
)
HintD
HintD
HintD
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
HintD
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
HintD
(DecD "Ki" nat (DefD (NumE (Nat 1024))))
HintD
(DecD
  "packfield_"
  (ExpP "storagetype" (VarT "storagetype"))
  (ExpP "val" (VarT "val"))
  (VarT "fieldval")
  (DefD
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "val" (VarT "val"))
    (ExpA (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype")))
    (ExpA (VarE "val"))
    (SubE (VarT "val") (VarT "fieldval") (VarE "val"))
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "i" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (ExpA
      (CaseE
        (Seq (Atom CONST) Arg Arg)
        (TupE
          (CaseE (Atom I32) (TupE))
          (CaseE
            (Seq (Atom mk_num__0) Arg Arg)
            (TupE (CaseE (Atom I32) (TupE)) (VarE "i"))
          )
        )
      )
    )
    (CaseE
      (Seq (Atom PACK) Arg Arg)
      (TupE
        (VarE "packtype")
        (CallE
          "wrap__"
          (ExpA (NumE (Nat 32)))
          (ExpA (CallE "psize" (ExpA (VarE "packtype"))))
          (ExpA (VarE "i"))
        )
      )
    )
  )
)
HintD
(DecD
  "unpackfield_"
  (ExpP "storagetype" (VarT "storagetype"))
  (ExpP "_" (IterT (VarT "sx") Opt))
  (ExpP "fieldval" (VarT "fieldval"))
  (VarT "val")
  (DefD
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "val" (VarT "val"))
    (ExpA (SubE (VarT "valtype") (VarT "storagetype") (VarE "valtype")))
    (ExpA (OptE))
    (ExpA (SubE (VarT "val") (VarT "fieldval") (VarE "val")))
    (VarE "val")
  )
  (DefD
    (ExpP "packtype" (VarT "packtype"))
    (ExpP "sx" (VarT "sx"))
    (ExpP "i" (VarT "uN" (ExpA (CallE "psize" (ExpA (VarE "packtype"))))))
    (ExpA (SubE (VarT "packtype") (VarT "storagetype") (VarE "packtype")))
    (ExpA (OptE (VarE "sx")))
    (ExpA (CaseE (Seq (Atom PACK) Arg Arg) (TupE (VarE "packtype") (VarE "i"))))
    (CaseE
      (Seq (Atom CONST) Arg Arg)
      (TupE
        (CaseE (Atom I32) (TupE))
        (CaseE
          (Seq (Atom mk_num__0) Arg Arg)
          (TupE
            (CaseE (Atom I32) (TupE))
            (CallE
              "extend__"
              (ExpA (CallE "psize" (ExpA (VarE "packtype"))))
              (ExpA (NumE (Nat 32)))
              (ExpA (VarE "sx"))
              (ExpA (VarE "i"))
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
    "tagsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "tagaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "a" nat)
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "a"))))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CatE
        (ListE (VarE "a"))
        (CallE
          "tagsxa"
          (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CallE
        "tagsxa"
        (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "globalsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "globaladdr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "a" nat)
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "a"))))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CatE
        (ListE (VarE "a"))
        (CallE
          "globalsxa"
          (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CallE
        "globalsxa"
        (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "memsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "memaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "a" nat)
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "a"))))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CatE
        (ListE (VarE "a"))
        (CallE
          "memsxa"
          (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CallE
        "memsxa"
        (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "tablesxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "tableaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "a" nat)
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "a"))))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CatE
        (ListE (VarE "a"))
        (CallE
          "tablesxa"
          (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CallE
        "tablesxa"
        (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
      )
    )
  )
)
HintD
(RecD
  (DecD
    "funcsxa"
    (ExpP "_" (IterT (VarT "externaddr") List))
    (IterT (VarT "funcaddr") List)
    (DefD (ExpA (ListE)) (ListE))
    (DefD
      (ExpP "a" nat)
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "a"))))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CatE
        (ListE (VarE "a"))
        (CallE
          "funcsxa"
          (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
        )
      )
    )
    (DefD
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xa*" (IterT (VarT "externaddr") List))
      (ExpA
        (CatE
          (ListE (VarE "externaddr"))
          (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*")))
        )
      )
      (CallE
        "funcsxa"
        (ExpA (IterE (VarE "xa") List (iterexp "xa" (VarE "xa*"))))
      )
    )
  )
)
HintD
(DecD
  "store"
  (ExpP "state" (VarT "state"))
  (VarT "store")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (VarE "s")
  )
)
HintD
(DecD
  "frame"
  (ExpP "state" (VarT "state"))
  (VarT "frame")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (VarE "f")
  )
)
HintD
(DecD
  "tagaddr"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "tagaddr") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (DotE (VarE "f") (Atom MODULE)) (Atom TAGS))
  )
)
HintD
(DecD
  "moduleinst"
  (ExpP "state" (VarT "state"))
  (VarT "moduleinst")
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "f") (Atom MODULE))
  )
)
HintD
(DecD
  "taginst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "taginst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom TAGS))
  )
)
HintD
(DecD
  "globalinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "globalinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom GLOBALS))
  )
)
HintD
(DecD
  "meminst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "meminst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom MEMS))
  )
)
HintD
(DecD
  "tableinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "tableinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom TABLES))
  )
)
HintD
(DecD
  "funcinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "funcinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom FUNCS))
  )
)
HintD
(DecD
  "datainst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "datainst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom DATAS))
  )
)
HintD
(DecD
  "eleminst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "eleminst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom ELEMS))
  )
)
HintD
(DecD
  "structinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "structinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom STRUCTS))
  )
)
HintD
(DecD
  "arrayinst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "arrayinst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom ARRAYS))
  )
)
HintD
(DecD
  "exninst"
  (ExpP "state" (VarT "state"))
  (IterT (VarT "exninst") List)
  (DefD
    (ExpP "s" (VarT "store"))
    (ExpP "f" (VarT "frame"))
    (ExpA (CaseE (Infix Arg ; Arg) (TupE (VarE "s") (VarE "f"))))
    (DotE (VarE "s") (Atom EXNS))
  )
)
HintD
(DecD
  "fof"
  (ExpP "state" (VarT "state"))
  (VarT "frame")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpA (VarE "z"))
    (CallE "frame" (ExpA (VarE "z")))
  )
)
(DecD
  "type"
  (ExpP "state" (VarT "state"))
  (ExpP "typeidx" (VarT "typeidx"))
  (VarT "deftype")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE)) (Atom TYPES))
      (ProjE (UncaseE (VarE "x") Arg) 0)
    )
  )
)
HintD
(DecD
  "sof"
  (ExpP "state" (VarT "state"))
  (VarT "store")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpA (VarE "z"))
    (CallE "store" (ExpA (VarE "z")))
  )
)
(DecD
  "tag"
  (ExpP "state" (VarT "state"))
  (ExpP "tagidx" (VarT "tagidx"))
  (VarT "taginst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom TAGS))
      (IdxE
        (DotE (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE)) (Atom TAGS))
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "global"
  (ExpP "state" (VarT "state"))
  (ExpP "globalidx" (VarT "globalidx"))
  (VarT "globalinst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom GLOBALS))
      (IdxE
        (DotE
          (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
          (Atom GLOBALS)
        )
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "mem"
  (ExpP "state" (VarT "state"))
  (ExpP "memidx" (VarT "memidx"))
  (VarT "meminst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom MEMS))
      (IdxE
        (DotE (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE)) (Atom MEMS))
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "table"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (VarT "tableinst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom TABLES))
      (IdxE
        (DotE
          (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
          (Atom TABLES)
        )
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "func"
  (ExpP "state" (VarT "state"))
  (ExpP "funcidx" (VarT "funcidx"))
  (VarT "funcinst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom FUNCS))
      (IdxE
        (DotE (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE)) (Atom FUNCS))
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "data"
  (ExpP "state" (VarT "state"))
  (ExpP "dataidx" (VarT "dataidx"))
  (VarT "datainst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom DATAS))
      (IdxE
        (DotE (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE)) (Atom DATAS))
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "elem"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (VarT "eleminst")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "sof" (ExpA (VarE "z"))) (Atom ELEMS))
      (IdxE
        (DotE (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE)) (Atom ELEMS))
        (ProjE (UncaseE (VarE "x") Arg) 0)
      )
    )
  )
)
HintD
(DecD
  "local"
  (ExpP "state" (VarT "state"))
  (ExpP "localidx" (VarT "localidx"))
  (IterT (VarT "val") Opt)
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (IdxE
      (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom LOCALS))
      (ProjE (UncaseE (VarE "x") Arg) 0)
    )
  )
)
HintD
HintD
HintD
(DecD
  "with_local"
  (ExpP "state" (VarT "state"))
  (ExpP "localidx" (VarT "localidx"))
  (ExpP "val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "v" (VarT "val"))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (CallE "sof" (ExpA (VarE "z")))
        (UpdE
          (CallE "fof" (ExpA (VarE "z")))
          (IdxP (DotP RootP (Atom LOCALS)) (ProjE (UncaseE (VarE "x") Arg) 0))
          (OptE (VarE "v"))
        )
      )
    )
  )
)
HintD
(DecD
  "with_global"
  (ExpP "state" (VarT "state"))
  (ExpP "globalidx" (VarT "globalidx"))
  (ExpP "val" (VarT "val"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "v" (VarT "val"))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (VarE "v"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (DotP
            (IdxP
              (DotP RootP (Atom GLOBALS))
              (IdxE
                (DotE
                  (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                  (Atom GLOBALS)
                )
                (ProjE (UncaseE (VarE "x") Arg) 0)
              )
            )
            (Atom VALUE)
          )
          (VarE "v")
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_table"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (ExpP "nat" nat)
  (ExpP "ref" (VarT "ref"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "i" nat)
    (ExpP "r" (VarT "ref"))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (VarE "i"))
    (ExpA (VarE "r"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (IdxP
            (DotP
              (IdxP
                (DotP RootP (Atom TABLES))
                (IdxE
                  (DotE
                    (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                    (Atom TABLES)
                  )
                  (ProjE (UncaseE (VarE "x") Arg) 0)
                )
              )
              (Atom REFS)
            )
            (VarE "i")
          )
          (VarE "r")
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_tableinst"
  (ExpP "state" (VarT "state"))
  (ExpP "tableidx" (VarT "tableidx"))
  (ExpP "tableinst" (VarT "tableinst"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "ti" (VarT "tableinst"))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (VarE "ti"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (IdxP
            (DotP RootP (Atom TABLES))
            (IdxE
              (DotE
                (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                (Atom TABLES)
              )
              (ProjE (UncaseE (VarE "x") Arg) 0)
            )
          )
          (VarE "ti")
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_mem"
  (ExpP "state" (VarT "state"))
  (ExpP "memidx" (VarT "memidx"))
  (ExpP "nat" nat)
  (ExpP "nat" nat)
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "i" nat)
    (ExpP "j" nat)
    (ExpP "b*" (IterT (VarT "byte") List))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (VarE "i"))
    (ExpA (VarE "j"))
    (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (SliceP
            (DotP
              (IdxP
                (DotP RootP (Atom MEMS))
                (IdxE
                  (DotE
                    (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                    (Atom MEMS)
                  )
                  (ProjE (UncaseE (VarE "x") Arg) 0)
                )
              )
              (Atom BYTES)
            )
            (VarE "i")
            (VarE "j")
          )
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_meminst"
  (ExpP "state" (VarT "state"))
  (ExpP "memidx" (VarT "memidx"))
  (ExpP "meminst" (VarT "meminst"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "mi" (VarT "meminst"))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (VarE "mi"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (IdxP
            (DotP RootP (Atom MEMS))
            (IdxE
              (DotE
                (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                (Atom MEMS)
              )
              (ProjE (UncaseE (VarE "x") Arg) 0)
            )
          )
          (VarE "mi")
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_elem"
  (ExpP "state" (VarT "state"))
  (ExpP "elemidx" (VarT "elemidx"))
  (ExpP "_" (IterT (VarT "ref") List))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "r*" (IterT (VarT "ref") List))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (IterE (VarE "r") List (iterexp "r" (VarE "r*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (DotP
            (IdxP
              (DotP RootP (Atom ELEMS))
              (IdxE
                (DotE
                  (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                  (Atom ELEMS)
                )
                (ProjE (UncaseE (VarE "x") Arg) 0)
              )
            )
            (Atom REFS)
          )
          (IterE (VarE "r") List (iterexp "r" (VarE "r*")))
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_data"
  (ExpP "state" (VarT "state"))
  (ExpP "dataidx" (VarT "dataidx"))
  (ExpP "_" (IterT (VarT "byte") List))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "x" (VarT "uN" (ExpA (NumE (Nat 32)))))
    (ExpP "b*" (IterT (VarT "byte") List))
    (ExpA (VarE "z"))
    (ExpA (VarE "x"))
    (ExpA (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (DotP
            (IdxP
              (DotP RootP (Atom DATAS))
              (IdxE
                (DotE
                  (DotE (CallE "fof" (ExpA (VarE "z"))) (Atom MODULE))
                  (Atom DATAS)
                )
                (ProjE (UncaseE (VarE "x") Arg) 0)
              )
            )
            (Atom BYTES)
          )
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_struct"
  (ExpP "state" (VarT "state"))
  (ExpP "structaddr" (VarT "structaddr"))
  (ExpP "nat" nat)
  (ExpP "fieldval" (VarT "fieldval"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "a" nat)
    (ExpP "i" nat)
    (ExpP "fv" (VarT "fieldval"))
    (ExpA (VarE "z"))
    (ExpA (VarE "a"))
    (ExpA (VarE "i"))
    (ExpA (VarE "fv"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (IdxP
            (DotP (IdxP (DotP RootP (Atom STRUCTS)) (VarE "a")) (Atom FIELDS))
            (VarE "i")
          )
          (VarE "fv")
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "with_array"
  (ExpP "state" (VarT "state"))
  (ExpP "arrayaddr" (VarT "arrayaddr"))
  (ExpP "nat" nat)
  (ExpP "fieldval" (VarT "fieldval"))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "a" nat)
    (ExpP "i" nat)
    (ExpP "fv" (VarT "fieldval"))
    (ExpA (VarE "z"))
    (ExpA (VarE "a"))
    (ExpA (VarE "i"))
    (ExpA (VarE "fv"))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (UpdE
          (CallE "sof" (ExpA (VarE "z")))
          (IdxP
            (DotP (IdxP (DotP RootP (Atom ARRAYS)) (VarE "a")) (Atom FIELDS))
            (VarE "i")
          )
          (VarE "fv")
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "add_structinst"
  (ExpP "state" (VarT "state"))
  (ExpP "_" (IterT (VarT "structinst") List))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "si*" (IterT (VarT "structinst") List))
    (ExpA (VarE "z"))
    (ExpA (IterE (VarE "si") List (iterexp "si" (VarE "si*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (ExtE
          (CallE "sof" (ExpA (VarE "z")))
          (DotP RootP (Atom STRUCTS))
          (IterE (VarE "si") List (iterexp "si" (VarE "si*")))
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "add_arrayinst"
  (ExpP "state" (VarT "state"))
  (ExpP "_" (IterT (VarT "arrayinst") List))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "ai*" (IterT (VarT "arrayinst") List))
    (ExpA (VarE "z"))
    (ExpA (IterE (VarE "ai") List (iterexp "ai" (VarE "ai*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (ExtE
          (CallE "sof" (ExpA (VarE "z")))
          (DotP RootP (Atom ARRAYS))
          (IterE (VarE "ai") List (iterexp "ai" (VarE "ai*")))
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "add_exninst"
  (ExpP "state" (VarT "state"))
  (ExpP "_" (IterT (VarT "exninst") List))
  (VarT "state")
  (DefD
    (ExpP "z" (VarT "state"))
    (ExpP "exn*" (IterT (VarT "exninst") List))
    (ExpA (VarE "z"))
    (ExpA (IterE (VarE "exn") List (iterexp "exn" (VarE "exn*"))))
    (CaseE
      (Infix Arg ; Arg)
      (TupE
        (ExtE
          (CallE "sof" (ExpA (VarE "z")))
          (DotP RootP (Atom EXNS))
          (IterE (VarE "exn") List (iterexp "exn" (VarE "exn*")))
        )
        (CallE "fof" (ExpA (VarE "z")))
      )
    )
  )
)
HintD
(DecD
  "growtable"
  (ExpP "tableinst" (VarT "tableinst"))
  (ExpP "nat" nat)
  (ExpP "ref" (VarT "ref"))
  (VarT "tableinst")
  (DefD
    (ExpP "tableinst" (VarT "tableinst"))
    (ExpP "n" nat)
    (ExpP "r" (VarT "ref"))
    (ExpP "tableinst'" (VarT "tableinst"))
    (ExpP "i'" (VarT "uN" (ExpA (NumE (Nat 64)))))
    (ExpA (VarE "tableinst"))
    (ExpA (VarE "n"))
    (ExpA (VarE "r"))
    (VarE "tableinst'")
    (LetPr
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq Arg Arg Arg)
            (TupE
              (VarE "at")
              (CaseE
                (Brack [ (Infix Arg .. Arg) ])
                (TupE
                  (VarE "i")
                  (IterE (VarE "j") Opt (iterexp "j" (VarE "j?")))
                )
              )
              (VarE "rt")
            )
          )
        )
        (expfield
          (Atom REFS)
          (IterE (VarE "r'") List (iterexp "r'" (VarE "r'*")))
        )
      )
      (VarE "tableinst")
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "tableinst'")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq Arg Arg Arg)
              (TupE
                (VarE "at")
                (CaseE
                  (Brack [ (Infix Arg .. Arg) ])
                  (TupE
                    (VarE "i'")
                    (IterE (VarE "j") Opt (iterexp "j" (VarE "j?")))
                  )
                )
                (VarE "rt")
              )
            )
          )
          (expfield
            (Atom REFS)
            (CatE
              (IterE (VarE "r'") List (iterexp "r'" (VarE "r'*")))
              (IterE (VarE "r") (ListN (VarE "n")))
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (ProjE (UncaseE (VarE "i'") Arg) 0)
        (BinE
          AddOp
          nat
          (LenE (IterE (VarE "r'") List (iterexp "r'" (VarE "r'*"))))
          (VarE "n")
        )
      )
    )
    (IterPr
      (IfPr
        (CmpE
          LeOp
          nat
          (ProjE (UncaseE (VarE "i'") Arg) 0)
          (ProjE (UncaseE (VarE "j") Arg) 0)
        )
      )
      Opt
      (iterexp "j" (VarE "j?"))
    )
    (IfPr
      (CmpE
        LeOp
        int
        (CvtE nat int (ProjE (UncaseE (VarE "i'") Arg) 0))
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
              (CallE
                "size"
                (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "at")))
              )
            )
          )
          (CvtE nat int (NumE (Nat 1)))
        )
      )
    )
  )
)
HintD
(DecD
  "growmem"
  (ExpP "meminst" (VarT "meminst"))
  (ExpP "nat" nat)
  (VarT "meminst")
  (DefD
    (ExpP "meminst" (VarT "meminst"))
    (ExpP "n" nat)
    (ExpP "meminst'" (VarT "meminst"))
    (ExpP "i'" (VarT "uN" (ExpA (NumE (Nat 64)))))
    (ExpA (VarE "meminst"))
    (ExpA (VarE "n"))
    (VarE "meminst'")
    (LetPr
      (StrE
        (expfield
          (Atom TYPE)
          (CaseE
            (Seq Arg Arg (Atom PAGE))
            (TupE
              (VarE "at")
              (CaseE
                (Brack [ (Infix Arg .. Arg) ])
                (TupE
                  (VarE "i")
                  (IterE (VarE "j") Opt (iterexp "j" (VarE "j?")))
                )
              )
            )
          )
        )
        (expfield
          (Atom BYTES)
          (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
        )
      )
      (VarE "meminst")
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "meminst'")
        (StrE
          (expfield
            (Atom TYPE)
            (CaseE
              (Seq Arg Arg (Atom PAGE))
              (TupE
                (VarE "at")
                (CaseE
                  (Brack [ (Infix Arg .. Arg) ])
                  (TupE
                    (VarE "i'")
                    (IterE (VarE "j") Opt (iterexp "j" (VarE "j?")))
                  )
                )
              )
            )
          )
          (expfield
            (Atom BYTES)
            (CatE
              (IterE (VarE "b") List (iterexp "b" (VarE "b*")))
              (IterE
                (CaseE Arg (TupE (NumE (Nat 0))))
                (ListN
                  (BinE
                    MulOp
                    nat
                    (VarE "n")
                    (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki"))
                  )
                )
              )
            )
          )
        )
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (CvtE nat rat (ProjE (UncaseE (VarE "i'") Arg) 0))
        (BinE
          AddOp
          rat
          (BinE
            DivOp
            rat
            (CvtE
              nat
              rat
              (LenE (IterE (VarE "b") List (iterexp "b" (VarE "b*"))))
            )
            (CvtE nat rat (BinE MulOp nat (NumE (Nat 64)) (CallE "Ki")))
          )
          (CvtE nat rat (VarE "n"))
        )
      )
    )
    (IterPr
      (IfPr
        (CmpE
          LeOp
          nat
          (ProjE (UncaseE (VarE "i'") Arg) 0)
          (ProjE (UncaseE (VarE "j") Arg) 0)
        )
      )
      Opt
      (iterexp "j" (VarE "j?"))
    )
    (IfPr
      (CmpE
        LeOp
        nat
        (ProjE (UncaseE (VarE "i'") Arg) 0)
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
              (CvtE
                nat
                int
                (CallE
                  "size"
                  (ExpA (SubE (VarT "addrtype") (VarT "numtype") (VarE "at")))
                )
              )
              (CvtE nat int (NumE (Nat 16)))
            )
          )
        )
      )
    )
  )
)
HintD
HintD
(RelD
  "Num_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "num"))
    (typbind "_" (VarT "numtype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "nt" (VarT "numtype"))
    (ExpP "c" (VarT "num_" (ExpA (VarE "nt"))))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (CaseE (Seq (Atom CONST) Arg Arg) (TupE (VarE "nt") (VarE "c")))
      (VarE "nt")
    )
  )
)
HintD
(RelD
  "Vec_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "vec"))
    (typbind "_" (VarT "vectype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "vt" (VarT "vectype"))
    (ExpP "c" (VarT "vec_" (ExpA (VarE "vt"))))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (CaseE (Seq (Atom VCONST) Arg Arg) (TupE (VarE "vt") (VarE "c")))
      (VarE "vt")
    )
  )
)
HintD
(RecD
  (RelD
    "Ref_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "ref"))
      (typbind "_" (VarT "reftype"))
    )
    (RuleD
      "null"
      (ExpP "s" (VarT "store"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Atom REF.NULL_ADDR) (TupE))
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (OptE (CaseE (Atom NULL) (TupE))) (CaseE (Atom BOT) (TupE)))
        )
      )
    )
    (RuleD
      "i31"
      (ExpP "s" (VarT "store"))
      (ExpP "i" (VarT "u31"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.I31_NUM) Arg) (TupE (VarE "i")))
        (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (CaseE (Atom I31) (TupE))))
      )
    )
    (RuleD
      "struct"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "dt" (VarT "deftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.STRUCT_ADDR) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (OptE) (SubE (VarT "deftype") (VarT "heaptype") (VarE "dt")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (IdxE (DotE (VarE "s") (Atom STRUCTS)) (VarE "a")) (Atom TYPE))
          (VarE "dt")
        )
      )
    )
    (RuleD
      "array"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "dt" (VarT "deftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.ARRAY_ADDR) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (OptE) (SubE (VarT "deftype") (VarT "heaptype") (VarE "dt")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (IdxE (DotE (VarE "s") (Atom ARRAYS)) (VarE "a")) (Atom TYPE))
          (VarE "dt")
        )
      )
    )
    (RuleD
      "func"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "dt" (VarT "deftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.FUNC_ADDR) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (OptE) (SubE (VarT "deftype") (VarT "heaptype") (VarE "dt")))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (DotE (IdxE (DotE (VarE "s") (Atom FUNCS)) (VarE "a")) (Atom TYPE))
          (VarE "dt")
        )
      )
    )
    (RuleD
      "exn"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "exn" (VarT "exninst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.EXN_ADDR) Arg) (TupE (VarE "a")))
        (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (CaseE (Atom EXN) (TupE))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom EXNS)) (VarE "a"))
          (VarE "exn")
        )
      )
    )
    (RuleD
      "host"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.HOST_ADDR) Arg) (TupE (VarE "a")))
        (CaseE (Seq (Atom REF) Arg Arg) (TupE (OptE) (CaseE (Atom ANY) (TupE))))
      )
    )
    (RuleD
      "extern"
      (ExpP "s" (VarT "store"))
      (ExpP "ref" (VarT "ref"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom REF.EXTERN) Arg) (TupE (VarE "ref")))
        (CaseE
          (Seq (Atom REF) Arg Arg)
          (TupE (OptE) (CaseE (Atom EXTERN) (TupE)))
        )
      )
      (RulePr
        "Ref_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE
          (VarE "s")
          (VarE "ref")
          (CaseE
            (Seq (Atom REF) Arg Arg)
            (TupE (OptE) (CaseE (Atom ANY) (TupE)))
          )
        )
      )
      (IfPr (CmpE NeOp bool (VarE "ref") (CaseE (Atom REF.NULL_ADDR) (TupE))))
    )
    (RuleD
      "sub"
      (ExpP "s" (VarT "store"))
      (ExpP "ref" (VarT "ref"))
      (ExpP "rt" (VarT "reftype"))
      (ExpP "rt'" (VarT "reftype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "ref") (VarE "rt"))
      (RulePr
        "Ref_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "ref") (VarE "rt'"))
      )
      (RulePr
        "Reftype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
          (VarE "rt")
        )
      )
      (RulePr
        "Reftype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
          (VarE "rt'")
          (VarE "rt")
        )
      )
    )
  )
)
HintD
(RelD
  "Val_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "val"))
    (typbind "_" (VarT "valtype"))
  )
  (RuleD
    "num"
    (ExpP "s" (VarT "store"))
    (ExpP "num" (VarT "num"))
    (ExpP "nt" (VarT "numtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (SubE (VarT "num") (VarT "val") (VarE "num"))
      (SubE (VarT "numtype") (VarT "valtype") (VarE "nt"))
    )
    (RulePr
      "Num_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "num") (VarE "nt"))
    )
  )
  (RuleD
    "vec"
    (ExpP "s" (VarT "store"))
    (ExpP "vec" (VarT "vec"))
    (ExpP "vt" (VarT "vectype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (SubE (VarT "vec") (VarT "val") (VarE "vec"))
      (SubE (VarT "vectype") (VarT "valtype") (VarE "vt"))
    )
    (RulePr
      "Vec_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "vec") (VarE "vt"))
    )
  )
  (RuleD
    "ref"
    (ExpP "s" (VarT "store"))
    (ExpP "ref" (VarT "ref"))
    (ExpP "rt" (VarT "reftype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (SubE (VarT "ref") (VarT "val") (VarE "ref"))
      (SubE (VarT "reftype") (VarT "valtype") (VarE "rt"))
    )
    (RulePr
      "Ref_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "ref") (VarE "rt"))
    )
  )
)
HintD
(RelD
  "Packval_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "packval"))
    (typbind "_" (VarT "packtype"))
  )
  (RuleD
    ""
    (ExpP "s" (VarT "store"))
    (ExpP "pt" (VarT "packtype"))
    (ExpP "c" (VarT "iN" (ExpA (CallE "psizenn" (ExpA (VarE "pt"))))))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (CaseE (Seq (Atom PACK) Arg Arg) (TupE (VarE "pt") (VarE "c")))
      (VarE "pt")
    )
  )
)
(RelD
  "Fieldval_ok"
  (Infix Arg |- (Infix Arg : Arg))
  (TupT
    (typbind "_" (VarT "store"))
    (typbind "_" (VarT "fieldval"))
    (typbind "_" (VarT "storagetype"))
  )
  (RuleD
    "val"
    (ExpP "s" (VarT "store"))
    (ExpP "val" (VarT "val"))
    (ExpP "t" (VarT "valtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (SubE (VarT "val") (VarT "fieldval") (VarE "val"))
      (SubE (VarT "valtype") (VarT "storagetype") (VarE "t"))
    )
    (RulePr
      "Val_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "val") (VarE "t"))
    )
  )
  (RuleD
    "packval"
    (ExpP "s" (VarT "store"))
    (ExpP "packval" (VarT "packval"))
    (ExpP "pt" (VarT "packtype"))
    (Infix Arg |- (Infix Arg : Arg))
    (TupE
      (VarE "s")
      (SubE (VarT "packval") (VarT "fieldval") (VarE "packval"))
      (SubE (VarT "packtype") (VarT "storagetype") (VarE "pt"))
    )
    (RulePr
      "Packval_ok"
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "packval") (VarE "pt"))
    )
  )
)
(RecD
  (RelD
    "Externaddr_ok"
    (Infix Arg |- (Infix Arg : Arg))
    (TupT
      (typbind "_" (VarT "store"))
      (typbind "_" (VarT "externaddr"))
      (typbind "_" (VarT "externtype"))
    )
    (RuleD
      "tag"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "taginst" (VarT "taginst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom TAG) Arg) (TupE (VarE "a")))
        (CaseE (Seq (Atom TAG) Arg) (TupE (DotE (VarE "taginst") (Atom TYPE))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom TAGS)) (VarE "a"))
          (VarE "taginst")
        )
      )
    )
    (RuleD
      "global"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "globalinst" (VarT "globalinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom GLOBAL) Arg)
          (TupE (DotE (VarE "globalinst") (Atom TYPE)))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom GLOBALS)) (VarE "a"))
          (VarE "globalinst")
        )
      )
    )
    (RuleD
      "mem"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "meminst" (VarT "meminst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "a")))
        (CaseE (Seq (Atom MEM) Arg) (TupE (DotE (VarE "meminst") (Atom TYPE))))
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom MEMS)) (VarE "a"))
          (VarE "meminst")
        )
      )
    )
    (RuleD
      "table"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "tableinst" (VarT "tableinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom TABLE) Arg)
          (TupE (DotE (VarE "tableinst") (Atom TYPE)))
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom TABLES)) (VarE "a"))
          (VarE "tableinst")
        )
      )
    )
    (RuleD
      "func"
      (ExpP "s" (VarT "store"))
      (ExpP "a" (VarT "addr"))
      (ExpP "funcinst" (VarT "funcinst"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE
        (VarE "s")
        (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "a")))
        (CaseE
          (Seq (Atom FUNC) Arg)
          (TupE
            (SubE
              (VarT "deftype")
              (VarT "typeuse")
              (DotE (VarE "funcinst") (Atom TYPE))
            )
          )
        )
      )
      (IfPr
        (CmpE
          EqOp
          bool
          (IdxE (DotE (VarE "s") (Atom FUNCS)) (VarE "a"))
          (VarE "funcinst")
        )
      )
    )
    (RuleD
      "sub"
      (ExpP "s" (VarT "store"))
      (ExpP "externaddr" (VarT "externaddr"))
      (ExpP "xt" (VarT "externtype"))
      (ExpP "xt'" (VarT "externtype"))
      (Infix Arg |- (Infix Arg : Arg))
      (TupE (VarE "s") (VarE "externaddr") (VarE "xt"))
      (RulePr
        "Externaddr_ok"
        (Infix Arg |- (Infix Arg : Arg))
        (TupE (VarE "s") (VarE "externaddr") (VarE "xt'"))
      )
      (RulePr
        "Externtype_ok"
        (Infix Arg |- (Infix Arg : (Atom OK)))
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
          (VarE "xt")
        )
      )
      (RulePr
        "Externtype_sub"
        (Infix Arg |- (Infix Arg <: Arg))
        (TupE
          (StrE
            (expfield (Atom TYPES) (ListE))
            (expfield (Atom TAGS) (ListE))
            (expfield (Atom GLOBALS) (ListE))
            (expfield (Atom MEMS) (ListE))
            (expfield (Atom TABLES) (ListE))
            (expfield (Atom FUNCS) (ListE))
            (expfield (Atom DATAS) (ListE))
            (expfield (Atom ELEMS) (ListE))
            (expfield (Atom LOCALS) (ListE))
            (expfield (Atom LABELS) (ListE))
            (expfield (Atom RETURN) (OptE))
            (expfield (Atom REFS) (ListE))
            (expfield (Atom RECS) (ListE))
          )
          (VarE "xt'")
          (VarE "xt")
        )
      )
    )
  )
)
HintD
(DecD
  "inst_valtype"
  (ExpP "moduleinst" (VarT "moduleinst"))
  (ExpP "valtype" (VarT "valtype"))
  (VarT "valtype")
  (DefD
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "t" (VarT "valtype"))
    (ExpA (VarE "moduleinst"))
    (ExpA (VarE "t"))
    (CallE
      "subst_all_valtype"
      (ExpA (VarE "t"))
      (ExpA
        (SubE
          (IterT (VarT "deftype") List)
          (IterT (VarT "typeuse") List)
          (DotE (VarE "moduleinst") (Atom TYPES))
        )
      )
    )
  )
)
HintD
(DecD
  "inst_reftype"
  (ExpP "moduleinst" (VarT "moduleinst"))
  (ExpP "reftype" (VarT "reftype"))
  (VarT "reftype")
  (DefD
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "rt" (VarT "reftype"))
    (ExpA (VarE "moduleinst"))
    (ExpA (VarE "rt"))
    (CallE
      "subst_all_reftype"
      (ExpA (VarE "rt"))
      (ExpA
        (SubE
          (IterT (VarT "deftype") List)
          (IterT (VarT "typeuse") List)
          (DotE (VarE "moduleinst") (Atom TYPES))
        )
      )
    )
  )
)
HintD
(DecD
  "inst_globaltype"
  (ExpP "moduleinst" (VarT "moduleinst"))
  (ExpP "globaltype" (VarT "globaltype"))
  (VarT "globaltype")
  (DefD
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "gt" (VarT "globaltype"))
    (ExpA (VarE "moduleinst"))
    (ExpA (VarE "gt"))
    (CallE
      "subst_all_globaltype"
      (ExpA (VarE "gt"))
      (ExpA
        (SubE
          (IterT (VarT "deftype") List)
          (IterT (VarT "typeuse") List)
          (DotE (VarE "moduleinst") (Atom TYPES))
        )
      )
    )
  )
)
HintD
(DecD
  "inst_memtype"
  (ExpP "moduleinst" (VarT "moduleinst"))
  (ExpP "memtype" (VarT "memtype"))
  (VarT "memtype")
  (DefD
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "mt" (VarT "memtype"))
    (ExpA (VarE "moduleinst"))
    (ExpA (VarE "mt"))
    (CallE
      "subst_all_memtype"
      (ExpA (VarE "mt"))
      (ExpA
        (SubE
          (IterT (VarT "deftype") List)
          (IterT (VarT "typeuse") List)
          (DotE (VarE "moduleinst") (Atom TYPES))
        )
      )
    )
  )
)
HintD
(DecD
  "inst_tabletype"
  (ExpP "moduleinst" (VarT "moduleinst"))
  (ExpP "tabletype" (VarT "tabletype"))
  (VarT "tabletype")
  (DefD
    (ExpP "moduleinst" (VarT "moduleinst"))
    (ExpP "tt" (VarT "tabletype"))
    (ExpA (VarE "moduleinst"))
    (ExpA (VarE "tt"))
    (CallE
      "subst_all_tabletype"
      (ExpA (VarE "tt"))
      (ExpA
        (SubE
          (IterT (VarT "deftype") List)
          (IterT (VarT "typeuse") List)
          (DotE (VarE "moduleinst") (Atom TYPES))
        )
      )
    )
  )
)
HintD

