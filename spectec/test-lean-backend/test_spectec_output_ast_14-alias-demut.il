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
  (RelD
    "fun_sum"
    (Seq Arg Arg)
    (TupT (typbind "_" (IterT nat List)) (typbind "_" nat))
    (RuleD "fun_sum_case_0" (Seq Arg Arg) (TupE (ListE) (NumE (Nat 0))))
    (RuleD
      "fun_sum_case_1"
      (ExpP "n" nat)
      (ExpP "n'*" (IterT (VarT "n") List))
      (ExpP "var_0" nat)
      (Seq Arg Arg)
      (TupE
        (CatE
          (ListE (VarE "n"))
          (IterE (VarE "n'#1") List (iterexp "n'#1" (VarE "n'*")))
        )
        (BinE AddOp nat (VarE "n") (VarE "var_0"))
      )
      (RulePr
        "fun_sum"
        (Seq Arg Arg)
        (TupE
          (IterE (VarE "n'") List (iterexp "n'" (VarE "n'*")))
          (VarE "var_0")
        )
      )
    )
  )
)
(DecD
  "opt_"
  (TypP "X")
  (ExpP "_" (IterT (VarT "X") List))
  (IterT (IterT (VarT "X") Opt) Opt)
  (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (OptE (OptE)))
  (DefD
    (TypP "X")
    (ExpP "w" (VarT "X"))
    (TypA (VarT "X"))
    (ExpA (ListE (VarE "w")))
    (OptE (OptE (VarE "w")))
  )
  (DefD
    (TypP "X")
    (ExpP "x1" (IterT (VarT "X") List))
    (TypA (VarT "X"))
    (ExpA (VarE "x1"))
    (OptE)
    ElsePr
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
          (ListE (IterE (VarE "w#1") List (iterexp "w#1" (VarE "w*"))))
          (IterE
            (IterE (VarE "w'#1") List (iterexp "w'#1" (VarE "w'*#1")))
            List
            (iterexp "w'*#1" (VarE "w'**"))
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
          (IterE (VarE "w'#2") List (iterexp "w'#2" (VarE "w'*")))
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
    (IfPr (CmpE EqOp bool (LenE (VarE "m*")) (LenE (VarE "n*"))))
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
(TypD "byte" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(RelD
  "wf_byte"
  (Seq Arg)
  (TupT (typbind "_" (VarT "byte")))
  (RuleD
    "byte_case_0"
    (ExpP "i" nat)
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "i"))))
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
HintD
HintD
(TypD "uN" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(RelD
  "wf_uN"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "uN")))
  (RuleD
    "uN_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "i" nat)
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE Arg (TupE (VarE "i"))))
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
HintD
HintD
(TypD "sN" (InstD (VariantT (typcase Arg (TupT (typbind "i" int))))))
(RelD
  "wf_sN"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "sN")))
  (RuleD
    "sN_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "i" int)
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE Arg (TupE (VarE "i"))))
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
HintD
HintD
(TypD "iN" (InstD (AliasT (VarT "uN"))))
HintD
(TypD "u31" (InstD (AliasT (VarT "uN"))))
(TypD "u32" (InstD (AliasT (VarT "uN"))))
(TypD "u64" (InstD (AliasT (VarT "uN"))))
(TypD "i32" (InstD (AliasT (VarT "iN"))))
(TypD "i64" (InstD (AliasT (VarT "iN"))))
(DecD
  "signif"
  (ExpP "N" (VarT "N"))
  (IterT nat Opt)
  (DefD (ExpA (NumE (Nat 32))) (OptE (NumE (Nat 23))))
  (DefD (ExpA (NumE (Nat 64))) (OptE (NumE (Nat 52))))
  (DefD (ExpP "x0" (VarT "N")) (ExpA (VarE "x0")) (OptE) ElsePr)
)
HintD
(DecD
  "expon"
  (ExpP "N" (VarT "N"))
  (IterT nat Opt)
  (DefD (ExpA (NumE (Nat 32))) (OptE (NumE (Nat 8))))
  (DefD (ExpA (NumE (Nat 64))) (OptE (NumE (Nat 11))))
  (DefD (ExpP "x0" (VarT "N")) (ExpA (VarE "x0")) (OptE) ElsePr)
)
HintD
(DecD
  "M"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (TheE (CallE "signif" (ExpA (VarE "N"))))
  )
)
HintD
(DecD
  "E"
  (ExpP "N" (VarT "N"))
  nat
  (DefD
    (ExpP "N" nat)
    (ExpA (VarE "N"))
    (TheE (CallE "expon" (ExpA (VarE "N"))))
  )
)
HintD
(TypD "exp" (InstD (AliasT int)))
(TypD
  "fNmag"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom NORM) Arg Arg)
        (TupT (typbind "m" (VarT "m")) (typbind "exp" (VarT "exp")))
      )
      (typcase
        (Seq (Atom SUBNORM) Arg)
        (TupT (typbind "m" (VarT "m")))
        (ExpP "exp" (VarT "exp"))
      )
      (typcase (Atom INF) (TupT))
      (typcase (Seq (Atom NAN) Arg) (TupT (typbind "m" (VarT "m"))))
    )
  )
)
(RelD
  "wf_fNmag"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fNmag")))
  (RuleD
    "fNmag_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "m" (VarT "m"))
    (ExpP "exp" (VarT "exp"))
    (Seq Arg Arg)
    (TupE
      (VarE "N")
      (CaseE (Seq (Atom NORM) Arg Arg) (TupE (VarE "m") (VarE "exp")))
    )
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
  (RuleD
    "fNmag_case_1"
    (ExpP "N" (VarT "N"))
    (ExpP "exp" (VarT "exp"))
    (ExpP "m" (VarT "m"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom SUBNORM) Arg) (TupE (VarE "m"))))
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
  (RuleD
    "fNmag_case_2"
    (ExpP "N" (VarT "N"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Atom INF) (TupE)))
  )
  (RuleD
    "fNmag_case_3"
    (ExpP "N" (VarT "N"))
    (ExpP "m" (VarT "m"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom NAN) Arg) (TupE (VarE "m"))))
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
HintD
(TypD
  "fN"
  (InstD
    (VariantT
      (typcase (Seq (Atom POS) Arg) (TupT (typbind "_" (VarT "fNmag"))))
      (typcase (Seq (Atom NEG) Arg) (TupT (typbind "_" (VarT "fNmag"))))
    )
  )
)
(RelD
  "wf_fN"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "N")) (typbind "_" (VarT "fN")))
  (RuleD
    "fN_case_0"
    (ExpP "N" (VarT "N"))
    (ExpP "var_0" (VarT "fNmag"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom POS) Arg) (TupE (VarE "var_0"))))
    (RulePr "wf_fNmag" (Seq Arg Arg) (TupE (VarE "N") (VarE "var_0")))
  )
  (RuleD
    "fN_case_1"
    (ExpP "N" (VarT "N"))
    (ExpP "var_0" (VarT "fNmag"))
    (Seq Arg Arg)
    (TupE (VarE "N") (CaseE (Seq (Atom NEG) Arg) (TupE (VarE "var_0"))))
    (RulePr "wf_fNmag" (Seq Arg Arg) (TupE (VarE "N") (VarE "var_0")))
  )
)
HintD
HintD
HintD
HintD
(TypD "f32" (InstD (AliasT (VarT "fN"))))
(TypD "f64" (InstD (AliasT (VarT "fN"))))
(DecD
  "fzero"
  (ExpP "N" (VarT "N"))
  (VarT "fN")
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
(RelD
  "fzero_is_wf"
  (Seq Arg Arg)
  (TupT (typbind "N" (VarT "N")) (typbind "ret_val" (VarT "fN")))
  (RuleD
    "fzero_is_wf_0"
    (ExpP "N" (VarT "N"))
    (ExpP "ret_val" (VarT "fN"))
    (Seq Arg Arg)
    (TupE (VarE "N") (VarE "ret_val"))
    (IfPr (CmpE EqOp bool (VarE "ret_val") (CallE "fzero" (ExpA (VarE "N")))))
    (RulePr "wf_fN" (Seq Arg Arg) (TupE (VarE "N") (VarE "ret_val")))
  )
)
HintD
(DecD
  "fone"
  (ExpP "N" (VarT "N"))
  (VarT "fN")
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
(RelD
  "fone_is_wf"
  (Seq Arg Arg)
  (TupT (typbind "N" (VarT "N")) (typbind "ret_val" (VarT "fN")))
  (RuleD
    "fone_is_wf_0"
    (ExpP "N" (VarT "N"))
    (ExpP "ret_val" (VarT "fN"))
    (Seq Arg Arg)
    (TupE (VarE "N") (VarE "ret_val"))
    (IfPr (CmpE EqOp bool (VarE "ret_val") (CallE "fone" (ExpA (VarE "N")))))
    (RulePr "wf_fN" (Seq Arg Arg) (TupE (VarE "N") (VarE "ret_val")))
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
          (CvtE nat int (TheE (CallE "signif" (ExpA (VarE "N")))))
          (CvtE nat int (NumE (Nat 1)))
        )
      )
    )
  )
)
(TypD "char" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(RelD
  "wf_char"
  (Seq Arg)
  (TupT (typbind "_" (VarT "char")))
  (RuleD
    "char_case_0"
    (ExpP "i" nat)
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "i"))))
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
HintD
HintD
(DecD "utf8" (ExpP "_" (IterT (VarT "char") List)) (IterT (VarT "byte") List))
HintD
(RelD
  "utf8_is_wf"
  (Seq Arg Arg)
  (TupT
    (typbind "var_0*" (IterT (VarT "char") List))
    (typbind "ret_val*" (IterT (VarT "byte") List))
  )
  (RuleD
    "utf8_is_wf_0"
    (ExpP "var_0*" (IterT (VarT "char") List))
    (ExpP "ret_val*" (IterT (VarT "byte") List))
    (Seq Arg Arg)
    (TupE (VarE "var_0*") (VarE "ret_val*"))
    (IterPr
      (RulePr "wf_char" (Seq Arg) (TupE (VarE "var_0")))
      List
      (iterexp "var_0" (VarE "var_0*"))
    )
    (IfPr
      (CmpE EqOp bool (VarE "ret_val*") (CallE "utf8" (ExpA (VarE "var_0*"))))
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "ret_val")))
      List
      (iterexp "ret_val" (VarE "ret_val*"))
    )
  )
)
(TypD
  "name"
  (InstD
    (VariantT (typcase Arg (TupT (typbind "char*" (IterT (VarT "char") List)))))
  )
)
(RelD
  "wf_name"
  (Seq Arg)
  (TupT (typbind "_" (VarT "name")))
  (RuleD
    "name_case_0"
    (ExpP "char*" (IterT (VarT "char") List))
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "char*"))))
    (IterPr
      (RulePr "wf_char" (Seq Arg) (TupE (VarE "char")))
      List
      (iterexp "char" (VarE "char*"))
    )
    (IfPr
      (CmpE
        LtOp
        nat
        (LenE
          (CallE
            "utf8"
            (ExpA (IterE (VarE "char") List (iterexp "char" (VarE "char*"))))
          )
        )
        (BinE PowOp nat (NumE (Nat 2)) (NumE (Nat 32)))
      )
    )
  )
)
HintD
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
(DecD
  "valtype_Inn"
  (ExpP "_" (VarT "Inn"))
  (VarT "valtype")
  (DefD (ExpA (CaseE (Atom I32) (TupE))) (CaseE (Atom I32) (TupE)))
  (DefD (ExpA (CaseE (Atom I64) (TupE))) (CaseE (Atom I64) (TupE)))
)
HintD
(TypD
  "Fnn"
  (InstD (VariantT (typcase (Atom F32) (TupT)) (typcase (Atom F64) (TupT))))
)
(DecD
  "valtype_Fnn"
  (ExpP "_" (VarT "Fnn"))
  (VarT "valtype")
  (DefD (ExpA (CaseE (Atom F32) (TupE))) (CaseE (Atom F32) (TupE)))
  (DefD (ExpA (CaseE (Atom F64) (TupE))) (CaseE (Atom F64) (TupE)))
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
(RelD
  "wf_limits"
  (Seq Arg)
  (TupT (typbind "_" (VarT "limits")))
  (RuleD
    "limits_case_0"
    (ExpP "u32" (VarT "u32"))
    (ExpP "u32?" (IterT (VarT "u32") Opt))
    (Seq Arg)
    (TupE
      (CaseE (Brack [ (Infix Arg .. Arg) ]) (TupE (VarE "u32") (VarE "u32?")))
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "u32")))
  )
)
HintD
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
(RelD
  "wf_externtype"
  (Seq Arg)
  (TupT (typbind "_" (VarT "externtype")))
  (RuleD
    "externtype_case_0"
    (ExpP "functype" (VarT "functype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "functype"))))
  )
  (RuleD
    "externtype_case_1"
    (ExpP "globaltype" (VarT "globaltype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globaltype"))))
  )
  (RuleD
    "externtype_case_2"
    (ExpP "tabletype" (VarT "tabletype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "tabletype")))
  )
  (RuleD
    "externtype_case_3"
    (ExpP "memtype" (VarT "memtype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memtype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "memtype")))
  )
)
HintD
HintD
(DecD "size" (ExpP "valtype" (VarT "valtype")) nat)
HintD
(TypD
  "val_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_val__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "iN")))
      )
      (typcase
        (Seq (Atom mk_val__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "fN")))
      )
    )
  )
)
(RelD
  "wf_val_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "val_")))
  (RuleD
    "val__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "iN"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_val__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (RulePr
      "wf_uN"
      (Seq Arg Arg)
      (TupE
        (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
        (VarE "var_x")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "val__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "fN"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_val__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (RulePr
      "wf_fN"
      (Seq Arg Arg)
      (TupE
        (CallE "size" (ExpA (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))))
        (VarE "var_x")
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
HintD
(DecD
  "proj_val__0"
  (ExpP "var_x" (VarT "val_"))
  (IterT (VarT "iN") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "iN"))
    (ExpA
      (CaseE (Seq (Atom mk_val__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "val_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_val__1"
  (ExpP "var_x" (VarT "val_"))
  (IterT (VarT "fN") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "fN"))
    (ExpA
      (CaseE (Seq (Atom mk_val__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "val_")) (ExpA (VarE "var_x")) (OptE))
)
HintD
HintD
HintD
(TypD
  "sx"
  (InstD (VariantT (typcase (Atom U) (TupT)) (typcase (Atom S) (TupT))))
)
HintD
(TypD "sz" (InstD (VariantT (typcase Arg (TupT (typbind "i" nat))))))
(DecD
  "proj_sz_0"
  (ExpP "x" (VarT "sz"))
  (TupT (typbind "_" nat))
  (DefD
    (ExpP "v_num_0" nat)
    (ExpA (CaseE Arg (TupE (VarE "v_num_0"))))
    (TupE (VarE "v_num_0"))
  )
)
HintD
(RelD
  "wf_sz"
  (Seq Arg)
  (TupT (typbind "_" (VarT "sz")))
  (RuleD
    "sz_case_0"
    (ExpP "i" nat)
    (Seq Arg)
    (TupE (CaseE Arg (TupE (VarE "i"))))
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
HintD
HintD
(TypD
  "unop_Inn"
  (InstD
    (VariantT
      (typcase (Atom CLZ) (TupT))
      (typcase (Atom CTZ) (TupT))
      (typcase (Atom POPCNT) (TupT))
    )
  )
)
(TypD
  "unop_Fnn"
  (InstD
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
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_unop__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "unop_Inn")))
      )
      (typcase
        (Seq (Atom mk_unop__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "unop_Fnn")))
      )
    )
  )
)
(RelD
  "wf_unop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "unop_")))
  (RuleD
    "unop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_unop__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "unop__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE (Seq (Atom mk_unop__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
HintD
(DecD
  "proj_unop__0"
  (ExpP "var_x" (VarT "unop_"))
  (IterT (VarT "unop_Inn") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "unop_Inn"))
    (ExpA
      (CaseE (Seq (Atom mk_unop__0) Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "unop_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_unop__1"
  (ExpP "var_x" (VarT "unop_"))
  (IterT (VarT "unop_Fnn") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "unop_Fnn"))
    (ExpA
      (CaseE (Seq (Atom mk_unop__1) Arg Arg) (TupE (VarE "Fnn") (VarE "var_x")))
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "unop_")) (ExpA (VarE "var_x")) (OptE))
)
HintD
HintD
HintD
(TypD
  "binop_Inn"
  (InstD
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
  (InstD
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
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "binop_Inn")))
      )
      (typcase
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "binop_Fnn")))
      )
    )
  )
)
(RelD
  "wf_binop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "binop_")))
  (RuleD
    "binop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "binop__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
HintD
(DecD
  "proj_binop__0"
  (ExpP "var_x" (VarT "binop_"))
  (IterT (VarT "binop_Inn") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "binop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "binop_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_binop__1"
  (ExpP "var_x" (VarT "binop_"))
  (IterT (VarT "binop_Fnn") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "binop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_binop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "binop_")) (ExpA (VarE "var_x")) (OptE))
)
HintD
HintD
HintD
(TypD "testop_Inn" (InstD (VariantT (typcase (Atom EQZ) (TupT)))))
(TypD
  "testop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "testop_Inn"))
        )
      )
    )
  )
)
(RelD
  "wf_testop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "testop_")))
  (RuleD
    "testop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_testop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
)
HintD
(DecD
  "proj_testop__0"
  (ExpP "var_x" (VarT "testop_"))
  (VarT "testop_Inn")
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "testop_Inn"))
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
  (InstD
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
  (InstD
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
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupT (typbind "Inn" (VarT "Inn")) (typbind "var_x" (VarT "relop_Inn")))
      )
      (typcase
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupT (typbind "Fnn" (VarT "Fnn")) (typbind "var_x" (VarT "relop_Fnn")))
      )
    )
  )
)
(RelD
  "wf_relop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "relop_")))
  (RuleD
    "relop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
  (RuleD
    "relop__case_1"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Fnn" (ExpA (VarE "Fnn")))
      )
    )
  )
)
HintD
(DecD
  "proj_relop__0"
  (ExpP "var_x" (VarT "relop_"))
  (IterT (VarT "relop_Inn") Opt)
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "relop_Inn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "relop_")) (ExpA (VarE "var_x")) (OptE))
)
(DecD
  "proj_relop__1"
  (ExpP "var_x" (VarT "relop_"))
  (IterT (VarT "relop_Fnn") Opt)
  (DefD
    (ExpP "Fnn" (VarT "Fnn"))
    (ExpP "var_x" (VarT "relop_Fnn"))
    (ExpA
      (CaseE
        (Seq (Atom mk_relop__1) Arg Arg)
        (TupE (VarE "Fnn") (VarE "var_x"))
      )
    )
    (OptE (VarE "var_x"))
  )
  (DefD (ExpP "var_x" (VarT "relop_")) (ExpA (VarE "var_x")) (OptE))
)
HintD
HintD
HintD
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
(RelD
  "wf_memarg"
  (Seq Arg)
  (TupT (typbind "_" (VarT "memarg")))
  (RuleD
    "memarg_case_"
    (ExpP "var_0" (VarT "u32"))
    (ExpP "var_1" (VarT "u32"))
    (Seq Arg)
    (TupE
      (StrE
        (expfield (Atom ALIGN) (VarE "var_0"))
        (expfield (Atom OFFSET) (VarE "var_1"))
      )
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "var_0")))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "var_1")))
  )
)
HintD
HintD
(TypD
  "loadop_Inn"
  (InstD
    (VariantT
      (typcase
        (Seq Arg (Atom _) Arg)
        (TupT (typbind "sz" (VarT "sz")) (typbind "sx" (VarT "sx")))
      )
    )
  )
)
(RelD
  "wf_loadop_Inn"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "Inn")) (typbind "_" (VarT "loadop_Inn")))
  (RuleD
    "loadop_Inn_case_0"
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "sz" (VarT "sz"))
    (ExpP "sx" (VarT "sx"))
    (Seq Arg Arg)
    (TupE
      (VarE "Inn")
      (CaseE (Seq Arg (Atom _) Arg) (TupE (VarE "sz") (VarE "sx")))
    )
    (RulePr "wf_sz" (Seq Arg) (TupE (VarE "sz")))
    (IfPr
      (CmpE
        LtOp
        nat
        (ProjE (CallE "proj_sz_0" (ExpA (VarE "sz"))) 0)
        (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
      )
    )
  )
)
HintD
(TypD
  "loadop_"
  (InstD
    (VariantT
      (typcase
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupT
          (typbind "Inn" (VarT "Inn"))
          (typbind "var_x" (VarT "loadop_Inn"))
        )
      )
    )
  )
)
(RelD
  "wf_loadop_"
  (Seq Arg Arg)
  (TupT (typbind "_" (VarT "valtype")) (typbind "_" (VarT "loadop_")))
  (RuleD
    "loadop__case_0"
    (ExpP "valtype" (VarT "valtype"))
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn"))
    (Seq Arg Arg)
    (TupE
      (VarE "valtype")
      (CaseE
        (Seq (Atom mk_loadop__0) Arg Arg)
        (TupE (VarE "Inn") (VarE "var_x"))
      )
    )
    (RulePr "wf_loadop_Inn" (Seq Arg Arg) (TupE (VarE "Inn") (VarE "var_x")))
    (IfPr
      (CmpE
        EqOp
        bool
        (VarE "valtype")
        (CallE "valtype_Inn" (ExpA (VarE "Inn")))
      )
    )
  )
)
HintD
(DecD
  "proj_loadop__0"
  (ExpP "var_x" (VarT "loadop_"))
  (VarT "loadop_Inn")
  (DefD
    (ExpP "Inn" (VarT "Inn"))
    (ExpP "var_x" (VarT "loadop_Inn"))
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
            (typbind "_" (VarT "val_"))
          )
        )
        (typcase
          (Seq (Atom UNOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "unop_"))
          )
        )
        (typcase
          (Seq (Atom BINOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "binop_"))
          )
        )
        (typcase
          (Seq (Atom TESTOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "testop_"))
          )
        )
        (typcase
          (Seq (Atom RELOP) Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (VarT "relop_"))
          )
        )
        (typcase
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupT
            (typbind "valtype_1" (VarT "valtype"))
            (typbind "valtype_2" (VarT "valtype"))
            (typbind "cvtop" (VarT "cvtop"))
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
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupT
            (typbind "valtype" (VarT "valtype"))
            (typbind "_" (IterT (VarT "loadop_") Opt))
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
        )
        (typcase (Atom MEMORY.SIZE) (TupT))
        (typcase (Atom MEMORY.GROW) (TupT))
      )
    )
  )
)
(RecD
  (RelD
    "wf_instr"
    (Seq Arg)
    (TupT (typbind "_" (VarT "instr")))
    (RuleD "instr_case_0" (Seq Arg) (TupE (CaseE (Atom NOP) (TupE))))
    (RuleD "instr_case_1" (Seq Arg) (TupE (CaseE (Atom UNREACHABLE) (TupE))))
    (RuleD "instr_case_2" (Seq Arg) (TupE (CaseE (Atom DROP) (TupE))))
    (RuleD "instr_case_3" (Seq Arg) (TupE (CaseE (Atom SELECT) (TupE))))
    (RuleD
      "instr_case_4"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BLOCK) Arg Arg)
          (TupE (VarE "blocktype") (VarE "instr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
    (RuleD
      "instr_case_5"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOOP) Arg Arg)
          (TupE (VarE "blocktype") (VarE "instr*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
    )
    (RuleD
      "instr_case_6"
      (ExpP "blocktype" (VarT "blocktype"))
      (ExpP "instr*" (IterT (VarT "instr") List))
      (ExpP "instr*_0*" (IterT (VarT "instr") List))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom IF) Arg Arg (Atom ELSE) Arg)
          (TupE (VarE "blocktype") (VarE "instr*") (VarE "instr*_0*"))
        )
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr")))
        List
        (iterexp "instr" (VarE "instr*"))
      )
      (IterPr
        (RulePr "wf_instr" (Seq Arg) (TupE (VarE "instr*_0")))
        List
        (iterexp "instr*_0" (VarE "instr*_0*"))
      )
    )
    (RuleD
      "instr_case_7"
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR) Arg) (TupE (VarE "labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "instr_case_8"
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom BR_IF) Arg) (TupE (VarE "labelidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "instr_case_9"
      (ExpP "labelidx*" (IterT (VarT "labelidx") List))
      (ExpP "labelidx" (VarT "labelidx"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BR_TABLE) Arg Arg)
          (TupE (VarE "labelidx*") (VarE "labelidx"))
        )
      )
      (IterPr
        (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
        List
        (iterexp "labelidx" (VarE "labelidx*"))
      )
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "labelidx")))
    )
    (RuleD
      "instr_case_10"
      (ExpP "funcidx" (VarT "funcidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL) Arg) (TupE (VarE "funcidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
    )
    (RuleD
      "instr_case_11"
      (ExpP "typeidx" (VarT "typeidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom CALL_INDIRECT) Arg) (TupE (VarE "typeidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "typeidx")))
    )
    (RuleD "instr_case_12" (Seq Arg) (TupE (CaseE (Atom RETURN) (TupE))))
    (RuleD
      "instr_case_13"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "val_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CONST) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_val_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_14"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "unop_"))
      (Seq Arg)
      (TupE
        (CaseE (Seq (Atom UNOP) Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
      )
      (RulePr "wf_unop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_15"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "binop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom BINOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_binop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_16"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "testop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom TESTOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_testop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_17"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0" (VarT "relop_"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom RELOP) Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
      )
      (RulePr "wf_relop_" (Seq Arg Arg) (TupE (VarE "valtype") (VarE "var_0")))
    )
    (RuleD
      "instr_case_18"
      (ExpP "valtype_1" (VarT "valtype"))
      (ExpP "valtype_2" (VarT "valtype"))
      (ExpP "cvtop" (VarT "cvtop"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom CVTOP) Arg Arg Arg)
          (TupE (VarE "valtype_1") (VarE "valtype_2") (VarE "cvtop"))
        )
      )
      (IfPr (CmpE NeOp bool (VarE "valtype_1") (VarE "valtype_2")))
    )
    (RuleD
      "instr_case_19"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.GET) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "instr_case_20"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.SET) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "instr_case_21"
      (ExpP "localidx" (VarT "localidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom LOCAL.TEE) Arg) (TupE (VarE "localidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "localidx")))
    )
    (RuleD
      "instr_case_22"
      (ExpP "globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.GET) Arg) (TupE (VarE "globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
    )
    (RuleD
      "instr_case_23"
      (ExpP "globalidx" (VarT "globalidx"))
      (Seq Arg)
      (TupE (CaseE (Seq (Atom GLOBAL.SET) Arg) (TupE (VarE "globalidx"))))
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
    )
    (RuleD
      "instr_case_24"
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "var_0?" (IterT (VarT "loadop_") Opt))
      (ExpP "memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom LOAD) Arg Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0?") (VarE "memarg"))
        )
      )
      (IterPr
        (RulePr
          "wf_loadop_"
          (Seq Arg Arg)
          (TupE (VarE "valtype") (VarE "var_0"))
        )
        Opt
        (iterexp "var_0" (VarE "var_0?"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "memarg")))
    )
    (RuleD
      "instr_case_25"
      (ExpP "Inn?" (IterT (VarT "Inn") Opt))
      (ExpP "valtype?" (IterT (VarT "valtype") Opt))
      (ExpP "valtype" (VarT "valtype"))
      (ExpP "sz?" (IterT (VarT "sz") Opt))
      (ExpP "memarg" (VarT "memarg"))
      (Seq Arg)
      (TupE
        (CaseE
          (Seq (Atom STORE) Arg Arg Arg)
          (TupE (VarE "valtype") (VarE "sz?") (VarE "memarg"))
        )
      )
      (IterPr
        (RulePr "wf_sz" (Seq Arg) (TupE (VarE "sz")))
        Opt
        (iterexp "sz" (VarE "sz?"))
      )
      (RulePr "wf_memarg" (Seq Arg) (TupE (VarE "memarg")))
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE EqOp bool (VarE "Inn?") (OptE))
          (CmpE EqOp bool (VarE "sz?") (OptE))
        )
      )
      (IfPr
        (BinE
          EquivOp
          bool
          (CmpE EqOp bool (VarE "Inn?") (OptE))
          (CmpE EqOp bool (VarE "valtype?") (OptE))
        )
      )
      (IterPr
        (IfPr
          (BinE
            AndOp
            bool
            (CmpE
              EqOp
              bool
              (VarE "valtype")
              (CallE "valtype_Inn" (ExpA (VarE "Inn")))
            )
            (CmpE
              LtOp
              nat
              (ProjE (CallE "proj_sz_0" (ExpA (VarE "sz"))) 0)
              (CallE "size" (ExpA (CallE "valtype_Inn" (ExpA (VarE "Inn")))))
            )
          )
        )
        Opt
        (iterexp "Inn" (VarE "Inn?"))
        (iterexp "sz" (VarE "sz?"))
        (iterexp "valtype" (VarE "valtype?"))
      )
    )
    (RuleD "instr_case_26" (Seq Arg) (TupE (CaseE (Atom MEMORY.SIZE) (TupE))))
    (RuleD "instr_case_27" (Seq Arg) (TupE (CaseE (Atom MEMORY.GROW) (TupE))))
  )
  HintD
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
(RelD
  "wf_func"
  (Seq Arg)
  (TupT (typbind "_" (VarT "func")))
  (RuleD
    "func_case_0"
    (ExpP "typeidx" (VarT "typeidx"))
    (ExpP "local*" (IterT (VarT "local") List))
    (ExpP "expr" (VarT "expr"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom FUNC) Arg Arg Arg)
        (TupE (VarE "typeidx") (VarE "local*") (VarE "expr"))
      )
    )
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "typeidx")))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
  )
)
HintD
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
(RelD
  "wf_global"
  (Seq Arg)
  (TupT (typbind "_" (VarT "global")))
  (RuleD
    "global_case_0"
    (ExpP "globaltype" (VarT "globaltype"))
    (ExpP "expr" (VarT "expr"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom GLOBAL) Arg Arg)
        (TupE (VarE "globaltype") (VarE "expr"))
      )
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
  )
)
HintD
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
(RelD
  "wf_table"
  (Seq Arg)
  (TupT (typbind "_" (VarT "table")))
  (RuleD
    "table_case_0"
    (ExpP "tabletype" (VarT "tabletype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tabletype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "tabletype")))
  )
)
HintD
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
(RelD
  "wf_mem"
  (Seq Arg)
  (TupT (typbind "_" (VarT "mem")))
  (RuleD
    "mem_case_0"
    (ExpP "memtype" (VarT "memtype"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEMORY) Arg) (TupE (VarE "memtype"))))
    (RulePr "wf_limits" (Seq Arg) (TupE (VarE "memtype")))
  )
)
HintD
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
(RelD
  "wf_elem"
  (Seq Arg)
  (TupT (typbind "_" (VarT "elem")))
  (RuleD
    "elem_case_0"
    (ExpP "expr" (VarT "expr"))
    (ExpP "funcidx*" (IterT (VarT "funcidx") List))
    (Seq Arg)
    (TupE
      (CaseE (Seq (Atom ELEM) Arg Arg) (TupE (VarE "expr") (VarE "funcidx*")))
    )
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
    (IterPr
      (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
      List
      (iterexp "funcidx" (VarE "funcidx*"))
    )
  )
)
HintD
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
(RelD
  "wf_data"
  (Seq Arg)
  (TupT (typbind "_" (VarT "data")))
  (RuleD
    "data_case_0"
    (ExpP "expr" (VarT "expr"))
    (ExpP "byte*" (IterT (VarT "byte") List))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom DATA) Arg Arg) (TupE (VarE "expr") (VarE "byte*"))))
    (IterPr
      (RulePr "wf_instr" (Seq Arg) (TupE (VarE "expr")))
      List
      (iterexp "expr" (VarE "expr"))
    )
    (IterPr
      (RulePr "wf_byte" (Seq Arg) (TupE (VarE "byte")))
      List
      (iterexp "byte" (VarE "byte*"))
    )
  )
)
HintD
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
(RelD
  "wf_start"
  (Seq Arg)
  (TupT (typbind "_" (VarT "start")))
  (RuleD
    "start_case_0"
    (ExpP "funcidx" (VarT "funcidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom START) Arg) (TupE (VarE "funcidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
  )
)
HintD
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
(RelD
  "wf_externidx"
  (Seq Arg)
  (TupT (typbind "_" (VarT "externidx")))
  (RuleD
    "externidx_case_0"
    (ExpP "funcidx" (VarT "funcidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom FUNC) Arg) (TupE (VarE "funcidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "funcidx")))
  )
  (RuleD
    "externidx_case_1"
    (ExpP "globalidx" (VarT "globalidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom GLOBAL) Arg) (TupE (VarE "globalidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "globalidx")))
  )
  (RuleD
    "externidx_case_2"
    (ExpP "tableidx" (VarT "tableidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom TABLE) Arg) (TupE (VarE "tableidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "tableidx")))
  )
  (RuleD
    "externidx_case_3"
    (ExpP "memidx" (VarT "memidx"))
    (Seq Arg)
    (TupE (CaseE (Seq (Atom MEM) Arg) (TupE (VarE "memidx"))))
    (RulePr "wf_uN" (Seq Arg Arg) (TupE (NumE (Nat 32)) (VarE "memidx")))
  )
)
HintD
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
(RelD
  "wf_export"
  (Seq Arg)
  (TupT (typbind "_" (VarT "export")))
  (RuleD
    "export_case_0"
    (ExpP "name" (VarT "name"))
    (ExpP "externidx" (VarT "externidx"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom EXPORT) Arg Arg)
        (TupE (VarE "name") (VarE "externidx"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name")))
    (RulePr "wf_externidx" (Seq Arg) (TupE (VarE "externidx")))
  )
)
HintD
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
(RelD
  "wf_import"
  (Seq Arg)
  (TupT (typbind "_" (VarT "import")))
  (RuleD
    "import_case_0"
    (ExpP "name" (VarT "name"))
    (ExpP "name_0" (VarT "name"))
    (ExpP "externtype" (VarT "externtype"))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom IMPORT) Arg Arg Arg)
        (TupE (VarE "name") (VarE "name_0") (VarE "externtype"))
      )
    )
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name")))
    (RulePr "wf_name" (Seq Arg) (TupE (VarE "name_0")))
    (RulePr "wf_externtype" (Seq Arg) (TupE (VarE "externtype")))
  )
)
HintD
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
(RelD
  "wf_module"
  (Seq Arg)
  (TupT (typbind "_" (VarT "module")))
  (RuleD
    "module_case_0"
    (ExpP "type*" (IterT (VarT "type") List))
    (ExpP "import*" (IterT (VarT "import") List))
    (ExpP "func*" (IterT (VarT "func") List))
    (ExpP "global*" (IterT (VarT "global") List))
    (ExpP "table*" (IterT (VarT "table") List))
    (ExpP "mem*" (IterT (VarT "mem") List))
    (ExpP "elem*" (IterT (VarT "elem") List))
    (ExpP "data*" (IterT (VarT "data") List))
    (ExpP "start?" (IterT (VarT "start") Opt))
    (ExpP "export*" (IterT (VarT "export") List))
    (Seq Arg)
    (TupE
      (CaseE
        (Seq (Atom MODULE) Arg Arg Arg Arg Arg Arg Arg Arg Arg Arg)
        (TupE
          (VarE "type*")
          (VarE "import*")
          (VarE "func*")
          (VarE "global*")
          (VarE "table*")
          (VarE "mem*")
          (VarE "elem*")
          (VarE "data*")
          (VarE "start?")
          (VarE "export*")
        )
      )
    )
    (IterPr
      (RulePr "wf_import" (Seq Arg) (TupE (VarE "import")))
      List
      (iterexp "import" (VarE "import*"))
    )
    (IterPr
      (RulePr "wf_func" (Seq Arg) (TupE (VarE "func")))
      List
      (iterexp "func" (VarE "func*"))
    )
    (IterPr
      (RulePr "wf_global" (Seq Arg) (TupE (VarE "global")))
      List
      (iterexp "global" (VarE "global*"))
    )
    (IterPr
      (RulePr "wf_table" (Seq Arg) (TupE (VarE "table")))
      List
      (iterexp "table" (VarE "table*"))
    )
    (IterPr
      (RulePr "wf_mem" (Seq Arg) (TupE (VarE "mem")))
      List
      (iterexp "mem" (VarE "mem*"))
    )
    (IterPr
      (RulePr "wf_elem" (Seq Arg) (TupE (VarE "elem")))
      List
      (iterexp "elem" (VarE "elem*"))
    )
    (IterPr
      (RulePr "wf_data" (Seq Arg) (TupE (VarE "data")))
      List
      (iterexp "data" (VarE "data*"))
    )
    (IterPr
      (RulePr "wf_start" (Seq Arg) (TupE (VarE "start")))
      Opt
      (iterexp "start" (VarE "start?"))
    )
    (IterPr
      (RulePr "wf_export" (Seq Arg) (TupE (VarE "export")))
      List
      (iterexp "export" (VarE "export*"))
    )
  )
)
HintD
HintD

