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

