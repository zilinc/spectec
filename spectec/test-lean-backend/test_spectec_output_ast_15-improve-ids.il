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
  (ExpP "nat_0" nat)
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
      (ExpP "v_n" nat)
      (ExpP "n'_lst" (IterT (VarT "n") List))
      (ExpP "var_0" nat)
      (Seq Arg Arg)
      (TupE
        (CatE (ListE (VarE "v_n")) (VarE "n'_lst"))
        (BinE AddOp nat (VarE "v_n") (VarE "var_0"))
      )
      (RulePr "fun_sum" (Seq Arg Arg) (TupE (VarE "n'_lst") (VarE "var_0")))
    )
  )
)
(DecD
  "opt_"
  (TypP "X")
  (ExpP "var_0_lst" (IterT (VarT "X") List))
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
  (ExpP "var_0_opt" (IterT (VarT "X") Opt))
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
    (ExpP "var_0_lst_lst" (IterT (IterT (VarT "X") List) List))
    (IterT (VarT "X") List)
    (DefD (TypP "X") (TypA (VarT "X")) (ExpA (ListE)) (ListE))
    (DefD
      (TypP "X")
      (ExpP "w_lst" (IterT (VarT "X") List))
      (ExpP "w'_lst_lst" (IterT (IterT (VarT "X") List) List))
      (TypA (VarT "X"))
      (ExpA (CatE (ListE (VarE "w_lst")) (VarE "w'_lst_lst")))
      (CatE
        (VarE "w_lst")
        (CallE "concat_" (TypA (VarT "X")) (ExpA (VarE "w'_lst_lst")))
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
    (ExpP "v_n" (VarT "n"))
    (Infix Arg |- Arg)
    (TupE (VarE "v_n") (VarE "v_n"))
  )
)
(RelD
  "Nats_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" (IterT nat List)) (typbind "_" (IterT nat List)))
  (RuleD
    "all"
    (ExpP "n_lst" (IterT (VarT "n") List))
    (Infix Arg |- Arg)
    (TupE (VarE "n_lst") (VarE "n_lst"))
    (IterPr
      (RulePr "Nat_ok" (Infix Arg |- Arg) (TupE (VarE "v_n") (VarE "v_n")))
      List
      (iterexp "v_n" (VarE "n_lst"))
    )
  )
)
(RelD
  "Pair_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" nat) (typbind "_" nat))
  (RuleD
    "eq"
    (ExpP "v_n" (VarT "n"))
    (Infix Arg |- Arg)
    (TupE (VarE "v_n") (VarE "v_n"))
  )
)
(RelD
  "Pairs_ok"
  (Infix Arg |- Arg)
  (TupT (typbind "_" (IterT nat List)) (typbind "_" (IterT nat List)))
  (RuleD
    "all"
    (ExpP "n_lst" (IterT (VarT "n") List))
    (ExpP "m_lst" (IterT (VarT "m") List))
    (Infix Arg |- Arg)
    (TupE (VarE "n_lst") (VarE "m_lst"))
    (IfPr (CmpE EqOp bool (LenE (VarE "m_lst")) (LenE (VarE "n_lst"))))
    (IterPr
      (RulePr "Pair_ok" (Infix Arg |- Arg) (TupE (VarE "v_n") (VarE "v_m")))
      List
      (iterexp "v_m" (VarE "m_lst"))
      (iterexp "v_n" (VarE "n_lst"))
    )
  )
)

