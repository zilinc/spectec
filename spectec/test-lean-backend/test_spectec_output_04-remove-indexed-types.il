
;; test.spectec:5.1-5.32
syntax N = fuck3nat

;; test.spectec:6.1-6.32
syntax M = fuck3nat

;; test.spectec:7.1-7.32
syntax K = fuck3nat

;; test.spectec:8.1-8.32
syntax n = fuck3nat

;; test.spectec:9.1-9.32
syntax m = fuck3nat

;; test.spectec:22.1-22.25
def $min(nat : fuck3nat, nat : fuck3nat) : fuck3nat
  ;; test.spectec:23.1-23.36
  def $min{i : fuck3nat, j : fuck3nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:26.1-26.56
rec {

;; test.spectec:26.1-26.56
def $sum(fuck6fuck3nat*) : fuck3nat
  ;; test.spectec:27.1-27.18
  def $sum([]) = 0
  ;; test.spectec:28.1-28.35
  def $sum{n : fuck3nat, `n'*` : fuck6fuck1n*}([n] ++ n'*{n' <- `n'*`}) = (n + $sum(n'*{n' <- `n'*`}))
}

;; test.spectec:30.1-30.57
rec {

;; test.spectec:30.1-30.57
def $prod(fuck6fuck3nat*) : fuck3nat
  ;; test.spectec:31.1-31.19
  def $prod([]) = 1
  ;; test.spectec:32.1-32.37
  def $prod{n : fuck3nat, `n'*` : fuck6fuck1n*}([n] ++ n'*{n' <- `n'*`}) = (n * $prod(n'*{n' <- `n'*`}))
}

;; test.spectec:47.1-47.58
def $opt_(syntax X, fuck6fuck1X*) : fuck6fuck1X?
  ;; test.spectec:48.1-48.31
  def $opt_{syntax X}(syntax fuck1X, []) = ?()
  ;; test.spectec:49.1-49.27
  def $opt_{syntax X, w : fuck1X}(syntax fuck1X, [w]) = ?(w)

;; test.spectec:54.1-54.82
rec {

;; test.spectec:54.1-54.82
def $concat_(syntax X, fuck6fuck6fuck1X**) : fuck6fuck1X*
  ;; test.spectec:55.1-55.34
  def $concat_{syntax X}(syntax fuck1X, []) = []
  ;; test.spectec:56.1-56.64
  def $concat_{syntax X, `w*` : fuck6fuck1X*, `w'**` : fuck6fuck6fuck1X**}(syntax fuck1X, [w*{w <- `w*`}] ++ w'*{w' <- `w'*`}*{`w'*` <- `w'**`}) = w*{w <- `w*`} ++ $concat_(syntax fuck1X, w'*{w' <- `w'*`}*{`w'*` <- `w'**`})
}

;; test.spectec:58.1-58.89
rec {

;; test.spectec:58.1-58.89
def $concatn_(syntax X, fuck6fuck6fuck1X**, nat : fuck3nat) : fuck6fuck1X*
  ;; test.spectec:59.1-59.38
  def $concatn_{syntax X, n : fuck3nat}(syntax fuck1X, [], n) = []
  ;; test.spectec:60.1-60.73
  def $concatn_{syntax X, n : fuck3nat, `w*` : fuck6fuck1X*, `w'**` : fuck6fuck6fuck1X**}(syntax fuck1X, [w^n{w <- `w*`}] ++ w'^n{w' <- `w'*`}*{`w'*` <- `w'**`}, n) = w^n{w <- `w*`} ++ $concatn_(syntax fuck1X, w'^n{w' <- `w'*`}*{`w'*` <- `w'**`}, n)
}

;; test.spectec:62.1-62.58
def $concatopt_(syntax X, fuck6fuck6fuck1X?*) : fuck6fuck1X*
  ;; test.spectec:63.1-63.37
  def $concatopt_{syntax X}(syntax fuck1X, []) = []
  ;; test.spectec:64.1-64.67
  def $concatopt_{syntax X, `w?` : fuck6fuck1X?, `w'?*` : fuck6fuck6fuck1X?*}(syntax fuck1X, [w?{w <- `w?`}] ++ w'?{w' <- `w'?`}*{`w'?` <- `w'?*`}) = lift(w?{w <- `w?`}) ++ $concat_(syntax fuck1X, lift(w'?{w' <- `w'?`})*{`w'?` <- `w'?*`})

;; test.spectec:66.1-66.39
def $inv_concat_(syntax X, fuck6fuck1X*) : fuck6fuck6fuck1X**

;; test.spectec:69.1-69.45
def $inv_concatn_(syntax X, nat : fuck3nat, fuck6fuck1X*) : fuck6fuck6fuck1X**

;; test.spectec:75.1-75.78
rec {

;; test.spectec:75.1-75.78
def $disjoint_(syntax X, fuck6fuck1X*) : fuck2bool
  ;; test.spectec:76.1-76.37
  def $disjoint_{syntax X}(syntax fuck1X, []) = true
  ;; test.spectec:77.1-77.68
  def $disjoint_{syntax X, w : fuck1X, `w'*` : fuck6fuck1X*}(syntax fuck1X, [w] ++ w'*{w' <- `w'*`}) = (~ (w <- w'*{w' <- `w'*`}) /\ $disjoint_(syntax fuck1X, w'*{w' <- `w'*`}))
}

;; test.spectec:80.1-80.38
rec {

;; test.spectec:80.1-80.38
def $setminus1_(syntax X, X : fuck1X, fuck6fuck1X*) : fuck6fuck1X*
  ;; test.spectec:84.1-84.38
  def $setminus1_{syntax X, w : fuck1X}(syntax fuck1X, w, []) = [w]
  ;; test.spectec:85.1-85.78
  def $setminus1_{syntax X, w : fuck1X, w_1 : fuck1X, `w'*` : fuck6fuck1X*}(syntax fuck1X, w, [w_1] ++ w'*{w' <- `w'*`}) = (if (w = w_1) then [] else $setminus1_(syntax fuck1X, w, w'*{w' <- `w'*`}))
}

;; test.spectec:79.1-79.56
rec {

;; test.spectec:79.1-79.56
def $setminus_(syntax X, fuck6fuck1X*, fuck6fuck1X*) : fuck6fuck1X*
  ;; test.spectec:82.1-82.40
  def $setminus_{syntax X, `w*` : fuck6fuck1X*}(syntax fuck1X, [], w*{w <- `w*`}) = []
  ;; test.spectec:83.1-83.90
  def $setminus_{syntax X, w_1 : fuck1X, `w'*` : fuck6fuck1X*, `w*` : fuck6fuck1X*}(syntax fuck1X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}) = $setminus1_(syntax fuck1X, w_1, w*{w <- `w*`}) ++ $setminus_(syntax fuck1X, w'*{w' <- `w'*`}, w*{w <- `w*`})
}

;; test.spectec:91.1-91.46
rec {

;; test.spectec:91.1-91.46
def $setproduct2_(syntax X, X : fuck1X, fuck6fuck6fuck1X**) : fuck6fuck6fuck1X**
  ;; test.spectec:97.1-97.44
  def $setproduct2_{syntax X, w_1 : fuck1X}(syntax fuck1X, w_1, []) = []
  ;; test.spectec:98.1-98.90
  def $setproduct2_{syntax X, w_1 : fuck1X, `w'*` : fuck6fuck1X*, `w**` : fuck6fuck6fuck1X**}(syntax fuck1X, w_1, [w'*{w' <- `w'*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = [[w_1] ++ w'*{w' <- `w'*`}] ++ $setproduct2_(syntax fuck1X, w_1, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; test.spectec:90.1-90.47
rec {

;; test.spectec:90.1-90.47
def $setproduct1_(syntax X, fuck6fuck1X*, fuck6fuck6fuck1X**) : fuck6fuck6fuck1X**
  ;; test.spectec:95.1-95.46
  def $setproduct1_{syntax X, `w**` : fuck6fuck6fuck1X**}(syntax fuck1X, [], w*{w <- `w*`}*{`w*` <- `w**`}) = []
  ;; test.spectec:96.1-96.107
  def $setproduct1_{syntax X, w_1 : fuck1X, `w'*` : fuck6fuck1X*, `w**` : fuck6fuck6fuck1X**}(syntax fuck1X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct2_(syntax fuck1X, w_1, w*{w <- `w*`}*{`w*` <- `w**`}) ++ $setproduct1_(syntax fuck1X, w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; test.spectec:89.1-89.84
rec {

;; test.spectec:89.1-89.84
def $setproduct_(syntax X, fuck6fuck6fuck1X**) : fuck6fuck6fuck1X**
  ;; test.spectec:93.1-93.40
  def $setproduct_{syntax X}(syntax fuck1X, []) = [[]]
  ;; test.spectec:94.1-94.90
  def $setproduct_{syntax X, `w_1*` : fuck6fuck1X*, `w**` : fuck6fuck6fuck1X**}(syntax fuck1X, [w_1*{w_1 <- `w_1*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct1_(syntax fuck1X, w_1*{w_1 <- `w_1*`}, $setproduct_(syntax fuck1X, w*{w <- `w*`}*{`w*` <- `w**`}))
}

;; test.spectec:111.1-111.29
def $ND : fuck2bool

;; test.spectec:126.1-126.37
syntax bit = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:126.8-126.11
relation wf_bit: `%`fuck5(fuck1bit)
  ;; test.spectec:126.8-126.11
  rule bit_case_0{i : fuck3nat}:
    `%`(`%`_bit(i))
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:127.1-127.50
syntax byte = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:127.8-127.12
relation wf_byte: `%`fuck5(fuck1byte)
  ;; test.spectec:127.8-127.12
  rule byte_case_0{i : fuck3nat}:
    `%`(`%`_byte(i))
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:129.1-130.25
syntax uN = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:129.8-129.11
relation wf_uN: `%%`fuck5(fuck1N, fuck1uN)
  ;; test.spectec:129.8-129.11
  rule uN_case_0{N : fuck1N, i : fuck3nat}:
    `%%`(N, `%`_uN(i))
    -- if ((i >= 0) /\ (i <= ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:131.1-132.50
syntax sN = 
  | `%`fuck5(i : fuck3int)

;; test.spectec:131.8-131.11
relation wf_sN: `%%`fuck5(fuck1N, fuck1sN)
  ;; test.spectec:131.8-131.11
  rule sN_case_0{N : fuck1N, i : fuck3int}:
    `%%`(N, `%`_sN(i))
    -- if ((((i >= - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (+ ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; test.spectec:133.1-134.8
syntax iN = fuck1uN

;; test.spectec:136.1-136.20
syntax u8 = fuck1uN

;; test.spectec:137.1-137.21
syntax u16 = fuck1uN

;; test.spectec:138.1-138.21
syntax u31 = fuck1uN

;; test.spectec:139.1-139.21
syntax u32 = fuck1uN

;; test.spectec:140.1-140.21
syntax u64 = fuck1uN

;; test.spectec:141.1-141.21
syntax s33 = fuck1sN

;; test.spectec:142.1-142.21
syntax i32 = fuck1iN

;; test.spectec:143.1-143.21
syntax i64 = fuck1iN

;; test.spectec:144.1-144.23
syntax i128 = fuck1iN

;; test.spectec:151.1-151.35
def $signif(N : fuck1N) : fuck3nat
  ;; test.spectec:152.1-152.21
  def $signif(32) = 23
  ;; test.spectec:153.1-153.21
  def $signif(64) = 52

;; test.spectec:155.1-155.34
def $expon(N : fuck1N) : fuck3nat
  ;; test.spectec:156.1-156.19
  def $expon(32) = 8
  ;; test.spectec:157.1-157.20
  def $expon(64) = 11

;; test.spectec:159.1-159.47
def $M(N : fuck1N) : fuck3nat
  ;; test.spectec:160.1-160.23
  def $M{N : fuck3nat}(N) = $signif(N)

;; test.spectec:162.1-162.47
def $E(N : fuck1N) : fuck3nat
  ;; test.spectec:163.1-163.22
  def $E{N : fuck3nat}(N) = $expon(N)

;; test.spectec:169.1-169.47
syntax exp = fuck3int

;; test.spectec:170.1-174.84
syntax fNmag = 
  | NORMfuck5(m : fuck1m, exp : fuck1exp)
  | SUBNORMfuck5(m : fuck1m)
  | INF
  | NANfuck5(m : fuck1m)

;; test.spectec:170.8-170.14
relation wf_fNmag: `%%`fuck5(fuck1N, fuck1fNmag)
  ;; test.spectec:170.8-170.14
  rule fNmag_case_0{N : fuck1N, m : fuck1m, exp : fuck1exp}:
    `%%`(N, NORM_fNmag(m, exp))
    -- if ((m < (2 ^ $M(N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= exp) /\ (exp <= (((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

  ;; test.spectec:170.8-170.14
  rule fNmag_case_1{N : fuck1N, exp : fuck1exp, m : fuck1m}:
    `%%`(N, SUBNORM_fNmag(m))
    -- if ((m < (2 ^ $M(N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = exp))

  ;; test.spectec:170.8-170.14
  rule fNmag_case_2{N : fuck1N}:
    `%%`(N, INF_fNmag)

  ;; test.spectec:170.8-170.14
  rule fNmag_case_3{N : fuck1N, m : fuck1m}:
    `%%`(N, NAN_fNmag(m))
    -- if ((1 <= m) /\ (m < (2 ^ $M(N))))

;; test.spectec:165.1-167.35
syntax fN = 
  | POSfuck5(fuck1fNmag)
  | NEGfuck5(fuck1fNmag)

;; test.spectec:165.8-165.11
relation wf_fN: `%%`fuck5(fuck1N, fuck1fN)
  ;; test.spectec:165.8-165.11
  rule fN_case_0{N : fuck1N, var_0 : fuck1fNmag}:
    `%%`(N, POS_fN(var_0))
    -- wf_fNmag: `%%`(N, var_0)

  ;; test.spectec:165.8-165.11
  rule fN_case_1{N : fuck1N, var_0 : fuck1fNmag}:
    `%%`(N, NEG_fN(var_0))
    -- wf_fNmag: `%%`(N, var_0)

;; test.spectec:176.1-176.21
syntax f32 = fuck1fN

;; test.spectec:177.1-177.21
syntax f64 = fuck1fN

;; test.spectec:179.1-179.39
def $fzero(N : fuck1N) : fuck1fN
  ;; test.spectec:180.1-180.32
  def $fzero{N : fuck3nat}(N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:179.6-179.12
relation fzero_is_wf: `%%`fuck5(N : fuck1N, ret_val : fuck1fN)
  ;; test.spectec:179.6-179.12
  rule fzero_is_wf_0{N : fuck1N, ret_val : fuck1fN}:
    `%%`(N, ret_val)
    -- if (ret_val = $fzero(N))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:182.1-182.45
def $fnat(N : fuck1N, nat : fuck3nat) : fuck1fN
  ;; test.spectec:183.1-183.33
  def $fnat{N : fuck3nat, n : fuck3nat}(N, n) = POS_fN(NORM_fNmag(n, (0 : nat <:> int)))

;; test.spectec:182.6-182.11
relation fnat_is_wf: `%%%`fuck5(N : fuck1N, nat : fuck3nat, ret_val : fuck1fN)
  ;; test.spectec:182.6-182.11
  rule fnat_is_wf_0{N : fuck1N, nat : fuck3nat, ret_val : fuck1fN}:
    `%%%`(N, nat, ret_val)
    -- if (ret_val = $fnat(N, nat))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:185.1-185.39
def $fone(N : fuck1N) : fuck1fN
  ;; test.spectec:186.1-186.30
  def $fone{N : fuck3nat}(N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:185.6-185.11
relation fone_is_wf: `%%`fuck5(N : fuck1N, ret_val : fuck1fN)
  ;; test.spectec:185.6-185.11
  rule fone_is_wf_0{N : fuck1N, ret_val : fuck1fN}:
    `%%`(N, ret_val)
    -- if (ret_val = $fone(N))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:188.1-188.21
def $canon_(N : fuck1N) : fuck3nat
  ;; test.spectec:189.1-189.37
  def $canon_{N : fuck3nat}(N) = (2 ^ ((($signif(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:194.1-195.8
syntax vN = fuck1uN

;; test.spectec:197.1-197.23
syntax v128 = fuck1vN

;; test.spectec:203.1-203.49
syntax list{syntax X}(syntax fuck1X) = 
  | `%`fuck5(`X*` : fuck6fuck1X*)
    -- if (|X*{X <- `X*`}| < (2 ^ 32))

;; test.spectec:208.1-208.85
syntax char = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:208.8-208.12
relation wf_char: `%`fuck5(fuck1char)
  ;; test.spectec:208.8-208.12
  rule char_case_0{i : fuck3nat}:
    `%`(`%`_char(i))
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:210.1-210.25
def $utf8(fuck6fuck1char*) : fuck6fuck1byte*

;; test.spectec:210.6-210.11
relation utf8_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1char*, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:210.6-210.11
  rule utf8_is_wf_0{`var_0*` : fuck6fuck1char*, `ret_val*` : fuck6fuck1byte*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_char: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $utf8(`var_0*`))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:212.1-212.70
syntax name = 
  | `%`fuck5(`char*` : fuck6fuck1char*)

;; test.spectec:212.8-212.12
relation wf_name: `%`fuck5(fuck1name)
  ;; test.spectec:212.8-212.12
  rule name_case_0{`char*` : fuck6fuck1char*}:
    `%`(`%`_name(`char*`))
    -- (wf_char: `%`(char))*{char <- `char*`}
    -- if (|$utf8(char*{char <- `char*`})| < (2 ^ 32))

;; test.spectec:219.1-219.36
syntax idx = fuck1u32

;; test.spectec:220.1-220.44
syntax laneidx = fuck1u8

;; test.spectec:222.1-222.45
syntax typeidx = fuck1idx

;; test.spectec:223.1-223.49
syntax funcidx = fuck1idx

;; test.spectec:224.1-224.49
syntax globalidx = fuck1idx

;; test.spectec:225.1-225.47
syntax tableidx = fuck1idx

;; test.spectec:226.1-226.46
syntax memidx = fuck1idx

;; test.spectec:227.1-227.43
syntax tagidx = fuck1idx

;; test.spectec:228.1-228.45
syntax elemidx = fuck1idx

;; test.spectec:229.1-229.45
syntax dataidx = fuck1idx

;; test.spectec:230.1-230.47
syntax labelidx = fuck1idx

;; test.spectec:231.1-231.47
syntax localidx = fuck1idx

;; test.spectec:232.1-232.47
syntax fieldidx = fuck1idx

;; test.spectec:234.1-235.79
syntax externidx = 
  | FUNCfuck5(funcidx : fuck1funcidx)
  | GLOBALfuck5(globalidx : fuck1globalidx)
  | TABLEfuck5(tableidx : fuck1tableidx)
  | MEMfuck5(memidx : fuck1memidx)
  | TAGfuck5(tagidx : fuck1tagidx)

;; test.spectec:234.8-234.17
relation wf_externidx: `%`fuck5(fuck1externidx)
  ;; test.spectec:234.8-234.17
  rule externidx_case_0{funcidx : fuck1funcidx}:
    `%`(FUNC_externidx(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_1{globalidx : fuck1globalidx}:
    `%`(GLOBAL_externidx(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_2{tableidx : fuck1tableidx}:
    `%`(TABLE_externidx(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_3{memidx : fuck1memidx}:
    `%`(MEM_externidx(memidx))
    -- wf_uN: `%%`(32, memidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_4{tagidx : fuck1tagidx}:
    `%`(TAG_externidx(tagidx))
    -- wf_uN: `%%`(32, tagidx)

;; test.spectec:248.1-248.86
rec {

;; test.spectec:248.1-248.86
def $funcsxx(fuck6fuck1externidx*) : fuck6fuck1typeidx*
  ;; test.spectec:254.1-254.24
  def $funcsxx([]) = []
  ;; test.spectec:255.1-255.45
  def $funcsxx{x : fuck1uN, `xx*` : fuck6fuck1externidx*}([FUNC_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $funcsxx(xx*{xx <- `xx*`})
  ;; test.spectec:256.1-256.58
  def $funcsxx{externidx : fuck1externidx, `xx*` : fuck6fuck1externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $funcsxx(xx*{xx <- `xx*`})
}

;; test.spectec:248.1-248.86
rec {

;; test.spectec:248.6-248.14
relation funcsxx_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1typeidx*)
  ;; test.spectec:248.6-248.14
  rule funcsxx_is_wf_0{`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1typeidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externidx: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $funcsxx(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:249.1-249.88
rec {

;; test.spectec:249.1-249.88
def $globalsxx(fuck6fuck1externidx*) : fuck6fuck1globalidx*
  ;; test.spectec:258.1-258.26
  def $globalsxx([]) = []
  ;; test.spectec:259.1-259.51
  def $globalsxx{x : fuck1uN, `xx*` : fuck6fuck1externidx*}([GLOBAL_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $globalsxx(xx*{xx <- `xx*`})
  ;; test.spectec:260.1-260.62
  def $globalsxx{externidx : fuck1externidx, `xx*` : fuck6fuck1externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $globalsxx(xx*{xx <- `xx*`})
}

;; test.spectec:249.1-249.88
rec {

;; test.spectec:249.6-249.16
relation globalsxx_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1globalidx*)
  ;; test.spectec:249.6-249.16
  rule globalsxx_is_wf_0{`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1globalidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externidx: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $globalsxx(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:250.1-250.87
rec {

;; test.spectec:250.1-250.87
def $tablesxx(fuck6fuck1externidx*) : fuck6fuck1tableidx*
  ;; test.spectec:262.1-262.25
  def $tablesxx([]) = []
  ;; test.spectec:263.1-263.48
  def $tablesxx{x : fuck1uN, `xx*` : fuck6fuck1externidx*}([TABLE_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $tablesxx(xx*{xx <- `xx*`})
  ;; test.spectec:264.1-264.60
  def $tablesxx{externidx : fuck1externidx, `xx*` : fuck6fuck1externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $tablesxx(xx*{xx <- `xx*`})
}

;; test.spectec:250.1-250.87
rec {

;; test.spectec:250.6-250.15
relation tablesxx_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1tableidx*)
  ;; test.spectec:250.6-250.15
  rule tablesxx_is_wf_0{`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1tableidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externidx: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $tablesxx(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:251.1-251.85
rec {

;; test.spectec:251.1-251.85
def $memsxx(fuck6fuck1externidx*) : fuck6fuck1memidx*
  ;; test.spectec:266.1-266.23
  def $memsxx([]) = []
  ;; test.spectec:267.1-267.42
  def $memsxx{x : fuck1uN, `xx*` : fuck6fuck1externidx*}([MEM_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $memsxx(xx*{xx <- `xx*`})
  ;; test.spectec:268.1-268.56
  def $memsxx{externidx : fuck1externidx, `xx*` : fuck6fuck1externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $memsxx(xx*{xx <- `xx*`})
}

;; test.spectec:251.1-251.85
rec {

;; test.spectec:251.6-251.13
relation memsxx_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1memidx*)
  ;; test.spectec:251.6-251.13
  rule memsxx_is_wf_0{`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1memidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externidx: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $memsxx(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:252.1-252.85
rec {

;; test.spectec:252.1-252.85
def $tagsxx(fuck6fuck1externidx*) : fuck6fuck1tagidx*
  ;; test.spectec:270.1-270.23
  def $tagsxx([]) = []
  ;; test.spectec:271.1-271.42
  def $tagsxx{x : fuck1uN, `xx*` : fuck6fuck1externidx*}([TAG_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $tagsxx(xx*{xx <- `xx*`})
  ;; test.spectec:272.1-272.56
  def $tagsxx{externidx : fuck1externidx, `xx*` : fuck6fuck1externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $tagsxx(xx*{xx <- `xx*`})
}

;; test.spectec:252.1-252.85
rec {

;; test.spectec:252.6-252.13
relation tagsxx_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1tagidx*)
  ;; test.spectec:252.6-252.13
  rule tagsxx_is_wf_0{`var_0*` : fuck6fuck1externidx*, `ret_val*` : fuck6fuck1tagidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externidx: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $tagsxx(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:277.1-288.4
syntax free = 
{
  TYPES fuck6fuck1typeidx*,
  FUNCS fuck6fuck1funcidx*,
  GLOBALS fuck6fuck1globalidx*,
  TABLES fuck6fuck1tableidx*,
  MEMS fuck6fuck1memidx*,
  ELEMS fuck6fuck1elemidx*,
  DATAS fuck6fuck1dataidx*,
  LOCALS fuck6fuck1localidx*,
  LABELS fuck6fuck1labelidx*,
  TAGS fuck6fuck1tagidx*
}

;; test.spectec:277.8-277.12
relation wf_free: `%`fuck5(fuck1free)
  ;; test.spectec:277.8-277.12
  rule free_case_{`var_0*` : fuck6fuck1typeidx*, `var_1*` : fuck6fuck1funcidx*, `var_2*` : fuck6fuck1globalidx*, `var_3*` : fuck6fuck1tableidx*, `var_4*` : fuck6fuck1memidx*, `var_5*` : fuck6fuck1elemidx*, `var_6*` : fuck6fuck1dataidx*, `var_7*` : fuck6fuck1localidx*, `var_8*` : fuck6fuck1labelidx*, `var_9*` : fuck6fuck1tagidx*}:
    `%`({TYPES `var_0*`, FUNCS `var_1*`, GLOBALS `var_2*`, TABLES `var_3*`, MEMS `var_4*`, ELEMS `var_5*`, DATAS `var_6*`, LOCALS `var_7*`, LABELS `var_8*`, TAGS `var_9*`})
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- `var_0*`}
    -- (wf_uN: `%%`(32, var_1))*{var_1 <- `var_1*`}
    -- (wf_uN: `%%`(32, var_2))*{var_2 <- `var_2*`}
    -- (wf_uN: `%%`(32, var_3))*{var_3 <- `var_3*`}
    -- (wf_uN: `%%`(32, var_4))*{var_4 <- `var_4*`}
    -- (wf_uN: `%%`(32, var_5))*{var_5 <- `var_5*`}
    -- (wf_uN: `%%`(32, var_6))*{var_6 <- `var_6*`}
    -- (wf_uN: `%%`(32, var_7))*{var_7 <- `var_7*`}
    -- (wf_uN: `%%`(32, var_8))*{var_8 <- `var_8*`}
    -- (wf_uN: `%%`(32, var_9))*{var_9 <- `var_9*`}

;; test.spectec:291.1-291.28
def $free_opt(fuck6fuck1free?) : fuck1free
  ;; test.spectec:294.1-294.24
  def $free_opt(?()) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:295.1-295.27
  def $free_opt{free : fuck1free}(?(free)) = free

;; test.spectec:291.6-291.15
relation free_opt_is_wf: `%%`fuck5(`var_0?` : fuck6fuck1free?, ret_val : fuck1free)
  ;; test.spectec:291.6-291.15
  rule free_opt_is_wf_0{`var_0?` : fuck6fuck1free?, ret_val : fuck1free}:
    `%%`(`var_0?`, ret_val)
    -- (wf_free: `%`(var_0))?{var_0 <- `var_0?`}
    -- if (ret_val = $free_opt(`var_0?`))
    -- wf_free: `%`(ret_val)

;; test.spectec:292.1-292.29
rec {

;; test.spectec:292.1-292.29
def $free_list(fuck6fuck1free*) : fuck1free
  ;; test.spectec:297.1-297.25
  def $free_list([]) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:298.1-298.57
  def $free_list{free : fuck1free, `free'*` : fuck6fuck1free*}([free] ++ free'*{free' <- `free'*`}) = free +++ $free_list(free'*{free' <- `free'*`})
}

;; test.spectec:292.1-292.29
rec {

;; test.spectec:292.6-292.16
relation free_list_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1free*, ret_val : fuck1free)
  ;; test.spectec:292.6-292.16
  rule free_list_is_wf_0{`var_0*` : fuck6fuck1free*, ret_val : fuck1free}:
    `%%`(`var_0*`, ret_val)
    -- (wf_free: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $free_list(`var_0*`))
    -- wf_free: `%`(ret_val)
}

;; test.spectec:301.1-301.34
def $free_typeidx(typeidx : fuck1typeidx) : fuck1free
  ;; test.spectec:313.1-313.45
  def $free_typeidx{typeidx : fuck1uN}(typeidx) = {TYPES [typeidx], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:301.6-301.19
relation free_typeidx_is_wf: `%%`fuck5(typeidx : fuck1typeidx, ret_val : fuck1free)
  ;; test.spectec:301.6-301.19
  rule free_typeidx_is_wf_0{typeidx : fuck1typeidx, ret_val : fuck1free}:
    `%%`(typeidx, ret_val)
    -- wf_uN: `%%`(32, typeidx)
    -- if (ret_val = $free_typeidx(typeidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:302.1-302.34
def $free_funcidx(funcidx : fuck1funcidx) : fuck1free
  ;; test.spectec:314.1-314.45
  def $free_funcidx{funcidx : fuck1uN}(funcidx) = {TYPES [], FUNCS [funcidx], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:302.6-302.19
relation free_funcidx_is_wf: `%%`fuck5(funcidx : fuck1funcidx, ret_val : fuck1free)
  ;; test.spectec:302.6-302.19
  rule free_funcidx_is_wf_0{funcidx : fuck1funcidx, ret_val : fuck1free}:
    `%%`(funcidx, ret_val)
    -- wf_uN: `%%`(32, funcidx)
    -- if (ret_val = $free_funcidx(funcidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:303.1-303.38
def $free_globalidx(globalidx : fuck1globalidx) : fuck1free
  ;; test.spectec:315.1-315.53
  def $free_globalidx{globalidx : fuck1uN}(globalidx) = {TYPES [], FUNCS [], GLOBALS [globalidx], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:303.6-303.21
relation free_globalidx_is_wf: `%%`fuck5(globalidx : fuck1globalidx, ret_val : fuck1free)
  ;; test.spectec:303.6-303.21
  rule free_globalidx_is_wf_0{globalidx : fuck1globalidx, ret_val : fuck1free}:
    `%%`(globalidx, ret_val)
    -- wf_uN: `%%`(32, globalidx)
    -- if (ret_val = $free_globalidx(globalidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:304.1-304.36
def $free_tableidx(tableidx : fuck1tableidx) : fuck1free
  ;; test.spectec:316.1-316.49
  def $free_tableidx{tableidx : fuck1uN}(tableidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [tableidx], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:304.6-304.20
relation free_tableidx_is_wf: `%%`fuck5(tableidx : fuck1tableidx, ret_val : fuck1free)
  ;; test.spectec:304.6-304.20
  rule free_tableidx_is_wf_0{tableidx : fuck1tableidx, ret_val : fuck1free}:
    `%%`(tableidx, ret_val)
    -- wf_uN: `%%`(32, tableidx)
    -- if (ret_val = $free_tableidx(tableidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:305.1-305.32
def $free_memidx(memidx : fuck1memidx) : fuck1free
  ;; test.spectec:317.1-317.41
  def $free_memidx{memidx : fuck1uN}(memidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [memidx], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:305.6-305.18
relation free_memidx_is_wf: `%%`fuck5(memidx : fuck1memidx, ret_val : fuck1free)
  ;; test.spectec:305.6-305.18
  rule free_memidx_is_wf_0{memidx : fuck1memidx, ret_val : fuck1free}:
    `%%`(memidx, ret_val)
    -- wf_uN: `%%`(32, memidx)
    -- if (ret_val = $free_memidx(memidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:306.1-306.34
def $free_elemidx(elemidx : fuck1elemidx) : fuck1free
  ;; test.spectec:318.1-318.45
  def $free_elemidx{elemidx : fuck1uN}(elemidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [elemidx], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:306.6-306.19
relation free_elemidx_is_wf: `%%`fuck5(elemidx : fuck1elemidx, ret_val : fuck1free)
  ;; test.spectec:306.6-306.19
  rule free_elemidx_is_wf_0{elemidx : fuck1elemidx, ret_val : fuck1free}:
    `%%`(elemidx, ret_val)
    -- wf_uN: `%%`(32, elemidx)
    -- if (ret_val = $free_elemidx(elemidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:307.1-307.34
def $free_dataidx(dataidx : fuck1dataidx) : fuck1free
  ;; test.spectec:319.1-319.45
  def $free_dataidx{dataidx : fuck1uN}(dataidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [dataidx], LOCALS [], LABELS [], TAGS []}

;; test.spectec:307.6-307.19
relation free_dataidx_is_wf: `%%`fuck5(dataidx : fuck1dataidx, ret_val : fuck1free)
  ;; test.spectec:307.6-307.19
  rule free_dataidx_is_wf_0{dataidx : fuck1dataidx, ret_val : fuck1free}:
    `%%`(dataidx, ret_val)
    -- wf_uN: `%%`(32, dataidx)
    -- if (ret_val = $free_dataidx(dataidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:308.1-308.36
def $free_localidx(localidx : fuck1localidx) : fuck1free
  ;; test.spectec:320.1-320.49
  def $free_localidx{localidx : fuck1uN}(localidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [localidx], LABELS [], TAGS []}

;; test.spectec:308.6-308.20
relation free_localidx_is_wf: `%%`fuck5(localidx : fuck1localidx, ret_val : fuck1free)
  ;; test.spectec:308.6-308.20
  rule free_localidx_is_wf_0{localidx : fuck1localidx, ret_val : fuck1free}:
    `%%`(localidx, ret_val)
    -- wf_uN: `%%`(32, localidx)
    -- if (ret_val = $free_localidx(localidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:309.1-309.36
def $free_labelidx(labelidx : fuck1labelidx) : fuck1free
  ;; test.spectec:321.1-321.49
  def $free_labelidx{labelidx : fuck1uN}(labelidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [labelidx], TAGS []}

;; test.spectec:309.6-309.20
relation free_labelidx_is_wf: `%%`fuck5(labelidx : fuck1labelidx, ret_val : fuck1free)
  ;; test.spectec:309.6-309.20
  rule free_labelidx_is_wf_0{labelidx : fuck1labelidx, ret_val : fuck1free}:
    `%%`(labelidx, ret_val)
    -- wf_uN: `%%`(32, labelidx)
    -- if (ret_val = $free_labelidx(labelidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:311.1-311.32
def $free_tagidx(tagidx : fuck1tagidx) : fuck1free
  ;; test.spectec:322.1-322.41
  def $free_tagidx{tagidx : fuck1uN}(tagidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS [tagidx]}

;; test.spectec:311.6-311.18
relation free_tagidx_is_wf: `%%`fuck5(tagidx : fuck1tagidx, ret_val : fuck1free)
  ;; test.spectec:311.6-311.18
  rule free_tagidx_is_wf_0{tagidx : fuck1tagidx, ret_val : fuck1free}:
    `%%`(tagidx, ret_val)
    -- wf_uN: `%%`(32, tagidx)
    -- if (ret_val = $free_tagidx(tagidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:310.1-310.38
def $free_externidx(externidx : fuck1externidx) : fuck1free
  ;; test.spectec:324.1-324.59
  def $free_externidx{funcidx : fuck1uN}(FUNC_externidx(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:325.1-325.67
  def $free_externidx{globalidx : fuck1uN}(GLOBAL_externidx(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:326.1-326.63
  def $free_externidx{tableidx : fuck1uN}(TABLE_externidx(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:327.1-327.55
  def $free_externidx{memidx : fuck1uN}(MEM_externidx(memidx)) = $free_memidx(memidx)
  ;; test.spectec:328.1-328.55
  def $free_externidx{tagidx : fuck1uN}(TAG_externidx(tagidx)) = $free_tagidx(tagidx)

;; test.spectec:310.6-310.21
relation free_externidx_is_wf: `%%`fuck5(externidx : fuck1externidx, ret_val : fuck1free)
  ;; test.spectec:310.6-310.21
  rule free_externidx_is_wf_0{externidx : fuck1externidx, ret_val : fuck1free}:
    `%%`(externidx, ret_val)
    -- wf_externidx: `%`(externidx)
    -- if (ret_val = $free_externidx(externidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:344.1-344.55
syntax null = 
  | NULL

;; test.spectec:346.1-347.14
syntax addrtype = 
  | I32
  | I64

;; test.spectec:349.1-350.26
syntax numtype = 
  | I32
  | I64
  | F32
  | F64

;; test.spectec:352.1-353.9
syntax vectype = 
  | V128

;; test.spectec:355.1-356.22
syntax consttype = 
  | I32
  | I64
  | F32
  | F64
  | V128

;; test.spectec:364.1-365.14
syntax absheaptype = 
  | ANY
  | EQ
  | I31
  | STRUCT
  | ARRAY
  | NONE
  | FUNC
  | NOFUNC
  | EXN
  | NOEXN
  | EXTERN
  | NOEXTERN
  | BOT

;; test.spectec:445.1-445.54
syntax mut = 
  | MUT

;; test.spectec:446.1-446.60
syntax final = 
  | FINAL

;; test.spectec:373.1-459.22
rec {

;; test.spectec:373.1-374.43
syntax typeuse = 
  | _IDXfuck5(typeidx : fuck1typeidx)
  | _DEFfuck5(rectype : fuck1rectype, n : fuck1n)
  | RECfuck5(n : fuck1n)

;; test.spectec:379.1-380.26
syntax heaptype = 
  | ANY
  | EQ
  | I31
  | STRUCT
  | ARRAY
  | NONE
  | FUNC
  | NOFUNC
  | EXN
  | NOEXN
  | EXTERN
  | NOEXTERN
  | BOT
  | _IDXfuck5(typeidx : fuck1typeidx)
  | _DEFfuck5(rectype : fuck1rectype, n : fuck1n)
  | RECfuck5(n : fuck1n)

;; test.spectec:387.1-388.14
syntax valtype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REFfuck5(`null?` : fuck6fuck1null?, heaptype : fuck1heaptype)
  | BOT

;; test.spectec:428.1-428.66
syntax storagetype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REFfuck5(`null?` : fuck6fuck1null?, heaptype : fuck1heaptype)
  | BOT
  | I8
  | I16

;; test.spectec:438.1-439.16
syntax resulttype = fuck1list(syntax fuck1valtype)

;; test.spectec:448.1-448.61
syntax fieldtype = 
  | `%%`fuck5(`mut?` : fuck6fuck1mut?, storagetype : fuck1storagetype)

;; test.spectec:450.1-453.34
syntax comptype = 
  | STRUCTfuck5(fuck1list(syntax fuck1fieldtype))
  | ARRAYfuck5(fieldtype : fuck1fieldtype)
  | `FUNC%->%`fuck5(resulttype : fuck1resulttype, resulttype : fuck1resulttype)

;; test.spectec:455.1-456.33
syntax subtype = 
  | SUBfuck5(`final?` : fuck6fuck1final?, `typeuse*` : fuck6fuck1typeuse*, comptype : fuck1comptype)

;; test.spectec:458.1-459.22
syntax rectype = 
  | RECfuck5(fuck1list(syntax fuck1subtype))
}

;; test.spectec:373.1-459.22
rec {

;; test.spectec:373.8-373.15
relation wf_typeuse: `%`fuck5(fuck1typeuse)
  ;; test.spectec:373.8-373.15
  rule typeuse_case_0{typeidx : fuck1typeidx}:
    `%`(_IDX_typeuse(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:373.8-373.15
  rule typeuse_case_1{rectype : fuck1rectype, n : fuck1n}:
    `%`(_DEF_typeuse(rectype, n))

  ;; test.spectec:373.8-373.15
  rule typeuse_case_2{n : fuck1n}:
    `%`(REC_typeuse(n))

;; test.spectec:379.8-379.16
relation wf_heaptype: `%`fuck5(fuck1heaptype)
  ;; test.spectec:379.8-379.16
  rule heaptype_case_0:
    `%`(ANY_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_1:
    `%`(EQ_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_2:
    `%`(I31_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_3:
    `%`(STRUCT_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_4:
    `%`(ARRAY_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_5:
    `%`(NONE_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_6:
    `%`(FUNC_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_7:
    `%`(NOFUNC_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_8:
    `%`(EXN_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_9:
    `%`(NOEXN_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_10:
    `%`(EXTERN_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_11:
    `%`(NOEXTERN_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_12:
    `%`(BOT_heaptype)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_13{typeidx : fuck1typeidx}:
    `%`(_IDX_heaptype(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_14{rectype : fuck1rectype, n : fuck1n}:
    `%`(_DEF_heaptype(rectype, n))

  ;; test.spectec:379.8-379.16
  rule heaptype_case_15{n : fuck1n}:
    `%`(REC_heaptype(n))

;; test.spectec:387.8-387.15
relation wf_valtype: `%`fuck5(fuck1valtype)
  ;; test.spectec:387.8-387.15
  rule valtype_case_0:
    `%`(I32_valtype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_1:
    `%`(I64_valtype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_2:
    `%`(F32_valtype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_3:
    `%`(F64_valtype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_4:
    `%`(V128_valtype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_5{`null?` : fuck6fuck1null?, heaptype : fuck1heaptype}:
    `%`(REF_valtype(`null?`, heaptype))
    -- wf_heaptype: `%`(heaptype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_6:
    `%`(BOT_valtype)

;; test.spectec:428.8-428.19
relation wf_storagetype: `%`fuck5(fuck1storagetype)
  ;; test.spectec:428.8-428.19
  rule storagetype_case_0:
    `%`(I32_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_1:
    `%`(I64_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_2:
    `%`(F32_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_3:
    `%`(F64_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_4:
    `%`(V128_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_5{`null?` : fuck6fuck1null?, heaptype : fuck1heaptype}:
    `%`(REF_storagetype(`null?`, heaptype))
    -- wf_heaptype: `%`(heaptype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_6:
    `%`(BOT_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_7:
    `%`(I8_storagetype)

  ;; test.spectec:428.8-428.19
  rule storagetype_case_8:
    `%`(I16_storagetype)

;; test.spectec:448.8-448.17
relation wf_fieldtype: `%`fuck5(fuck1fieldtype)
  ;; test.spectec:448.8-448.17
  rule fieldtype_case_0{`mut?` : fuck6fuck1mut?, storagetype : fuck1storagetype}:
    `%`(`%%`_fieldtype(`mut?`, storagetype))
    -- wf_storagetype: `%`(storagetype)

;; test.spectec:450.8-450.16
relation wf_comptype: `%`fuck5(fuck1comptype)
  ;; test.spectec:450.8-450.16
  rule comptype_case_0{var_0 : fuck1list(syntax fuck1fieldtype)}:
    `%`(STRUCT_comptype(var_0))

  ;; test.spectec:450.8-450.16
  rule comptype_case_1{fieldtype : fuck1fieldtype}:
    `%`(ARRAY_comptype(fieldtype))
    -- wf_fieldtype: `%`(fieldtype)

  ;; test.spectec:450.8-450.16
  rule comptype_case_2{resulttype : fuck1resulttype, resulttype_0 : fuck1resulttype}:
    `%`(`FUNC%->%`_comptype(resulttype, resulttype_0))

;; test.spectec:455.8-455.15
relation wf_subtype: `%`fuck5(fuck1subtype)
  ;; test.spectec:455.8-455.15
  rule subtype_case_0{`final?` : fuck6fuck1final?, `typeuse*` : fuck6fuck1typeuse*, comptype : fuck1comptype}:
    `%`(SUB_subtype(`final?`, `typeuse*`, comptype))
    -- (wf_typeuse: `%`(typeuse))*{typeuse <- `typeuse*`}
    -- wf_comptype: `%`(comptype)
}

;; test.spectec:368.1-369.34
syntax deftype = 
  | _DEFfuck5(rectype : fuck1rectype, n : fuck1n)

;; test.spectec:376.1-377.42
syntax typevar = 
  | _IDXfuck5(typeidx : fuck1typeidx)
  | RECfuck5(n : fuck1n)

;; test.spectec:376.8-376.15
relation wf_typevar: `%`fuck5(fuck1typevar)
  ;; test.spectec:376.8-376.15
  rule typevar_case_0{typeidx : fuck1typeidx}:
    `%`(_IDX_typevar(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:376.8-376.15
  rule typevar_case_1{n : fuck1n}:
    `%`(REC_typevar(n))

;; test.spectec:382.1-383.23
syntax reftype = 
  | REFfuck5(`null?` : fuck6fuck1null?, heaptype : fuck1heaptype)

;; test.spectec:382.8-382.15
relation wf_reftype: `%`fuck5(fuck1reftype)
  ;; test.spectec:382.8-382.15
  rule reftype_case_0{`null?` : fuck6fuck1null?, heaptype : fuck1heaptype}:
    `%`(REF_reftype(`null?`, heaptype))
    -- wf_heaptype: `%`(heaptype)

;; test.spectec:391.1-391.55
syntax Inn = fuck1addrtype

;; test.spectec:392.1-392.56
syntax Fnn = 
  | F32
  | F64

;; test.spectec:393.1-393.54
syntax Vnn = fuck1vectype

;; test.spectec:394.1-394.42
syntax Cnn = 
  | I32
  | I64
  | F32
  | F64
  | V128

;; test.spectec:397.1-397.43
def $ANYREF : fuck1reftype
  ;; test.spectec:410.1-410.32
  def $ANYREF = REF_reftype(?(NULL_null), ANY_heaptype)

;; test.spectec:397.6-397.12
relation ANYREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:397.6-397.12
  rule ANYREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $ANYREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:398.1-398.42
def $EQREF : fuck1reftype
  ;; test.spectec:411.1-411.31
  def $EQREF = REF_reftype(?(NULL_null), EQ_heaptype)

;; test.spectec:398.6-398.11
relation EQREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:398.6-398.11
  rule EQREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $EQREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:399.1-399.43
def $I31REF : fuck1reftype
  ;; test.spectec:412.1-412.32
  def $I31REF = REF_reftype(?(NULL_null), I31_heaptype)

;; test.spectec:399.6-399.12
relation I31REF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:399.6-399.12
  rule I31REF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $I31REF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:400.1-400.46
def $STRUCTREF : fuck1reftype
  ;; test.spectec:413.1-413.35
  def $STRUCTREF = REF_reftype(?(NULL_null), STRUCT_heaptype)

;; test.spectec:400.6-400.15
relation STRUCTREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:400.6-400.15
  rule STRUCTREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $STRUCTREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:401.1-401.45
def $ARRAYREF : fuck1reftype
  ;; test.spectec:414.1-414.34
  def $ARRAYREF = REF_reftype(?(NULL_null), ARRAY_heaptype)

;; test.spectec:401.6-401.14
relation ARRAYREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:401.6-401.14
  rule ARRAYREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $ARRAYREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:402.1-402.44
def $FUNCREF : fuck1reftype
  ;; test.spectec:415.1-415.33
  def $FUNCREF = REF_reftype(?(NULL_null), FUNC_heaptype)

;; test.spectec:402.6-402.13
relation FUNCREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:402.6-402.13
  rule FUNCREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $FUNCREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:403.1-403.43
def $EXNREF : fuck1reftype
  ;; test.spectec:416.1-416.32
  def $EXNREF = REF_reftype(?(NULL_null), EXN_heaptype)

;; test.spectec:403.6-403.12
relation EXNREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:403.6-403.12
  rule EXNREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $EXNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:404.1-404.46
def $EXTERNREF : fuck1reftype
  ;; test.spectec:417.1-417.35
  def $EXTERNREF = REF_reftype(?(NULL_null), EXTERN_heaptype)

;; test.spectec:404.6-404.15
relation EXTERNREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:404.6-404.15
  rule EXTERNREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $EXTERNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:405.1-405.44
def $NULLREF : fuck1reftype
  ;; test.spectec:418.1-418.33
  def $NULLREF = REF_reftype(?(NULL_null), NONE_heaptype)

;; test.spectec:405.6-405.13
relation NULLREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:405.6-405.13
  rule NULLREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:406.1-406.50
def $NULLFUNCREF : fuck1reftype
  ;; test.spectec:419.1-419.37
  def $NULLFUNCREF = REF_reftype(?(NULL_null), NOFUNC_heaptype)

;; test.spectec:406.6-406.17
relation NULLFUNCREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:406.6-406.17
  rule NULLFUNCREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLFUNCREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:407.1-407.49
def $NULLEXNREF : fuck1reftype
  ;; test.spectec:420.1-420.36
  def $NULLEXNREF = REF_reftype(?(NULL_null), NOEXN_heaptype)

;; test.spectec:407.6-407.16
relation NULLEXNREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:407.6-407.16
  rule NULLEXNREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLEXNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:408.1-408.54
def $NULLEXTERNREF : fuck1reftype
  ;; test.spectec:421.1-421.41
  def $NULLEXTERNREF = REF_reftype(?(NULL_null), NOEXTERN_heaptype)

;; test.spectec:408.6-408.19
relation NULLEXTERNREF_is_wf: `%`fuck5(ret_val : fuck1reftype)
  ;; test.spectec:408.6-408.19
  rule NULLEXTERNREF_is_wf_0{ret_val : fuck1reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLEXTERNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:426.1-426.52
syntax packtype = 
  | I8
  | I16

;; test.spectec:427.1-427.60
syntax lanetype = 
  | I32
  | I64
  | F32
  | F64
  | I8
  | I16

;; test.spectec:431.1-431.55
syntax Pnn = fuck1packtype

;; test.spectec:432.1-432.56
syntax Jnn = 
  | I32
  | I64
  | I8
  | I16

;; test.spectec:433.1-433.55
syntax Lnn = fuck1lanetype

;; test.spectec:464.1-464.74
syntax limits = 
  | `[%..%]`fuck5(u64 : fuck1u64, `u64?` : fuck6fuck1u64?)

;; test.spectec:464.8-464.14
relation wf_limits: `%`fuck5(fuck1limits)
  ;; test.spectec:464.8-464.14
  rule limits_case_0{u64 : fuck1u64, `u64?` : fuck6fuck1u64?}:
    `%`(`[%..%]`_limits(u64, `u64?`))
    -- wf_uN: `%%`(64, u64)
    -- (wf_uN: `%%`(64, u64))?{u64 <- `u64?`}

;; test.spectec:466.1-466.47
syntax tagtype = fuck1typeuse

;; test.spectec:467.1-467.58
syntax globaltype = 
  | `%%`fuck5(`mut?` : fuck6fuck1mut?, valtype : fuck1valtype)

;; test.spectec:467.8-467.18
relation wf_globaltype: `%`fuck5(fuck1globaltype)
  ;; test.spectec:467.8-467.18
  rule globaltype_case_0{`mut?` : fuck6fuck1mut?, valtype : fuck1valtype}:
    `%`(`%%`_globaltype(`mut?`, valtype))
    -- wf_valtype: `%`(valtype)

;; test.spectec:468.1-468.63
syntax memtype = 
  | `%%PAGE`fuck5(addrtype : fuck1addrtype, limits : fuck1limits)

;; test.spectec:468.8-468.15
relation wf_memtype: `%`fuck5(fuck1memtype)
  ;; test.spectec:468.8-468.15
  rule memtype_case_0{addrtype : fuck1addrtype, limits : fuck1limits}:
    `%`(`%%PAGE`_memtype(addrtype, limits))
    -- wf_limits: `%`(limits)

;; test.spectec:469.1-469.67
syntax tabletype = 
  | `%%%`fuck5(addrtype : fuck1addrtype, limits : fuck1limits, reftype : fuck1reftype)

;; test.spectec:469.8-469.17
relation wf_tabletype: `%`fuck5(fuck1tabletype)
  ;; test.spectec:469.8-469.17
  rule tabletype_case_0{addrtype : fuck1addrtype, limits : fuck1limits, reftype : fuck1reftype}:
    `%`(`%%%`_tabletype(addrtype, limits, reftype))
    -- wf_limits: `%`(limits)
    -- wf_reftype: `%`(reftype)

;; test.spectec:470.1-470.64
syntax datatype = 
  | OK

;; test.spectec:471.1-471.52
syntax elemtype = fuck1reftype

;; test.spectec:473.1-474.83
syntax externtype = 
  | TAGfuck5(tagtype : fuck1tagtype)
  | GLOBALfuck5(globaltype : fuck1globaltype)
  | MEMfuck5(memtype : fuck1memtype)
  | TABLEfuck5(tabletype : fuck1tabletype)
  | FUNCfuck5(typeuse : fuck1typeuse)

;; test.spectec:473.8-473.18
relation wf_externtype: `%`fuck5(fuck1externtype)
  ;; test.spectec:473.8-473.18
  rule externtype_case_0{tagtype : fuck1tagtype}:
    `%`(TAG_externtype(tagtype))
    -- wf_typeuse: `%`(tagtype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_1{globaltype : fuck1globaltype}:
    `%`(GLOBAL_externtype(globaltype))
    -- wf_globaltype: `%`(globaltype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_2{memtype : fuck1memtype}:
    `%`(MEM_externtype(memtype))
    -- wf_memtype: `%`(memtype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_3{tabletype : fuck1tabletype}:
    `%`(TABLE_externtype(tabletype))
    -- wf_tabletype: `%`(tabletype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_4{typeuse : fuck1typeuse}:
    `%`(FUNC_externtype(typeuse))
    -- wf_typeuse: `%`(typeuse)

;; test.spectec:476.1-477.47
syntax moduletype = 
  | `%->%`fuck5(`externtype*` : fuck6fuck1externtype*, `externtype*` : fuck6fuck1externtype*)

;; test.spectec:476.8-476.18
relation wf_moduletype: `%`fuck5(fuck1moduletype)
  ;; test.spectec:476.8-476.18
  rule moduletype_case_0{`externtype*` : fuck6fuck1externtype*, `externtype*_0*` : fuck6fuck1externtype*}:
    `%`(`%->%`_moduletype(`externtype*`, `externtype*_0*`))
    -- (wf_externtype: `%`(externtype))*{externtype <- `externtype*`}
    -- (wf_externtype: `%`(`externtype*_0`))*{`externtype*_0` <- `externtype*_0*`}

;; test.spectec:515.1-515.65
def $IN(N : fuck1N) : fuck1Inn
  ;; test.spectec:516.1-516.18
  def $IN(32) = I32_Inn
  ;; test.spectec:517.1-517.18
  def $IN(64) = I64_Inn

;; test.spectec:519.1-519.65
def $FN(N : fuck1N) : fuck1Fnn
  ;; test.spectec:520.1-520.18
  def $FN(32) = F32_Fnn
  ;; test.spectec:521.1-521.18
  def $FN(64) = F64_Fnn

;; test.spectec:523.1-523.65
def $JN(N : fuck1N) : fuck1Jnn
  ;; test.spectec:524.1-524.16
  def $JN(8) = I8_Jnn
  ;; test.spectec:525.1-525.18
  def $JN(16) = I16_Jnn
  ;; test.spectec:526.1-526.18
  def $JN(32) = I32_Jnn
  ;; test.spectec:527.1-527.18
  def $JN(64) = I64_Jnn

;; test.spectec:532.1-532.46
def $size(numtype : fuck1numtype) : fuck3nat
  ;; test.spectec:541.1-541.20
  def $size(I32_numtype) = 32
  ;; test.spectec:542.1-542.20
  def $size(I64_numtype) = 64
  ;; test.spectec:543.1-543.20
  def $size(F32_numtype) = 32
  ;; test.spectec:544.1-544.20
  def $size(F64_numtype) = 64

;; test.spectec:533.1-533.46
def $vsize(vectype : fuck1vectype) : fuck3nat
  ;; test.spectec:546.1-546.23
  def $vsize(V128_vectype) = 128

;; test.spectec:534.1-534.46
def $psize(packtype : fuck1packtype) : fuck3nat
  ;; test.spectec:548.1-548.19
  def $psize(I8_packtype) = 8
  ;; test.spectec:549.1-549.21
  def $psize(I16_packtype) = 16

;; test.spectec:535.1-535.46
def $lsize(lanetype : fuck1lanetype) : fuck3nat
  ;; test.spectec:551.1-551.37
  def $lsize{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1lanetype)) = $size(numtype)
  ;; test.spectec:552.1-552.40
  def $lsize{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1lanetype)) = $psize(packtype)

;; test.spectec:536.1-536.60
def $zsize(storagetype : fuck1storagetype) : fuck3nat
  ;; test.spectec:554.1-554.37
  def $zsize{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1storagetype)) = $size(numtype)
  ;; test.spectec:555.1-555.38
  def $zsize{vectype : fuck1vectype}((vectype : fuck1vectype <: fuck1storagetype)) = $vsize(vectype)
  ;; test.spectec:556.1-556.40
  def $zsize{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1storagetype)) = $psize(packtype)

;; test.spectec:537.1-537.71
def $isize(Inn : fuck1Inn) : fuck3nat
  ;; test.spectec:558.1-558.29
  def $isize{Inn : fuck1addrtype}(Inn) = $size((Inn : fuck1addrtype <: fuck1numtype))

;; test.spectec:538.1-538.71
def $jsize(Jnn : fuck1Jnn) : fuck3nat
  ;; test.spectec:560.1-560.30
  def $jsize{Jnn : fuck1Jnn}(Jnn) = $lsize((Jnn : fuck1Jnn <: fuck1lanetype))

;; test.spectec:539.1-539.71
def $fsize(Fnn : fuck1Fnn) : fuck3nat
  ;; test.spectec:559.1-559.29
  def $fsize{Fnn : fuck1Fnn}(Fnn) = $size((Fnn : fuck1Fnn <: fuck1numtype))

;; test.spectec:562.1-562.40
def $inv_isize(nat : fuck3nat) : fuck1Inn
  ;; test.spectec:566.1-566.25
  def $inv_isize(32) = I32_Inn
  ;; test.spectec:567.1-567.25
  def $inv_isize(64) = I64_Inn

;; test.spectec:563.1-563.40
def $inv_jsize(nat : fuck3nat) : fuck1Jnn
  ;; test.spectec:570.1-570.24
  def $inv_jsize(8) = I8_Jnn
  ;; test.spectec:571.1-571.25
  def $inv_jsize(16) = I16_Jnn
  ;; test.spectec:572.1-572.34
  def $inv_jsize{n : fuck3nat}(n) = ($inv_isize(n) : fuck1addrtype <: fuck1Jnn)

;; test.spectec:564.1-564.40
def $inv_fsize(nat : fuck3nat) : fuck1Fnn
  ;; test.spectec:568.1-568.25
  def $inv_fsize(32) = F32_Fnn
  ;; test.spectec:569.1-569.25
  def $inv_fsize(64) = F64_Fnn

;; test.spectec:575.1-575.63
def $sizenn(numtype : fuck1numtype) : fuck3nat
  ;; test.spectec:578.1-578.28
  def $sizenn{nt : fuck1numtype}(nt) = $size(nt)

;; test.spectec:576.1-576.63
def $sizenn1(numtype : fuck1numtype) : fuck3nat
  ;; test.spectec:579.1-579.29
  def $sizenn1{nt : fuck1numtype}(nt) = $size(nt)

;; test.spectec:577.1-577.63
def $sizenn2(numtype : fuck1numtype) : fuck3nat
  ;; test.spectec:580.1-580.29
  def $sizenn2{nt : fuck1numtype}(nt) = $size(nt)

;; test.spectec:582.1-582.63
def $vsizenn(vectype : fuck1vectype) : fuck3nat
  ;; test.spectec:583.1-583.30
  def $vsizenn{vt : fuck1vectype}(vt) = $vsize(vt)

;; test.spectec:585.1-585.63
def $psizenn(packtype : fuck1packtype) : fuck3nat
  ;; test.spectec:586.1-586.30
  def $psizenn{pt : fuck1packtype}(pt) = $psize(pt)

;; test.spectec:588.1-588.63
def $lsizenn(lanetype : fuck1lanetype) : fuck3nat
  ;; test.spectec:591.1-591.30
  def $lsizenn{lt : fuck1lanetype}(lt) = $lsize(lt)

;; test.spectec:589.1-589.63
def $lsizenn1(lanetype : fuck1lanetype) : fuck3nat
  ;; test.spectec:592.1-592.31
  def $lsizenn1{lt : fuck1lanetype}(lt) = $lsize(lt)

;; test.spectec:590.1-590.63
def $lsizenn2(lanetype : fuck1lanetype) : fuck3nat
  ;; test.spectec:593.1-593.31
  def $lsizenn2{lt : fuck1lanetype}(lt) = $lsize(lt)

;; test.spectec:595.1-595.83
def $jsizenn(Jnn : fuck1Jnn) : fuck3nat
  ;; test.spectec:596.1-596.32
  def $jsizenn{Jnn : fuck1Jnn}(Jnn) = $lsize((Jnn : fuck1Jnn <: fuck1lanetype))

;; test.spectec:598.1-598.42
def $inv_jsizenn(nat : fuck3nat) : fuck1Jnn
  ;; test.spectec:599.1-599.36
  def $inv_jsizenn{n : fuck3nat}(n) = $inv_jsize(n)

;; test.spectec:604.1-604.56
def $lunpack(lanetype : fuck1lanetype) : fuck1numtype
  ;; test.spectec:605.1-605.32
  def $lunpack{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1lanetype)) = numtype
  ;; test.spectec:606.1-606.29
  def $lunpack{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1lanetype)) = I32_numtype

;; test.spectec:608.1-608.35
def $unpack(storagetype : fuck1storagetype) : fuck1valtype
  ;; test.spectec:609.1-609.31
  def $unpack{valtype : fuck1valtype}((valtype : fuck1valtype <: fuck1storagetype)) = valtype
  ;; test.spectec:610.1-610.28
  def $unpack{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1storagetype)) = I32_valtype

;; test.spectec:608.6-608.13
relation unpack_is_wf: `%%`fuck5(storagetype : fuck1storagetype, ret_val : fuck1valtype)
  ;; test.spectec:608.6-608.13
  rule unpack_is_wf_0{storagetype : fuck1storagetype, ret_val : fuck1valtype}:
    `%%`(storagetype, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- if (ret_val = $unpack(storagetype))
    -- wf_valtype: `%`(ret_val)

;; test.spectec:612.1-612.73
def $nunpack(storagetype : fuck1storagetype) : fuck1numtype
  ;; test.spectec:613.1-613.32
  def $nunpack{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1storagetype)) = numtype
  ;; test.spectec:614.1-614.29
  def $nunpack{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1storagetype)) = I32_numtype

;; test.spectec:616.1-616.73
def $vunpack(storagetype : fuck1storagetype) : fuck1vectype
  ;; test.spectec:617.1-617.32
  def $vunpack{vectype : fuck1vectype}((vectype : fuck1vectype <: fuck1storagetype)) = vectype

;; test.spectec:619.1-619.74
def $cunpack(storagetype : fuck1storagetype) : fuck1consttype
  ;; test.spectec:620.1-620.36
  def $cunpack{consttype : fuck1consttype}((consttype : fuck1consttype <: fuck1storagetype)) = consttype
  ;; test.spectec:621.1-621.29
  def $cunpack{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1storagetype)) = I32_consttype
  ;; test.spectec:622.1-622.44
  def $cunpack{lanetype : fuck1lanetype}((lanetype : fuck1lanetype <: fuck1storagetype)) = ($lunpack(lanetype) : fuck1numtype <: fuck1consttype)

;; test.spectec:627.1-627.90
def $minat(addrtype : fuck1addrtype, addrtype : fuck1addrtype) : fuck1addrtype
  ;; test.spectec:628.1-628.64
  def $minat{at_1 : fuck1addrtype, at_2 : fuck1addrtype}(at_1, at_2) = (if ($size((at_1 : fuck1addrtype <: fuck1numtype)) <= $size((at_2 : fuck1addrtype <: fuck1numtype))) then at_1 else at_2)

;; test.spectec:631.1-631.82
def $diffrt(reftype : fuck1reftype, reftype : fuck1reftype) : fuck1reftype
  ;; test.spectec:632.1-632.62
  def $diffrt{`null_1?` : fuck6fuck1null?, ht_1 : fuck1heaptype, ht_2 : fuck1heaptype}(REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(?(NULL_null), ht_2)) = REF_reftype(?(), ht_1)
  ;; test.spectec:633.1-633.65
  def $diffrt{`null_1?` : fuck6fuck1null?, ht_1 : fuck1heaptype, ht_2 : fuck1heaptype}(REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(?(), ht_2)) = REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1)

;; test.spectec:631.6-631.13
relation diffrt_is_wf: `%%%`fuck5(reftype : fuck1reftype, reftype_0 : fuck1reftype, ret_val : fuck1reftype)
  ;; test.spectec:631.6-631.13
  rule diffrt_is_wf_0{reftype : fuck1reftype, reftype_0 : fuck1reftype, ret_val : fuck1reftype}:
    `%%%`(reftype, reftype_0, ret_val)
    -- wf_reftype: `%`(reftype)
    -- wf_reftype: `%`(reftype_0)
    -- if (ret_val = $diffrt(reftype, reftype_0))
    -- wf_reftype: `%`(ret_val)

;; test.spectec:636.1-636.63
def $as_deftype(typeuse : fuck1typeuse) : fuck1deftype
  ;; test.spectec:637.1-637.25
  def $as_deftype{dt : fuck1deftype}((dt : fuck1deftype <: fuck1typeuse)) = dt

;; test.spectec:644.1-644.87
rec {

;; test.spectec:644.1-644.87
def $tagsxt(fuck6fuck1externtype*) : fuck6fuck1tagtype*
  ;; test.spectec:650.1-650.23
  def $tagsxt([]) = []
  ;; test.spectec:651.1-651.44
  def $tagsxt{jt : fuck1typeuse, `xt*` : fuck6fuck1externtype*}([TAG_externtype(jt)] ++ xt*{xt <- `xt*`}) = [jt] ++ $tagsxt(xt*{xt <- `xt*`})
  ;; test.spectec:652.1-652.57
  def $tagsxt{externtype : fuck1externtype, `xt*` : fuck6fuck1externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tagsxt(xt*{xt <- `xt*`})
}

;; test.spectec:644.1-644.87
rec {

;; test.spectec:644.6-644.13
relation tagsxt_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1tagtype*)
  ;; test.spectec:644.6-644.13
  rule tagsxt_is_wf_0{`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1tagtype*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externtype: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $tagsxt(`var_0*`))
    -- (wf_typeuse: `%`(ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:645.1-645.90
rec {

;; test.spectec:645.1-645.90
def $globalsxt(fuck6fuck1externtype*) : fuck6fuck1globaltype*
  ;; test.spectec:654.1-654.26
  def $globalsxt([]) = []
  ;; test.spectec:655.1-655.53
  def $globalsxt{gt : fuck1globaltype, `xt*` : fuck6fuck1externtype*}([GLOBAL_externtype(gt)] ++ xt*{xt <- `xt*`}) = [gt] ++ $globalsxt(xt*{xt <- `xt*`})
  ;; test.spectec:656.1-656.63
  def $globalsxt{externtype : fuck1externtype, `xt*` : fuck6fuck1externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $globalsxt(xt*{xt <- `xt*`})
}

;; test.spectec:645.1-645.90
rec {

;; test.spectec:645.6-645.16
relation globalsxt_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1globaltype*)
  ;; test.spectec:645.6-645.16
  rule globalsxt_is_wf_0{`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1globaltype*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externtype: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $globalsxt(`var_0*`))
    -- (wf_globaltype: `%`(ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:646.1-646.87
rec {

;; test.spectec:646.1-646.87
def $memsxt(fuck6fuck1externtype*) : fuck6fuck1memtype*
  ;; test.spectec:658.1-658.23
  def $memsxt([]) = []
  ;; test.spectec:659.1-659.44
  def $memsxt{mt : fuck1memtype, `xt*` : fuck6fuck1externtype*}([MEM_externtype(mt)] ++ xt*{xt <- `xt*`}) = [mt] ++ $memsxt(xt*{xt <- `xt*`})
  ;; test.spectec:660.1-660.57
  def $memsxt{externtype : fuck1externtype, `xt*` : fuck6fuck1externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $memsxt(xt*{xt <- `xt*`})
}

;; test.spectec:646.1-646.87
rec {

;; test.spectec:646.6-646.13
relation memsxt_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1memtype*)
  ;; test.spectec:646.6-646.13
  rule memsxt_is_wf_0{`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1memtype*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externtype: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $memsxt(`var_0*`))
    -- (wf_memtype: `%`(ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:647.1-647.89
rec {

;; test.spectec:647.1-647.89
def $tablesxt(fuck6fuck1externtype*) : fuck6fuck1tabletype*
  ;; test.spectec:662.1-662.25
  def $tablesxt([]) = []
  ;; test.spectec:663.1-663.50
  def $tablesxt{tt : fuck1tabletype, `xt*` : fuck6fuck1externtype*}([TABLE_externtype(tt)] ++ xt*{xt <- `xt*`}) = [tt] ++ $tablesxt(xt*{xt <- `xt*`})
  ;; test.spectec:664.1-664.61
  def $tablesxt{externtype : fuck1externtype, `xt*` : fuck6fuck1externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tablesxt(xt*{xt <- `xt*`})
}

;; test.spectec:647.1-647.89
rec {

;; test.spectec:647.6-647.15
relation tablesxt_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1tabletype*)
  ;; test.spectec:647.6-647.15
  rule tablesxt_is_wf_0{`var_0*` : fuck6fuck1externtype*, `ret_val*` : fuck6fuck1tabletype*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externtype: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $tablesxt(`var_0*`))
    -- (wf_tabletype: `%`(ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:648.1-648.88
rec {

;; test.spectec:648.1-648.88
def $funcsxt(fuck6fuck1externtype*) : fuck6fuck1deftype*
  ;; test.spectec:666.1-666.24
  def $funcsxt([]) = []
  ;; test.spectec:667.1-667.47
  def $funcsxt{dt : fuck1deftype, `xt*` : fuck6fuck1externtype*}([FUNC_externtype((dt : fuck1deftype <: fuck1typeuse))] ++ xt*{xt <- `xt*`}) = [dt] ++ $funcsxt(xt*{xt <- `xt*`})
  ;; test.spectec:668.1-668.59
  def $funcsxt{externtype : fuck1externtype, `xt*` : fuck6fuck1externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $funcsxt(xt*{xt <- `xt*`})
}

;; test.spectec:673.1-673.126
rec {

;; test.spectec:673.1-673.126
def $subst_typevar(typevar : fuck1typevar, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1typeuse
  ;; test.spectec:701.1-701.38
  def $subst_typevar{tv : fuck1typevar}(tv, [], []) = (tv : fuck1typevar <: fuck1typeuse)
  ;; test.spectec:702.1-702.95
  def $subst_typevar{tv : fuck1typevar, tv_1 : fuck1typevar, `tv'*` : fuck6fuck1typevar*, tu_1 : fuck1typeuse, `tu'*` : fuck6fuck1typeuse*}(tv, [tv_1] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`}) = (if (tv = tv_1) then tu_1 else $subst_typevar(tv, tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}))
}

;; test.spectec:673.1-673.126
rec {

;; test.spectec:673.6-673.20
relation subst_typevar_is_wf: `%%%%`fuck5(typevar : fuck1typevar, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1typeuse)
  ;; test.spectec:673.6-673.20
  rule subst_typevar_is_wf_0{typevar : fuck1typevar, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1typeuse}:
    `%%%%`(typevar, `var_0*`, `var_1*`, ret_val)
    -- wf_typevar: `%`(typevar)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_typevar(typevar, `var_0*`, `var_1*`))
    -- wf_typeuse: `%`(ret_val)
}

;; test.spectec:737.1-737.87
rec {

;; test.spectec:737.1-737.87
def $minus_recs(fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck5(fuck6fuck1typevar*, fuck6fuck1typeuse*)
  ;; test.spectec:738.1-738.39
  def $minus_recs([], []) = ([], [])
  ;; test.spectec:739.1-739.63
  def $minus_recs{n : fuck3nat, `tv*` : fuck6fuck1typevar*, tu_1 : fuck1typeuse, `tu*` : fuck6fuck1typeuse*}([REC_typevar(n)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  ;; test.spectec:740.1-741.45
  def $minus_recs{x : fuck1uN, `tv*` : fuck6fuck1typevar*, tu_1 : fuck1typeuse, `tu*` : fuck6fuck1typeuse*}([_IDX_typevar(x)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = ([_IDX_typevar(x)] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`})
    -- let{`tv'*` : fuck6fuck1typevar*, `tu'*` : fuck6fuck1typeuse*} (tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
}

;; test.spectec:737.1-737.87
rec {

;; test.spectec:737.6-737.17
relation minus_recs_is_wf: `%%%`fuck5(`var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck5(fuck6fuck1typevar*, fuck6fuck1typeuse*))
  ;; test.spectec:737.6-737.17
  rule minus_recs_is_wf_0{`var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck5(fuck6fuck1typevar*, fuck6fuck1typeuse*)}:
    `%%%`(`var_0*`, `var_1*`, ret_val)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $minus_recs(`var_0*`, `var_1*`))
    -- (wf_typevar: `%`(iter))*{iter <- ret_val.0}
    -- (wf_typeuse: `%`(iter))*{iter <- ret_val.1}
}

;; test.spectec:683.1-683.112
def $subst_packtype(packtype : fuck1packtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1packtype
  ;; test.spectec:723.1-723.39
  def $subst_packtype{pt : fuck1packtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(pt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = pt

;; test.spectec:677.1-677.112
def $subst_numtype(numtype : fuck1numtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1numtype
  ;; test.spectec:709.1-709.38
  def $subst_numtype{nt : fuck1numtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(nt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = nt

;; test.spectec:678.1-678.112
def $subst_vectype(vectype : fuck1vectype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1vectype
  ;; test.spectec:710.1-710.38
  def $subst_vectype{vt : fuck1vectype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(vt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = vt

;; test.spectec:674.1-690.112
rec {

;; test.spectec:674.1-674.112
def $subst_typeuse(typeuse : fuck1typeuse, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1typeuse
  ;; test.spectec:705.1-705.66
  def $subst_typeuse{tv' : fuck1typevar, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((tv' : fuck1typevar <: fuck1typeuse), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = $subst_typevar(tv', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  ;; test.spectec:706.1-706.64
  def $subst_typeuse{dt : fuck1deftype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((dt : fuck1deftype <: fuck1typeuse), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_deftype(dt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1deftype <: fuck1typeuse)

;; test.spectec:679.1-679.112
def $subst_heaptype(heaptype : fuck1heaptype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1heaptype
  ;; test.spectec:712.1-712.67
  def $subst_heaptype{tv' : fuck1typevar, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((tv' : fuck1typevar <: fuck1heaptype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_typevar(tv', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1typeuse <: fuck1heaptype)
  ;; test.spectec:713.1-713.65
  def $subst_heaptype{dt : fuck1deftype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((dt : fuck1deftype <: fuck1heaptype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_deftype(dt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1deftype <: fuck1heaptype)
  ;; test.spectec:714.1-714.53
  def $subst_heaptype{ht : fuck1heaptype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(ht, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ht

;; test.spectec:680.1-680.112
def $subst_reftype(reftype : fuck1reftype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1reftype
  ;; test.spectec:716.1-716.87
  def $subst_reftype{`null?` : fuck6fuck1null?, ht : fuck1heaptype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(REF_reftype(null?{null <- `null?`}, ht), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = REF_reftype(null?{null <- `null?`}, $subst_heaptype(ht, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:681.1-681.112
def $subst_valtype(valtype : fuck1valtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1valtype
  ;; test.spectec:718.1-718.64
  def $subst_valtype{nt : fuck1numtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((nt : fuck1numtype <: fuck1valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_numtype(nt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1numtype <: fuck1valtype)
  ;; test.spectec:719.1-719.64
  def $subst_valtype{vt : fuck1vectype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((vt : fuck1vectype <: fuck1valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_vectype(vt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1vectype <: fuck1valtype)
  ;; test.spectec:720.1-720.64
  def $subst_valtype{rt : fuck1reftype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((rt : fuck1reftype <: fuck1valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_reftype(rt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1reftype <: fuck1valtype)
  ;; test.spectec:721.1-721.40
  def $subst_valtype{`tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(BOT_valtype, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = BOT_valtype

;; test.spectec:684.1-684.112
def $subst_storagetype(storagetype : fuck1storagetype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1storagetype
  ;; test.spectec:725.1-725.66
  def $subst_storagetype{t : fuck1valtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((t : fuck1valtype <: fuck1storagetype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_valtype(t, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1valtype <: fuck1storagetype)
  ;; test.spectec:726.1-726.69
  def $subst_storagetype{pt : fuck1packtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}((pt : fuck1packtype <: fuck1storagetype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_packtype(pt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : fuck1packtype <: fuck1storagetype)

;; test.spectec:685.1-685.112
def $subst_fieldtype(fieldtype : fuck1fieldtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1fieldtype
  ;; test.spectec:728.1-728.82
  def $subst_fieldtype{`mut?` : fuck6fuck1mut?, zt : fuck1storagetype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(`%%`_fieldtype(mut?{mut <- `mut?`}, zt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%`_fieldtype(mut?{mut <- `mut?`}, $subst_storagetype(zt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:687.1-687.112
def $subst_comptype(comptype : fuck1comptype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1comptype
  ;; test.spectec:730.1-730.85
  def $subst_comptype{`ft*` : fuck6fuck1fieldtype*, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = STRUCT_comptype(`%`_list($subst_fieldtype(ft, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{ft <- `ft*`}))
  ;; test.spectec:731.1-731.81
  def $subst_comptype{ft : fuck1fieldtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(ARRAY_comptype(ft), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ARRAY_comptype($subst_fieldtype(ft, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:732.1-732.123
  def $subst_comptype{`t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `FUNC%->%`_comptype(`%`_resulttype($subst_valtype(t_1, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{t_1 <- `t_1*`}), `%`_resulttype($subst_valtype(t_2, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{t_2 <- `t_2*`}))

;; test.spectec:688.1-688.112
def $subst_subtype(subtype : fuck1subtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1subtype
  ;; test.spectec:734.1-735.74
  def $subst_subtype{`final?` : fuck6fuck1final?, `tu'*` : fuck6fuck1typeuse*, ct : fuck1comptype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(SUB_subtype(final?{final <- `final?`}, tu'*{tu' <- `tu'*`}, ct), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = SUB_subtype(final?{final <- `final?`}, $subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{tu' <- `tu'*`}, $subst_comptype(ct, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:689.1-689.112
def $subst_rectype(rectype : fuck1rectype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1rectype
  ;; test.spectec:743.1-744.45
  def $subst_rectype{`st*` : fuck6fuck1subtype*, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(REC_rectype(`%`_list(st*{st <- `st*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = REC_rectype(`%`_list($subst_subtype(st, tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`})*{st <- `st*`}))
    -- let{`tv'*` : fuck6fuck1typevar*, `tu'*` : fuck6fuck1typeuse*} (tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})

;; test.spectec:690.1-690.112
def $subst_deftype(deftype : fuck1deftype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1deftype
  ;; test.spectec:749.1-749.80
  def $subst_deftype{qt : fuck1rectype, i : fuck3nat, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(_DEF_deftype(qt, i), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = _DEF_deftype($subst_rectype(qt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}), i)
}

;; test.spectec:674.1-690.112
rec {

;; test.spectec:674.6-674.20
relation subst_typeuse_is_wf: `%%%%`fuck5(typeuse : fuck1typeuse, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1typeuse)
  ;; test.spectec:674.6-674.20
  rule subst_typeuse_is_wf_0{typeuse : fuck1typeuse, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1typeuse}:
    `%%%%`(typeuse, `var_0*`, `var_1*`, ret_val)
    -- wf_typeuse: `%`(typeuse)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_typeuse(typeuse, `var_0*`, `var_1*`))
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:679.6-679.21
relation subst_heaptype_is_wf: `%%%%`fuck5(heaptype : fuck1heaptype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1heaptype)
  ;; test.spectec:679.6-679.21
  rule subst_heaptype_is_wf_0{heaptype : fuck1heaptype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1heaptype}:
    `%%%%`(heaptype, `var_0*`, `var_1*`, ret_val)
    -- wf_heaptype: `%`(heaptype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_heaptype(heaptype, `var_0*`, `var_1*`))
    -- wf_heaptype: `%`(ret_val)

;; test.spectec:680.6-680.20
relation subst_reftype_is_wf: `%%%%`fuck5(reftype : fuck1reftype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1reftype)
  ;; test.spectec:680.6-680.20
  rule subst_reftype_is_wf_0{reftype : fuck1reftype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1reftype}:
    `%%%%`(reftype, `var_0*`, `var_1*`, ret_val)
    -- wf_reftype: `%`(reftype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_reftype(reftype, `var_0*`, `var_1*`))
    -- wf_reftype: `%`(ret_val)

;; test.spectec:681.6-681.20
relation subst_valtype_is_wf: `%%%%`fuck5(valtype : fuck1valtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1valtype)
  ;; test.spectec:681.6-681.20
  rule subst_valtype_is_wf_0{valtype : fuck1valtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1valtype}:
    `%%%%`(valtype, `var_0*`, `var_1*`, ret_val)
    -- wf_valtype: `%`(valtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_valtype(valtype, `var_0*`, `var_1*`))
    -- wf_valtype: `%`(ret_val)

;; test.spectec:684.6-684.24
relation subst_storagetype_is_wf: `%%%%`fuck5(storagetype : fuck1storagetype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1storagetype)
  ;; test.spectec:684.6-684.24
  rule subst_storagetype_is_wf_0{storagetype : fuck1storagetype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1storagetype}:
    `%%%%`(storagetype, `var_0*`, `var_1*`, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_storagetype(storagetype, `var_0*`, `var_1*`))
    -- wf_storagetype: `%`(ret_val)

;; test.spectec:685.6-685.22
relation subst_fieldtype_is_wf: `%%%%`fuck5(fieldtype : fuck1fieldtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1fieldtype)
  ;; test.spectec:685.6-685.22
  rule subst_fieldtype_is_wf_0{fieldtype : fuck1fieldtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1fieldtype}:
    `%%%%`(fieldtype, `var_0*`, `var_1*`, ret_val)
    -- wf_fieldtype: `%`(fieldtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_fieldtype(fieldtype, `var_0*`, `var_1*`))
    -- wf_fieldtype: `%`(ret_val)

;; test.spectec:687.6-687.21
relation subst_comptype_is_wf: `%%%%`fuck5(comptype : fuck1comptype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1comptype)
  ;; test.spectec:687.6-687.21
  rule subst_comptype_is_wf_0{comptype : fuck1comptype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1comptype}:
    `%%%%`(comptype, `var_0*`, `var_1*`, ret_val)
    -- wf_comptype: `%`(comptype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_comptype(comptype, `var_0*`, `var_1*`))
    -- wf_comptype: `%`(ret_val)

;; test.spectec:688.6-688.20
relation subst_subtype_is_wf: `%%%%`fuck5(subtype : fuck1subtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1subtype)
  ;; test.spectec:688.6-688.20
  rule subst_subtype_is_wf_0{subtype : fuck1subtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1subtype}:
    `%%%%`(subtype, `var_0*`, `var_1*`, ret_val)
    -- wf_subtype: `%`(subtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_subtype(subtype, `var_0*`, `var_1*`))
    -- wf_subtype: `%`(ret_val)
}

;; test.spectec:676.1-676.112
def $subst_addrtype(addrtype : fuck1addrtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1addrtype
  ;; test.spectec:708.1-708.39
  def $subst_addrtype{at : fuck1addrtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(at, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = at

;; test.spectec:692.1-692.112
def $subst_tagtype(tagtype : fuck1tagtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1tagtype
  ;; test.spectec:751.1-751.66
  def $subst_tagtype{tu' : fuck1typeuse, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = $subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})

;; test.spectec:692.6-692.20
relation subst_tagtype_is_wf: `%%%%`fuck5(tagtype : fuck1tagtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1tagtype)
  ;; test.spectec:692.6-692.20
  rule subst_tagtype_is_wf_0{tagtype : fuck1tagtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1tagtype}:
    `%%%%`(tagtype, `var_0*`, `var_1*`, ret_val)
    -- wf_typeuse: `%`(tagtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_tagtype(tagtype, `var_0*`, `var_1*`))
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:693.1-693.112
def $subst_globaltype(globaltype : fuck1globaltype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1globaltype
  ;; test.spectec:752.1-752.77
  def $subst_globaltype{`mut?` : fuck6fuck1mut?, t : fuck1valtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(`%%`_globaltype(mut?{mut <- `mut?`}, t), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%`_globaltype(mut?{mut <- `mut?`}, $subst_valtype(t, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:693.6-693.23
relation subst_globaltype_is_wf: `%%%%`fuck5(globaltype : fuck1globaltype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1globaltype)
  ;; test.spectec:693.6-693.23
  rule subst_globaltype_is_wf_0{globaltype : fuck1globaltype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1globaltype}:
    `%%%%`(globaltype, `var_0*`, `var_1*`, ret_val)
    -- wf_globaltype: `%`(globaltype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_globaltype(globaltype, `var_0*`, `var_1*`))
    -- wf_globaltype: `%`(ret_val)

;; test.spectec:694.1-694.112
def $subst_memtype(memtype : fuck1memtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1memtype
  ;; test.spectec:753.1-753.58
  def $subst_memtype{at : fuck1addrtype, lim : fuck1limits, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(`%%PAGE`_memtype(at, lim), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%PAGE`_memtype(at, lim)

;; test.spectec:694.6-694.20
relation subst_memtype_is_wf: `%%%%`fuck5(memtype : fuck1memtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1memtype)
  ;; test.spectec:694.6-694.20
  rule subst_memtype_is_wf_0{memtype : fuck1memtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1memtype}:
    `%%%%`(memtype, `var_0*`, `var_1*`, ret_val)
    -- wf_memtype: `%`(memtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_memtype(memtype, `var_0*`, `var_1*`))
    -- wf_memtype: `%`(ret_val)

;; test.spectec:695.1-695.112
def $subst_tabletype(tabletype : fuck1tabletype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1tabletype
  ;; test.spectec:754.1-754.82
  def $subst_tabletype{at : fuck1addrtype, lim : fuck1limits, rt : fuck1reftype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(`%%%`_tabletype(at, lim, rt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%%`_tabletype(at, lim, $subst_reftype(rt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:695.6-695.22
relation subst_tabletype_is_wf: `%%%%`fuck5(tabletype : fuck1tabletype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1tabletype)
  ;; test.spectec:695.6-695.22
  rule subst_tabletype_is_wf_0{tabletype : fuck1tabletype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1tabletype}:
    `%%%%`(tabletype, `var_0*`, `var_1*`, ret_val)
    -- wf_tabletype: `%`(tabletype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_tabletype(tabletype, `var_0*`, `var_1*`))
    -- wf_tabletype: `%`(ret_val)

;; test.spectec:697.1-697.112
def $subst_externtype(externtype : fuck1externtype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1externtype
  ;; test.spectec:756.1-756.77
  def $subst_externtype{jt : fuck1typeuse, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(TAG_externtype(jt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = TAG_externtype($subst_tagtype(jt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:757.1-757.86
  def $subst_externtype{gt : fuck1globaltype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(GLOBAL_externtype(gt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = GLOBAL_externtype($subst_globaltype(gt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:758.1-758.83
  def $subst_externtype{tt : fuck1tabletype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(TABLE_externtype(tt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = TABLE_externtype($subst_tabletype(tt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:759.1-759.77
  def $subst_externtype{mt : fuck1memtype, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(MEM_externtype(mt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = MEM_externtype($subst_memtype(mt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:760.1-760.81
  def $subst_externtype{tu' : fuck1typeuse, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(FUNC_externtype(tu'), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = FUNC_externtype($subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:697.6-697.23
relation subst_externtype_is_wf: `%%%%`fuck5(externtype : fuck1externtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1externtype)
  ;; test.spectec:697.6-697.23
  rule subst_externtype_is_wf_0{externtype : fuck1externtype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1externtype}:
    `%%%%`(externtype, `var_0*`, `var_1*`, ret_val)
    -- wf_externtype: `%`(externtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_externtype(externtype, `var_0*`, `var_1*`))
    -- wf_externtype: `%`(ret_val)

;; test.spectec:698.1-698.112
def $subst_moduletype(moduletype : fuck1moduletype, fuck6fuck1typevar*, fuck6fuck1typeuse*) : fuck1moduletype
  ;; test.spectec:762.1-762.123
  def $subst_moduletype{`xt_1*` : fuck6fuck1externtype*, `xt_2*` : fuck6fuck1externtype*, `tv*` : fuck6fuck1typevar*, `tu*` : fuck6fuck1typeuse*}(`%->%`_moduletype(xt_1*{xt_1 <- `xt_1*`}, xt_2*{xt_2 <- `xt_2*`}), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%->%`_moduletype($subst_externtype(xt_1, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{xt_1 <- `xt_1*`}, $subst_externtype(xt_2, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{xt_2 <- `xt_2*`})

;; test.spectec:698.6-698.23
relation subst_moduletype_is_wf: `%%%%`fuck5(moduletype : fuck1moduletype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1moduletype)
  ;; test.spectec:698.6-698.23
  rule subst_moduletype_is_wf_0{moduletype : fuck1moduletype, `var_0*` : fuck6fuck1typevar*, `var_1*` : fuck6fuck1typeuse*, ret_val : fuck1moduletype}:
    `%%%%`(moduletype, `var_0*`, `var_1*`, ret_val)
    -- wf_moduletype: `%`(moduletype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $subst_moduletype(moduletype, `var_0*`, `var_1*`))
    -- wf_moduletype: `%`(ret_val)

;; test.spectec:767.1-767.94
def $subst_all_valtype(valtype : fuck1valtype, fuck6fuck1typeuse*) : fuck1valtype
  ;; test.spectec:777.1-777.74
  def $subst_all_valtype{t : fuck1valtype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(t, tu^n{tu <- `tu*`}) = $subst_valtype(t, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:767.6-767.24
relation subst_all_valtype_is_wf: `%%%`fuck5(valtype : fuck1valtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1valtype)
  ;; test.spectec:767.6-767.24
  rule subst_all_valtype_is_wf_0{valtype : fuck1valtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1valtype}:
    `%%%`(valtype, `var_0*`, ret_val)
    -- wf_valtype: `%`(valtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_valtype(valtype, `var_0*`))
    -- wf_valtype: `%`(ret_val)

;; test.spectec:768.1-768.94
def $subst_all_reftype(reftype : fuck1reftype, fuck6fuck1typeuse*) : fuck1reftype
  ;; test.spectec:778.1-778.76
  def $subst_all_reftype{rt : fuck1reftype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(rt, tu^n{tu <- `tu*`}) = $subst_reftype(rt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:768.6-768.24
relation subst_all_reftype_is_wf: `%%%`fuck5(reftype : fuck1reftype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1reftype)
  ;; test.spectec:768.6-768.24
  rule subst_all_reftype_is_wf_0{reftype : fuck1reftype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1reftype}:
    `%%%`(reftype, `var_0*`, ret_val)
    -- wf_reftype: `%`(reftype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_reftype(reftype, `var_0*`))
    -- wf_reftype: `%`(ret_val)

;; test.spectec:769.1-769.94
def $subst_all_deftype(deftype : fuck1deftype, fuck6fuck1typeuse*) : fuck1deftype
  ;; test.spectec:779.1-779.76
  def $subst_all_deftype{dt : fuck1deftype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(dt, tu^n{tu <- `tu*`}) = $subst_deftype(dt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:770.1-770.94
def $subst_all_tagtype(tagtype : fuck1tagtype, fuck6fuck1typeuse*) : fuck1tagtype
  ;; test.spectec:780.1-780.76
  def $subst_all_tagtype{jt : fuck1typeuse, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(jt, tu^n{tu <- `tu*`}) = $subst_tagtype(jt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:770.6-770.24
relation subst_all_tagtype_is_wf: `%%%`fuck5(tagtype : fuck1tagtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1tagtype)
  ;; test.spectec:770.6-770.24
  rule subst_all_tagtype_is_wf_0{tagtype : fuck1tagtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1tagtype}:
    `%%%`(tagtype, `var_0*`, ret_val)
    -- wf_typeuse: `%`(tagtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_tagtype(tagtype, `var_0*`))
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:771.1-771.103
def $subst_all_globaltype(globaltype : fuck1globaltype, fuck6fuck1typeuse*) : fuck1globaltype
  ;; test.spectec:781.1-781.82
  def $subst_all_globaltype{gt : fuck1globaltype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(gt, tu^n{tu <- `tu*`}) = $subst_globaltype(gt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:771.6-771.27
relation subst_all_globaltype_is_wf: `%%%`fuck5(globaltype : fuck1globaltype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1globaltype)
  ;; test.spectec:771.6-771.27
  rule subst_all_globaltype_is_wf_0{globaltype : fuck1globaltype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1globaltype}:
    `%%%`(globaltype, `var_0*`, ret_val)
    -- wf_globaltype: `%`(globaltype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_globaltype(globaltype, `var_0*`))
    -- wf_globaltype: `%`(ret_val)

;; test.spectec:772.1-772.94
def $subst_all_memtype(memtype : fuck1memtype, fuck6fuck1typeuse*) : fuck1memtype
  ;; test.spectec:782.1-782.76
  def $subst_all_memtype{mt : fuck1memtype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(mt, tu^n{tu <- `tu*`}) = $subst_memtype(mt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:772.6-772.24
relation subst_all_memtype_is_wf: `%%%`fuck5(memtype : fuck1memtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1memtype)
  ;; test.spectec:772.6-772.24
  rule subst_all_memtype_is_wf_0{memtype : fuck1memtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1memtype}:
    `%%%`(memtype, `var_0*`, ret_val)
    -- wf_memtype: `%`(memtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_memtype(memtype, `var_0*`))
    -- wf_memtype: `%`(ret_val)

;; test.spectec:773.1-773.100
def $subst_all_tabletype(tabletype : fuck1tabletype, fuck6fuck1typeuse*) : fuck1tabletype
  ;; test.spectec:783.1-783.80
  def $subst_all_tabletype{tt : fuck1tabletype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(tt, tu^n{tu <- `tu*`}) = $subst_tabletype(tt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:773.6-773.26
relation subst_all_tabletype_is_wf: `%%%`fuck5(tabletype : fuck1tabletype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1tabletype)
  ;; test.spectec:773.6-773.26
  rule subst_all_tabletype_is_wf_0{tabletype : fuck1tabletype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1tabletype}:
    `%%%`(tabletype, `var_0*`, ret_val)
    -- wf_tabletype: `%`(tabletype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_tabletype(tabletype, `var_0*`))
    -- wf_tabletype: `%`(ret_val)

;; test.spectec:774.1-774.103
def $subst_all_externtype(externtype : fuck1externtype, fuck6fuck1typeuse*) : fuck1externtype
  ;; test.spectec:784.1-784.82
  def $subst_all_externtype{xt : fuck1externtype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(xt, tu^n{tu <- `tu*`}) = $subst_externtype(xt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:774.6-774.27
relation subst_all_externtype_is_wf: `%%%`fuck5(externtype : fuck1externtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1externtype)
  ;; test.spectec:774.6-774.27
  rule subst_all_externtype_is_wf_0{externtype : fuck1externtype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1externtype}:
    `%%%`(externtype, `var_0*`, ret_val)
    -- wf_externtype: `%`(externtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_externtype(externtype, `var_0*`))
    -- wf_externtype: `%`(ret_val)

;; test.spectec:775.1-775.103
def $subst_all_moduletype(moduletype : fuck1moduletype, fuck6fuck1typeuse*) : fuck1moduletype
  ;; test.spectec:785.1-785.84
  def $subst_all_moduletype{mmt : fuck1moduletype, n : fuck3nat, `tu*` : fuck6fuck1typeuse*, i : fuck3nat}(mmt, tu^n{tu <- `tu*`}) = $subst_moduletype(mmt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:775.6-775.27
relation subst_all_moduletype_is_wf: `%%%`fuck5(moduletype : fuck1moduletype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1moduletype)
  ;; test.spectec:775.6-775.27
  rule subst_all_moduletype_is_wf_0{moduletype : fuck1moduletype, `var_0*` : fuck6fuck1typeuse*, ret_val : fuck1moduletype}:
    `%%%`(moduletype, `var_0*`, ret_val)
    -- wf_moduletype: `%`(moduletype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $subst_all_moduletype(moduletype, `var_0*`))
    -- wf_moduletype: `%`(ret_val)

;; test.spectec:787.1-787.97
rec {

;; test.spectec:787.1-787.97
def $subst_all_deftypes(fuck6fuck1deftype*, fuck6fuck1typeuse*) : fuck6fuck1deftype*
  ;; test.spectec:788.1-788.40
  def $subst_all_deftypes{`tu*` : fuck6fuck1typeuse*}([], tu*{tu <- `tu*`}) = []
  ;; test.spectec:789.1-789.101
  def $subst_all_deftypes{dt_1 : fuck1deftype, `dt*` : fuck6fuck1deftype*, `tu*` : fuck6fuck1typeuse*}([dt_1] ++ dt*{dt <- `dt*`}, tu*{tu <- `tu*`}) = [$subst_all_deftype(dt_1, tu*{tu <- `tu*`})] ++ $subst_all_deftypes(dt*{dt <- `dt*`}, tu*{tu <- `tu*`})
}

;; test.spectec:794.1-794.88
def $rollrt(typeidx : fuck1typeidx, rectype : fuck1rectype) : fuck1rectype
  ;; test.spectec:799.1-800.32
  def $rollrt{x : fuck1uN, rectype : fuck1rectype, i : fuck3nat, n : fuck3nat, `subtype*` : fuck6fuck1subtype*}(x, rectype) = REC_rectype(`%`_list($subst_subtype(subtype, _IDX_typevar(`%`_typeidx((x!`%`_uN.0 + i)))^(i<n){}, REC_typeuse(i)^(i<n){})^n{subtype <- `subtype*`}))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:795.1-795.90
def $unrollrt(rectype : fuck1rectype) : fuck1rectype
  ;; test.spectec:801.1-802.32
  def $unrollrt{rectype : fuck1rectype, i : fuck3nat, n : fuck3nat, `subtype*` : fuck6fuck1subtype*}(rectype) = REC_rectype(`%`_list($subst_subtype(subtype, REC_typevar(i)^(i<n){}, _DEF_typeuse(rectype, i)^(i<n){})^n{subtype <- `subtype*`}))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:796.1-796.90
def $rolldt(typeidx : fuck1typeidx, rectype : fuck1rectype) : fuck6fuck1deftype*
  ;; test.spectec:804.1-804.100
  def $rolldt{x : fuck1uN, rectype : fuck1rectype, n : fuck3nat, `subtype*` : fuck6fuck1subtype*}(x, rectype) = _DEF_deftype(REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})), i)^(i<n){}
    -- if ($rollrt(x, rectype) = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:797.1-797.90
def $unrolldt(deftype : fuck1deftype) : fuck1subtype
  ;; test.spectec:805.1-805.98
  def $unrolldt{rectype : fuck1rectype, i : fuck3nat}(_DEF_deftype(rectype, i)) = subtype*{subtype <- `subtype*`}[i]
    -- let{`subtype*` : fuck6fuck1subtype*} REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})) = $unrollrt(rectype)

;; test.spectec:797.6-797.15
relation unrolldt_is_wf: `%%`fuck5(deftype : fuck1deftype, ret_val : fuck1subtype)
  ;; test.spectec:797.6-797.15
  rule unrolldt_is_wf_0{deftype : fuck1deftype, ret_val : fuck1subtype}:
    `%%`(deftype, ret_val)
    -- if (ret_val = $unrolldt(deftype))
    -- wf_subtype: `%`(ret_val)

;; test.spectec:810.1-810.36
def $free_addrtype(addrtype : fuck1addrtype) : fuck1free
  ;; test.spectec:840.1-840.34
  def $free_addrtype{addrtype : fuck1addrtype}(addrtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:810.6-810.20
relation free_addrtype_is_wf: `%%`fuck5(addrtype : fuck1addrtype, ret_val : fuck1free)
  ;; test.spectec:810.6-810.20
  rule free_addrtype_is_wf_0{addrtype : fuck1addrtype, ret_val : fuck1free}:
    `%%`(addrtype, ret_val)
    -- if (ret_val = $free_addrtype(addrtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:811.1-811.34
def $free_numtype(numtype : fuck1numtype) : fuck1free
  ;; test.spectec:842.1-842.32
  def $free_numtype{numtype : fuck1numtype}(numtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:811.6-811.19
relation free_numtype_is_wf: `%%`fuck5(numtype : fuck1numtype, ret_val : fuck1free)
  ;; test.spectec:811.6-811.19
  rule free_numtype_is_wf_0{numtype : fuck1numtype, ret_val : fuck1free}:
    `%%`(numtype, ret_val)
    -- if (ret_val = $free_numtype(numtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:812.1-812.36
def $free_packtype(packtype : fuck1packtype) : fuck1free
  ;; test.spectec:844.1-844.34
  def $free_packtype{packtype : fuck1packtype}(packtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:812.6-812.20
relation free_packtype_is_wf: `%%`fuck5(packtype : fuck1packtype, ret_val : fuck1free)
  ;; test.spectec:812.6-812.20
  rule free_packtype_is_wf_0{packtype : fuck1packtype, ret_val : fuck1free}:
    `%%`(packtype, ret_val)
    -- if (ret_val = $free_packtype(packtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:813.1-813.36
def $free_lanetype(lanetype : fuck1lanetype) : fuck1free
  ;; test.spectec:846.1-846.53
  def $free_lanetype{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1lanetype)) = $free_numtype(numtype)
  ;; test.spectec:847.1-847.56
  def $free_lanetype{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1lanetype)) = $free_packtype(packtype)

;; test.spectec:813.6-813.20
relation free_lanetype_is_wf: `%%`fuck5(lanetype : fuck1lanetype, ret_val : fuck1free)
  ;; test.spectec:813.6-813.20
  rule free_lanetype_is_wf_0{lanetype : fuck1lanetype, ret_val : fuck1free}:
    `%%`(lanetype, ret_val)
    -- if (ret_val = $free_lanetype(lanetype))
    -- wf_free: `%`(ret_val)

;; test.spectec:814.1-814.34
def $free_vectype(vectype : fuck1vectype) : fuck1free
  ;; test.spectec:849.1-849.32
  def $free_vectype{vectype : fuck1vectype}(vectype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:814.6-814.19
relation free_vectype_is_wf: `%%`fuck5(vectype : fuck1vectype, ret_val : fuck1free)
  ;; test.spectec:814.6-814.19
  rule free_vectype_is_wf_0{vectype : fuck1vectype, ret_val : fuck1free}:
    `%%`(vectype, ret_val)
    -- if (ret_val = $free_vectype(vectype))
    -- wf_free: `%`(ret_val)

;; test.spectec:815.1-815.38
def $free_consttype(consttype : fuck1consttype) : fuck1free
  ;; test.spectec:851.1-851.54
  def $free_consttype{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1consttype)) = $free_numtype(numtype)
  ;; test.spectec:852.1-852.54
  def $free_consttype{vectype : fuck1vectype}((vectype : fuck1vectype <: fuck1consttype)) = $free_vectype(vectype)

;; test.spectec:815.6-815.21
relation free_consttype_is_wf: `%%`fuck5(consttype : fuck1consttype, ret_val : fuck1free)
  ;; test.spectec:815.6-815.21
  rule free_consttype_is_wf_0{consttype : fuck1consttype, ret_val : fuck1free}:
    `%%`(consttype, ret_val)
    -- if (ret_val = $free_consttype(consttype))
    -- wf_free: `%`(ret_val)

;; test.spectec:816.1-816.42
def $free_absheaptype(absheaptype : fuck1absheaptype) : fuck1free
  ;; test.spectec:854.1-854.40
  def $free_absheaptype{absheaptype : fuck1absheaptype}(absheaptype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:816.6-816.23
relation free_absheaptype_is_wf: `%%`fuck5(absheaptype : fuck1absheaptype, ret_val : fuck1free)
  ;; test.spectec:816.6-816.23
  rule free_absheaptype_is_wf_0{absheaptype : fuck1absheaptype, ret_val : fuck1free}:
    `%%`(absheaptype, ret_val)
    -- if (ret_val = $free_absheaptype(absheaptype))
    -- wf_free: `%`(ret_val)

;; test.spectec:819.1-819.34
def $free_typevar(typevar : fuck1typevar) : fuck1free
  ;; test.spectec:859.1-859.57
  def $free_typevar{typeidx : fuck1uN}(_IDX_typevar(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:860.1-860.30
  def $free_typevar{n : fuck3nat}(REC_typevar(n)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:819.6-819.19
relation free_typevar_is_wf: `%%`fuck5(typevar : fuck1typevar, ret_val : fuck1free)
  ;; test.spectec:819.6-819.19
  rule free_typevar_is_wf_0{typevar : fuck1typevar, ret_val : fuck1free}:
    `%%`(typevar, ret_val)
    -- wf_typevar: `%`(typevar)
    -- if (ret_val = $free_typevar(typevar))
    -- wf_free: `%`(ret_val)

;; test.spectec:817.1-856.34
rec {

;; test.spectec:817.1-817.36
def $free_heaptype(heaptype : fuck1heaptype) : fuck1free
  ;; test.spectec:865.1-865.65
  def $free_heaptype{absheaptype : fuck1absheaptype}((absheaptype : fuck1absheaptype <: fuck1heaptype)) = $free_absheaptype(absheaptype)
  ;; test.spectec:866.1-866.53
  def $free_heaptype{typeuse : fuck1typeuse}((typeuse : fuck1typeuse <: fuck1heaptype)) = $free_typeuse(typeuse)

;; test.spectec:818.1-818.34
def $free_reftype(reftype : fuck1reftype) : fuck1free
  ;; test.spectec:868.1-868.65
  def $free_reftype{`null?` : fuck6fuck1null?, heaptype : fuck1heaptype}(REF_reftype(null?{null <- `null?`}, heaptype)) = $free_heaptype(heaptype)

;; test.spectec:820.1-820.34
def $free_typeuse(typeuse : fuck1typeuse) : fuck1free
  ;; test.spectec:862.1-862.52
  def $free_typeuse{typevar : fuck1typevar}((typevar : fuck1typevar <: fuck1typeuse)) = $free_typevar(typevar)
  ;; test.spectec:863.1-863.52
  def $free_typeuse{deftype : fuck1deftype}((deftype : fuck1deftype <: fuck1typeuse)) = $free_deftype(deftype)

;; test.spectec:821.1-821.34
def $free_valtype(valtype : fuck1valtype) : fuck1free
  ;; test.spectec:870.1-870.52
  def $free_valtype{numtype : fuck1numtype}((numtype : fuck1numtype <: fuck1valtype)) = $free_numtype(numtype)
  ;; test.spectec:871.1-871.52
  def $free_valtype{vectype : fuck1vectype}((vectype : fuck1vectype <: fuck1valtype)) = $free_vectype(vectype)
  ;; test.spectec:872.1-872.52
  def $free_valtype{reftype : fuck1reftype}((reftype : fuck1reftype <: fuck1valtype)) = $free_reftype(reftype)
  ;; test.spectec:873.1-873.28
  def $free_valtype(BOT_valtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:823.1-823.40
def $free_resulttype(resulttype : fuck1resulttype) : fuck1free
  ;; test.spectec:875.1-875.69
  def $free_resulttype{`valtype*` : fuck6fuck1valtype*}(`%`_resulttype(valtype*{valtype <- `valtype*`})) = $free_list($free_valtype(valtype)*{valtype <- `valtype*`})

;; test.spectec:824.1-824.42
def $free_storagetype(storagetype : fuck1storagetype) : fuck1free
  ;; test.spectec:877.1-877.56
  def $free_storagetype{valtype : fuck1valtype}((valtype : fuck1valtype <: fuck1storagetype)) = $free_valtype(valtype)
  ;; test.spectec:878.1-878.59
  def $free_storagetype{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1storagetype)) = $free_packtype(packtype)

;; test.spectec:825.1-825.38
def $free_fieldtype(fieldtype : fuck1fieldtype) : fuck1free
  ;; test.spectec:880.1-880.71
  def $free_fieldtype{`mut?` : fuck6fuck1mut?, storagetype : fuck1storagetype}(`%%`_fieldtype(mut?{mut <- `mut?`}, storagetype)) = $free_storagetype(storagetype)

;; test.spectec:826.1-826.36
def $free_comptype(comptype : fuck1comptype) : fuck1free
  ;; test.spectec:882.1-882.80
  def $free_comptype{`fieldtype*` : fuck6fuck1fieldtype*}(STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))) = $free_list($free_fieldtype(fieldtype)*{fieldtype <- `fieldtype*`})
  ;; test.spectec:883.1-883.65
  def $free_comptype{fieldtype : fuck1fieldtype}(ARRAY_comptype(fieldtype)) = $free_fieldtype(fieldtype)
  ;; test.spectec:884.1-884.121
  def $free_comptype{resulttype_1 : fuck1list(syntax fuck1valtype), resulttype_2 : fuck1list(syntax fuck1valtype)}(`FUNC%->%`_comptype(resulttype_1, resulttype_2)) = $free_resulttype(resulttype_1) +++ $free_resulttype(resulttype_2)

;; test.spectec:827.1-827.34
def $free_subtype(subtype : fuck1subtype) : fuck1free
  ;; test.spectec:886.1-887.66
  def $free_subtype{`final?` : fuck6fuck1final?, `typeuse*` : fuck6fuck1typeuse*, comptype : fuck1comptype}(SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype)) = $free_list($free_typeuse(typeuse)*{typeuse <- `typeuse*`}) +++ $free_comptype(comptype)

;; test.spectec:828.1-828.34
def $free_rectype(rectype : fuck1rectype) : fuck1free
  ;; test.spectec:889.1-889.70
  def $free_rectype{`subtype*` : fuck6fuck1subtype*}(REC_rectype(`%`_list(subtype*{subtype <- `subtype*`}))) = $free_list($free_subtype(subtype)*{subtype <- `subtype*`})

;; test.spectec:856.1-856.34
def $free_deftype(deftype : fuck1deftype) : fuck1free
  ;; test.spectec:857.1-857.59
  def $free_deftype{rectype : fuck1rectype, n : fuck3nat}(_DEF_deftype(rectype, n)) = $free_rectype(rectype)
}

;; test.spectec:817.1-856.34
rec {

;; test.spectec:817.6-817.20
relation free_heaptype_is_wf: `%%`fuck5(heaptype : fuck1heaptype, ret_val : fuck1free)
  ;; test.spectec:817.6-817.20
  rule free_heaptype_is_wf_0{heaptype : fuck1heaptype, ret_val : fuck1free}:
    `%%`(heaptype, ret_val)
    -- wf_heaptype: `%`(heaptype)
    -- if (ret_val = $free_heaptype(heaptype))
    -- wf_free: `%`(ret_val)

;; test.spectec:818.6-818.19
relation free_reftype_is_wf: `%%`fuck5(reftype : fuck1reftype, ret_val : fuck1free)
  ;; test.spectec:818.6-818.19
  rule free_reftype_is_wf_0{reftype : fuck1reftype, ret_val : fuck1free}:
    `%%`(reftype, ret_val)
    -- wf_reftype: `%`(reftype)
    -- if (ret_val = $free_reftype(reftype))
    -- wf_free: `%`(ret_val)

;; test.spectec:820.6-820.19
relation free_typeuse_is_wf: `%%`fuck5(typeuse : fuck1typeuse, ret_val : fuck1free)
  ;; test.spectec:820.6-820.19
  rule free_typeuse_is_wf_0{typeuse : fuck1typeuse, ret_val : fuck1free}:
    `%%`(typeuse, ret_val)
    -- wf_typeuse: `%`(typeuse)
    -- if (ret_val = $free_typeuse(typeuse))
    -- wf_free: `%`(ret_val)

;; test.spectec:821.6-821.19
relation free_valtype_is_wf: `%%`fuck5(valtype : fuck1valtype, ret_val : fuck1free)
  ;; test.spectec:821.6-821.19
  rule free_valtype_is_wf_0{valtype : fuck1valtype, ret_val : fuck1free}:
    `%%`(valtype, ret_val)
    -- wf_valtype: `%`(valtype)
    -- if (ret_val = $free_valtype(valtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:823.6-823.22
relation free_resulttype_is_wf: `%%`fuck5(resulttype : fuck1resulttype, ret_val : fuck1free)
  ;; test.spectec:823.6-823.22
  rule free_resulttype_is_wf_0{resulttype : fuck1resulttype, ret_val : fuck1free}:
    `%%`(resulttype, ret_val)
    -- if (ret_val = $free_resulttype(resulttype))
    -- wf_free: `%`(ret_val)

;; test.spectec:824.6-824.23
relation free_storagetype_is_wf: `%%`fuck5(storagetype : fuck1storagetype, ret_val : fuck1free)
  ;; test.spectec:824.6-824.23
  rule free_storagetype_is_wf_0{storagetype : fuck1storagetype, ret_val : fuck1free}:
    `%%`(storagetype, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- if (ret_val = $free_storagetype(storagetype))
    -- wf_free: `%`(ret_val)

;; test.spectec:825.6-825.21
relation free_fieldtype_is_wf: `%%`fuck5(fieldtype : fuck1fieldtype, ret_val : fuck1free)
  ;; test.spectec:825.6-825.21
  rule free_fieldtype_is_wf_0{fieldtype : fuck1fieldtype, ret_val : fuck1free}:
    `%%`(fieldtype, ret_val)
    -- wf_fieldtype: `%`(fieldtype)
    -- if (ret_val = $free_fieldtype(fieldtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:826.6-826.20
relation free_comptype_is_wf: `%%`fuck5(comptype : fuck1comptype, ret_val : fuck1free)
  ;; test.spectec:826.6-826.20
  rule free_comptype_is_wf_0{comptype : fuck1comptype, ret_val : fuck1free}:
    `%%`(comptype, ret_val)
    -- wf_comptype: `%`(comptype)
    -- if (ret_val = $free_comptype(comptype))
    -- wf_free: `%`(ret_val)

;; test.spectec:827.6-827.19
relation free_subtype_is_wf: `%%`fuck5(subtype : fuck1subtype, ret_val : fuck1free)
  ;; test.spectec:827.6-827.19
  rule free_subtype_is_wf_0{subtype : fuck1subtype, ret_val : fuck1free}:
    `%%`(subtype, ret_val)
    -- wf_subtype: `%`(subtype)
    -- if (ret_val = $free_subtype(subtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:828.6-828.19
relation free_rectype_is_wf: `%%`fuck5(rectype : fuck1rectype, ret_val : fuck1free)
  ;; test.spectec:828.6-828.19
  rule free_rectype_is_wf_0{rectype : fuck1rectype, ret_val : fuck1free}:
    `%%`(rectype, ret_val)
    -- if (ret_val = $free_rectype(rectype))
    -- wf_free: `%`(ret_val)

;; test.spectec:856.6-856.19
relation free_deftype_is_wf: `%%`fuck5(deftype : fuck1deftype, ret_val : fuck1free)
  ;; test.spectec:856.6-856.19
  rule free_deftype_is_wf_0{deftype : fuck1deftype, ret_val : fuck1free}:
    `%%`(deftype, ret_val)
    -- if (ret_val = $free_deftype(deftype))
    -- wf_free: `%`(ret_val)
}

;; test.spectec:830.1-830.34
def $free_tagtype(tagtype : fuck1tagtype) : fuck1free
  ;; test.spectec:891.1-891.52
  def $free_tagtype{deftype : fuck1deftype}((deftype : fuck1deftype <: fuck1typeuse)) = $free_deftype(deftype)

;; test.spectec:830.6-830.19
relation free_tagtype_is_wf: `%%`fuck5(tagtype : fuck1tagtype, ret_val : fuck1free)
  ;; test.spectec:830.6-830.19
  rule free_tagtype_is_wf_0{tagtype : fuck1tagtype, ret_val : fuck1free}:
    `%%`(tagtype, ret_val)
    -- wf_typeuse: `%`(tagtype)
    -- if (ret_val = $free_tagtype(tagtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:831.1-831.40
def $free_globaltype(globaltype : fuck1globaltype) : fuck1free
  ;; test.spectec:893.1-893.60
  def $free_globaltype{`mut?` : fuck6fuck1mut?, valtype : fuck1valtype}(`%%`_globaltype(mut?{mut <- `mut?`}, valtype)) = $free_valtype(valtype)

;; test.spectec:831.6-831.22
relation free_globaltype_is_wf: `%%`fuck5(globaltype : fuck1globaltype, ret_val : fuck1free)
  ;; test.spectec:831.6-831.22
  rule free_globaltype_is_wf_0{globaltype : fuck1globaltype, ret_val : fuck1free}:
    `%%`(globaltype, ret_val)
    -- wf_globaltype: `%`(globaltype)
    -- if (ret_val = $free_globaltype(globaltype))
    -- wf_free: `%`(ret_val)

;; test.spectec:832.1-832.34
def $free_memtype(memtype : fuck1memtype) : fuck1free
  ;; test.spectec:895.1-895.67
  def $free_memtype{addrtype : fuck1addrtype, limits : fuck1limits}(`%%PAGE`_memtype(addrtype, limits)) = $free_addrtype(addrtype)

;; test.spectec:832.6-832.19
relation free_memtype_is_wf: `%%`fuck5(memtype : fuck1memtype, ret_val : fuck1free)
  ;; test.spectec:832.6-832.19
  rule free_memtype_is_wf_0{memtype : fuck1memtype, ret_val : fuck1free}:
    `%%`(memtype, ret_val)
    -- wf_memtype: `%`(memtype)
    -- if (ret_val = $free_memtype(memtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:833.1-833.38
def $free_tabletype(tabletype : fuck1tabletype) : fuck1free
  ;; test.spectec:897.1-898.53
  def $free_tabletype{addrtype : fuck1addrtype, limits : fuck1limits, reftype : fuck1reftype}(`%%%`_tabletype(addrtype, limits, reftype)) = $free_addrtype(addrtype) +++ $free_reftype(reftype)

;; test.spectec:833.6-833.21
relation free_tabletype_is_wf: `%%`fuck5(tabletype : fuck1tabletype, ret_val : fuck1free)
  ;; test.spectec:833.6-833.21
  rule free_tabletype_is_wf_0{tabletype : fuck1tabletype, ret_val : fuck1free}:
    `%%`(tabletype, ret_val)
    -- wf_tabletype: `%`(tabletype)
    -- if (ret_val = $free_tabletype(tabletype))
    -- wf_free: `%`(ret_val)

;; test.spectec:834.1-834.36
def $free_datatype(datatype : fuck1datatype) : fuck1free
  ;; test.spectec:900.1-900.28
  def $free_datatype(OK_datatype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:834.6-834.20
relation free_datatype_is_wf: `%%`fuck5(datatype : fuck1datatype, ret_val : fuck1free)
  ;; test.spectec:834.6-834.20
  rule free_datatype_is_wf_0{datatype : fuck1datatype, ret_val : fuck1free}:
    `%%`(datatype, ret_val)
    -- if (ret_val = $free_datatype(datatype))
    -- wf_free: `%`(ret_val)

;; test.spectec:835.1-835.36
def $free_elemtype(elemtype : fuck1elemtype) : fuck1free
  ;; test.spectec:902.1-902.53
  def $free_elemtype{reftype : fuck1reftype}(reftype) = $free_reftype(reftype)

;; test.spectec:835.6-835.20
relation free_elemtype_is_wf: `%%`fuck5(elemtype : fuck1elemtype, ret_val : fuck1free)
  ;; test.spectec:835.6-835.20
  rule free_elemtype_is_wf_0{elemtype : fuck1elemtype, ret_val : fuck1free}:
    `%%`(elemtype, ret_val)
    -- wf_reftype: `%`(elemtype)
    -- if (ret_val = $free_elemtype(elemtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:836.1-836.40
def $free_externtype(externtype : fuck1externtype) : fuck1free
  ;; test.spectec:904.1-904.59
  def $free_externtype{tagtype : fuck1typeuse}(TAG_externtype(tagtype)) = $free_tagtype(tagtype)
  ;; test.spectec:905.1-905.71
  def $free_externtype{globaltype : fuck1globaltype}(GLOBAL_externtype(globaltype)) = $free_globaltype(globaltype)
  ;; test.spectec:906.1-906.59
  def $free_externtype{memtype : fuck1memtype}(MEM_externtype(memtype)) = $free_memtype(memtype)
  ;; test.spectec:907.1-907.67
  def $free_externtype{tabletype : fuck1tabletype}(TABLE_externtype(tabletype)) = $free_tabletype(tabletype)
  ;; test.spectec:908.1-908.60
  def $free_externtype{typeuse : fuck1typeuse}(FUNC_externtype(typeuse)) = $free_typeuse(typeuse)

;; test.spectec:836.6-836.22
relation free_externtype_is_wf: `%%`fuck5(externtype : fuck1externtype, ret_val : fuck1free)
  ;; test.spectec:836.6-836.22
  rule free_externtype_is_wf_0{externtype : fuck1externtype, ret_val : fuck1free}:
    `%%`(externtype, ret_val)
    -- wf_externtype: `%`(externtype)
    -- if (ret_val = $free_externtype(externtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:837.1-837.40
def $free_moduletype(moduletype : fuck1moduletype) : fuck1free
  ;; test.spectec:910.1-912.46
  def $free_moduletype{`externtype_1*` : fuck6fuck1externtype*, `externtype_2*` : fuck6fuck1externtype*}(`%->%`_moduletype(externtype_1*{externtype_1 <- `externtype_1*`}, externtype_2*{externtype_2 <- `externtype_2*`})) = $free_list($free_externtype(externtype_1)*{externtype_1 <- `externtype_1*`}) +++ $free_list($free_externtype(externtype_2)*{externtype_2 <- `externtype_2*`})

;; test.spectec:837.6-837.22
relation free_moduletype_is_wf: `%%`fuck5(moduletype : fuck1moduletype, ret_val : fuck1free)
  ;; test.spectec:837.6-837.22
  rule free_moduletype_is_wf_0{moduletype : fuck1moduletype, ret_val : fuck1free}:
    `%%`(moduletype, ret_val)
    -- wf_moduletype: `%`(moduletype)
    -- if (ret_val = $free_moduletype(moduletype))
    -- wf_free: `%`(ret_val)

;; test.spectec:927.1-927.21
syntax num_ = 
  | mk_num__0fuck5(Inn : fuck1Inn, var_x : fuck1iN)
  | mk_num__1fuck5(Fnn : fuck1Fnn, var_x : fuck1fN)

;; test.spectec:927.8-927.13
relation wf_num_: `%%`fuck5(fuck1numtype, fuck1num_)
  ;; test.spectec:927.8-927.13
  rule num__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1iN}:
    `%%`(numtype, mk_num__0_num_(Inn, var_x))
    -- wf_uN: `%%`($size((Inn : fuck1addrtype <: fuck1numtype)), var_x)
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

  ;; test.spectec:927.8-927.13
  rule num__case_1{numtype : fuck1numtype, Fnn : fuck1Fnn, var_x : fuck1fN}:
    `%%`(numtype, mk_num__1_num_(Fnn, var_x))
    -- wf_fN: `%%`($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), var_x)
    -- if (numtype = (Fnn : fuck1Fnn <: fuck1numtype))

;; test.spectec:927.1-927.21
def $proj_num__0(var_x : fuck1num_) : fuck6fuck1iN?
  ;; test.spectec:927.8-927.13
  def $proj_num__0{Inn : fuck1Inn, var_x : fuck1iN}(mk_num__0_num_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:927.8-927.13
  def $proj_num__0{var_x : fuck1num_}(var_x) = ?()

;; test.spectec:927.1-927.21
def $proj_num__1(var_x : fuck1num_) : fuck6fuck1fN?
  ;; test.spectec:927.8-927.13
  def $proj_num__1{Fnn : fuck1Fnn, var_x : fuck1fN}(mk_num__1_num_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:927.8-927.13
  def $proj_num__1{var_x : fuck1num_}(var_x) = ?()

;; test.spectec:931.1-931.38
syntax pack_ = fuck1iN

;; test.spectec:933.1-933.23
syntax lane_ = 
  | mk_lane__0fuck5(numtype : fuck1numtype, var_x : fuck1num_)
  | mk_lane__1fuck5(packtype : fuck1packtype, var_x : fuck1pack_)
  | mk_lane__2fuck5(Jnn : fuck1Jnn, var_x : fuck1iN)

;; test.spectec:933.8-933.14
relation wf_lane_: `%%`fuck5(fuck1lanetype, fuck1lane_)
  ;; test.spectec:933.8-933.14
  rule lane__case_0{lanetype : fuck1lanetype, numtype : fuck1numtype, var_x : fuck1num_}:
    `%%`(lanetype, mk_lane__0_lane_(numtype, var_x))
    -- wf_num_: `%%`(numtype, var_x)
    -- if (lanetype = (numtype : fuck1numtype <: fuck1lanetype))

  ;; test.spectec:933.8-933.14
  rule lane__case_1{lanetype : fuck1lanetype, packtype : fuck1packtype, var_x : fuck1pack_}:
    `%%`(lanetype, mk_lane__1_lane_(packtype, var_x))
    -- wf_uN: `%%`($psize(packtype), var_x)
    -- if (lanetype = (packtype : fuck1packtype <: fuck1lanetype))

  ;; test.spectec:933.8-933.14
  rule lane__case_2{lanetype : fuck1lanetype, Jnn : fuck1Jnn, var_x : fuck1iN}:
    `%%`(lanetype, mk_lane__2_lane_(Jnn, var_x))
    -- wf_uN: `%%`($lsize((Jnn : fuck1Jnn <: fuck1lanetype)), var_x)
    -- if (lanetype = (Jnn : fuck1Jnn <: fuck1lanetype))

;; test.spectec:933.1-933.23
def $proj_lane__0(var_x : fuck1lane_) : fuck6fuck1num_?
  ;; test.spectec:933.8-933.14
  def $proj_lane__0{numtype : fuck1numtype, var_x : fuck1num_}(mk_lane__0_lane_(numtype, var_x)) = ?(var_x)
  ;; test.spectec:933.8-933.14
  def $proj_lane__0{var_x : fuck1lane_}(var_x) = ?()

;; test.spectec:933.1-933.23
def $proj_lane__1(var_x : fuck1lane_) : fuck6fuck1pack_?
  ;; test.spectec:933.8-933.14
  def $proj_lane__1{packtype : fuck1packtype, var_x : fuck1pack_}(mk_lane__1_lane_(packtype, var_x)) = ?(var_x)
  ;; test.spectec:933.8-933.14
  def $proj_lane__1{var_x : fuck1lane_}(var_x) = ?()

;; test.spectec:933.1-933.23
def $proj_lane__2(var_x : fuck1lane_) : fuck6fuck1iN?
  ;; test.spectec:933.8-933.14
  def $proj_lane__2{Jnn : fuck1Jnn, var_x : fuck1iN}(mk_lane__2_lane_(Jnn, var_x)) = ?(var_x)
  ;; test.spectec:933.8-933.14
  def $proj_lane__2{var_x : fuck1lane_}(var_x) = ?()

;; test.spectec:938.1-938.35
syntax vec_ = fuck1vN

;; test.spectec:940.1-940.25
syntax lit_ = 
  | mk_lit__0fuck5(numtype : fuck1numtype, var_x : fuck1num_)
  | mk_lit__1fuck5(vectype : fuck1vectype, var_x : fuck1vec_)
  | mk_lit__2fuck5(packtype : fuck1packtype, var_x : fuck1pack_)

;; test.spectec:940.8-940.13
relation wf_lit_: `%%`fuck5(fuck1storagetype, fuck1lit_)
  ;; test.spectec:940.8-940.13
  rule lit__case_0{storagetype : fuck1storagetype, numtype : fuck1numtype, var_x : fuck1num_}:
    `%%`(storagetype, mk_lit__0_lit_(numtype, var_x))
    -- wf_num_: `%%`(numtype, var_x)
    -- if (storagetype = (numtype : fuck1numtype <: fuck1storagetype))

  ;; test.spectec:940.8-940.13
  rule lit__case_1{storagetype : fuck1storagetype, vectype : fuck1vectype, var_x : fuck1vec_}:
    `%%`(storagetype, mk_lit__1_lit_(vectype, var_x))
    -- wf_uN: `%%`($vsize(vectype), var_x)
    -- if (storagetype = (vectype : fuck1vectype <: fuck1storagetype))

  ;; test.spectec:940.8-940.13
  rule lit__case_2{storagetype : fuck1storagetype, packtype : fuck1packtype, var_x : fuck1pack_}:
    `%%`(storagetype, mk_lit__2_lit_(packtype, var_x))
    -- wf_uN: `%%`($psize(packtype), var_x)
    -- if (storagetype = (packtype : fuck1packtype <: fuck1storagetype))

;; test.spectec:940.1-940.25
def $proj_lit__0(var_x : fuck1lit_) : fuck6fuck1num_?
  ;; test.spectec:940.8-940.13
  def $proj_lit__0{numtype : fuck1numtype, var_x : fuck1num_}(mk_lit__0_lit_(numtype, var_x)) = ?(var_x)
  ;; test.spectec:940.8-940.13
  def $proj_lit__0{var_x : fuck1lit_}(var_x) = ?()

;; test.spectec:940.1-940.25
def $proj_lit__1(var_x : fuck1lit_) : fuck6fuck1vec_?
  ;; test.spectec:940.8-940.13
  def $proj_lit__1{vectype : fuck1vectype, var_x : fuck1vec_}(mk_lit__1_lit_(vectype, var_x)) = ?(var_x)
  ;; test.spectec:940.8-940.13
  def $proj_lit__1{var_x : fuck1lit_}(var_x) = ?()

;; test.spectec:940.1-940.25
def $proj_lit__2(var_x : fuck1lit_) : fuck6fuck1pack_?
  ;; test.spectec:940.8-940.13
  def $proj_lit__2{packtype : fuck1packtype, var_x : fuck1pack_}(mk_lit__2_lit_(packtype, var_x)) = ?(var_x)
  ;; test.spectec:940.8-940.13
  def $proj_lit__2{var_x : fuck1lit_}(var_x) = ?()

;; test.spectec:948.1-948.56
syntax sz = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:948.8-948.10
relation wf_sz: `%`fuck5(fuck1sz)
  ;; test.spectec:948.8-948.10
  rule sz_case_0{i : fuck3nat}:
    `%`(`%`_sz(i))
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; test.spectec:949.1-949.42
syntax sx = 
  | U
  | S

;; test.spectec:951.1-951.22
syntax unop_Inn = 
  | CLZ
  | CTZ
  | POPCNT
  | EXTENDfuck5(sz : fuck1sz)

;; test.spectec:951.8-951.14
relation wf_unop_Inn: `%%`fuck5(fuck1Inn, fuck1unop_Inn)
  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_0{Inn : fuck1Inn}:
    `%%`(Inn, CLZ_unop_Inn)

  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_1{Inn : fuck1Inn}:
    `%%`(Inn, CTZ_unop_Inn)

  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_2{Inn : fuck1Inn}:
    `%%`(Inn, POPCNT_unop_Inn)

  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_3{Inn : fuck1Inn, sz : fuck1sz}:
    `%%`(Inn, EXTEND_unop_Inn(sz))
    -- wf_sz: `%`(sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : fuck1addrtype <: fuck1numtype)))

;; test.spectec:951.1-951.22
syntax unop_Fnn = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST

;; test.spectec:951.1-951.22
syntax unop_ = 
  | mk_unop__0fuck5(Inn : fuck1Inn, var_x : fuck1unop_Inn)
  | mk_unop__1fuck5(Fnn : fuck1Fnn, var_x : fuck1unop_Fnn)

;; test.spectec:951.8-951.14
relation wf_unop_: `%%`fuck5(fuck1numtype, fuck1unop_)
  ;; test.spectec:951.8-951.14
  rule unop__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1unop_Inn}:
    `%%`(numtype, mk_unop__0_unop_(Inn, var_x))
    -- wf_unop_Inn: `%%`(Inn, var_x)
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

  ;; test.spectec:951.8-951.14
  rule unop__case_1{numtype : fuck1numtype, Fnn : fuck1Fnn, var_x : fuck1unop_Fnn}:
    `%%`(numtype, mk_unop__1_unop_(Fnn, var_x))
    -- if (numtype = (Fnn : fuck1Fnn <: fuck1numtype))

;; test.spectec:951.1-951.22
def $proj_unop__0(var_x : fuck1unop_) : fuck6fuck1unop_Inn?
  ;; test.spectec:951.8-951.14
  def $proj_unop__0{Inn : fuck1Inn, var_x : fuck1unop_Inn}(mk_unop__0_unop_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:951.8-951.14
  def $proj_unop__0{var_x : fuck1unop_}(var_x) = ?()

;; test.spectec:951.1-951.22
def $proj_unop__1(var_x : fuck1unop_) : fuck6fuck1unop_Fnn?
  ;; test.spectec:951.8-951.14
  def $proj_unop__1{Fnn : fuck1Fnn, var_x : fuck1unop_Fnn}(mk_unop__1_unop_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:951.8-951.14
  def $proj_unop__1{var_x : fuck1unop_}(var_x) = ?()

;; test.spectec:955.1-955.23
syntax binop_Inn = 
  | ADD
  | SUB
  | MUL
  | DIVfuck5(sx : fuck1sx)
  | REMfuck5(sx : fuck1sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHRfuck5(sx : fuck1sx)
  | ROTL
  | ROTR

;; test.spectec:955.1-955.23
syntax binop_Fnn = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN

;; test.spectec:955.1-955.23
syntax binop_ = 
  | mk_binop__0fuck5(Inn : fuck1Inn, var_x : fuck1binop_Inn)
  | mk_binop__1fuck5(Fnn : fuck1Fnn, var_x : fuck1binop_Fnn)

;; test.spectec:955.8-955.15
relation wf_binop_: `%%`fuck5(fuck1numtype, fuck1binop_)
  ;; test.spectec:955.8-955.15
  rule binop__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1binop_Inn}:
    `%%`(numtype, mk_binop__0_binop_(Inn, var_x))
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

  ;; test.spectec:955.8-955.15
  rule binop__case_1{numtype : fuck1numtype, Fnn : fuck1Fnn, var_x : fuck1binop_Fnn}:
    `%%`(numtype, mk_binop__1_binop_(Fnn, var_x))
    -- if (numtype = (Fnn : fuck1Fnn <: fuck1numtype))

;; test.spectec:955.1-955.23
def $proj_binop__0(var_x : fuck1binop_) : fuck6fuck1binop_Inn?
  ;; test.spectec:955.8-955.15
  def $proj_binop__0{Inn : fuck1Inn, var_x : fuck1binop_Inn}(mk_binop__0_binop_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:955.8-955.15
  def $proj_binop__0{var_x : fuck1binop_}(var_x) = ?()

;; test.spectec:955.1-955.23
def $proj_binop__1(var_x : fuck1binop_) : fuck6fuck1binop_Fnn?
  ;; test.spectec:955.8-955.15
  def $proj_binop__1{Fnn : fuck1Fnn, var_x : fuck1binop_Fnn}(mk_binop__1_binop_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:955.8-955.15
  def $proj_binop__1{var_x : fuck1binop_}(var_x) = ?()

;; test.spectec:962.1-962.24
syntax testop_Inn = 
  | EQZ

;; test.spectec:962.1-962.24
syntax testop_ = 
  | mk_testop__0fuck5(Inn : fuck1Inn, var_x : fuck1testop_Inn)

;; test.spectec:962.8-962.16
relation wf_testop_: `%%`fuck5(fuck1numtype, fuck1testop_)
  ;; test.spectec:962.8-962.16
  rule testop__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1testop_Inn}:
    `%%`(numtype, mk_testop__0_testop_(Inn, var_x))
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

;; test.spectec:962.1-962.24
def $proj_testop__0(var_x : fuck1testop_) : fuck1testop_Inn
  ;; test.spectec:962.8-962.16
  def $proj_testop__0{Inn : fuck1Inn, var_x : fuck1testop_Inn}(mk_testop__0_testop_(Inn, var_x)) = var_x

;; test.spectec:966.1-966.23
syntax relop_Inn = 
  | EQ
  | NE
  | LTfuck5(sx : fuck1sx)
  | GTfuck5(sx : fuck1sx)
  | LEfuck5(sx : fuck1sx)
  | GEfuck5(sx : fuck1sx)

;; test.spectec:966.1-966.23
syntax relop_Fnn = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

;; test.spectec:966.1-966.23
syntax relop_ = 
  | mk_relop__0fuck5(Inn : fuck1Inn, var_x : fuck1relop_Inn)
  | mk_relop__1fuck5(Fnn : fuck1Fnn, var_x : fuck1relop_Fnn)

;; test.spectec:966.8-966.15
relation wf_relop_: `%%`fuck5(fuck1numtype, fuck1relop_)
  ;; test.spectec:966.8-966.15
  rule relop__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1relop_Inn}:
    `%%`(numtype, mk_relop__0_relop_(Inn, var_x))
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

  ;; test.spectec:966.8-966.15
  rule relop__case_1{numtype : fuck1numtype, Fnn : fuck1Fnn, var_x : fuck1relop_Fnn}:
    `%%`(numtype, mk_relop__1_relop_(Fnn, var_x))
    -- if (numtype = (Fnn : fuck1Fnn <: fuck1numtype))

;; test.spectec:966.1-966.23
def $proj_relop__0(var_x : fuck1relop_) : fuck6fuck1relop_Inn?
  ;; test.spectec:966.8-966.15
  def $proj_relop__0{Inn : fuck1Inn, var_x : fuck1relop_Inn}(mk_relop__0_relop_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:966.8-966.15
  def $proj_relop__0{var_x : fuck1relop_}(var_x) = ?()

;; test.spectec:966.1-966.23
def $proj_relop__1(var_x : fuck1relop_) : fuck6fuck1relop_Fnn?
  ;; test.spectec:966.8-966.15
  def $proj_relop__1{Fnn : fuck1Fnn, var_x : fuck1relop_Fnn}(mk_relop__1_relop_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:966.8-966.15
  def $proj_relop__1{var_x : fuck1relop_}(var_x) = ?()

;; test.spectec:975.1-975.37
syntax cvtop__Inn_1_Inn_2 = 
  | EXTENDfuck5(sx : fuck1sx)
  | WRAP

;; test.spectec:975.8-975.16
relation wf_cvtop__Inn_1_Inn_2: `%%%`fuck5(fuck1Inn, fuck1Inn, fuck1cvtop__Inn_1_Inn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Inn_2_case_0{Inn_1 : fuck1Inn, Inn_2 : fuck1Inn, sx : fuck1sx}:
    `%%%`(Inn_1, Inn_2, EXTEND_cvtop__Inn_1_Inn_2(sx))
    -- if ($sizenn1((Inn_1 : fuck1addrtype <: fuck1numtype)) < $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)))

  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Inn_2_case_1{Inn_1 : fuck1Inn, Inn_2 : fuck1Inn}:
    `%%%`(Inn_1, Inn_2, WRAP_cvtop__Inn_1_Inn_2)
    -- if ($sizenn1((Inn_1 : fuck1addrtype <: fuck1numtype)) > $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)))

;; test.spectec:975.1-975.37
syntax cvtop__Inn_1_Fnn_2 = 
  | CONVERTfuck5(sx : fuck1sx)
  | REINTERPRET

;; test.spectec:975.8-975.16
relation wf_cvtop__Inn_1_Fnn_2: `%%%`fuck5(fuck1Inn, fuck1Fnn, fuck1cvtop__Inn_1_Fnn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Fnn_2_case_0{Inn_1 : fuck1Inn, Fnn_2 : fuck1Fnn, sx : fuck1sx}:
    `%%%`(Inn_1, Fnn_2, CONVERT_cvtop__Inn_1_Fnn_2(sx))

  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Fnn_2_case_1{Inn_1 : fuck1Inn, Fnn_2 : fuck1Fnn}:
    `%%%`(Inn_1, Fnn_2, REINTERPRET_cvtop__Inn_1_Fnn_2)
    -- if ($sizenn1((Inn_1 : fuck1addrtype <: fuck1numtype)) = $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)))

;; test.spectec:975.1-975.37
syntax cvtop__Fnn_1_Inn_2 = 
  | TRUNCfuck5(sx : fuck1sx)
  | TRUNC_SATfuck5(sx : fuck1sx)
  | REINTERPRET

;; test.spectec:975.8-975.16
relation wf_cvtop__Fnn_1_Inn_2: `%%%`fuck5(fuck1Fnn, fuck1Inn, fuck1cvtop__Fnn_1_Inn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Inn_2_case_0{Fnn_1 : fuck1Fnn, Inn_2 : fuck1Inn, sx : fuck1sx}:
    `%%%`(Fnn_1, Inn_2, TRUNC_cvtop__Fnn_1_Inn_2(sx))

  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Inn_2_case_1{Fnn_1 : fuck1Fnn, Inn_2 : fuck1Inn, sx : fuck1sx}:
    `%%%`(Fnn_1, Inn_2, TRUNC_SAT_cvtop__Fnn_1_Inn_2(sx))

  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Inn_2_case_2{Fnn_1 : fuck1Fnn, Inn_2 : fuck1Inn}:
    `%%%`(Fnn_1, Inn_2, REINTERPRET_cvtop__Fnn_1_Inn_2)
    -- if ($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) = $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)))

;; test.spectec:975.1-975.37
syntax cvtop__Fnn_1_Fnn_2 = 
  | PROMOTE
  | DEMOTE

;; test.spectec:975.8-975.16
relation wf_cvtop__Fnn_1_Fnn_2: `%%%`fuck5(fuck1Fnn, fuck1Fnn, fuck1cvtop__Fnn_1_Fnn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Fnn_2_case_0{Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn}:
    `%%%`(Fnn_1, Fnn_2, PROMOTE_cvtop__Fnn_1_Fnn_2)
    -- if ($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) < $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)))

  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Fnn_2_case_1{Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn}:
    `%%%`(Fnn_1, Fnn_2, DEMOTE_cvtop__Fnn_1_Fnn_2)
    -- if ($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) > $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)))

;; test.spectec:975.1-975.37
syntax cvtop__ = 
  | mk_cvtop___0fuck5(Inn_1 : fuck1Inn, Inn_2 : fuck1Inn, var_x : fuck1cvtop__Inn_1_Inn_2)
  | mk_cvtop___1fuck5(Inn_1 : fuck1Inn, Fnn_2 : fuck1Fnn, var_x : fuck1cvtop__Inn_1_Fnn_2)
  | mk_cvtop___2fuck5(Fnn_1 : fuck1Fnn, Inn_2 : fuck1Inn, var_x : fuck1cvtop__Fnn_1_Inn_2)
  | mk_cvtop___3fuck5(Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn, var_x : fuck1cvtop__Fnn_1_Fnn_2)

;; test.spectec:975.8-975.16
relation wf_cvtop__: `%%%`fuck5(fuck1numtype, fuck1numtype, fuck1cvtop__)
  ;; test.spectec:975.8-975.16
  rule cvtop___case_0{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, Inn_1 : fuck1Inn, Inn_2 : fuck1Inn, var_x : fuck1cvtop__Inn_1_Inn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___0_cvtop__(Inn_1, Inn_2, var_x))
    -- wf_cvtop__Inn_1_Inn_2: `%%%`(Inn_1, Inn_2, var_x)
    -- if (numtype_1 = (Inn_1 : fuck1addrtype <: fuck1numtype))
    -- if (numtype_2 = (Inn_2 : fuck1addrtype <: fuck1numtype))

  ;; test.spectec:975.8-975.16
  rule cvtop___case_1{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, Inn_1 : fuck1Inn, Fnn_2 : fuck1Fnn, var_x : fuck1cvtop__Inn_1_Fnn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___1_cvtop__(Inn_1, Fnn_2, var_x))
    -- wf_cvtop__Inn_1_Fnn_2: `%%%`(Inn_1, Fnn_2, var_x)
    -- if (numtype_1 = (Inn_1 : fuck1addrtype <: fuck1numtype))
    -- if (numtype_2 = (Fnn_2 : fuck1Fnn <: fuck1numtype))

  ;; test.spectec:975.8-975.16
  rule cvtop___case_2{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, Fnn_1 : fuck1Fnn, Inn_2 : fuck1Inn, var_x : fuck1cvtop__Fnn_1_Inn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___2_cvtop__(Fnn_1, Inn_2, var_x))
    -- wf_cvtop__Fnn_1_Inn_2: `%%%`(Fnn_1, Inn_2, var_x)
    -- if (numtype_1 = (Fnn_1 : fuck1Fnn <: fuck1numtype))
    -- if (numtype_2 = (Inn_2 : fuck1addrtype <: fuck1numtype))

  ;; test.spectec:975.8-975.16
  rule cvtop___case_3{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn, var_x : fuck1cvtop__Fnn_1_Fnn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___3_cvtop__(Fnn_1, Fnn_2, var_x))
    -- wf_cvtop__Fnn_1_Fnn_2: `%%%`(Fnn_1, Fnn_2, var_x)
    -- if (numtype_1 = (Fnn_1 : fuck1Fnn <: fuck1numtype))
    -- if (numtype_2 = (Fnn_2 : fuck1Fnn <: fuck1numtype))

;; test.spectec:975.1-975.37
def $proj_cvtop___0(var_x : fuck1cvtop__) : fuck6fuck1cvtop__Inn_1_Inn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___0{Inn_1 : fuck1Inn, Inn_2 : fuck1Inn, var_x : fuck1cvtop__Inn_1_Inn_2}(mk_cvtop___0_cvtop__(Inn_1, Inn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___0{var_x : fuck1cvtop__}(var_x) = ?()

;; test.spectec:975.1-975.37
def $proj_cvtop___1(var_x : fuck1cvtop__) : fuck6fuck1cvtop__Inn_1_Fnn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___1{Inn_1 : fuck1Inn, Fnn_2 : fuck1Fnn, var_x : fuck1cvtop__Inn_1_Fnn_2}(mk_cvtop___1_cvtop__(Inn_1, Fnn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___1{var_x : fuck1cvtop__}(var_x) = ?()

;; test.spectec:975.1-975.37
def $proj_cvtop___2(var_x : fuck1cvtop__) : fuck6fuck1cvtop__Fnn_1_Inn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___2{Fnn_1 : fuck1Fnn, Inn_2 : fuck1Inn, var_x : fuck1cvtop__Fnn_1_Inn_2}(mk_cvtop___2_cvtop__(Fnn_1, Inn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___2{var_x : fuck1cvtop__}(var_x) = ?()

;; test.spectec:975.1-975.37
def $proj_cvtop___3(var_x : fuck1cvtop__) : fuck6fuck1cvtop__Fnn_1_Fnn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___3{Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn, var_x : fuck1cvtop__Fnn_1_Fnn_2}(mk_cvtop___3_cvtop__(Fnn_1, Fnn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___3{var_x : fuck1cvtop__}(var_x) = ?()

;; test.spectec:993.1-993.60
syntax dim = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:993.8-993.11
relation wf_dim: `%`fuck5(fuck1dim)
  ;; test.spectec:993.8-993.11
  rule dim_case_0{i : fuck3nat}:
    `%`(`%`_dim(i))
    -- if (((((i = 1) \/ (i = 2)) \/ (i = 4)) \/ (i = 8)) \/ (i = 16))

;; test.spectec:994.1-995.40
syntax shape = 
  | `%X%`fuck5(lanetype : fuck1lanetype, dim : fuck1dim)

;; test.spectec:994.8-994.13
relation wf_shape: `%`fuck5(fuck1shape)
  ;; test.spectec:994.8-994.13
  rule shape_case_0{lanetype : fuck1lanetype, dim : fuck1dim}:
    `%`(`%X%`_shape(lanetype, dim))
    -- wf_dim: `%`(dim)
    -- if (($lsize(lanetype) * dim!`%`_dim.0) = 128)

;; test.spectec:998.1-998.43
def $dim(shape : fuck1shape) : fuck1dim
  ;; test.spectec:999.1-999.22
  def $dim{Lnn : fuck1lanetype, N : fuck3nat}(`%X%`_shape(Lnn, `%`_dim(N))) = `%`_dim(N)

;; test.spectec:998.6-998.10
relation dim_is_wf: `%%`fuck5(shape : fuck1shape, ret_val : fuck1dim)
  ;; test.spectec:998.6-998.10
  rule dim_is_wf_0{shape : fuck1shape, ret_val : fuck1dim}:
    `%%`(shape, ret_val)
    -- wf_shape: `%`(shape)
    -- if (ret_val = $dim(shape))
    -- wf_dim: `%`(ret_val)

;; test.spectec:1001.1-1001.58
def $lanetype(shape : fuck1shape) : fuck1lanetype
  ;; test.spectec:1002.1-1002.29
  def $lanetype{Lnn : fuck1lanetype, N : fuck3nat}(`%X%`_shape(Lnn, `%`_dim(N))) = Lnn

;; test.spectec:1004.1-1004.57
def $unpackshape(shape : fuck1shape) : fuck1numtype
  ;; test.spectec:1005.1-1005.42
  def $unpackshape{Lnn : fuck1lanetype, N : fuck3nat}(`%X%`_shape(Lnn, `%`_dim(N))) = $lunpack(Lnn)

;; test.spectec:1008.1-1008.78
syntax ishape = 
  | `%`fuck5(shape : fuck1shape)

;; test.spectec:1008.8-1008.14
relation wf_ishape: `%`fuck5(fuck1ishape)
  ;; test.spectec:1008.8-1008.14
  rule ishape_case_0{Jnn : fuck1Jnn, shape : fuck1shape}:
    `%`(`%`_ishape(shape))
    -- wf_shape: `%`(shape)
    -- if ($lanetype(shape) = (Jnn : fuck1Jnn <: fuck1lanetype))

;; test.spectec:1009.1-1009.77
syntax bshape = 
  | `%`fuck5(shape : fuck1shape)

;; test.spectec:1009.8-1009.14
relation wf_bshape: `%`fuck5(fuck1bshape)
  ;; test.spectec:1009.8-1009.14
  rule bshape_case_0{shape : fuck1shape}:
    `%`(`%`_bshape(shape))
    -- wf_shape: `%`(shape)
    -- if ($lanetype(shape) = I8_lanetype)

;; test.spectec:1014.1-1014.19
syntax zero = 
  | ZERO

;; test.spectec:1015.1-1015.25
syntax half = 
  | LOW
  | HIGH

;; test.spectec:1017.1-1017.41
syntax vvunop = 
  | NOT

;; test.spectec:1018.1-1018.62
syntax vvbinop = 
  | AND
  | ANDNOT
  | OR
  | XOR

;; test.spectec:1019.1-1019.49
syntax vvternop = 
  | BITSELECT

;; test.spectec:1020.1-1020.48
syntax vvtestop = 
  | ANY_TRUE

;; test.spectec:1022.1-1022.42
syntax vunop_Jnn_M = 
  | ABS
  | NEG
  | POPCNT

;; test.spectec:1022.8-1022.15
relation wf_vunop_Jnn_M: `%%%`fuck5(fuck1Jnn, fuck1M, fuck1vunop_Jnn_M)
  ;; test.spectec:1022.8-1022.15
  rule vunop_Jnn_M_case_0{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, ABS_vunop_Jnn_M)

  ;; test.spectec:1022.8-1022.15
  rule vunop_Jnn_M_case_1{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, NEG_vunop_Jnn_M)

  ;; test.spectec:1022.8-1022.15
  rule vunop_Jnn_M_case_2{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, POPCNT_vunop_Jnn_M)
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) = 8)

;; test.spectec:1022.1-1022.42
syntax vunop_Fnn_M = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST

;; test.spectec:1022.1-1022.42
syntax vunop_ = 
  | mk_vunop__0fuck5(Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vunop_Jnn_M)
  | mk_vunop__1fuck5(Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vunop_Fnn_M)

;; test.spectec:1022.8-1022.15
relation wf_vunop_: `%%`fuck5(fuck1shape, fuck1vunop_)
  ;; test.spectec:1022.8-1022.15
  rule vunop__case_0{shape : fuck1shape, Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vunop_Jnn_M}:
    `%%`(shape, mk_vunop__0_vunop_(Jnn, M, var_x))
    -- wf_vunop_Jnn_M: `%%%`(Jnn, M, var_x)
    -- if (shape = `%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)))

  ;; test.spectec:1022.8-1022.15
  rule vunop__case_1{shape : fuck1shape, Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vunop_Fnn_M}:
    `%%`(shape, mk_vunop__1_vunop_(Fnn, M, var_x))
    -- if (shape = `%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)))

;; test.spectec:1022.1-1022.42
def $proj_vunop__0(var_x : fuck1vunop_) : fuck6fuck1vunop_Jnn_M?
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__0{Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vunop_Jnn_M}(mk_vunop__0_vunop_(Jnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__0{var_x : fuck1vunop_}(var_x) = ?()

;; test.spectec:1022.1-1022.42
def $proj_vunop__1(var_x : fuck1vunop_) : fuck6fuck1vunop_Fnn_M?
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__1{Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vunop_Fnn_M}(mk_vunop__1_vunop_(Fnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__1{var_x : fuck1vunop_}(var_x) = ?()

;; test.spectec:1028.1-1028.43
syntax vbinop_Jnn_M = 
  | ADD
  | SUB
  | ADD_SATfuck5(sx : fuck1sx)
  | SUB_SATfuck5(sx : fuck1sx)
  | MUL
  | AVGRU
  | Q15MULR_SATS
  | RELAXED_Q15MULRS
  | MINfuck5(sx : fuck1sx)
  | MAXfuck5(sx : fuck1sx)

;; test.spectec:1028.8-1028.16
relation wf_vbinop_Jnn_M: `%%%`fuck5(fuck1Jnn, fuck1M, fuck1vbinop_Jnn_M)
  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_0{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, ADD_vbinop_Jnn_M)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_1{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, SUB_vbinop_Jnn_M)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_2{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, ADD_SAT_vbinop_Jnn_M(sx))
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) <= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_3{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, SUB_SAT_vbinop_Jnn_M(sx))
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) <= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_4{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, MUL_vbinop_Jnn_M)
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) >= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_5{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, AVGRU_vbinop_Jnn_M)
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) <= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_6{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, Q15MULR_SATS_vbinop_Jnn_M)
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) = 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_7{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, RELAXED_Q15MULRS_vbinop_Jnn_M)
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) = 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_8{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, MIN_vbinop_Jnn_M(sx))
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) <= 32)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_9{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, MAX_vbinop_Jnn_M(sx))
    -- if ($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) <= 32)

;; test.spectec:1028.1-1028.43
syntax vbinop_Fnn_M = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | PMIN
  | PMAX
  | RELAXED_MIN
  | RELAXED_MAX

;; test.spectec:1028.1-1028.43
syntax vbinop_ = 
  | mk_vbinop__0fuck5(Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vbinop_Jnn_M)
  | mk_vbinop__1fuck5(Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vbinop_Fnn_M)

;; test.spectec:1028.8-1028.16
relation wf_vbinop_: `%%`fuck5(fuck1shape, fuck1vbinop_)
  ;; test.spectec:1028.8-1028.16
  rule vbinop__case_0{shape : fuck1shape, Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vbinop_Jnn_M}:
    `%%`(shape, mk_vbinop__0_vbinop_(Jnn, M, var_x))
    -- wf_vbinop_Jnn_M: `%%%`(Jnn, M, var_x)
    -- if (shape = `%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)))

  ;; test.spectec:1028.8-1028.16
  rule vbinop__case_1{shape : fuck1shape, Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vbinop_Fnn_M}:
    `%%`(shape, mk_vbinop__1_vbinop_(Fnn, M, var_x))
    -- if (shape = `%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)))

;; test.spectec:1028.1-1028.43
def $proj_vbinop__0(var_x : fuck1vbinop_) : fuck6fuck1vbinop_Jnn_M?
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__0{Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vbinop_Jnn_M}(mk_vbinop__0_vbinop_(Jnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__0{var_x : fuck1vbinop_}(var_x) = ?()

;; test.spectec:1028.1-1028.43
def $proj_vbinop__1(var_x : fuck1vbinop_) : fuck6fuck1vbinop_Fnn_M?
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__1{Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vbinop_Fnn_M}(mk_vbinop__1_vbinop_(Fnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__1{var_x : fuck1vbinop_}(var_x) = ?()

;; test.spectec:1044.1-1044.44
syntax vternop_Jnn_M = 
  | RELAXED_LANESELECT

;; test.spectec:1044.1-1044.44
syntax vternop_Fnn_M = 
  | RELAXED_MADD
  | RELAXED_NMADD

;; test.spectec:1044.1-1044.44
syntax vternop_ = 
  | mk_vternop__0fuck5(Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vternop_Jnn_M)
  | mk_vternop__1fuck5(Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vternop_Fnn_M)

;; test.spectec:1044.8-1044.17
relation wf_vternop_: `%%`fuck5(fuck1shape, fuck1vternop_)
  ;; test.spectec:1044.8-1044.17
  rule vternop__case_0{shape : fuck1shape, Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vternop_Jnn_M}:
    `%%`(shape, mk_vternop__0_vternop_(Jnn, M, var_x))
    -- if (shape = `%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)))

  ;; test.spectec:1044.8-1044.17
  rule vternop__case_1{shape : fuck1shape, Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vternop_Fnn_M}:
    `%%`(shape, mk_vternop__1_vternop_(Fnn, M, var_x))
    -- if (shape = `%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)))

;; test.spectec:1044.1-1044.44
def $proj_vternop__0(var_x : fuck1vternop_) : fuck6fuck1vternop_Jnn_M?
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__0{Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vternop_Jnn_M}(mk_vternop__0_vternop_(Jnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__0{var_x : fuck1vternop_}(var_x) = ?()

;; test.spectec:1044.1-1044.44
def $proj_vternop__1(var_x : fuck1vternop_) : fuck6fuck1vternop_Fnn_M?
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__1{Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vternop_Fnn_M}(mk_vternop__1_vternop_(Fnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__1{var_x : fuck1vternop_}(var_x) = ?()

;; test.spectec:1048.1-1048.44
syntax vtestop_Jnn_M = 
  | ALL_TRUE

;; test.spectec:1048.1-1048.44
syntax vtestop_ = 
  | mk_vtestop__0fuck5(Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vtestop_Jnn_M)

;; test.spectec:1048.8-1048.17
relation wf_vtestop_: `%%`fuck5(fuck1shape, fuck1vtestop_)
  ;; test.spectec:1048.8-1048.17
  rule vtestop__case_0{shape : fuck1shape, Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vtestop_Jnn_M}:
    `%%`(shape, mk_vtestop__0_vtestop_(Jnn, M, var_x))
    -- if (shape = `%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)))

;; test.spectec:1048.1-1048.44
def $proj_vtestop__0(var_x : fuck1vtestop_) : fuck1vtestop_Jnn_M
  ;; test.spectec:1048.8-1048.17
  def $proj_vtestop__0{Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vtestop_Jnn_M}(mk_vtestop__0_vtestop_(Jnn, M, var_x)) = var_x

;; test.spectec:1052.1-1052.43
syntax vrelop_Jnn_M = 
  | EQ
  | NE
  | LTfuck5(sx : fuck1sx)
  | GTfuck5(sx : fuck1sx)
  | LEfuck5(sx : fuck1sx)
  | GEfuck5(sx : fuck1sx)

;; test.spectec:1052.8-1052.16
relation wf_vrelop_Jnn_M: `%%%`fuck5(fuck1Jnn, fuck1M, fuck1vrelop_Jnn_M)
  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_0{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, EQ_vrelop_Jnn_M)

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_1{Jnn : fuck1Jnn, M : fuck1M}:
    `%%%`(Jnn, M, NE_vrelop_Jnn_M)

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_2{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, LT_vrelop_Jnn_M(sx))
    -- if (($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) =/= 64) \/ (sx = S_sx))

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_3{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, GT_vrelop_Jnn_M(sx))
    -- if (($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) =/= 64) \/ (sx = S_sx))

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_4{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, LE_vrelop_Jnn_M(sx))
    -- if (($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) =/= 64) \/ (sx = S_sx))

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_5{Jnn : fuck1Jnn, M : fuck1M, sx : fuck1sx}:
    `%%%`(Jnn, M, GE_vrelop_Jnn_M(sx))
    -- if (($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)) =/= 64) \/ (sx = S_sx))

;; test.spectec:1052.1-1052.43
syntax vrelop_Fnn_M = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

;; test.spectec:1052.1-1052.43
syntax vrelop_ = 
  | mk_vrelop__0fuck5(Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vrelop_Jnn_M)
  | mk_vrelop__1fuck5(Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vrelop_Fnn_M)

;; test.spectec:1052.8-1052.16
relation wf_vrelop_: `%%`fuck5(fuck1shape, fuck1vrelop_)
  ;; test.spectec:1052.8-1052.16
  rule vrelop__case_0{shape : fuck1shape, Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vrelop_Jnn_M}:
    `%%`(shape, mk_vrelop__0_vrelop_(Jnn, M, var_x))
    -- wf_vrelop_Jnn_M: `%%%`(Jnn, M, var_x)
    -- if (shape = `%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)))

  ;; test.spectec:1052.8-1052.16
  rule vrelop__case_1{shape : fuck1shape, Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vrelop_Fnn_M}:
    `%%`(shape, mk_vrelop__1_vrelop_(Fnn, M, var_x))
    -- if (shape = `%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)))

;; test.spectec:1052.1-1052.43
def $proj_vrelop__0(var_x : fuck1vrelop_) : fuck6fuck1vrelop_Jnn_M?
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__0{Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vrelop_Jnn_M}(mk_vrelop__0_vrelop_(Jnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__0{var_x : fuck1vrelop_}(var_x) = ?()

;; test.spectec:1052.1-1052.43
def $proj_vrelop__1(var_x : fuck1vrelop_) : fuck6fuck1vrelop_Fnn_M?
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__1{Fnn : fuck1Fnn, M : fuck1M, var_x : fuck1vrelop_Fnn_M}(mk_vrelop__1_vrelop_(Fnn, M, var_x)) = ?(var_x)
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__1{var_x : fuck1vrelop_}(var_x) = ?()

;; test.spectec:1060.1-1060.46
syntax vshiftop_Jnn_M = 
  | SHL
  | SHRfuck5(sx : fuck1sx)

;; test.spectec:1060.1-1060.46
syntax vshiftop_ = 
  | mk_vshiftop__0fuck5(Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vshiftop_Jnn_M)

;; test.spectec:1060.8-1060.18
relation wf_vshiftop_: `%%`fuck5(fuck1ishape, fuck1vshiftop_)
  ;; test.spectec:1060.8-1060.18
  rule vshiftop__case_0{ishape : fuck1ishape, Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vshiftop_Jnn_M}:
    `%%`(ishape, mk_vshiftop__0_vshiftop_(Jnn, M, var_x))
    -- if (ishape = `%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))))

;; test.spectec:1060.1-1060.46
def $proj_vshiftop__0(var_x : fuck1vshiftop_) : fuck1vshiftop_Jnn_M
  ;; test.spectec:1060.8-1060.18
  def $proj_vshiftop__0{Jnn : fuck1Jnn, M : fuck1M, var_x : fuck1vshiftop_Jnn_M}(mk_vshiftop__0_vshiftop_(Jnn, M, var_x)) = var_x

;; test.spectec:1063.1-1063.47
syntax vswizzlop_M = 
  | SWIZZLE
  | RELAXED_SWIZZLE

;; test.spectec:1063.1-1063.47
syntax vswizzlop_ = 
  | mk_vswizzlop__0fuck5(M : fuck1M, var_x : fuck1vswizzlop_M)

;; test.spectec:1063.8-1063.19
relation wf_vswizzlop_: `%%`fuck5(fuck1bshape, fuck1vswizzlop_)
  ;; test.spectec:1063.8-1063.19
  rule vswizzlop__case_0{bshape : fuck1bshape, M : fuck1M, var_x : fuck1vswizzlop_M}:
    `%%`(bshape, mk_vswizzlop__0_vswizzlop_(M, var_x))
    -- if (bshape = `%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))))

;; test.spectec:1063.1-1063.47
def $proj_vswizzlop__0(var_x : fuck1vswizzlop_) : fuck1vswizzlop_M
  ;; test.spectec:1063.8-1063.19
  def $proj_vswizzlop__0{M : fuck1M, var_x : fuck1vswizzlop_M}(mk_vswizzlop__0_vswizzlop_(M, var_x)) = var_x

;; test.spectec:1066.1-1066.59
syntax vextunop__Jnn_1_M_1_Jnn_2_M_2 = 
  | EXTADD_PAIRWISEfuck5(sx : fuck1sx)

;; test.spectec:1066.8-1066.19
relation wf_vextunop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`fuck5(fuck1Jnn, fuck1M, fuck1Jnn, fuck1M, fuck1vextunop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1066.8-1066.19
  rule vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, sx : fuck1sx}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(sx))
    -- if ((16 <= (2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)))) /\ (((2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) <= 32)))

;; test.spectec:1066.1-1066.59
syntax vextunop__ = 
  | mk_vextunop___0fuck5(Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextunop__Jnn_1_M_1_Jnn_2_M_2)

;; test.spectec:1066.8-1066.19
relation wf_vextunop__: `%%%`fuck5(fuck1ishape, fuck1ishape, fuck1vextunop__)
  ;; test.spectec:1066.8-1066.19
  rule vextunop___case_0{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextunop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(ishape_1, ishape_2, mk_vextunop___0_vextunop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vextunop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (ishape_1 = `%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))))
    -- if (ishape_2 = `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))))

;; test.spectec:1066.1-1066.59
def $proj_vextunop___0(var_x : fuck1vextunop__) : fuck1vextunop__Jnn_1_M_1_Jnn_2_M_2
  ;; test.spectec:1066.8-1066.19
  def $proj_vextunop___0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextunop__Jnn_1_M_1_Jnn_2_M_2}(mk_vextunop___0_vextunop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = var_x

;; test.spectec:1071.1-1071.60
syntax vextbinop__Jnn_1_M_1_Jnn_2_M_2 = 
  | EXTMULfuck5(half : fuck1half, sx : fuck1sx)
  | DOTS
  | RELAXED_DOTS

;; test.spectec:1071.8-1071.20
relation wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`fuck5(fuck1Jnn, fuck1M, fuck1Jnn, fuck1M, fuck1vextbinop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1071.8-1071.20
  rule vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, half : fuck1half, sx : fuck1sx}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(half, sx))
    -- if (((2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) >= 16))

  ;; test.spectec:1071.8-1071.20
  rule vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2)
    -- if (((2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) = 32))

  ;; test.spectec:1071.8-1071.20
  rule vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2)
    -- if (((2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) = 16))

;; test.spectec:1071.1-1071.60
syntax vextbinop__ = 
  | mk_vextbinop___0fuck5(Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextbinop__Jnn_1_M_1_Jnn_2_M_2)

;; test.spectec:1071.8-1071.20
relation wf_vextbinop__: `%%%`fuck5(fuck1ishape, fuck1ishape, fuck1vextbinop__)
  ;; test.spectec:1071.8-1071.20
  rule vextbinop___case_0{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextbinop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(ishape_1, ishape_2, mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (ishape_1 = `%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))))
    -- if (ishape_2 = `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))))

;; test.spectec:1071.1-1071.60
def $proj_vextbinop___0(var_x : fuck1vextbinop__) : fuck1vextbinop__Jnn_1_M_1_Jnn_2_M_2
  ;; test.spectec:1071.8-1071.20
  def $proj_vextbinop___0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextbinop__Jnn_1_M_1_Jnn_2_M_2}(mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = var_x

;; test.spectec:1080.1-1080.61
syntax vextternop__Jnn_1_M_1_Jnn_2_M_2 = 
  | RELAXED_DOT_ADDS

;; test.spectec:1080.8-1080.21
relation wf_vextternop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`fuck5(fuck1Jnn, fuck1M, fuck1Jnn, fuck1M, fuck1vextternop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1080.8-1080.21
  rule vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2)
    -- if (((4 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) = 32))

;; test.spectec:1080.1-1080.61
syntax vextternop__ = 
  | mk_vextternop___0fuck5(Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextternop__Jnn_1_M_1_Jnn_2_M_2)

;; test.spectec:1080.8-1080.21
relation wf_vextternop__: `%%%`fuck5(fuck1ishape, fuck1ishape, fuck1vextternop__)
  ;; test.spectec:1080.8-1080.21
  rule vextternop___case_0{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextternop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(ishape_1, ishape_2, mk_vextternop___0_vextternop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vextternop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (ishape_1 = `%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))))
    -- if (ishape_2 = `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))))

;; test.spectec:1080.1-1080.61
def $proj_vextternop___0(var_x : fuck1vextternop__) : fuck1vextternop__Jnn_1_M_1_Jnn_2_M_2
  ;; test.spectec:1080.8-1080.21
  def $proj_vextternop___0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vextternop__Jnn_1_M_1_Jnn_2_M_2}(mk_vextternop___0_vextternop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = var_x

;; test.spectec:1085.1-1085.55
syntax vcvtop__Jnn_1_M_1_Jnn_2_M_2 = 
  | EXTENDfuck5(half : fuck1half, sx : fuck1sx)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`fuck5(fuck1Jnn, fuck1M, fuck1Jnn, fuck1M, fuck1vcvtop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, half : fuck1half, sx : fuck1sx}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(half, sx))
    -- if ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) = (2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))))

;; test.spectec:1085.1-1085.55
syntax vcvtop__Jnn_1_M_1_Fnn_2_M_2 = 
  | CONVERTfuck5(`half?` : fuck6fuck1half?, sx : fuck1sx)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2: `%%%%%`fuck5(fuck1Jnn, fuck1M, fuck1Fnn, fuck1M, fuck1vcvtop__Jnn_1_M_1_Fnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, `half?` : fuck6fuck1half?, sx : fuck1sx}:
    `%%%%%`(Jnn_1, M_1, Fnn_2, M_2, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(`half?`, sx))
    -- if (((($sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)) = $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)) = 32)) /\ (half?{half <- `half?`} = ?())) \/ (($sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)) = (2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)))) /\ (half?{half <- `half?`} = ?(LOW_half))))

;; test.spectec:1085.1-1085.55
syntax vcvtop__Fnn_1_M_1_Jnn_2_M_2 = 
  | TRUNC_SATfuck5(sx : fuck1sx, `zero?` : fuck6fuck1zero?)
  | RELAXED_TRUNCfuck5(sx : fuck1sx, `zero?` : fuck6fuck1zero?)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2: `%%%%%`fuck5(fuck1Fnn, fuck1M, fuck1Jnn, fuck1M, fuck1vcvtop__Fnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0{Fnn_1 : fuck1Fnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, sx : fuck1sx, `zero?` : fuck6fuck1zero?}:
    `%%%%%`(Fnn_1, M_1, Jnn_2, M_2, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, `zero?`))
    -- if (((($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) = (2 * $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_1{Fnn_1 : fuck1Fnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, sx : fuck1sx, `zero?` : fuck6fuck1zero?}:
    `%%%%%`(Fnn_1, M_1, Jnn_2, M_2, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, `zero?`))
    -- if (((($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) = $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype))) /\ ($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) = (2 * $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))

;; test.spectec:1085.1-1085.55
syntax vcvtop__Fnn_1_M_1_Fnn_2_M_2 = 
  | DEMOTEfuck5(zero : fuck1zero)
  | PROMOTELOW

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2: `%%%%%`fuck5(fuck1Fnn, fuck1M, fuck1Fnn, fuck1M, fuck1vcvtop__Fnn_1_M_1_Fnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0{Fnn_1 : fuck1Fnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, zero : fuck1zero}:
    `%%%%%`(Fnn_1, M_1, Fnn_2, M_2, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(zero))
    -- if ($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)) = (2 * $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype))))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1{Fnn_1 : fuck1Fnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M}:
    `%%%%%`(Fnn_1, M_1, Fnn_2, M_2, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2)
    -- if ((2 * $sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype))) = $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)))

;; test.spectec:1085.1-1085.55
syntax vcvtop__ = 
  | mk_vcvtop___0fuck5(Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vcvtop__Jnn_1_M_1_Jnn_2_M_2)
  | mk_vcvtop___1fuck5(Jnn_1 : fuck1Jnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, var_x : fuck1vcvtop__Jnn_1_M_1_Fnn_2_M_2)
  | mk_vcvtop___2fuck5(Fnn_1 : fuck1Fnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vcvtop__Fnn_1_M_1_Jnn_2_M_2)
  | mk_vcvtop___3fuck5(Fnn_1 : fuck1Fnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, var_x : fuck1vcvtop__Fnn_1_M_1_Fnn_2_M_2)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__: `%%%`fuck5(fuck1shape, fuck1shape, fuck1vcvtop__)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_0{shape_1 : fuck1shape, shape_2 : fuck1shape, Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vcvtop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)))
    -- if (shape_2 = `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_1{shape_1 : fuck1shape, shape_2 : fuck1shape, Jnn_1 : fuck1Jnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, var_x : fuck1vcvtop__Jnn_1_M_1_Fnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, var_x))
    -- wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2: `%%%%%`(Jnn_1, M_1, Fnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)))
    -- if (shape_2 = `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_2{shape_1 : fuck1shape, shape_2 : fuck1shape, Fnn_1 : fuck1Fnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vcvtop__Fnn_1_M_1_Jnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2: `%%%%%`(Fnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)))
    -- if (shape_2 = `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_3{shape_1 : fuck1shape, shape_2 : fuck1shape, Fnn_1 : fuck1Fnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, var_x : fuck1vcvtop__Fnn_1_M_1_Fnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, var_x))
    -- wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2: `%%%%%`(Fnn_1, M_1, Fnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)))
    -- if (shape_2 = `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)))

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___0(var_x : fuck1vcvtop__) : fuck6fuck1vcvtop__Jnn_1_M_1_Jnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___0{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vcvtop__Jnn_1_M_1_Jnn_2_M_2}(mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___0{var_x : fuck1vcvtop__}(var_x) = ?()

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___1(var_x : fuck1vcvtop__) : fuck6fuck1vcvtop__Jnn_1_M_1_Fnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___1{Jnn_1 : fuck1Jnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, var_x : fuck1vcvtop__Jnn_1_M_1_Fnn_2_M_2}(mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___1{var_x : fuck1vcvtop__}(var_x) = ?()

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___2(var_x : fuck1vcvtop__) : fuck6fuck1vcvtop__Fnn_1_M_1_Jnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___2{Fnn_1 : fuck1Fnn, M_1 : fuck1M, Jnn_2 : fuck1Jnn, M_2 : fuck1M, var_x : fuck1vcvtop__Fnn_1_M_1_Jnn_2_M_2}(mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___2{var_x : fuck1vcvtop__}(var_x) = ?()

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___3(var_x : fuck1vcvtop__) : fuck6fuck1vcvtop__Fnn_1_M_1_Fnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___3{Fnn_1 : fuck1Fnn, M_1 : fuck1M, Fnn_2 : fuck1Fnn, M_2 : fuck1M, var_x : fuck1vcvtop__Fnn_1_M_1_Fnn_2_M_2}(mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___3{var_x : fuck1vcvtop__}(var_x) = ?()

;; test.spectec:1109.1-1109.69
syntax memarg = 
{
  ALIGN fuck1u32,
  OFFSET fuck1u64
}

;; test.spectec:1109.8-1109.14
relation wf_memarg: `%`fuck5(fuck1memarg)
  ;; test.spectec:1109.8-1109.14
  rule memarg_case_{var_0 : fuck1u32, var_1 : fuck1u64}:
    `%`({ALIGN var_0, OFFSET var_1})
    -- wf_uN: `%%`(32, var_0)
    -- wf_uN: `%%`(64, var_1)

;; test.spectec:1113.1-1113.24
syntax loadop_Inn = 
  | `%_%`fuck5(sz : fuck1sz, sx : fuck1sx)

;; test.spectec:1113.8-1113.16
relation wf_loadop_Inn: `%%`fuck5(fuck1Inn, fuck1loadop_Inn)
  ;; test.spectec:1113.8-1113.16
  rule loadop_Inn_case_0{Inn : fuck1Inn, sz : fuck1sz, sx : fuck1sx}:
    `%%`(Inn, `%_%`_loadop_Inn(sz, sx))
    -- wf_sz: `%`(sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : fuck1addrtype <: fuck1numtype)))

;; test.spectec:1113.1-1113.24
syntax loadop_ = 
  | mk_loadop__0fuck5(Inn : fuck1Inn, var_x : fuck1loadop_Inn)

;; test.spectec:1113.8-1113.16
relation wf_loadop_: `%%`fuck5(fuck1numtype, fuck1loadop_)
  ;; test.spectec:1113.8-1113.16
  rule loadop__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1loadop_Inn}:
    `%%`(numtype, mk_loadop__0_loadop_(Inn, var_x))
    -- wf_loadop_Inn: `%%`(Inn, var_x)
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

;; test.spectec:1113.1-1113.24
def $proj_loadop__0(var_x : fuck1loadop_) : fuck1loadop_Inn
  ;; test.spectec:1113.8-1113.16
  def $proj_loadop__0{Inn : fuck1Inn, var_x : fuck1loadop_Inn}(mk_loadop__0_loadop_(Inn, var_x)) = var_x

;; test.spectec:1116.1-1116.25
syntax storeop_Inn = 
  | `%`fuck5(sz : fuck1sz)

;; test.spectec:1116.8-1116.17
relation wf_storeop_Inn: `%%`fuck5(fuck1Inn, fuck1storeop_Inn)
  ;; test.spectec:1116.8-1116.17
  rule storeop_Inn_case_0{Inn : fuck1Inn, sz : fuck1sz}:
    `%%`(Inn, `%`_storeop_Inn(sz))
    -- wf_sz: `%`(sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : fuck1addrtype <: fuck1numtype)))

;; test.spectec:1116.1-1116.25
syntax storeop_ = 
  | mk_storeop__0fuck5(Inn : fuck1Inn, var_x : fuck1storeop_Inn)

;; test.spectec:1116.8-1116.17
relation wf_storeop_: `%%`fuck5(fuck1numtype, fuck1storeop_)
  ;; test.spectec:1116.8-1116.17
  rule storeop__case_0{numtype : fuck1numtype, Inn : fuck1Inn, var_x : fuck1storeop_Inn}:
    `%%`(numtype, mk_storeop__0_storeop_(Inn, var_x))
    -- wf_storeop_Inn: `%%`(Inn, var_x)
    -- if (numtype = (Inn : fuck1addrtype <: fuck1numtype))

;; test.spectec:1116.1-1116.25
def $proj_storeop__0(var_x : fuck1storeop_) : fuck1storeop_Inn
  ;; test.spectec:1116.8-1116.17
  def $proj_storeop__0{Inn : fuck1Inn, var_x : fuck1storeop_Inn}(mk_storeop__0_storeop_(Inn, var_x)) = var_x

;; test.spectec:1119.1-1122.59
syntax vloadop_ = 
  | `SHAPE%X%_%`fuck5(sz : fuck1sz, M : fuck1M, sx : fuck1sx)
  | SPLATfuck5(sz : fuck1sz)
  | ZEROfuck5(sz : fuck1sz)

;; test.spectec:1119.8-1119.17
relation wf_vloadop_: `%%`fuck5(fuck1vectype, fuck1vloadop_)
  ;; test.spectec:1119.8-1119.17
  rule vloadop__case_0{vectype : fuck1vectype, sz : fuck1sz, M : fuck1M, sx : fuck1sx}:
    `%%`(vectype, `SHAPE%X%_%`_vloadop_(sz, M, sx))
    -- wf_sz: `%`(sz)
    -- if (((sz!`%`_sz.0 * M) : nat <:> rat) = (($vsize(vectype) : nat <:> rat) / (2 : nat <:> rat)))

  ;; test.spectec:1119.8-1119.17
  rule vloadop__case_1{vectype : fuck1vectype, sz : fuck1sz}:
    `%%`(vectype, SPLAT_vloadop_(sz))
    -- wf_sz: `%`(sz)

  ;; test.spectec:1119.8-1119.17
  rule vloadop__case_2{vectype : fuck1vectype, sz : fuck1sz}:
    `%%`(vectype, ZERO_vloadop_(sz))
    -- wf_sz: `%`(sz)
    -- if (sz!`%`_sz.0 >= 32)

;; test.spectec:1127.1-1129.17
syntax blocktype = 
  | _RESULTfuck5(`valtype?` : fuck6fuck1valtype?)
  | _IDXfuck5(typeidx : fuck1typeidx)

;; test.spectec:1127.8-1127.17
relation wf_blocktype: `%`fuck5(fuck1blocktype)
  ;; test.spectec:1127.8-1127.17
  rule blocktype_case_0{`valtype?` : fuck6fuck1valtype?}:
    `%`(_RESULT_blocktype(`valtype?`))
    -- (wf_valtype: `%`(valtype))?{valtype <- `valtype?`}

  ;; test.spectec:1127.8-1127.17
  rule blocktype_case_1{typeidx : fuck1typeidx}:
    `%`(_IDX_blocktype(typeidx))
    -- wf_uN: `%%`(32, typeidx)

;; test.spectec:4102.1-4102.39
syntax addr = fuck3nat

;; test.spectec:4111.1-4111.51
syntax arrayaddr = fuck1addr

;; test.spectec:1177.1-1181.27
syntax catch = 
  | CATCHfuck5(tagidx : fuck1tagidx, labelidx : fuck1labelidx)
  | CATCH_REFfuck5(tagidx : fuck1tagidx, labelidx : fuck1labelidx)
  | CATCH_ALLfuck5(labelidx : fuck1labelidx)
  | CATCH_ALL_REFfuck5(labelidx : fuck1labelidx)

;; test.spectec:1177.8-1177.13
relation wf_catch: `%`fuck5(fuck1catch)
  ;; test.spectec:1177.8-1177.13
  rule catch_case_0{tagidx : fuck1tagidx, labelidx : fuck1labelidx}:
    `%`(CATCH_catch(tagidx, labelidx))
    -- wf_uN: `%%`(32, tagidx)
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:1177.8-1177.13
  rule catch_case_1{tagidx : fuck1tagidx, labelidx : fuck1labelidx}:
    `%`(CATCH_REF_catch(tagidx, labelidx))
    -- wf_uN: `%%`(32, tagidx)
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:1177.8-1177.13
  rule catch_case_2{labelidx : fuck1labelidx}:
    `%`(CATCH_ALL_catch(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:1177.8-1177.13
  rule catch_case_3{labelidx : fuck1labelidx}:
    `%`(CATCH_ALL_REF_catch(labelidx))
    -- wf_uN: `%%`(32, labelidx)

;; test.spectec:4112.1-4112.53
syntax exnaddr = fuck1addr

;; test.spectec:4108.1-4108.49
syntax dataaddr = fuck1addr

;; test.spectec:4109.1-4109.49
syntax elemaddr = fuck1addr

;; test.spectec:4107.1-4107.53
syntax funcaddr = fuck1addr

;; test.spectec:4104.1-4104.53
syntax globaladdr = fuck1addr

;; test.spectec:4105.1-4105.50
syntax memaddr = fuck1addr

;; test.spectec:4106.1-4106.51
syntax tableaddr = fuck1addr

;; test.spectec:4103.1-4103.47
syntax tagaddr = fuck1addr

;; test.spectec:4115.1-4116.84
syntax externaddr = 
  | TAGfuck5(tagaddr : fuck1tagaddr)
  | GLOBALfuck5(globaladdr : fuck1globaladdr)
  | MEMfuck5(memaddr : fuck1memaddr)
  | TABLEfuck5(tableaddr : fuck1tableaddr)
  | FUNCfuck5(funcaddr : fuck1funcaddr)

;; test.spectec:4176.1-4177.33
syntax exportinst = 
{
  NAME fuck1name,
  ADDR fuck1externaddr
}

;; test.spectec:4176.8-4176.18
relation wf_exportinst: `%`fuck5(fuck1exportinst)
  ;; test.spectec:4176.8-4176.18
  rule exportinst_case_{var_0 : fuck1name, var_1 : fuck1externaddr}:
    `%`({NAME var_0, ADDR var_1})
    -- wf_name: `%`(var_0)

;; test.spectec:4196.1-4205.26
syntax moduleinst = 
{
  TYPES fuck6fuck1deftype*,
  TAGS fuck6fuck1tagaddr*,
  GLOBALS fuck6fuck1globaladdr*,
  MEMS fuck6fuck1memaddr*,
  TABLES fuck6fuck1tableaddr*,
  FUNCS fuck6fuck1funcaddr*,
  DATAS fuck6fuck1dataaddr*,
  ELEMS fuck6fuck1elemaddr*,
  EXPORTS fuck6fuck1exportinst*
}

;; test.spectec:4196.8-4196.18
relation wf_moduleinst: `%`fuck5(fuck1moduleinst)
  ;; test.spectec:4196.8-4196.18
  rule moduleinst_case_{`var_0*` : fuck6fuck1deftype*, `var_1*` : fuck6fuck1tagaddr*, `var_2*` : fuck6fuck1globaladdr*, `var_3*` : fuck6fuck1memaddr*, `var_4*` : fuck6fuck1tableaddr*, `var_5*` : fuck6fuck1funcaddr*, `var_6*` : fuck6fuck1dataaddr*, `var_7*` : fuck6fuck1elemaddr*, `var_8*` : fuck6fuck1exportinst*}:
    `%`({TYPES `var_0*`, TAGS `var_1*`, GLOBALS `var_2*`, MEMS `var_3*`, TABLES `var_4*`, FUNCS `var_5*`, DATAS `var_6*`, ELEMS `var_7*`, EXPORTS `var_8*`})
    -- (wf_exportinst: `%`(var_8))*{var_8 <- `var_8*`}

;; test.spectec:4113.1-4113.49
syntax hostaddr = fuck1addr

;; test.spectec:4110.1-4110.56
syntax structaddr = fuck1addr

;; test.spectec:4130.1-4138.19
rec {

;; test.spectec:4130.1-4138.19
syntax ref = 
  | `REF.I31_NUM`fuck5(u31 : fuck1u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`fuck5(structaddr : fuck1structaddr)
  | `REF.ARRAY_ADDR`fuck5(arrayaddr : fuck1arrayaddr)
  | `REF.FUNC_ADDR`fuck5(funcaddr : fuck1funcaddr)
  | `REF.EXN_ADDR`fuck5(exnaddr : fuck1exnaddr)
  | `REF.HOST_ADDR`fuck5(hostaddr : fuck1hostaddr)
  | `REF.EXTERN`fuck5(ref : fuck1ref)
}

;; test.spectec:4130.1-4138.19
rec {

;; test.spectec:4130.8-4130.11
relation wf_ref: `%`fuck5(fuck1ref)
  ;; test.spectec:4130.8-4130.11
  rule ref_case_0{u31 : fuck1u31}:
    `%`(`REF.I31_NUM`_ref(u31))
    -- wf_uN: `%%`(31, u31)

  ;; test.spectec:4130.8-4130.11
  rule ref_case_1:
    `%`(`REF.NULL_ADDR`_ref)

  ;; test.spectec:4130.8-4130.11
  rule ref_case_2{structaddr : fuck1structaddr}:
    `%`(`REF.STRUCT_ADDR`_ref(structaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_3{arrayaddr : fuck1arrayaddr}:
    `%`(`REF.ARRAY_ADDR`_ref(arrayaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_4{funcaddr : fuck1funcaddr}:
    `%`(`REF.FUNC_ADDR`_ref(funcaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_5{exnaddr : fuck1exnaddr}:
    `%`(`REF.EXN_ADDR`_ref(exnaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_6{hostaddr : fuck1hostaddr}:
    `%`(`REF.HOST_ADDR`_ref(hostaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_7{ref : fuck1ref}:
    `%`(`REF.EXTERN`_ref(ref))
}

;; test.spectec:4140.1-4141.20
syntax val = 
  | CONSTfuck5(numtype : fuck1numtype, fuck1num_)
  | VCONSTfuck5(vectype : fuck1vectype, fuck1vec_)
  | `REF.I31_NUM`fuck5(u31 : fuck1u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`fuck5(structaddr : fuck1structaddr)
  | `REF.ARRAY_ADDR`fuck5(arrayaddr : fuck1arrayaddr)
  | `REF.FUNC_ADDR`fuck5(funcaddr : fuck1funcaddr)
  | `REF.EXN_ADDR`fuck5(exnaddr : fuck1exnaddr)
  | `REF.HOST_ADDR`fuck5(hostaddr : fuck1hostaddr)
  | `REF.EXTERN`fuck5(ref : fuck1ref)

;; test.spectec:4140.8-4140.11
relation wf_val: `%`fuck5(fuck1val)
  ;; test.spectec:4140.8-4140.11
  rule val_case_0{numtype : fuck1numtype, var_0 : fuck1num_}:
    `%`(CONST_val(numtype, var_0))
    -- wf_num_: `%%`(numtype, var_0)

  ;; test.spectec:4140.8-4140.11
  rule val_case_1{vectype : fuck1vectype, var_0 : fuck1vec_}:
    `%`(VCONST_val(vectype, var_0))
    -- wf_uN: `%%`($vsize(vectype), var_0)

  ;; test.spectec:4140.8-4140.11
  rule val_case_2{u31 : fuck1u31}:
    `%`(`REF.I31_NUM`_val(u31))
    -- wf_uN: `%%`(31, u31)

  ;; test.spectec:4140.8-4140.11
  rule val_case_3:
    `%`(`REF.NULL_ADDR`_val)

  ;; test.spectec:4140.8-4140.11
  rule val_case_4{structaddr : fuck1structaddr}:
    `%`(`REF.STRUCT_ADDR`_val(structaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_5{arrayaddr : fuck1arrayaddr}:
    `%`(`REF.ARRAY_ADDR`_val(arrayaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_6{funcaddr : fuck1funcaddr}:
    `%`(`REF.FUNC_ADDR`_val(funcaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_7{exnaddr : fuck1exnaddr}:
    `%`(`REF.EXN_ADDR`_val(exnaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_8{hostaddr : fuck1hostaddr}:
    `%`(`REF.HOST_ADDR`_val(hostaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_9{ref : fuck1ref}:
    `%`(`REF.EXTERN`_val(ref))
    -- wf_ref: `%`(ref)

;; test.spectec:4222.1-4223.40
syntax frame = 
{
  LOCALS fuck6fuck6fuck1val?*,
  MODULE fuck1moduleinst
}

;; test.spectec:4222.8-4222.13
relation wf_frame: `%`fuck5(fuck1frame)
  ;; test.spectec:4222.8-4222.13
  rule frame_case_{`var_0?*` : fuck6fuck6fuck1val?*, var_1 : fuck1moduleinst}:
    `%`({LOCALS `var_0?*`, MODULE var_1})
    -- (wf_val: `%`(var_0))?{var_0 <- `var_0?`}*{`var_0?` <- `var_0?*`}
    -- wf_moduleinst: `%`(var_1)

;; test.spectec:4228.1-4234.9
rec {

;; test.spectec:4228.1-4234.9
syntax instr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECTfuck5(`valtype*?` : fuck6fuck6fuck1valtype*?)
  | BLOCKfuck5(blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*)
  | LOOPfuck5(blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*)
  | `IF%%ELSE%`fuck5(blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*, `instr*` : fuck6fuck1instr*)
  | BRfuck5(labelidx : fuck1labelidx)
  | BR_IFfuck5(labelidx : fuck1labelidx)
  | BR_TABLEfuck5(`labelidx*` : fuck6fuck1labelidx*, labelidx : fuck1labelidx)
  | BR_ON_NULLfuck5(labelidx : fuck1labelidx)
  | BR_ON_NON_NULLfuck5(labelidx : fuck1labelidx)
  | BR_ON_CASTfuck5(labelidx : fuck1labelidx, reftype : fuck1reftype, reftype : fuck1reftype)
  | BR_ON_CAST_FAILfuck5(labelidx : fuck1labelidx, reftype : fuck1reftype, reftype : fuck1reftype)
  | CALLfuck5(funcidx : fuck1funcidx)
  | CALL_REFfuck5(typeuse : fuck1typeuse)
  | CALL_INDIRECTfuck5(tableidx : fuck1tableidx, typeuse : fuck1typeuse)
  | RETURN
  | RETURN_CALLfuck5(funcidx : fuck1funcidx)
  | RETURN_CALL_REFfuck5(typeuse : fuck1typeuse)
  | RETURN_CALL_INDIRECTfuck5(tableidx : fuck1tableidx, typeuse : fuck1typeuse)
  | THROWfuck5(tagidx : fuck1tagidx)
  | THROW_REF
  | TRY_TABLEfuck5(blocktype : fuck1blocktype, fuck1list(syntax fuck1catch), `instr*` : fuck6fuck1instr*)
  | `LOCAL.GET`fuck5(localidx : fuck1localidx)
  | `LOCAL.SET`fuck5(localidx : fuck1localidx)
  | `LOCAL.TEE`fuck5(localidx : fuck1localidx)
  | `GLOBAL.GET`fuck5(globalidx : fuck1globalidx)
  | `GLOBAL.SET`fuck5(globalidx : fuck1globalidx)
  | `TABLE.GET`fuck5(tableidx : fuck1tableidx)
  | `TABLE.SET`fuck5(tableidx : fuck1tableidx)
  | `TABLE.SIZE`fuck5(tableidx : fuck1tableidx)
  | `TABLE.GROW`fuck5(tableidx : fuck1tableidx)
  | `TABLE.FILL`fuck5(tableidx : fuck1tableidx)
  | `TABLE.COPY`fuck5(tableidx : fuck1tableidx, tableidx : fuck1tableidx)
  | `TABLE.INIT`fuck5(tableidx : fuck1tableidx, elemidx : fuck1elemidx)
  | `ELEM.DROP`fuck5(elemidx : fuck1elemidx)
  | LOADfuck5(numtype : fuck1numtype, fuck6fuck1loadop_?, memidx : fuck1memidx, memarg : fuck1memarg)
  | STOREfuck5(numtype : fuck1numtype, fuck6fuck1storeop_?, memidx : fuck1memidx, memarg : fuck1memarg)
  | VLOADfuck5(vectype : fuck1vectype, fuck6fuck1vloadop_?, memidx : fuck1memidx, memarg : fuck1memarg)
  | VLOAD_LANEfuck5(vectype : fuck1vectype, sz : fuck1sz, memidx : fuck1memidx, memarg : fuck1memarg, laneidx : fuck1laneidx)
  | VSTOREfuck5(vectype : fuck1vectype, memidx : fuck1memidx, memarg : fuck1memarg)
  | VSTORE_LANEfuck5(vectype : fuck1vectype, sz : fuck1sz, memidx : fuck1memidx, memarg : fuck1memarg, laneidx : fuck1laneidx)
  | `MEMORY.SIZE`fuck5(memidx : fuck1memidx)
  | `MEMORY.GROW`fuck5(memidx : fuck1memidx)
  | `MEMORY.FILL`fuck5(memidx : fuck1memidx)
  | `MEMORY.COPY`fuck5(memidx : fuck1memidx, memidx : fuck1memidx)
  | `MEMORY.INIT`fuck5(memidx : fuck1memidx, dataidx : fuck1dataidx)
  | `DATA.DROP`fuck5(dataidx : fuck1dataidx)
  | `REF.NULL`fuck5(heaptype : fuck1heaptype)
  | `REF.IS_NULL`
  | `REF.AS_NON_NULL`
  | `REF.EQ`
  | `REF.TEST`fuck5(reftype : fuck1reftype)
  | `REF.CAST`fuck5(reftype : fuck1reftype)
  | `REF.FUNC`fuck5(funcidx : fuck1funcidx)
  | `REF.I31`
  | `I31.GET`fuck5(sx : fuck1sx)
  | `STRUCT.NEW`fuck5(typeidx : fuck1typeidx)
  | `STRUCT.NEW_DEFAULT`fuck5(typeidx : fuck1typeidx)
  | `STRUCT.GET`fuck5(`sx?` : fuck6fuck1sx?, typeidx : fuck1typeidx, fieldidx : fuck1fieldidx)
  | `STRUCT.SET`fuck5(typeidx : fuck1typeidx, fieldidx : fuck1fieldidx)
  | `ARRAY.NEW`fuck5(typeidx : fuck1typeidx)
  | `ARRAY.NEW_DEFAULT`fuck5(typeidx : fuck1typeidx)
  | `ARRAY.NEW_FIXED`fuck5(typeidx : fuck1typeidx, u32 : fuck1u32)
  | `ARRAY.NEW_DATA`fuck5(typeidx : fuck1typeidx, dataidx : fuck1dataidx)
  | `ARRAY.NEW_ELEM`fuck5(typeidx : fuck1typeidx, elemidx : fuck1elemidx)
  | `ARRAY.GET`fuck5(`sx?` : fuck6fuck1sx?, typeidx : fuck1typeidx)
  | `ARRAY.SET`fuck5(typeidx : fuck1typeidx)
  | `ARRAY.LEN`
  | `ARRAY.FILL`fuck5(typeidx : fuck1typeidx)
  | `ARRAY.COPY`fuck5(typeidx : fuck1typeidx, typeidx : fuck1typeidx)
  | `ARRAY.INIT_DATA`fuck5(typeidx : fuck1typeidx, dataidx : fuck1dataidx)
  | `ARRAY.INIT_ELEM`fuck5(typeidx : fuck1typeidx, elemidx : fuck1elemidx)
  | `EXTERN.CONVERT_ANY`
  | `ANY.CONVERT_EXTERN`
  | CONSTfuck5(numtype : fuck1numtype, fuck1num_)
  | UNOPfuck5(numtype : fuck1numtype, fuck1unop_)
  | BINOPfuck5(numtype : fuck1numtype, fuck1binop_)
  | TESTOPfuck5(numtype : fuck1numtype, fuck1testop_)
  | RELOPfuck5(numtype : fuck1numtype, fuck1relop_)
  | CVTOPfuck5(numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, fuck1cvtop__)
  | VCONSTfuck5(vectype : fuck1vectype, fuck1vec_)
  | VVUNOPfuck5(vectype : fuck1vectype, vvunop : fuck1vvunop)
  | VVBINOPfuck5(vectype : fuck1vectype, vvbinop : fuck1vvbinop)
  | VVTERNOPfuck5(vectype : fuck1vectype, vvternop : fuck1vvternop)
  | VVTESTOPfuck5(vectype : fuck1vectype, vvtestop : fuck1vvtestop)
  | VUNOPfuck5(shape : fuck1shape, fuck1vunop_)
  | VBINOPfuck5(shape : fuck1shape, fuck1vbinop_)
  | VTERNOPfuck5(shape : fuck1shape, fuck1vternop_)
  | VTESTOPfuck5(shape : fuck1shape, fuck1vtestop_)
  | VRELOPfuck5(shape : fuck1shape, fuck1vrelop_)
  | VSHIFTOPfuck5(ishape : fuck1ishape, fuck1vshiftop_)
  | VBITMASKfuck5(ishape : fuck1ishape)
  | VSWIZZLOPfuck5(bshape : fuck1bshape, fuck1vswizzlop_)
  | VSHUFFLEfuck5(bshape : fuck1bshape, `laneidx*` : fuck6fuck1laneidx*)
  | VEXTUNOPfuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, fuck1vextunop__)
  | VEXTBINOPfuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, fuck1vextbinop__)
  | VEXTTERNOPfuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, fuck1vextternop__)
  | VNARROWfuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, sx : fuck1sx)
  | VCVTOPfuck5(shape_1 : fuck1shape, shape_2 : fuck1shape, fuck1vcvtop__)
  | VSPLATfuck5(shape : fuck1shape)
  | VEXTRACT_LANEfuck5(shape : fuck1shape, `sx?` : fuck6fuck1sx?, laneidx : fuck1laneidx)
  | VREPLACE_LANEfuck5(shape : fuck1shape, laneidx : fuck1laneidx)
  | `REF.I31_NUM`fuck5(u31 : fuck1u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`fuck5(structaddr : fuck1structaddr)
  | `REF.ARRAY_ADDR`fuck5(arrayaddr : fuck1arrayaddr)
  | `REF.FUNC_ADDR`fuck5(funcaddr : fuck1funcaddr)
  | `REF.EXN_ADDR`fuck5(exnaddr : fuck1exnaddr)
  | `REF.HOST_ADDR`fuck5(hostaddr : fuck1hostaddr)
  | `REF.EXTERN`fuck5(ref : fuck1ref)
  | `LABEL_%{%}%`fuck5(n : fuck1n, `instr*` : fuck6fuck1instr*, `instr*` : fuck6fuck1instr*)
  | `FRAME_%{%}%`fuck5(n : fuck1n, frame : fuck1frame, `instr*` : fuck6fuck1instr*)
  | `HANDLER_%{%}%`fuck5(n : fuck1n, `catch*` : fuck6fuck1catch*, `instr*` : fuck6fuck1instr*)
  | TRAP
}

;; test.spectec:4228.1-4234.9
rec {

;; test.spectec:4228.8-4228.13
relation wf_instr: `%`fuck5(fuck1instr)
  ;; test.spectec:4228.8-4228.13
  rule instr_case_0:
    `%`(NOP_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_1:
    `%`(UNREACHABLE_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_2:
    `%`(DROP_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_3{`valtype*?` : fuck6fuck6fuck1valtype*?}:
    `%`(SELECT_instr(`valtype*?`))
    -- (wf_valtype: `%`(valtype))*{valtype <- `valtype*`}?{`valtype*` <- `valtype*?`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_4{blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*}:
    `%`(BLOCK_instr(blocktype, `instr*`))
    -- wf_blocktype: `%`(blocktype)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_5{blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*}:
    `%`(LOOP_instr(blocktype, `instr*`))
    -- wf_blocktype: `%`(blocktype)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_6{blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*, `instr*_0*` : fuck6fuck1instr*}:
    `%`(`IF%%ELSE%`_instr(blocktype, `instr*`, `instr*_0*`))
    -- wf_blocktype: `%`(blocktype)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- (wf_instr: `%`(`instr*_0`))*{`instr*_0` <- `instr*_0*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_7{labelidx : fuck1labelidx}:
    `%`(BR_instr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_8{labelidx : fuck1labelidx}:
    `%`(BR_IF_instr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_9{`labelidx*` : fuck6fuck1labelidx*, labelidx : fuck1labelidx}:
    `%`(BR_TABLE_instr(`labelidx*`, labelidx))
    -- (wf_uN: `%%`(32, labelidx))*{labelidx <- `labelidx*`}
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_10{labelidx : fuck1labelidx}:
    `%`(BR_ON_NULL_instr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_11{labelidx : fuck1labelidx}:
    `%`(BR_ON_NON_NULL_instr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_12{labelidx : fuck1labelidx, reftype : fuck1reftype, reftype_0 : fuck1reftype}:
    `%`(BR_ON_CAST_instr(labelidx, reftype, reftype_0))
    -- wf_uN: `%%`(32, labelidx)
    -- wf_reftype: `%`(reftype)
    -- wf_reftype: `%`(reftype_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_13{labelidx : fuck1labelidx, reftype : fuck1reftype, reftype_0 : fuck1reftype}:
    `%`(BR_ON_CAST_FAIL_instr(labelidx, reftype, reftype_0))
    -- wf_uN: `%%`(32, labelidx)
    -- wf_reftype: `%`(reftype)
    -- wf_reftype: `%`(reftype_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_14{funcidx : fuck1funcidx}:
    `%`(CALL_instr(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_15{typeuse : fuck1typeuse}:
    `%`(CALL_REF_instr(typeuse))
    -- wf_typeuse: `%`(typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_16{tableidx : fuck1tableidx, typeuse : fuck1typeuse}:
    `%`(CALL_INDIRECT_instr(tableidx, typeuse))
    -- wf_uN: `%%`(32, tableidx)
    -- wf_typeuse: `%`(typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_17:
    `%`(RETURN_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_18{funcidx : fuck1funcidx}:
    `%`(RETURN_CALL_instr(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_19{typeuse : fuck1typeuse}:
    `%`(RETURN_CALL_REF_instr(typeuse))
    -- wf_typeuse: `%`(typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_20{tableidx : fuck1tableidx, typeuse : fuck1typeuse}:
    `%`(RETURN_CALL_INDIRECT_instr(tableidx, typeuse))
    -- wf_uN: `%%`(32, tableidx)
    -- wf_typeuse: `%`(typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_21{tagidx : fuck1tagidx}:
    `%`(THROW_instr(tagidx))
    -- wf_uN: `%%`(32, tagidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_22:
    `%`(THROW_REF_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_23{blocktype : fuck1blocktype, var_0 : fuck1list(syntax fuck1catch), `instr*` : fuck6fuck1instr*}:
    `%`(TRY_TABLE_instr(blocktype, var_0, `instr*`))
    -- wf_blocktype: `%`(blocktype)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_24{localidx : fuck1localidx}:
    `%`(`LOCAL.GET`_instr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_25{localidx : fuck1localidx}:
    `%`(`LOCAL.SET`_instr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_26{localidx : fuck1localidx}:
    `%`(`LOCAL.TEE`_instr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_27{globalidx : fuck1globalidx}:
    `%`(`GLOBAL.GET`_instr(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_28{globalidx : fuck1globalidx}:
    `%`(`GLOBAL.SET`_instr(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_29{tableidx : fuck1tableidx}:
    `%`(`TABLE.GET`_instr(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_30{tableidx : fuck1tableidx}:
    `%`(`TABLE.SET`_instr(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_31{tableidx : fuck1tableidx}:
    `%`(`TABLE.SIZE`_instr(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_32{tableidx : fuck1tableidx}:
    `%`(`TABLE.GROW`_instr(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_33{tableidx : fuck1tableidx}:
    `%`(`TABLE.FILL`_instr(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_34{tableidx : fuck1tableidx, tableidx_0 : fuck1tableidx}:
    `%`(`TABLE.COPY`_instr(tableidx, tableidx_0))
    -- wf_uN: `%%`(32, tableidx)
    -- wf_uN: `%%`(32, tableidx_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_35{tableidx : fuck1tableidx, elemidx : fuck1elemidx}:
    `%`(`TABLE.INIT`_instr(tableidx, elemidx))
    -- wf_uN: `%%`(32, tableidx)
    -- wf_uN: `%%`(32, elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_36{elemidx : fuck1elemidx}:
    `%`(`ELEM.DROP`_instr(elemidx))
    -- wf_uN: `%%`(32, elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_37{numtype : fuck1numtype, `var_0?` : fuck6fuck1loadop_?, memidx : fuck1memidx, memarg : fuck1memarg}:
    `%`(LOAD_instr(numtype, `var_0?`, memidx, memarg))
    -- (wf_loadop_: `%%`(numtype, var_0))?{var_0 <- `var_0?`}
    -- wf_uN: `%%`(32, memidx)
    -- wf_memarg: `%`(memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_38{numtype : fuck1numtype, `var_0?` : fuck6fuck1storeop_?, memidx : fuck1memidx, memarg : fuck1memarg}:
    `%`(STORE_instr(numtype, `var_0?`, memidx, memarg))
    -- (wf_storeop_: `%%`(numtype, var_0))?{var_0 <- `var_0?`}
    -- wf_uN: `%%`(32, memidx)
    -- wf_memarg: `%`(memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_39{vectype : fuck1vectype, `var_0?` : fuck6fuck1vloadop_?, memidx : fuck1memidx, memarg : fuck1memarg}:
    `%`(VLOAD_instr(vectype, `var_0?`, memidx, memarg))
    -- (wf_vloadop_: `%%`(vectype, var_0))?{var_0 <- `var_0?`}
    -- wf_uN: `%%`(32, memidx)
    -- wf_memarg: `%`(memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_40{vectype : fuck1vectype, sz : fuck1sz, memidx : fuck1memidx, memarg : fuck1memarg, laneidx : fuck1laneidx}:
    `%`(VLOAD_LANE_instr(vectype, sz, memidx, memarg, laneidx))
    -- wf_sz: `%`(sz)
    -- wf_uN: `%%`(32, memidx)
    -- wf_memarg: `%`(memarg)
    -- wf_uN: `%%`(8, laneidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_41{vectype : fuck1vectype, memidx : fuck1memidx, memarg : fuck1memarg}:
    `%`(VSTORE_instr(vectype, memidx, memarg))
    -- wf_uN: `%%`(32, memidx)
    -- wf_memarg: `%`(memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_42{vectype : fuck1vectype, sz : fuck1sz, memidx : fuck1memidx, memarg : fuck1memarg, laneidx : fuck1laneidx}:
    `%`(VSTORE_LANE_instr(vectype, sz, memidx, memarg, laneidx))
    -- wf_sz: `%`(sz)
    -- wf_uN: `%%`(32, memidx)
    -- wf_memarg: `%`(memarg)
    -- wf_uN: `%%`(8, laneidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_43{memidx : fuck1memidx}:
    `%`(`MEMORY.SIZE`_instr(memidx))
    -- wf_uN: `%%`(32, memidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_44{memidx : fuck1memidx}:
    `%`(`MEMORY.GROW`_instr(memidx))
    -- wf_uN: `%%`(32, memidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_45{memidx : fuck1memidx}:
    `%`(`MEMORY.FILL`_instr(memidx))
    -- wf_uN: `%%`(32, memidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_46{memidx : fuck1memidx, memidx_0 : fuck1memidx}:
    `%`(`MEMORY.COPY`_instr(memidx, memidx_0))
    -- wf_uN: `%%`(32, memidx)
    -- wf_uN: `%%`(32, memidx_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_47{memidx : fuck1memidx, dataidx : fuck1dataidx}:
    `%`(`MEMORY.INIT`_instr(memidx, dataidx))
    -- wf_uN: `%%`(32, memidx)
    -- wf_uN: `%%`(32, dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_48{dataidx : fuck1dataidx}:
    `%`(`DATA.DROP`_instr(dataidx))
    -- wf_uN: `%%`(32, dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_49{heaptype : fuck1heaptype}:
    `%`(`REF.NULL`_instr(heaptype))
    -- wf_heaptype: `%`(heaptype)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_50:
    `%`(`REF.IS_NULL`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_51:
    `%`(`REF.AS_NON_NULL`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_52:
    `%`(`REF.EQ`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_53{reftype : fuck1reftype}:
    `%`(`REF.TEST`_instr(reftype))
    -- wf_reftype: `%`(reftype)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_54{reftype : fuck1reftype}:
    `%`(`REF.CAST`_instr(reftype))
    -- wf_reftype: `%`(reftype)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_55{funcidx : fuck1funcidx}:
    `%`(`REF.FUNC`_instr(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_56:
    `%`(`REF.I31`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_57{sx : fuck1sx}:
    `%`(`I31.GET`_instr(sx))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_58{typeidx : fuck1typeidx}:
    `%`(`STRUCT.NEW`_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_59{typeidx : fuck1typeidx}:
    `%`(`STRUCT.NEW_DEFAULT`_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_60{`sx?` : fuck6fuck1sx?, typeidx : fuck1typeidx, fieldidx : fuck1fieldidx}:
    `%`(`STRUCT.GET`_instr(`sx?`, typeidx, fieldidx))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, fieldidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_61{typeidx : fuck1typeidx, fieldidx : fuck1fieldidx}:
    `%`(`STRUCT.SET`_instr(typeidx, fieldidx))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, fieldidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_62{typeidx : fuck1typeidx}:
    `%`(`ARRAY.NEW`_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_63{typeidx : fuck1typeidx}:
    `%`(`ARRAY.NEW_DEFAULT`_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_64{typeidx : fuck1typeidx, u32 : fuck1u32}:
    `%`(`ARRAY.NEW_FIXED`_instr(typeidx, u32))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, u32)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_65{typeidx : fuck1typeidx, dataidx : fuck1dataidx}:
    `%`(`ARRAY.NEW_DATA`_instr(typeidx, dataidx))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_66{typeidx : fuck1typeidx, elemidx : fuck1elemidx}:
    `%`(`ARRAY.NEW_ELEM`_instr(typeidx, elemidx))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_67{`sx?` : fuck6fuck1sx?, typeidx : fuck1typeidx}:
    `%`(`ARRAY.GET`_instr(`sx?`, typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_68{typeidx : fuck1typeidx}:
    `%`(`ARRAY.SET`_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_69:
    `%`(`ARRAY.LEN`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_70{typeidx : fuck1typeidx}:
    `%`(`ARRAY.FILL`_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_71{typeidx : fuck1typeidx, typeidx_0 : fuck1typeidx}:
    `%`(`ARRAY.COPY`_instr(typeidx, typeidx_0))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, typeidx_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_72{typeidx : fuck1typeidx, dataidx : fuck1dataidx}:
    `%`(`ARRAY.INIT_DATA`_instr(typeidx, dataidx))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_73{typeidx : fuck1typeidx, elemidx : fuck1elemidx}:
    `%`(`ARRAY.INIT_ELEM`_instr(typeidx, elemidx))
    -- wf_uN: `%%`(32, typeidx)
    -- wf_uN: `%%`(32, elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_74:
    `%`(`EXTERN.CONVERT_ANY`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_75:
    `%`(`ANY.CONVERT_EXTERN`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_76{numtype : fuck1numtype, var_0 : fuck1num_}:
    `%`(CONST_instr(numtype, var_0))
    -- wf_num_: `%%`(numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_77{numtype : fuck1numtype, var_0 : fuck1unop_}:
    `%`(UNOP_instr(numtype, var_0))
    -- wf_unop_: `%%`(numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_78{numtype : fuck1numtype, var_0 : fuck1binop_}:
    `%`(BINOP_instr(numtype, var_0))
    -- wf_binop_: `%%`(numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_79{numtype : fuck1numtype, var_0 : fuck1testop_}:
    `%`(TESTOP_instr(numtype, var_0))
    -- wf_testop_: `%%`(numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_80{numtype : fuck1numtype, var_0 : fuck1relop_}:
    `%`(RELOP_instr(numtype, var_0))
    -- wf_relop_: `%%`(numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_81{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, var_0 : fuck1cvtop__}:
    `%`(CVTOP_instr(numtype_1, numtype_2, var_0))
    -- wf_cvtop__: `%%%`(numtype_2, numtype_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_82{vectype : fuck1vectype, var_0 : fuck1vec_}:
    `%`(VCONST_instr(vectype, var_0))
    -- wf_uN: `%%`($vsize(vectype), var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_83{vectype : fuck1vectype, vvunop : fuck1vvunop}:
    `%`(VVUNOP_instr(vectype, vvunop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_84{vectype : fuck1vectype, vvbinop : fuck1vvbinop}:
    `%`(VVBINOP_instr(vectype, vvbinop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_85{vectype : fuck1vectype, vvternop : fuck1vvternop}:
    `%`(VVTERNOP_instr(vectype, vvternop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_86{vectype : fuck1vectype, vvtestop : fuck1vvtestop}:
    `%`(VVTESTOP_instr(vectype, vvtestop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_87{shape : fuck1shape, var_0 : fuck1vunop_}:
    `%`(VUNOP_instr(shape, var_0))
    -- wf_shape: `%`(shape)
    -- wf_vunop_: `%%`(shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_88{shape : fuck1shape, var_0 : fuck1vbinop_}:
    `%`(VBINOP_instr(shape, var_0))
    -- wf_shape: `%`(shape)
    -- wf_vbinop_: `%%`(shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_89{shape : fuck1shape, var_0 : fuck1vternop_}:
    `%`(VTERNOP_instr(shape, var_0))
    -- wf_shape: `%`(shape)
    -- wf_vternop_: `%%`(shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_90{shape : fuck1shape, var_0 : fuck1vtestop_}:
    `%`(VTESTOP_instr(shape, var_0))
    -- wf_shape: `%`(shape)
    -- wf_vtestop_: `%%`(shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_91{shape : fuck1shape, var_0 : fuck1vrelop_}:
    `%`(VRELOP_instr(shape, var_0))
    -- wf_shape: `%`(shape)
    -- wf_vrelop_: `%%`(shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_92{ishape : fuck1ishape, var_0 : fuck1vshiftop_}:
    `%`(VSHIFTOP_instr(ishape, var_0))
    -- wf_ishape: `%`(ishape)
    -- wf_vshiftop_: `%%`(ishape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_93{ishape : fuck1ishape}:
    `%`(VBITMASK_instr(ishape))
    -- wf_ishape: `%`(ishape)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_94{bshape : fuck1bshape, var_0 : fuck1vswizzlop_}:
    `%`(VSWIZZLOP_instr(bshape, var_0))
    -- wf_bshape: `%`(bshape)
    -- wf_vswizzlop_: `%%`(bshape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_95{bshape : fuck1bshape, `laneidx*` : fuck6fuck1laneidx*}:
    `%`(VSHUFFLE_instr(bshape, `laneidx*`))
    -- wf_bshape: `%`(bshape)
    -- (wf_uN: `%%`(8, laneidx))*{laneidx <- `laneidx*`}
    -- if (`%`_dim(|laneidx*{laneidx <- `laneidx*`}|) = $dim(bshape!`%`_bshape.0))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_96{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, var_0 : fuck1vextunop__}:
    `%`(VEXTUNOP_instr(ishape_1, ishape_2, var_0))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextunop__: `%%%`(ishape_2, ishape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_97{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, var_0 : fuck1vextbinop__}:
    `%`(VEXTBINOP_instr(ishape_1, ishape_2, var_0))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextbinop__: `%%%`(ishape_2, ishape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_98{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, var_0 : fuck1vextternop__}:
    `%`(VEXTTERNOP_instr(ishape_1, ishape_2, var_0))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextternop__: `%%%`(ishape_2, ishape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_99{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, sx : fuck1sx}:
    `%`(VNARROW_instr(ishape_1, ishape_2, sx))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- if (($lsize($lanetype(ishape_2!`%`_ishape.0)) = (2 * $lsize($lanetype(ishape_1!`%`_ishape.0)))) /\ ((2 * $lsize($lanetype(ishape_1!`%`_ishape.0))) <= 32))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_100{shape_1 : fuck1shape, shape_2 : fuck1shape, var_0 : fuck1vcvtop__}:
    `%`(VCVTOP_instr(shape_1, shape_2, var_0))
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_vcvtop__: `%%%`(shape_2, shape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_101{shape : fuck1shape}:
    `%`(VSPLAT_instr(shape))
    -- wf_shape: `%`(shape)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_102{shape : fuck1shape, `sx?` : fuck6fuck1sx?, laneidx : fuck1laneidx}:
    `%`(VEXTRACT_LANE_instr(shape, `sx?`, laneidx))
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(8, laneidx)
    -- if ((sx?{sx <- `sx?`} = ?()) <=> ($lanetype(shape) <- [I32_lanetype I64_lanetype F32_lanetype F64_lanetype]))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_103{shape : fuck1shape, laneidx : fuck1laneidx}:
    `%`(VREPLACE_LANE_instr(shape, laneidx))
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(8, laneidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_104{u31 : fuck1u31}:
    `%`(`REF.I31_NUM`_instr(u31))
    -- wf_uN: `%%`(31, u31)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_105:
    `%`(`REF.NULL_ADDR`_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_106{structaddr : fuck1structaddr}:
    `%`(`REF.STRUCT_ADDR`_instr(structaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_107{arrayaddr : fuck1arrayaddr}:
    `%`(`REF.ARRAY_ADDR`_instr(arrayaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_108{funcaddr : fuck1funcaddr}:
    `%`(`REF.FUNC_ADDR`_instr(funcaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_109{exnaddr : fuck1exnaddr}:
    `%`(`REF.EXN_ADDR`_instr(exnaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_110{hostaddr : fuck1hostaddr}:
    `%`(`REF.HOST_ADDR`_instr(hostaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_111{ref : fuck1ref}:
    `%`(`REF.EXTERN`_instr(ref))
    -- wf_ref: `%`(ref)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_112{n : fuck1n, `instr*` : fuck6fuck1instr*, `instr*_0*` : fuck6fuck1instr*}:
    `%`(`LABEL_%{%}%`_instr(n, `instr*`, `instr*_0*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- (wf_instr: `%`(`instr*_0`))*{`instr*_0` <- `instr*_0*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_113{n : fuck1n, frame : fuck1frame, `instr*` : fuck6fuck1instr*}:
    `%`(`FRAME_%{%}%`_instr(n, frame, `instr*`))
    -- wf_frame: `%`(frame)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_114{n : fuck1n, `catch*` : fuck6fuck1catch*, `instr*` : fuck6fuck1instr*}:
    `%`(`HANDLER_%{%}%`_instr(n, `catch*`, `instr*`))
    -- (wf_catch: `%`(catch))*{catch <- `catch*`}
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_115:
    `%`(TRAP_instr)
}

;; test.spectec:1314.1-1315.9
syntax expr = fuck6fuck1instr*

;; test.spectec:1326.1-1326.35
def $memarg0 : fuck1memarg
  ;; test.spectec:1327.1-1327.35
  def $memarg0 = {ALIGN `%`_u32(0), OFFSET `%`_u64(0)}

;; test.spectec:1326.6-1326.13
relation memarg0_is_wf: `%`fuck5(ret_val : fuck1memarg)
  ;; test.spectec:1326.6-1326.13
  rule memarg0_is_wf_0{ret_val : fuck1memarg}:
    `%`(ret_val)
    -- if (ret_val = $memarg0)
    -- wf_memarg: `%`(ret_val)

;; test.spectec:1329.1-1329.69
def $const(consttype : fuck1consttype, lit_ : fuck1lit_) : fuck1instr
  ;; test.spectec:1330.1-1330.43
  def $const{numtype : fuck1numtype, c : fuck1num_}((numtype : fuck1numtype <: fuck1consttype), mk_lit__0_lit_(numtype, c)) = CONST_instr(numtype, c)
  ;; test.spectec:1331.1-1331.44
  def $const{vectype : fuck1vectype, c : fuck1uN}((vectype : fuck1vectype <: fuck1consttype), mk_lit__1_lit_(vectype, c)) = VCONST_instr(vectype, c)

;; test.spectec:1329.6-1329.12
relation const_is_wf: `%%%`fuck5(consttype : fuck1consttype, lit_ : fuck1lit_, ret_val : fuck1instr)
  ;; test.spectec:1329.6-1329.12
  rule const_is_wf_0{consttype : fuck1consttype, lit_ : fuck1lit_, ret_val : fuck1instr}:
    `%%%`(consttype, lit_, ret_val)
    -- wf_lit_: `%%`((consttype : fuck1consttype <: fuck1storagetype), lit_)
    -- if (ret_val = $const(consttype, lit_))
    -- wf_instr: `%`(ret_val)

;; test.spectec:1336.1-1336.30
def $free_shape(shape : fuck1shape) : fuck1free
  ;; test.spectec:1345.1-1345.59
  def $free_shape{lanetype : fuck1lanetype, dim : fuck1dim}(`%X%`_shape(lanetype, dim)) = $free_lanetype(lanetype)

;; test.spectec:1336.6-1336.17
relation free_shape_is_wf: `%%`fuck5(shape : fuck1shape, ret_val : fuck1free)
  ;; test.spectec:1336.6-1336.17
  rule free_shape_is_wf_0{shape : fuck1shape, ret_val : fuck1free}:
    `%%`(shape, ret_val)
    -- wf_shape: `%`(shape)
    -- if (ret_val = $free_shape(shape))
    -- wf_free: `%`(ret_val)

;; test.spectec:1337.1-1337.38
def $free_blocktype(blocktype : fuck1blocktype) : fuck1free
  ;; test.spectec:1347.1-1347.75
  def $free_blocktype{`valtype?` : fuck6fuck1valtype?}(_RESULT_blocktype(valtype?{valtype <- `valtype?`})) = $free_opt($free_valtype(valtype)?{valtype <- `valtype?`})
  ;; test.spectec:1348.1-1348.59
  def $free_blocktype{typeidx : fuck1uN}(_IDX_blocktype(typeidx)) = $free_typeidx(typeidx)

;; test.spectec:1337.6-1337.21
relation free_blocktype_is_wf: `%%`fuck5(blocktype : fuck1blocktype, ret_val : fuck1free)
  ;; test.spectec:1337.6-1337.21
  rule free_blocktype_is_wf_0{blocktype : fuck1blocktype, ret_val : fuck1free}:
    `%%`(blocktype, ret_val)
    -- wf_blocktype: `%`(blocktype)
    -- if (ret_val = $free_blocktype(blocktype))
    -- wf_free: `%`(ret_val)

;; test.spectec:1338.1-1338.30
def $free_catch(catch : fuck1catch) : fuck1free
  ;; test.spectec:1350.1-1350.90
  def $free_catch{tagidx : fuck1uN, labelidx : fuck1uN}(CATCH_catch(tagidx, labelidx)) = $free_tagidx(tagidx) +++ $free_labelidx(labelidx)
  ;; test.spectec:1351.1-1351.94
  def $free_catch{tagidx : fuck1uN, labelidx : fuck1uN}(CATCH_REF_catch(tagidx, labelidx)) = $free_tagidx(tagidx) +++ $free_labelidx(labelidx)
  ;; test.spectec:1352.1-1352.63
  def $free_catch{labelidx : fuck1uN}(CATCH_ALL_catch(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1353.1-1353.67
  def $free_catch{labelidx : fuck1uN}(CATCH_ALL_REF_catch(labelidx)) = $free_labelidx(labelidx)

;; test.spectec:1338.6-1338.17
relation free_catch_is_wf: `%%`fuck5(catch : fuck1catch, ret_val : fuck1free)
  ;; test.spectec:1338.6-1338.17
  rule free_catch_is_wf_0{catch : fuck1catch, ret_val : fuck1free}:
    `%%`(catch, ret_val)
    -- wf_catch: `%`(catch)
    -- if (ret_val = $free_catch(catch))
    -- wf_free: `%`(ret_val)

;; test.spectec:1504.1-1504.44
rec {

;; test.spectec:1504.1-1504.44
def $shift_labelidxs(fuck6fuck1labelidx*) : fuck6fuck1labelidx*
  ;; test.spectec:1505.1-1505.32
  def $shift_labelidxs([]) = []
  ;; test.spectec:1506.1-1506.66
  def $shift_labelidxs{`labelidx'*` : fuck6fuck1labelidx*}([`%`_labelidx(0)] ++ labelidx'*{labelidx' <- `labelidx'*`}) = $shift_labelidxs(labelidx'*{labelidx' <- `labelidx'*`})
  ;; test.spectec:1507.1-1507.91
  def $shift_labelidxs{labelidx : fuck1uN, `labelidx'*` : fuck6fuck1labelidx*}([labelidx] ++ labelidx'*{labelidx' <- `labelidx'*`}) = [`%`_labelidx((((labelidx!`%`_uN.0 : nat <:> int) - (1 : nat <:> int)) : int <:> nat))] ++ $shift_labelidxs(labelidx'*{labelidx' <- `labelidx'*`})
}

;; test.spectec:1504.1-1504.44
rec {

;; test.spectec:1504.6-1504.22
relation shift_labelidxs_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1labelidx*, `ret_val*` : fuck6fuck1labelidx*)
  ;; test.spectec:1504.6-1504.22
  rule shift_labelidxs_is_wf_0{`var_0*` : fuck6fuck1labelidx*, `ret_val*` : fuck6fuck1labelidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $shift_labelidxs(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:1340.1-1341.31
rec {

;; test.spectec:1340.1-1340.30
def $free_instr(instr : fuck1instr) : fuck1free
  ;; test.spectec:1355.1-1355.26
  def $free_instr(NOP_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1356.1-1356.34
  def $free_instr(UNREACHABLE_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1357.1-1357.27
  def $free_instr(DROP_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1358.1-1358.86
  def $free_instr{`valtype*?` : fuck6fuck6fuck1valtype*?}(SELECT_instr(valtype*{valtype <- `valtype*`}?{`valtype*` <- `valtype*?`})) = $free_opt($free_list($free_valtype(valtype)*{valtype <- `valtype*`})?{`valtype*` <- `valtype*?`})
  ;; test.spectec:1360.1-1360.92
  def $free_instr{blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*}(BLOCK_instr(blocktype, instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_block(instr*{instr <- `instr*`})
  ;; test.spectec:1361.1-1361.91
  def $free_instr{blocktype : fuck1blocktype, `instr*` : fuck6fuck1instr*}(LOOP_instr(blocktype, instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_block(instr*{instr <- `instr*`})
  ;; test.spectec:1362.1-1363.79
  def $free_instr{blocktype : fuck1blocktype, `instr_1*` : fuck6fuck1instr*, `instr_2*` : fuck6fuck1instr*}(`IF%%ELSE%`_instr(blocktype, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})) = $free_blocktype(blocktype) +++ $free_block(instr_1*{instr_1 <- `instr_1*`}) +++ $free_block(instr_2*{instr_2 <- `instr_2*`})
  ;; test.spectec:1365.1-1365.56
  def $free_instr{labelidx : fuck1uN}(BR_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1366.1-1366.59
  def $free_instr{labelidx : fuck1uN}(BR_IF_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1367.1-1368.69
  def $free_instr{`labelidx*` : fuck6fuck1labelidx*, labelidx' : fuck1uN}(BR_TABLE_instr(labelidx*{labelidx <- `labelidx*`}, labelidx')) = $free_list($free_labelidx(labelidx)*{labelidx <- `labelidx*`}) +++ $free_labelidx(labelidx')
  ;; test.spectec:1369.1-1369.64
  def $free_instr{labelidx : fuck1uN}(BR_ON_NULL_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1370.1-1370.68
  def $free_instr{labelidx : fuck1uN}(BR_ON_NON_NULL_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1371.1-1372.83
  def $free_instr{labelidx : fuck1uN, reftype_1 : fuck1reftype, reftype_2 : fuck1reftype}(BR_ON_CAST_instr(labelidx, reftype_1, reftype_2)) = $free_labelidx(labelidx) +++ $free_reftype(reftype_1) +++ $free_reftype(reftype_2)
  ;; test.spectec:1373.1-1374.83
  def $free_instr{labelidx : fuck1uN, reftype_1 : fuck1reftype, reftype_2 : fuck1reftype}(BR_ON_CAST_FAIL_instr(labelidx, reftype_1, reftype_2)) = $free_labelidx(labelidx) +++ $free_reftype(reftype_1) +++ $free_reftype(reftype_2)
  ;; test.spectec:1376.1-1376.55
  def $free_instr{funcidx : fuck1uN}(CALL_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1377.1-1377.59
  def $free_instr{typeuse : fuck1typeuse}(CALL_REF_instr(typeuse)) = $free_typeuse(typeuse)
  ;; test.spectec:1378.1-1379.53
  def $free_instr{tableidx : fuck1uN, typeuse : fuck1typeuse}(CALL_INDIRECT_instr(tableidx, typeuse)) = $free_tableidx(tableidx) +++ $free_typeuse(typeuse)
  ;; test.spectec:1380.1-1380.29
  def $free_instr(RETURN_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1381.1-1381.62
  def $free_instr{funcidx : fuck1uN}(RETURN_CALL_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1382.1-1382.66
  def $free_instr{typeuse : fuck1typeuse}(RETURN_CALL_REF_instr(typeuse)) = $free_typeuse(typeuse)
  ;; test.spectec:1383.1-1384.53
  def $free_instr{tableidx : fuck1uN, typeuse : fuck1typeuse}(RETURN_CALL_INDIRECT_instr(tableidx, typeuse)) = $free_tableidx(tableidx) +++ $free_typeuse(typeuse)
  ;; test.spectec:1386.1-1386.53
  def $free_instr{tagidx : fuck1uN}(THROW_instr(tagidx)) = $free_tagidx(tagidx)
  ;; test.spectec:1387.1-1387.32
  def $free_instr(THROW_REF_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1388.1-1389.99
  def $free_instr{blocktype : fuck1blocktype, `catch*` : fuck6fuck1catch*, `instr*` : fuck6fuck1instr*}(TRY_TABLE_instr(blocktype, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_list($free_catch(catch)*{catch <- `catch*`}) +++ $free_list($free_instr(instr)*{instr <- `instr*`})
  ;; test.spectec:1391.1-1391.63
  def $free_instr{numtype : fuck1numtype, numlit : fuck1num_}(CONST_instr(numtype, numlit)) = $free_numtype(numtype)
  ;; test.spectec:1392.1-1392.60
  def $free_instr{numtype : fuck1numtype, unop : fuck1unop_}(UNOP_instr(numtype, unop)) = $free_numtype(numtype)
  ;; test.spectec:1393.1-1393.62
  def $free_instr{numtype : fuck1numtype, binop : fuck1binop_}(BINOP_instr(numtype, binop)) = $free_numtype(numtype)
  ;; test.spectec:1394.1-1394.64
  def $free_instr{numtype : fuck1numtype, testop : fuck1testop_}(TESTOP_instr(numtype, testop)) = $free_numtype(numtype)
  ;; test.spectec:1395.1-1395.62
  def $free_instr{numtype : fuck1numtype, relop : fuck1relop_}(RELOP_instr(numtype, relop)) = $free_numtype(numtype)
  ;; test.spectec:1396.1-1397.55
  def $free_instr{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, cvtop : fuck1cvtop__}(CVTOP_instr(numtype_1, numtype_2, cvtop)) = $free_numtype(numtype_1) +++ $free_numtype(numtype_2)
  ;; test.spectec:1399.1-1399.64
  def $free_instr{vectype : fuck1vectype, veclit : fuck1uN}(VCONST_instr(vectype, veclit)) = $free_vectype(vectype)
  ;; test.spectec:1400.1-1400.64
  def $free_instr{vectype : fuck1vectype, vvunop : fuck1vvunop}(VVUNOP_instr(vectype, vvunop)) = $free_vectype(vectype)
  ;; test.spectec:1401.1-1401.66
  def $free_instr{vectype : fuck1vectype, vvbinop : fuck1vvbinop}(VVBINOP_instr(vectype, vvbinop)) = $free_vectype(vectype)
  ;; test.spectec:1402.1-1402.68
  def $free_instr{vectype : fuck1vectype, vvternop : fuck1vvternop}(VVTERNOP_instr(vectype, vvternop)) = $free_vectype(vectype)
  ;; test.spectec:1403.1-1403.68
  def $free_instr{vectype : fuck1vectype, vvtestop : fuck1vvtestop}(VVTESTOP_instr(vectype, vvtestop)) = $free_vectype(vectype)
  ;; test.spectec:1404.1-1404.56
  def $free_instr{shape : fuck1shape, vunop : fuck1vunop_}(VUNOP_instr(shape, vunop)) = $free_shape(shape)
  ;; test.spectec:1405.1-1405.58
  def $free_instr{shape : fuck1shape, vbinop : fuck1vbinop_}(VBINOP_instr(shape, vbinop)) = $free_shape(shape)
  ;; test.spectec:1406.1-1406.60
  def $free_instr{shape : fuck1shape, vternop : fuck1vternop_}(VTERNOP_instr(shape, vternop)) = $free_shape(shape)
  ;; test.spectec:1407.1-1407.60
  def $free_instr{shape : fuck1shape, vtestop : fuck1vtestop_}(VTESTOP_instr(shape, vtestop)) = $free_shape(shape)
  ;; test.spectec:1408.1-1408.58
  def $free_instr{shape : fuck1shape, vrelop : fuck1vrelop_}(VRELOP_instr(shape, vrelop)) = $free_shape(shape)
  ;; test.spectec:1409.1-1409.64
  def $free_instr{ishape : fuck1ishape, vshiftop : fuck1vshiftop_}(VSHIFTOP_instr(ishape, vshiftop)) = $free_shape(ishape!`%`_ishape.0)
  ;; test.spectec:1410.1-1410.55
  def $free_instr{ishape : fuck1ishape}(VBITMASK_instr(ishape)) = $free_shape(ishape!`%`_ishape.0)
  ;; test.spectec:1411.1-1411.66
  def $free_instr{bshape : fuck1bshape, vswizzlop : fuck1vswizzlop_}(VSWIZZLOP_instr(bshape, vswizzlop)) = $free_shape(bshape!`%`_bshape.0)
  ;; test.spectec:1412.1-1412.64
  def $free_instr{bshape : fuck1bshape, `laneidx*` : fuck6fuck1laneidx*}(VSHUFFLE_instr(bshape, laneidx*{laneidx <- `laneidx*`})) = $free_shape(bshape!`%`_bshape.0)
  ;; test.spectec:1413.1-1414.49
  def $free_instr{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextunop : fuck1vextunop__}(VEXTUNOP_instr(ishape_1, ishape_2, vextunop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1415.1-1416.49
  def $free_instr{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextbinop : fuck1vextbinop__}(VEXTBINOP_instr(ishape_1, ishape_2, vextbinop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1417.1-1418.49
  def $free_instr{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextternop : fuck1vextternop__}(VEXTTERNOP_instr(ishape_1, ishape_2, vextternop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1419.1-1420.49
  def $free_instr{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, sx : fuck1sx}(VNARROW_instr(ishape_1, ishape_2, sx)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1421.1-1422.47
  def $free_instr{shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop : fuck1vcvtop__}(VCVTOP_instr(shape_1, shape_2, vcvtop)) = $free_shape(shape_1) +++ $free_shape(shape_2)
  ;; test.spectec:1423.1-1423.51
  def $free_instr{shape : fuck1shape}(VSPLAT_instr(shape)) = $free_shape(shape)
  ;; test.spectec:1424.1-1424.70
  def $free_instr{shape : fuck1shape, `sx?` : fuck6fuck1sx?, laneidx : fuck1uN}(VEXTRACT_LANE_instr(shape, sx?{sx <- `sx?`}, laneidx)) = $free_shape(shape)
  ;; test.spectec:1425.1-1425.66
  def $free_instr{shape : fuck1shape, laneidx : fuck1uN}(VREPLACE_LANE_instr(shape, laneidx)) = $free_shape(shape)
  ;; test.spectec:1427.1-1427.62
  def $free_instr{heaptype : fuck1heaptype}(`REF.NULL`_instr(heaptype)) = $free_heaptype(heaptype)
  ;; test.spectec:1428.1-1428.34
  def $free_instr(`REF.IS_NULL`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1429.1-1429.38
  def $free_instr(`REF.AS_NON_NULL`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1430.1-1430.29
  def $free_instr(`REF.EQ`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1431.1-1431.59
  def $free_instr{reftype : fuck1reftype}(`REF.TEST`_instr(reftype)) = $free_reftype(reftype)
  ;; test.spectec:1432.1-1432.59
  def $free_instr{reftype : fuck1reftype}(`REF.CAST`_instr(reftype)) = $free_reftype(reftype)
  ;; test.spectec:1433.1-1433.59
  def $free_instr{funcidx : fuck1uN}(`REF.FUNC`_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1434.1-1434.30
  def $free_instr(`REF.I31`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1436.1-1436.33
  def $free_instr{sx : fuck1sx}(`I31.GET`_instr(sx)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1438.1-1438.61
  def $free_instr{typeidx : fuck1uN}(`STRUCT.NEW`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1439.1-1439.69
  def $free_instr{typeidx : fuck1uN}(`STRUCT.NEW_DEFAULT`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1440.1-1440.69
  def $free_instr{`sx?` : fuck6fuck1sx?, typeidx : fuck1uN, u32 : fuck1uN}(`STRUCT.GET`_instr(sx?{sx <- `sx?`}, typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1441.1-1441.65
  def $free_instr{typeidx : fuck1uN, u32 : fuck1uN}(`STRUCT.SET`_instr(typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1443.1-1443.60
  def $free_instr{typeidx : fuck1uN}(`ARRAY.NEW`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1444.1-1444.68
  def $free_instr{typeidx : fuck1uN}(`ARRAY.NEW_DEFAULT`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1445.1-1445.70
  def $free_instr{typeidx : fuck1uN, u32 : fuck1uN}(`ARRAY.NEW_FIXED`_instr(typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1446.1-1447.51
  def $free_instr{typeidx : fuck1uN, dataidx : fuck1uN}(`ARRAY.NEW_DATA`_instr(typeidx, dataidx)) = $free_typeidx(typeidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1448.1-1449.51
  def $free_instr{typeidx : fuck1uN, elemidx : fuck1uN}(`ARRAY.NEW_ELEM`_instr(typeidx, elemidx)) = $free_typeidx(typeidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1450.1-1450.64
  def $free_instr{`sx?` : fuck6fuck1sx?, typeidx : fuck1uN}(`ARRAY.GET`_instr(sx?{sx <- `sx?`}, typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1451.1-1451.60
  def $free_instr{typeidx : fuck1uN}(`ARRAY.SET`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1452.1-1452.32
  def $free_instr(`ARRAY.LEN`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1453.1-1453.61
  def $free_instr{typeidx : fuck1uN}(`ARRAY.FILL`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1454.1-1455.55
  def $free_instr{typeidx_1 : fuck1uN, typeidx_2 : fuck1uN}(`ARRAY.COPY`_instr(typeidx_1, typeidx_2)) = $free_typeidx(typeidx_1) +++ $free_typeidx(typeidx_2)
  ;; test.spectec:1456.1-1457.51
  def $free_instr{typeidx : fuck1uN, dataidx : fuck1uN}(`ARRAY.INIT_DATA`_instr(typeidx, dataidx)) = $free_typeidx(typeidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1458.1-1459.51
  def $free_instr{typeidx : fuck1uN, elemidx : fuck1uN}(`ARRAY.INIT_ELEM`_instr(typeidx, elemidx)) = $free_typeidx(typeidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1461.1-1461.41
  def $free_instr(`EXTERN.CONVERT_ANY`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1462.1-1462.41
  def $free_instr(`ANY.CONVERT_EXTERN`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1464.1-1464.63
  def $free_instr{localidx : fuck1uN}(`LOCAL.GET`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1465.1-1465.63
  def $free_instr{localidx : fuck1uN}(`LOCAL.SET`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1466.1-1466.63
  def $free_instr{localidx : fuck1uN}(`LOCAL.TEE`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1468.1-1468.67
  def $free_instr{globalidx : fuck1uN}(`GLOBAL.GET`_instr(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:1469.1-1469.67
  def $free_instr{globalidx : fuck1uN}(`GLOBAL.SET`_instr(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:1471.1-1471.63
  def $free_instr{tableidx : fuck1uN}(`TABLE.GET`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1472.1-1472.63
  def $free_instr{tableidx : fuck1uN}(`TABLE.SET`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1473.1-1473.64
  def $free_instr{tableidx : fuck1uN}(`TABLE.SIZE`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1474.1-1474.64
  def $free_instr{tableidx : fuck1uN}(`TABLE.GROW`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1475.1-1475.64
  def $free_instr{tableidx : fuck1uN}(`TABLE.FILL`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1476.1-1477.59
  def $free_instr{tableidx_1 : fuck1uN, tableidx_2 : fuck1uN}(`TABLE.COPY`_instr(tableidx_1, tableidx_2)) = $free_tableidx(tableidx_1) +++ $free_tableidx(tableidx_2)
  ;; test.spectec:1478.1-1479.53
  def $free_instr{tableidx : fuck1uN, elemidx : fuck1uN}(`TABLE.INIT`_instr(tableidx, elemidx)) = $free_tableidx(tableidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1480.1-1480.60
  def $free_instr{elemidx : fuck1uN}(`ELEM.DROP`_instr(elemidx)) = $free_elemidx(elemidx)
  ;; test.spectec:1482.1-1483.49
  def $free_instr{numtype : fuck1numtype, `loadop?` : fuck6fuck1loadop_?, memidx : fuck1uN, memarg : fuck1memarg}(LOAD_instr(numtype, loadop?{loadop <- `loadop?`}, memidx, memarg)) = $free_numtype(numtype) +++ $free_memidx(memidx)
  ;; test.spectec:1484.1-1485.49
  def $free_instr{numtype : fuck1numtype, `storeop?` : fuck6fuck1storeop_?, memidx : fuck1uN, memarg : fuck1memarg}(STORE_instr(numtype, storeop?{storeop <- `storeop?`}, memidx, memarg)) = $free_numtype(numtype) +++ $free_memidx(memidx)
  ;; test.spectec:1486.1-1487.49
  def $free_instr{vectype : fuck1vectype, `vloadop?` : fuck6fuck1vloadop_?, memidx : fuck1uN, memarg : fuck1memarg}(VLOAD_instr(vectype, vloadop?{vloadop <- `vloadop?`}, memidx, memarg)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1488.1-1489.49
  def $free_instr{vectype : fuck1vectype, sz : fuck1sz, memidx : fuck1uN, memarg : fuck1memarg, laneidx : fuck1uN}(VLOAD_LANE_instr(vectype, sz, memidx, memarg, laneidx)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1490.1-1491.49
  def $free_instr{vectype : fuck1vectype, memidx : fuck1uN, memarg : fuck1memarg}(VSTORE_instr(vectype, memidx, memarg)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1492.1-1493.49
  def $free_instr{vectype : fuck1vectype, sz : fuck1sz, memidx : fuck1uN, memarg : fuck1memarg, laneidx : fuck1uN}(VSTORE_LANE_instr(vectype, sz, memidx, memarg, laneidx)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1494.1-1494.59
  def $free_instr{memidx : fuck1uN}(`MEMORY.SIZE`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1495.1-1495.59
  def $free_instr{memidx : fuck1uN}(`MEMORY.GROW`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1496.1-1496.59
  def $free_instr{memidx : fuck1uN}(`MEMORY.FILL`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1497.1-1498.51
  def $free_instr{memidx_1 : fuck1uN, memidx_2 : fuck1uN}(`MEMORY.COPY`_instr(memidx_1, memidx_2)) = $free_memidx(memidx_1) +++ $free_memidx(memidx_2)
  ;; test.spectec:1499.1-1500.49
  def $free_instr{memidx : fuck1uN, dataidx : fuck1uN}(`MEMORY.INIT`_instr(memidx, dataidx)) = $free_memidx(memidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1501.1-1501.60
  def $free_instr{dataidx : fuck1uN}(`DATA.DROP`_instr(dataidx)) = $free_dataidx(dataidx)

;; test.spectec:1341.1-1341.31
def $free_block(fuck6fuck1instr*) : fuck1free
  ;; test.spectec:1509.1-1510.47
  def $free_block{`instr*` : fuck6fuck1instr*}(instr*{instr <- `instr*`}) = free[LABELS_free = $shift_labelidxs(free.LABELS_free)]
    -- let{free : fuck1free} free = $free_list($free_instr(instr)*{instr <- `instr*`})
}

;; test.spectec:1340.1-1341.31
rec {

;; test.spectec:1340.6-1340.17
relation free_instr_is_wf: `%%`fuck5(instr : fuck1instr, ret_val : fuck1free)
  ;; test.spectec:1340.6-1340.17
  rule free_instr_is_wf_0{instr : fuck1instr, ret_val : fuck1free}:
    `%%`(instr, ret_val)
    -- wf_instr: `%`(instr)
    -- if (ret_val = $free_instr(instr))
    -- wf_free: `%`(ret_val)

;; test.spectec:1341.6-1341.17
relation free_block_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1instr*, ret_val : fuck1free)
  ;; test.spectec:1341.6-1341.17
  rule free_block_is_wf_0{`var_0*` : fuck6fuck1instr*, ret_val : fuck1free}:
    `%%`(`var_0*`, ret_val)
    -- (wf_instr: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $free_block(`var_0*`))
    -- wf_free: `%`(ret_val)
}

;; test.spectec:1342.1-1342.28
def $free_expr(expr : fuck1expr) : fuck1free
  ;; test.spectec:1513.1-1513.57
  def $free_expr{`instr*` : fuck6fuck1instr*}(instr*{instr <- `instr*`}) = $free_list($free_instr(instr)*{instr <- `instr*`})

;; test.spectec:1342.6-1342.16
relation free_expr_is_wf: `%%`fuck5(expr : fuck1expr, ret_val : fuck1free)
  ;; test.spectec:1342.6-1342.16
  rule free_expr_is_wf_0{expr : fuck1expr, ret_val : fuck1free}:
    `%%`(expr, ret_val)
    -- (wf_instr: `%`(expr))*{expr <- expr}
    -- if (ret_val = $free_expr(expr))
    -- wf_free: `%`(ret_val)

;; test.spectec:1526.1-1527.43
syntax elemmode = 
  | ACTIVEfuck5(tableidx : fuck1tableidx, expr : fuck1expr)
  | PASSIVE
  | DECLARE

;; test.spectec:1526.8-1526.16
relation wf_elemmode: `%`fuck5(fuck1elemmode)
  ;; test.spectec:1526.8-1526.16
  rule elemmode_case_0{tableidx : fuck1tableidx, expr : fuck1expr}:
    `%`(ACTIVE_elemmode(tableidx, expr))
    -- wf_uN: `%%`(32, tableidx)
    -- (wf_instr: `%`(expr))*{expr <- expr}

  ;; test.spectec:1526.8-1526.16
  rule elemmode_case_1:
    `%`(PASSIVE_elemmode)

  ;; test.spectec:1526.8-1526.16
  rule elemmode_case_2:
    `%`(DECLARE_elemmode)

;; test.spectec:1528.1-1529.31
syntax datamode = 
  | ACTIVEfuck5(memidx : fuck1memidx, expr : fuck1expr)
  | PASSIVE

;; test.spectec:1528.8-1528.16
relation wf_datamode: `%`fuck5(fuck1datamode)
  ;; test.spectec:1528.8-1528.16
  rule datamode_case_0{memidx : fuck1memidx, expr : fuck1expr}:
    `%`(ACTIVE_datamode(memidx, expr))
    -- wf_uN: `%%`(32, memidx)
    -- (wf_instr: `%`(expr))*{expr <- expr}

  ;; test.spectec:1528.8-1528.16
  rule datamode_case_1:
    `%`(PASSIVE_datamode)

;; test.spectec:1531.1-1532.15
syntax type = 
  | TYPEfuck5(rectype : fuck1rectype)

;; test.spectec:1534.1-1535.14
syntax tag = 
  | TAGfuck5(tagtype : fuck1tagtype)

;; test.spectec:1534.8-1534.11
relation wf_tag: `%`fuck5(fuck1tag)
  ;; test.spectec:1534.8-1534.11
  rule tag_case_0{tagtype : fuck1tagtype}:
    `%`(TAG_tag(tagtype))
    -- wf_typeuse: `%`(tagtype)

;; test.spectec:1537.1-1538.25
syntax global = 
  | GLOBALfuck5(globaltype : fuck1globaltype, expr : fuck1expr)

;; test.spectec:1537.8-1537.14
relation wf_global: `%`fuck5(fuck1global)
  ;; test.spectec:1537.8-1537.14
  rule global_case_0{globaltype : fuck1globaltype, expr : fuck1expr}:
    `%`(GLOBAL_global(globaltype, expr))
    -- wf_globaltype: `%`(globaltype)
    -- (wf_instr: `%`(expr))*{expr <- expr}

;; test.spectec:1540.1-1541.17
syntax mem = 
  | MEMORYfuck5(memtype : fuck1memtype)

;; test.spectec:1540.8-1540.11
relation wf_mem: `%`fuck5(fuck1mem)
  ;; test.spectec:1540.8-1540.11
  rule mem_case_0{memtype : fuck1memtype}:
    `%`(MEMORY_mem(memtype))
    -- wf_memtype: `%`(memtype)

;; test.spectec:1543.1-1544.23
syntax table = 
  | TABLEfuck5(tabletype : fuck1tabletype, expr : fuck1expr)

;; test.spectec:1543.8-1543.13
relation wf_table: `%`fuck5(fuck1table)
  ;; test.spectec:1543.8-1543.13
  rule table_case_0{tabletype : fuck1tabletype, expr : fuck1expr}:
    `%`(TABLE_table(tabletype, expr))
    -- wf_tabletype: `%`(tabletype)
    -- (wf_instr: `%`(expr))*{expr <- expr}

;; test.spectec:1546.1-1547.22
syntax data = 
  | DATAfuck5(`byte*` : fuck6fuck1byte*, datamode : fuck1datamode)

;; test.spectec:1546.8-1546.12
relation wf_data: `%`fuck5(fuck1data)
  ;; test.spectec:1546.8-1546.12
  rule data_case_0{`byte*` : fuck6fuck1byte*, datamode : fuck1datamode}:
    `%`(DATA_data(`byte*`, datamode))
    -- (wf_byte: `%`(byte))*{byte <- `byte*`}
    -- wf_datamode: `%`(datamode)

;; test.spectec:1549.1-1550.16
syntax local = 
  | LOCALfuck5(valtype : fuck1valtype)

;; test.spectec:1549.8-1549.13
relation wf_local: `%`fuck5(fuck1local)
  ;; test.spectec:1549.8-1549.13
  rule local_case_0{valtype : fuck1valtype}:
    `%`(LOCAL_local(valtype))
    -- wf_valtype: `%`(valtype)

;; test.spectec:1552.1-1553.27
syntax func = 
  | FUNCfuck5(typeidx : fuck1typeidx, `local*` : fuck6fuck1local*, expr : fuck1expr)

;; test.spectec:1552.8-1552.12
relation wf_func: `%`fuck5(fuck1func)
  ;; test.spectec:1552.8-1552.12
  rule func_case_0{typeidx : fuck1typeidx, `local*` : fuck6fuck1local*, expr : fuck1expr}:
    `%`(FUNC_func(typeidx, `local*`, expr))
    -- wf_uN: `%%`(32, typeidx)
    -- (wf_local: `%`(local))*{local <- `local*`}
    -- (wf_instr: `%`(expr))*{expr <- expr}

;; test.spectec:1555.1-1556.30
syntax elem = 
  | ELEMfuck5(reftype : fuck1reftype, `expr*` : fuck6fuck1expr*, elemmode : fuck1elemmode)

;; test.spectec:1555.8-1555.12
relation wf_elem: `%`fuck5(fuck1elem)
  ;; test.spectec:1555.8-1555.12
  rule elem_case_0{reftype : fuck1reftype, `expr*` : fuck6fuck1expr*, elemmode : fuck1elemmode}:
    `%`(ELEM_elem(reftype, `expr*`, elemmode))
    -- wf_reftype: `%`(reftype)
    -- (wf_instr: `%`(expr))*{expr <- expr}*{expr <- `expr*`}
    -- wf_elemmode: `%`(elemmode)

;; test.spectec:1558.1-1559.16
syntax start = 
  | STARTfuck5(funcidx : fuck1funcidx)

;; test.spectec:1558.8-1558.13
relation wf_start: `%`fuck5(fuck1start)
  ;; test.spectec:1558.8-1558.13
  rule start_case_0{funcidx : fuck1funcidx}:
    `%`(START_start(funcidx))
    -- wf_uN: `%%`(32, funcidx)

;; test.spectec:1561.1-1562.30
syntax import = 
  | IMPORTfuck5(name : fuck1name, name : fuck1name, externtype : fuck1externtype)

;; test.spectec:1561.8-1561.14
relation wf_import: `%`fuck5(fuck1import)
  ;; test.spectec:1561.8-1561.14
  rule import_case_0{name : fuck1name, name_0 : fuck1name, externtype : fuck1externtype}:
    `%`(IMPORT_import(name, name_0, externtype))
    -- wf_name: `%`(name)
    -- wf_name: `%`(name_0)
    -- wf_externtype: `%`(externtype)

;; test.spectec:1564.1-1565.24
syntax export = 
  | EXPORTfuck5(name : fuck1name, externidx : fuck1externidx)

;; test.spectec:1564.8-1564.14
relation wf_export: `%`fuck5(fuck1export)
  ;; test.spectec:1564.8-1564.14
  rule export_case_0{name : fuck1name, externidx : fuck1externidx}:
    `%`(EXPORT_export(name, externidx))
    -- wf_name: `%`(name)
    -- wf_externidx: `%`(externidx)

;; test.spectec:1567.1-1579.17
syntax module = 
  | MODULEfuck5(fuck1list(syntax fuck1type), fuck1list(syntax fuck1import), fuck1list(syntax fuck1tag), fuck1list(syntax fuck1global), fuck1list(syntax fuck1mem), fuck1list(syntax fuck1table), fuck1list(syntax fuck1func), fuck1list(syntax fuck1data), fuck1list(syntax fuck1elem), `start?` : fuck6fuck1start?, fuck1list(syntax fuck1export))

;; test.spectec:1567.8-1567.14
relation wf_module: `%`fuck5(fuck1module)
  ;; test.spectec:1567.8-1567.14
  rule module_case_0{var_0 : fuck1list(syntax fuck1type), var_1 : fuck1list(syntax fuck1import), var_2 : fuck1list(syntax fuck1tag), var_3 : fuck1list(syntax fuck1global), var_4 : fuck1list(syntax fuck1mem), var_5 : fuck1list(syntax fuck1table), var_6 : fuck1list(syntax fuck1func), var_7 : fuck1list(syntax fuck1data), var_8 : fuck1list(syntax fuck1elem), `start?` : fuck6fuck1start?, var_9 : fuck1list(syntax fuck1export)}:
    `%`(MODULE_module(var_0, var_1, var_2, var_3, var_4, var_5, var_6, var_7, var_8, `start?`, var_9))
    -- (wf_start: `%`(start))?{start <- `start?`}

;; test.spectec:1594.1-1594.28
def $free_type(type : fuck1type) : fuck1free
  ;; test.spectec:1611.1-1611.54
  def $free_type{rectype : fuck1rectype}(TYPE_type(rectype)) = $free_rectype(rectype)

;; test.spectec:1594.6-1594.16
relation free_type_is_wf: `%%`fuck5(type : fuck1type, ret_val : fuck1free)
  ;; test.spectec:1594.6-1594.16
  rule free_type_is_wf_0{type : fuck1type, ret_val : fuck1free}:
    `%%`(type, ret_val)
    -- if (ret_val = $free_type(type))
    -- wf_free: `%`(ret_val)

;; test.spectec:1595.1-1595.26
def $free_tag(tag : fuck1tag) : fuck1free
  ;; test.spectec:1613.1-1613.52
  def $free_tag{tagtype : fuck1typeuse}(TAG_tag(tagtype)) = $free_tagtype(tagtype)

;; test.spectec:1595.6-1595.15
relation free_tag_is_wf: `%%`fuck5(tag : fuck1tag, ret_val : fuck1free)
  ;; test.spectec:1595.6-1595.15
  rule free_tag_is_wf_0{tag : fuck1tag, ret_val : fuck1free}:
    `%%`(tag, ret_val)
    -- wf_tag: `%`(tag)
    -- if (ret_val = $free_tag(tag))
    -- wf_free: `%`(ret_val)

;; test.spectec:1596.1-1596.32
def $free_global(global : fuck1global) : fuck1free
  ;; test.spectec:1615.1-1616.51
  def $free_global{globaltype : fuck1globaltype, expr : fuck6fuck1instr*}(GLOBAL_global(globaltype, expr)) = $free_globaltype(globaltype) +++ $free_expr(expr)

;; test.spectec:1596.6-1596.18
relation free_global_is_wf: `%%`fuck5(global : fuck1global, ret_val : fuck1free)
  ;; test.spectec:1596.6-1596.18
  rule free_global_is_wf_0{global : fuck1global, ret_val : fuck1free}:
    `%%`(global, ret_val)
    -- wf_global: `%`(global)
    -- if (ret_val = $free_global(global))
    -- wf_free: `%`(ret_val)

;; test.spectec:1597.1-1597.26
def $free_mem(mem : fuck1mem) : fuck1free
  ;; test.spectec:1618.1-1618.55
  def $free_mem{memtype : fuck1memtype}(MEMORY_mem(memtype)) = $free_memtype(memtype)

;; test.spectec:1597.6-1597.15
relation free_mem_is_wf: `%%`fuck5(mem : fuck1mem, ret_val : fuck1free)
  ;; test.spectec:1597.6-1597.15
  rule free_mem_is_wf_0{mem : fuck1mem, ret_val : fuck1free}:
    `%%`(mem, ret_val)
    -- wf_mem: `%`(mem)
    -- if (ret_val = $free_mem(mem))
    -- wf_free: `%`(ret_val)

;; test.spectec:1598.1-1598.30
def $free_table(table : fuck1table) : fuck1free
  ;; test.spectec:1620.1-1621.49
  def $free_table{tabletype : fuck1tabletype, expr : fuck6fuck1instr*}(TABLE_table(tabletype, expr)) = $free_tabletype(tabletype) +++ $free_expr(expr)

;; test.spectec:1598.6-1598.17
relation free_table_is_wf: `%%`fuck5(table : fuck1table, ret_val : fuck1free)
  ;; test.spectec:1598.6-1598.17
  rule free_table_is_wf_0{table : fuck1table, ret_val : fuck1free}:
    `%%`(table, ret_val)
    -- wf_table: `%`(table)
    -- if (ret_val = $free_table(table))
    -- wf_free: `%`(ret_val)

;; test.spectec:1599.1-1599.30
def $free_local(local : fuck1local) : fuck1free
  ;; test.spectec:1623.1-1623.44
  def $free_local{t : fuck1valtype}(LOCAL_local(t)) = $free_valtype(t)

;; test.spectec:1599.6-1599.17
relation free_local_is_wf: `%%`fuck5(local : fuck1local, ret_val : fuck1free)
  ;; test.spectec:1599.6-1599.17
  rule free_local_is_wf_0{local : fuck1local, ret_val : fuck1free}:
    `%%`(local, ret_val)
    -- wf_local: `%`(local)
    -- if (ret_val = $free_local(local))
    -- wf_free: `%`(ret_val)

;; test.spectec:1600.1-1600.28
def $free_func(func : fuck1func) : fuck1free
  ;; test.spectec:1625.1-1627.35
  def $free_func{typeidx : fuck1uN, `local*` : fuck6fuck1local*, expr : fuck6fuck1instr*}(FUNC_func(typeidx, local*{local <- `local*`}, expr)) = $free_typeidx(typeidx) +++ $free_list($free_local(local)*{local <- `local*`}) +++ $free_block(expr)[LOCALS_free = []]

;; test.spectec:1600.6-1600.16
relation free_func_is_wf: `%%`fuck5(func : fuck1func, ret_val : fuck1free)
  ;; test.spectec:1600.6-1600.16
  rule free_func_is_wf_0{func : fuck1func, ret_val : fuck1free}:
    `%%`(func, ret_val)
    -- wf_func: `%`(func)
    -- if (ret_val = $free_func(func))
    -- wf_free: `%`(ret_val)

;; test.spectec:1603.1-1603.36
def $free_datamode(datamode : fuck1datamode) : fuck1free
  ;; test.spectec:1639.1-1639.82
  def $free_datamode{memidx : fuck1uN, expr : fuck6fuck1instr*}(ACTIVE_datamode(memidx, expr)) = $free_memidx(memidx) +++ $free_expr(expr)
  ;; test.spectec:1640.1-1640.33
  def $free_datamode(PASSIVE_datamode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:1603.6-1603.20
relation free_datamode_is_wf: `%%`fuck5(datamode : fuck1datamode, ret_val : fuck1free)
  ;; test.spectec:1603.6-1603.20
  rule free_datamode_is_wf_0{datamode : fuck1datamode, ret_val : fuck1free}:
    `%%`(datamode, ret_val)
    -- wf_datamode: `%`(datamode)
    -- if (ret_val = $free_datamode(datamode))
    -- wf_free: `%`(ret_val)

;; test.spectec:1601.1-1601.28
def $free_data(data : fuck1data) : fuck1free
  ;; test.spectec:1629.1-1629.63
  def $free_data{`byte*` : fuck6fuck1byte*, datamode : fuck1datamode}(DATA_data(byte*{byte <- `byte*`}, datamode)) = $free_datamode(datamode)

;; test.spectec:1601.6-1601.16
relation free_data_is_wf: `%%`fuck5(data : fuck1data, ret_val : fuck1free)
  ;; test.spectec:1601.6-1601.16
  rule free_data_is_wf_0{data : fuck1data, ret_val : fuck1free}:
    `%%`(data, ret_val)
    -- wf_data: `%`(data)
    -- if (ret_val = $free_data(data))
    -- wf_free: `%`(ret_val)

;; test.spectec:1604.1-1604.36
def $free_elemmode(elemmode : fuck1elemmode) : fuck1free
  ;; test.spectec:1635.1-1635.88
  def $free_elemmode{tableidx : fuck1uN, expr : fuck6fuck1instr*}(ACTIVE_elemmode(tableidx, expr)) = $free_tableidx(tableidx) +++ $free_expr(expr)
  ;; test.spectec:1636.1-1636.33
  def $free_elemmode(PASSIVE_elemmode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1637.1-1637.33
  def $free_elemmode(DECLARE_elemmode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:1604.6-1604.20
relation free_elemmode_is_wf: `%%`fuck5(elemmode : fuck1elemmode, ret_val : fuck1free)
  ;; test.spectec:1604.6-1604.20
  rule free_elemmode_is_wf_0{elemmode : fuck1elemmode, ret_val : fuck1free}:
    `%%`(elemmode, ret_val)
    -- wf_elemmode: `%`(elemmode)
    -- if (ret_val = $free_elemmode(elemmode))
    -- wf_free: `%`(ret_val)

;; test.spectec:1602.1-1602.28
def $free_elem(elem : fuck1elem) : fuck1free
  ;; test.spectec:1631.1-1633.27
  def $free_elem{reftype : fuck1reftype, `expr*` : fuck6fuck1expr*, elemmode : fuck1elemmode}(ELEM_elem(reftype, expr*{expr <- `expr*`}, elemmode)) = $free_reftype(reftype) +++ $free_list($free_expr(expr)*{expr <- `expr*`}) +++ $free_elemmode(elemmode)

;; test.spectec:1602.6-1602.16
relation free_elem_is_wf: `%%`fuck5(elem : fuck1elem, ret_val : fuck1free)
  ;; test.spectec:1602.6-1602.16
  rule free_elem_is_wf_0{elem : fuck1elem, ret_val : fuck1free}:
    `%%`(elem, ret_val)
    -- wf_elem: `%`(elem)
    -- if (ret_val = $free_elem(elem))
    -- wf_free: `%`(ret_val)

;; test.spectec:1605.1-1605.30
def $free_start(start : fuck1start) : fuck1free
  ;; test.spectec:1642.1-1642.56
  def $free_start{funcidx : fuck1uN}(START_start(funcidx)) = $free_funcidx(funcidx)

;; test.spectec:1605.6-1605.17
relation free_start_is_wf: `%%`fuck5(start : fuck1start, ret_val : fuck1free)
  ;; test.spectec:1605.6-1605.17
  rule free_start_is_wf_0{start : fuck1start, ret_val : fuck1free}:
    `%%`(start, ret_val)
    -- wf_start: `%`(start)
    -- if (ret_val = $free_start(start))
    -- wf_free: `%`(ret_val)

;; test.spectec:1606.1-1606.32
def $free_import(import : fuck1import) : fuck1free
  ;; test.spectec:1644.1-1644.81
  def $free_import{name_1 : fuck1name, name_2 : fuck1name, externtype : fuck1externtype}(IMPORT_import(name_1, name_2, externtype)) = $free_externtype(externtype)

;; test.spectec:1606.6-1606.18
relation free_import_is_wf: `%%`fuck5(import : fuck1import, ret_val : fuck1free)
  ;; test.spectec:1606.6-1606.18
  rule free_import_is_wf_0{import : fuck1import, ret_val : fuck1free}:
    `%%`(import, ret_val)
    -- wf_import: `%`(import)
    -- if (ret_val = $free_import(import))
    -- wf_free: `%`(ret_val)

;; test.spectec:1607.1-1607.32
def $free_export(export : fuck1export) : fuck1free
  ;; test.spectec:1646.1-1646.69
  def $free_export{name : fuck1name, externidx : fuck1externidx}(EXPORT_export(name, externidx)) = $free_externidx(externidx)

;; test.spectec:1607.6-1607.18
relation free_export_is_wf: `%%`fuck5(export : fuck1export, ret_val : fuck1free)
  ;; test.spectec:1607.6-1607.18
  rule free_export_is_wf_0{export : fuck1export, ret_val : fuck1free}:
    `%%`(export, ret_val)
    -- wf_export: `%`(export)
    -- if (ret_val = $free_export(export))
    -- wf_free: `%`(ret_val)

;; test.spectec:1608.1-1608.32
def $free_module(module : fuck1module) : fuck1free
  ;; test.spectec:1648.1-1659.36
  def $free_module{`type*` : fuck6fuck1type*, `import*` : fuck6fuck1import*, `tag*` : fuck6fuck1tag*, `global*` : fuck6fuck1global*, `mem*` : fuck6fuck1mem*, `table*` : fuck6fuck1table*, `func*` : fuck6fuck1func*, `data*` : fuck6fuck1data*, `elem*` : fuck6fuck1elem*, `start?` : fuck6fuck1start?, `export*` : fuck6fuck1export*}(MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`}))) = $free_list($free_type(type)*{type <- `type*`}) +++ $free_list($free_tag(tag)*{tag <- `tag*`}) +++ $free_list($free_global(global)*{global <- `global*`}) +++ $free_list($free_mem(mem)*{mem <- `mem*`}) +++ $free_list($free_table(table)*{table <- `table*`}) +++ $free_list($free_func(func)*{func <- `func*`}) +++ $free_list($free_data(data)*{data <- `data*`}) +++ $free_list($free_elem(elem)*{elem <- `elem*`}) +++ $free_opt($free_start(start)?{start <- `start?`}) +++ $free_list($free_import(import)*{import <- `import*`}) +++ $free_list($free_export(export)*{export <- `export*`})

;; test.spectec:1608.6-1608.18
relation free_module_is_wf: `%%`fuck5(module : fuck1module, ret_val : fuck1free)
  ;; test.spectec:1608.6-1608.18
  rule free_module_is_wf_0{module : fuck1module, ret_val : fuck1free}:
    `%%`(module, ret_val)
    -- wf_module: `%`(module)
    -- if (ret_val = $free_module(module))
    -- wf_free: `%`(ret_val)

;; test.spectec:1662.1-1662.89
def $funcidx_module(module : fuck1module) : fuck6fuck1funcidx*
  ;; test.spectec:1663.1-1663.57
  def $funcidx_module{module : fuck1module}(module) = $free_module(module).FUNCS_free

;; test.spectec:1662.6-1662.21
relation funcidx_module_is_wf: `%%`fuck5(module : fuck1module, `ret_val*` : fuck6fuck1funcidx*)
  ;; test.spectec:1662.6-1662.21
  rule funcidx_module_is_wf_0{module : fuck1module, `ret_val*` : fuck6fuck1funcidx*}:
    `%%`(module, `ret_val*`)
    -- wf_module: `%`(module)
    -- if (`ret_val*` = $funcidx_module(module))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:1665.1-1665.87
def $dataidx_funcs(fuck6fuck1func*) : fuck6fuck1dataidx*
  ;; test.spectec:1666.1-1666.64
  def $dataidx_funcs{`func*` : fuck6fuck1func*}(func*{func <- `func*`}) = $free_list($free_func(func)*{func <- `func*`}).DATAS_free

;; test.spectec:1665.6-1665.20
relation dataidx_funcs_is_wf: `%%`fuck5(`var_0*` : fuck6fuck1func*, `ret_val*` : fuck6fuck1dataidx*)
  ;; test.spectec:1665.6-1665.20
  rule dataidx_funcs_is_wf_0{`var_0*` : fuck6fuck1func*, `ret_val*` : fuck6fuck1dataidx*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_func: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $dataidx_funcs(`var_0*`))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:1682.1-1683.16
syntax init = 
  | SET
  | UNSET

;; test.spectec:1685.1-1686.15
syntax localtype = 
  | `%%`fuck5(init : fuck1init, valtype : fuck1valtype)

;; test.spectec:1685.8-1685.17
relation wf_localtype: `%`fuck5(fuck1localtype)
  ;; test.spectec:1685.8-1685.17
  rule localtype_case_0{init : fuck1init, valtype : fuck1valtype}:
    `%`(`%%`_localtype(init, valtype))
    -- wf_valtype: `%`(valtype)

;; test.spectec:1688.1-1689.57
syntax instrtype = 
  | `%->_%%`fuck5(resulttype : fuck1resulttype, `localidx*` : fuck6fuck1localidx*, resulttype : fuck1resulttype)

;; test.spectec:1688.8-1688.17
relation wf_instrtype: `%`fuck5(fuck1instrtype)
  ;; test.spectec:1688.8-1688.17
  rule instrtype_case_0{resulttype : fuck1resulttype, `localidx*` : fuck6fuck1localidx*, resulttype_0 : fuck1resulttype}:
    `%`(`%->_%%`_instrtype(resulttype, `localidx*`, resulttype_0))
    -- (wf_uN: `%%`(32, localidx))*{localidx <- `localidx*`}

;; test.spectec:1714.1-1715.58
syntax context = 
{
  TYPES fuck6fuck1deftype*,
  TAGS fuck6fuck1tagtype*,
  GLOBALS fuck6fuck1globaltype*,
  MEMS fuck6fuck1memtype*,
  TABLES fuck6fuck1tabletype*,
  FUNCS fuck6fuck1deftype*,
  DATAS fuck6fuck1datatype*,
  ELEMS fuck6fuck1elemtype*,
  LOCALS fuck6fuck1localtype*,
  LABELS fuck6fuck1resulttype*,
  RETURN fuck6fuck1resulttype?,
  REFS fuck6fuck1funcidx*,
  RECS fuck6fuck1subtype*
}

;; test.spectec:1714.8-1714.15
relation wf_context: `%`fuck5(fuck1context)
  ;; test.spectec:1714.8-1714.15
  rule context_case_{`var_0*` : fuck6fuck1deftype*, `var_1*` : fuck6fuck1tagtype*, `var_2*` : fuck6fuck1globaltype*, `var_3*` : fuck6fuck1memtype*, `var_4*` : fuck6fuck1tabletype*, `var_5*` : fuck6fuck1deftype*, `var_6*` : fuck6fuck1datatype*, `var_7*` : fuck6fuck1elemtype*, `var_8*` : fuck6fuck1localtype*, `var_9*` : fuck6fuck1resulttype*, `var_10?` : fuck6fuck1resulttype?, `var_11*` : fuck6fuck1funcidx*, `var_12*` : fuck6fuck1subtype*}:
    `%`({TYPES `var_0*`, TAGS `var_1*`, GLOBALS `var_2*`, MEMS `var_3*`, TABLES `var_4*`, FUNCS `var_5*`, DATAS `var_6*`, ELEMS `var_7*`, LOCALS `var_8*`, LABELS `var_9*`, RETURN `var_10?`, REFS `var_11*`, RECS `var_12*`})
    -- (wf_typeuse: `%`(var_1))*{var_1 <- `var_1*`}
    -- (wf_globaltype: `%`(var_2))*{var_2 <- `var_2*`}
    -- (wf_memtype: `%`(var_3))*{var_3 <- `var_3*`}
    -- (wf_tabletype: `%`(var_4))*{var_4 <- `var_4*`}
    -- (wf_reftype: `%`(var_7))*{var_7 <- `var_7*`}
    -- (wf_localtype: `%`(var_8))*{var_8 <- `var_8*`}
    -- (wf_uN: `%%`(32, var_11))*{var_11 <- `var_11*`}
    -- (wf_subtype: `%`(var_12))*{var_12 <- `var_12*`}

;; test.spectec:1723.1-1723.158
rec {

;; test.spectec:1723.1-1723.158
def $with_locals(context : fuck1context, fuck6fuck1localidx*, fuck6fuck1localtype*) : fuck1context
  ;; test.spectec:1725.1-1725.34
  def $with_locals{C : fuck1context}(C, [], []) = C
  ;; test.spectec:1726.1-1726.90
  def $with_locals{C : fuck1context, x_1 : fuck1uN, `x*` : fuck6fuck1idx*, lct_1 : fuck1localtype, `lct*` : fuck6fuck1localtype*}(C, [x_1] ++ x*{x <- `x*`}, [lct_1] ++ lct*{lct <- `lct*`}) = $with_locals(C[LOCALS_context[x_1!`%`_uN.0] = lct_1], x*{x <- `x*`}, lct*{lct <- `lct*`})
}

;; test.spectec:1723.1-1723.158
rec {

;; test.spectec:1723.6-1723.18
relation with_locals_is_wf: `%%%%`fuck5(context : fuck1context, `var_0*` : fuck6fuck1localidx*, `var_1*` : fuck6fuck1localtype*, ret_val : fuck1context)
  ;; test.spectec:1723.6-1723.18
  rule with_locals_is_wf_0{context : fuck1context, `var_0*` : fuck6fuck1localidx*, `var_1*` : fuck6fuck1localtype*, ret_val : fuck1context}:
    `%%%%`(context, `var_0*`, `var_1*`, ret_val)
    -- wf_context: `%`(context)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- `var_0*`}
    -- (wf_localtype: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $with_locals(context, `var_0*`, `var_1*`))
    -- wf_context: `%`(ret_val)
}

;; test.spectec:1736.1-1736.94
rec {

;; test.spectec:1736.1-1736.94
def $clos_deftypes(fuck6fuck1deftype*) : fuck6fuck1deftype*
  ;; test.spectec:1745.1-1745.30
  def $clos_deftypes([]) = []
  ;; test.spectec:1746.1-1746.101
  def $clos_deftypes{`dt*` : fuck6fuck1deftype*, dt_n : fuck1deftype}(dt*{dt <- `dt*`} ++ [dt_n]) = dt'*{dt' <- `dt'*`} ++ [$subst_all_deftype(dt_n, (dt' : fuck1deftype <: fuck1typeuse)*{dt' <- `dt'*`})]
    -- let{`dt'*` : fuck6fuck1deftype*} dt'*{dt' <- `dt'*`} = $clos_deftypes(dt*{dt <- `dt*`})
}

;; test.spectec:1731.1-1731.93
def $clos_valtype(context : fuck1context, valtype : fuck1valtype) : fuck1valtype
  ;; test.spectec:1739.1-1739.89
  def $clos_valtype{C : fuck1context, t : fuck1valtype}(C, t) = $subst_all_valtype(t, (dt : fuck1deftype <: fuck1typeuse)*{dt <- `dt*`})
    -- let{`dt*` : fuck6fuck1deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1731.6-1731.19
relation clos_valtype_is_wf: `%%%`fuck5(context : fuck1context, valtype : fuck1valtype, ret_val : fuck1valtype)
  ;; test.spectec:1731.6-1731.19
  rule clos_valtype_is_wf_0{context : fuck1context, valtype : fuck1valtype, ret_val : fuck1valtype}:
    `%%%`(context, valtype, ret_val)
    -- wf_context: `%`(context)
    -- wf_valtype: `%`(valtype)
    -- if (ret_val = $clos_valtype(context, valtype))
    -- wf_valtype: `%`(ret_val)

;; test.spectec:1732.1-1732.93
def $clos_deftype(context : fuck1context, deftype : fuck1deftype) : fuck1deftype
  ;; test.spectec:1740.1-1740.93
  def $clos_deftype{C : fuck1context, dt : fuck1deftype}(C, dt) = $subst_all_deftype(dt, (dt' : fuck1deftype <: fuck1typeuse)*{dt' <- `dt'*`})
    -- let{`dt'*` : fuck6fuck1deftype*} dt'*{dt' <- `dt'*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1733.1-1733.93
def $clos_tagtype(context : fuck1context, tagtype : fuck1tagtype) : fuck1tagtype
  ;; test.spectec:1741.1-1741.91
  def $clos_tagtype{C : fuck1context, jt : fuck1typeuse}(C, jt) = $subst_all_tagtype(jt, (dt : fuck1deftype <: fuck1typeuse)*{dt <- `dt*`})
    -- let{`dt*` : fuck6fuck1deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1733.6-1733.19
relation clos_tagtype_is_wf: `%%%`fuck5(context : fuck1context, tagtype : fuck1tagtype, ret_val : fuck1tagtype)
  ;; test.spectec:1733.6-1733.19
  rule clos_tagtype_is_wf_0{context : fuck1context, tagtype : fuck1tagtype, ret_val : fuck1tagtype}:
    `%%%`(context, tagtype, ret_val)
    -- wf_context: `%`(context)
    -- wf_typeuse: `%`(tagtype)
    -- if (ret_val = $clos_tagtype(context, tagtype))
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:1734.1-1734.102
def $clos_externtype(context : fuck1context, externtype : fuck1externtype) : fuck1externtype
  ;; test.spectec:1742.1-1742.97
  def $clos_externtype{C : fuck1context, xt : fuck1externtype}(C, xt) = $subst_all_externtype(xt, (dt : fuck1deftype <: fuck1typeuse)*{dt <- `dt*`})
    -- let{`dt*` : fuck6fuck1deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1734.6-1734.22
relation clos_externtype_is_wf: `%%%`fuck5(context : fuck1context, externtype : fuck1externtype, ret_val : fuck1externtype)
  ;; test.spectec:1734.6-1734.22
  rule clos_externtype_is_wf_0{context : fuck1context, externtype : fuck1externtype, ret_val : fuck1externtype}:
    `%%%`(context, externtype, ret_val)
    -- wf_context: `%`(context)
    -- wf_externtype: `%`(externtype)
    -- if (ret_val = $clos_externtype(context, externtype))
    -- wf_externtype: `%`(ret_val)

;; test.spectec:1735.1-1735.102
def $clos_moduletype(context : fuck1context, moduletype : fuck1moduletype) : fuck1moduletype
  ;; test.spectec:1743.1-1743.99
  def $clos_moduletype{C : fuck1context, mmt : fuck1moduletype}(C, mmt) = $subst_all_moduletype(mmt, (dt : fuck1deftype <: fuck1typeuse)*{dt <- `dt*`})
    -- let{`dt*` : fuck6fuck1deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1735.6-1735.22
relation clos_moduletype_is_wf: `%%%`fuck5(context : fuck1context, moduletype : fuck1moduletype, ret_val : fuck1moduletype)
  ;; test.spectec:1735.6-1735.22
  rule clos_moduletype_is_wf_0{context : fuck1context, moduletype : fuck1moduletype, ret_val : fuck1moduletype}:
    `%%%`(context, moduletype, ret_val)
    -- wf_context: `%`(context)
    -- wf_moduletype: `%`(moduletype)
    -- if (ret_val = $clos_moduletype(context, moduletype))
    -- wf_moduletype: `%`(ret_val)

;; test.spectec:1761.1-1761.91
relation Numtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1numtype)
  ;; test.spectec:1768.1-1769.20
  rule _{C : fuck1context, numtype : fuck1numtype}:
    `%|-%:OK`(C, numtype)
    -- wf_context: `%`(C)

;; test.spectec:1762.1-1762.91
relation Vectype_ok: `%|-%:OK`fuck5(fuck1context, fuck1vectype)
  ;; test.spectec:1771.1-1772.20
  rule _{C : fuck1context, vectype : fuck1vectype}:
    `%|-%:OK`(C, vectype)
    -- wf_context: `%`(C)

;; test.spectec:1842.1-1843.79
syntax oktypenat = 
  | OKfuck5(fuck3nat)

;; test.spectec:1845.1-1845.103
relation Packtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1packtype)
  ;; test.spectec:1873.1-1874.21
  rule _{C : fuck1context, packtype : fuck1packtype}:
    `%|-%:OK`(C, packtype)
    -- wf_context: `%`(C)

;; test.spectec:2168.1-2168.116
relation Packtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1packtype, fuck1packtype)
  ;; test.spectec:2177.1-2178.28
  rule _{C : fuck1context, packtype : fuck1packtype}:
    `%|-%<:%`(C, packtype, packtype)
    -- wf_context: `%`(C)

;; test.spectec:2026.1-2026.103
relation Numtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1numtype, fuck1numtype)
  ;; test.spectec:2032.1-2033.26
  rule _{C : fuck1context, numtype : fuck1numtype}:
    `%|-%<:%`(C, numtype, numtype)
    -- wf_context: `%`(C)

;; test.spectec:1827.1-1828.70
relation Expand: `%~~%`fuck5(fuck1deftype, fuck1comptype)
  ;; test.spectec:1832.1-1832.91
  rule _{deftype : fuck1deftype, comptype : fuck1comptype, `final?` : fuck6fuck1final?, `typeuse*` : fuck6fuck1typeuse*}:
    `%~~%`(deftype, comptype)
    -- if ($unrolldt(deftype) = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype))
    -- wf_subtype: `%`($unrolldt(deftype))
    -- wf_subtype: `%`(SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype))

;; test.spectec:2027.1-2027.103
relation Vectype_sub: `%|-%<:%`fuck5(fuck1context, fuck1vectype, fuck1vectype)
  ;; test.spectec:2035.1-2036.26
  rule _{C : fuck1context, vectype : fuck1vectype}:
    `%|-%<:%`(C, vectype, vectype)
    -- wf_context: `%`(C)

;; test.spectec:1912.1-1912.70
def $before(typeuse : fuck1typeuse, nat : fuck3nat) : fuck2bool
  ;; test.spectec:1913.1-1913.30
  def $before{j : fuck3nat, i : fuck3nat}(REC_typeuse(j), i) = (j < i)
  ;; test.spectec:1914.1-1914.45
  def $before{typeuse : fuck1typeuse, i : fuck3nat}(typeuse, i) = true

;; test.spectec:1916.1-1916.44
def $unrollht_(context : fuck1context, heaptype : fuck1heaptype) : fuck1subtype
  ;; test.spectec:1917.1-1917.48
  def $unrollht_{C : fuck1context, deftype : fuck1deftype}(C, (deftype : fuck1deftype <: fuck1heaptype)) = $unrolldt(deftype)
  ;; test.spectec:1918.1-1918.62
  def $unrollht_{C : fuck1context, typeidx : fuck1uN}(C, _IDX_heaptype(typeidx)) = $unrolldt(C.TYPES_context[typeidx!`%`_uN.0])
  ;; test.spectec:1919.1-1919.37
  def $unrollht_{C : fuck1context, i : fuck3nat}(C, REC_heaptype(i)) = C.RECS_context[i]

;; test.spectec:1916.6-1916.16
relation unrollht__is_wf: `%%%`fuck5(context : fuck1context, heaptype : fuck1heaptype, ret_val : fuck1subtype)
  ;; test.spectec:1916.6-1916.16
  rule unrollht__is_wf_0{context : fuck1context, heaptype : fuck1heaptype, ret_val : fuck1subtype}:
    `%%%`(context, heaptype, ret_val)
    -- wf_context: `%`(context)
    -- wf_heaptype: `%`(heaptype)
    -- if (ret_val = $unrollht_(context, heaptype))
    -- wf_subtype: `%`(ret_val)

;; test.spectec:1763.1-2170.117
rec {

;; test.spectec:1763.1-1763.92
relation Heaptype_ok: `%|-%:OK`fuck5(fuck1context, fuck1heaptype)
  ;; test.spectec:1774.1-1775.24
  rule abs{C : fuck1context, absheaptype : fuck1absheaptype}:
    `%|-%:OK`(C, (absheaptype : fuck1absheaptype <: fuck1heaptype))
    -- wf_context: `%`(C)

  ;; test.spectec:1777.1-1779.35
  rule typeuse{C : fuck1context, typeuse : fuck1typeuse}:
    `%|-%:OK`(C, (typeuse : fuck1typeuse <: fuck1heaptype))
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(typeuse)

  ;; test.spectec:1781.1-1782.16
  rule bot{C : fuck1context}:
    `%|-%:OK`(C, BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(BOT_heaptype)

;; test.spectec:1764.1-1764.91
relation Reftype_ok: `%|-%:OK`fuck5(fuck1context, fuck1reftype)
  ;; test.spectec:1784.1-1786.37
  rule _{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%:OK`(C, REF_reftype(?(NULL_null), heaptype))
    -- Heaptype_ok: `%|-%:OK`(C, heaptype)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), heaptype))

;; test.spectec:1765.1-1765.91
relation Valtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1valtype)
  ;; test.spectec:1788.1-1790.35
  rule num{C : fuck1context, numtype : fuck1numtype}:
    `%|-%:OK`(C, (numtype : fuck1numtype <: fuck1valtype))
    -- Numtype_ok: `%|-%:OK`(C, numtype)
    -- wf_context: `%`(C)

  ;; test.spectec:1792.1-1794.35
  rule vec{C : fuck1context, vectype : fuck1vectype}:
    `%|-%:OK`(C, (vectype : fuck1vectype <: fuck1valtype))
    -- Vectype_ok: `%|-%:OK`(C, vectype)
    -- wf_context: `%`(C)

  ;; test.spectec:1796.1-1798.35
  rule ref{C : fuck1context, reftype : fuck1reftype}:
    `%|-%:OK`(C, (reftype : fuck1reftype <: fuck1valtype))
    -- Reftype_ok: `%|-%:OK`(C, reftype)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(reftype)

  ;; test.spectec:1800.1-1801.16
  rule bot{C : fuck1context}:
    `%|-%:OK`(C, BOT_valtype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(BOT_valtype)

;; test.spectec:1766.1-1766.94
relation Typeuse_ok: `%|-%:OK`fuck5(fuck1context, fuck1typeuse)
  ;; test.spectec:1860.1-1862.30
  rule typeidx{C : fuck1context, typeidx : fuck1typeidx, dt : fuck1deftype}:
    `%|-%:OK`(C, _IDX_typeuse(typeidx))
    -- if (C.TYPES_context[typeidx!`%`_uN.0] = dt)
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(_IDX_typeuse(typeidx))

  ;; test.spectec:1864.1-1866.23
  rule rec{C : fuck1context, i : fuck1n, st : fuck1subtype}:
    `%|-%:OK`(C, REC_typeuse(i))
    -- if (C.RECS_context[i] = st)
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(st)
    -- wf_typeuse: `%`(REC_typeuse(i))

  ;; test.spectec:1868.1-1870.35
  rule deftype{C : fuck1context, deftype : fuck1deftype}:
    `%|-%:OK`(C, (deftype : fuck1deftype <: fuck1typeuse))
    -- Deftype_ok: `%|-%:OK`(C, deftype)
    -- wf_context: `%`(C)

;; test.spectec:1807.1-1807.100
relation Resulttype_ok: `%|-%:OK`fuck5(fuck1context, fuck1resulttype)
  ;; test.spectec:1814.1-1816.32
  rule _{C : fuck1context, `t*` : fuck6fuck1valtype*}:
    `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))
    -- (Valtype_ok: `%|-%:OK`(C, t))*{t <- `t*`}
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t))*{t <- `t*`}

;; test.spectec:1846.1-1846.104
relation Fieldtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1fieldtype)
  ;; test.spectec:1884.1-1886.43
  rule _{C : fuck1context, storagetype : fuck1storagetype}:
    `%|-%:OK`(C, `%%`_fieldtype(?(MUT_mut), storagetype))
    -- Storagetype_ok: `%|-%:OK`(C, storagetype)
    -- wf_context: `%`(C)
    -- wf_fieldtype: `%`(`%%`_fieldtype(?(MUT_mut), storagetype))

;; test.spectec:1847.1-1847.106
relation Storagetype_ok: `%|-%:OK`fuck5(fuck1context, fuck1storagetype)
  ;; test.spectec:1876.1-1878.35
  rule val{C : fuck1context, valtype : fuck1valtype}:
    `%|-%:OK`(C, (valtype : fuck1valtype <: fuck1storagetype))
    -- Valtype_ok: `%|-%:OK`(C, valtype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(valtype)

  ;; test.spectec:1880.1-1882.37
  rule pack{C : fuck1context, packtype : fuck1packtype}:
    `%|-%:OK`(C, (packtype : fuck1packtype <: fuck1storagetype))
    -- Packtype_ok: `%|-%:OK`(C, packtype)
    -- wf_context: `%`(C)

;; test.spectec:1848.1-1848.103
relation Comptype_ok: `%|-%:OK`fuck5(fuck1context, fuck1comptype)
  ;; test.spectec:1889.1-1891.42
  rule struct{C : fuck1context, `fieldtype*` : fuck6fuck1fieldtype*}:
    `%|-%:OK`(C, STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))
    -- (Fieldtype_ok: `%|-%:OK`(C, fieldtype))*{fieldtype <- `fieldtype*`}
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))

  ;; test.spectec:1893.1-1895.39
  rule array{C : fuck1context, fieldtype : fuck1fieldtype}:
    `%|-%:OK`(C, ARRAY_comptype(fieldtype))
    -- Fieldtype_ok: `%|-%:OK`(C, fieldtype)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(ARRAY_comptype(fieldtype))

  ;; test.spectec:1897.1-1900.35
  rule func{C : fuck1context, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:OK`(C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:1851.1-1851.126
relation Subtype_ok2: `%|-%:%`fuck5(fuck1context, fuck1subtype, fuck1oktypenat)
  ;; test.spectec:1921.1-1930.49
  rule _{C : fuck1context, `typeuse*` : fuck6fuck1typeuse*, comptype : fuck1comptype, i : fuck3nat, `comptype'*` : fuck6fuck1comptype*, `typeuse'**` : fuck6fuck6fuck1typeuse**}:
    `%|-%:%`(C, SUB_subtype(?(FINAL_final), typeuse*{typeuse <- `typeuse*`}, comptype), OK_oktypenat(i))
    -- if (|typeuse*{typeuse <- `typeuse*`}| <= 1)
    -- (Typeuse_ok: `%|-%:OK`(C, typeuse))*{typeuse <- `typeuse*`}
    -- (if $before(typeuse, i))*{typeuse <- `typeuse*`}
    -- (if ($unrollht_(C, (typeuse : fuck1typeuse <: fuck1heaptype)) = SUB_subtype(?(), typeuse'*{typeuse' <- `typeuse'*`}, comptype')))*{comptype' <- `comptype'*`, typeuse <- `typeuse*`, `typeuse'*` <- `typeuse'**`}
    -- Comptype_ok: `%|-%:OK`(C, comptype)
    -- (Comptype_sub: `%|-%<:%`(C, comptype, comptype'))*{comptype' <- `comptype'*`}
    -- wf_context: `%`(C)
    -- (wf_subtype: `%`($unrollht_(C, (typeuse : fuck1typeuse <: fuck1heaptype))))*{typeuse <- `typeuse*`}
    -- wf_subtype: `%`(SUB_subtype(?(FINAL_final), typeuse*{typeuse <- `typeuse*`}, comptype))
    -- (wf_subtype: `%`(SUB_subtype(?(), typeuse'*{typeuse' <- `typeuse'*`}, comptype')))*{comptype' <- `comptype'*`, `typeuse'*` <- `typeuse'**`}

;; test.spectec:1852.1-1852.126
relation Rectype_ok2: `%|-%:%`fuck5(fuck1context, fuck1rectype, fuck1oktypenat)
  ;; test.spectec:1942.1-1943.23
  rule empty{C : fuck1context, i : fuck3nat}:
    `%|-%:%`(C, REC_rectype(`%`_list([])), OK_oktypenat(i))
    -- wf_context: `%`(C)

  ;; test.spectec:1945.1-1948.49
  rule cons{C : fuck1context, subtype_1 : fuck1subtype, `subtype*` : fuck6fuck1subtype*, i : fuck3nat}:
    `%|-%:%`(C, REC_rectype(`%`_list([subtype_1] ++ subtype*{subtype <- `subtype*`})), OK_oktypenat(i))
    -- Subtype_ok2: `%|-%:%`(C, subtype_1, OK_oktypenat(i))
    -- Rectype_ok2: `%|-%:%`(C, REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})), OK_oktypenat((i + 1)))
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(subtype_1)
    -- (wf_subtype: `%`(subtype))*{subtype <- `subtype*`}

;; test.spectec:1853.1-1853.102
relation Deftype_ok: `%|-%:OK`fuck5(fuck1context, fuck1deftype)
  ;; test.spectec:1951.1-1955.14
  rule _{C : fuck1context, rectype : fuck1rectype, i : fuck1n, n : fuck1n, `subtype*` : fuck6fuck1subtype*}:
    `%|-%:OK`(C, _DEF_deftype(rectype, i))
    -- Rectype_ok2: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS subtype^n{subtype <- `subtype*`}} +++ C, rectype, OK_oktypenat(0))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))
    -- if (i < n)
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS subtype^n{subtype <- `subtype*`}})

;; test.spectec:1856.1-1856.108
relation Comptype_sub: `%|-%<:%`fuck5(fuck1context, fuck1comptype, fuck1comptype)
  ;; test.spectec:2200.1-2202.41
  rule struct{C : fuck1context, `ft_1*` : fuck6fuck1fieldtype*, `ft'_1*` : fuck6fuck1fieldtype*, `ft_2*` : fuck6fuck1fieldtype*}:
    `%|-%<:%`(C, STRUCT_comptype(`%`_list(ft_1*{ft_1 <- `ft_1*`} ++ ft'_1*{ft'_1 <- `ft'_1*`})), STRUCT_comptype(`%`_list(ft_2*{ft_2 <- `ft_2*`})))
    -- (Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2))*{ft_1 <- `ft_1*`, ft_2 <- `ft_2*`}
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(ft_1*{ft_1 <- `ft_1*`} ++ ft'_1*{ft'_1 <- `ft'_1*`})))
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(ft_2*{ft_2 <- `ft_2*`})))

  ;; test.spectec:2204.1-2206.38
  rule array{C : fuck1context, ft_1 : fuck1fieldtype, ft_2 : fuck1fieldtype}:
    `%|-%<:%`(C, ARRAY_comptype(ft_1), ARRAY_comptype(ft_2))
    -- Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(ARRAY_comptype(ft_1))
    -- wf_comptype: `%`(ARRAY_comptype(ft_2))

  ;; test.spectec:2208.1-2211.41
  rule func{C : fuck1context, `t_11*` : fuck6fuck1valtype*, `t_12*` : fuck6fuck1valtype*, `t_21*` : fuck6fuck1valtype*, `t_22*` : fuck6fuck1valtype*}:
    `%|-%<:%`(C, `FUNC%->%`_comptype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), `%`_resulttype(t_12*{t_12 <- `t_12*`})), `FUNC%->%`_comptype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_11*{t_11 <- `t_11*`}))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_12*{t_12 <- `t_12*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`}))
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), `%`_resulttype(t_12*{t_12 <- `t_12*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`})))

;; test.spectec:1857.1-1857.107
relation Deftype_sub: `%|-%<:%`fuck5(fuck1context, fuck1deftype, fuck1deftype)
  ;; test.spectec:2214.1-2216.66
  rule refl{C : fuck1context, deftype_1 : fuck1deftype, deftype_2 : fuck1deftype}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($clos_deftype(C, deftype_1) = $clos_deftype(C, deftype_2))
    -- wf_context: `%`(C)

  ;; test.spectec:2218.1-2221.49
  rule super{C : fuck1context, deftype_1 : fuck1deftype, deftype_2 : fuck1deftype, `final?` : fuck6fuck1final?, `typeuse*` : fuck6fuck1typeuse*, ct : fuck1comptype, i : fuck3nat}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($unrolldt(deftype_1) = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))
    -- Heaptype_sub: `%|-%<:%`(C, (typeuse*{typeuse <- `typeuse*`}[i] : fuck1typeuse <: fuck1heaptype), (deftype_2 : fuck1deftype <: fuck1heaptype))
    -- wf_context: `%`(C)
    -- wf_subtype: `%`($unrolldt(deftype_1))
    -- wf_subtype: `%`(SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))

;; test.spectec:2028.1-2028.104
relation Heaptype_sub: `%|-%<:%`fuck5(fuck1context, fuck1heaptype, fuck1heaptype)
  ;; test.spectec:2039.1-2040.28
  rule refl{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, heaptype, heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)

  ;; test.spectec:2042.1-2046.48
  rule trans{C : fuck1context, heaptype_1 : fuck1heaptype, heaptype_2 : fuck1heaptype, heaptype' : fuck1heaptype}:
    `%|-%<:%`(C, heaptype_1, heaptype_2)
    -- Heaptype_ok: `%|-%:OK`(C, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype_1, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype', heaptype_2)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype_1)
    -- wf_heaptype: `%`(heaptype_2)
    -- wf_heaptype: `%`(heaptype')

  ;; test.spectec:2048.1-2049.17
  rule `eq-any`{C : fuck1context}:
    `%|-%<:%`(C, EQ_heaptype, ANY_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(EQ_heaptype)
    -- wf_heaptype: `%`(ANY_heaptype)

  ;; test.spectec:2051.1-2052.17
  rule `i31-eq`{C : fuck1context}:
    `%|-%<:%`(C, I31_heaptype, EQ_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(I31_heaptype)
    -- wf_heaptype: `%`(EQ_heaptype)

  ;; test.spectec:2054.1-2055.20
  rule `struct-eq`{C : fuck1context}:
    `%|-%<:%`(C, STRUCT_heaptype, EQ_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(STRUCT_heaptype)
    -- wf_heaptype: `%`(EQ_heaptype)

  ;; test.spectec:2057.1-2058.19
  rule `array-eq`{C : fuck1context}:
    `%|-%<:%`(C, ARRAY_heaptype, EQ_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(ARRAY_heaptype)
    -- wf_heaptype: `%`(EQ_heaptype)

  ;; test.spectec:2060.1-2062.42
  rule struct{C : fuck1context, deftype : fuck1deftype, `fieldtype*` : fuck6fuck1fieldtype*}:
    `%|-%<:%`(C, (deftype : fuck1deftype <: fuck1heaptype), STRUCT_heaptype)
    -- Expand: `%~~%`(deftype, STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(STRUCT_heaptype)
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))

  ;; test.spectec:2064.1-2066.40
  rule array{C : fuck1context, deftype : fuck1deftype, fieldtype : fuck1fieldtype}:
    `%|-%<:%`(C, (deftype : fuck1deftype <: fuck1heaptype), ARRAY_heaptype)
    -- Expand: `%~~%`(deftype, ARRAY_comptype(fieldtype))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(ARRAY_heaptype)
    -- wf_comptype: `%`(ARRAY_comptype(fieldtype))

  ;; test.spectec:2068.1-2070.42
  rule func{C : fuck1context, deftype : fuck1deftype, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%<:%`(C, (deftype : fuck1deftype <: fuck1heaptype), FUNC_heaptype)
    -- Expand: `%~~%`(deftype, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(FUNC_heaptype)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2072.1-2074.46
  rule def{C : fuck1context, deftype_1 : fuck1deftype, deftype_2 : fuck1deftype}:
    `%|-%<:%`(C, (deftype_1 : fuck1deftype <: fuck1heaptype), (deftype_2 : fuck1deftype <: fuck1heaptype))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- wf_context: `%`(C)

  ;; test.spectec:2076.1-2078.53
  rule `typeidx-l`{C : fuck1context, typeidx : fuck1typeidx, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, _IDX_heaptype(typeidx), heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, (C.TYPES_context[typeidx!`%`_uN.0] : fuck1deftype <: fuck1heaptype), heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(_IDX_heaptype(typeidx))

  ;; test.spectec:2080.1-2082.53
  rule `typeidx-r`{C : fuck1context, heaptype : fuck1heaptype, typeidx : fuck1typeidx}:
    `%|-%<:%`(C, heaptype, _IDX_heaptype(typeidx))
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, (C.TYPES_context[typeidx!`%`_uN.0] : fuck1deftype <: fuck1heaptype))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(_IDX_heaptype(typeidx))

  ;; test.spectec:2084.1-2086.51
  rule `rec-struct`{C : fuck1context, i : fuck1n, `final?` : fuck6fuck1final?, `fieldtype*` : fuck6fuck1fieldtype*}:
    `%|-%<:%`(C, REC_heaptype(i), STRUCT_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_heaptype: `%`(STRUCT_heaptype)
    -- wf_subtype: `%`(SUB_subtype(final?{final <- `final?`}, [], STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))))

  ;; test.spectec:2088.1-2090.49
  rule `rec-array`{C : fuck1context, i : fuck1n, `final?` : fuck6fuck1final?, fieldtype : fuck1fieldtype}:
    `%|-%<:%`(C, REC_heaptype(i), ARRAY_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], ARRAY_comptype(fieldtype)))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_heaptype: `%`(ARRAY_heaptype)
    -- wf_subtype: `%`(SUB_subtype(final?{final <- `final?`}, [], ARRAY_comptype(fieldtype)))

  ;; test.spectec:2092.1-2094.51
  rule `rec-func`{C : fuck1context, i : fuck1n, `final?` : fuck6fuck1final?, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%<:%`(C, REC_heaptype(i), FUNC_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_heaptype: `%`(FUNC_heaptype)
    -- wf_subtype: `%`(SUB_subtype(final?{final <- `final?`}, [], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))

  ;; test.spectec:2096.1-2098.43
  rule `rec-sub`{C : fuck1context, i : fuck1n, `typeuse*` : fuck6fuck1typeuse*, j : fuck3nat, `final?` : fuck6fuck1final?, ct : fuck1comptype}:
    `%|-%<:%`(C, REC_heaptype(i), (typeuse*{typeuse <- `typeuse*`}[j] : fuck1typeuse <: fuck1heaptype))
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_subtype: `%`(SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))

  ;; test.spectec:2100.1-2103.25
  rule none{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, NONE_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, ANY_heaptype)
    -- if (heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(NONE_heaptype)
    -- wf_heaptype: `%`(ANY_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2105.1-2108.25
  rule nofunc{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, NOFUNC_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, FUNC_heaptype)
    -- if (heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(NOFUNC_heaptype)
    -- wf_heaptype: `%`(FUNC_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2110.1-2113.25
  rule noexn{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, NOEXN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXN_heaptype)
    -- if (heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(NOEXN_heaptype)
    -- wf_heaptype: `%`(EXN_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2115.1-2118.25
  rule noextern{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, NOEXTERN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXTERN_heaptype)
    -- if (heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(NOEXTERN_heaptype)
    -- wf_heaptype: `%`(EXTERN_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2120.1-2121.23
  rule bot{C : fuck1context, heaptype : fuck1heaptype}:
    `%|-%<:%`(C, BOT_heaptype, heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

;; test.spectec:2029.1-2029.103
relation Reftype_sub: `%|-%<:%`fuck5(fuck1context, fuck1reftype, fuck1reftype)
  ;; test.spectec:2124.1-2126.37
  rule nonnull{C : fuck1context, ht_1 : fuck1heaptype, ht_2 : fuck1heaptype}:
    `%|-%<:%`(C, REF_reftype(?(), ht_1), REF_reftype(?(), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(REF_reftype(?(), ht_1))
    -- wf_reftype: `%`(REF_reftype(?(), ht_2))

  ;; test.spectec:2128.1-2130.37
  rule null{C : fuck1context, ht_1 : fuck1heaptype, ht_2 : fuck1heaptype}:
    `%|-%<:%`(C, REF_reftype(?(NULL_null), ht_1), REF_reftype(?(NULL_null), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), ht_1))
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), ht_2))

;; test.spectec:2030.1-2030.103
relation Valtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1valtype, fuck1valtype)
  ;; test.spectec:2133.1-2135.46
  rule num{C : fuck1context, numtype_1 : fuck1numtype, numtype_2 : fuck1numtype}:
    `%|-%<:%`(C, (numtype_1 : fuck1numtype <: fuck1valtype), (numtype_2 : fuck1numtype <: fuck1valtype))
    -- Numtype_sub: `%|-%<:%`(C, numtype_1, numtype_2)
    -- wf_context: `%`(C)

  ;; test.spectec:2137.1-2139.46
  rule vec{C : fuck1context, vectype_1 : fuck1vectype, vectype_2 : fuck1vectype}:
    `%|-%<:%`(C, (vectype_1 : fuck1vectype <: fuck1valtype), (vectype_2 : fuck1vectype <: fuck1valtype))
    -- Vectype_sub: `%|-%<:%`(C, vectype_1, vectype_2)
    -- wf_context: `%`(C)

  ;; test.spectec:2141.1-2143.46
  rule ref{C : fuck1context, reftype_1 : fuck1reftype, reftype_2 : fuck1reftype}:
    `%|-%<:%`(C, (reftype_1 : fuck1reftype <: fuck1valtype), (reftype_2 : fuck1reftype <: fuck1valtype))
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(reftype_1)
    -- wf_reftype: `%`(reftype_2)

  ;; test.spectec:2145.1-2146.22
  rule bot{C : fuck1context, valtype : fuck1valtype}:
    `%|-%<:%`(C, BOT_valtype, valtype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(valtype)
    -- wf_valtype: `%`(BOT_valtype)

;; test.spectec:2151.1-2151.115
relation Resulttype_sub: `%|-%<:%`fuck5(fuck1context, fuck1resulttype, fuck1resulttype)
  ;; test.spectec:2154.1-2156.37
  rule _{C : fuck1context, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%<:%`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (Valtype_sub: `%|-%<:%`(C, t_1, t_2))*{t_1 <- `t_1*`, t_2 <- `t_2*`}
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t_1))*{t_1 <- `t_1*`}
    -- (wf_valtype: `%`(t_2))*{t_2 <- `t_2*`}

;; test.spectec:2169.1-2169.119
relation Storagetype_sub: `%|-%<:%`fuck5(fuck1context, fuck1storagetype, fuck1storagetype)
  ;; test.spectec:2181.1-2183.46
  rule val{C : fuck1context, valtype_1 : fuck1valtype, valtype_2 : fuck1valtype}:
    `%|-%<:%`(C, (valtype_1 : fuck1valtype <: fuck1storagetype), (valtype_2 : fuck1valtype <: fuck1storagetype))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(valtype_1)
    -- wf_valtype: `%`(valtype_2)

  ;; test.spectec:2185.1-2187.49
  rule pack{C : fuck1context, packtype_1 : fuck1packtype, packtype_2 : fuck1packtype}:
    `%|-%<:%`(C, (packtype_1 : fuck1packtype <: fuck1storagetype), (packtype_2 : fuck1packtype <: fuck1storagetype))
    -- Packtype_sub: `%|-%<:%`(C, packtype_1, packtype_2)
    -- wf_context: `%`(C)

;; test.spectec:2170.1-2170.117
relation Fieldtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1fieldtype, fuck1fieldtype)
  ;; test.spectec:2190.1-2192.40
  rule const{C : fuck1context, zt_1 : fuck1storagetype, zt_2 : fuck1storagetype}:
    `%|-%<:%`(C, `%%`_fieldtype(?(), zt_1), `%%`_fieldtype(?(), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- wf_context: `%`(C)
    -- wf_fieldtype: `%`(`%%`_fieldtype(?(), zt_1))
    -- wf_fieldtype: `%`(`%%`_fieldtype(?(), zt_2))

  ;; test.spectec:2194.1-2197.40
  rule var{C : fuck1context, zt_1 : fuck1storagetype, zt_2 : fuck1storagetype}:
    `%|-%<:%`(C, `%%`_fieldtype(?(MUT_mut), zt_1), `%%`_fieldtype(?(MUT_mut), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)
    -- wf_context: `%`(C)
    -- wf_fieldtype: `%`(`%%`_fieldtype(?(MUT_mut), zt_1))
    -- wf_fieldtype: `%`(`%%`_fieldtype(?(MUT_mut), zt_2))
}

;; test.spectec:1806.1-1806.96
relation Localtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1localtype)
  ;; test.spectec:1810.1-1812.29
  rule _{C : fuck1context, init : fuck1init, t : fuck1valtype}:
    `%|-%:OK`(C, `%%`_localtype(init, t))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_localtype: `%`(`%%`_localtype(init, t))

;; test.spectec:1808.1-1808.99
relation Instrtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1instrtype)
  ;; test.spectec:1818.1-1822.29
  rule _{C : fuck1context, `t_1*` : fuck6fuck1valtype*, `x*` : fuck6fuck1idx*, `t_2*` : fuck6fuck1valtype*, `lct*` : fuck6fuck1localtype*}:
    `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (if (C.LOCALS_context[x!`%`_uN.0] = lct))*{lct <- `lct*`, x <- `x*`}
    -- wf_context: `%`(C)
    -- (wf_localtype: `%`(lct))*{lct <- `lct*`}
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:1829.1-1830.70
relation Expand_use: `%~~_%%`fuck5(fuck1typeuse, fuck1context, fuck1comptype)
  ;; test.spectec:1834.1-1834.84
  rule deftype{deftype : fuck1deftype, C : fuck1context, comptype : fuck1comptype}:
    `%~~_%%`((deftype : fuck1deftype <: fuck1typeuse), C, comptype)
    -- Expand: `%~~%`(deftype, comptype)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(comptype)

  ;; test.spectec:1835.1-1835.93
  rule typeidx{typeidx : fuck1typeidx, C : fuck1context, comptype : fuck1comptype}:
    `%~~_%%`(_IDX_typeuse(typeidx), C, comptype)
    -- Expand: `%~~%`(C.TYPES_context[typeidx!`%`_uN.0], comptype)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(comptype)
    -- wf_typeuse: `%`(_IDX_typeuse(typeidx))

;; test.spectec:1840.1-1841.76
syntax oktypeidx = 
  | OKfuck5(typeidx : fuck1typeidx)

;; test.spectec:1840.8-1840.17
relation wf_oktypeidx: `%`fuck5(fuck1oktypeidx)
  ;; test.spectec:1840.8-1840.17
  rule oktypeidx_case_0{typeidx : fuck1typeidx}:
    `%`(OK_oktypeidx(typeidx))
    -- wf_uN: `%%`(32, typeidx)

;; test.spectec:1849.1-1849.126
relation Subtype_ok: `%|-%:%`fuck5(fuck1context, fuck1subtype, fuck1oktypeidx)
  ;; test.spectec:1903.1-1910.49
  rule _{C : fuck1context, `x*` : fuck6fuck1idx*, comptype : fuck1comptype, x_0 : fuck1idx, `comptype'*` : fuck6fuck1comptype*, `yy**` : fuck6fuck6fuck1typeuse**}:
    `%|-%:%`(C, SUB_subtype(?(FINAL_final), _IDX_typeuse(x)*{x <- `x*`}, comptype), OK_oktypeidx(x_0))
    -- if (|x*{x <- `x*`}| <= 1)
    -- (if (x!`%`_uN.0 < x_0!`%`_uN.0))*{x <- `x*`}
    -- (if ($unrolldt(C.TYPES_context[x!`%`_uN.0]) = SUB_subtype(?(), yy*{yy <- `yy*`}, comptype')))*{comptype' <- `comptype'*`, x <- `x*`, `yy*` <- `yy**`}
    -- Comptype_ok: `%|-%:OK`(C, comptype)
    -- (Comptype_sub: `%|-%<:%`(C, comptype, comptype'))*{comptype' <- `comptype'*`}
    -- wf_context: `%`(C)
    -- (wf_subtype: `%`($unrolldt(C.TYPES_context[x!`%`_uN.0])))*{x <- `x*`}
    -- wf_subtype: `%`(SUB_subtype(?(FINAL_final), _IDX_typeuse(x)*{x <- `x*`}, comptype))
    -- wf_oktypeidx: `%`(OK_oktypeidx(x_0))
    -- (wf_subtype: `%`(SUB_subtype(?(), yy*{yy <- `yy*`}, comptype')))*{comptype' <- `comptype'*`, `yy*` <- `yy**`}

;; test.spectec:1850.1-1850.126
rec {

;; test.spectec:1850.1-1850.126
relation Rectype_ok: `%|-%:%`fuck5(fuck1context, fuck1rectype, fuck1oktypeidx)
  ;; test.spectec:1933.1-1934.23
  rule empty{C : fuck1context, x : fuck1idx}:
    `%|-%:%`(C, REC_rectype(`%`_list([])), OK_oktypeidx(x))
    -- wf_context: `%`(C)
    -- wf_oktypeidx: `%`(OK_oktypeidx(x))

  ;; test.spectec:1936.1-1939.48
  rule cons{C : fuck1context, subtype_1 : fuck1subtype, `subtype*` : fuck6fuck1subtype*, x : fuck1idx}:
    `%|-%:%`(C, REC_rectype(`%`_list([subtype_1] ++ subtype*{subtype <- `subtype*`})), OK_oktypeidx(x))
    -- Subtype_ok: `%|-%:%`(C, subtype_1, OK_oktypeidx(x))
    -- Rectype_ok: `%|-%:%`(C, REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})), OK_oktypeidx(`%`_typeidx((x!`%`_uN.0 + 1))))
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(subtype_1)
    -- (wf_subtype: `%`(subtype))*{subtype <- `subtype*`}
    -- wf_oktypeidx: `%`(OK_oktypeidx(x))
    -- wf_oktypeidx: `%`(OK_oktypeidx(`%`_typeidx((x!`%`_uN.0 + 1))))
}

;; test.spectec:1960.1-1960.120
relation Limits_ok: `%|-%:%`fuck5(fuck1context, fuck1limits, fuck3nat)
  ;; test.spectec:1968.1-1971.23
  rule _{C : fuck1context, n : fuck1n, `m?` : fuck6fuck1m?, k : fuck3nat}:
    `%|-%:%`(C, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), k)
    -- if (n <= k)
    -- (if ((n <= m) /\ (m <= k)))?{m <- `m?`}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}))

;; test.spectec:1961.1-1961.97
relation Tagtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1tagtype)
  ;; test.spectec:1973.1-1976.54
  rule _{C : fuck1context, typeuse : fuck1typeuse, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:OK`(C, typeuse)
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- Expand_use: `%~~_%%`(typeuse, C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(typeuse)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:1962.1-1962.100
relation Globaltype_ok: `%|-%:OK`fuck5(fuck1context, fuck1globaltype)
  ;; test.spectec:1978.1-1980.29
  rule _{C : fuck1context, t : fuck1valtype}:
    `%|-%:OK`(C, `%%`_globaltype(?(MUT_mut), t))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_globaltype: `%`(`%%`_globaltype(?(MUT_mut), t))

;; test.spectec:1963.1-1963.97
relation Memtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1memtype)
  ;; test.spectec:1982.1-1984.58
  rule _{C : fuck1context, addrtype : fuck1addrtype, limits : fuck1limits}:
    `%|-%:OK`(C, `%%PAGE`_memtype(addrtype, limits))
    -- Limits_ok: `%|-%:%`(C, limits, (2 ^ ((($size((addrtype : fuck1addrtype <: fuck1numtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))
    -- wf_context: `%`(C)
    -- wf_memtype: `%`(`%%PAGE`_memtype(addrtype, limits))

;; test.spectec:1964.1-1964.99
relation Tabletype_ok: `%|-%:OK`fuck5(fuck1context, fuck1tabletype)
  ;; test.spectec:1986.1-1989.35
  rule _{C : fuck1context, addrtype : fuck1addrtype, limits : fuck1limits, reftype : fuck1reftype}:
    `%|-%:OK`(C, `%%%`_tabletype(addrtype, limits, reftype))
    -- Limits_ok: `%|-%:%`(C, limits, ((((2 ^ $size((addrtype : fuck1addrtype <: fuck1numtype))) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- Reftype_ok: `%|-%:OK`(C, reftype)
    -- wf_context: `%`(C)
    -- wf_tabletype: `%`(`%%%`_tabletype(addrtype, limits, reftype))

;; test.spectec:1965.1-1965.100
relation Externtype_ok: `%|-%:OK`fuck5(fuck1context, fuck1externtype)
  ;; test.spectec:1992.1-1994.35
  rule tag{C : fuck1context, tagtype : fuck1tagtype}:
    `%|-%:OK`(C, TAG_externtype(tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, tagtype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TAG_externtype(tagtype))

  ;; test.spectec:1996.1-1998.41
  rule global{C : fuck1context, globaltype : fuck1globaltype}:
    `%|-%:OK`(C, GLOBAL_externtype(globaltype))
    -- Globaltype_ok: `%|-%:OK`(C, globaltype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(GLOBAL_externtype(globaltype))

  ;; test.spectec:2000.1-2002.35
  rule mem{C : fuck1context, memtype : fuck1memtype}:
    `%|-%:OK`(C, MEM_externtype(memtype))
    -- Memtype_ok: `%|-%:OK`(C, memtype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(MEM_externtype(memtype))

  ;; test.spectec:2004.1-2006.39
  rule table{C : fuck1context, tabletype : fuck1tabletype}:
    `%|-%:OK`(C, TABLE_externtype(tabletype))
    -- Tabletype_ok: `%|-%:OK`(C, tabletype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TABLE_externtype(tabletype))

  ;; test.spectec:2008.1-2011.54
  rule func{C : fuck1context, typeuse : fuck1typeuse, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:OK`(C, FUNC_externtype(typeuse))
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- Expand_use: `%~~_%%`(typeuse, C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(FUNC_externtype(typeuse))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:2152.1-2152.114
relation Instrtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1instrtype, fuck1instrtype)
  ;; test.spectec:2158.1-2163.31
  rule _{C : fuck1context, `t_11*` : fuck6fuck1valtype*, `x_1*` : fuck6fuck1idx*, `t_12*` : fuck6fuck1valtype*, `t_21*` : fuck6fuck1valtype*, `x_2*` : fuck6fuck1idx*, `t_22*` : fuck6fuck1valtype*, `x*` : fuck6fuck1idx*, `t*` : fuck6fuck1valtype*}:
    `%|-%<:%`(C, `%->_%%`_instrtype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_12*{t_12 <- `t_12*`})), `%->_%%`_instrtype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_11*{t_11 <- `t_11*`}))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_12*{t_12 <- `t_12*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`}))
    -- if (x*{x <- `x*`} = $setminus_(syntax fuck1localidx, x_2*{x_2 <- `x_2*`}, x_1*{x_1 <- `x_1*`}))
    -- (if (C.LOCALS_context[x!`%`_uN.0] = `%%`_localtype(SET_init, t)))*{t <- `t*`, x <- `x*`}
    -- wf_context: `%`(C)
    -- (wf_uN: `%%`(32, x))*{x <- `x*`}
    -- (wf_uN: `%%`(32, iter))*{iter <- $setminus_(syntax fuck1localidx, x_2*{x_2 <- `x_2*`}, x_1*{x_1 <- `x_1*`})}
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_12*{t_12 <- `t_12*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- (wf_localtype: `%`(`%%`_localtype(SET_init, t)))*{t <- `t*`}

;; test.spectec:2226.1-2226.110
relation Limits_sub: `%|-%<:%`fuck5(fuck1context, fuck1limits, fuck1limits)
  ;; test.spectec:2234.1-2237.22
  rule max{C : fuck1context, n_1 : fuck1n, m_1 : fuck1m, n_2 : fuck1n, `m_2?` : fuck6fuck1m?}:
    `%|-%<:%`(C, `[%..%]`_limits(`%`_u64(n_1), ?(`%`_u64(m_1))), `[%..%]`_limits(`%`_u64(n_2), `%`_u64(m_2)?{m_2 <- `m_2?`}))
    -- if (n_1 >= n_2)
    -- (if (m_1 <= m_2))?{m_2 <- `m_2?`}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u64(n_1), ?(`%`_u64(m_1))))
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u64(n_2), `%`_u64(m_2)?{m_2 <- `m_2?`}))

  ;; test.spectec:2239.1-2241.19
  rule eps{C : fuck1context, n_1 : fuck1n, n_2 : fuck1n}:
    `%|-%<:%`(C, `[%..%]`_limits(`%`_u64(n_1), ?()), `[%..%]`_limits(`%`_u64(n_2), ?()))
    -- if (n_1 >= n_2)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u64(n_1), ?()))
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u64(n_2), ?()))

;; test.spectec:2227.1-2227.111
relation Tagtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1tagtype, fuck1tagtype)
  ;; test.spectec:2244.1-2247.46
  rule _{C : fuck1context, deftype_1 : fuck1deftype, deftype_2 : fuck1deftype}:
    `%|-%<:%`(C, (deftype_1 : fuck1deftype <: fuck1typeuse), (deftype_2 : fuck1deftype <: fuck1typeuse))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- Deftype_sub: `%|-%<:%`(C, deftype_2, deftype_1)
    -- wf_context: `%`(C)

;; test.spectec:2228.1-2228.114
relation Globaltype_sub: `%|-%<:%`fuck5(fuck1context, fuck1globaltype, fuck1globaltype)
  ;; test.spectec:2249.1-2251.46
  rule const{C : fuck1context, valtype_1 : fuck1valtype, valtype_2 : fuck1valtype}:
    `%|-%<:%`(C, `%%`_globaltype(?(), valtype_1), `%%`_globaltype(?(), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- wf_context: `%`(C)
    -- wf_globaltype: `%`(`%%`_globaltype(?(), valtype_1))
    -- wf_globaltype: `%`(`%%`_globaltype(?(), valtype_2))

  ;; test.spectec:2253.1-2256.46
  rule var{C : fuck1context, valtype_1 : fuck1valtype, valtype_2 : fuck1valtype}:
    `%|-%<:%`(C, `%%`_globaltype(?(MUT_mut), valtype_1), `%%`_globaltype(?(MUT_mut), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- Valtype_sub: `%|-%<:%`(C, valtype_2, valtype_1)
    -- wf_context: `%`(C)
    -- wf_globaltype: `%`(`%%`_globaltype(?(MUT_mut), valtype_1))
    -- wf_globaltype: `%`(`%%`_globaltype(?(MUT_mut), valtype_2))

;; test.spectec:2229.1-2229.111
relation Memtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1memtype, fuck1memtype)
  ;; test.spectec:2258.1-2260.43
  rule _{C : fuck1context, addrtype : fuck1addrtype, limits_1 : fuck1limits, limits_2 : fuck1limits}:
    `%|-%<:%`(C, `%%PAGE`_memtype(addrtype, limits_1), `%%PAGE`_memtype(addrtype, limits_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)
    -- wf_context: `%`(C)
    -- wf_memtype: `%`(`%%PAGE`_memtype(addrtype, limits_1))
    -- wf_memtype: `%`(`%%PAGE`_memtype(addrtype, limits_2))

;; test.spectec:2230.1-2230.113
relation Tabletype_sub: `%|-%<:%`fuck5(fuck1context, fuck1tabletype, fuck1tabletype)
  ;; test.spectec:2262.1-2266.46
  rule _{C : fuck1context, addrtype : fuck1addrtype, limits_1 : fuck1limits, reftype_1 : fuck1reftype, limits_2 : fuck1limits, reftype_2 : fuck1reftype}:
    `%|-%<:%`(C, `%%%`_tabletype(addrtype, limits_1, reftype_1), `%%%`_tabletype(addrtype, limits_2, reftype_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_2, reftype_1)
    -- wf_context: `%`(C)
    -- wf_tabletype: `%`(`%%%`_tabletype(addrtype, limits_1, reftype_1))
    -- wf_tabletype: `%`(`%%%`_tabletype(addrtype, limits_2, reftype_2))

;; test.spectec:2231.1-2231.114
relation Externtype_sub: `%|-%<:%`fuck5(fuck1context, fuck1externtype, fuck1externtype)
  ;; test.spectec:2269.1-2271.46
  rule tag{C : fuck1context, tagtype_1 : fuck1tagtype, tagtype_2 : fuck1tagtype}:
    `%|-%<:%`(C, TAG_externtype(tagtype_1), TAG_externtype(tagtype_2))
    -- Tagtype_sub: `%|-%<:%`(C, tagtype_1, tagtype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TAG_externtype(tagtype_1))
    -- wf_externtype: `%`(TAG_externtype(tagtype_2))

  ;; test.spectec:2273.1-2275.55
  rule global{C : fuck1context, globaltype_1 : fuck1globaltype, globaltype_2 : fuck1globaltype}:
    `%|-%<:%`(C, GLOBAL_externtype(globaltype_1), GLOBAL_externtype(globaltype_2))
    -- Globaltype_sub: `%|-%<:%`(C, globaltype_1, globaltype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(GLOBAL_externtype(globaltype_1))
    -- wf_externtype: `%`(GLOBAL_externtype(globaltype_2))

  ;; test.spectec:2277.1-2279.46
  rule mem{C : fuck1context, memtype_1 : fuck1memtype, memtype_2 : fuck1memtype}:
    `%|-%<:%`(C, MEM_externtype(memtype_1), MEM_externtype(memtype_2))
    -- Memtype_sub: `%|-%<:%`(C, memtype_1, memtype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(MEM_externtype(memtype_1))
    -- wf_externtype: `%`(MEM_externtype(memtype_2))

  ;; test.spectec:2281.1-2283.52
  rule table{C : fuck1context, tabletype_1 : fuck1tabletype, tabletype_2 : fuck1tabletype}:
    `%|-%<:%`(C, TABLE_externtype(tabletype_1), TABLE_externtype(tabletype_2))
    -- Tabletype_sub: `%|-%<:%`(C, tabletype_1, tabletype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TABLE_externtype(tabletype_1))
    -- wf_externtype: `%`(TABLE_externtype(tabletype_2))

  ;; test.spectec:2285.1-2287.46
  rule func{C : fuck1context, deftype_1 : fuck1deftype, deftype_2 : fuck1deftype}:
    `%|-%<:%`(C, FUNC_externtype((deftype_1 : fuck1deftype <: fuck1typeuse)), FUNC_externtype((deftype_2 : fuck1deftype <: fuck1typeuse)))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(FUNC_externtype((deftype_1 : fuck1deftype <: fuck1typeuse)))
    -- wf_externtype: `%`(FUNC_externtype((deftype_2 : fuck1deftype <: fuck1typeuse)))

;; test.spectec:2337.1-2337.121
relation Blocktype_ok: `%|-%:%`fuck5(fuck1context, fuck1blocktype, fuck1instrtype)
  ;; test.spectec:2339.1-2341.38
  rule valtype{C : fuck1context, `valtype?` : fuck6fuck1valtype?}:
    `%|-%:%`(C, _RESULT_blocktype(valtype?{valtype <- `valtype?`}), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(lift(valtype?{valtype <- `valtype?`}))))
    -- (Valtype_ok: `%|-%:OK`(C, valtype))?{valtype <- `valtype?`}
    -- wf_context: `%`(C)
    -- wf_blocktype: `%`(_RESULT_blocktype(valtype?{valtype <- `valtype?`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(lift(valtype?{valtype <- `valtype?`}))))

  ;; test.spectec:2343.1-2345.51
  rule typeidx{C : fuck1context, typeidx : fuck1typeidx, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, _IDX_blocktype(typeidx), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.TYPES_context[typeidx!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_blocktype: `%`(_IDX_blocktype(typeidx))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:2459.1-2459.77
relation Catch_ok: `%|-%:OK`fuck5(fuck1context, fuck1catch)
  ;; test.spectec:2476.1-2479.44
  rule catch{C : fuck1context, x : fuck1idx, l : fuck1labelidx, `t*` : fuck6fuck1valtype*}:
    `%|-%:OK`(C, CATCH_catch(x, l))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_uN.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_uN.0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_catch(x, l))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))

  ;; test.spectec:2481.1-2484.54
  rule catch_ref{C : fuck1context, x : fuck1idx, l : fuck1labelidx, `t*` : fuck6fuck1valtype*}:
    `%|-%:OK`(C, CATCH_REF_catch(x, l))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_uN.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[l!`%`_uN.0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_REF_catch(x, l))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))

  ;; test.spectec:2486.1-2488.45
  rule catch_all{C : fuck1context, l : fuck1labelidx}:
    `%|-%:OK`(C, CATCH_ALL_catch(l))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype([]), C.LABELS_context[l!`%`_uN.0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_ALL_catch(l))

  ;; test.spectec:2490.1-2492.51
  rule catch_all_ref{C : fuck1context, l : fuck1labelidx}:
    `%|-%:OK`(C, CATCH_ALL_REF_catch(l))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype([REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[l!`%`_uN.0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_ALL_REF_catch(l))

;; test.spectec:4441.1-4441.44
def $default_(valtype : fuck1valtype) : fuck6fuck1val?
  ;; test.spectec:4442.1-4442.35
  def $default_{Inn : fuck1addrtype}((Inn : fuck1addrtype <: fuck1valtype)) = ?(CONST_val((Inn : fuck1addrtype <: fuck1numtype), mk_num__0_num_(Inn, `%`_uN(0))))
  ;; test.spectec:4443.1-4443.52
  def $default_{Fnn : fuck1Fnn}((Fnn : fuck1Fnn <: fuck1valtype)) = ?(CONST_val((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, $fzero($size((Fnn : fuck1Fnn <: fuck1numtype))))))
  ;; test.spectec:4444.1-4444.36
  def $default_{Vnn : fuck1vectype}((Vnn : fuck1vectype <: fuck1valtype)) = ?(VCONST_val(Vnn, `%`_vec_(0)))
  ;; test.spectec:4445.1-4445.43
  def $default_{ht : fuck1heaptype}(REF_valtype(?(NULL_null), ht)) = ?(`REF.NULL_ADDR`_val)
  ;; test.spectec:4446.1-4446.28
  def $default_{ht : fuck1heaptype}(REF_valtype(?(), ht)) = ?()

;; test.spectec:4441.6-4441.15
relation default__is_wf: `%%`fuck5(valtype : fuck1valtype, `ret_val?` : fuck6fuck1val?)
  ;; test.spectec:4441.6-4441.15
  rule default__is_wf_0{valtype : fuck1valtype, `ret_val?` : fuck6fuck1val?}:
    `%%`(valtype, `ret_val?`)
    -- wf_valtype: `%`(valtype)
    -- if (`ret_val?` = $default_(valtype))
    -- (wf_val: `%`(ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:2304.1-2305.71
relation Defaultable: `|-%DEFAULTABLE`(fuck1valtype)
  ;; test.spectec:4449.1-4449.62
  rule _{t : fuck1valtype}:
    `|-%DEFAULTABLE`(t)
    -- if ($default_(t) =/= ?())
    -- wf_valtype: `%`(t)
    -- (wf_val: `%`(iter))?{iter <- $default_(t)}

;; test.spectec:2703.1-2703.131
relation Memarg_ok: `|-%:%->%`fuck5(fuck1memarg, fuck1addrtype, fuck1N)
  ;; test.spectec:2705.1-2708.27
  rule _{n : fuck1n, m : fuck1m, at : fuck1addrtype, N : fuck1N}:
    `|-%:%->%`({ALIGN `%`_u32(n), OFFSET `%`_u64(m)}, at, N)
    -- if (((2 ^ n) : nat <:> rat) <= ((N : nat <:> rat) / (8 : nat <:> rat)))
    -- if (m < (2 ^ $size((at : fuck1addrtype <: fuck1numtype))))
    -- wf_memarg: `%`({ALIGN `%`_u32(n), OFFSET `%`_u64(m)})

;; test.spectec:2550.1-2550.111
def $is_packtype(storagetype : fuck1storagetype) : fuck2bool
  ;; test.spectec:2551.1-2551.42
  def $is_packtype{zt : fuck1storagetype}(zt) = (zt =/= ($unpack(zt) : fuck1valtype <: fuck1storagetype))

;; test.spectec:2300.1-2301.96
rec {

;; test.spectec:2300.1-2300.95
relation Instr_ok: `%|-%:%`fuck5(fuck1context, fuck1instr, fuck1instrtype)
  ;; test.spectec:2313.1-2314.24
  rule nop{C : fuck1context}:
    `%|-%:%`(C, NOP_instr, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(NOP_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2316.1-2318.42
  rule unreachable{C : fuck1context, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNREACHABLE_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2320.1-2322.29
  rule drop{C : fuck1context, t : fuck1valtype}:
    `%|-%:%`(C, DROP_instr, `%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(DROP_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))

  ;; test.spectec:2324.1-2326.29
  rule `select-expl`{C : fuck1context, t : fuck1valtype}:
    `%|-%:%`(C, SELECT_instr(?([t])), `%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(SELECT_instr(?([t])))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))

  ;; test.spectec:2328.1-2332.37
  rule `select-impl`{C : fuck1context, t : fuck1valtype, t' : fuck1valtype, numtype : fuck1numtype, vectype : fuck1vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- Valtype_sub: `%|-%<:%`(C, t, t')
    -- if ((t' = (numtype : fuck1numtype <: fuck1valtype)) \/ (t' = (vectype : fuck1vectype <: fuck1valtype)))
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(t')
    -- wf_instr: `%`(SELECT_instr(?()))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))

  ;; test.spectec:2348.1-2351.67
  rule block{C : fuck1context, bt : fuck1blocktype, `instr*` : fuck6fuck1instr*, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `x*` : fuck6fuck1idx*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BLOCK_instr(bt, instr*{instr <- `instr*`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2353.1-2356.67
  rule loop{C : fuck1context, bt : fuck1blocktype, `instr*` : fuck6fuck1instr*, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `x*` : fuck6fuck1idx*}:
    `%|-%:%`(C, LOOP_instr(bt, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_1*{t_1 <- `t_1*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOOP_instr(bt, instr*{instr <- `instr*`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_1*{t_1 <- `t_1*`})], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2358.1-2362.71
  rule if{C : fuck1context, bt : fuck1blocktype, `instr_1*` : fuck6fuck1instr*, `instr_2*` : fuck6fuck1instr*, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `x_1*` : fuck6fuck1idx*, `x_2*` : fuck6fuck1idx*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr_1*{instr_1 <- `instr_1*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2367.1-2370.42
  rule br{C : fuck1context, l : fuck1labelidx, `t_1*` : fuck6fuck1valtype*, `t*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.LABELS_context[l!`%`_uN.0]!`%`_list.0 = t*{t <- `t*`})
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_instr(l))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2372.1-2374.25
  rule br_if{C : fuck1context, l : fuck1labelidx, `t*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_uN.0]!`%`_list.0 = t*{t <- `t*`})
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_IF_instr(l))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t*{t <- `t*`})))

  ;; test.spectec:2376.1-2380.49
  rule br_table{C : fuck1context, `l*` : fuck6fuck1labelidx*, l' : fuck1labelidx, `t_1*` : fuck6fuck1valtype*, `t*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l*{l <- `l*`}, l'), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_uN.0]))*{l <- `l*`}
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l'!`%`_uN.0])
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_TABLE_instr(l*{l <- `l*`}, l'))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2382.1-2385.31
  rule br_on_null{C : fuck1context, l : fuck1labelidx, `t*` : fuck6fuck1valtype*, ht : fuck1heaptype}:
    `%|-%:%`(C, BR_ON_NULL_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), ht)])))
    -- if (C.LABELS_context[l!`%`_uN.0]!`%`_list.0 = t*{t <- `t*`})
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_ON_NULL_instr(l))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), ht)])))

  ;; test.spectec:2387.1-2389.40
  rule br_on_non_null{C : fuck1context, l : fuck1labelidx, `t*` : fuck6fuck1valtype*, ht : fuck1heaptype}:
    `%|-%:%`(C, BR_ON_NON_NULL_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_uN.0] = `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_ON_NON_NULL_instr(l))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`})))

  ;; test.spectec:2391.1-2397.34
  rule br_on_cast{C : fuck1context, l : fuck1labelidx, rt_1 : fuck1reftype, rt_2 : fuck1reftype, `t*` : fuck6fuck1valtype*, rt : fuck1reftype}:
    `%|-%:%`(C, BR_ON_CAST_instr(l, rt_1, rt_2), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [($diffrt(rt_1, rt_2) : fuck1reftype <: fuck1valtype)])))
    -- if (C.LABELS_context[l!`%`_uN.0] = `%`_resulttype(t*{t <- `t*`} ++ [(rt : fuck1reftype <: fuck1valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_instr: `%`(BR_ON_CAST_instr(l, rt_1, rt_2))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [($diffrt(rt_1, rt_2) : fuck1reftype <: fuck1valtype)])))

  ;; test.spectec:2399.1-2405.49
  rule br_on_cast_fail{C : fuck1context, l : fuck1labelidx, rt_1 : fuck1reftype, rt_2 : fuck1reftype, `t*` : fuck6fuck1valtype*, rt : fuck1reftype}:
    `%|-%:%`(C, BR_ON_CAST_FAIL_instr(l, rt_1, rt_2), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [(rt_2 : fuck1reftype <: fuck1valtype)])))
    -- if (C.LABELS_context[l!`%`_uN.0] = `%`_resulttype(t*{t <- `t*`} ++ [(rt : fuck1reftype <: fuck1valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, $diffrt(rt_1, rt_2), rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_reftype: `%`($diffrt(rt_1, rt_2))
    -- wf_instr: `%`(BR_ON_CAST_FAIL_instr(l, rt_1, rt_2))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [(rt_2 : fuck1reftype <: fuck1valtype)])))

  ;; test.spectec:2410.1-2412.45
  rule call{C : fuck1context, x : fuck1idx, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, CALL_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2414.1-2416.45
  rule call_ref{C : fuck1context, x : fuck1idx, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, CALL_REF_instr(_IDX_typeuse(x)), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_REF_instr(_IDX_typeuse(x)))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2418.1-2422.45
  rule call_indirect{C : fuck1context, x : fuck1idx, y : fuck1idx, `t_1*` : fuck6fuck1valtype*, at : fuck1addrtype, `t_2*` : fuck6fuck1valtype*, lim : fuck1limits, rt : fuck1reftype}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, _IDX_typeuse(y)), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPES_context[y!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_INDIRECT_instr(x, _IDX_typeuse(y)))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), FUNC_heaptype))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2424.1-2427.42
  rule return{C : fuck1context, `t_1*` : fuck6fuck1valtype*, `t*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t*{t <- `t*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RETURN_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2430.1-2435.42
  rule return_call{C : fuck1context, x : fuck1idx, `t_3*` : fuck6fuck1valtype*, `t_1*` : fuck6fuck1valtype*, `t_4*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `t'_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, RETURN_CALL_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t'_2))*{t'_2 <- `t'_2*`}
    -- wf_instr: `%`(RETURN_CALL_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2438.1-2443.42
  rule return_call_ref{C : fuck1context, x : fuck1idx, `t_3*` : fuck6fuck1valtype*, `t_1*` : fuck6fuck1valtype*, `t_4*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `t'_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, RETURN_CALL_REF_instr(_IDX_typeuse(x)), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t'_2))*{t'_2 <- `t'_2*`}
    -- wf_instr: `%`(RETURN_CALL_REF_instr(_IDX_typeuse(x)))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2446.1-2454.42
  rule return_call_indirect{C : fuck1context, x : fuck1idx, y : fuck1idx, `t_3*` : fuck6fuck1valtype*, `t_1*` : fuck6fuck1valtype*, at : fuck1addrtype, `t_4*` : fuck6fuck1valtype*, lim : fuck1limits, rt : fuck1reftype, `t_2*` : fuck6fuck1valtype*, `t'_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y)), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPES_context[y!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t'_2))*{t'_2 <- `t'_2*`}
    -- wf_instr: `%`(RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y)))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), FUNC_heaptype))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2461.1-2464.42
  rule throw{C : fuck1context, x : fuck1idx, `t_1*` : fuck6fuck1valtype*, `t*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, THROW_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_uN.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(THROW_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2466.1-2468.42
  rule throw_ref{C : fuck1context, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, THROW_REF_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), EXN_heaptype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(THROW_REF_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), EXN_heaptype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2470.1-2474.34
  rule try_table{C : fuck1context, bt : fuck1blocktype, `catch*` : fuck6fuck1catch*, `instr*` : fuck6fuck1instr*, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `x*` : fuck6fuck1idx*}:
    `%|-%:%`(C, TRY_TABLE_instr(bt, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Catch_ok: `%|-%:OK`(C, catch))*{catch <- `catch*`}
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TRY_TABLE_instr(bt, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2497.1-2499.31
  rule `ref.null`{C : fuck1context, ht : fuck1heaptype}:
    `%|-%:%`(C, `REF.NULL`_instr(ht), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(NULL_null), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.NULL`_instr(ht))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(NULL_null), ht)])))

  ;; test.spectec:2501.1-2504.20
  rule `ref.func`{C : fuck1context, x : fuck1idx, dt : fuck1deftype}:
    `%|-%:%`(C, `REF.FUNC`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), (dt : fuck1deftype <: fuck1heaptype))])))
    -- if (C.FUNCS_context[x!`%`_uN.0] = dt)
    -- if (x <- C.REFS_context)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.FUNC`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), (dt : fuck1deftype <: fuck1heaptype))])))

  ;; test.spectec:2506.1-2507.34
  rule `ref.i31`{C : fuck1context}:
    `%|-%:%`(C, `REF.I31`_instr, `%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), I31_heaptype)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.I31`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), I31_heaptype)])))

  ;; test.spectec:2509.1-2511.31
  rule `ref.is_null`{C : fuck1context, ht : fuck1heaptype}:
    `%|-%:%`(C, `REF.IS_NULL`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([I32_valtype])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.IS_NULL`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2513.1-2515.31
  rule `ref.as_non_null`{C : fuck1context, ht : fuck1heaptype}:
    `%|-%:%`(C, `REF.AS_NON_NULL`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([REF_valtype(?(), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.AS_NON_NULL`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([REF_valtype(?(), ht)])))

  ;; test.spectec:2517.1-2518.51
  rule `ref.eq`{C : fuck1context}:
    `%|-%:%`(C, `REF.EQ`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), EQ_heaptype) REF_valtype(?(NULL_null), EQ_heaptype)]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.EQ`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), EQ_heaptype) REF_valtype(?(NULL_null), EQ_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2520.1-2524.33
  rule `ref.test`{C : fuck1context, rt : fuck1reftype, rt' : fuck1reftype}:
    `%|-%:%`(C, `REF.TEST`_instr(rt), `%->_%%`_instrtype(`%`_resulttype([(rt' : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype([I32_valtype])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.TEST`_instr(rt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(rt' : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2526.1-2530.33
  rule `ref.cast`{C : fuck1context, rt : fuck1reftype, rt' : fuck1reftype}:
    `%|-%:%`(C, `REF.CAST`_instr(rt), `%->_%%`_instrtype(`%`_resulttype([(rt' : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype([(rt : fuck1reftype <: fuck1valtype)])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.CAST`_instr(rt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(rt' : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype([(rt : fuck1reftype <: fuck1valtype)])))

  ;; test.spectec:2535.1-2536.42
  rule `i31.get`{C : fuck1context, sx : fuck1sx}:
    `%|-%:%`(C, `I31.GET`_instr(sx), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), I31_heaptype)]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`I31.GET`_instr(sx))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), I31_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2541.1-2543.45
  rule `struct.new`{C : fuck1context, x : fuck1idx, `zt*` : fuck6fuck1storagetype*, `mut?*` : fuck6fuck6fuck1mut?*}:
    `%|-%:%`(C, `STRUCT.NEW`_instr(x), `%->_%%`_instrtype(`%`_resulttype($unpack(zt)*{zt <- `zt*`}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`STRUCT.NEW`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype($unpack(zt)*{zt <- `zt*`}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))

  ;; test.spectec:2545.1-2548.48
  rule `struct.new_default`{C : fuck1context, x : fuck1idx, `mut?*` : fuck6fuck6fuck1mut?*, `zt*` : fuck6fuck1storagetype*}:
    `%|-%:%`(C, `STRUCT.NEW_DEFAULT`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- (Defaultable: `|-%DEFAULTABLE`($unpack(zt)))*{zt <- `zt*`}
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`($unpack(zt)))*{zt <- `zt*`}
    -- wf_instr: `%`(`STRUCT.NEW_DEFAULT`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))

  ;; test.spectec:2553.1-2557.41
  rule `struct.get`{C : fuck1context, `sx?` : fuck6fuck1sx?, x : fuck1idx, i : fuck1fieldidx, zt : fuck1storagetype, `ft*` : fuck6fuck1fieldtype*, `mut?` : fuck6fuck1mut?}:
    `%|-%:%`(C, `STRUCT.GET`_instr(sx?{sx <- `sx?`}, x, i), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype([$unpack(zt)])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i!`%`_uN.0] = `%%`_fieldtype(mut?{mut <- `mut?`}, zt))
    -- if ((sx?{sx <- `sx?`} =/= ?()) <=> $is_packtype(zt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`STRUCT.GET`_instr(sx?{sx <- `sx?`}, x, i))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype([$unpack(zt)])))
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- wf_fieldtype: `%`(`%%`_fieldtype(mut?{mut <- `mut?`}, zt))

  ;; test.spectec:2559.1-2562.24
  rule `struct.set`{C : fuck1context, x : fuck1idx, i : fuck1fieldidx, zt : fuck1storagetype, `ft*` : fuck6fuck1fieldtype*}:
    `%|-%:%`(C, `STRUCT.SET`_instr(x, i), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) $unpack(zt)]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i!`%`_uN.0] = `%%`_fieldtype(?(MUT_mut), zt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`STRUCT.SET`_instr(x, i))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) $unpack(zt)]), [], `%`_resulttype([])))
    -- wf_comptype: `%`(STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- wf_fieldtype: `%`(`%%`_fieldtype(?(MUT_mut), zt))

  ;; test.spectec:2567.1-2569.43
  rule `array.new`{C : fuck1context, x : fuck1idx, zt : fuck1storagetype, `mut?` : fuck6fuck1mut?}:
    `%|-%:%`(C, `ARRAY.NEW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([$unpack(zt) I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.NEW`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([$unpack(zt) I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2571.1-2574.45
  rule `array.new_default`{C : fuck1context, x : fuck1idx, `mut?` : fuck6fuck1mut?, zt : fuck1storagetype}:
    `%|-%:%`(C, `ARRAY.NEW_DEFAULT`_instr(x), `%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- Defaultable: `|-%DEFAULTABLE`($unpack(zt))
    -- wf_context: `%`(C)
    -- wf_valtype: `%`($unpack(zt))
    -- wf_instr: `%`(`ARRAY.NEW_DEFAULT`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2576.1-2578.43
  rule `array.new_fixed`{C : fuck1context, x : fuck1idx, n : fuck1n, zt : fuck1storagetype, `mut?` : fuck6fuck1mut?}:
    `%|-%:%`(C, `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)), `%->_%%`_instrtype(`%`_resulttype($unpack(zt)^n{}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype($unpack(zt)^n{}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2580.1-2583.40
  rule `array.new_elem`{C : fuck1context, x : fuck1idx, y : fuck1idx, `mut?` : fuck6fuck1mut?, rt : fuck1reftype}:
    `%|-%:%`(C, `ARRAY.NEW_ELEM`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, (rt : fuck1reftype <: fuck1storagetype))))
    -- Reftype_sub: `%|-%<:%`(C, C.ELEMS_context[y!`%`_uN.0], rt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.NEW_ELEM`_instr(x, y))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, (rt : fuck1reftype <: fuck1storagetype))))

  ;; test.spectec:2585.1-2589.24
  rule `array.new_data`{C : fuck1context, x : fuck1idx, y : fuck1idx, `mut?` : fuck6fuck1mut?, zt : fuck1storagetype, numtype : fuck1numtype, vectype : fuck1vectype}:
    `%|-%:%`(C, `ARRAY.NEW_DATA`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if (($unpack(zt) = (numtype : fuck1numtype <: fuck1valtype)) \/ ($unpack(zt) = (vectype : fuck1vectype <: fuck1valtype)))
    -- if (C.DATAS_context[y!`%`_uN.0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`($unpack(zt))
    -- wf_instr: `%`(`ARRAY.NEW_DATA`_instr(x, y))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2591.1-2594.41
  rule `array.get`{C : fuck1context, `sx?` : fuck6fuck1sx?, x : fuck1idx, zt : fuck1storagetype, `mut?` : fuck6fuck1mut?}:
    `%|-%:%`(C, `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype]), [], `%`_resulttype([$unpack(zt)])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ((sx?{sx <- `sx?`} =/= ?()) <=> $is_packtype(zt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.GET`_instr(sx?{sx <- `sx?`}, x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype]), [], `%`_resulttype([$unpack(zt)])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2596.1-2598.42
  rule `array.set`{C : fuck1context, x : fuck1idx, zt : fuck1storagetype}:
    `%|-%:%`(C, `ARRAY.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt)]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.SET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt)]), [], `%`_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2600.1-2601.43
  rule `array.len`{C : fuck1context}:
    `%|-%:%`(C, `ARRAY.LEN`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ARRAY_heaptype)]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.LEN`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ARRAY_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2603.1-2605.42
  rule `array.fill`{C : fuck1context, x : fuck1idx, zt : fuck1storagetype}:
    `%|-%:%`(C, `ARRAY.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt) I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.FILL`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt) I32_valtype]), [], `%`_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2607.1-2611.40
  rule `array.copy`{C : fuck1context, x_1 : fuck1idx, x_2 : fuck1idx, zt_1 : fuck1storagetype, `mut?` : fuck6fuck1mut?, zt_2 : fuck1storagetype}:
    `%|-%:%`(C, `ARRAY.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x_1)) I32_valtype REF_valtype(?(NULL_null), _IDX_heaptype(x_2)) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x_1!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt_1)))
    -- Expand: `%~~%`(C.TYPES_context[x_2!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt_2)))
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.COPY`_instr(x_1, x_2))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x_1)) I32_valtype REF_valtype(?(NULL_null), _IDX_heaptype(x_2)) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt_1)))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt_2)))

  ;; test.spectec:2613.1-2616.44
  rule `array.init_elem`{C : fuck1context, x : fuck1idx, y : fuck1idx, zt : fuck1storagetype}:
    `%|-%:%`(C, `ARRAY.INIT_ELEM`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- Storagetype_sub: `%|-%<:%`(C, (C.ELEMS_context[y!`%`_uN.0] : fuck1reftype <: fuck1storagetype), zt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.INIT_ELEM`_instr(x, y))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2618.1-2622.24
  rule `array.init_data`{C : fuck1context, x : fuck1idx, y : fuck1idx, zt : fuck1storagetype, numtype : fuck1numtype, vectype : fuck1vectype}:
    `%|-%:%`(C, `ARRAY.INIT_DATA`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- if (($unpack(zt) = (numtype : fuck1numtype <: fuck1valtype)) \/ ($unpack(zt) = (vectype : fuck1vectype <: fuck1valtype)))
    -- if (C.DATAS_context[y!`%`_uN.0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`($unpack(zt))
    -- wf_instr: `%`(`ARRAY.INIT_DATA`_instr(x, y))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2627.1-2629.26
  rule `extern.convert_any`{C : fuck1context, `null_1?` : fuck6fuck1null?, `null_2?` : fuck6fuck1null?}:
    `%|-%:%`(C, `EXTERN.CONVERT_ANY`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, ANY_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, EXTERN_heaptype)])))
    -- if (null_1?{null_1 <- `null_1?`} = null_2?{null_2 <- `null_2?`})
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`EXTERN.CONVERT_ANY`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, ANY_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, EXTERN_heaptype)])))

  ;; test.spectec:2631.1-2633.26
  rule `any.convert_extern`{C : fuck1context, `null_1?` : fuck6fuck1null?, `null_2?` : fuck6fuck1null?}:
    `%|-%:%`(C, `ANY.CONVERT_EXTERN`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, EXTERN_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, ANY_heaptype)])))
    -- if (null_1?{null_1 <- `null_1?`} = null_2?{null_2 <- `null_2?`})
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ANY.CONVERT_EXTERN`_instr)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, EXTERN_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, ANY_heaptype)])))

  ;; test.spectec:2638.1-2640.28
  rule `local.get`{C : fuck1context, x : fuck1idx, t : fuck1valtype}:
    `%|-%:%`(C, `LOCAL.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_uN.0] = `%%`_localtype(SET_init, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`LOCAL.GET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- wf_localtype: `%`(`%%`_localtype(SET_init, t))

  ;; test.spectec:2642.1-2644.29
  rule `local.set`{C : fuck1context, x : fuck1idx, t : fuck1valtype, init : fuck1init}:
    `%|-%:%`(C, `LOCAL.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([])))
    -- if (C.LOCALS_context[x!`%`_uN.0] = `%%`_localtype(init, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`LOCAL.SET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([])))
    -- wf_localtype: `%`(`%%`_localtype(init, t))

  ;; test.spectec:2646.1-2648.29
  rule `local.tee`{C : fuck1context, x : fuck1idx, t : fuck1valtype, init : fuck1init}:
    `%|-%:%`(C, `LOCAL.TEE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_uN.0] = `%%`_localtype(init, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`LOCAL.TEE`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([t])))
    -- wf_localtype: `%`(`%%`_localtype(init, t))

  ;; test.spectec:2653.1-2655.30
  rule `global.get`{C : fuck1context, x : fuck1idx, t : fuck1valtype, `mut?` : fuck6fuck1mut?}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = `%%`_globaltype(mut?{mut <- `mut?`}, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`GLOBAL.GET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- wf_globaltype: `%`(`%%`_globaltype(mut?{mut <- `mut?`}, t))

  ;; test.spectec:2657.1-2659.29
  rule `global.set`{C : fuck1context, x : fuck1idx, t : fuck1valtype}:
    `%|-%:%`(C, `GLOBAL.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = `%%`_globaltype(?(MUT_mut), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`GLOBAL.SET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- wf_globaltype: `%`(`%%`_globaltype(?(MUT_mut), t))

  ;; test.spectec:2664.1-2666.32
  rule `table.get`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, rt : fuck1reftype, lim : fuck1limits}:
    `%|-%:%`(C, `TABLE.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(rt : fuck1reftype <: fuck1valtype)])))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`TABLE.GET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(rt : fuck1reftype <: fuck1valtype)])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2668.1-2670.32
  rule `table.set`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, rt : fuck1reftype, lim : fuck1limits}:
    `%|-%:%`(C, `TABLE.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (rt : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`TABLE.SET`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (rt : fuck1reftype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2672.1-2674.32
  rule `table.size`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, lim : fuck1limits, rt : fuck1reftype}:
    `%|-%:%`(C, `TABLE.SIZE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`TABLE.SIZE`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2676.1-2678.32
  rule `table.grow`{C : fuck1context, x : fuck1idx, rt : fuck1reftype, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, `TABLE.GROW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(rt : fuck1reftype <: fuck1valtype) (at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`TABLE.GROW`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(rt : fuck1reftype <: fuck1valtype) (at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2680.1-2682.32
  rule `table.fill`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, rt : fuck1reftype, lim : fuck1limits}:
    `%|-%:%`(C, `TABLE.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (rt : fuck1reftype <: fuck1valtype) (at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`TABLE.FILL`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (rt : fuck1reftype <: fuck1valtype) (at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2684.1-2688.36
  rule `table.copy`{C : fuck1context, x_1 : fuck1idx, x_2 : fuck1idx, at_1 : fuck1addrtype, at_2 : fuck1addrtype, lim_1 : fuck1limits, rt_1 : fuck1reftype, lim_2 : fuck1limits, rt_2 : fuck1reftype}:
    `%|-%:%`(C, `TABLE.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([(at_1 : fuck1addrtype <: fuck1valtype) (at_2 : fuck1addrtype <: fuck1valtype) ($minat(at_1, at_2) : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x_1!`%`_uN.0] = `%%%`_tabletype(at_1, lim_1, rt_1))
    -- if (C.TABLES_context[x_2!`%`_uN.0] = `%%%`_tabletype(at_2, lim_2, rt_2))
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`TABLE.COPY`_instr(x_1, x_2))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at_1 : fuck1addrtype <: fuck1valtype) (at_2 : fuck1addrtype <: fuck1valtype) ($minat(at_1, at_2) : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at_1, lim_1, rt_1))
    -- wf_tabletype: `%`(`%%%`_tabletype(at_2, lim_2, rt_2))

  ;; test.spectec:2690.1-2694.36
  rule `table.init`{C : fuck1context, x : fuck1idx, y : fuck1idx, at : fuck1addrtype, lim : fuck1limits, rt_1 : fuck1reftype, rt_2 : fuck1reftype}:
    `%|-%:%`(C, `TABLE.INIT`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt_1))
    -- if (C.ELEMS_context[y!`%`_uN.0] = rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt_2)
    -- wf_instr: `%`(`TABLE.INIT`_instr(x, y))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt_1))

  ;; test.spectec:2696.1-2698.24
  rule `elem.drop`{C : fuck1context, x : fuck1idx, rt : fuck1reftype}:
    `%|-%:%`(C, `ELEM.DROP`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- if (C.ELEMS_context[x!`%`_uN.0] = rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_instr: `%`(`ELEM.DROP`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2711.1-2713.32
  rule `memory.size`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, `MEMORY.SIZE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`MEMORY.SIZE`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2715.1-2717.32
  rule `memory.grow`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, `MEMORY.GROW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`MEMORY.GROW`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(at : fuck1addrtype <: fuck1valtype)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2719.1-2721.32
  rule `memory.fill`{C : fuck1context, x : fuck1idx, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, `MEMORY.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) I32_valtype (at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`MEMORY.FILL`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) I32_valtype (at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2723.1-2726.38
  rule `memory.copy`{C : fuck1context, x_1 : fuck1idx, x_2 : fuck1idx, at_1 : fuck1addrtype, at_2 : fuck1addrtype, lim_1 : fuck1limits, lim_2 : fuck1limits}:
    `%|-%:%`(C, `MEMORY.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([(at_1 : fuck1addrtype <: fuck1valtype) (at_2 : fuck1addrtype <: fuck1valtype) ($minat(at_1, at_2) : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x_1!`%`_uN.0] = `%%PAGE`_memtype(at_1, lim_1))
    -- if (C.MEMS_context[x_2!`%`_uN.0] = `%%PAGE`_memtype(at_2, lim_2))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`MEMORY.COPY`_instr(x_1, x_2))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at_1 : fuck1addrtype <: fuck1valtype) (at_2 : fuck1addrtype <: fuck1valtype) ($minat(at_1, at_2) : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at_1, lim_1))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at_2, lim_2))

  ;; test.spectec:2728.1-2731.24
  rule `memory.init`{C : fuck1context, x : fuck1idx, y : fuck1idx, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, `MEMORY.INIT`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- if (C.DATAS_context[y!`%`_uN.0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`MEMORY.INIT`_instr(x, y))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2733.1-2735.24
  rule `data.drop`{C : fuck1context, x : fuck1idx}:
    `%|-%:%`(C, `DATA.DROP`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- if (C.DATAS_context[x!`%`_uN.0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`DATA.DROP`_instr(x))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2746.1-2749.44
  rule `load-val`{C : fuck1context, nt : fuck1numtype, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, LOAD_instr(nt, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $size(nt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOAD_instr(nt, ?(), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2751.1-2754.36
  rule `load-pack`{C : fuck1context, Inn : fuck1Inn, M : fuck1M, sx : fuck1sx, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, LOAD_instr((Inn : fuck1addrtype <: fuck1numtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(M), sx))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(Inn : fuck1addrtype <: fuck1valtype)])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, M)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOAD_instr((Inn : fuck1addrtype <: fuck1numtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(M), sx))), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([(Inn : fuck1addrtype <: fuck1valtype)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2765.1-2768.44
  rule `store-val`{C : fuck1context, nt : fuck1numtype, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, STORE_instr(nt, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $size(nt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STORE_instr(nt, ?(), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2770.1-2773.36
  rule `store-pack`{C : fuck1context, Inn : fuck1Inn, M : fuck1M, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, STORE_instr((Inn : fuck1addrtype <: fuck1numtype), ?(mk_storeop__0_storeop_(Inn, `%`_storeop_Inn(`%`_sz(M)))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (Inn : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, M)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STORE_instr((Inn : fuck1addrtype <: fuck1numtype), ?(mk_storeop__0_storeop_(Inn, `%`_storeop_Inn(`%`_sz(M)))), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) (Inn : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2775.1-2778.47
  rule `vload-val`{C : fuck1context, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $vsize(V128_vectype))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2780.1-2783.41
  rule `vload-pack`{C : fuck1context, M : fuck1M, N : fuck1N, sx : fuck1sx, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, (M * N))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2785.1-2788.36
  rule `vload-splat`{C : fuck1context, N : fuck1N, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2790.1-2793.36
  rule `vload-zero`{C : fuck1context, N : fuck1N, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2795.1-2799.21
  rule vload_lane{C : fuck1context, N : fuck1N, x : fuck1idx, memarg : fuck1memarg, i : fuck1laneidx, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VLOAD_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- if ((i!`%`_uN.0 : nat <:> rat) < ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2801.1-2804.47
  rule vstore{C : fuck1context, x : fuck1idx, memarg : fuck1memarg, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VSTORE_instr(V128_vectype, x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) V128_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $vsize(V128_vectype))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSTORE_instr(V128_vectype, x, memarg))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) V128_valtype]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2806.1-2810.21
  rule vstore_lane{C : fuck1context, N : fuck1N, x : fuck1idx, memarg : fuck1memarg, i : fuck1laneidx, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, VSTORE_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i), `%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) V128_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- if ((i!`%`_uN.0 : nat <:> rat) < ((128 : nat <:> rat) / (N : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSTORE_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(at : fuck1addrtype <: fuck1valtype) V128_valtype]), [], `%`_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2815.1-2816.33
  rule const{C : fuck1context, nt : fuck1numtype, c_nt : fuck1num_}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(nt, c_nt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))

  ;; test.spectec:2818.1-2819.34
  rule unop{C : fuck1context, nt : fuck1numtype, unop_nt : fuck1unop_}:
    `%|-%:%`(C, UNOP_instr(nt, unop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNOP_instr(nt, unop_nt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))

  ;; test.spectec:2821.1-2822.39
  rule binop{C : fuck1context, nt : fuck1numtype, binop_nt : fuck1binop_}:
    `%|-%:%`(C, BINOP_instr(nt, binop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype) (nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr(nt, binop_nt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype) (nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([(nt : fuck1numtype <: fuck1valtype)])))

  ;; test.spectec:2824.1-2825.39
  rule testop{C : fuck1context, nt : fuck1numtype, testop_nt : fuck1testop_}:
    `%|-%:%`(C, TESTOP_instr(nt, testop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TESTOP_instr(nt, testop_nt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2827.1-2828.40
  rule relop{C : fuck1context, nt : fuck1numtype, relop_nt : fuck1relop_}:
    `%|-%:%`(C, RELOP_instr(nt, relop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype) (nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RELOP_instr(nt, relop_nt))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(nt : fuck1numtype <: fuck1valtype) (nt : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2830.1-2831.44
  rule cvtop{C : fuck1context, nt_1 : fuck1numtype, nt_2 : fuck1numtype, cvtop : fuck1cvtop__}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, cvtop), `%->_%%`_instrtype(`%`_resulttype([(nt_2 : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([(nt_1 : fuck1numtype <: fuck1valtype)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, cvtop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([(nt_2 : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([(nt_1 : fuck1numtype <: fuck1valtype)])))

  ;; test.spectec:2836.1-2837.35
  rule vconst{C : fuck1context, c : fuck1vec_}:
    `%|-%:%`(C, VCONST_instr(V128_vectype, c), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VCONST_instr(V128_vectype, c))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2839.1-2840.41
  rule vvunop{C : fuck1context, vvunop : fuck1vvunop}:
    `%|-%:%`(C, VVUNOP_instr(V128_vectype, vvunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVUNOP_instr(V128_vectype, vvunop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2842.1-2843.48
  rule vvbinop{C : fuck1context, vvbinop : fuck1vvbinop}:
    `%|-%:%`(C, VVBINOP_instr(V128_vectype, vvbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVBINOP_instr(V128_vectype, vvbinop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2845.1-2846.55
  rule vvternop{C : fuck1context, vvternop : fuck1vvternop}:
    `%|-%:%`(C, VVTERNOP_instr(V128_vectype, vvternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVTERNOP_instr(V128_vectype, vvternop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2848.1-2849.44
  rule vvtestop{C : fuck1context, vvtestop : fuck1vvtestop}:
    `%|-%:%`(C, VVTESTOP_instr(V128_vectype, vvtestop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVTESTOP_instr(V128_vectype, vvtestop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2851.1-2852.37
  rule vunop{C : fuck1context, sh : fuck1shape, vunop : fuck1vunop_}:
    `%|-%:%`(C, VUNOP_instr(sh, vunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VUNOP_instr(sh, vunop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2854.1-2855.44
  rule vbinop{C : fuck1context, sh : fuck1shape, vbinop : fuck1vbinop_}:
    `%|-%:%`(C, VBINOP_instr(sh, vbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VBINOP_instr(sh, vbinop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2857.1-2858.51
  rule vternop{C : fuck1context, sh : fuck1shape, vternop : fuck1vternop_}:
    `%|-%:%`(C, VTERNOP_instr(sh, vternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VTERNOP_instr(sh, vternop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2860.1-2861.40
  rule vtestop{C : fuck1context, sh : fuck1shape, vtestop : fuck1vtestop_}:
    `%|-%:%`(C, VTESTOP_instr(sh, vtestop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VTESTOP_instr(sh, vtestop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2863.1-2864.44
  rule vrelop{C : fuck1context, sh : fuck1shape, vrelop : fuck1vrelop_}:
    `%|-%:%`(C, VRELOP_instr(sh, vrelop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VRELOP_instr(sh, vrelop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2866.1-2867.47
  rule vshiftop{C : fuck1context, sh : fuck1ishape, vshiftop : fuck1vshiftop_}:
    `%|-%:%`(C, VSHIFTOP_instr(sh, vshiftop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype I32_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSHIFTOP_instr(sh, vshiftop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype I32_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2869.1-2870.33
  rule vbitmask{C : fuck1context, sh : fuck1ishape}:
    `%|-%:%`(C, VBITMASK_instr(sh), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VBITMASK_instr(sh))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2872.1-2873.50
  rule vswizzlop{C : fuck1context, sh : fuck1bshape, vswizzlop : fuck1vswizzlop_}:
    `%|-%:%`(C, VSWIZZLOP_instr(sh, vswizzlop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSWIZZLOP_instr(sh, vswizzlop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2875.1-2877.29
  rule vshuffle{C : fuck1context, sh : fuck1bshape, `i*` : fuck6fuck1laneidx*}:
    `%|-%:%`(C, VSHUFFLE_instr(sh, i*{i <- `i*`}), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- (if (i!`%`_uN.0 < (2 * $dim(sh!`%`_bshape.0)!`%`_dim.0)))*{i <- `i*`}
    -- wf_context: `%`(C)
    -- wf_dim: `%`($dim(sh!`%`_bshape.0))
    -- wf_instr: `%`(VSHUFFLE_instr(sh, i*{i <- `i*`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2879.1-2880.44
  rule vsplat{C : fuck1context, sh : fuck1shape}:
    `%|-%:%`(C, VSPLAT_instr(sh), `%->_%%`_instrtype(`%`_resulttype([($unpackshape(sh) : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSPLAT_instr(sh))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([($unpackshape(sh) : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2882.1-2884.21
  rule vextract_lane{C : fuck1context, sh : fuck1shape, `sx?` : fuck6fuck1sx?, i : fuck1laneidx}:
    `%|-%:%`(C, VEXTRACT_LANE_instr(sh, sx?{sx <- `sx?`}, i), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([($unpackshape(sh) : fuck1numtype <: fuck1valtype)])))
    -- if (i!`%`_uN.0 < $dim(sh)!`%`_dim.0)
    -- wf_context: `%`(C)
    -- wf_dim: `%`($dim(sh))
    -- wf_instr: `%`(VEXTRACT_LANE_instr(sh, sx?{sx <- `sx?`}, i))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([($unpackshape(sh) : fuck1numtype <: fuck1valtype)])))

  ;; test.spectec:2886.1-2888.21
  rule vreplace_lane{C : fuck1context, sh : fuck1shape, i : fuck1laneidx}:
    `%|-%:%`(C, VREPLACE_LANE_instr(sh, i), `%->_%%`_instrtype(`%`_resulttype([V128_valtype ($unpackshape(sh) : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (i!`%`_uN.0 < $dim(sh)!`%`_dim.0)
    -- wf_context: `%`(C)
    -- wf_dim: `%`($dim(sh))
    -- wf_instr: `%`(VREPLACE_LANE_instr(sh, i))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype ($unpackshape(sh) : fuck1numtype <: fuck1valtype)]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2890.1-2891.50
  rule vextunop{C : fuck1context, sh_1 : fuck1ishape, sh_2 : fuck1ishape, vextunop : fuck1vextunop__}:
    `%|-%:%`(C, VEXTUNOP_instr(sh_1, sh_2, vextunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VEXTUNOP_instr(sh_1, sh_2, vextunop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2893.1-2894.57
  rule vextbinop{C : fuck1context, sh_1 : fuck1ishape, sh_2 : fuck1ishape, vextbinop : fuck1vextbinop__}:
    `%|-%:%`(C, VEXTBINOP_instr(sh_1, sh_2, vextbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VEXTBINOP_instr(sh_1, sh_2, vextbinop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2896.1-2897.64
  rule vextternop{C : fuck1context, sh_1 : fuck1ishape, sh_2 : fuck1ishape, vextternop : fuck1vextternop__}:
    `%|-%:%`(C, VEXTTERNOP_instr(sh_1, sh_2, vextternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VEXTTERNOP_instr(sh_1, sh_2, vextternop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2899.1-2900.48
  rule vnarrow{C : fuck1context, sh_1 : fuck1ishape, sh_2 : fuck1ishape, sx : fuck1sx}:
    `%|-%:%`(C, VNARROW_instr(sh_1, sh_2, sx), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VNARROW_instr(sh_1, sh_2, sx))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2902.1-2903.46
  rule vcvtop{C : fuck1context, sh_1 : fuck1shape, sh_2 : fuck1shape, vcvtop : fuck1vcvtop__}:
    `%|-%:%`(C, VCVTOP_instr(sh_1, sh_2, vcvtop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VCVTOP_instr(sh_1, sh_2, vcvtop))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

;; test.spectec:2301.1-2301.96
relation Instrs_ok: `%|-%:%`fuck5(fuck1context, fuck6fuck1instr*, fuck1instrtype)
  ;; test.spectec:2908.1-2909.24
  rule empty{C : fuck1context}:
    `%|-%:%`(C, [], `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- wf_context: `%`(C)
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2912.1-2916.82
  rule seq{C : fuck1context, instr_1 : fuck1instr, `instr_2*` : fuck6fuck1instr*, `t_1*` : fuck6fuck1valtype*, `x_1*` : fuck6fuck1idx*, `x_2*` : fuck6fuck1idx*, `t_3*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `init*` : fuck6fuck1init*, `t*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, [instr_1] ++ instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`} ++ x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (if (C.LOCALS_context[x_1!`%`_uN.0] = `%%`_localtype(init, t)))*{init <- `init*`, t <- `t*`, x_1 <- `x_1*`}
    -- Instrs_ok: `%|-%:%`($with_locals(C, x_1*{x_1 <- `x_1*`}, `%%`_localtype(SET_init, t)*{t <- `t*`}), instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(instr_1)
    -- (wf_instr: `%`(instr_2))*{instr_2 <- `instr_2*`}
    -- wf_context: `%`($with_locals(C, x_1*{x_1 <- `x_1*`}, `%%`_localtype(SET_init, t)*{t <- `t*`}))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`} ++ x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (wf_localtype: `%`(`%%`_localtype(init, t)))*{init <- `init*`, t <- `t*`}
    -- (wf_localtype: `%`(`%%`_localtype(SET_init, t)))*{t <- `t*`}
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))

  ;; test.spectec:2918.1-2922.33
  rule sub{C : fuck1context, `instr*` : fuck6fuck1instr*, it' : fuck1instrtype, it : fuck1instrtype}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, it')
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, it)
    -- Instrtype_sub: `%|-%<:%`(C, it, it')
    -- Instrtype_ok: `%|-%:OK`(C, it')
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- wf_instrtype: `%`(it')
    -- wf_instrtype: `%`(it)

  ;; test.spectec:2925.1-2928.33
  rule frame{C : fuck1context, `instr*` : fuck6fuck1instr*, `t*` : fuck6fuck1valtype*, `t_1*` : fuck6fuck1valtype*, `x*` : fuck6fuck1idx*, `t_2*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
}

;; test.spectec:2302.1-2302.94
relation Expr_ok: `%|-%:%`fuck5(fuck1context, fuck1expr, fuck1resulttype)
  ;; test.spectec:2933.1-2935.40
  rule _{C : fuck1context, `instr*` : fuck6fuck1instr*, `t*` : fuck6fuck1valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%`_resulttype(t*{t <- `t*`}))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t*{t <- `t*`})))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- wf_instrtype: `%`(`%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t*{t <- `t*`})))

;; test.spectec:2307.1-2308.75
relation Nondefaultable: `|-%NONDEFAULTABLE`(fuck1valtype)
  ;; test.spectec:4452.1-4452.66
  rule _{t : fuck1valtype}:
    `|-%NONDEFAULTABLE`(t)
    -- if ($default_(t) = ?())
    -- wf_valtype: `%`(t)
    -- (wf_val: `%`(iter))?{iter <- $default_(t)}

;; test.spectec:2940.1-2940.104
relation Instr_const: `%|-%CONST`fuck5(fuck1context, fuck1instr)
  ;; test.spectec:2944.1-2945.29
  rule const{C : fuck1context, nt : fuck1numtype, c_nt : fuck1num_}:
    `%|-%CONST`(C, CONST_instr(nt, c_nt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(nt, c_nt))

  ;; test.spectec:2947.1-2948.30
  rule vconst{C : fuck1context, vt : fuck1vectype, c_vt : fuck1vec_}:
    `%|-%CONST`(C, VCONST_instr(vt, c_vt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VCONST_instr(vt, c_vt))

  ;; test.spectec:2950.1-2951.27
  rule `ref.null`{C : fuck1context, ht : fuck1heaptype}:
    `%|-%CONST`(C, `REF.NULL`_instr(ht))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.NULL`_instr(ht))

  ;; test.spectec:2953.1-2954.23
  rule `ref.i31`{C : fuck1context}:
    `%|-%CONST`(C, `REF.I31`_instr)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.I31`_instr)

  ;; test.spectec:2956.1-2957.26
  rule `ref.func`{C : fuck1context, x : fuck1idx}:
    `%|-%CONST`(C, `REF.FUNC`_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`REF.FUNC`_instr(x))

  ;; test.spectec:2959.1-2960.28
  rule `struct.new`{C : fuck1context, x : fuck1idx}:
    `%|-%CONST`(C, `STRUCT.NEW`_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`STRUCT.NEW`_instr(x))

  ;; test.spectec:2962.1-2963.36
  rule `struct.new_default`{C : fuck1context, x : fuck1idx}:
    `%|-%CONST`(C, `STRUCT.NEW_DEFAULT`_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`STRUCT.NEW_DEFAULT`_instr(x))

  ;; test.spectec:2965.1-2966.27
  rule `array.new`{C : fuck1context, x : fuck1idx}:
    `%|-%CONST`(C, `ARRAY.NEW`_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.NEW`_instr(x))

  ;; test.spectec:2968.1-2969.35
  rule `array.new_default`{C : fuck1context, x : fuck1idx}:
    `%|-%CONST`(C, `ARRAY.NEW_DEFAULT`_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.NEW_DEFAULT`_instr(x))

  ;; test.spectec:2971.1-2972.35
  rule `array.new_fixed`{C : fuck1context, x : fuck1idx, n : fuck1n}:
    `%|-%CONST`(C, `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)))

  ;; test.spectec:2974.1-2975.34
  rule `any.convert_extern`{C : fuck1context}:
    `%|-%CONST`(C, `ANY.CONVERT_EXTERN`_instr)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`ANY.CONVERT_EXTERN`_instr)

  ;; test.spectec:2977.1-2978.34
  rule `extern.convert_any`{C : fuck1context}:
    `%|-%CONST`(C, `EXTERN.CONVERT_ANY`_instr)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`EXTERN.CONVERT_ANY`_instr)

  ;; test.spectec:2980.1-2982.25
  rule `global.get`{C : fuck1context, x : fuck1idx, t : fuck1valtype}:
    `%|-%CONST`(C, `GLOBAL.GET`_instr(x))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = `%%`_globaltype(?(), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`GLOBAL.GET`_instr(x))
    -- wf_globaltype: `%`(`%%`_globaltype(?(), t))

  ;; test.spectec:2984.1-2987.29
  rule binop{C : fuck1context, Inn : fuck1Inn, binop : fuck1binop_}:
    `%|-%CONST`(C, BINOP_instr((Inn : fuck1addrtype <: fuck1numtype), binop))
    -- if (Inn <- [I32_Inn I64_Inn])
    -- if (binop <- [mk_binop__0_binop_(Inn, ADD_binop_Inn) mk_binop__0_binop_(Inn, SUB_binop_Inn) mk_binop__0_binop_(Inn, MUL_binop_Inn)])
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr((Inn : fuck1addrtype <: fuck1numtype), binop))
    -- wf_binop_: `%%`((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, ADD_binop_Inn))
    -- wf_binop_: `%%`((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, SUB_binop_Inn))
    -- wf_binop_: `%%`((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, MUL_binop_Inn))

;; test.spectec:2941.1-2941.103
relation Expr_const: `%|-%CONST`fuck5(fuck1context, fuck1expr)
  ;; test.spectec:2990.1-2991.38
  rule _{C : fuck1context, `instr*` : fuck6fuck1instr*}:
    `%|-%CONST`(C, instr*{instr <- `instr*`})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr <- `instr*`}
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

;; test.spectec:2942.1-2942.105
relation Expr_ok_const: `%|-%:%CONST`fuck5(fuck1context, fuck1expr, fuck1valtype)
  ;; test.spectec:2994.1-2997.33
  rule _{C : fuck1context, expr : fuck1expr, t : fuck1valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, `%`_resulttype([t]))
    -- Expr_const: `%|-%CONST`(C, expr)
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(expr))*{expr <- expr}
    -- wf_valtype: `%`(t)

;; test.spectec:3012.1-3012.97
relation Type_ok: `%|-%:%`fuck5(fuck1context, fuck1type, fuck6fuck1deftype*)
  ;; test.spectec:3025.1-3029.53
  rule _{C : fuck1context, rectype : fuck1rectype, `dt*` : fuck6fuck1deftype*, x : fuck1idx}:
    `%|-%:%`(C, TYPE_type(rectype), dt*{dt <- `dt*`})
    -- if (x!`%`_uN.0 = |C.TYPES_context|)
    -- if (dt*{dt <- `dt*`} = $rolldt(x, rectype))
    -- Rectype_ok: `%|-%:%`(C +++ {TYPES dt*{dt <- `dt*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rectype, OK_oktypeidx(x))
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES dt*{dt <- `dt*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_oktypeidx: `%`(OK_oktypeidx(x))

;; test.spectec:3013.1-3013.96
relation Tag_ok: `%|-%:%`fuck5(fuck1context, fuck1tag, fuck1tagtype)
  ;; test.spectec:3031.1-3033.35
  rule _{C : fuck1context, tagtype : fuck1tagtype}:
    `%|-%:%`(C, TAG_tag(tagtype), $clos_tagtype(C, tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, tagtype)
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`($clos_tagtype(C, tagtype))
    -- wf_tag: `%`(TAG_tag(tagtype))

;; test.spectec:3014.1-3014.99
relation Global_ok: `%|-%:%`fuck5(fuck1context, fuck1global, fuck1globaltype)
  ;; test.spectec:3035.1-3039.40
  rule _{C : fuck1context, globaltype : fuck1globaltype, expr : fuck1expr, t : fuck1valtype}:
    `%|-%:%`(C, GLOBAL_global(globaltype, expr), globaltype)
    -- Globaltype_ok: `%|-%:OK`(C, globaltype)
    -- if (globaltype = `%%`_globaltype(?(MUT_mut), t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)
    -- wf_context: `%`(C)
    -- wf_global: `%`(GLOBAL_global(globaltype, expr))
    -- wf_globaltype: `%`(`%%`_globaltype(?(MUT_mut), t))

;; test.spectec:3015.1-3015.96
relation Mem_ok: `%|-%:%`fuck5(fuck1context, fuck1mem, fuck1memtype)
  ;; test.spectec:3041.1-3043.35
  rule _{C : fuck1context, memtype : fuck1memtype}:
    `%|-%:%`(C, MEMORY_mem(memtype), memtype)
    -- Memtype_ok: `%|-%:OK`(C, memtype)
    -- wf_context: `%`(C)
    -- wf_mem: `%`(MEMORY_mem(memtype))

;; test.spectec:3016.1-3016.98
relation Table_ok: `%|-%:%`fuck5(fuck1context, fuck1table, fuck1tabletype)
  ;; test.spectec:3045.1-3049.41
  rule _{C : fuck1context, tabletype : fuck1tabletype, expr : fuck1expr, at : fuck1addrtype, lim : fuck1limits, rt : fuck1reftype}:
    `%|-%:%`(C, TABLE_table(tabletype, expr), tabletype)
    -- Tabletype_ok: `%|-%:OK`(C, tabletype)
    -- if (tabletype = `%%%`_tabletype(at, lim, rt))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (rt : fuck1reftype <: fuck1valtype))
    -- wf_context: `%`(C)
    -- wf_table: `%`(TABLE_table(tabletype, expr))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt))

;; test.spectec:3023.1-3023.98
relation Local_ok: `%|-%:%`fuck5(fuck1context, fuck1local, fuck1localtype)
  ;; test.spectec:3051.1-3053.35
  rule set{C : fuck1context, t : fuck1valtype}:
    `%|-%:%`(C, LOCAL_local(t), `%%`_localtype(SET_init, t))
    -- Defaultable: `|-%DEFAULTABLE`(t)
    -- wf_context: `%`(C)
    -- wf_local: `%`(LOCAL_local(t))
    -- wf_localtype: `%`(`%%`_localtype(SET_init, t))

  ;; test.spectec:3055.1-3057.41
  rule unset{C : fuck1context, t : fuck1valtype}:
    `%|-%:%`(C, LOCAL_local(t), `%%`_localtype(UNSET_init, t))
    -- Nondefaultable: `|-%NONDEFAULTABLE`(t)
    -- wf_context: `%`(C)
    -- wf_local: `%`(LOCAL_local(t))
    -- wf_localtype: `%`(`%%`_localtype(UNSET_init, t))

;; test.spectec:3017.1-3017.97
relation Func_ok: `%|-%:%`fuck5(fuck1context, fuck1func, fuck1deftype)
  ;; test.spectec:3059.1-3064.89
  rule _{C : fuck1context, x : fuck1idx, `local*` : fuck6fuck1local*, expr : fuck1expr, `t_1*` : fuck6fuck1valtype*, `t_2*` : fuck6fuck1valtype*, `lct*` : fuck6fuck1localtype*}:
    `%|-%:%`(C, FUNC_func(x, local*{local <- `local*`}, expr), C.TYPES_context[x!`%`_uN.0])
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Local_ok: `%|-%:%`(C, local, lct))*{lct <- `lct*`, local <- `local*`}
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS `%%`_localtype(SET_init, t_1)*{t_1 <- `t_1*`} ++ lct*{lct <- `lct*`}, LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(`%`_resulttype(t_2*{t_2 <- `t_2*`})), REFS [], RECS []}, expr, `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- wf_context: `%`(C)
    -- wf_func: `%`(FUNC_func(x, local*{local <- `local*`}, expr))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS `%%`_localtype(SET_init, t_1)*{t_1 <- `t_1*`} ++ lct*{lct <- `lct*`}, LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(`%`_resulttype(t_2*{t_2 <- `t_2*`})), REFS [], RECS []})

;; test.spectec:3020.1-3020.118
relation Datamode_ok: `%|-%:%`fuck5(fuck1context, fuck1datamode, fuck1datatype)
  ;; test.spectec:3076.1-3077.20
  rule passive{C : fuck1context}:
    `%|-%:%`(C, PASSIVE_datamode, OK_datatype)
    -- wf_context: `%`(C)
    -- wf_datamode: `%`(PASSIVE_datamode)

  ;; test.spectec:3079.1-3082.41
  rule active{C : fuck1context, x : fuck1idx, expr : fuck1expr, at : fuck1addrtype, lim : fuck1limits}:
    `%|-%:%`(C, ACTIVE_datamode(x, expr), OK_datatype)
    -- if (C.MEMS_context[x!`%`_uN.0] = `%%PAGE`_memtype(at, lim))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (at : fuck1addrtype <: fuck1valtype))
    -- wf_context: `%`(C)
    -- wf_datamode: `%`(ACTIVE_datamode(x, expr))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

;; test.spectec:3018.1-3018.115
relation Data_ok: `%|-%:%`fuck5(fuck1context, fuck1data, fuck1datatype)
  ;; test.spectec:3066.1-3068.37
  rule _{C : fuck1context, `b*` : fuck6fuck1byte*, datamode : fuck1datamode}:
    `%|-%:%`(C, DATA_data(b*{b <- `b*`}, datamode), OK_datatype)
    -- Datamode_ok: `%|-%:%`(C, datamode, OK_datatype)
    -- wf_context: `%`(C)
    -- wf_data: `%`(DATA_data(b*{b <- `b*`}, datamode))

;; test.spectec:3021.1-3021.101
relation Elemmode_ok: `%|-%:%`fuck5(fuck1context, fuck1elemmode, fuck1elemtype)
  ;; test.spectec:3084.1-3085.20
  rule passive{C : fuck1context, rt : fuck1reftype}:
    `%|-%:%`(C, PASSIVE_elemmode, rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_elemmode: `%`(PASSIVE_elemmode)

  ;; test.spectec:3087.1-3088.20
  rule declare{C : fuck1context, rt : fuck1reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_elemmode: `%`(DECLARE_elemmode)

  ;; test.spectec:3090.1-3094.41
  rule active{C : fuck1context, x : fuck1idx, expr : fuck1expr, rt : fuck1reftype, at : fuck1addrtype, lim : fuck1limits, rt' : fuck1reftype}:
    `%|-%:%`(C, ACTIVE_elemmode(x, expr), rt)
    -- if (C.TABLES_context[x!`%`_uN.0] = `%%%`_tabletype(at, lim, rt'))
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (at : fuck1addrtype <: fuck1valtype))
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_elemmode: `%`(ACTIVE_elemmode(x, expr))
    -- wf_tabletype: `%`(`%%%`_tabletype(at, lim, rt'))

;; test.spectec:3019.1-3019.97
relation Elem_ok: `%|-%:%`fuck5(fuck1context, fuck1elem, fuck1elemtype)
  ;; test.spectec:3070.1-3074.43
  rule _{C : fuck1context, elemtype : fuck1elemtype, `expr*` : fuck6fuck1expr*, elemmode : fuck1elemmode}:
    `%|-%:%`(C, ELEM_elem(elemtype, expr*{expr <- `expr*`}, elemmode), elemtype)
    -- Reftype_ok: `%|-%:OK`(C, elemtype)
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, (elemtype : fuck1reftype <: fuck1valtype)))*{expr <- `expr*`}
    -- Elemmode_ok: `%|-%:%`(C, elemmode, elemtype)
    -- wf_context: `%`(C)
    -- wf_elem: `%`(ELEM_elem(elemtype, expr*{expr <- `expr*`}, elemmode))

;; test.spectec:3022.1-3022.98
relation Start_ok: `%|-%:OK`fuck5(fuck1context, fuck1start)
  ;; test.spectec:3096.1-3098.43
  rule _{C : fuck1context, x : fuck1idx}:
    `%|-%:OK`(C, START_start(x))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_uN.0], `FUNC%->%`_comptype(`%`_resulttype([]), `%`_resulttype([])))
    -- wf_context: `%`(C)
    -- wf_start: `%`(START_start(x))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(`%`_resulttype([]), `%`_resulttype([])))

;; test.spectec:3103.1-3103.105
relation Import_ok: `%|-%:%`fuck5(fuck1context, fuck1import, fuck1externtype)
  ;; test.spectec:3107.1-3109.33
  rule _{C : fuck1context, name_1 : fuck1name, name_2 : fuck1name, xt : fuck1externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), $clos_externtype(C, xt))
    -- Externtype_ok: `%|-%:OK`(C, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`($clos_externtype(C, xt))
    -- wf_import: `%`(IMPORT_import(name_1, name_2, xt))

;; test.spectec:3105.1-3105.108
relation Externidx_ok: `%|-%:%`fuck5(fuck1context, fuck1externidx, fuck1externtype)
  ;; test.spectec:3116.1-3118.23
  rule tag{C : fuck1context, x : fuck1idx, jt : fuck1tagtype}:
    `%|-%:%`(C, TAG_externidx(x), TAG_externtype(jt))
    -- if (C.TAGS_context[x!`%`_uN.0] = jt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TAG_externidx(x))
    -- wf_externtype: `%`(TAG_externtype(jt))

  ;; test.spectec:3120.1-3122.26
  rule global{C : fuck1context, x : fuck1idx, gt : fuck1globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = gt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(GLOBAL_externidx(x))
    -- wf_externtype: `%`(GLOBAL_externtype(gt))

  ;; test.spectec:3124.1-3126.23
  rule mem{C : fuck1context, x : fuck1idx, mt : fuck1memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if (C.MEMS_context[x!`%`_uN.0] = mt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(MEM_externidx(x))
    -- wf_externtype: `%`(MEM_externtype(mt))

  ;; test.spectec:3128.1-3130.25
  rule table{C : fuck1context, x : fuck1idx, tt : fuck1tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if (C.TABLES_context[x!`%`_uN.0] = tt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TABLE_externidx(x))
    -- wf_externtype: `%`(TABLE_externtype(tt))

  ;; test.spectec:3132.1-3134.24
  rule func{C : fuck1context, x : fuck1idx, dt : fuck1deftype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype((dt : fuck1deftype <: fuck1typeuse)))
    -- if (C.FUNCS_context[x!`%`_uN.0] = dt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(FUNC_externidx(x))
    -- wf_externtype: `%`(FUNC_externtype((dt : fuck1deftype <: fuck1typeuse)))

;; test.spectec:3104.1-3104.105
relation Export_ok: `%|-%:%%`fuck5(fuck1context, fuck1export, fuck1name, fuck1externtype)
  ;; test.spectec:3111.1-3113.39
  rule _{C : fuck1context, name : fuck1name, externidx : fuck1externidx, xt : fuck1externtype}:
    `%|-%:%%`(C, EXPORT_export(name, externidx), name, xt)
    -- Externidx_ok: `%|-%:%`(C, externidx, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(xt)
    -- wf_export: `%`(EXPORT_export(name, externidx))

;; test.spectec:3141.1-3141.100
rec {

;; test.spectec:3141.1-3141.100
relation Globals_ok: `%|-%:%`fuck5(fuck1context, fuck6fuck1global*, fuck6fuck1globaltype*)
  ;; test.spectec:3186.1-3187.17
  rule empty{C : fuck1context}:
    `%|-%:%`(C, [], [])
    -- wf_context: `%`(C)

  ;; test.spectec:3189.1-3192.54
  rule cons{C : fuck1context, global_1 : fuck1global, `global*` : fuck6fuck1global*, gt_1 : fuck1globaltype, `gt*` : fuck6fuck1globaltype*}:
    `%|-%:%`(C, [global_1] ++ global*{global <- `global*`}, [gt_1] ++ gt*{gt <- `gt*`})
    -- Global_ok: `%|-%:%`(C, global_1, gt_1)
    -- Globals_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [gt_1], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, global*{global <- `global*`}, gt*{gt <- `gt*`})
    -- wf_context: `%`(C)
    -- wf_global: `%`(global_1)
    -- (wf_global: `%`(global))*{global <- `global*`}
    -- (wf_globaltype: `%`(gt))*{gt <- `gt*`}
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [gt_1], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:3140.1-3140.98
rec {

;; test.spectec:3140.1-3140.98
relation Types_ok: `%|-%:%`fuck5(fuck1context, fuck6fuck1type*, fuck6fuck1deftype*)
  ;; test.spectec:3178.1-3179.17
  rule empty{C : fuck1context}:
    `%|-%:%`(C, [], [])
    -- wf_context: `%`(C)

  ;; test.spectec:3181.1-3184.49
  rule cons{C : fuck1context, type_1 : fuck1type, `type*` : fuck6fuck1type*, `dt_1*` : fuck6fuck1deftype*, `dt*` : fuck6fuck1deftype*}:
    `%|-%:%`(C, [type_1] ++ type*{type <- `type*`}, dt_1*{dt_1 <- `dt_1*`} ++ dt*{dt <- `dt*`})
    -- Type_ok: `%|-%:%`(C, type_1, dt_1*{dt_1 <- `dt_1*`})
    -- Types_ok: `%|-%:%`(C +++ {TYPES dt_1*{dt_1 <- `dt_1*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type*{type <- `type*`}, dt*{dt <- `dt*`})
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES dt_1*{dt_1 <- `dt_1*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:3144.1-3144.59
syntax nonfuncs = 
  | `%%%%%%`fuck5(`global*` : fuck6fuck1global*, `mem*` : fuck6fuck1mem*, `table*` : fuck6fuck1table*, `elem*` : fuck6fuck1elem*, `start?` : fuck6fuck1start?, `export*` : fuck6fuck1export*)

;; test.spectec:3144.8-3144.16
relation wf_nonfuncs: `%`fuck5(fuck1nonfuncs)
  ;; test.spectec:3144.8-3144.16
  rule nonfuncs_case_0{`global*` : fuck6fuck1global*, `mem*` : fuck6fuck1mem*, `table*` : fuck6fuck1table*, `elem*` : fuck6fuck1elem*, `start?` : fuck6fuck1start?, `export*` : fuck6fuck1export*}:
    `%`(`%%%%%%`_nonfuncs(`global*`, `mem*`, `table*`, `elem*`, `start?`, `export*`))
    -- (wf_global: `%`(global))*{global <- `global*`}
    -- (wf_mem: `%`(mem))*{mem <- `mem*`}
    -- (wf_table: `%`(table))*{table <- `table*`}
    -- (wf_elem: `%`(elem))*{elem <- `elem*`}
    -- (wf_start: `%`(start))?{start <- `start?`}
    -- (wf_export: `%`(export))*{export <- `export*`}

;; test.spectec:3145.1-3145.93
def $funcidx_nonfuncs(nonfuncs : fuck1nonfuncs) : fuck6fuck1funcidx*
  ;; test.spectec:3146.1-3147.87
  def $funcidx_nonfuncs{`global*` : fuck6fuck1global*, `mem*` : fuck6fuck1mem*, `table*` : fuck6fuck1table*, `elem*` : fuck6fuck1elem*, `start?` : fuck6fuck1start?, `export*` : fuck6fuck1export*}(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`})) = $funcidx_module(MODULE_module(`%`_list([]), `%`_list([]), `%`_list([]), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list([]), `%`_list([]), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})))

;; test.spectec:3145.6-3145.23
relation funcidx_nonfuncs_is_wf: `%%`fuck5(nonfuncs : fuck1nonfuncs, `ret_val*` : fuck6fuck1funcidx*)
  ;; test.spectec:3145.6-3145.23
  rule funcidx_nonfuncs_is_wf_0{nonfuncs : fuck1nonfuncs, `ret_val*` : fuck6fuck1funcidx*}:
    `%%`(nonfuncs, `ret_val*`)
    -- wf_nonfuncs: `%`(nonfuncs)
    -- if (`ret_val*` = $funcidx_nonfuncs(nonfuncs))
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3139.1-3139.99
relation Module_ok: `|-%:%`fuck5(fuck1module, fuck1moduletype)
  ;; test.spectec:3149.1-3175.32
  rule _{`type*` : fuck6fuck1type*, `import*` : fuck6fuck1import*, `tag*` : fuck6fuck1tag*, `global*` : fuck6fuck1global*, `mem*` : fuck6fuck1mem*, `table*` : fuck6fuck1table*, `func*` : fuck6fuck1func*, `data*` : fuck6fuck1data*, `elem*` : fuck6fuck1elem*, `start?` : fuck6fuck1start?, `export*` : fuck6fuck1export*, C : fuck1context, `xt_I*` : fuck6fuck1externtype*, `xt_E*` : fuck6fuck1externtype*, `dt'*` : fuck6fuck1deftype*, C' : fuck1context, `jt*` : fuck6fuck1tagtype*, `gt*` : fuck6fuck1globaltype*, `mt*` : fuck6fuck1memtype*, `tt*` : fuck6fuck1tabletype*, `dt*` : fuck6fuck1deftype*, `ok*` : fuck6fuck1datatype*, `rt*` : fuck6fuck1reftype*, `nm*` : fuck6fuck1name*, `jt_I*` : fuck6fuck1tagtype*, `mt_I*` : fuck6fuck1memtype*, `tt_I*` : fuck6fuck1tabletype*, `gt_I*` : fuck6fuck1globaltype*, `dt_I*` : fuck6fuck1deftype*, `x*` : fuck6fuck1idx*}:
    `|-%:%`(MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})), $clos_moduletype(C, `%->%`_moduletype(xt_I*{xt_I <- `xt_I*`}, xt_E*{xt_E <- `xt_E*`})))
    -- Types_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type*{type <- `type*`}, dt'*{dt' <- `dt'*`})
    -- (Import_ok: `%|-%:%`({TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, import, xt_I))*{import <- `import*`, xt_I <- `xt_I*`}
    -- (Tag_ok: `%|-%:%`(C', tag, jt))*{jt <- `jt*`, tag <- `tag*`}
    -- Globals_ok: `%|-%:%`(C', global*{global <- `global*`}, gt*{gt <- `gt*`})
    -- (Mem_ok: `%|-%:%`(C', mem, mt))*{mem <- `mem*`, mt <- `mt*`}
    -- (Table_ok: `%|-%:%`(C', table, tt))*{table <- `table*`, tt <- `tt*`}
    -- (Func_ok: `%|-%:%`(C, func, dt))*{dt <- `dt*`, func <- `func*`}
    -- (Data_ok: `%|-%:%`(C, data, ok))*{data <- `data*`, ok <- `ok*`}
    -- (Elem_ok: `%|-%:%`(C, elem, rt))*{elem <- `elem*`, rt <- `rt*`}
    -- (Start_ok: `%|-%:OK`(C, start))?{start <- `start?`}
    -- (Export_ok: `%|-%:%%`(C, export, nm, xt_E))*{export <- `export*`, nm <- `nm*`, xt_E <- `xt_E*`}
    -- if $disjoint_(syntax fuck1name, nm*{nm <- `nm*`})
    -- if (C = C' +++ {TYPES [], TAGS jt_I*{jt_I <- `jt_I*`} ++ jt*{jt <- `jt*`}, GLOBALS gt*{gt <- `gt*`}, MEMS mt_I*{mt_I <- `mt_I*`} ++ mt*{mt <- `mt*`}, TABLES tt_I*{tt_I <- `tt_I*`} ++ tt*{tt <- `tt*`}, FUNCS [], DATAS ok*{ok <- `ok*`}, ELEMS rt*{rt <- `rt*`}, LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- if (C' = {TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS gt_I*{gt_I <- `gt_I*`}, MEMS [], TABLES [], FUNCS dt_I*{dt_I <- `dt_I*`} ++ dt*{dt <- `dt*`}, DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS x*{x <- `x*`}, RECS []})
    -- if (x*{x <- `x*`} = $funcidx_nonfuncs(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`})))
    -- if (jt_I*{jt_I <- `jt_I*`} = $tagsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (gt_I*{gt_I <- `gt_I*`} = $globalsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (mt_I*{mt_I <- `mt_I*`} = $memsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (tt_I*{tt_I <- `tt_I*`} = $tablesxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (dt_I*{dt_I <- `dt_I*`} = $funcsxt(xt_I*{xt_I <- `xt_I*`}))
    -- wf_context: `%`(C)
    -- wf_context: `%`(C')
    -- (wf_name: `%`(nm))*{nm <- `nm*`}
    -- wf_moduletype: `%`($clos_moduletype(C, `%->%`_moduletype(xt_I*{xt_I <- `xt_I*`}, xt_E*{xt_E <- `xt_E*`})))
    -- (wf_uN: `%%`(32, iter))*{iter <- $funcidx_nonfuncs(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`}))}
    -- (wf_typeuse: `%`(iter))*{iter <- $tagsxt(xt_I*{xt_I <- `xt_I*`})}
    -- (wf_globaltype: `%`(iter))*{iter <- $globalsxt(xt_I*{xt_I <- `xt_I*`})}
    -- (wf_memtype: `%`(iter))*{iter <- $memsxt(xt_I*{xt_I <- `xt_I*`})}
    -- (wf_tabletype: `%`(iter))*{iter <- $tablesxt(xt_I*{xt_I <- `xt_I*`})}
    -- wf_module: `%`(MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})))
    -- wf_moduletype: `%`(`%->%`_moduletype(xt_I*{xt_I <- `xt_I*`}, xt_E*{xt_E <- `xt_E*`}))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_context: `%`({TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_context: `%`({TYPES [], TAGS jt_I*{jt_I <- `jt_I*`} ++ jt*{jt <- `jt*`}, GLOBALS gt*{gt <- `gt*`}, MEMS mt_I*{mt_I <- `mt_I*`} ++ mt*{mt <- `mt*`}, TABLES tt_I*{tt_I <- `tt_I*`} ++ tt*{tt <- `tt*`}, FUNCS [], DATAS ok*{ok <- `ok*`}, ELEMS rt*{rt <- `rt*`}, LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_context: `%`({TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS gt_I*{gt_I <- `gt_I*`}, MEMS [], TABLES [], FUNCS dt_I*{dt_I <- `dt_I*`} ++ dt*{dt <- `dt*`}, DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS x*{x <- `x*`}, RECS []})
    -- wf_nonfuncs: `%`(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`}))

;; test.spectec:3205.1-3205.24
syntax relaxed2 = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:3205.8-3205.16
relation wf_relaxed2: `%`fuck5(fuck1relaxed2)
  ;; test.spectec:3205.8-3205.16
  rule relaxed2_case_0{i : fuck3nat}:
    `%`(`%`_relaxed2(i))
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:3206.1-3206.32
syntax relaxed4 = 
  | `%`fuck5(i : fuck3nat)

;; test.spectec:3206.8-3206.16
relation wf_relaxed4: `%`fuck5(fuck1relaxed4)
  ;; test.spectec:3206.8-3206.16
  rule relaxed4_case_0{i : fuck3nat}:
    `%`(`%`_relaxed4(i))
    -- if ((((i = 0) \/ (i = 1)) \/ (i = 2)) \/ (i = 3))

;; test.spectec:3208.1-3208.83
def $relaxed2(relaxed2 : fuck1relaxed2, syntax X, X : fuck1X, X : fuck1X) : fuck1X
  ;; test.spectec:3211.1-3211.63
  def $relaxed2{i : fuck1relaxed2, syntax X, X_1 : fuck1X, X_2 : fuck1X}(i, syntax fuck1X, X_1, X_2) = (if $ND then [X_1 X_2][i!`%`_relaxed2.0] else [X_1 X_2][0])

;; test.spectec:3209.1-3209.89
def $relaxed4(relaxed4 : fuck1relaxed4, syntax X, X : fuck1X, X : fuck1X, X : fuck1X, X : fuck1X) : fuck1X
  ;; test.spectec:3214.1-3214.81
  def $relaxed4{i : fuck1relaxed4, syntax X, X_1 : fuck1X, X_2 : fuck1X, X_3 : fuck1X, X_4 : fuck1X}(i, syntax fuck1X, X_1, X_2, X_3, X_4) = (if $ND then [X_1 X_2 X_3 X_4][i!`%`_relaxed4.0] else [X_1 X_2 X_3 X_4][0])

;; test.spectec:3218.1-3218.43
def $R_fmadd : fuck1relaxed2

;; test.spectec:3218.6-3218.13
relation R_fmadd_is_wf: `%`fuck5(ret_val : fuck1relaxed2)
  ;; test.spectec:3218.6-3218.13
  rule R_fmadd_is_wf_0{ret_val : fuck1relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_fmadd)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3219.1-3219.43
def $R_fmin : fuck1relaxed4

;; test.spectec:3219.6-3219.12
relation R_fmin_is_wf: `%`fuck5(ret_val : fuck1relaxed4)
  ;; test.spectec:3219.6-3219.12
  rule R_fmin_is_wf_0{ret_val : fuck1relaxed4}:
    `%`(ret_val)
    -- if (ret_val = $R_fmin)
    -- wf_relaxed4: `%`(ret_val)

;; test.spectec:3220.1-3220.43
def $R_fmax : fuck1relaxed4

;; test.spectec:3220.6-3220.12
relation R_fmax_is_wf: `%`fuck5(ret_val : fuck1relaxed4)
  ;; test.spectec:3220.6-3220.12
  rule R_fmax_is_wf_0{ret_val : fuck1relaxed4}:
    `%`(ret_val)
    -- if (ret_val = $R_fmax)
    -- wf_relaxed4: `%`(ret_val)

;; test.spectec:3221.1-3221.43
def $R_idot : fuck1relaxed2

;; test.spectec:3221.6-3221.12
relation R_idot_is_wf: `%`fuck5(ret_val : fuck1relaxed2)
  ;; test.spectec:3221.6-3221.12
  rule R_idot_is_wf_0{ret_val : fuck1relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_idot)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3222.1-3222.43
def $R_iq15mulr : fuck1relaxed2

;; test.spectec:3222.6-3222.16
relation R_iq15mulr_is_wf: `%`fuck5(ret_val : fuck1relaxed2)
  ;; test.spectec:3222.6-3222.16
  rule R_iq15mulr_is_wf_0{ret_val : fuck1relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_iq15mulr)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3223.1-3223.43
def $R_trunc_u : fuck1relaxed4

;; test.spectec:3223.6-3223.15
relation R_trunc_u_is_wf: `%`fuck5(ret_val : fuck1relaxed4)
  ;; test.spectec:3223.6-3223.15
  rule R_trunc_u_is_wf_0{ret_val : fuck1relaxed4}:
    `%`(ret_val)
    -- if (ret_val = $R_trunc_u)
    -- wf_relaxed4: `%`(ret_val)

;; test.spectec:3224.1-3224.43
def $R_trunc_s : fuck1relaxed2

;; test.spectec:3224.6-3224.15
relation R_trunc_s_is_wf: `%`fuck5(ret_val : fuck1relaxed2)
  ;; test.spectec:3224.6-3224.15
  rule R_trunc_s_is_wf_0{ret_val : fuck1relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_trunc_s)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3225.1-3225.43
def $R_swizzle : fuck1relaxed2

;; test.spectec:3225.6-3225.15
relation R_swizzle_is_wf: `%`fuck5(ret_val : fuck1relaxed2)
  ;; test.spectec:3225.6-3225.15
  rule R_swizzle_is_wf_0{ret_val : fuck1relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_swizzle)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3226.1-3226.43
def $R_laneselect : fuck1relaxed2

;; test.spectec:3226.6-3226.18
relation R_laneselect_is_wf: `%`fuck5(ret_val : fuck1relaxed2)
  ;; test.spectec:3226.6-3226.18
  rule R_laneselect_is_wf_0{ret_val : fuck1relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_laneselect)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3241.1-3241.41
def $s33_to_u32(s33 : fuck1s33) : fuck1u32

;; test.spectec:3241.6-3241.17
relation s33_to_u32_is_wf: `%%`fuck5(s33 : fuck1s33, ret_val : fuck1u32)
  ;; test.spectec:3241.6-3241.17
  rule s33_to_u32_is_wf_0{s33 : fuck1s33, ret_val : fuck1u32}:
    `%%`(s33, ret_val)
    -- wf_sN: `%%`(33, s33)
    -- if (ret_val = $s33_to_u32(s33))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3246.1-3246.107
def $ibits_(N : fuck1N, iN : fuck1iN) : fuck6fuck1bit*

;; test.spectec:3246.6-3246.13
relation ibits__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, `ret_val*` : fuck6fuck1bit*)
  ;; test.spectec:3246.6-3246.13
  rule ibits__is_wf_0{N : fuck1N, iN : fuck1iN, `ret_val*` : fuck6fuck1bit*}:
    `%%%`(N, iN, `ret_val*`)
    -- wf_uN: `%%`(N, iN)
    -- if (`ret_val*` = $ibits_(N, iN))
    -- (wf_bit: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3247.1-3247.107
def $fbits_(N : fuck1N, fN : fuck1fN) : fuck6fuck1bit*

;; test.spectec:3247.6-3247.13
relation fbits__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1bit*)
  ;; test.spectec:3247.6-3247.13
  rule fbits__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1bit*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fbits_(N, fN))
    -- (wf_bit: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3248.1-3248.109
def $ibytes_(N : fuck1N, iN : fuck1iN) : fuck6fuck1byte*

;; test.spectec:3248.6-3248.14
relation ibytes__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:3248.6-3248.14
  rule ibytes__is_wf_0{N : fuck1N, iN : fuck1iN, `ret_val*` : fuck6fuck1byte*}:
    `%%%`(N, iN, `ret_val*`)
    -- wf_uN: `%%`(N, iN)
    -- if (`ret_val*` = $ibytes_(N, iN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3249.1-3249.109
def $fbytes_(N : fuck1N, fN : fuck1fN) : fuck6fuck1byte*

;; test.spectec:3249.6-3249.14
relation fbytes__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:3249.6-3249.14
  rule fbytes__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1byte*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fbytes_(N, fN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3250.1-3250.104
def $nbytes_(numtype : fuck1numtype, num_ : fuck1num_) : fuck6fuck1byte*

;; test.spectec:3250.6-3250.14
relation nbytes__is_wf: `%%%`fuck5(numtype : fuck1numtype, num_ : fuck1num_, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:3250.6-3250.14
  rule nbytes__is_wf_0{numtype : fuck1numtype, num_ : fuck1num_, `ret_val*` : fuck6fuck1byte*}:
    `%%%`(numtype, num_, `ret_val*`)
    -- wf_num_: `%%`(numtype, num_)
    -- if (`ret_val*` = $nbytes_(numtype, num_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3251.1-3251.104
def $vbytes_(vectype : fuck1vectype, vec_ : fuck1vec_) : fuck6fuck1byte*

;; test.spectec:3251.6-3251.14
relation vbytes__is_wf: `%%%`fuck5(vectype : fuck1vectype, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:3251.6-3251.14
  rule vbytes__is_wf_0{vectype : fuck1vectype, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1byte*}:
    `%%%`(vectype, vec_, `ret_val*`)
    -- wf_uN: `%%`($vsize(vectype), vec_)
    -- if (`ret_val*` = $vbytes_(vectype, vec_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3252.1-3252.104
def $zbytes_(storagetype : fuck1storagetype, lit_ : fuck1lit_) : fuck6fuck1byte*

;; test.spectec:3252.6-3252.14
relation zbytes__is_wf: `%%%`fuck5(storagetype : fuck1storagetype, lit_ : fuck1lit_, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:3252.6-3252.14
  rule zbytes__is_wf_0{storagetype : fuck1storagetype, lit_ : fuck1lit_, `ret_val*` : fuck6fuck1byte*}:
    `%%%`(storagetype, lit_, `ret_val*`)
    -- wf_storagetype: `%`(storagetype)
    -- wf_lit_: `%%`(storagetype, lit_)
    -- if (`ret_val*` = $zbytes_(storagetype, lit_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3253.1-3253.104
def $cbytes_(Cnn : fuck1Cnn, lit_ : fuck1lit_) : fuck6fuck1byte*

;; test.spectec:3253.6-3253.14
relation cbytes__is_wf: `%%%`fuck5(Cnn : fuck1Cnn, lit_ : fuck1lit_, `ret_val*` : fuck6fuck1byte*)
  ;; test.spectec:3253.6-3253.14
  rule cbytes__is_wf_0{Cnn : fuck1Cnn, lit_ : fuck1lit_, `ret_val*` : fuck6fuck1byte*}:
    `%%%`(Cnn, lit_, `ret_val*`)
    -- wf_lit_: `%%`((Cnn : fuck1Cnn <: fuck1storagetype), lit_)
    -- if (`ret_val*` = $cbytes_(Cnn, lit_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3255.1-3255.91
def $inv_ibits_(N : fuck1N, fuck6fuck1bit*) : fuck1iN

;; test.spectec:3255.6-3255.17
relation inv_ibits__is_wf: `%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1bit*, ret_val : fuck1iN)
  ;; test.spectec:3255.6-3255.17
  rule inv_ibits__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1bit*, ret_val : fuck1iN}:
    `%%%`(N, `var_0*`, ret_val)
    -- (wf_bit: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_ibits_(N, `var_0*`))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3256.1-3256.91
def $inv_fbits_(N : fuck1N, fuck6fuck1bit*) : fuck1fN

;; test.spectec:3256.6-3256.17
relation inv_fbits__is_wf: `%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1bit*, ret_val : fuck1fN)
  ;; test.spectec:3256.6-3256.17
  rule inv_fbits__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1bit*, ret_val : fuck1fN}:
    `%%%`(N, `var_0*`, ret_val)
    -- (wf_bit: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_fbits_(N, `var_0*`))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:3257.1-3257.92
def $inv_ibytes_(N : fuck1N, fuck6fuck1byte*) : fuck1iN

;; test.spectec:3257.6-3257.18
relation inv_ibytes__is_wf: `%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1byte*, ret_val : fuck1iN)
  ;; test.spectec:3257.6-3257.18
  rule inv_ibytes__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1byte*, ret_val : fuck1iN}:
    `%%%`(N, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_ibytes_(N, `var_0*`))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3258.1-3258.92
def $inv_fbytes_(N : fuck1N, fuck6fuck1byte*) : fuck1fN

;; test.spectec:3258.6-3258.18
relation inv_fbytes__is_wf: `%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1byte*, ret_val : fuck1fN)
  ;; test.spectec:3258.6-3258.18
  rule inv_fbytes__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1byte*, ret_val : fuck1fN}:
    `%%%`(N, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_fbytes_(N, `var_0*`))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:3259.1-3259.87
def $inv_nbytes_(numtype : fuck1numtype, fuck6fuck1byte*) : fuck1num_

;; test.spectec:3259.6-3259.18
relation inv_nbytes__is_wf: `%%%`fuck5(numtype : fuck1numtype, `var_0*` : fuck6fuck1byte*, ret_val : fuck1num_)
  ;; test.spectec:3259.6-3259.18
  rule inv_nbytes__is_wf_0{numtype : fuck1numtype, `var_0*` : fuck6fuck1byte*, ret_val : fuck1num_}:
    `%%%`(numtype, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_nbytes_(numtype, `var_0*`))
    -- wf_num_: `%%`(numtype, ret_val)

;; test.spectec:3260.1-3260.87
def $inv_vbytes_(vectype : fuck1vectype, fuck6fuck1byte*) : fuck1vec_

;; test.spectec:3260.6-3260.18
relation inv_vbytes__is_wf: `%%%`fuck5(vectype : fuck1vectype, `var_0*` : fuck6fuck1byte*, ret_val : fuck1vec_)
  ;; test.spectec:3260.6-3260.18
  rule inv_vbytes__is_wf_0{vectype : fuck1vectype, `var_0*` : fuck6fuck1byte*, ret_val : fuck1vec_}:
    `%%%`(vectype, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_vbytes_(vectype, `var_0*`))
    -- wf_uN: `%%`($vsize(vectype), ret_val)

;; test.spectec:3261.1-3261.92
def $inv_zbytes_(storagetype : fuck1storagetype, fuck6fuck1byte*) : fuck1lit_

;; test.spectec:3261.6-3261.18
relation inv_zbytes__is_wf: `%%%`fuck5(storagetype : fuck1storagetype, `var_0*` : fuck6fuck1byte*, ret_val : fuck1lit_)
  ;; test.spectec:3261.6-3261.18
  rule inv_zbytes__is_wf_0{storagetype : fuck1storagetype, `var_0*` : fuck6fuck1byte*, ret_val : fuck1lit_}:
    `%%%`(storagetype, `var_0*`, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_zbytes_(storagetype, `var_0*`))
    -- wf_lit_: `%%`(storagetype, ret_val)

;; test.spectec:3262.1-3262.87
def $inv_cbytes_(Cnn : fuck1Cnn, fuck6fuck1byte*) : fuck1lit_

;; test.spectec:3262.6-3262.18
relation inv_cbytes__is_wf: `%%%`fuck5(Cnn : fuck1Cnn, `var_0*` : fuck6fuck1byte*, ret_val : fuck1lit_)
  ;; test.spectec:3262.6-3262.18
  rule inv_cbytes__is_wf_0{Cnn : fuck1Cnn, `var_0*` : fuck6fuck1byte*, ret_val : fuck1lit_}:
    `%%%`(Cnn, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_cbytes_(Cnn, `var_0*`))
    -- wf_lit_: `%%`((Cnn : fuck1Cnn <: fuck1storagetype), ret_val)

;; test.spectec:3286.1-3286.54
def $signed_(N : fuck1N, nat : fuck3nat) : fuck3int
  ;; test.spectec:3287.1-3287.54
  def $signed_{N : fuck3nat, i : fuck3nat}(N, i) = (i : nat <:> int)
    -- if (i < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))
  ;; test.spectec:3288.1-3288.61
  def $signed_{N : fuck3nat, i : fuck3nat}(N, i) = ((i : nat <:> int) - ((2 ^ N) : nat <:> int))
    -- if (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ N)))

;; test.spectec:3290.1-3290.68
def $inv_signed_(N : fuck1N, int : fuck3int) : fuck3nat
  ;; test.spectec:3291.1-3291.62
  def $inv_signed_{N : fuck3nat, i : fuck3int}(N, i) = (i : int <:> nat)
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))
  ;; test.spectec:3292.1-3292.63
  def $inv_signed_{N : fuck3nat, i : fuck3int}(N, i) = ((i + ((2 ^ N) : nat <:> int)) : int <:> nat)
    -- if ((- ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; test.spectec:3295.1-3295.60
def $sx(storagetype : fuck1storagetype) : fuck6fuck1sx?
  ;; test.spectec:3296.1-3296.25
  def $sx{consttype : fuck1consttype}((consttype : fuck1consttype <: fuck1storagetype)) = ?()
  ;; test.spectec:3297.1-3297.22
  def $sx{packtype : fuck1packtype}((packtype : fuck1packtype <: fuck1storagetype)) = ?(S_sx)

;; test.spectec:3302.1-3302.51
def $zero(lanetype : fuck1lanetype) : fuck1lane_
  ;; test.spectec:3303.1-3303.19
  def $zero{Jnn : fuck1Jnn}((Jnn : fuck1Jnn <: fuck1lanetype)) = mk_lane__2_lane_(Jnn, `%`_uN(0))
  ;; test.spectec:3304.1-3304.36
  def $zero{Fnn : fuck1Fnn}((Fnn : fuck1Fnn <: fuck1lanetype)) = mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, $fzero($size((Fnn : fuck1Fnn <: fuck1numtype)))))

;; test.spectec:3302.6-3302.11
relation zero_is_wf: `%%`fuck5(lanetype : fuck1lanetype, ret_val : fuck1lane_)
  ;; test.spectec:3302.6-3302.11
  rule zero_is_wf_0{lanetype : fuck1lanetype, ret_val : fuck1lane_}:
    `%%`(lanetype, ret_val)
    -- if (ret_val = $zero(lanetype))
    -- wf_lane_: `%%`(lanetype, ret_val)

;; test.spectec:3306.1-3306.22
def $bool(bool : fuck2bool) : fuck3nat
  ;; test.spectec:3307.1-3307.21
  def $bool(false) = 0
  ;; test.spectec:3308.1-3308.20
  def $bool(true) = 1

;; test.spectec:3310.1-3310.23
def $truncz(rat : fuck3rat) : fuck3int

;; test.spectec:3314.1-3314.59
def $ceilz(rat : fuck3rat) : fuck3int

;; test.spectec:3321.1-3321.61
def $sat_u_(N : fuck1N, int : fuck3int) : fuck3nat
  ;; test.spectec:3322.1-3322.48
  def $sat_u_{N : fuck3nat, i : fuck3int}(N, i) = (if (i < (0 : nat <:> int)) then 0 else (if (i > (((2 ^ N) : nat <:> int) - (1 : nat <:> int))) then ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat) else (i : int <:> nat)))

;; test.spectec:3326.1-3326.61
def $sat_s_(N : fuck1N, int : fuck3int) : fuck3int
  ;; test.spectec:3327.1-3327.58
  def $sat_s_{N : fuck3nat, i : fuck3int}(N, i) = (if (i < - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) then - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) else (if (i > (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int))) then (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)) else i))

;; test.spectec:3334.1-3334.29
def $ineg_(N : fuck1N, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3381.1-3381.42
  def $ineg_{N : fuck3nat, i_1 : fuck1uN}(N, i_1) = `%`_iN((((((2 ^ N) : nat <:> int) - (i_1!`%`_uN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:3334.6-3334.12
relation ineg__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3334.6-3334.12
  rule ineg__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ineg_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3335.1-3335.29
def $iabs_(N : fuck1N, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3383.1-3383.65
  def $iabs_{N : fuck3nat, i_1 : fuck1uN}(N, i_1) = (if ($signed_(N, i_1!`%`_uN.0) >= (0 : nat <:> int)) then i_1 else $ineg_(N, i_1))

;; test.spectec:3335.6-3335.12
relation iabs__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3335.6-3335.12
  rule iabs__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $iabs_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3336.1-3336.29
def $iclz_(N : fuck1N, iN : fuck1iN) : fuck1iN

;; test.spectec:3336.6-3336.12
relation iclz__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3336.6-3336.12
  rule iclz__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $iclz_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3337.1-3337.29
def $ictz_(N : fuck1N, iN : fuck1iN) : fuck1iN

;; test.spectec:3337.6-3337.12
relation ictz__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3337.6-3337.12
  rule ictz__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ictz_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3338.1-3338.32
def $ipopcnt_(N : fuck1N, iN : fuck1iN) : fuck1iN

;; test.spectec:3338.6-3338.15
relation ipopcnt__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3338.6-3338.15
  rule ipopcnt__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ipopcnt_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3339.1-3339.86
def $iextend_(N : fuck1N, M : fuck1M, sx : fuck1sx, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3395.1-3395.39
  def $iextend_{N : fuck3nat, M : fuck3nat, i : fuck1uN}(N, M, U_sx, i) = `%`_iN((i!`%`_uN.0 \ (2 ^ M)))
  ;; test.spectec:3396.1-3396.69
  def $iextend_{N : fuck3nat, M : fuck3nat, i : fuck1uN}(N, M, S_sx, i) = `%`_iN($inv_signed_(N, $signed_(M, (i!`%`_uN.0 \ (2 ^ M)))))

;; test.spectec:3339.6-3339.15
relation iextend__is_wf: `%%%%%`fuck5(N : fuck1N, M : fuck1M, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3339.6-3339.15
  rule iextend__is_wf_0{N : fuck1N, M : fuck1M, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, M, sx, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $iextend_(N, M, sx, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3341.1-3341.36
def $iadd_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3399.1-3399.47
  def $iadd_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, i_1, i_2) = `%`_iN(((i_1!`%`_uN.0 + i_2!`%`_uN.0) \ (2 ^ N)))

;; test.spectec:3341.6-3341.12
relation iadd__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3341.6-3341.12
  rule iadd__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iadd_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3342.1-3342.36
def $isub_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3401.1-3401.53
  def $isub_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, i_1, i_2) = `%`_iN(((((((2 ^ N) + i_1!`%`_uN.0) : nat <:> int) - (i_2!`%`_uN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:3342.6-3342.12
relation isub__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3342.6-3342.12
  rule isub__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $isub_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3343.1-3343.36
def $imul_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3403.1-3403.47
  def $imul_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, i_1, i_2) = `%`_iN(((i_1!`%`_uN.0 * i_2!`%`_uN.0) \ (2 ^ N)))

;; test.spectec:3343.6-3343.12
relation imul__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3343.6-3343.12
  rule imul__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $imul_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3344.1-3344.83
def $idiv_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN?
  ;; test.spectec:3405.1-3405.33
  def $idiv_{N : fuck3nat, i_1 : fuck1uN}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3406.1-3406.51
  def $idiv_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = ?(`%`_iN(($truncz(((i_1!`%`_uN.0 : nat <:> rat) / (i_2!`%`_uN.0 : nat <:> rat))) : int <:> nat)))
  ;; test.spectec:3407.1-3407.33
  def $idiv_{N : fuck3nat, i_1 : fuck1uN}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3408.1-3408.96
  def $idiv_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = ?()
    -- if ((($signed_(N, i_1!`%`_uN.0) : int <:> rat) / ($signed_(N, i_2!`%`_uN.0) : int <:> rat)) = ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))
  ;; test.spectec:3409.1-3409.94
  def $idiv_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, $truncz((($signed_(N, i_1!`%`_uN.0) : int <:> rat) / ($signed_(N, i_2!`%`_uN.0) : int <:> rat))))))

;; test.spectec:3344.6-3344.12
relation idiv__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, `ret_val?` : fuck6fuck1iN?)
  ;; test.spectec:3344.6-3344.12
  rule idiv__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, `ret_val?` : fuck6fuck1iN?}:
    `%%%%%`(N, sx, iN, iN_0, `ret_val?`)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (`ret_val?` = $idiv_(N, sx, iN, iN_0))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:3345.1-3345.83
def $irem_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN?
  ;; test.spectec:3411.1-3411.33
  def $irem_{N : fuck3nat, i_1 : fuck1uN}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3412.1-3412.66
  def $irem_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = ?(`%`_iN((((i_1!`%`_uN.0 : nat <:> int) - ((i_2!`%`_uN.0 * ($truncz(((i_1!`%`_uN.0 : nat <:> rat) / (i_2!`%`_uN.0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat)))
  ;; test.spectec:3413.1-3413.33
  def $irem_{N : fuck3nat, i_1 : fuck1uN}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3414.1-3415.84
  def $irem_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN, j_1 : fuck3int, j_2 : fuck3int}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))))))
    -- if ((j_1 = $signed_(N, i_1!`%`_uN.0)) /\ (j_2 = $signed_(N, i_2!`%`_uN.0)))

;; test.spectec:3345.6-3345.12
relation irem__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, `ret_val?` : fuck6fuck1iN?)
  ;; test.spectec:3345.6-3345.12
  rule irem__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, `ret_val?` : fuck6fuck1iN?}:
    `%%%%%`(N, sx, iN, iN_0, `ret_val?`)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (`ret_val?` = $irem_(N, sx, iN, iN_0))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:3346.1-3346.83
def $imin_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3417.1-3417.51
  def $imin_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_uN.0 <= i_2!`%`_uN.0)
  ;; test.spectec:3418.1-3418.50
  def $imin_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_uN.0 > i_2!`%`_uN.0)
  ;; test.spectec:3419.1-3419.77
  def $imin_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = (if ($signed_(N, i_1!`%`_uN.0) <= $signed_(N, i_2!`%`_uN.0)) then i_1 else i_2)

;; test.spectec:3346.6-3346.12
relation imin__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3346.6-3346.12
  rule imin__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $imin_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3347.1-3347.83
def $imax_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3422.1-3422.51
  def $imax_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_uN.0 >= i_2!`%`_uN.0)
  ;; test.spectec:3423.1-3423.50
  def $imax_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_uN.0 < i_2!`%`_uN.0)
  ;; test.spectec:3424.1-3424.77
  def $imax_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = (if ($signed_(N, i_1!`%`_uN.0) >= $signed_(N, i_2!`%`_uN.0)) then i_1 else i_2)

;; test.spectec:3347.6-3347.12
relation imax__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3347.6-3347.12
  rule imax__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $imax_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3348.1-3348.88
def $iadd_sat_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3427.1-3427.58
  def $iadd_sat_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_uN.0 + i_2!`%`_uN.0) : nat <:> int)))
  ;; test.spectec:3428.1-3428.101
  def $iadd_sat_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_uN.0) + $signed_(N, i_2!`%`_uN.0)))))

;; test.spectec:3348.6-3348.16
relation iadd_sat__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3348.6-3348.16
  rule iadd_sat__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iadd_sat_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3349.1-3349.88
def $isub_sat_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3430.1-3430.58
  def $isub_sat_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_uN.0 : nat <:> int) - (i_2!`%`_uN.0 : nat <:> int))))
  ;; test.spectec:3431.1-3431.101
  def $isub_sat_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_uN.0) - $signed_(N, i_2!`%`_uN.0)))))

;; test.spectec:3349.6-3349.16
relation isub_sat__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3349.6-3349.16
  rule isub_sat__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $isub_sat_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3350.1-3350.92
def $iq15mulr_sat_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3350.6-3350.20
relation iq15mulr_sat__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3350.6-3350.20
  rule iq15mulr_sat__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iq15mulr_sat_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3351.1-3351.101
def $irelaxed_q15mulr_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*

;; test.spectec:3351.6-3351.24
relation irelaxed_q15mulr__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, `ret_val*` : fuck6fuck1iN*)
  ;; test.spectec:3351.6-3351.24
  rule irelaxed_q15mulr__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, `ret_val*` : fuck6fuck1iN*}:
    `%%%%%`(N, sx, iN, iN_0, `ret_val*`)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (`ret_val*` = $irelaxed_q15mulr_(N, sx, iN, iN_0))
    -- (wf_uN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3352.1-3352.84
def $iavgr_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3352.6-3352.13
relation iavgr__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3352.6-3352.13
  rule iavgr__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iavgr_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3354.1-3354.29
def $inot_(N : fuck1N, iN : fuck1iN) : fuck1iN

;; test.spectec:3354.6-3354.12
relation inot__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3354.6-3354.12
  rule inot__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $inot_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3355.1-3355.29
def $irev_(N : fuck1N, iN : fuck1iN) : fuck1iN

;; test.spectec:3355.6-3355.12
relation irev__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3355.6-3355.12
  rule irev__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $irev_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3356.1-3356.36
def $iand_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3356.6-3356.12
relation iand__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3356.6-3356.12
  rule iand__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iand_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3357.1-3357.39
def $iandnot_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3357.6-3357.15
relation iandnot__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3357.6-3357.15
  rule iandnot__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iandnot_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3358.1-3358.35
def $ior_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3358.6-3358.11
relation ior__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3358.6-3358.11
  rule ior__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ior_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3359.1-3359.36
def $ixor_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3359.6-3359.12
relation ixor__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3359.6-3359.12
  rule ixor__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ixor_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3360.1-3360.34
def $ishl_(N : fuck1N, iN : fuck1iN, u32 : fuck1u32) : fuck1iN

;; test.spectec:3360.6-3360.12
relation ishl__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, u32 : fuck1u32, ret_val : fuck1iN)
  ;; test.spectec:3360.6-3360.12
  rule ishl__is_wf_0{N : fuck1N, iN : fuck1iN, u32 : fuck1u32, ret_val : fuck1iN}:
    `%%%%`(N, iN, u32, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $ishl_(N, iN, u32))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3361.1-3361.76
def $ishr_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32) : fuck1iN

;; test.spectec:3361.6-3361.12
relation ishr__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32, ret_val : fuck1iN)
  ;; test.spectec:3361.6-3361.12
  rule ishr__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32, ret_val : fuck1iN}:
    `%%%%%`(N, sx, iN, u32, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $ishr_(N, sx, iN, u32))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3362.1-3362.37
def $irotl_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3362.6-3362.13
relation irotl__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3362.6-3362.13
  rule irotl__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $irotl_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3363.1-3363.37
def $irotr_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3363.6-3363.13
relation irotr__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3363.6-3363.13
  rule irotr__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $irotr_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3365.1-3365.49
def $ibitselect_(N : fuck1N, iN : fuck1iN, iN : fuck1iN, iN : fuck1iN) : fuck1iN

;; test.spectec:3365.6-3365.18
relation ibitselect__is_wf: `%%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, iN_1 : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3365.6-3365.18
  rule ibitselect__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, iN_1 : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(N, iN, iN_0, iN_1, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- wf_uN: `%%`(N, iN_1)
    -- if (ret_val = $ibitselect_(N, iN, iN_0, iN_1))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3366.1-3366.59
def $irelaxed_laneselect_(N : fuck1N, iN : fuck1iN, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*

;; test.spectec:3366.6-3366.27
relation irelaxed_laneselect__is_wf: `%%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, iN_1 : fuck1iN, `ret_val*` : fuck6fuck1iN*)
  ;; test.spectec:3366.6-3366.27
  rule irelaxed_laneselect__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, iN_1 : fuck1iN, `ret_val*` : fuck6fuck1iN*}:
    `%%%%%`(N, iN, iN_0, iN_1, `ret_val*`)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- wf_uN: `%%`(N, iN_1)
    -- if (`ret_val*` = $irelaxed_laneselect_(N, iN, iN_0, iN_1))
    -- (wf_uN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3368.1-3368.27
def $ieqz_(N : fuck1N, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3452.1-3452.36
  def $ieqz_{N : fuck3nat, i_1 : fuck1uN}(N, i_1) = `%`_u32($bool((i_1!`%`_uN.0 = 0)))

;; test.spectec:3368.6-3368.12
relation ieqz__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3368.6-3368.12
  rule ieqz__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1u32}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ieqz_(N, iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3369.1-3369.27
def $inez_(N : fuck1N, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3454.1-3454.38
  def $inez_{N : fuck3nat, i_1 : fuck1uN}(N, i_1) = `%`_u32($bool((i_1!`%`_uN.0 =/= 0)))

;; test.spectec:3369.6-3369.12
relation inez__is_wf: `%%%`fuck5(N : fuck1N, iN : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3369.6-3369.12
  rule inez__is_wf_0{N : fuck1N, iN : fuck1iN, ret_val : fuck1u32}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $inez_(N, iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3371.1-3371.33
def $ieq_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3457.1-3457.42
  def $ieq_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, i_1, i_2) = `%`_u32($bool((i_1 = i_2)))

;; test.spectec:3371.6-3371.11
relation ieq__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3371.6-3371.11
  rule ieq__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ieq_(N, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3372.1-3372.33
def $ine_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3459.1-3459.44
  def $ine_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, i_1, i_2) = `%`_u32($bool((i_1 =/= i_2)))

;; test.spectec:3372.6-3372.11
relation ine__is_wf: `%%%%`fuck5(N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3372.6-3372.11
  rule ine__is_wf_0{N : fuck1N, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ine_(N, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3373.1-3373.75
def $ilt_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3461.1-3461.45
  def $ilt_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 < i_2!`%`_uN.0)))
  ;; test.spectec:3462.1-3462.71
  def $ilt_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) < $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:3373.6-3373.11
relation ilt__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3373.6-3373.11
  rule ilt__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ilt_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3374.1-3374.75
def $igt_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3464.1-3464.45
  def $igt_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 > i_2!`%`_uN.0)))
  ;; test.spectec:3465.1-3465.71
  def $igt_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) > $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:3374.6-3374.11
relation igt__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3374.6-3374.11
  rule igt__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $igt_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3375.1-3375.75
def $ile_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3467.1-3467.46
  def $ile_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 <= i_2!`%`_uN.0)))
  ;; test.spectec:3468.1-3468.72
  def $ile_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) <= $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:3375.6-3375.11
relation ile__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3375.6-3375.11
  rule ile__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ile_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3376.1-3376.75
def $ige_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32
  ;; test.spectec:3470.1-3470.46
  def $ige_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 >= i_2!`%`_uN.0)))
  ;; test.spectec:3471.1-3471.72
  def $ige_{N : fuck3nat, i_1 : fuck1uN, i_2 : fuck1uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) >= $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:3376.6-3376.11
relation ige__is_wf: `%%%%%`fuck5(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32)
  ;; test.spectec:3376.6-3376.11
  rule ige__is_wf_0{N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN_0 : fuck1iN, ret_val : fuck1u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ige_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3476.1-3476.30
def $fabs_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3476.6-3476.12
relation fabs__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3476.6-3476.12
  rule fabs__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fabs_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3477.1-3477.30
def $fneg_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3477.6-3477.12
relation fneg__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3477.6-3477.12
  rule fneg__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fneg_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3478.1-3478.31
def $fsqrt_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3478.6-3478.13
relation fsqrt__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3478.6-3478.13
  rule fsqrt__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fsqrt_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3479.1-3479.31
def $fceil_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3479.6-3479.13
relation fceil__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3479.6-3479.13
  rule fceil__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fceil_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3480.1-3480.32
def $ffloor_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3480.6-3480.14
relation ffloor__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3480.6-3480.14
  rule ffloor__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $ffloor_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3481.1-3481.32
def $ftrunc_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3481.6-3481.14
relation ftrunc__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3481.6-3481.14
  rule ftrunc__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $ftrunc_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3482.1-3482.34
def $fnearest_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3482.6-3482.16
relation fnearest__is_wf: `%%%`fuck5(N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3482.6-3482.16
  rule fnearest__is_wf_0{N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fnearest_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3484.1-3484.37
def $fadd_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3484.6-3484.12
relation fadd__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3484.6-3484.12
  rule fadd__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fadd_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3485.1-3485.37
def $fsub_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3485.6-3485.12
relation fsub__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3485.6-3485.12
  rule fsub__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fsub_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3486.1-3486.37
def $fmul_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3486.6-3486.12
relation fmul__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3486.6-3486.12
  rule fmul__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fmul_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3487.1-3487.37
def $fdiv_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3487.6-3487.12
relation fdiv__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3487.6-3487.12
  rule fdiv__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fdiv_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3488.1-3488.37
def $fmin_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3488.6-3488.12
relation fmin__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3488.6-3488.12
  rule fmin__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fmin_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3489.1-3489.37
def $fmax_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3489.6-3489.12
relation fmax__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3489.6-3489.12
  rule fmax__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fmax_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3490.1-3490.38
def $fpmin_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3490.6-3490.13
relation fpmin__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3490.6-3490.13
  rule fpmin__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fpmin_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3491.1-3491.38
def $fpmax_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3491.6-3491.13
relation fpmax__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3491.6-3491.13
  rule fpmax__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fpmax_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3492.1-3492.82
def $frelaxed_min_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3492.6-3492.20
relation frelaxed_min__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3492.6-3492.20
  rule frelaxed_min__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $frelaxed_min_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3493.1-3493.82
def $frelaxed_max_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3493.6-3493.20
relation frelaxed_max__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3493.6-3493.20
  rule frelaxed_max__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $frelaxed_max_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3494.1-3494.42
def $fcopysign_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3494.6-3494.17
relation fcopysign__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3494.6-3494.17
  rule fcopysign__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fcopysign_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3496.1-3496.33
def $feq_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32

;; test.spectec:3496.6-3496.11
relation feq__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32)
  ;; test.spectec:3496.6-3496.11
  rule feq__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $feq_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3497.1-3497.33
def $fne_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32

;; test.spectec:3497.6-3497.11
relation fne__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32)
  ;; test.spectec:3497.6-3497.11
  rule fne__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fne_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3498.1-3498.33
def $flt_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32

;; test.spectec:3498.6-3498.11
relation flt__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32)
  ;; test.spectec:3498.6-3498.11
  rule flt__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $flt_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3499.1-3499.33
def $fgt_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32

;; test.spectec:3499.6-3499.11
relation fgt__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32)
  ;; test.spectec:3499.6-3499.11
  rule fgt__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fgt_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3500.1-3500.33
def $fle_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32

;; test.spectec:3500.6-3500.11
relation fle__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32)
  ;; test.spectec:3500.6-3500.11
  rule fle__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fle_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3501.1-3501.33
def $fge_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32

;; test.spectec:3501.6-3501.11
relation fge__is_wf: `%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32)
  ;; test.spectec:3501.6-3501.11
  rule fge__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, ret_val : fuck1u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fge_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3503.1-3503.91
def $frelaxed_madd_(N : fuck1N, fN : fuck1fN, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3503.6-3503.21
relation frelaxed_madd__is_wf: `%%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, fN_1 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3503.6-3503.21
  rule frelaxed_madd__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, fN_1 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%%`(N, fN, fN_0, fN_1, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- wf_fN: `%%`(N, fN_1)
    -- if (`ret_val*` = $frelaxed_madd_(N, fN, fN_0, fN_1))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3504.1-3504.92
def $frelaxed_nmadd_(N : fuck1N, fN : fuck1fN, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3504.6-3504.22
relation frelaxed_nmadd__is_wf: `%%%%%`fuck5(N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, fN_1 : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3504.6-3504.22
  rule frelaxed_nmadd__is_wf_0{N : fuck1N, fN : fuck1fN, fN_0 : fuck1fN, fN_1 : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%%`(N, fN, fN_0, fN_1, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- wf_fN: `%%`(N, fN_1)
    -- if (`ret_val*` = $frelaxed_nmadd_(N, fN, fN_0, fN_1))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3542.1-3542.33
def $wrap__(M : fuck1M, N : fuck1N, iN : fuck1iN) : fuck1iN

;; test.spectec:3542.6-3542.13
relation wrap___is_wf: `%%%%`fuck5(M : fuck1M, N : fuck1N, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3542.6-3542.13
  rule wrap___is_wf_0{M : fuck1M, N : fuck1N, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(M, N, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $wrap__(M, N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3543.1-3543.90
def $extend__(M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN) : fuck1iN

;; test.spectec:3543.6-3543.15
relation extend___is_wf: `%%%%%`fuck5(M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3543.6-3543.15
  rule extend___is_wf_0{M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(M, N, sx, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $extend__(M, N, sx, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3544.1-3544.89
def $trunc__(M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN) : fuck6fuck1iN?

;; test.spectec:3544.6-3544.14
relation trunc___is_wf: `%%%%%`fuck5(M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN, `ret_val?` : fuck6fuck1iN?)
  ;; test.spectec:3544.6-3544.14
  rule trunc___is_wf_0{M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN, `ret_val?` : fuck6fuck1iN?}:
    `%%%%%`(M, N, sx, fN, `ret_val?`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val?` = $trunc__(M, N, sx, fN))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:3545.1-3545.94
def $trunc_sat__(M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN) : fuck6fuck1iN?

;; test.spectec:3545.6-3545.18
relation trunc_sat___is_wf: `%%%%%`fuck5(M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN, `ret_val?` : fuck6fuck1iN?)
  ;; test.spectec:3545.6-3545.18
  rule trunc_sat___is_wf_0{M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN, `ret_val?` : fuck6fuck1iN?}:
    `%%%%%`(M, N, sx, fN, `ret_val?`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val?` = $trunc_sat__(M, N, sx, fN))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:3546.1-3546.98
def $relaxed_trunc__(M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN) : fuck6fuck1iN?

;; test.spectec:3546.6-3546.22
relation relaxed_trunc___is_wf: `%%%%%`fuck5(M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN, `ret_val?` : fuck6fuck1iN?)
  ;; test.spectec:3546.6-3546.22
  rule relaxed_trunc___is_wf_0{M : fuck1M, N : fuck1N, sx : fuck1sx, fN : fuck1fN, `ret_val?` : fuck6fuck1iN?}:
    `%%%%%`(M, N, sx, fN, `ret_val?`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val?` = $relaxed_trunc__(M, N, sx, fN))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:3547.1-3547.36
def $demote__(M : fuck1M, N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3547.6-3547.15
relation demote___is_wf: `%%%%`fuck5(M : fuck1M, N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3547.6-3547.15
  rule demote___is_wf_0{M : fuck1M, N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(M, N, fN, `ret_val*`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val*` = $demote__(M, N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3548.1-3548.37
def $promote__(M : fuck1M, N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*

;; test.spectec:3548.6-3548.16
relation promote___is_wf: `%%%%`fuck5(M : fuck1M, N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*)
  ;; test.spectec:3548.6-3548.16
  rule promote___is_wf_0{M : fuck1M, N : fuck1N, fN : fuck1fN, `ret_val*` : fuck6fuck1fN*}:
    `%%%%`(M, N, fN, `ret_val*`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val*` = $promote__(M, N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3549.1-3549.91
def $convert__(M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN) : fuck1fN

;; test.spectec:3549.6-3549.16
relation convert___is_wf: `%%%%%`fuck5(M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1fN)
  ;; test.spectec:3549.6-3549.16
  rule convert___is_wf_0{M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1fN}:
    `%%%%%`(M, N, sx, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $convert__(M, N, sx, iN))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:3550.1-3550.88
def $narrow__(M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN) : fuck1iN

;; test.spectec:3550.6-3550.15
relation narrow___is_wf: `%%%%%`fuck5(M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3550.6-3550.15
  rule narrow___is_wf_0{M : fuck1M, N : fuck1N, sx : fuck1sx, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%%%`(M, N, sx, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $narrow__(M, N, sx, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3552.1-3552.76
def $reinterpret__(numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, num_ : fuck1num_) : fuck1num_

;; test.spectec:3552.6-3552.20
relation reinterpret___is_wf: `%%%%`fuck5(numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, num_ : fuck1num_, ret_val : fuck1num_)
  ;; test.spectec:3552.6-3552.20
  rule reinterpret___is_wf_0{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, num_ : fuck1num_, ret_val : fuck1num_}:
    `%%%%`(numtype_1, numtype_2, num_, ret_val)
    -- wf_num_: `%%`(numtype_1, num_)
    -- if (ret_val = $reinterpret__(numtype_1, numtype_2, num_))
    -- wf_num_: `%%`(numtype_2, ret_val)

;; test.spectec:3572.1-3573.49
def $lpacknum_(lanetype : fuck1lanetype, num_ : fuck1num_) : fuck1lane_
  ;; test.spectec:3577.1-3577.31
  def $lpacknum_{numtype : fuck1numtype, c : fuck1num_}((numtype : fuck1numtype <: fuck1lanetype), c) = mk_lane__0_lane_(numtype, c)
  ;; test.spectec:3578.1-3578.86
  def $lpacknum_{packtype : fuck1packtype, c : fuck1uN}((packtype : fuck1packtype <: fuck1lanetype), mk_num__0_num_(I32_Inn, c)) = mk_lane__1_lane_(packtype, $wrap__($size($lunpack((packtype : fuck1packtype <: fuck1lanetype))), $psize(packtype), c))

;; test.spectec:3572.6-3572.16
relation lpacknum__is_wf: `%%%`fuck5(lanetype : fuck1lanetype, num_ : fuck1num_, ret_val : fuck1lane_)
  ;; test.spectec:3572.6-3572.16
  rule lpacknum__is_wf_0{lanetype : fuck1lanetype, num_ : fuck1num_, ret_val : fuck1lane_}:
    `%%%`(lanetype, num_, ret_val)
    -- wf_num_: `%%`($lunpack(lanetype), num_)
    -- if (ret_val = $lpacknum_(lanetype, num_))
    -- wf_lane_: `%%`(lanetype, ret_val)

;; test.spectec:3574.1-3575.49
def $cpacknum_(storagetype : fuck1storagetype, lit_ : fuck1lit_) : fuck1lit_
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{consttype : fuck1consttype, c : fuck1lit_}((consttype : fuck1consttype <: fuck1storagetype), c) = c
  ;; test.spectec:3581.1-3581.86
  def $cpacknum_{packtype : fuck1packtype, c : fuck1uN}((packtype : fuck1packtype <: fuck1storagetype), mk_lit__0_lit_(I32_numtype, mk_num__0_num_(I32_Inn, c))) = mk_lit__2_lit_(packtype, $wrap__($size($lunpack((packtype : fuck1packtype <: fuck1lanetype))), $psize(packtype), c))

;; test.spectec:3574.6-3574.16
relation cpacknum__is_wf: `%%%`fuck5(storagetype : fuck1storagetype, lit_ : fuck1lit_, ret_val : fuck1lit_)
  ;; test.spectec:3574.6-3574.16
  rule cpacknum__is_wf_0{storagetype : fuck1storagetype, lit_ : fuck1lit_, ret_val : fuck1lit_}:
    `%%%`(storagetype, lit_, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- wf_lit_: `%%`(($cunpack(storagetype) : fuck1consttype <: fuck1storagetype), lit_)
    -- if (ret_val = $cpacknum_(storagetype, lit_))
    -- wf_lit_: `%%`(storagetype, ret_val)

;; test.spectec:3584.1-3585.53
def $lunpacknum_(lanetype : fuck1lanetype, lane_ : fuck1lane_) : fuck1num_
  ;; test.spectec:3589.1-3589.33
  def $lunpacknum_{numtype : fuck1numtype, c : fuck1num_}((numtype : fuck1numtype <: fuck1lanetype), mk_lane__0_lane_(numtype, c)) = c
  ;; test.spectec:3590.1-3590.93
  def $lunpacknum_{packtype : fuck1packtype, c : fuck1uN}((packtype : fuck1packtype <: fuck1lanetype), mk_lane__1_lane_(packtype, c)) = mk_num__0_num_(I32_Inn, $extend__($psize(packtype), $size($lunpack((packtype : fuck1packtype <: fuck1lanetype))), U_sx, c))

;; test.spectec:3584.6-3584.18
relation lunpacknum__is_wf: `%%%`fuck5(lanetype : fuck1lanetype, lane_ : fuck1lane_, ret_val : fuck1num_)
  ;; test.spectec:3584.6-3584.18
  rule lunpacknum__is_wf_0{lanetype : fuck1lanetype, lane_ : fuck1lane_, ret_val : fuck1num_}:
    `%%%`(lanetype, lane_, ret_val)
    -- wf_lane_: `%%`(lanetype, lane_)
    -- if (ret_val = $lunpacknum_(lanetype, lane_))
    -- wf_num_: `%%`($lunpack(lanetype), ret_val)

;; test.spectec:3586.1-3587.53
def $cunpacknum_(storagetype : fuck1storagetype, lit_ : fuck1lit_) : fuck1lit_
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{consttype : fuck1consttype, c : fuck1lit_}((consttype : fuck1consttype <: fuck1storagetype), c) = c
  ;; test.spectec:3593.1-3593.93
  def $cunpacknum_{packtype : fuck1packtype, c : fuck1uN}((packtype : fuck1packtype <: fuck1storagetype), mk_lit__2_lit_(packtype, c)) = mk_lit__0_lit_(I32_numtype, mk_num__0_num_(I32_Inn, $extend__($psize(packtype), $size($lunpack((packtype : fuck1packtype <: fuck1lanetype))), U_sx, c)))

;; test.spectec:3586.6-3586.18
relation cunpacknum__is_wf: `%%%`fuck5(storagetype : fuck1storagetype, lit_ : fuck1lit_, ret_val : fuck1lit_)
  ;; test.spectec:3586.6-3586.18
  rule cunpacknum__is_wf_0{storagetype : fuck1storagetype, lit_ : fuck1lit_, ret_val : fuck1lit_}:
    `%%%`(storagetype, lit_, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- wf_lit_: `%%`(storagetype, lit_)
    -- if (ret_val = $cunpacknum_(storagetype, lit_))
    -- wf_lit_: `%%`(($cunpack(storagetype) : fuck1consttype <: fuck1storagetype), ret_val)

;; test.spectec:3598.1-3599.28
def $unop_(numtype : fuck1numtype, unop_ : fuck1unop_, num_ : fuck1num_) : fuck6fuck1num_*
  ;; test.spectec:3609.1-3609.50
  def $unop_{Inn : fuck1addrtype, i : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_unop__0_unop_(Inn, CLZ_unop_Inn), mk_num__0_num_(Inn, i)) = [mk_num__0_num_(Inn, $iclz_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i))]
  ;; test.spectec:3610.1-3610.50
  def $unop_{Inn : fuck1addrtype, i : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_unop__0_unop_(Inn, CTZ_unop_Inn), mk_num__0_num_(Inn, i)) = [mk_num__0_num_(Inn, $ictz_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i))]
  ;; test.spectec:3611.1-3611.56
  def $unop_{Inn : fuck1addrtype, i : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_unop__0_unop_(Inn, POPCNT_unop_Inn), mk_num__0_num_(Inn, i)) = [mk_num__0_num_(Inn, $ipopcnt_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i))]
  ;; test.spectec:3612.1-3612.64
  def $unop_{Inn : fuck1addrtype, M : fuck3nat, i : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_unop__0_unop_(Inn, EXTEND_unop_Inn(`%`_sz(M))), mk_num__0_num_(Inn, i)) = [mk_num__0_num_(Inn, $iextend_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), M, S_sx, i))]
  ;; test.spectec:3614.1-3614.50
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, ABS_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fabs_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}
  ;; test.spectec:3615.1-3615.50
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, NEG_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fneg_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}
  ;; test.spectec:3616.1-3616.52
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, SQRT_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fsqrt_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}
  ;; test.spectec:3617.1-3617.52
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, CEIL_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fceil_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}
  ;; test.spectec:3618.1-3618.54
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, FLOOR_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $ffloor_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}
  ;; test.spectec:3619.1-3619.54
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, TRUNC_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $ftrunc_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}
  ;; test.spectec:3620.1-3620.58
  def $unop_{Fnn : fuck1Fnn, f : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_unop__1_unop_(Fnn, NEAREST_unop_Fnn), mk_num__1_num_(Fnn, f)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fnearest_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f)}

;; test.spectec:3598.6-3598.12
relation unop__is_wf: `%%%%`fuck5(numtype : fuck1numtype, unop_ : fuck1unop_, num_ : fuck1num_, `ret_val*` : fuck6fuck1num_*)
  ;; test.spectec:3598.6-3598.12
  rule unop__is_wf_0{numtype : fuck1numtype, unop_ : fuck1unop_, num_ : fuck1num_, `ret_val*` : fuck6fuck1num_*}:
    `%%%%`(numtype, unop_, num_, `ret_val*`)
    -- wf_unop_: `%%`(numtype, unop_)
    -- wf_num_: `%%`(numtype, num_)
    -- if (`ret_val*` = $unop_(numtype, unop_, num_))
    -- (wf_num_: `%%`(numtype, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3600.1-3601.32
def $binop_(numtype : fuck1numtype, binop_ : fuck1binop_, num_ : fuck1num_, num_ : fuck1num_) : fuck6fuck1num_*
  ;; test.spectec:3622.1-3622.65
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, ADD_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $iadd_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3623.1-3623.65
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, SUB_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $isub_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3624.1-3624.65
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, MUL_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $imul_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3625.1-3625.72
  def $binop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, DIV_binop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = mk_num__0_num_(Inn, iter_0)*{iter_0 <- lift($idiv_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, i_2))}
  ;; test.spectec:3626.1-3626.72
  def $binop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, REM_binop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = mk_num__0_num_(Inn, iter_0)*{iter_0 <- lift($irem_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, i_2))}
  ;; test.spectec:3627.1-3627.65
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, AND_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $iand_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3628.1-3628.63
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, OR_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $ior_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3629.1-3629.65
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, XOR_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $ixor_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3630.1-3630.65
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, SHL_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $ishl_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, `%`_u32(i_2!`%`_uN.0)))]
  ;; test.spectec:3631.1-3631.72
  def $binop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, SHR_binop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $ishr_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, `%`_u32(i_2!`%`_uN.0)))]
  ;; test.spectec:3632.1-3632.67
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, ROTL_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $irotl_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3633.1-3633.67
  def $binop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_binop__0_binop_(Inn, ROTR_binop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = [mk_num__0_num_(Inn, $irotr_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2))]
  ;; test.spectec:3635.1-3635.65
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, ADD_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fadd_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}
  ;; test.spectec:3636.1-3636.65
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, SUB_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fsub_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}
  ;; test.spectec:3637.1-3637.65
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, MUL_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fmul_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}
  ;; test.spectec:3638.1-3638.65
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, DIV_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fdiv_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}
  ;; test.spectec:3639.1-3639.65
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, MIN_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fmin_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}
  ;; test.spectec:3640.1-3640.65
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, MAX_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fmax_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}
  ;; test.spectec:3641.1-3641.75
  def $binop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_binop__1_binop_(Fnn, COPYSIGN_binop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = mk_num__1_num_(Fnn, iter_0)*{iter_0 <- $fcopysign_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)}

;; test.spectec:3600.6-3600.13
relation binop__is_wf: `%%%%%`fuck5(numtype : fuck1numtype, binop_ : fuck1binop_, num_ : fuck1num_, num__0 : fuck1num_, `ret_val*` : fuck6fuck1num_*)
  ;; test.spectec:3600.6-3600.13
  rule binop__is_wf_0{numtype : fuck1numtype, binop_ : fuck1binop_, num_ : fuck1num_, num__0 : fuck1num_, `ret_val*` : fuck6fuck1num_*}:
    `%%%%%`(numtype, binop_, num_, num__0, `ret_val*`)
    -- wf_binop_: `%%`(numtype, binop_)
    -- wf_num_: `%%`(numtype, num_)
    -- wf_num_: `%%`(numtype, num__0)
    -- if (`ret_val*` = $binop_(numtype, binop_, num_, num__0))
    -- (wf_num_: `%%`(numtype, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3602.1-3603.28
def $testop_(numtype : fuck1numtype, testop_ : fuck1testop_, num_ : fuck1num_) : fuck1u32
  ;; test.spectec:3643.1-3643.52
  def $testop_{Inn : fuck1addrtype, i : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_testop__0_testop_(Inn, EQZ_testop_Inn), mk_num__0_num_(Inn, i)) = $ieqz_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i)

;; test.spectec:3602.6-3602.14
relation testop__is_wf: `%%%%`fuck5(numtype : fuck1numtype, testop_ : fuck1testop_, num_ : fuck1num_, ret_val : fuck1u32)
  ;; test.spectec:3602.6-3602.14
  rule testop__is_wf_0{numtype : fuck1numtype, testop_ : fuck1testop_, num_ : fuck1num_, ret_val : fuck1u32}:
    `%%%%`(numtype, testop_, num_, ret_val)
    -- wf_testop_: `%%`(numtype, testop_)
    -- wf_num_: `%%`(numtype, num_)
    -- if (ret_val = $testop_(numtype, testop_, num_))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3604.1-3605.32
def $relop_(numtype : fuck1numtype, relop_ : fuck1relop_, num_ : fuck1num_, num_ : fuck1num_) : fuck1u32
  ;; test.spectec:3645.1-3645.63
  def $relop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_relop__0_relop_(Inn, EQ_relop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = $ieq_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2)
  ;; test.spectec:3646.1-3646.63
  def $relop_{Inn : fuck1addrtype, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_relop__0_relop_(Inn, NE_relop_Inn), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = $ine_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), i_1, i_2)
  ;; test.spectec:3647.1-3647.70
  def $relop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_relop__0_relop_(Inn, LT_relop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = $ilt_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, i_2)
  ;; test.spectec:3648.1-3648.70
  def $relop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_relop__0_relop_(Inn, GT_relop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = $igt_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, i_2)
  ;; test.spectec:3649.1-3649.70
  def $relop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_relop__0_relop_(Inn, LE_relop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = $ile_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, i_2)
  ;; test.spectec:3650.1-3650.70
  def $relop_{Inn : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN, i_2 : fuck1uN}((Inn : fuck1addrtype <: fuck1numtype), mk_relop__0_relop_(Inn, GE_relop_Inn(sx)), mk_num__0_num_(Inn, i_1), mk_num__0_num_(Inn, i_2)) = $ige_($sizenn((Inn : fuck1addrtype <: fuck1numtype)), sx, i_1, i_2)
  ;; test.spectec:3652.1-3652.63
  def $relop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_relop__1_relop_(Fnn, EQ_relop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = $feq_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)
  ;; test.spectec:3653.1-3653.63
  def $relop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_relop__1_relop_(Fnn, NE_relop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = $fne_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)
  ;; test.spectec:3654.1-3654.63
  def $relop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_relop__1_relop_(Fnn, LT_relop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = $flt_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)
  ;; test.spectec:3655.1-3655.63
  def $relop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_relop__1_relop_(Fnn, GT_relop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = $fgt_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)
  ;; test.spectec:3656.1-3656.63
  def $relop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_relop__1_relop_(Fnn, LE_relop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = $fle_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)
  ;; test.spectec:3657.1-3657.63
  def $relop_{Fnn : fuck1Fnn, f_1 : fuck1fN, f_2 : fuck1fN}((Fnn : fuck1Fnn <: fuck1numtype), mk_relop__1_relop_(Fnn, GE_relop_Fnn), mk_num__1_num_(Fnn, f_1), mk_num__1_num_(Fnn, f_2)) = $fge_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), f_1, f_2)

;; test.spectec:3604.6-3604.13
relation relop__is_wf: `%%%%%`fuck5(numtype : fuck1numtype, relop_ : fuck1relop_, num_ : fuck1num_, num__0 : fuck1num_, ret_val : fuck1u32)
  ;; test.spectec:3604.6-3604.13
  rule relop__is_wf_0{numtype : fuck1numtype, relop_ : fuck1relop_, num_ : fuck1num_, num__0 : fuck1num_, ret_val : fuck1u32}:
    `%%%%%`(numtype, relop_, num_, num__0, ret_val)
    -- wf_relop_: `%%`(numtype, relop_)
    -- wf_num_: `%%`(numtype, num_)
    -- wf_num_: `%%`(numtype, num__0)
    -- if (ret_val = $relop_(numtype, relop_, num_, num__0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3606.1-3607.32
def $cvtop__(numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, cvtop__ : fuck1cvtop__, num_ : fuck1num_) : fuck6fuck1num_*
  ;; test.spectec:3659.1-3660.55
  def $cvtop__{Inn_1 : fuck1addrtype, Inn_2 : fuck1addrtype, sx : fuck1sx, i_1 : fuck1uN}((Inn_1 : fuck1addrtype <: fuck1numtype), (Inn_2 : fuck1addrtype <: fuck1numtype), mk_cvtop___0_cvtop__(Inn_1, Inn_2, EXTEND_cvtop__Inn_1_Inn_2(sx)), mk_num__0_num_(Inn_1, i_1)) = [mk_num__0_num_(Inn_2, $extend__($sizenn1((Inn_1 : fuck1addrtype <: fuck1numtype)), $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)), sx, i_1))]
  ;; test.spectec:3661.1-3662.49
  def $cvtop__{Inn_1 : fuck1addrtype, Inn_2 : fuck1addrtype, i_1 : fuck1uN}((Inn_1 : fuck1addrtype <: fuck1numtype), (Inn_2 : fuck1addrtype <: fuck1numtype), mk_cvtop___0_cvtop__(Inn_1, Inn_2, WRAP_cvtop__Inn_1_Inn_2), mk_num__0_num_(Inn_1, i_1)) = [mk_num__0_num_(Inn_2, $wrap__($sizenn1((Inn_1 : fuck1addrtype <: fuck1numtype)), $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)), i_1))]
  ;; test.spectec:3663.1-3664.54
  def $cvtop__{Fnn_1 : fuck1Fnn, Inn_2 : fuck1addrtype, sx : fuck1sx, f_1 : fuck1fN}((Fnn_1 : fuck1Fnn <: fuck1numtype), (Inn_2 : fuck1addrtype <: fuck1numtype), mk_cvtop___2_cvtop__(Fnn_1, Inn_2, TRUNC_cvtop__Fnn_1_Inn_2(sx)), mk_num__1_num_(Fnn_1, f_1)) = mk_num__0_num_(Inn_2, iter_0)*{iter_0 <- lift($trunc__($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)), $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)), sx, f_1))}
  ;; test.spectec:3665.1-3666.58
  def $cvtop__{Fnn_1 : fuck1Fnn, Inn_2 : fuck1addrtype, sx : fuck1sx, f_1 : fuck1fN}((Fnn_1 : fuck1Fnn <: fuck1numtype), (Inn_2 : fuck1addrtype <: fuck1numtype), mk_cvtop___2_cvtop__(Fnn_1, Inn_2, TRUNC_SAT_cvtop__Fnn_1_Inn_2(sx)), mk_num__1_num_(Fnn_1, f_1)) = mk_num__0_num_(Inn_2, iter_0)*{iter_0 <- lift($trunc_sat__($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)), $sizenn2((Inn_2 : fuck1addrtype <: fuck1numtype)), sx, f_1))}
  ;; test.spectec:3667.1-3668.56
  def $cvtop__{Inn_1 : fuck1addrtype, Fnn_2 : fuck1Fnn, sx : fuck1sx, i_1 : fuck1uN}((Inn_1 : fuck1addrtype <: fuck1numtype), (Fnn_2 : fuck1Fnn <: fuck1numtype), mk_cvtop___1_cvtop__(Inn_1, Fnn_2, CONVERT_cvtop__Inn_1_Fnn_2(sx)), mk_num__0_num_(Inn_1, i_1)) = [mk_num__1_num_(Fnn_2, $convert__($sizenn1((Inn_1 : fuck1addrtype <: fuck1numtype)), $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)), sx, i_1))]
  ;; test.spectec:3669.1-3670.52
  def $cvtop__{Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn, f_1 : fuck1fN}((Fnn_1 : fuck1Fnn <: fuck1numtype), (Fnn_2 : fuck1Fnn <: fuck1numtype), mk_cvtop___3_cvtop__(Fnn_1, Fnn_2, PROMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(Fnn_1, f_1)) = mk_num__1_num_(Fnn_2, iter_0)*{iter_0 <- $promote__($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)), $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)), f_1)}
  ;; test.spectec:3671.1-3672.51
  def $cvtop__{Fnn_1 : fuck1Fnn, Fnn_2 : fuck1Fnn, f_1 : fuck1fN}((Fnn_1 : fuck1Fnn <: fuck1numtype), (Fnn_2 : fuck1Fnn <: fuck1numtype), mk_cvtop___3_cvtop__(Fnn_1, Fnn_2, DEMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(Fnn_1, f_1)) = mk_num__1_num_(Fnn_2, iter_0)*{iter_0 <- $demote__($sizenn1((Fnn_1 : fuck1Fnn <: fuck1numtype)), $sizenn2((Fnn_2 : fuck1Fnn <: fuck1numtype)), f_1)}
  ;; test.spectec:3673.1-3674.70
  def $cvtop__{Inn_1 : fuck1addrtype, Fnn_2 : fuck1Fnn, i_1 : fuck1uN}((Inn_1 : fuck1addrtype <: fuck1numtype), (Fnn_2 : fuck1Fnn <: fuck1numtype), mk_cvtop___1_cvtop__(Inn_1, Fnn_2, REINTERPRET_cvtop__Inn_1_Fnn_2), mk_num__0_num_(Inn_1, i_1)) = [$reinterpret__((Inn_1 : fuck1addrtype <: fuck1numtype), (Fnn_2 : fuck1Fnn <: fuck1numtype), mk_num__0_num_(Inn_1, i_1))]
    -- if ($size((Inn_1 : fuck1addrtype <: fuck1numtype)) = $size((Fnn_2 : fuck1Fnn <: fuck1numtype)))
  ;; test.spectec:3675.1-3676.70
  def $cvtop__{Fnn_1 : fuck1Fnn, Inn_2 : fuck1addrtype, f_1 : fuck1fN}((Fnn_1 : fuck1Fnn <: fuck1numtype), (Inn_2 : fuck1addrtype <: fuck1numtype), mk_cvtop___2_cvtop__(Fnn_1, Inn_2, REINTERPRET_cvtop__Fnn_1_Inn_2), mk_num__1_num_(Fnn_1, f_1)) = [$reinterpret__((Fnn_1 : fuck1Fnn <: fuck1numtype), (Inn_2 : fuck1addrtype <: fuck1numtype), mk_num__1_num_(Fnn_1, f_1))]
    -- if ($size((Fnn_1 : fuck1Fnn <: fuck1numtype)) = $size((Inn_2 : fuck1addrtype <: fuck1numtype)))

;; test.spectec:3606.6-3606.14
relation cvtop___is_wf: `%%%%%`fuck5(numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, cvtop__ : fuck1cvtop__, num_ : fuck1num_, `ret_val*` : fuck6fuck1num_*)
  ;; test.spectec:3606.6-3606.14
  rule cvtop___is_wf_0{numtype_1 : fuck1numtype, numtype_2 : fuck1numtype, cvtop__ : fuck1cvtop__, num_ : fuck1num_, `ret_val*` : fuck6fuck1num_*}:
    `%%%%%`(numtype_1, numtype_2, cvtop__, num_, `ret_val*`)
    -- wf_cvtop__: `%%%`(numtype_1, numtype_2, cvtop__)
    -- wf_num_: `%%`(numtype_1, num_)
    -- if (`ret_val*` = $cvtop__(numtype_1, numtype_2, cvtop__, num_))
    -- (wf_num_: `%%`(numtype_2, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3694.1-3694.84
def $lanes_(shape : fuck1shape, vec_ : fuck1vec_) : fuck6fuck1lane_*

;; test.spectec:3694.6-3694.13
relation lanes__is_wf: `%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1lane_*)
  ;; test.spectec:3694.6-3694.13
  rule lanes__is_wf_0{shape : fuck1shape, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1lane_*}:
    `%%%`(shape, vec_, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- if (`ret_val*` = $lanes_(shape, vec_))
    -- (wf_lane_: `%%`($lanetype(shape), ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3696.1-3697.37
def $inv_lanes_(shape : fuck1shape, fuck6fuck1lane_*) : fuck1vec_

;; test.spectec:3696.6-3696.17
relation inv_lanes__is_wf: `%%%`fuck5(shape : fuck1shape, `var_0*` : fuck6fuck1lane_*, ret_val : fuck1vec_)
  ;; test.spectec:3696.6-3696.17
  rule inv_lanes__is_wf_0{shape : fuck1shape, `var_0*` : fuck6fuck1lane_*, ret_val : fuck1vec_}:
    `%%%`(shape, `var_0*`, ret_val)
    -- wf_shape: `%`(shape)
    -- (wf_lane_: `%%`($lanetype(shape), var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_lanes_(shape, `var_0*`))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3703.1-3703.66
def $zeroop(shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__) : fuck6fuck1zero?
  ;; test.spectec:3704.1-3704.60
  def $zeroop{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, half : fuck1half, sx : fuck1sx}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(half, sx))) = ?()
  ;; test.spectec:3705.1-3705.62
  def $zeroop{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, `half?` : fuck6fuck1half?, sx : fuck1sx}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half?{half <- `half?`}, sx))) = ?()
  ;; test.spectec:3706.1-3706.66
  def $zeroop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, sx : fuck1sx, `zero?` : fuck6fuck1zero?}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, zero?{zero <- `zero?`}))) = zero?{zero <- `zero?`}
  ;; test.spectec:3707.1-3707.70
  def $zeroop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, sx : fuck1sx, `zero?` : fuck6fuck1zero?}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, zero?{zero <- `zero?`}))) = zero?{zero <- `zero?`}
  ;; test.spectec:3708.1-3708.58
  def $zeroop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, zero : fuck1zero}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(zero))) = ?(zero)
  ;; test.spectec:3709.1-3709.57
  def $zeroop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2)) = ?()

;; test.spectec:3711.1-3711.66
def $halfop(shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__) : fuck6fuck1half?
  ;; test.spectec:3712.1-3712.61
  def $halfop{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, half : fuck1half, sx : fuck1sx}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(half, sx))) = ?(half)
  ;; test.spectec:3713.1-3713.64
  def $halfop{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, `half?` : fuck6fuck1half?, sx : fuck1sx}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half?{half <- `half?`}, sx))) = half?{half <- `half?`}
  ;; test.spectec:3714.1-3714.64
  def $halfop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, sx : fuck1sx, `zero?` : fuck6fuck1zero?}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, zero?{zero <- `zero?`}))) = ?()
  ;; test.spectec:3715.1-3715.68
  def $halfop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, sx : fuck1sx, `zero?` : fuck6fuck1zero?}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, zero?{zero <- `zero?`}))) = ?()
  ;; test.spectec:3716.1-3716.57
  def $halfop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, zero : fuck1zero}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(zero))) = ?()
  ;; test.spectec:3717.1-3717.57
  def $halfop{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2)) = ?(LOW_half)

;; test.spectec:3719.1-3719.32
def $half(half : fuck1half, nat : fuck3nat, nat : fuck3nat) : fuck3nat
  ;; test.spectec:3720.1-3720.25
  def $half{i : fuck3nat, j : fuck3nat}(LOW_half, i, j) = i
  ;; test.spectec:3721.1-3721.26
  def $half{i : fuck3nat, j : fuck3nat}(HIGH_half, i, j) = j

;; test.spectec:3724.1-3724.46
def $iswizzle_lane_(N : fuck1N, fuck6fuck1iN*, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3727.1-3727.62
  def $iswizzle_lane_{N : fuck3nat, `c*` : fuck6fuck1iN*, i : fuck1uN}(N, c*{c <- `c*`}, i) = (if (i!`%`_uN.0 < |c*{c <- `c*`}|) then c*{c <- `c*`}[i!`%`_uN.0] else `%`_iN(0))

;; test.spectec:3724.6-3724.21
relation iswizzle_lane__is_wf: `%%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1iN*, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3724.6-3724.21
  rule iswizzle_lane__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1iN*, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, `var_0*`, iN, ret_val)
    -- (wf_uN: `%%`(N, var_0))*{var_0 <- `var_0*`}
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $iswizzle_lane_(N, `var_0*`, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3725.1-3725.54
def $irelaxed_swizzle_lane_(N : fuck1N, fuck6fuck1iN*, iN : fuck1iN) : fuck1iN
  ;; test.spectec:3730.1-3730.62
  def $irelaxed_swizzle_lane_{N : fuck3nat, `c*` : fuck6fuck1iN*, i : fuck1uN}(N, c*{c <- `c*`}, i) = (if (i!`%`_uN.0 < |c*{c <- `c*`}|) then c*{c <- `c*`}[i!`%`_uN.0] else (if ($signed_(N, i!`%`_uN.0) < (0 : nat <:> int)) then `%`_iN(0) else $relaxed2($R_swizzle, syntax fuck1iN, `%`_iN(0), c*{c <- `c*`}[(i!`%`_uN.0 \ |c*{c <- `c*`}|)])))

;; test.spectec:3725.6-3725.29
relation irelaxed_swizzle_lane__is_wf: `%%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1iN*, iN : fuck1iN, ret_val : fuck1iN)
  ;; test.spectec:3725.6-3725.29
  rule irelaxed_swizzle_lane__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1iN*, iN : fuck1iN, ret_val : fuck1iN}:
    `%%%%`(N, `var_0*`, iN, ret_val)
    -- (wf_uN: `%%`(N, var_0))*{var_0 <- `var_0*`}
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $irelaxed_swizzle_lane_(N, `var_0*`, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:3738.1-3738.87
def $ivunop_(shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN) : fuck1iN, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3761.1-3763.40
  def $ivunop_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, iN : fuck1iN) : fuck1iN, v_1 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1) = [$inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})]
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)))*{c_1 <- `c_1*`}

;; test.spectec:3738.6-3738.14
relation ivunop__is_wf(def $f_(N : fuck1N, iN : fuck1iN) : fuck1iN): `%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3738.6-3738.14
  rule ivunop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN) : fuck1iN, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%`(shape, vec_, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- if (`ret_val*` = $ivunop_(shape, def $f_, vec_))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3739.1-3739.74
def $fvunop_(shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3765.1-3767.66
  def $fvunop_{Fnn : fuck1Fnn, M : fuck3nat, def $f_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*, v_1 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1) = $inv_lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, iter_0))*{iter_0 <- $f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))))}*{c_1 <- `c_1*`})
    -- (wf_lane_: `%%`((Fnn : fuck1Fnn <: fuck1lanetype), mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, iter_0))))*{iter_0 <- $f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))))}*{c_1 <- `c_1*`}

;; test.spectec:3739.6-3739.14
relation fvunop__is_wf(def $f_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*): `%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3739.6-3739.14
  rule fvunop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN) : fuck6fuck1fN*, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%`(shape, vec_, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- if (`ret_val*` = $fvunop_(shape, def $f_, vec_))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3741.1-3741.107
def $ivbinop_(shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3770.1-3773.45
  def $ivbinop_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2) = [$inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})]
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3741.6-3741.15
relation ivbinop__is_wf(def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN): `%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3741.6-3741.15
  rule ivbinop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1iN, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%`(shape, vec_, vec__0, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (`ret_val*` = $ivbinop_(shape, def $f_, vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3742.1-3742.117
def $ivbinopsx_(shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN, sx : fuck1sx, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3775.1-3778.49
  def $ivbinopsx_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = [$inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})]
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3742.6-3742.17
relation ivbinopsx__is_wf(def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN): `%%%%%`fuck5(shape : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3742.6-3742.17
  rule ivbinopsx__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1iN, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%`(shape, sx, vec_, vec__0, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (`ret_val*` = $ivbinopsx_(shape, def $f_, sx, vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3743.1-3743.106
def $ivbinopsxnd_(shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*, sx : fuck1sx, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3780.1-3783.76
  def $ivbinopsxnd_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, mk_lane__2_lane_(Jnn, iter_0)*{iter_0 <- $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))}*{c_1 <- `c_1*`, c_2 <- `c_2*`})
    -- (wf_lane_: `%%`((Jnn : fuck1Jnn <: fuck1lanetype), mk_lane__2_lane_(Jnn, iter_0)))*{iter_0 <- $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))}*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3743.6-3743.19
relation ivbinopsxnd__is_wf(def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*): `%%%%%`fuck5(shape : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3743.6-3743.19
  rule ivbinopsxnd__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%`(shape, sx, vec_, vec__0, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (`ret_val*` = $ivbinopsxnd_(shape, def $f_, sx, vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3744.1-3744.94
def $fvbinop_(shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3785.1-3788.71
  def $fvbinop_{Fnn : fuck1Fnn, M : fuck3nat, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, iter_0))*{iter_0 <- $f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))), !($proj_num__1(!($proj_lane__0(c_2)))))}*{c_1 <- `c_1*`, c_2 <- `c_2*`})
    -- (wf_lane_: `%%`((Fnn : fuck1Fnn <: fuck1lanetype), mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, iter_0))))*{iter_0 <- $f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))), !($proj_num__1(!($proj_lane__0(c_2)))))}*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3744.6-3744.15
relation fvbinop__is_wf(def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*): `%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3744.6-3744.15
  rule fvbinop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%`(shape, vec_, vec__0, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (`ret_val*` = $fvbinop_(shape, def $f_, vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3746.1-3746.116
def $ivternopnd_(shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*, vec_ : fuck1vec_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3791.1-3795.77
  def $ivternopnd_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*, v_1 : fuck1uN, v_2 : fuck1uN, v_3 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c_3*` : fuck6fuck1lane_*} c_3*{c_3 <- `c_3*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_3)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, mk_lane__2_lane_(Jnn, iter_0)*{iter_0 <- $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)), !($proj_lane__2(c_2)), !($proj_lane__2(c_3)))}*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`})
    -- (wf_lane_: `%%`((Jnn : fuck1Jnn <: fuck1lanetype), mk_lane__2_lane_(Jnn, iter_0)))*{iter_0 <- $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)), !($proj_lane__2(c_2)), !($proj_lane__2(c_3)))}*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`}

;; test.spectec:3746.6-3746.18
relation ivternopnd__is_wf(def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*): `%%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3746.6-3746.18
  rule ivternopnd__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN, iN : fuck1iN) : fuck6fuck1iN*, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%`(shape, vec_, vec__0, vec__1, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (`ret_val*` = $ivternopnd_(shape, def $f_, vec_, vec__0, vec__1))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3747.1-3747.114
def $fvternop_(shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*, vec_ : fuck1vec_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3797.1-3801.76
  def $fvternop_{Fnn : fuck1Fnn, M : fuck3nat, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*, v_1 : fuck1uN, v_2 : fuck1uN, v_3 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c_3*` : fuck6fuck1lane_*} c_3*{c_3 <- `c_3*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_3)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, iter_0))*{iter_0 <- $f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))), !($proj_num__1(!($proj_lane__0(c_2)))), !($proj_num__1(!($proj_lane__0(c_3)))))}*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`})
    -- (wf_lane_: `%%`((Fnn : fuck1Fnn <: fuck1lanetype), mk_lane__0_lane_((Fnn : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn, iter_0))))*{iter_0 <- $f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))), !($proj_num__1(!($proj_lane__0(c_2)))), !($proj_num__1(!($proj_lane__0(c_3)))))}*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`}

;; test.spectec:3747.6-3747.16
relation fvternop__is_wf(def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*): `%%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3747.6-3747.16
  rule fvternop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN, fN : fuck1fN) : fuck6fuck1fN*, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%`(shape, vec_, vec__0, vec__1, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (`ret_val*` = $fvternop_(shape, def $f_, vec_, vec__0, vec__1))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3749.1-3749.90
def $ivrelop_(shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1u32, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3804.1-3807.77
  def $ivrelop_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1u32, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $extend__(1, $lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), S_sx, `%`_iN($f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))!`%`_uN.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`}
    -- (wf_uN: `%%`(1, `%`_uN($f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))!`%`_uN.0)))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3749.6-3749.15
relation ivrelop__is_wf(def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1u32): `%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3749.6-3749.15
  rule ivrelop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, iN : fuck1iN) : fuck1u32, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%`(shape, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivrelop_(shape, def $f_, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3750.1-3750.100
def $ivrelopsx_(shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32, sx : fuck1sx, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3809.1-3812.81
  def $ivrelopsx_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $extend__(1, $lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), S_sx, `%`_iN($f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))!`%`_uN.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`}
    -- (wf_uN: `%%`(1, `%`_uN($f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)), !($proj_lane__2(c_2)))!`%`_uN.0)))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3750.6-3750.17
relation ivrelopsx__is_wf(def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32): `%%%%%`fuck5(shape : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3750.6-3750.17
  rule ivrelopsx__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, iN : fuck1iN) : fuck1u32, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(shape, sx, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivrelopsx_(shape, def $f_, sx, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3751.1-3751.90
def $fvrelop_(shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3814.1-3818.36
  def $fvrelop_{Fnn : fuck1Fnn, M : fuck3nat, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32, v_1 : fuck1uN, v_2 : fuck1uN, Inn : fuck1addrtype}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Inn : fuck1addrtype <: fuck1lanetype), `%`_dim(M)), mk_lane__0_lane_((Inn : fuck1addrtype <: fuck1numtype), mk_num__0_num_(Inn, `%`_uN(c!`%`_uN.0)))*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $extend__(1, $sizenn((Fnn : fuck1Fnn <: fuck1numtype)), S_sx, `%`_iN($f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))), !($proj_num__1(!($proj_lane__0(c_2)))))!`%`_uN.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`}
    -- if ($isize(Inn) = $fsize(Fnn))
    -- wf_shape: `%`(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)))
    -- (wf_uN: `%%`(1, `%`_uN($f_($sizenn((Fnn : fuck1Fnn <: fuck1numtype)), !($proj_num__1(!($proj_lane__0(c_1)))), !($proj_num__1(!($proj_lane__0(c_2)))))!`%`_uN.0)))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3751.6-3751.15
relation fvrelop__is_wf(def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32): `%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3751.6-3751.15
  rule fvrelop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, fN : fuck1fN, fN : fuck1fN) : fuck1u32, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%`(shape, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $fvrelop_(shape, def $f_, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3753.1-3753.99
def $ivshiftop_(shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, u32 : fuck1u32) : fuck1iN, vec_ : fuck1vec_, u32 : fuck1u32) : fuck1vec_
  ;; test.spectec:3821.1-3823.41
  def $ivshiftop_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, iN : fuck1iN, u32 : fuck1u32) : fuck1iN, v_1 : fuck1uN, i : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, i) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1)), i)*{c_1 <- `c_1*`}

;; test.spectec:3753.6-3753.17
relation ivshiftop__is_wf(def $f_(N : fuck1N, iN : fuck1iN, u32 : fuck1u32) : fuck1iN): `%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, u32 : fuck1u32, ret_val : fuck1vec_)
  ;; test.spectec:3753.6-3753.17
  rule ivshiftop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, iN : fuck1iN, u32 : fuck1u32) : fuck1iN, vec_ : fuck1vec_, u32 : fuck1u32, ret_val : fuck1vec_}:
    `%%%%`(shape, vec_, u32, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $ivshiftop_(shape, def $f_, vec_, u32))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3754.1-3754.109
def $ivshiftopsx_(shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32) : fuck1iN, sx : fuck1sx, vec_ : fuck1vec_, u32 : fuck1u32) : fuck1vec_
  ;; test.spectec:3825.1-3827.45
  def $ivshiftopsx_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32) : fuck1iN, sx : fuck1sx, v_1 : fuck1uN, i : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, sx, v_1, i) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)), i)*{c_1 <- `c_1*`}

;; test.spectec:3754.6-3754.19
relation ivshiftopsx__is_wf(def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32) : fuck1iN): `%%%%%`fuck5(shape : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, u32 : fuck1u32, ret_val : fuck1vec_)
  ;; test.spectec:3754.6-3754.19
  rule ivshiftopsx__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, sx : fuck1sx, iN : fuck1iN, u32 : fuck1u32) : fuck1iN, sx : fuck1sx, vec_ : fuck1vec_, u32 : fuck1u32, ret_val : fuck1vec_}:
    `%%%%%`(shape, sx, vec_, u32, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $ivshiftopsx_(shape, def $f_, sx, vec_, u32))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3756.1-3756.43
def $ivbitmaskop_(shape : fuck1shape, vec_ : fuck1vec_) : fuck1u32
  ;; test.spectec:3830.1-3832.72
  def $ivbitmaskop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, c : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1) = $irev_(32, c)
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- if ($ibits_(32, c) = `%`_bit($ilt_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), S_sx, !($proj_lane__2(c_1)), `%`_iN(0))!`%`_uN.0)*{c_1 <- `c_1*`} ++ `%`_bit(0)^(((32 : nat <:> int) - (M : nat <:> int)) : int <:> nat){})
    -- wf_shape: `%`(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)))
    -- (wf_bit: `%`(`%`_bit($ilt_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), S_sx, !($proj_lane__2(c_1)), `%`_iN(0))!`%`_uN.0)))*{c_1 <- `c_1*`}
    -- wf_bit: `%`(`%`_bit(0))

;; test.spectec:3756.6-3756.19
relation ivbitmaskop__is_wf: `%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, ret_val : fuck1u32)
  ;; test.spectec:3756.6-3756.19
  rule ivbitmaskop__is_wf_0{shape : fuck1shape, vec_ : fuck1vec_, ret_val : fuck1u32}:
    `%%%`(shape, vec_, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- if (ret_val = $ivbitmaskop_(shape, vec_))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3757.1-3757.110
def $ivswizzlop_(shape : fuck1shape, def $f_(N : fuck1N, fuck6fuck1iN*, iN : fuck1iN) : fuck1iN, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3835.1-3838.44
  def $ivswizzlop_{Jnn : fuck1Jnn, M : fuck3nat, def $f_(N : fuck1N, fuck6fuck1iN*, iN : fuck1iN) : fuck1iN, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_lane__2_lane_(Jnn, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn((Jnn : fuck1Jnn <: fuck1lanetype)), !($proj_lane__2(c_1))*{c_1 <- `c_1*`}, !($proj_lane__2(c_2)))*{c_2 <- `c_2*`}

;; test.spectec:3757.6-3757.18
relation ivswizzlop__is_wf(def $f_(N : fuck1N, fuck6fuck1iN*, iN : fuck1iN) : fuck1iN): `%%%%`fuck5(shape : fuck1shape, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3757.6-3757.18
  rule ivswizzlop__is_wf_0{shape : fuck1shape, def $f_(N : fuck1N, fuck6fuck1iN*, iN : fuck1iN) : fuck1iN, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%`(shape, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivswizzlop_(shape, def $f_, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3758.1-3758.85
def $ivshufflop_(shape : fuck1shape, fuck6fuck1laneidx*, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3841.1-3844.34
  def $ivshufflop_{Jnn : fuck1Jnn, M : fuck3nat, `i*` : fuck6fuck1laneidx*, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), i*{i <- `i*`}, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : fuck6fuck1lane_*} c*{c <- `c*`} = c_1*{c_1 <- `c_1*`} ++ c_2*{c_2 <- `c_2*`}[i!`%`_uN.0]*{i <- `i*`}

;; test.spectec:3758.6-3758.18
relation ivshufflop__is_wf: `%%%%%`fuck5(shape : fuck1shape, `var_0*` : fuck6fuck1laneidx*, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3758.6-3758.18
  rule ivshufflop__is_wf_0{shape : fuck1shape, `var_0*` : fuck6fuck1laneidx*, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(shape, `var_0*`, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape)
    -- (wf_uN: `%%`(8, var_0))*{var_0 <- `var_0*`}
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivshufflop_(shape, `var_0*`, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3849.1-3850.28
def $vvunop_(vectype : fuck1vectype, vvunop : fuck1vvunop, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3890.1-3890.53
  def $vvunop_{Vnn : fuck1vectype, v : fuck1uN}(Vnn, NOT_vvunop, v) = [$inot_($vsizenn(Vnn), v)]

;; test.spectec:3849.6-3849.14
relation vvunop__is_wf: `%%%%`fuck5(vectype : fuck1vectype, vvunop : fuck1vvunop, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3849.6-3849.14
  rule vvunop__is_wf_0{vectype : fuck1vectype, vvunop : fuck1vvunop, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%`(vectype, vvunop, vec_, `ret_val*`)
    -- wf_uN: `%%`($vsize(vectype), vec_)
    -- if (`ret_val*` = $vvunop_(vectype, vvunop, vec_))
    -- (wf_uN: `%%`($vsize(vectype), ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3851.1-3852.31
def $vvbinop_(vectype : fuck1vectype, vvbinop : fuck1vvbinop, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3892.1-3892.68
  def $vvbinop_{Vnn : fuck1vectype, v_1 : fuck1uN, v_2 : fuck1uN}(Vnn, AND_vvbinop, v_1, v_2) = [$iand_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3893.1-3893.74
  def $vvbinop_{Vnn : fuck1vectype, v_1 : fuck1uN, v_2 : fuck1uN}(Vnn, ANDNOT_vvbinop, v_1, v_2) = [$iandnot_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3894.1-3894.66
  def $vvbinop_{Vnn : fuck1vectype, v_1 : fuck1uN, v_2 : fuck1uN}(Vnn, OR_vvbinop, v_1, v_2) = [$ior_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3895.1-3895.68
  def $vvbinop_{Vnn : fuck1vectype, v_1 : fuck1uN, v_2 : fuck1uN}(Vnn, XOR_vvbinop, v_1, v_2) = [$ixor_($vsizenn(Vnn), v_1, v_2)]

;; test.spectec:3851.6-3851.15
relation vvbinop__is_wf: `%%%%%`fuck5(vectype : fuck1vectype, vvbinop : fuck1vvbinop, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3851.6-3851.15
  rule vvbinop__is_wf_0{vectype : fuck1vectype, vvbinop : fuck1vvbinop, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%`(vectype, vvbinop, vec_, vec__0, `ret_val*`)
    -- wf_uN: `%%`($vsize(vectype), vec_)
    -- wf_uN: `%%`($vsize(vectype), vec__0)
    -- if (`ret_val*` = $vvbinop_(vectype, vvbinop, vec_, vec__0))
    -- (wf_uN: `%%`($vsize(vectype), ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3853.1-3854.34
def $vvternop_(vectype : fuck1vectype, vvternop : fuck1vvternop, vec_ : fuck1vec_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3897.1-3897.91
  def $vvternop_{Vnn : fuck1vectype, v_1 : fuck1uN, v_2 : fuck1uN, v_3 : fuck1uN}(Vnn, BITSELECT_vvternop, v_1, v_2, v_3) = [$ibitselect_($vsizenn(Vnn), v_1, v_2, v_3)]

;; test.spectec:3853.6-3853.16
relation vvternop__is_wf: `%%%%%%`fuck5(vectype : fuck1vectype, vvternop : fuck1vvternop, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3853.6-3853.16
  rule vvternop__is_wf_0{vectype : fuck1vectype, vvternop : fuck1vvternop, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%%`(vectype, vvternop, vec_, vec__0, vec__1, `ret_val*`)
    -- wf_uN: `%%`($vsize(vectype), vec_)
    -- wf_uN: `%%`($vsize(vectype), vec__0)
    -- wf_uN: `%%`($vsize(vectype), vec__1)
    -- if (`ret_val*` = $vvternop_(vectype, vvternop, vec_, vec__0, vec__1))
    -- (wf_uN: `%%`($vsize(vectype), ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3856.1-3857.28
def $vunop_(shape : fuck1shape, vunop_ : fuck1vunop_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3899.1-3899.60
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, ABS_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fabs_, v)
  ;; test.spectec:3900.1-3900.60
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, NEG_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fneg_, v)
  ;; test.spectec:3901.1-3901.62
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, SQRT_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fsqrt_, v)
  ;; test.spectec:3902.1-3902.62
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, CEIL_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fceil_, v)
  ;; test.spectec:3903.1-3903.64
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, FLOOR_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $ffloor_, v)
  ;; test.spectec:3904.1-3904.64
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, TRUNC_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $ftrunc_, v)
  ;; test.spectec:3905.1-3905.68
  def $vunop_{Fnn : fuck1Fnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__1_vunop_(Fnn, M, NEAREST_vunop_Fnn_M), v) = $fvunop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fnearest_, v)
  ;; test.spectec:3907.1-3907.60
  def $vunop_{Jnn : fuck1Jnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__0_vunop_(Jnn, M, ABS_vunop_Jnn_M), v) = $ivunop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $iabs_, v)
  ;; test.spectec:3908.1-3908.60
  def $vunop_{Jnn : fuck1Jnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__0_vunop_(Jnn, M, NEG_vunop_Jnn_M), v) = $ivunop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ineg_, v)
  ;; test.spectec:3909.1-3909.66
  def $vunop_{Jnn : fuck1Jnn, M : fuck3nat, v : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vunop__0_vunop_(Jnn, M, POPCNT_vunop_Jnn_M), v) = $ivunop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ipopcnt_, v)

;; test.spectec:3856.6-3856.13
relation vunop__is_wf: `%%%%`fuck5(shape : fuck1shape, vunop_ : fuck1vunop_, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3856.6-3856.13
  rule vunop__is_wf_0{shape : fuck1shape, vunop_ : fuck1vunop_, vec_ : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%`(shape, vunop_, vec_, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_vunop_: `%%`(shape, vunop_)
    -- wf_uN: `%%`(128, vec_)
    -- if (`ret_val*` = $vunop_(shape, vunop_, vec_))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3858.1-3859.31
def $vbinop_(shape : fuck1shape, vbinop_ : fuck1vbinop_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3911.1-3911.76
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, ADD_vbinop_Jnn_M), v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $iadd_, v_1, v_2)
  ;; test.spectec:3912.1-3912.76
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, SUB_vbinop_Jnn_M), v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $isub_, v_1, v_2)
  ;; test.spectec:3913.1-3913.76
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, MUL_vbinop_Jnn_M), v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $imul_, v_1, v_2)
  ;; test.spectec:3914.1-3914.93
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, ADD_SAT_vbinop_Jnn_M(sx)), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $iadd_sat_, sx, v_1, v_2)
  ;; test.spectec:3915.1-3915.93
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, SUB_SAT_vbinop_Jnn_M(sx)), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $isub_sat_, sx, v_1, v_2)
  ;; test.spectec:3916.1-3916.85
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, MIN_vbinop_Jnn_M(sx)), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $imin_, sx, v_1, v_2)
  ;; test.spectec:3917.1-3917.85
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, MAX_vbinop_Jnn_M(sx)), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $imax_, sx, v_1, v_2)
  ;; test.spectec:3918.1-3918.85
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, AVGRU_vbinop_Jnn_M), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $iavgr_, U_sx, v_1, v_2)
  ;; test.spectec:3919.1-3919.99
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, Q15MULR_SATS_vbinop_Jnn_M), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $iq15mulr_sat_, S_sx, v_1, v_2)
  ;; test.spectec:3920.1-3920.109
  def $vbinop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__0_vbinop_(Jnn, M, RELAXED_Q15MULRS_vbinop_Jnn_M), v_1, v_2) = $ivbinopsxnd_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2)
  ;; test.spectec:3922.1-3922.76
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, ADD_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fadd_, v_1, v_2)
  ;; test.spectec:3923.1-3923.76
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, SUB_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fsub_, v_1, v_2)
  ;; test.spectec:3924.1-3924.76
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, MUL_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fmul_, v_1, v_2)
  ;; test.spectec:3925.1-3925.76
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, DIV_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fdiv_, v_1, v_2)
  ;; test.spectec:3926.1-3926.76
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, MIN_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fmin_, v_1, v_2)
  ;; test.spectec:3927.1-3927.76
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, MAX_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fmax_, v_1, v_2)
  ;; test.spectec:3928.1-3928.78
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, PMIN_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fpmin_, v_1, v_2)
  ;; test.spectec:3929.1-3929.78
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, PMAX_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fpmax_, v_1, v_2)
  ;; test.spectec:3930.1-3930.92
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, RELAXED_MIN_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $frelaxed_min_, v_1, v_2)
  ;; test.spectec:3931.1-3931.92
  def $vbinop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vbinop__1_vbinop_(Fnn, M, RELAXED_MAX_vbinop_Fnn_M), v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $frelaxed_max_, v_1, v_2)

;; test.spectec:3858.6-3858.14
relation vbinop__is_wf: `%%%%%`fuck5(shape : fuck1shape, vbinop_ : fuck1vbinop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3858.6-3858.14
  rule vbinop__is_wf_0{shape : fuck1shape, vbinop_ : fuck1vbinop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%`(shape, vbinop_, vec_, vec__0, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_vbinop_: `%%`(shape, vbinop_)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (`ret_val*` = $vbinop_(shape, vbinop_, vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3860.1-3861.34
def $vternop_(shape : fuck1shape, vternop_ : fuck1vternop_, vec_ : fuck1vec_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck6fuck1vec_*
  ;; test.spectec:3933.1-3933.120
  def $vternop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN, v_3 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vternop__0_vternop_(Jnn, M, RELAXED_LANESELECT_vternop_Jnn_M), v_1, v_2, v_3) = $ivternopnd_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $irelaxed_laneselect_, v_1, v_2, v_3)
  ;; test.spectec:3935.1-3935.106
  def $vternop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN, v_3 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vternop__1_vternop_(Fnn, M, RELAXED_MADD_vternop_Fnn_M), v_1, v_2, v_3) = $fvternop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $frelaxed_madd_, v_1, v_2, v_3)
  ;; test.spectec:3936.1-3936.108
  def $vternop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN, v_3 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vternop__1_vternop_(Fnn, M, RELAXED_NMADD_vternop_Fnn_M), v_1, v_2, v_3) = $fvternop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $frelaxed_nmadd_, v_1, v_2, v_3)

;; test.spectec:3860.6-3860.15
relation vternop__is_wf: `%%%%%%`fuck5(shape : fuck1shape, vternop_ : fuck1vternop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*)
  ;; test.spectec:3860.6-3860.15
  rule vternop__is_wf_0{shape : fuck1shape, vternop_ : fuck1vternop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, `ret_val*` : fuck6fuck1vec_*}:
    `%%%%%%`(shape, vternop_, vec_, vec__0, vec__1, `ret_val*`)
    -- wf_shape: `%`(shape)
    -- wf_vternop_: `%%`(shape, vternop_)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (`ret_val*` = $vternop_(shape, vternop_, vec_, vec__0, vec__1))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3862.1-3863.31
def $vrelop_(shape : fuck1shape, vrelop_ : fuck1vrelop_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3938.1-3938.74
  def $vrelop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__0_vrelop_(Jnn, M, EQ_vrelop_Jnn_M), v_1, v_2) = $ivrelop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ieq_, v_1, v_2)
  ;; test.spectec:3939.1-3939.74
  def $vrelop_{Jnn : fuck1Jnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__0_vrelop_(Jnn, M, NE_vrelop_Jnn_M), v_1, v_2) = $ivrelop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ine_, v_1, v_2)
  ;; test.spectec:3940.1-3940.83
  def $vrelop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__0_vrelop_(Jnn, M, LT_vrelop_Jnn_M(sx)), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ilt_, sx, v_1, v_2)
  ;; test.spectec:3941.1-3941.83
  def $vrelop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__0_vrelop_(Jnn, M, GT_vrelop_Jnn_M(sx)), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $igt_, sx, v_1, v_2)
  ;; test.spectec:3942.1-3942.83
  def $vrelop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__0_vrelop_(Jnn, M, LE_vrelop_Jnn_M(sx)), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ile_, sx, v_1, v_2)
  ;; test.spectec:3943.1-3943.83
  def $vrelop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__0_vrelop_(Jnn, M, GE_vrelop_Jnn_M(sx)), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ige_, sx, v_1, v_2)
  ;; test.spectec:3945.1-3945.74
  def $vrelop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__1_vrelop_(Fnn, M, EQ_vrelop_Fnn_M), v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $feq_, v_1, v_2)
  ;; test.spectec:3946.1-3946.74
  def $vrelop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__1_vrelop_(Fnn, M, NE_vrelop_Fnn_M), v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fne_, v_1, v_2)
  ;; test.spectec:3947.1-3947.74
  def $vrelop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__1_vrelop_(Fnn, M, LT_vrelop_Fnn_M), v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $flt_, v_1, v_2)
  ;; test.spectec:3948.1-3948.74
  def $vrelop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__1_vrelop_(Fnn, M, GT_vrelop_Fnn_M), v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fgt_, v_1, v_2)
  ;; test.spectec:3949.1-3949.74
  def $vrelop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__1_vrelop_(Fnn, M, LE_vrelop_Fnn_M), v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fle_, v_1, v_2)
  ;; test.spectec:3950.1-3950.74
  def $vrelop_{Fnn : fuck1Fnn, M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), mk_vrelop__1_vrelop_(Fnn, M, GE_vrelop_Fnn_M), v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : fuck1Fnn <: fuck1lanetype), `%`_dim(M)), def $fge_, v_1, v_2)

;; test.spectec:3862.6-3862.14
relation vrelop__is_wf: `%%%%%`fuck5(shape : fuck1shape, vrelop_ : fuck1vrelop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3862.6-3862.14
  rule vrelop__is_wf_0{shape : fuck1shape, vrelop_ : fuck1vrelop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(shape, vrelop_, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape)
    -- wf_vrelop_: `%%`(shape, vrelop_)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $vrelop_(shape, vrelop_, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3865.1-3866.41
def $lcvtop__(shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__, lane_ : fuck1lane_) : fuck6fuck1lane_*
  ;; test.spectec:3962.1-3963.69
  def $lcvtop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, half : fuck1half, sx : fuck1sx, c_1 : fuck1uN}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(half, sx)), mk_lane__2_lane_(Jnn_1, c_1)) = [mk_lane__2_lane_(Jnn_2, c)]
    -- let{c : fuck1iN} c = $extend__($lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)), sx, c_1)
  ;; test.spectec:3964.1-3965.70
  def $lcvtop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, `half?` : fuck6fuck1half?, sx : fuck1sx, c_1 : fuck1uN}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half?{half <- `half?`}, sx)), mk_lane__2_lane_(Jnn_1, c_1)) = [mk_lane__0_lane_((Fnn_2 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_2, c))]
    -- let{c : fuck1fN} c = $convert__($lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsizenn2((Fnn_2 : fuck1Fnn <: fuck1lanetype)), sx, c_1)
  ;; test.spectec:3966.1-3967.73
  def $lcvtop__{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Inn_2 : fuck1addrtype, M_2 : fuck3nat, sx : fuck1sx, `zero?` : fuck6fuck1zero?, c_1 : fuck1fN}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : fuck1addrtype <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___2_vcvtop__(Fnn_1, M_1, (Inn_2 : fuck1addrtype <: fuck1Jnn), M_2, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, zero?{zero <- `zero?`})), mk_lane__0_lane_((Fnn_1 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_1, c_1))) = lift(mk_lane__0_lane_((Inn_2 : fuck1addrtype <: fuck1numtype), mk_num__0_num_(Inn_2, c))?{c <- `c?`})
    -- let{`c?` : fuck6fuck1iN?} c?{c <- `c?`} = $trunc_sat__($lsizenn1((Fnn_1 : fuck1Fnn <: fuck1lanetype)), $lsizenn2((Inn_2 : fuck1addrtype <: fuck1lanetype)), sx, c_1)
  ;; test.spectec:3968.1-3969.77
  def $lcvtop__{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Inn_2 : fuck1addrtype, M_2 : fuck3nat, sx : fuck1sx, `zero?` : fuck6fuck1zero?, c_1 : fuck1fN}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : fuck1addrtype <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___2_vcvtop__(Fnn_1, M_1, (Inn_2 : fuck1addrtype <: fuck1Jnn), M_2, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(sx, zero?{zero <- `zero?`})), mk_lane__0_lane_((Fnn_1 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_1, c_1))) = lift(mk_lane__0_lane_((Inn_2 : fuck1addrtype <: fuck1numtype), mk_num__0_num_(Inn_2, c))?{c <- `c?`})
    -- let{`c?` : fuck6fuck1iN?} c?{c <- `c?`} = $relaxed_trunc__($lsizenn1((Fnn_1 : fuck1Fnn <: fuck1lanetype)), $lsizenn2((Inn_2 : fuck1addrtype <: fuck1lanetype)), sx, c_1)
  ;; test.spectec:3970.1-3971.66
  def $lcvtop__{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, c_1 : fuck1fN}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(ZERO_zero)), mk_lane__0_lane_((Fnn_1 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_1, c_1))) = mk_lane__0_lane_((Fnn_2 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_2, c))*{c <- `c*`}
    -- let{`c*` : fuck6fuck1fN*} c*{c <- `c*`} = $demote__($lsizenn1((Fnn_1 : fuck1Fnn <: fuck1lanetype)), $lsizenn2((Fnn_2 : fuck1Fnn <: fuck1lanetype)), c_1)
  ;; test.spectec:3972.1-3973.67
  def $lcvtop__{Fnn_1 : fuck1Fnn, M_1 : fuck3nat, Fnn_2 : fuck1Fnn, M_2 : fuck3nat, c_1 : fuck1fN}(`%X%`_shape((Fnn_1 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : fuck1Fnn <: fuck1lanetype), `%`_dim(M_2)), mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), mk_lane__0_lane_((Fnn_1 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_1, c_1))) = mk_lane__0_lane_((Fnn_2 : fuck1Fnn <: fuck1numtype), mk_num__1_num_(Fnn_2, c))*{c <- `c*`}
    -- let{`c*` : fuck6fuck1fN*} c*{c <- `c*`} = $promote__($lsizenn1((Fnn_1 : fuck1Fnn <: fuck1lanetype)), $lsizenn2((Fnn_2 : fuck1Fnn <: fuck1lanetype)), c_1)

;; test.spectec:3865.6-3865.15
relation lcvtop___is_wf: `%%%%%`fuck5(shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__, lane_ : fuck1lane_, `ret_val*` : fuck6fuck1lane_*)
  ;; test.spectec:3865.6-3865.15
  rule lcvtop___is_wf_0{shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__, lane_ : fuck1lane_, `ret_val*` : fuck6fuck1lane_*}:
    `%%%%%`(shape_1, shape_2, vcvtop__, lane_, `ret_val*`)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_vcvtop__: `%%%`(shape_1, shape_2, vcvtop__)
    -- wf_lane_: `%%`($lanetype(shape_1), lane_)
    -- if (`ret_val*` = $lcvtop__(shape_1, shape_2, vcvtop__, lane_))
    -- (wf_lane_: `%%`($lanetype(shape_2), ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3867.1-3868.41
def $vcvtop__(shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3975.1-3979.41
  def $vcvtop__{Lnn_1 : fuck1lanetype, M : fuck3nat, Lnn_2 : fuck1lanetype, vcvtop : fuck1vcvtop__, v_1 : fuck1uN, v : fuck1uN}(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, v_1) = v
    -- if (($halfop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()) /\ ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()))
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M)), v_1)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, c_1)*{c_1 <- `c_1*`})
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`})
    -- wf_shape: `%`(`%X%`_shape(Lnn_1, `%`_dim(M)))
    -- wf_shape: `%`(`%X%`_shape(Lnn_2, `%`_dim(M)))
  ;; test.spectec:3980.1-3984.43
  def $vcvtop__{Lnn_1 : fuck1lanetype, M_1 : fuck3nat, Lnn_2 : fuck1lanetype, M_2 : fuck3nat, vcvtop : fuck1vcvtop__, v_1 : fuck1uN, v : fuck1uN, half : fuck1half}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v_1) = v
    -- if ($halfop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(half))
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v_1)[$half(half, 0, M_2) : M_2]
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`})
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})
    -- wf_shape: `%`(`%X%`_shape(Lnn_1, `%`_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape(Lnn_2, `%`_dim(M_2)))
  ;; test.spectec:3985.1-3989.43
  def $vcvtop__{Lnn_1 : fuck1lanetype, M_1 : fuck3nat, Lnn_2 : fuck1lanetype, M_2 : fuck3nat, vcvtop : fuck1vcvtop__, v_1 : fuck1uN, v : fuck1uN}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v_1) = v
    -- if ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(ZERO_zero))
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v_1)
    -- let{`c**` : fuck6fuck6fuck1lane_**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax fuck1lane_, $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`} ++ [$zero(Lnn_2)]^M_1{})
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})
    -- wf_shape: `%`(`%X%`_shape(Lnn_1, `%`_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape(Lnn_2, `%`_dim(M_2)))

;; test.spectec:3867.6-3867.15
relation vcvtop___is_wf: `%%%%%`fuck5(shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__, vec_ : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3867.6-3867.15
  rule vcvtop___is_wf_0{shape_1 : fuck1shape, shape_2 : fuck1shape, vcvtop__ : fuck1vcvtop__, vec_ : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(shape_1, shape_2, vcvtop__, vec_, ret_val)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_vcvtop__: `%%%`(shape_1, shape_2, vcvtop__)
    -- wf_uN: `%%`(128, vec_)
    -- if (ret_val = $vcvtop__(shape_1, shape_2, vcvtop__, vec_))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3870.1-3871.34
def $vshiftop_(ishape : fuck1ishape, vshiftop_ : fuck1vshiftop_, vec_ : fuck1vec_, u32 : fuck1u32) : fuck1vec_
  ;; test.spectec:3952.1-3952.72
  def $vshiftop_{Jnn : fuck1Jnn, M : fuck3nat, v : fuck1uN, i : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), mk_vshiftop__0_vshiftop_(Jnn, M, SHL_vshiftop_Jnn_M), v, i) = $ivshiftop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ishl_, v, i)
  ;; test.spectec:3953.1-3953.81
  def $vshiftop_{Jnn : fuck1Jnn, M : fuck3nat, sx : fuck1sx, v : fuck1uN, i : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), mk_vshiftop__0_vshiftop_(Jnn, M, SHR_vshiftop_Jnn_M(sx)), v, i) = $ivshiftopsx_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), def $ishr_, sx, v, i)

;; test.spectec:3870.6-3870.16
relation vshiftop__is_wf: `%%%%%`fuck5(ishape : fuck1ishape, vshiftop_ : fuck1vshiftop_, vec_ : fuck1vec_, u32 : fuck1u32, ret_val : fuck1vec_)
  ;; test.spectec:3870.6-3870.16
  rule vshiftop__is_wf_0{ishape : fuck1ishape, vshiftop_ : fuck1vshiftop_, vec_ : fuck1vec_, u32 : fuck1u32, ret_val : fuck1vec_}:
    `%%%%%`(ishape, vshiftop_, vec_, u32, ret_val)
    -- wf_ishape: `%`(ishape)
    -- wf_vshiftop_: `%%`(ishape, vshiftop_)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $vshiftop_(ishape, vshiftop_, vec_, u32))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3872.1-3873.34
def $vbitmaskop_(ishape : fuck1ishape, vec_ : fuck1vec_) : fuck1u32
  ;; test.spectec:3955.1-3955.57
  def $vbitmaskop_{Jnn : fuck1Jnn, M : fuck3nat, v : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), v) = $ivbitmaskop_(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M)), v)

;; test.spectec:3872.6-3872.18
relation vbitmaskop__is_wf: `%%%`fuck5(ishape : fuck1ishape, vec_ : fuck1vec_, ret_val : fuck1u32)
  ;; test.spectec:3872.6-3872.18
  rule vbitmaskop__is_wf_0{ishape : fuck1ishape, vec_ : fuck1vec_, ret_val : fuck1u32}:
    `%%%`(ishape, vec_, ret_val)
    -- wf_ishape: `%`(ishape)
    -- wf_uN: `%%`(128, vec_)
    -- if (ret_val = $vbitmaskop_(ishape, vec_))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3874.1-3875.31
def $vswizzlop_(bshape : fuck1bshape, vswizzlop_ : fuck1vswizzlop_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3957.1-3957.93
  def $vswizzlop_{M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), mk_vswizzlop__0_vswizzlop_(M, SWIZZLE_vswizzlop_M), v_1, v_2) = $ivswizzlop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), def $iswizzle_lane_, v_1, v_2)
  ;; test.spectec:3958.1-3958.109
  def $vswizzlop_{M : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), mk_vswizzlop__0_vswizzlop_(M, RELAXED_SWIZZLE_vswizzlop_M), v_1, v_2) = $ivswizzlop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), def $irelaxed_swizzle_lane_, v_1, v_2)

;; test.spectec:3874.6-3874.17
relation vswizzlop__is_wf: `%%%%%`fuck5(bshape : fuck1bshape, vswizzlop_ : fuck1vswizzlop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3874.6-3874.17
  rule vswizzlop__is_wf_0{bshape : fuck1bshape, vswizzlop_ : fuck1vswizzlop_, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(bshape, vswizzlop_, vec_, vec__0, ret_val)
    -- wf_bshape: `%`(bshape)
    -- wf_vswizzlop_: `%%`(bshape, vswizzlop_)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $vswizzlop_(bshape, vswizzlop_, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3876.1-3877.40
def $vshufflop_(bshape : fuck1bshape, fuck6fuck1laneidx*, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3960.1-3960.75
  def $vshufflop_{M : fuck3nat, `i*` : fuck6fuck1laneidx*, v_1 : fuck1uN, v_2 : fuck1uN}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), i*{i <- `i*`}, v_1, v_2) = $ivshufflop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), i*{i <- `i*`}, v_1, v_2)

;; test.spectec:3876.6-3876.17
relation vshufflop__is_wf: `%%%%%`fuck5(bshape : fuck1bshape, `var_0*` : fuck6fuck1laneidx*, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3876.6-3876.17
  rule vshufflop__is_wf_0{bshape : fuck1bshape, `var_0*` : fuck6fuck1laneidx*, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(bshape, `var_0*`, vec_, vec__0, ret_val)
    -- wf_bshape: `%`(bshape)
    -- (wf_uN: `%%`(8, var_0))*{var_0 <- `var_0*`}
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $vshufflop_(bshape, `var_0*`, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3879.1-3880.49
def $vnarrowop__(shape_1 : fuck1shape, shape_2 : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:3991.1-3996.53
  def $vnarrowop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), sx, v_1, v_2) = v
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), v_1)
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), v_2)
    -- let{`c'_1*` : fuck6fuck1iN*} c'_1*{c'_1 <- `c'_1*`} = $narrow__($lsize((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsize((Jnn_2 : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)))*{c_1 <- `c_1*`}
    -- let{`c'_2*` : fuck6fuck1iN*} c'_2*{c'_2 <- `c'_2*`} = $narrow__($lsize((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsize((Jnn_2 : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_2)))*{c_2 <- `c_2*`}
    -- let{v : fuck1vec_} v = $inv_lanes_(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_lane__2_lane_(Jnn_2, c'_1)*{c'_1 <- `c'_1*`} ++ mk_lane__2_lane_(Jnn_2, c'_2)*{c'_2 <- `c'_2*`})
    -- wf_shape: `%`(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)))
    -- (wf_lane_: `%%`($lanetype(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_lane__2_lane_(Jnn_2, c'_1)))*{c'_1 <- `c'_1*`}
    -- (wf_lane_: `%%`($lanetype(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_lane__2_lane_(Jnn_2, c'_2)))*{c'_2 <- `c'_2*`}

;; test.spectec:3879.6-3879.18
relation vnarrowop___is_wf: `%%%%%%`fuck5(shape_1 : fuck1shape, shape_2 : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3879.6-3879.18
  rule vnarrowop___is_wf_0{shape_1 : fuck1shape, shape_2 : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%%`(shape_1, shape_2, sx, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $vnarrowop__(shape_1, shape_2, sx, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4040.1-4040.76
def $ivadd_pairwise_(N : fuck1N, fuck6fuck1iN*) : fuck6fuck1iN*
  ;; test.spectec:4041.1-4042.37
  def $ivadd_pairwise_{N : fuck3nat, `i*` : fuck6fuck1iN*, `j_1*` : fuck6fuck1N*, `j_2*` : fuck6fuck1N*}(N, i*{i <- `i*`}) = $iadd_(N, `%`_iN(j_1), `%`_iN(j_2))*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax fuck1N, [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = i!`%`_uN.0*{i <- `i*`})

;; test.spectec:4040.6-4040.22
relation ivadd_pairwise__is_wf: `%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*)
  ;; test.spectec:4040.6-4040.22
  rule ivadd_pairwise__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*}:
    `%%%`(N, `var_0*`, `ret_val*`)
    -- (wf_uN: `%%`(N, var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $ivadd_pairwise_(N, `var_0*`))
    -- (wf_uN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4026.1-4026.93
def $ivextunop__(shape_1 : fuck1shape, shape_2 : fuck1shape, def $f_(N : fuck1N, fuck6fuck1iN*) : fuck6fuck1iN*, sx : fuck1sx, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, def $f_(N : fuck1N, fuck6fuck1iN*) : fuck6fuck1iN*, sx : fuck1sx, v_1 : fuck1uN}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), def $f_, sx, v_1) = $inv_lanes_(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_lane__2_lane_(Jnn_2, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), v_1)
    -- let{`c'_1*` : fuck6fuck1iN*} c'_1*{c'_1 <- `c'_1*`} = $extend__($lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)), sx, !($proj_lane__2(c_1)))*{c_1 <- `c_1*`}
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)), c'_1*{c'_1 <- `c'_1*`})
    -- wf_shape: `%`(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)))

;; test.spectec:4026.6-4026.18
relation ivextunop___is_wf(def $f_(N : fuck1N, fuck6fuck1iN*) : fuck6fuck1iN*): `%%%%%`fuck5(shape_1 : fuck1shape, shape_2 : fuck1shape, sx : fuck1sx, vec_ : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:4026.6-4026.18
  rule ivextunop___is_wf_0{shape_1 : fuck1shape, shape_2 : fuck1shape, def $f_(N : fuck1N, fuck6fuck1iN*) : fuck6fuck1iN*, sx : fuck1sx, vec_ : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(shape_1, shape_2, sx, vec_, ret_val)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_uN: `%%`(128, vec_)
    -- if (ret_val = $ivextunop__(shape_1, shape_2, def $f_, sx, vec_))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3882.1-3883.32
def $vextunop__(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextunop__ : fuck1vextunop__, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:4055.1-4056.70
  def $vextunop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, sx : fuck1sx, v_1 : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextunop___0_vextunop__(Jnn_1, M_1, Jnn_2, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(sx)), v_1) = $ivextunop__(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), def $ivadd_pairwise_, sx, v_1)

;; test.spectec:3882.6-3882.17
relation vextunop___is_wf: `%%%%%`fuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextunop__ : fuck1vextunop__, vec_ : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3882.6-3882.17
  rule vextunop___is_wf_0{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextunop__ : fuck1vextunop__, vec_ : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%`(ishape_1, ishape_2, vextunop__, vec_, ret_val)
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextunop__: `%%%`(ishape_1, ishape_2, vextunop__)
    -- wf_uN: `%%`(128, vec_)
    -- if (ret_val = $vextunop__(ishape_1, ishape_2, vextunop__, vec_))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4047.1-4047.40
def $ivdot_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*
  ;; test.spectec:4048.1-4049.59
  def $ivdot_{N : fuck3nat, `i_1*` : fuck6fuck1iN*, `i_2*` : fuck6fuck1iN*, `j_1*` : fuck6fuck1iN*, `j_2*` : fuck6fuck1iN*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $iadd_(N, j_1, j_2)*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax fuck1iN, [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`})

;; test.spectec:4047.6-4047.13
relation ivdot__is_wf: `%%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1iN*, `var_1*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*)
  ;; test.spectec:4047.6-4047.13
  rule ivdot__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1iN*, `var_1*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*}:
    `%%%%`(N, `var_0*`, `var_1*`, `ret_val*`)
    -- (wf_uN: `%%`(N, var_0))*{var_0 <- `var_0*`}
    -- (wf_uN: `%%`(N, var_1))*{var_1 <- `var_1*`}
    -- if (`ret_val*` = $ivdot_(N, `var_0*`, `var_1*`))
    -- (wf_uN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4051.1-4051.76
def $ivdot_sat_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*
  ;; test.spectec:4052.1-4053.59
  def $ivdot_sat_{N : fuck3nat, `i_1*` : fuck6fuck1iN*, `i_2*` : fuck6fuck1iN*, `j_1*` : fuck6fuck1iN*, `j_2*` : fuck6fuck1iN*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $iadd_sat_(N, S_sx, j_1, j_2)*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax fuck1iN, [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`})

;; test.spectec:4051.6-4051.17
relation ivdot_sat__is_wf: `%%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1iN*, `var_1*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*)
  ;; test.spectec:4051.6-4051.17
  rule ivdot_sat__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1iN*, `var_1*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*}:
    `%%%%`(N, `var_0*`, `var_1*`, `ret_val*`)
    -- (wf_uN: `%%`(N, var_0))*{var_0 <- `var_0*`}
    -- (wf_uN: `%%`(N, var_1))*{var_1 <- `var_1*`}
    -- if (`ret_val*` = $ivdot_sat_(N, `var_0*`, `var_1*`))
    -- (wf_uN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4032.1-4032.136
def $ivextbinop__(shape_1 : fuck1shape, shape_2 : fuck1shape, def $f_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*, sx : fuck1sx, sx : fuck1sx, laneidx : fuck1laneidx, laneidx : fuck1laneidx, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, def $f_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*, sx_1 : fuck1sx, sx_2 : fuck1sx, i : fuck1uN, k : fuck1uN, v_1 : fuck1uN, v_2 : fuck1uN}(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_lane__2_lane_(Jnn_2, c)*{c <- `c*`})
    -- let{`c_1*` : fuck6fuck1lane_*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), v_1)[i!`%`_uN.0 : k!`%`_uN.0]
    -- let{`c_2*` : fuck6fuck1lane_*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), v_2)[i!`%`_uN.0 : k!`%`_uN.0]
    -- let{`c'_1*` : fuck6fuck1iN*} c'_1*{c'_1 <- `c'_1*`} = $extend__($lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)), sx_1, !($proj_lane__2(c_1)))*{c_1 <- `c_1*`}
    -- let{`c'_2*` : fuck6fuck1iN*} c'_2*{c'_2 <- `c'_2*`} = $extend__($lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype)), $lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)), sx_2, !($proj_lane__2(c_2)))*{c_2 <- `c_2*`}
    -- let{`c*` : fuck6fuck1iN*} c*{c <- `c*`} = $f_($lsizenn2((Jnn_2 : fuck1Jnn <: fuck1lanetype)), c'_1*{c'_1 <- `c'_1*`}, c'_2*{c'_2 <- `c'_2*`})
    -- wf_shape: `%`(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)))

;; test.spectec:4032.6-4032.19
relation ivextbinop___is_wf(def $f_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*): `%%%%%%%%%`fuck5(shape_1 : fuck1shape, shape_2 : fuck1shape, sx : fuck1sx, sx_0 : fuck1sx, laneidx : fuck1laneidx, laneidx_0 : fuck1laneidx, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:4032.6-4032.19
  rule ivextbinop___is_wf_0{shape_1 : fuck1shape, shape_2 : fuck1shape, def $f_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*, sx : fuck1sx, sx_0 : fuck1sx, laneidx : fuck1laneidx, laneidx_0 : fuck1laneidx, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%%%%%`(shape_1, shape_2, sx, sx_0, laneidx, laneidx_0, vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_uN: `%%`(8, laneidx)
    -- wf_uN: `%%`(8, laneidx_0)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivextbinop__(shape_1, shape_2, def $f_, sx, sx_0, laneidx, laneidx_0, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4044.1-4044.40
def $ivmul_(N : fuck1N, fuck6fuck1iN*, fuck6fuck1iN*) : fuck6fuck1iN*
  ;; test.spectec:4045.1-4045.50
  def $ivmul_{N : fuck3nat, `i_1*` : fuck6fuck1iN*, `i_2*` : fuck6fuck1iN*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`}

;; test.spectec:4044.6-4044.13
relation ivmul__is_wf: `%%%%`fuck5(N : fuck1N, `var_0*` : fuck6fuck1iN*, `var_1*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*)
  ;; test.spectec:4044.6-4044.13
  rule ivmul__is_wf_0{N : fuck1N, `var_0*` : fuck6fuck1iN*, `var_1*` : fuck6fuck1iN*, `ret_val*` : fuck6fuck1iN*}:
    `%%%%`(N, `var_0*`, `var_1*`, `ret_val*`)
    -- (wf_uN: `%%`(N, var_0))*{var_0 <- `var_0*`}
    -- (wf_uN: `%%`(N, var_1))*{var_1 <- `var_1*`}
    -- if (`ret_val*` = $ivmul_(N, `var_0*`, `var_1*`))
    -- (wf_uN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:3884.1-3885.35
def $vextbinop__(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextbinop__ : fuck1vextbinop__, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:4058.1-4059.97
  def $vextbinop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, half : fuck1half, sx : fuck1sx, v_1 : fuck1uN, v_2 : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(half, sx)), v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), def $ivmul_, sx, sx, `%`_laneidx($half(half, 0, M_2)), `%`_laneidx(M_2), v_1, v_2)
  ;; test.spectec:4060.1-4061.77
  def $vextbinop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), def $ivdot_, S_sx, S_sx, `%`_laneidx(0), `%`_laneidx(M_1), v_1, v_2)
  ;; test.spectec:4062.1-4063.108
  def $vextbinop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, v_1 : fuck1uN, v_2 : fuck1uN}(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), def $ivdot_sat_, S_sx, $relaxed2($R_idot, syntax fuck1sx, S_sx, U_sx), `%`_laneidx(0), `%`_laneidx(M_1), v_1, v_2)

;; test.spectec:3884.6-3884.18
relation vextbinop___is_wf: `%%%%%%`fuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextbinop__ : fuck1vextbinop__, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3884.6-3884.18
  rule vextbinop___is_wf_0{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextbinop__ : fuck1vextbinop__, vec_ : fuck1vec_, vec__0 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%%`(ishape_1, ishape_2, vextbinop__, vec_, vec__0, ret_val)
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextbinop__: `%%%`(ishape_1, ishape_2, vextbinop__)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $vextbinop__(ishape_1, ishape_2, vextbinop__, vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3886.1-3887.38
def $vextternop__(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextternop__ : fuck1vextternop__, vec_ : fuck1vec_, vec_ : fuck1vec_, vec_ : fuck1vec_) : fuck1vec_
  ;; test.spectec:4082.1-4087.50
  def $vextternop__{Jnn_1 : fuck1Jnn, M_1 : fuck3nat, Jnn_2 : fuck1Jnn, M_2 : fuck3nat, c_1 : fuck1uN, c_2 : fuck1uN, c_3 : fuck1uN, c : fuck1uN, Jnn : fuck1Jnn}(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextternop___0_vextternop__(Jnn_1, M_1, Jnn_2, M_2, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3) = c
    -- if ($jsizenn(Jnn) = (2 * $lsizenn1((Jnn_1 : fuck1Jnn <: fuck1lanetype))))
    -- let{M : fuck1M} M = (2 * M_2)
    -- let{c' : fuck1vec_} c' = $vextbinop__(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn, M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2)
    -- let{c'' : fuck1vec_} c'' = $vextunop__(`%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextunop___0_vextunop__(Jnn, M, Jnn_2, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c')
    -- if (c <- $vbinop_(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vbinop__0_vbinop_(Jnn_2, M_2, ADD_vbinop_Jnn_M), c'', c_3))
    -- wf_ishape: `%`(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))))
    -- wf_ishape: `%`(`%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))))
    -- wf_vextbinop__: `%%%`(`%`_ishape(`%X%`_shape((Jnn_1 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn, M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(`%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))))
    -- wf_vextunop__: `%%%`(`%`_ishape(`%X%`_shape((Jnn : fuck1Jnn <: fuck1lanetype), `%`_dim(M))), `%`_ishape(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2))), mk_vextunop___0_vextunop__(Jnn, M, Jnn_2, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape((Jnn_2 : fuck1Jnn <: fuck1lanetype), `%`_dim(M_2)), mk_vbinop__0_vbinop_(Jnn_2, M_2, ADD_vbinop_Jnn_M))

;; test.spectec:3886.6-3886.19
relation vextternop___is_wf: `%%%%%%%`fuck5(ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextternop__ : fuck1vextternop__, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, ret_val : fuck1vec_)
  ;; test.spectec:3886.6-3886.19
  rule vextternop___is_wf_0{ishape_1 : fuck1ishape, ishape_2 : fuck1ishape, vextternop__ : fuck1vextternop__, vec_ : fuck1vec_, vec__0 : fuck1vec_, vec__1 : fuck1vec_, ret_val : fuck1vec_}:
    `%%%%%%%`(ishape_1, ishape_2, vextternop__, vec_, vec__0, vec__1, ret_val)
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextternop__: `%%%`(ishape_1, ishape_2, vextternop__)
    -- wf_uN: `%%`(128, vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (ret_val = $vextternop__(ishape_1, ishape_2, vextternop__, vec_, vec__0, vec__1))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4124.1-4125.63
syntax num = 
  | CONSTfuck5(numtype : fuck1numtype, fuck1num_)

;; test.spectec:4124.8-4124.11
relation wf_num: `%`fuck5(fuck1num)
  ;; test.spectec:4124.8-4124.11
  rule num_case_0{numtype : fuck1numtype, var_0 : fuck1num_}:
    `%`(CONST_num(numtype, var_0))
    -- wf_num_: `%%`(numtype, var_0)

;; test.spectec:4127.1-4128.87
syntax vec = 
  | VCONSTfuck5(vectype : fuck1vectype, fuck1vec_)

;; test.spectec:4127.8-4127.11
relation wf_vec: `%`fuck5(fuck1vec)
  ;; test.spectec:4127.8-4127.11
  rule vec_case_0{vectype : fuck1vectype, var_0 : fuck1vec_}:
    `%`(VCONST_vec(vectype, var_0))
    -- wf_uN: `%%`($vsize(vectype), var_0)

;; test.spectec:4143.1-4144.58
syntax result = 
  | _VALSfuck5(`val*` : fuck6fuck1val*)
  | `(REF.EXN_ADDR%)THROW_REF`fuck5(exnaddr : fuck1exnaddr)
  | TRAP

;; test.spectec:4143.8-4143.14
relation wf_result: `%`fuck5(fuck1result)
  ;; test.spectec:4143.8-4143.14
  rule result_case_0{`val*` : fuck6fuck1val*}:
    `%`(_VALS_result(`val*`))
    -- (wf_val: `%`(val))*{val <- `val*`}

  ;; test.spectec:4143.8-4143.14
  rule result_case_1{exnaddr : fuck1exnaddr}:
    `%`(`(REF.EXN_ADDR%)THROW_REF`_result(exnaddr))

  ;; test.spectec:4143.8-4143.14
  rule result_case_2:
    `%`(TRAP_result)

;; test.spectec:4152.1-4152.72
syntax hostfunc = 
  | `...`

;; test.spectec:4153.1-4153.73
syntax funccode = 
  | FUNCfuck5(typeidx : fuck1typeidx, `local*` : fuck6fuck1local*, expr : fuck1expr)
  | `...`

;; test.spectec:4153.8-4153.16
relation wf_funccode: `%`fuck5(fuck1funccode)
  ;; test.spectec:4153.8-4153.16
  rule funccode_case_0{typeidx : fuck1typeidx, `local*` : fuck6fuck1local*, expr : fuck1expr}:
    `%`(FUNC_funccode(typeidx, `local*`, expr))
    -- wf_uN: `%%`(32, typeidx)
    -- (wf_local: `%`(local))*{local <- `local*`}
    -- (wf_instr: `%`(expr))*{expr <- expr}

  ;; test.spectec:4153.8-4153.16
  rule funccode_case_1:
    `%`(`...`_funccode)

;; test.spectec:4155.1-4156.19
syntax taginst = 
{
  TYPE fuck1tagtype
}

;; test.spectec:4155.8-4155.15
relation wf_taginst: `%`fuck5(fuck1taginst)
  ;; test.spectec:4155.8-4155.15
  rule taginst_case_{var_0 : fuck1tagtype}:
    `%`({TYPE var_0})
    -- wf_typeuse: `%`(var_0)

;; test.spectec:4158.1-4159.33
syntax globalinst = 
{
  TYPE fuck1globaltype,
  VALUE fuck1val
}

;; test.spectec:4158.8-4158.18
relation wf_globalinst: `%`fuck5(fuck1globalinst)
  ;; test.spectec:4158.8-4158.18
  rule globalinst_case_{var_0 : fuck1globaltype, var_1 : fuck1val}:
    `%`({TYPE var_0, VALUE var_1})
    -- wf_globaltype: `%`(var_0)
    -- wf_val: `%`(var_1)

;; test.spectec:4161.1-4162.32
syntax meminst = 
{
  TYPE fuck1memtype,
  BYTES fuck6fuck1byte*
}

;; test.spectec:4161.8-4161.15
relation wf_meminst: `%`fuck5(fuck1meminst)
  ;; test.spectec:4161.8-4161.15
  rule meminst_case_{var_0 : fuck1memtype, `var_1*` : fuck6fuck1byte*}:
    `%`({TYPE var_0, BYTES `var_1*`})
    -- wf_memtype: `%`(var_0)
    -- (wf_byte: `%`(var_1))*{var_1 <- `var_1*`}

;; test.spectec:4164.1-4165.32
syntax tableinst = 
{
  TYPE fuck1tabletype,
  REFS fuck6fuck1ref*
}

;; test.spectec:4164.8-4164.17
relation wf_tableinst: `%`fuck5(fuck1tableinst)
  ;; test.spectec:4164.8-4164.17
  rule tableinst_case_{var_0 : fuck1tabletype, `var_1*` : fuck6fuck1ref*}:
    `%`({TYPE var_0, REFS `var_1*`})
    -- wf_tabletype: `%`(var_0)
    -- (wf_ref: `%`(var_1))*{var_1 <- `var_1*`}

;; test.spectec:4167.1-4168.53
syntax funcinst = 
{
  TYPE fuck1deftype,
  MODULE fuck1moduleinst,
  CODE fuck1funccode
}

;; test.spectec:4167.8-4167.16
relation wf_funcinst: `%`fuck5(fuck1funcinst)
  ;; test.spectec:4167.8-4167.16
  rule funcinst_case_{var_0 : fuck1deftype, var_1 : fuck1moduleinst, var_2 : fuck1funccode}:
    `%`({TYPE var_0, MODULE var_1, CODE var_2})
    -- wf_moduleinst: `%`(var_1)
    -- wf_funccode: `%`(var_2)

;; test.spectec:4170.1-4171.18
syntax datainst = 
{
  BYTES fuck6fuck1byte*
}

;; test.spectec:4170.8-4170.16
relation wf_datainst: `%`fuck5(fuck1datainst)
  ;; test.spectec:4170.8-4170.16
  rule datainst_case_{`var_0*` : fuck6fuck1byte*}:
    `%`({BYTES `var_0*`})
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}

;; test.spectec:4173.1-4174.31
syntax eleminst = 
{
  TYPE fuck1elemtype,
  REFS fuck6fuck1ref*
}

;; test.spectec:4173.8-4173.16
relation wf_eleminst: `%`fuck5(fuck1eleminst)
  ;; test.spectec:4173.8-4173.16
  rule eleminst_case_{var_0 : fuck1elemtype, `var_1*` : fuck6fuck1ref*}:
    `%`({TYPE var_0, REFS `var_1*`})
    -- wf_reftype: `%`(var_0)
    -- (wf_ref: `%`(var_1))*{var_1 <- `var_1*`}

;; test.spectec:4180.1-4181.64
syntax packval = 
  | PACKfuck5(packtype : fuck1packtype, fuck1iN)

;; test.spectec:4180.8-4180.15
relation wf_packval: `%`fuck5(fuck1packval)
  ;; test.spectec:4180.8-4180.15
  rule packval_case_0{packtype : fuck1packtype, var_0 : fuck1iN}:
    `%`(PACK_packval(packtype, var_0))
    -- wf_uN: `%%`($psize(packtype), var_0)

;; test.spectec:4183.1-4184.18
syntax fieldval = 
  | CONSTfuck5(numtype : fuck1numtype, fuck1num_)
  | VCONSTfuck5(vectype : fuck1vectype, fuck1vec_)
  | `REF.I31_NUM`fuck5(u31 : fuck1u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`fuck5(structaddr : fuck1structaddr)
  | `REF.ARRAY_ADDR`fuck5(arrayaddr : fuck1arrayaddr)
  | `REF.FUNC_ADDR`fuck5(funcaddr : fuck1funcaddr)
  | `REF.EXN_ADDR`fuck5(exnaddr : fuck1exnaddr)
  | `REF.HOST_ADDR`fuck5(hostaddr : fuck1hostaddr)
  | `REF.EXTERN`fuck5(ref : fuck1ref)
  | PACKfuck5(packtype : fuck1packtype, fuck1iN)

;; test.spectec:4183.8-4183.16
relation wf_fieldval: `%`fuck5(fuck1fieldval)
  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_0{numtype : fuck1numtype, var_0 : fuck1num_}:
    `%`(CONST_fieldval(numtype, var_0))
    -- wf_num_: `%%`(numtype, var_0)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_1{vectype : fuck1vectype, var_0 : fuck1vec_}:
    `%`(VCONST_fieldval(vectype, var_0))
    -- wf_uN: `%%`($vsize(vectype), var_0)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_2{u31 : fuck1u31}:
    `%`(`REF.I31_NUM`_fieldval(u31))
    -- wf_uN: `%%`(31, u31)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_3:
    `%`(`REF.NULL_ADDR`_fieldval)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_4{structaddr : fuck1structaddr}:
    `%`(`REF.STRUCT_ADDR`_fieldval(structaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_5{arrayaddr : fuck1arrayaddr}:
    `%`(`REF.ARRAY_ADDR`_fieldval(arrayaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_6{funcaddr : fuck1funcaddr}:
    `%`(`REF.FUNC_ADDR`_fieldval(funcaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_7{exnaddr : fuck1exnaddr}:
    `%`(`REF.EXN_ADDR`_fieldval(exnaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_8{hostaddr : fuck1hostaddr}:
    `%`(`REF.HOST_ADDR`_fieldval(hostaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_9{ref : fuck1ref}:
    `%`(`REF.EXTERN`_fieldval(ref))
    -- wf_ref: `%`(ref)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_10{packtype : fuck1packtype, var_0 : fuck1iN}:
    `%`(PACK_fieldval(packtype, var_0))
    -- wf_uN: `%%`($psize(packtype), var_0)

;; test.spectec:4186.1-4187.37
syntax structinst = 
{
  TYPE fuck1deftype,
  FIELDS fuck6fuck1fieldval*
}

;; test.spectec:4186.8-4186.18
relation wf_structinst: `%`fuck5(fuck1structinst)
  ;; test.spectec:4186.8-4186.18
  rule structinst_case_{var_0 : fuck1deftype, `var_1*` : fuck6fuck1fieldval*}:
    `%`({TYPE var_0, FIELDS `var_1*`})
    -- (wf_fieldval: `%`(var_1))*{var_1 <- `var_1*`}

;; test.spectec:4189.1-4190.37
syntax arrayinst = 
{
  TYPE fuck1deftype,
  FIELDS fuck6fuck1fieldval*
}

;; test.spectec:4189.8-4189.17
relation wf_arrayinst: `%`fuck5(fuck1arrayinst)
  ;; test.spectec:4189.8-4189.17
  rule arrayinst_case_{var_0 : fuck1deftype, `var_1*` : fuck6fuck1fieldval*}:
    `%`({TYPE var_0, FIELDS `var_1*`})
    -- (wf_fieldval: `%`(var_1))*{var_1 <- `var_1*`}

;; test.spectec:4192.1-4193.31
syntax exninst = 
{
  TAG fuck1tagaddr,
  FIELDS fuck6fuck1val*
}

;; test.spectec:4192.8-4192.15
relation wf_exninst: `%`fuck5(fuck1exninst)
  ;; test.spectec:4192.8-4192.15
  rule exninst_case_{var_0 : fuck1tagaddr, `var_1*` : fuck6fuck1val*}:
    `%`({TAG var_0, FIELDS `var_1*`})
    -- (wf_val: `%`(var_1))*{var_1 <- `var_1*`}

;; test.spectec:4210.1-4220.20
syntax store = 
{
  TAGS fuck6fuck1taginst*,
  GLOBALS fuck6fuck1globalinst*,
  MEMS fuck6fuck1meminst*,
  TABLES fuck6fuck1tableinst*,
  FUNCS fuck6fuck1funcinst*,
  DATAS fuck6fuck1datainst*,
  ELEMS fuck6fuck1eleminst*,
  STRUCTS fuck6fuck1structinst*,
  ARRAYS fuck6fuck1arrayinst*,
  EXNS fuck6fuck1exninst*
}

;; test.spectec:4210.8-4210.13
relation wf_store: `%`fuck5(fuck1store)
  ;; test.spectec:4210.8-4210.13
  rule store_case_{`var_0*` : fuck6fuck1taginst*, `var_1*` : fuck6fuck1globalinst*, `var_2*` : fuck6fuck1meminst*, `var_3*` : fuck6fuck1tableinst*, `var_4*` : fuck6fuck1funcinst*, `var_5*` : fuck6fuck1datainst*, `var_6*` : fuck6fuck1eleminst*, `var_7*` : fuck6fuck1structinst*, `var_8*` : fuck6fuck1arrayinst*, `var_9*` : fuck6fuck1exninst*}:
    `%`({TAGS `var_0*`, GLOBALS `var_1*`, MEMS `var_2*`, TABLES `var_3*`, FUNCS `var_4*`, DATAS `var_5*`, ELEMS `var_6*`, STRUCTS `var_7*`, ARRAYS `var_8*`, EXNS `var_9*`})
    -- (wf_taginst: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_globalinst: `%`(var_1))*{var_1 <- `var_1*`}
    -- (wf_meminst: `%`(var_2))*{var_2 <- `var_2*`}
    -- (wf_tableinst: `%`(var_3))*{var_3 <- `var_3*`}
    -- (wf_funcinst: `%`(var_4))*{var_4 <- `var_4*`}
    -- (wf_datainst: `%`(var_5))*{var_5 <- `var_5*`}
    -- (wf_eleminst: `%`(var_6))*{var_6 <- `var_6*`}
    -- (wf_structinst: `%`(var_7))*{var_7 <- `var_7*`}
    -- (wf_arrayinst: `%`(var_8))*{var_8 <- `var_8*`}
    -- (wf_exninst: `%`(var_9))*{var_9 <- `var_9*`}

;; test.spectec:4239.1-4239.47
syntax state = 
  | `%;%`fuck5(store : fuck1store, frame : fuck1frame)

;; test.spectec:4239.8-4239.13
relation wf_state: `%`fuck5(fuck1state)
  ;; test.spectec:4239.8-4239.13
  rule state_case_0{store : fuck1store, frame : fuck1frame}:
    `%`(`%;%`_state(store, frame))
    -- wf_store: `%`(store)
    -- wf_frame: `%`(frame)

;; test.spectec:4240.1-4240.57
syntax config = 
  | `%;%`fuck5(state : fuck1state, `instr*` : fuck6fuck1instr*)

;; test.spectec:4240.8-4240.14
relation wf_config: `%`fuck5(fuck1config)
  ;; test.spectec:4240.8-4240.14
  rule config_case_0{state : fuck1state, `instr*` : fuck6fuck1instr*}:
    `%`(`%;%`_config(state, `instr*`))
    -- wf_state: `%`(state)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

;; test.spectec:4267.1-4267.31
def $Ki : fuck3nat
  ;; test.spectec:4268.1-4268.15
  def $Ki = 1024

;; test.spectec:4273.1-4273.114
def $packfield_(storagetype : fuck1storagetype, val : fuck1val) : fuck1fieldval
  ;; test.spectec:4276.1-4276.36
  def $packfield_{valtype : fuck1valtype, val : fuck1val}((valtype : fuck1valtype <: fuck1storagetype), val) = (val : fuck1val <: fuck1fieldval)
  ;; test.spectec:4277.1-4277.88
  def $packfield_{packtype : fuck1packtype, i : fuck1uN}((packtype : fuck1packtype <: fuck1storagetype), CONST_val(I32_numtype, mk_num__0_num_(I32_Inn, i))) = PACK_fieldval(packtype, $wrap__(32, $psize(packtype), i))

;; test.spectec:4273.6-4273.17
relation packfield__is_wf: `%%%`fuck5(storagetype : fuck1storagetype, val : fuck1val, ret_val : fuck1fieldval)
  ;; test.spectec:4273.6-4273.17
  rule packfield__is_wf_0{storagetype : fuck1storagetype, val : fuck1val, ret_val : fuck1fieldval}:
    `%%%`(storagetype, val, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- wf_val: `%`(val)
    -- if (ret_val = $packfield_(storagetype, val))
    -- wf_fieldval: `%`(ret_val)

;; test.spectec:4274.1-4274.126
def $unpackfield_(storagetype : fuck1storagetype, fuck6fuck1sx?, fieldval : fuck1fieldval) : fuck1val
  ;; test.spectec:4279.1-4279.43
  def $unpackfield_{valtype : fuck1valtype, val : fuck1val}((valtype : fuck1valtype <: fuck1storagetype), ?(), (val : fuck1val <: fuck1fieldval)) = val
  ;; test.spectec:4280.1-4280.100
  def $unpackfield_{packtype : fuck1packtype, sx : fuck1sx, i : fuck1uN}((packtype : fuck1packtype <: fuck1storagetype), ?(sx), PACK_fieldval(packtype, i)) = CONST_val(I32_numtype, mk_num__0_num_(I32_Inn, $extend__($psize(packtype), 32, sx, i)))

;; test.spectec:4274.6-4274.19
relation unpackfield__is_wf: `%%%%`fuck5(storagetype : fuck1storagetype, `var_0?` : fuck6fuck1sx?, fieldval : fuck1fieldval, ret_val : fuck1val)
  ;; test.spectec:4274.6-4274.19
  rule unpackfield__is_wf_0{storagetype : fuck1storagetype, `var_0?` : fuck6fuck1sx?, fieldval : fuck1fieldval, ret_val : fuck1val}:
    `%%%%`(storagetype, `var_0?`, fieldval, ret_val)
    -- wf_storagetype: `%`(storagetype)
    -- wf_fieldval: `%`(fieldval)
    -- if (ret_val = $unpackfield_(storagetype, `var_0?`, fieldval))
    -- wf_val: `%`(ret_val)

;; test.spectec:4285.1-4285.86
rec {

;; test.spectec:4285.1-4285.86
def $tagsxa(fuck6fuck1externaddr*) : fuck6fuck1tagaddr*
  ;; test.spectec:4291.1-4291.23
  def $tagsxa([]) = []
  ;; test.spectec:4292.1-4292.42
  def $tagsxa{a : fuck3nat, `xa*` : fuck6fuck1externaddr*}([TAG_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $tagsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4293.1-4293.57
  def $tagsxa{externaddr : fuck1externaddr, `xa*` : fuck6fuck1externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $tagsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4286.1-4286.89
rec {

;; test.spectec:4286.1-4286.89
def $globalsxa(fuck6fuck1externaddr*) : fuck6fuck1globaladdr*
  ;; test.spectec:4295.1-4295.26
  def $globalsxa([]) = []
  ;; test.spectec:4296.1-4296.51
  def $globalsxa{a : fuck3nat, `xa*` : fuck6fuck1externaddr*}([GLOBAL_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $globalsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4297.1-4297.63
  def $globalsxa{externaddr : fuck1externaddr, `xa*` : fuck6fuck1externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $globalsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4287.1-4287.86
rec {

;; test.spectec:4287.1-4287.86
def $memsxa(fuck6fuck1externaddr*) : fuck6fuck1memaddr*
  ;; test.spectec:4299.1-4299.23
  def $memsxa([]) = []
  ;; test.spectec:4300.1-4300.42
  def $memsxa{a : fuck3nat, `xa*` : fuck6fuck1externaddr*}([MEM_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $memsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4301.1-4301.57
  def $memsxa{externaddr : fuck1externaddr, `xa*` : fuck6fuck1externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $memsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4288.1-4288.88
rec {

;; test.spectec:4288.1-4288.88
def $tablesxa(fuck6fuck1externaddr*) : fuck6fuck1tableaddr*
  ;; test.spectec:4303.1-4303.25
  def $tablesxa([]) = []
  ;; test.spectec:4304.1-4304.48
  def $tablesxa{a : fuck3nat, `xa*` : fuck6fuck1externaddr*}([TABLE_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $tablesxa(xa*{xa <- `xa*`})
  ;; test.spectec:4305.1-4305.61
  def $tablesxa{externaddr : fuck1externaddr, `xa*` : fuck6fuck1externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $tablesxa(xa*{xa <- `xa*`})
}

;; test.spectec:4289.1-4289.87
rec {

;; test.spectec:4289.1-4289.87
def $funcsxa(fuck6fuck1externaddr*) : fuck6fuck1funcaddr*
  ;; test.spectec:4307.1-4307.24
  def $funcsxa([]) = []
  ;; test.spectec:4308.1-4308.45
  def $funcsxa{a : fuck3nat, `xa*` : fuck6fuck1externaddr*}([FUNC_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $funcsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4309.1-4309.59
  def $funcsxa{externaddr : fuck1externaddr, `xa*` : fuck6fuck1externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $funcsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4314.1-4314.74
def $store(state : fuck1state) : fuck1store
  ;; test.spectec:4317.1-4317.23
  def $store{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s

;; test.spectec:4314.6-4314.12
relation store_is_wf: `%%`fuck5(state : fuck1state, ret_val : fuck1store)
  ;; test.spectec:4314.6-4314.12
  rule store_is_wf_0{state : fuck1state, ret_val : fuck1store}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $store(state))
    -- wf_store: `%`(ret_val)

;; test.spectec:4315.1-4315.74
def $frame(state : fuck1state) : fuck1frame
  ;; test.spectec:4318.1-4318.23
  def $frame{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = f

;; test.spectec:4315.6-4315.12
relation frame_is_wf: `%%`fuck5(state : fuck1state, ret_val : fuck1frame)
  ;; test.spectec:4315.6-4315.12
  rule frame_is_wf_0{state : fuck1state, ret_val : fuck1frame}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $frame(state))
    -- wf_frame: `%`(ret_val)

;; test.spectec:4320.1-4320.80
def $tagaddr(state : fuck1state) : fuck6fuck1tagaddr*
  ;; test.spectec:4321.1-4321.37
  def $tagaddr{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = f.MODULE_frame.TAGS_moduleinst

;; test.spectec:4323.1-4323.76
def $moduleinst(state : fuck1state) : fuck1moduleinst
  ;; test.spectec:4335.1-4335.35
  def $moduleinst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = f.MODULE_frame

;; test.spectec:4323.6-4323.17
relation moduleinst_is_wf: `%%`fuck5(state : fuck1state, ret_val : fuck1moduleinst)
  ;; test.spectec:4323.6-4323.17
  rule moduleinst_is_wf_0{state : fuck1state, ret_val : fuck1moduleinst}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $moduleinst(state))
    -- wf_moduleinst: `%`(ret_val)

;; test.spectec:4324.1-4324.76
def $taginst(state : fuck1state) : fuck6fuck1taginst*
  ;; test.spectec:4336.1-4336.30
  def $taginst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.TAGS_store

;; test.spectec:4324.6-4324.14
relation taginst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1taginst*)
  ;; test.spectec:4324.6-4324.14
  rule taginst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1taginst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $taginst(state))
    -- (wf_taginst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4325.1-4325.76
def $globalinst(state : fuck1state) : fuck6fuck1globalinst*
  ;; test.spectec:4337.1-4337.36
  def $globalinst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.GLOBALS_store

;; test.spectec:4325.6-4325.17
relation globalinst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1globalinst*)
  ;; test.spectec:4325.6-4325.17
  rule globalinst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1globalinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $globalinst(state))
    -- (wf_globalinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4326.1-4326.76
def $meminst(state : fuck1state) : fuck6fuck1meminst*
  ;; test.spectec:4338.1-4338.30
  def $meminst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.MEMS_store

;; test.spectec:4326.6-4326.14
relation meminst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1meminst*)
  ;; test.spectec:4326.6-4326.14
  rule meminst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1meminst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $meminst(state))
    -- (wf_meminst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4327.1-4327.76
def $tableinst(state : fuck1state) : fuck6fuck1tableinst*
  ;; test.spectec:4339.1-4339.34
  def $tableinst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.TABLES_store

;; test.spectec:4327.6-4327.16
relation tableinst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1tableinst*)
  ;; test.spectec:4327.6-4327.16
  rule tableinst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1tableinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $tableinst(state))
    -- (wf_tableinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4328.1-4328.76
def $funcinst(state : fuck1state) : fuck6fuck1funcinst*
  ;; test.spectec:4340.1-4340.32
  def $funcinst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.FUNCS_store

;; test.spectec:4328.6-4328.15
relation funcinst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1funcinst*)
  ;; test.spectec:4328.6-4328.15
  rule funcinst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1funcinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $funcinst(state))
    -- (wf_funcinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4329.1-4329.76
def $datainst(state : fuck1state) : fuck6fuck1datainst*
  ;; test.spectec:4341.1-4341.32
  def $datainst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.DATAS_store

;; test.spectec:4329.6-4329.15
relation datainst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1datainst*)
  ;; test.spectec:4329.6-4329.15
  rule datainst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1datainst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $datainst(state))
    -- (wf_datainst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4330.1-4330.76
def $eleminst(state : fuck1state) : fuck6fuck1eleminst*
  ;; test.spectec:4342.1-4342.32
  def $eleminst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.ELEMS_store

;; test.spectec:4330.6-4330.15
relation eleminst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1eleminst*)
  ;; test.spectec:4330.6-4330.15
  rule eleminst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1eleminst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $eleminst(state))
    -- (wf_eleminst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4331.1-4331.76
def $structinst(state : fuck1state) : fuck6fuck1structinst*
  ;; test.spectec:4343.1-4343.36
  def $structinst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.STRUCTS_store

;; test.spectec:4331.6-4331.17
relation structinst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1structinst*)
  ;; test.spectec:4331.6-4331.17
  rule structinst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1structinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $structinst(state))
    -- (wf_structinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4332.1-4332.76
def $arrayinst(state : fuck1state) : fuck6fuck1arrayinst*
  ;; test.spectec:4344.1-4344.34
  def $arrayinst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.ARRAYS_store

;; test.spectec:4332.6-4332.16
relation arrayinst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1arrayinst*)
  ;; test.spectec:4332.6-4332.16
  rule arrayinst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1arrayinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $arrayinst(state))
    -- (wf_arrayinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4333.1-4333.76
def $exninst(state : fuck1state) : fuck6fuck1exninst*
  ;; test.spectec:4345.1-4345.30
  def $exninst{s : fuck1store, f : fuck1frame}(`%;%`_state(s, f)) = s.EXNS_store

;; test.spectec:4333.6-4333.14
relation exninst_is_wf: `%%`fuck5(state : fuck1state, `ret_val*` : fuck6fuck1exninst*)
  ;; test.spectec:4333.6-4333.14
  rule exninst_is_wf_0{state : fuck1state, `ret_val*` : fuck6fuck1exninst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $exninst(state))
    -- (wf_exninst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:4359.1-4359.38
def $fof(state : fuck1state) : fuck1frame
  ;; test.spectec:4362.1-4362.24
  def $fof{z : fuck1state}(z) = $frame(z)

;; test.spectec:4359.6-4359.10
relation fof_is_wf: `%%`fuck5(state : fuck1state, ret_val : fuck1frame)
  ;; test.spectec:4359.6-4359.10
  rule fof_is_wf_0{state : fuck1state, ret_val : fuck1frame}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $fof(state))
    -- wf_frame: `%`(ret_val)

;; test.spectec:4348.1-4348.85
def $type(state : fuck1state, typeidx : fuck1typeidx) : fuck1deftype
  ;; test.spectec:4364.1-4364.42
  def $type{z : fuck1state, x : fuck1uN}(z, x) = $fof(z).MODULE_frame.TYPES_moduleinst[x!`%`_uN.0]

;; test.spectec:4358.1-4358.38
def $sof(state : fuck1state) : fuck1store
  ;; test.spectec:4361.1-4361.24
  def $sof{z : fuck1state}(z) = $store(z)

;; test.spectec:4358.6-4358.10
relation sof_is_wf: `%%`fuck5(state : fuck1state, ret_val : fuck1store)
  ;; test.spectec:4358.6-4358.10
  rule sof_is_wf_0{state : fuck1state, ret_val : fuck1store}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $sof(state))
    -- wf_store: `%`(ret_val)

;; test.spectec:4349.1-4349.85
def $tag(state : fuck1state, tagidx : fuck1tagidx) : fuck1taginst
  ;; test.spectec:4365.1-4365.54
  def $tag{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).TAGS_store[$fof(z).MODULE_frame.TAGS_moduleinst[x!`%`_uN.0]]

;; test.spectec:4349.6-4349.10
relation tag_is_wf: `%%%`fuck5(state : fuck1state, tagidx : fuck1tagidx, ret_val : fuck1taginst)
  ;; test.spectec:4349.6-4349.10
  rule tag_is_wf_0{state : fuck1state, tagidx : fuck1tagidx, ret_val : fuck1taginst}:
    `%%%`(state, tagidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tagidx)
    -- if (ret_val = $tag(state, tagidx))
    -- wf_taginst: `%`(ret_val)

;; test.spectec:4350.1-4350.85
def $global(state : fuck1state, globalidx : fuck1globalidx) : fuck1globalinst
  ;; test.spectec:4366.1-4366.63
  def $global{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[x!`%`_uN.0]]

;; test.spectec:4350.6-4350.13
relation global_is_wf: `%%%`fuck5(state : fuck1state, globalidx : fuck1globalidx, ret_val : fuck1globalinst)
  ;; test.spectec:4350.6-4350.13
  rule global_is_wf_0{state : fuck1state, globalidx : fuck1globalidx, ret_val : fuck1globalinst}:
    `%%%`(state, globalidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, globalidx)
    -- if (ret_val = $global(state, globalidx))
    -- wf_globalinst: `%`(ret_val)

;; test.spectec:4351.1-4351.85
def $mem(state : fuck1state, memidx : fuck1memidx) : fuck1meminst
  ;; test.spectec:4367.1-4367.54
  def $mem{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_uN.0]]

;; test.spectec:4351.6-4351.10
relation mem_is_wf: `%%%`fuck5(state : fuck1state, memidx : fuck1memidx, ret_val : fuck1meminst)
  ;; test.spectec:4351.6-4351.10
  rule mem_is_wf_0{state : fuck1state, memidx : fuck1memidx, ret_val : fuck1meminst}:
    `%%%`(state, memidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, memidx)
    -- if (ret_val = $mem(state, memidx))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:4352.1-4352.85
def $table(state : fuck1state, tableidx : fuck1tableidx) : fuck1tableinst
  ;; test.spectec:4368.1-4368.60
  def $table{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_uN.0]]

;; test.spectec:4352.6-4352.12
relation table_is_wf: `%%%`fuck5(state : fuck1state, tableidx : fuck1tableidx, ret_val : fuck1tableinst)
  ;; test.spectec:4352.6-4352.12
  rule table_is_wf_0{state : fuck1state, tableidx : fuck1tableidx, ret_val : fuck1tableinst}:
    `%%%`(state, tableidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- if (ret_val = $table(state, tableidx))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:4353.1-4353.85
def $func(state : fuck1state, funcidx : fuck1funcidx) : fuck1funcinst
  ;; test.spectec:4369.1-4369.57
  def $func{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).FUNCS_store[$fof(z).MODULE_frame.FUNCS_moduleinst[x!`%`_uN.0]]

;; test.spectec:4353.6-4353.11
relation func_is_wf: `%%%`fuck5(state : fuck1state, funcidx : fuck1funcidx, ret_val : fuck1funcinst)
  ;; test.spectec:4353.6-4353.11
  rule func_is_wf_0{state : fuck1state, funcidx : fuck1funcidx, ret_val : fuck1funcinst}:
    `%%%`(state, funcidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, funcidx)
    -- if (ret_val = $func(state, funcidx))
    -- wf_funcinst: `%`(ret_val)

;; test.spectec:4354.1-4354.85
def $data(state : fuck1state, dataidx : fuck1dataidx) : fuck1datainst
  ;; test.spectec:4370.1-4370.57
  def $data{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[x!`%`_uN.0]]

;; test.spectec:4354.6-4354.11
relation data_is_wf: `%%%`fuck5(state : fuck1state, dataidx : fuck1dataidx, ret_val : fuck1datainst)
  ;; test.spectec:4354.6-4354.11
  rule data_is_wf_0{state : fuck1state, dataidx : fuck1dataidx, ret_val : fuck1datainst}:
    `%%%`(state, dataidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, dataidx)
    -- if (ret_val = $data(state, dataidx))
    -- wf_datainst: `%`(ret_val)

;; test.spectec:4355.1-4355.85
def $elem(state : fuck1state, tableidx : fuck1tableidx) : fuck1eleminst
  ;; test.spectec:4371.1-4371.57
  def $elem{z : fuck1state, x : fuck1uN}(z, x) = $sof(z).ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[x!`%`_uN.0]]

;; test.spectec:4355.6-4355.11
relation elem_is_wf: `%%%`fuck5(state : fuck1state, tableidx : fuck1tableidx, ret_val : fuck1eleminst)
  ;; test.spectec:4355.6-4355.11
  rule elem_is_wf_0{state : fuck1state, tableidx : fuck1tableidx, ret_val : fuck1eleminst}:
    `%%%`(state, tableidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- if (ret_val = $elem(state, tableidx))
    -- wf_eleminst: `%`(ret_val)

;; test.spectec:4356.1-4356.85
def $local(state : fuck1state, localidx : fuck1localidx) : fuck6fuck1val?
  ;; test.spectec:4372.1-4372.37
  def $local{z : fuck1state, x : fuck1uN}(z, x) = $fof(z).LOCALS_frame[x!`%`_uN.0]

;; test.spectec:4356.6-4356.12
relation local_is_wf: `%%%`fuck5(state : fuck1state, localidx : fuck1localidx, `ret_val?` : fuck6fuck1val?)
  ;; test.spectec:4356.6-4356.12
  rule local_is_wf_0{state : fuck1state, localidx : fuck1localidx, `ret_val?` : fuck6fuck1val?}:
    `%%%`(state, localidx, `ret_val?`)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, localidx)
    -- if (`ret_val?` = $local(state, localidx))
    -- (wf_val: `%`(ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:4377.1-4377.165
def $with_local(state : fuck1state, localidx : fuck1localidx, val : fuck1val) : fuck1state
  ;; test.spectec:4388.1-4388.60
  def $with_local{z : fuck1state, x : fuck1uN, v : fuck1val}(z, x, v) = `%;%`_state($sof(z), $fof(z)[LOCALS_frame[x!`%`_uN.0] = ?(v)])

;; test.spectec:4377.6-4377.17
relation with_local_is_wf: `%%%%`fuck5(state : fuck1state, localidx : fuck1localidx, val : fuck1val, ret_val : fuck1state)
  ;; test.spectec:4377.6-4377.17
  rule with_local_is_wf_0{state : fuck1state, localidx : fuck1localidx, val : fuck1val, ret_val : fuck1state}:
    `%%%%`(state, localidx, val, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, localidx)
    -- wf_val: `%`(val)
    -- if (ret_val = $with_local(state, localidx, val))
    -- wf_state: `%`(ret_val)

;; test.spectec:4378.1-4378.172
def $with_global(state : fuck1state, globalidx : fuck1globalidx, val : fuck1val) : fuck1state
  ;; test.spectec:4389.1-4389.92
  def $with_global{z : fuck1state, x : fuck1uN, v : fuck1val}(z, x, v) = `%;%`_state($sof(z)[GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[x!`%`_uN.0]].VALUE_globalinst = v], $fof(z))

;; test.spectec:4378.6-4378.18
relation with_global_is_wf: `%%%%`fuck5(state : fuck1state, globalidx : fuck1globalidx, val : fuck1val, ret_val : fuck1state)
  ;; test.spectec:4378.6-4378.18
  rule with_global_is_wf_0{state : fuck1state, globalidx : fuck1globalidx, val : fuck1val, ret_val : fuck1state}:
    `%%%%`(state, globalidx, val, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, globalidx)
    -- wf_val: `%`(val)
    -- if (ret_val = $with_global(state, globalidx, val))
    -- wf_state: `%`(ret_val)

;; test.spectec:4379.1-4379.174
def $with_table(state : fuck1state, tableidx : fuck1tableidx, nat : fuck3nat, ref : fuck1ref) : fuck1state
  ;; test.spectec:4390.1-4390.94
  def $with_table{z : fuck1state, x : fuck1uN, i : fuck3nat, r : fuck1ref}(z, x, i, r) = `%;%`_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_uN.0]].REFS_tableinst[i] = r], $fof(z))

;; test.spectec:4379.6-4379.17
relation with_table_is_wf: `%%%%%`fuck5(state : fuck1state, tableidx : fuck1tableidx, nat : fuck3nat, ref : fuck1ref, ret_val : fuck1state)
  ;; test.spectec:4379.6-4379.17
  rule with_table_is_wf_0{state : fuck1state, tableidx : fuck1tableidx, nat : fuck3nat, ref : fuck1ref, ret_val : fuck1state}:
    `%%%%%`(state, tableidx, nat, ref, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- wf_ref: `%`(ref)
    -- if (ret_val = $with_table(state, tableidx, nat, ref))
    -- wf_state: `%`(ret_val)

;; test.spectec:4380.1-4380.165
def $with_tableinst(state : fuck1state, tableidx : fuck1tableidx, tableinst : fuck1tableinst) : fuck1state
  ;; test.spectec:4391.1-4391.89
  def $with_tableinst{z : fuck1state, x : fuck1uN, ti : fuck1tableinst}(z, x, ti) = `%;%`_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_uN.0]] = ti], $fof(z))

;; test.spectec:4380.6-4380.21
relation with_tableinst_is_wf: `%%%%`fuck5(state : fuck1state, tableidx : fuck1tableidx, tableinst : fuck1tableinst, ret_val : fuck1state)
  ;; test.spectec:4380.6-4380.21
  rule with_tableinst_is_wf_0{state : fuck1state, tableidx : fuck1tableidx, tableinst : fuck1tableinst, ret_val : fuck1state}:
    `%%%%`(state, tableidx, tableinst, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- wf_tableinst: `%`(tableinst)
    -- if (ret_val = $with_tableinst(state, tableidx, tableinst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4381.1-4381.176
def $with_mem(state : fuck1state, memidx : fuck1memidx, nat : fuck3nat, nat : fuck3nat, fuck6fuck1byte*) : fuck1state
  ;; test.spectec:4392.1-4392.98
  def $with_mem{z : fuck1state, x : fuck1uN, i : fuck3nat, j : fuck3nat, `b*` : fuck6fuck1byte*}(z, x, i, j, b*{b <- `b*`}) = `%;%`_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_uN.0]].BYTES_meminst[i : j] = b*{b <- `b*`}], $fof(z))

;; test.spectec:4381.6-4381.15
relation with_mem_is_wf: `%%%%%%`fuck5(state : fuck1state, memidx : fuck1memidx, nat : fuck3nat, nat_0 : fuck3nat, `var_0*` : fuck6fuck1byte*, ret_val : fuck1state)
  ;; test.spectec:4381.6-4381.15
  rule with_mem_is_wf_0{state : fuck1state, memidx : fuck1memidx, nat : fuck3nat, nat_0 : fuck3nat, `var_0*` : fuck6fuck1byte*, ret_val : fuck1state}:
    `%%%%%%`(state, memidx, nat, nat_0, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, memidx)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $with_mem(state, memidx, nat, nat_0, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:4382.1-4382.167
def $with_meminst(state : fuck1state, memidx : fuck1memidx, meminst : fuck1meminst) : fuck1state
  ;; test.spectec:4393.1-4393.83
  def $with_meminst{z : fuck1state, x : fuck1uN, mi : fuck1meminst}(z, x, mi) = `%;%`_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_uN.0]] = mi], $fof(z))

;; test.spectec:4382.6-4382.19
relation with_meminst_is_wf: `%%%%`fuck5(state : fuck1state, memidx : fuck1memidx, meminst : fuck1meminst, ret_val : fuck1state)
  ;; test.spectec:4382.6-4382.19
  rule with_meminst_is_wf_0{state : fuck1state, memidx : fuck1memidx, meminst : fuck1meminst, ret_val : fuck1state}:
    `%%%%`(state, memidx, meminst, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, memidx)
    -- wf_meminst: `%`(meminst)
    -- if (ret_val = $with_meminst(state, memidx, meminst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4383.1-4383.169
def $with_elem(state : fuck1state, elemidx : fuck1elemidx, fuck6fuck1ref*) : fuck1state
  ;; test.spectec:4394.1-4394.87
  def $with_elem{z : fuck1state, x : fuck1uN, `r*` : fuck6fuck1ref*}(z, x, r*{r <- `r*`}) = `%;%`_state($sof(z)[ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[x!`%`_uN.0]].REFS_eleminst = r*{r <- `r*`}], $fof(z))

;; test.spectec:4383.6-4383.16
relation with_elem_is_wf: `%%%%`fuck5(state : fuck1state, elemidx : fuck1elemidx, `var_0*` : fuck6fuck1ref*, ret_val : fuck1state)
  ;; test.spectec:4383.6-4383.16
  rule with_elem_is_wf_0{state : fuck1state, elemidx : fuck1elemidx, `var_0*` : fuck6fuck1ref*, ret_val : fuck1state}:
    `%%%%`(state, elemidx, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, elemidx)
    -- (wf_ref: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $with_elem(state, elemidx, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:4384.1-4384.170
def $with_data(state : fuck1state, dataidx : fuck1dataidx, fuck6fuck1byte*) : fuck1state
  ;; test.spectec:4395.1-4395.88
  def $with_data{z : fuck1state, x : fuck1uN, `b*` : fuck6fuck1byte*}(z, x, b*{b <- `b*`}) = `%;%`_state($sof(z)[DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[x!`%`_uN.0]].BYTES_datainst = b*{b <- `b*`}], $fof(z))

;; test.spectec:4384.6-4384.16
relation with_data_is_wf: `%%%%`fuck5(state : fuck1state, dataidx : fuck1dataidx, `var_0*` : fuck6fuck1byte*, ret_val : fuck1state)
  ;; test.spectec:4384.6-4384.16
  rule with_data_is_wf_0{state : fuck1state, dataidx : fuck1dataidx, `var_0*` : fuck6fuck1byte*, ret_val : fuck1state}:
    `%%%%`(state, dataidx, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, dataidx)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $with_data(state, dataidx, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:4385.1-4385.181
def $with_struct(state : fuck1state, structaddr : fuck1structaddr, nat : fuck3nat, fieldval : fuck1fieldval) : fuck1state
  ;; test.spectec:4396.1-4396.77
  def $with_struct{z : fuck1state, a : fuck3nat, i : fuck3nat, fv : fuck1fieldval}(z, a, i, fv) = `%;%`_state($sof(z)[STRUCTS_store[a].FIELDS_structinst[i] = fv], $fof(z))

;; test.spectec:4385.6-4385.18
relation with_struct_is_wf: `%%%%%`fuck5(state : fuck1state, structaddr : fuck1structaddr, nat : fuck3nat, fieldval : fuck1fieldval, ret_val : fuck1state)
  ;; test.spectec:4385.6-4385.18
  rule with_struct_is_wf_0{state : fuck1state, structaddr : fuck1structaddr, nat : fuck3nat, fieldval : fuck1fieldval, ret_val : fuck1state}:
    `%%%%%`(state, structaddr, nat, fieldval, ret_val)
    -- wf_state: `%`(state)
    -- wf_fieldval: `%`(fieldval)
    -- if (ret_val = $with_struct(state, structaddr, nat, fieldval))
    -- wf_state: `%`(ret_val)

;; test.spectec:4386.1-4386.180
def $with_array(state : fuck1state, arrayaddr : fuck1arrayaddr, nat : fuck3nat, fieldval : fuck1fieldval) : fuck1state
  ;; test.spectec:4397.1-4397.75
  def $with_array{z : fuck1state, a : fuck3nat, i : fuck3nat, fv : fuck1fieldval}(z, a, i, fv) = `%;%`_state($sof(z)[ARRAYS_store[a].FIELDS_arrayinst[i] = fv], $fof(z))

;; test.spectec:4386.6-4386.17
relation with_array_is_wf: `%%%%%`fuck5(state : fuck1state, arrayaddr : fuck1arrayaddr, nat : fuck3nat, fieldval : fuck1fieldval, ret_val : fuck1state)
  ;; test.spectec:4386.6-4386.17
  rule with_array_is_wf_0{state : fuck1state, arrayaddr : fuck1arrayaddr, nat : fuck3nat, fieldval : fuck1fieldval, ret_val : fuck1state}:
    `%%%%%`(state, arrayaddr, nat, fieldval, ret_val)
    -- wf_state: `%`(state)
    -- wf_fieldval: `%`(fieldval)
    -- if (ret_val = $with_array(state, arrayaddr, nat, fieldval))
    -- wf_state: `%`(ret_val)

;; test.spectec:4400.1-4400.140
def $add_structinst(state : fuck1state, fuck6fuck1structinst*) : fuck1state
  ;; test.spectec:4404.1-4404.65
  def $add_structinst{z : fuck1state, `si*` : fuck6fuck1structinst*}(z, si*{si <- `si*`}) = `%;%`_state($sof(z)[STRUCTS_store =++ si*{si <- `si*`}], $fof(z))

;; test.spectec:4400.6-4400.21
relation add_structinst_is_wf: `%%%`fuck5(state : fuck1state, `var_0*` : fuck6fuck1structinst*, ret_val : fuck1state)
  ;; test.spectec:4400.6-4400.21
  rule add_structinst_is_wf_0{state : fuck1state, `var_0*` : fuck6fuck1structinst*, ret_val : fuck1state}:
    `%%%`(state, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- (wf_structinst: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $add_structinst(state, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:4401.1-4401.139
def $add_arrayinst(state : fuck1state, fuck6fuck1arrayinst*) : fuck1state
  ;; test.spectec:4405.1-4405.63
  def $add_arrayinst{z : fuck1state, `ai*` : fuck6fuck1arrayinst*}(z, ai*{ai <- `ai*`}) = `%;%`_state($sof(z)[ARRAYS_store =++ ai*{ai <- `ai*`}], $fof(z))

;; test.spectec:4401.6-4401.20
relation add_arrayinst_is_wf: `%%%`fuck5(state : fuck1state, `var_0*` : fuck6fuck1arrayinst*, ret_val : fuck1state)
  ;; test.spectec:4401.6-4401.20
  rule add_arrayinst_is_wf_0{state : fuck1state, `var_0*` : fuck6fuck1arrayinst*, ret_val : fuck1state}:
    `%%%`(state, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- (wf_arrayinst: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $add_arrayinst(state, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:4402.1-4402.137
def $add_exninst(state : fuck1state, fuck6fuck1exninst*) : fuck1state
  ;; test.spectec:4406.1-4406.61
  def $add_exninst{z : fuck1state, `exn*` : fuck6fuck1exninst*}(z, exn*{exn <- `exn*`}) = `%;%`_state($sof(z)[EXNS_store =++ exn*{exn <- `exn*`}], $fof(z))

;; test.spectec:4402.6-4402.18
relation add_exninst_is_wf: `%%%`fuck5(state : fuck1state, `var_0*` : fuck6fuck1exninst*, ret_val : fuck1state)
  ;; test.spectec:4402.6-4402.18
  rule add_exninst_is_wf_0{state : fuck1state, `var_0*` : fuck6fuck1exninst*, ret_val : fuck1state}:
    `%%%`(state, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- (wf_exninst: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $add_exninst(state, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:4411.1-4411.62
def $growtable(tableinst : fuck1tableinst, nat : fuck3nat, ref : fuck1ref) : fuck1tableinst
  ;; test.spectec:4414.1-4419.33
  def $growtable{tableinst : fuck1tableinst, n : fuck3nat, r : fuck1ref, tableinst' : fuck1tableinst, i' : fuck1uN}(tableinst, n, r) = tableinst'
    -- let{at : fuck1addrtype, i : fuck1u64, `j?` : fuck6fuck1u64?, rt : fuck1reftype, `r'*` : fuck6fuck1ref*} {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`}} = tableinst
    -- if (tableinst' = {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i', j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`} ++ r^n{}})
    -- if (i'!`%`_uN.0 = (|r'*{r' <- `r'*`}| + n))
    -- (if (i'!`%`_uN.0 <= j!`%`_uN.0))?{j <- `j?`}
    -- if ((i'!`%`_uN.0 : nat <:> int) <= (((2 ^ $size((at : fuck1addrtype <: fuck1numtype))) : nat <:> int) - (1 : nat <:> int)))
    -- wf_tableinst: `%`({TYPE `%%%`_tabletype(at, `[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`}})
    -- wf_tableinst: `%`({TYPE `%%%`_tabletype(at, `[%..%]`_limits(i', j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`} ++ r^n{}})

;; test.spectec:4411.6-4411.16
relation growtable_is_wf: `%%%%`fuck5(tableinst : fuck1tableinst, nat : fuck3nat, ref : fuck1ref, ret_val : fuck1tableinst)
  ;; test.spectec:4411.6-4411.16
  rule growtable_is_wf_0{tableinst : fuck1tableinst, nat : fuck3nat, ref : fuck1ref, ret_val : fuck1tableinst}:
    `%%%%`(tableinst, nat, ref, ret_val)
    -- wf_tableinst: `%`(tableinst)
    -- wf_ref: `%`(ref)
    -- if (ret_val = $growtable(tableinst, nat, ref))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:4412.1-4412.62
def $growmem(meminst : fuck1meminst, nat : fuck3nat) : fuck1meminst
  ;; test.spectec:4421.1-4426.36
  def $growmem{meminst : fuck1meminst, n : fuck3nat, meminst' : fuck1meminst, i' : fuck1uN}(meminst, n) = meminst'
    -- let{at : fuck1addrtype, i : fuck1u64, `j?` : fuck6fuck1u64?, `b*` : fuck6fuck1byte*} {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i, j?{j <- `j?`})), BYTES b*{b <- `b*`}} = meminst
    -- if (meminst' = {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i', j?{j <- `j?`})), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})
    -- if ((i'!`%`_uN.0 : nat <:> rat) = (((|b*{b <- `b*`}| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (n : nat <:> rat)))
    -- (if (i'!`%`_uN.0 <= j!`%`_uN.0))?{j <- `j?`}
    -- if (i'!`%`_uN.0 <= (2 ^ ((($size((at : fuck1addrtype <: fuck1numtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))
    -- wf_meminst: `%`({TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i, j?{j <- `j?`})), BYTES b*{b <- `b*`}})
    -- wf_meminst: `%`({TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i', j?{j <- `j?`})), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})

;; test.spectec:4412.6-4412.14
relation growmem_is_wf: `%%%`fuck5(meminst : fuck1meminst, nat : fuck3nat, ret_val : fuck1meminst)
  ;; test.spectec:4412.6-4412.14
  rule growmem_is_wf_0{meminst : fuck1meminst, nat : fuck3nat, ret_val : fuck1meminst}:
    `%%%`(meminst, nat, ret_val)
    -- wf_meminst: `%`(meminst)
    -- if (ret_val = $growmem(meminst, nat))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:4457.1-4457.60
relation Num_ok: `%|-%:%`fuck5(fuck1store, fuck1num, fuck1numtype)
  ;; test.spectec:4462.1-4463.23
  rule _{s : fuck1store, nt : fuck1numtype, c : fuck1num_}:
    `%|-%:%`(s, CONST_num(nt, c), nt)
    -- wf_store: `%`(s)
    -- wf_num: `%`(CONST_num(nt, c))

;; test.spectec:4458.1-4458.60
relation Vec_ok: `%|-%:%`fuck5(fuck1store, fuck1vec, fuck1vectype)
  ;; test.spectec:4465.1-4466.24
  rule _{s : fuck1store, vt : fuck1vectype, c : fuck1vec_}:
    `%|-%:%`(s, VCONST_vec(vt, c), vt)
    -- wf_store: `%`(s)
    -- wf_vec: `%`(VCONST_vec(vt, c))

;; test.spectec:4459.1-4459.60
rec {

;; test.spectec:4459.1-4459.60
relation Ref_ok: `%|-%:%`fuck5(fuck1store, fuck1ref, fuck1reftype)
  ;; test.spectec:4469.1-4470.36
  rule null{s : fuck1store}:
    `%|-%:%`(s, `REF.NULL_ADDR`_ref, REF_reftype(?(NULL_null), BOT_heaptype))
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.NULL_ADDR`_ref)
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), BOT_heaptype))

  ;; test.spectec:4472.1-4473.31
  rule i31{s : fuck1store, i : fuck1u31}:
    `%|-%:%`(s, `REF.I31_NUM`_ref(i), REF_reftype(?(), I31_heaptype))
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.I31_NUM`_ref(i))
    -- wf_reftype: `%`(REF_reftype(?(), I31_heaptype))

  ;; test.spectec:4475.1-4477.31
  rule struct{s : fuck1store, a : fuck1addr, dt : fuck1deftype}:
    `%|-%:%`(s, `REF.STRUCT_ADDR`_ref(a), REF_reftype(?(), (dt : fuck1deftype <: fuck1heaptype)))
    -- if (s.STRUCTS_store[a].TYPE_structinst = dt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.STRUCT_ADDR`_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), (dt : fuck1deftype <: fuck1heaptype)))

  ;; test.spectec:4479.1-4481.30
  rule array{s : fuck1store, a : fuck1addr, dt : fuck1deftype}:
    `%|-%:%`(s, `REF.ARRAY_ADDR`_ref(a), REF_reftype(?(), (dt : fuck1deftype <: fuck1heaptype)))
    -- if (s.ARRAYS_store[a].TYPE_arrayinst = dt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.ARRAY_ADDR`_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), (dt : fuck1deftype <: fuck1heaptype)))

  ;; test.spectec:4483.1-4485.29
  rule func{s : fuck1store, a : fuck1addr, dt : fuck1deftype}:
    `%|-%:%`(s, `REF.FUNC_ADDR`_ref(a), REF_reftype(?(), (dt : fuck1deftype <: fuck1heaptype)))
    -- if (s.FUNCS_store[a].TYPE_funcinst = dt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.FUNC_ADDR`_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), (dt : fuck1deftype <: fuck1heaptype)))

  ;; test.spectec:4487.1-4489.24
  rule exn{s : fuck1store, a : fuck1addr, exn : fuck1exninst}:
    `%|-%:%`(s, `REF.EXN_ADDR`_ref(a), REF_reftype(?(), EXN_heaptype))
    -- if (s.EXNS_store[a] = exn)
    -- wf_store: `%`(s)
    -- wf_exninst: `%`(exn)
    -- wf_ref: `%`(`REF.EXN_ADDR`_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), EXN_heaptype))

  ;; test.spectec:4491.1-4492.33
  rule host{s : fuck1store, a : fuck1addr}:
    `%|-%:%`(s, `REF.HOST_ADDR`_ref(a), REF_reftype(?(), ANY_heaptype))
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.HOST_ADDR`_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), ANY_heaptype))

  ;; test.spectec:4494.1-4497.30
  rule extern{s : fuck1store, ref : fuck1ref}:
    `%|-%:%`(s, `REF.EXTERN`_ref(ref), REF_reftype(?(), EXTERN_heaptype))
    -- Ref_ok: `%|-%:%`(s, ref, REF_reftype(?(), ANY_heaptype))
    -- if (ref =/= `REF.NULL_ADDR`_ref)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(`REF.EXTERN`_ref(ref))
    -- wf_reftype: `%`(REF_reftype(?(), EXTERN_heaptype))
    -- wf_reftype: `%`(REF_reftype(?(), ANY_heaptype))
    -- wf_ref: `%`(`REF.NULL_ADDR`_ref)

  ;; test.spectec:4499.1-4503.34
  rule sub{s : fuck1store, ref : fuck1ref, rt : fuck1reftype, rt' : fuck1reftype}:
    `%|-%:%`(s, ref, rt)
    -- Ref_ok: `%|-%:%`(s, ref, rt')
    -- Reftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt)
    -- Reftype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt', rt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(ref)
    -- wf_reftype: `%`(rt)
    -- wf_reftype: `%`(rt')
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:4460.1-4460.60
relation Val_ok: `%|-%:%`fuck5(fuck1store, fuck1val, fuck1valtype)
  ;; test.spectec:4506.1-4508.27
  rule num{s : fuck1store, num : fuck1num, nt : fuck1numtype}:
    `%|-%:%`(s, (num : fuck1num <: fuck1val), (nt : fuck1numtype <: fuck1valtype))
    -- Num_ok: `%|-%:%`(s, num, nt)
    -- wf_store: `%`(s)
    -- wf_num: `%`(num)

  ;; test.spectec:4510.1-4512.27
  rule vec{s : fuck1store, vec : fuck1vec, vt : fuck1vectype}:
    `%|-%:%`(s, (vec : fuck1vec <: fuck1val), (vt : fuck1vectype <: fuck1valtype))
    -- Vec_ok: `%|-%:%`(s, vec, vt)
    -- wf_store: `%`(s)
    -- wf_vec: `%`(vec)

  ;; test.spectec:4514.1-4516.27
  rule ref{s : fuck1store, ref : fuck1ref, rt : fuck1reftype}:
    `%|-%:%`(s, (ref : fuck1ref <: fuck1val), (rt : fuck1reftype <: fuck1valtype))
    -- Ref_ok: `%|-%:%`(s, ref, rt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(ref)
    -- wf_reftype: `%`(rt)

;; test.spectec:4521.1-4521.49
relation Packval_ok: `%|-%:%`fuck5(fuck1store, fuck1packval, fuck1packtype)
  ;; test.spectec:4524.1-4525.22
  rule _{s : fuck1store, pt : fuck1packtype, c : fuck1iN}:
    `%|-%:%`(s, PACK_packval(pt, c), pt)
    -- wf_store: `%`(s)
    -- wf_packval: `%`(PACK_packval(pt, c))

;; test.spectec:4522.1-4522.54
relation Fieldval_ok: `%|-%:%`fuck5(fuck1store, fuck1fieldval, fuck1storagetype)
  ;; test.spectec:4527.1-4529.26
  rule val{s : fuck1store, val : fuck1val, t : fuck1valtype}:
    `%|-%:%`(s, (val : fuck1val <: fuck1fieldval), (t : fuck1valtype <: fuck1storagetype))
    -- Val_ok: `%|-%:%`(s, val, t)
    -- wf_store: `%`(s)
    -- wf_val: `%`(val)
    -- wf_valtype: `%`(t)

  ;; test.spectec:4531.1-4533.35
  rule packval{s : fuck1store, packval : fuck1packval, pt : fuck1packtype}:
    `%|-%:%`(s, (packval : fuck1packval <: fuck1fieldval), (pt : fuck1packtype <: fuck1storagetype))
    -- Packval_ok: `%|-%:%`(s, packval, pt)
    -- wf_store: `%`(s)
    -- wf_packval: `%`(packval)

;; test.spectec:4538.1-4538.84
rec {

;; test.spectec:4538.1-4538.84
relation Externaddr_ok: `%|-%:%`fuck5(fuck1store, fuck1externaddr, fuck1externtype)
  ;; test.spectec:4540.1-4542.28
  rule tag{s : fuck1store, a : fuck1addr, taginst : fuck1taginst}:
    `%|-%:%`(s, TAG_externaddr(a), TAG_externtype(taginst.TYPE_taginst))
    -- if (s.TAGS_store[a] = taginst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TAG_externtype(taginst.TYPE_taginst))

  ;; test.spectec:4544.1-4546.34
  rule global{s : fuck1store, a : fuck1addr, globalinst : fuck1globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(globalinst.TYPE_globalinst))
    -- if (s.GLOBALS_store[a] = globalinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(GLOBAL_externtype(globalinst.TYPE_globalinst))

  ;; test.spectec:4548.1-4550.28
  rule mem{s : fuck1store, a : fuck1addr, meminst : fuck1meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(meminst.TYPE_meminst))
    -- if (s.MEMS_store[a] = meminst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(MEM_externtype(meminst.TYPE_meminst))

  ;; test.spectec:4552.1-4554.32
  rule table{s : fuck1store, a : fuck1addr, tableinst : fuck1tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(tableinst.TYPE_tableinst))
    -- if (s.TABLES_store[a] = tableinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TABLE_externtype(tableinst.TYPE_tableinst))

  ;; test.spectec:4556.1-4558.30
  rule func{s : fuck1store, a : fuck1addr, funcinst : fuck1funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype((funcinst.TYPE_funcinst : fuck1deftype <: fuck1typeuse)))
    -- if (s.FUNCS_store[a] = funcinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(FUNC_externtype((funcinst.TYPE_funcinst : fuck1deftype <: fuck1typeuse)))

  ;; test.spectec:4560.1-4564.37
  rule sub{s : fuck1store, externaddr : fuck1externaddr, xt : fuck1externtype, xt' : fuck1externtype}:
    `%|-%:%`(s, externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, externaddr, xt')
    -- Externtype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt)
    -- Externtype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt', xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_externtype: `%`(xt')
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:4577.1-4577.96
def $inst_valtype(moduleinst : fuck1moduleinst, valtype : fuck1valtype) : fuck1valtype
  ;; test.spectec:4583.1-4583.75
  def $inst_valtype{moduleinst : fuck1moduleinst, t : fuck1valtype}(moduleinst, t) = $subst_all_valtype(t, (moduleinst.TYPES_moduleinst : fuck6fuck1deftype* <: fuck6fuck1typeuse*))

;; test.spectec:4577.6-4577.19
relation inst_valtype_is_wf: `%%%`fuck5(moduleinst : fuck1moduleinst, valtype : fuck1valtype, ret_val : fuck1valtype)
  ;; test.spectec:4577.6-4577.19
  rule inst_valtype_is_wf_0{moduleinst : fuck1moduleinst, valtype : fuck1valtype, ret_val : fuck1valtype}:
    `%%%`(moduleinst, valtype, ret_val)
    -- wf_moduleinst: `%`(moduleinst)
    -- wf_valtype: `%`(valtype)
    -- if (ret_val = $inst_valtype(moduleinst, valtype))
    -- wf_valtype: `%`(ret_val)

;; test.spectec:4578.1-4578.96
def $inst_reftype(moduleinst : fuck1moduleinst, reftype : fuck1reftype) : fuck1reftype
  ;; test.spectec:4584.1-4584.77
  def $inst_reftype{moduleinst : fuck1moduleinst, rt : fuck1reftype}(moduleinst, rt) = $subst_all_reftype(rt, (moduleinst.TYPES_moduleinst : fuck6fuck1deftype* <: fuck6fuck1typeuse*))

;; test.spectec:4578.6-4578.19
relation inst_reftype_is_wf: `%%%`fuck5(moduleinst : fuck1moduleinst, reftype : fuck1reftype, ret_val : fuck1reftype)
  ;; test.spectec:4578.6-4578.19
  rule inst_reftype_is_wf_0{moduleinst : fuck1moduleinst, reftype : fuck1reftype, ret_val : fuck1reftype}:
    `%%%`(moduleinst, reftype, ret_val)
    -- wf_moduleinst: `%`(moduleinst)
    -- wf_reftype: `%`(reftype)
    -- if (ret_val = $inst_reftype(moduleinst, reftype))
    -- wf_reftype: `%`(ret_val)

;; test.spectec:4579.1-4579.105
def $inst_globaltype(moduleinst : fuck1moduleinst, globaltype : fuck1globaltype) : fuck1globaltype
  ;; test.spectec:4585.1-4585.83
  def $inst_globaltype{moduleinst : fuck1moduleinst, gt : fuck1globaltype}(moduleinst, gt) = $subst_all_globaltype(gt, (moduleinst.TYPES_moduleinst : fuck6fuck1deftype* <: fuck6fuck1typeuse*))

;; test.spectec:4579.6-4579.22
relation inst_globaltype_is_wf: `%%%`fuck5(moduleinst : fuck1moduleinst, globaltype : fuck1globaltype, ret_val : fuck1globaltype)
  ;; test.spectec:4579.6-4579.22
  rule inst_globaltype_is_wf_0{moduleinst : fuck1moduleinst, globaltype : fuck1globaltype, ret_val : fuck1globaltype}:
    `%%%`(moduleinst, globaltype, ret_val)
    -- wf_moduleinst: `%`(moduleinst)
    -- wf_globaltype: `%`(globaltype)
    -- if (ret_val = $inst_globaltype(moduleinst, globaltype))
    -- wf_globaltype: `%`(ret_val)

;; test.spectec:4580.1-4580.96
def $inst_memtype(moduleinst : fuck1moduleinst, memtype : fuck1memtype) : fuck1memtype
  ;; test.spectec:4586.1-4586.77
  def $inst_memtype{moduleinst : fuck1moduleinst, mt : fuck1memtype}(moduleinst, mt) = $subst_all_memtype(mt, (moduleinst.TYPES_moduleinst : fuck6fuck1deftype* <: fuck6fuck1typeuse*))

;; test.spectec:4580.6-4580.19
relation inst_memtype_is_wf: `%%%`fuck5(moduleinst : fuck1moduleinst, memtype : fuck1memtype, ret_val : fuck1memtype)
  ;; test.spectec:4580.6-4580.19
  rule inst_memtype_is_wf_0{moduleinst : fuck1moduleinst, memtype : fuck1memtype, ret_val : fuck1memtype}:
    `%%%`(moduleinst, memtype, ret_val)
    -- wf_moduleinst: `%`(moduleinst)
    -- wf_memtype: `%`(memtype)
    -- if (ret_val = $inst_memtype(moduleinst, memtype))
    -- wf_memtype: `%`(ret_val)

;; test.spectec:4581.1-4581.102
def $inst_tabletype(moduleinst : fuck1moduleinst, tabletype : fuck1tabletype) : fuck1tabletype
  ;; test.spectec:4587.1-4587.81
  def $inst_tabletype{moduleinst : fuck1moduleinst, tt : fuck1tabletype}(moduleinst, tt) = $subst_all_tabletype(tt, (moduleinst.TYPES_moduleinst : fuck6fuck1deftype* <: fuck6fuck1typeuse*))

;; test.spectec:4581.6-4581.21
relation inst_tabletype_is_wf: `%%%`fuck5(moduleinst : fuck1moduleinst, tabletype : fuck1tabletype, ret_val : fuck1tabletype)
  ;; test.spectec:4581.6-4581.21
  rule inst_tabletype_is_wf_0{moduleinst : fuck1moduleinst, tabletype : fuck1tabletype, ret_val : fuck1tabletype}:
    `%%%`(moduleinst, tabletype, ret_val)
    -- wf_moduleinst: `%`(moduleinst)
    -- wf_tabletype: `%`(tabletype)
    -- if (ret_val = $inst_tabletype(moduleinst, tabletype))
    -- wf_tabletype: `%`(ret_val)

