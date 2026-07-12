
;; test.spectec:5.1-5.32
syntax N = nat

;; test.spectec:6.1-6.32
syntax M = nat

;; test.spectec:7.1-7.32
syntax K = nat

;; test.spectec:8.1-8.32
syntax n = nat

;; test.spectec:9.1-9.32
syntax m = nat

;; test.spectec:22.1-22.25
def $min(nat : nat, nat_0 : nat) : nat
  ;; test.spectec:23.1-23.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:26.1-26.56
rec {

;; test.spectec:26.6-26.10
relation fun_sum: `%%`(nat*, nat)
  ;; test.spectec:26.6-26.10
  rule fun_sum_case_0:
    `%%`([], 0)

  ;; test.spectec:26.6-26.10
  rule fun_sum_case_1{v_n : nat, n'_lst : n*, var_0 : nat}:
    `%%`([v_n] ++ n'_lst, (v_n + var_0))
    -- fun_sum: `%%`(n'_lst, var_0)
}

;; test.spectec:30.1-30.57
rec {

;; test.spectec:30.6-30.11
relation fun_prod: `%%`(nat*, nat)
  ;; test.spectec:30.6-30.11
  rule fun_prod_case_0:
    `%%`([], 1)

  ;; test.spectec:30.6-30.11
  rule fun_prod_case_1{v_n : nat, n'_lst : n*, var_0 : nat}:
    `%%`([v_n] ++ n'_lst, (v_n * var_0))
    -- fun_prod: `%%`(n'_lst, var_0)
}

;; test.spectec:47.1-47.58
def $opt_(syntax X, var_0_lst : X*) : X??
  ;; test.spectec:48.1-48.31
  def $opt_{syntax X}(syntax X, []) = ?(?())
  ;; test.spectec:49.1-49.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(?(w))
  def $opt_{syntax X, x1 : X*}(syntax X, x1) = ?()
    -- otherwise

;; test.spectec:54.1-54.82
rec {

;; test.spectec:54.1-54.82
def $concat_(syntax X, var_0_lst_lst : X**) : X*
  ;; test.spectec:55.1-55.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; test.spectec:56.1-56.64
  def $concat_{syntax X, w_lst : X*, w'_lst_lst : X**}(syntax X, [w_lst] ++ w'_lst_lst) = w_lst ++ $concat_(syntax X, w'_lst_lst)
}

;; test.spectec:58.1-58.89
rec {

;; test.spectec:58.1-58.89
def $concatn_(syntax X, var_0_lst_lst : X**, nat : nat) : X*
  ;; test.spectec:59.1-59.38
  def $concatn_{syntax X, v_n : nat}(syntax X, [], v_n) = []
  ;; test.spectec:60.1-60.73
  def $concatn_{syntax X, v_n : nat, w_lst : X*, w'_lst_lst : X**}(syntax X, [w_lst] ++ w'_lst_lst, v_n) = w_lst ++ $concatn_(syntax X, w'_lst_lst, v_n)
    -- if (v_n = |w_lst|)
    -- (if (v_n = |w'_lst_2|))*{w'_lst_2 <- w'_lst_lst}
}

;; test.spectec:62.1-62.58
def $concatopt_(syntax X, var_0_opt_lst : X?*) : X*
  ;; test.spectec:63.1-63.37
  def $concatopt_{syntax X}(syntax X, []) = []
  ;; test.spectec:64.1-64.67
  def $concatopt_{syntax X, w_opt : X?, w'_opt_lst : X?*}(syntax X, [w_opt] ++ w'_opt_lst) = lift(w_opt) ++ $concat_(syntax X, lift(w'_opt)*{w'_opt <- w'_opt_lst})

;; test.spectec:66.1-66.39
def $inv_concat_(syntax X, var_0_lst : X*) : X**

;; test.spectec:69.1-69.45
def $inv_concatn_(syntax X, nat : nat, var_0_lst : X*) : X**

;; test.spectec:75.1-75.78
rec {

;; test.spectec:75.1-75.78
def $disjoint_(syntax X, var_0_lst : X*) : bool
  ;; test.spectec:76.1-76.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; test.spectec:77.1-77.68
  def $disjoint_{syntax X, w : X, w'_lst : X*}(syntax X, [w] ++ w'_lst) = (~ (w <- w'_lst) /\ $disjoint_(syntax X, w'_lst))
}

;; test.spectec:80.1-80.38
rec {

;; test.spectec:80.1-80.38
def $setminus1_(syntax X, X_0 : X, var_0_lst : X*) : X*
  ;; test.spectec:84.1-84.38
  def $setminus1_{syntax X, w : X}(syntax X, w, []) = [w]
  ;; test.spectec:85.1-85.78
  def $setminus1_{syntax X, w : X, w_1 : X, w'_lst : X*}(syntax X, w, [w_1] ++ w'_lst) = (if (w = w_1) then [] else $setminus1_(syntax X, w, w'_lst))
}

;; test.spectec:79.1-79.56
rec {

;; test.spectec:79.1-79.56
def $setminus_(syntax X, var_0_lst : X*, var_1_lst : X*) : X*
  ;; test.spectec:82.1-82.40
  def $setminus_{syntax X, w_lst : X*}(syntax X, [], w_lst) = []
  ;; test.spectec:83.1-83.90
  def $setminus_{syntax X, w_1 : X, w'_lst : X*, w_lst : X*}(syntax X, [w_1] ++ w'_lst, w_lst) = $setminus1_(syntax X, w_1, w_lst) ++ $setminus_(syntax X, w'_lst, w_lst)
}

;; test.spectec:91.1-91.46
rec {

;; test.spectec:91.1-91.46
def $setproduct2_(syntax X, X_0 : X, var_0_lst_lst : X**) : X**
  ;; test.spectec:97.1-97.44
  def $setproduct2_{syntax X, w_1 : X}(syntax X, w_1, []) = []
  ;; test.spectec:98.1-98.90
  def $setproduct2_{syntax X, w_1 : X, w'_lst : X*, w_lst_lst : X**}(syntax X, w_1, [w'_lst] ++ w_lst_lst) = [[w_1] ++ w'_lst] ++ $setproduct2_(syntax X, w_1, w_lst_lst)
}

;; test.spectec:90.1-90.47
rec {

;; test.spectec:90.1-90.47
def $setproduct1_(syntax X, var_0_lst : X*, var_1_lst_lst : X**) : X**
  ;; test.spectec:95.1-95.46
  def $setproduct1_{syntax X, w_lst_lst : X**}(syntax X, [], w_lst_lst) = []
  ;; test.spectec:96.1-96.107
  def $setproduct1_{syntax X, w_1 : X, w'_lst : X*, w_lst_lst : X**}(syntax X, [w_1] ++ w'_lst, w_lst_lst) = $setproduct2_(syntax X, w_1, w_lst_lst) ++ $setproduct1_(syntax X, w'_lst, w_lst_lst)
}

;; test.spectec:89.1-89.84
rec {

;; test.spectec:89.1-89.84
def $setproduct_(syntax X, var_0_lst_lst : X**) : X**
  ;; test.spectec:93.1-93.40
  def $setproduct_{syntax X}(syntax X, []) = [[]]
  ;; test.spectec:94.1-94.90
  def $setproduct_{syntax X, w_1_lst : X*, w_lst_lst : X**}(syntax X, [w_1_lst] ++ w_lst_lst) = $setproduct1_(syntax X, w_1_lst, $setproduct_(syntax X, w_lst_lst))
}

;; test.spectec:111.1-111.29
def $ND : bool

;; test.spectec:126.1-126.37
syntax bit = 
  | mk_bit(i : nat)

;; test.spectec:126.8-126.11
relation wf_bit: `%`(bit)
  ;; test.spectec:126.8-126.11
  rule bit_case_0{i : nat}:
    `%`(mk_bit_bit(i))
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:127.1-127.50
syntax byte = 
  | mk_byte(i : nat)

;; test.spectec:127.8-127.12
relation wf_byte: `%`(byte)
  ;; test.spectec:127.8-127.12
  rule byte_case_0{i : nat}:
    `%`(mk_byte_byte(i))
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:129.1-130.25
syntax uN = 
  | mk_uN(i : nat)

;; test.spectec:129.1-130.25
def $proj_uN_0(x : uN) : (nat)
  ;; test.spectec:129.1-130.25
  def $proj_uN_0{v_num_0 : nat}(mk_uN_uN(v_num_0)) = (v_num_0)

;; test.spectec:129.8-129.11
relation wf_uN: `%%`(N, uN)
  ;; test.spectec:129.8-129.11
  rule uN_case_0{v_N : N, i : nat}:
    `%%`(v_N, mk_uN_uN(i))
    -- if ((i >= 0) /\ (i <= ((((2 ^ v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:131.1-132.50
syntax sN = 
  | mk_sN(i : int)

;; test.spectec:131.8-131.11
relation wf_sN: `%%`(N, sN)
  ;; test.spectec:131.8-131.11
  rule sN_case_0{v_N : N, i : int}:
    `%%`(v_N, mk_sN_sN(i))
    -- if ((((i >= - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (+ ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; test.spectec:133.1-134.8
syntax iN = uN

;; test.spectec:136.1-136.20
syntax u8 = uN

;; test.spectec:137.1-137.21
syntax u16 = uN

;; test.spectec:138.1-138.21
syntax u31 = uN

;; test.spectec:139.1-139.21
syntax u32 = uN

;; test.spectec:140.1-140.21
syntax u64 = uN

;; test.spectec:141.1-141.21
syntax s33 = sN

;; test.spectec:142.1-142.21
syntax i32 = iN

;; test.spectec:143.1-143.21
syntax i64 = iN

;; test.spectec:144.1-144.23
syntax i128 = iN

;; test.spectec:151.1-151.35
def $signif(v_N : N) : nat?
  ;; test.spectec:152.1-152.21
  def $signif(32) = ?(23)
  ;; test.spectec:153.1-153.21
  def $signif(64) = ?(52)
  def $signif{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:155.1-155.34
def $expon(v_N : N) : nat?
  ;; test.spectec:156.1-156.19
  def $expon(32) = ?(8)
  ;; test.spectec:157.1-157.20
  def $expon(64) = ?(11)
  def $expon{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:159.1-159.47
def $fun_M(v_N : N) : nat
  ;; test.spectec:160.1-160.23
  def $fun_M{v_N : nat}(v_N) = !($signif(v_N))

;; test.spectec:162.1-162.47
def $E(v_N : N) : nat
  ;; test.spectec:163.1-163.22
  def $E{v_N : nat}(v_N) = !($expon(v_N))

;; test.spectec:169.1-169.47
syntax exp = int

;; test.spectec:170.1-174.84
syntax fNmag = 
  | NORM(v_m : m, v_exp : exp)
  | SUBNORM(v_m : m)
  | INF
  | NAN(v_m : m)

;; test.spectec:170.8-170.14
relation wf_fNmag: `%%`(N, fNmag)
  ;; test.spectec:170.8-170.14
  rule fNmag_case_0{v_N : N, v_m : m, v_exp : exp}:
    `%%`(v_N, NORM_fNmag(v_m, v_exp))
    -- if ((v_m < (2 ^ $fun_M(v_N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= v_exp) /\ (v_exp <= (((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

  ;; test.spectec:170.8-170.14
  rule fNmag_case_1{v_N : N, v_exp : exp, v_m : m}:
    `%%`(v_N, SUBNORM_fNmag(v_m))
    -- if ((v_m < (2 ^ $fun_M(v_N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = v_exp))

  ;; test.spectec:170.8-170.14
  rule fNmag_case_2{v_N : N}:
    `%%`(v_N, INF_fNmag)

  ;; test.spectec:170.8-170.14
  rule fNmag_case_3{v_N : N, v_m : m}:
    `%%`(v_N, NAN_fNmag(v_m))
    -- if ((1 <= v_m) /\ (v_m < (2 ^ $fun_M(v_N))))

;; test.spectec:165.1-167.35
syntax fN = 
  | POS(fNmag)
  | NEG(fNmag)

;; test.spectec:165.8-165.11
relation wf_fN: `%%`(N, fN)
  ;; test.spectec:165.8-165.11
  rule fN_case_0{v_N : N, var_0 : fNmag}:
    `%%`(v_N, POS_fN(var_0))
    -- wf_fNmag: `%%`(v_N, var_0)

  ;; test.spectec:165.8-165.11
  rule fN_case_1{v_N : N, var_0 : fNmag}:
    `%%`(v_N, NEG_fN(var_0))
    -- wf_fNmag: `%%`(v_N, var_0)

;; test.spectec:176.1-176.21
syntax f32 = fN

;; test.spectec:177.1-177.21
syntax f64 = fN

;; test.spectec:179.1-179.39
def $fzero(v_N : N) : fN
  ;; test.spectec:180.1-180.32
  def $fzero{v_N : nat}(v_N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:179.6-179.12
relation fzero_is_wf: `%%`(v_N : N, ret_val : fN)
  ;; test.spectec:179.6-179.12
  rule fzero_is_wf_0{v_N : N, ret_val : fN}:
    `%%`(v_N, ret_val)
    -- if (ret_val = $fzero(v_N))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:182.1-182.45
def $fnat(v_N : N, nat : nat) : fN
  ;; test.spectec:183.1-183.33
  def $fnat{v_N : nat, v_n : nat}(v_N, v_n) = POS_fN(NORM_fNmag(v_n, (0 : nat <:> int)))

;; test.spectec:182.6-182.11
relation fnat_is_wf: `%%%`(v_N : N, nat : nat, ret_val : fN)
  ;; test.spectec:182.6-182.11
  rule fnat_is_wf_0{v_N : N, nat : nat, ret_val : fN}:
    `%%%`(v_N, nat, ret_val)
    -- if (ret_val = $fnat(v_N, nat))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:185.1-185.39
def $fone(v_N : N) : fN
  ;; test.spectec:186.1-186.30
  def $fone{v_N : nat}(v_N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:185.6-185.11
relation fone_is_wf: `%%`(v_N : N, ret_val : fN)
  ;; test.spectec:185.6-185.11
  rule fone_is_wf_0{v_N : N, ret_val : fN}:
    `%%`(v_N, ret_val)
    -- if (ret_val = $fone(v_N))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:188.1-188.21
def $canon_(v_N : N) : nat
  ;; test.spectec:189.1-189.37
  def $canon_{v_N : nat}(v_N) = (2 ^ (((!($signif(v_N)) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:194.1-195.8
syntax vN = uN

;; test.spectec:197.1-197.23
syntax v128 = vN

;; test.spectec:203.1-203.49
syntax list{syntax X}(syntax X) = 
  | mk_list(X_lst : X*)
    -- if (|X_lst| < (2 ^ 32))

;; test.spectec:203.1-203.49
def $proj_list_0(syntax X, x : list(syntax X)) : (X*)
  ;; test.spectec:203.1-203.49
  def $proj_list_0{syntax X, v_X_list_0 : X*}(syntax X, mk_list_list(v_X_list_0)) = (v_X_list_0)

;; test.spectec:208.1-208.85
syntax char = 
  | mk_char(i : nat)

;; test.spectec:208.8-208.12
relation wf_char: `%`(char)
  ;; test.spectec:208.8-208.12
  rule char_case_0{i : nat}:
    `%`(mk_char_char(i))
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:210.1-210.25
def $utf8(var_0_lst : char*) : byte*

;; test.spectec:210.6-210.11
relation utf8_is_wf: `%%`(var_0_lst : char*, ret_val_lst : byte*)
  ;; test.spectec:210.6-210.11
  rule utf8_is_wf_0{var_0_lst : char*, ret_val_lst : byte*}:
    `%%`(var_0_lst, ret_val_lst)
    -- (wf_char: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = $utf8(var_0_lst))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:212.1-212.70
syntax name = 
  | mk_name(char_lst : char*)

;; test.spectec:212.8-212.12
relation wf_name: `%`(name)
  ;; test.spectec:212.8-212.12
  rule name_case_0{char_lst : char*}:
    `%`(mk_name_name(char_lst))
    -- (wf_char: `%`(v_char))*{v_char <- char_lst}
    -- if (|$utf8(char_lst)| < (2 ^ 32))

;; test.spectec:219.1-219.36
syntax idx = u32

;; test.spectec:220.1-220.44
syntax laneidx = u8

;; test.spectec:222.1-222.45
syntax typeidx = idx

;; test.spectec:223.1-223.49
syntax funcidx = idx

;; test.spectec:224.1-224.49
syntax globalidx = idx

;; test.spectec:225.1-225.47
syntax tableidx = idx

;; test.spectec:226.1-226.46
syntax memidx = idx

;; test.spectec:227.1-227.43
syntax tagidx = idx

;; test.spectec:228.1-228.45
syntax elemidx = idx

;; test.spectec:229.1-229.45
syntax dataidx = idx

;; test.spectec:230.1-230.47
syntax labelidx = idx

;; test.spectec:231.1-231.47
syntax localidx = idx

;; test.spectec:232.1-232.47
syntax fieldidx = idx

;; test.spectec:234.1-235.79
syntax externidx = 
  | FUNC(v_funcidx : funcidx)
  | GLOBAL(v_globalidx : globalidx)
  | TABLE(v_tableidx : tableidx)
  | MEM(v_memidx : memidx)
  | TAG(v_tagidx : tagidx)

;; test.spectec:234.8-234.17
relation wf_externidx: `%`(externidx)
  ;; test.spectec:234.8-234.17
  rule externidx_case_0{v_funcidx : funcidx}:
    `%`(FUNC_externidx(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_1{v_globalidx : globalidx}:
    `%`(GLOBAL_externidx(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_2{v_tableidx : tableidx}:
    `%`(TABLE_externidx(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_3{v_memidx : memidx}:
    `%`(MEM_externidx(v_memidx))
    -- wf_uN: `%%`(32, v_memidx)

  ;; test.spectec:234.8-234.17
  rule externidx_case_4{v_tagidx : tagidx}:
    `%`(TAG_externidx(v_tagidx))
    -- wf_uN: `%%`(32, v_tagidx)

;; test.spectec:248.1-248.86
rec {

;; test.spectec:248.6-248.14
relation fun_funcsxx: `%%`(externidx*, typeidx*)
  ;; test.spectec:248.6-248.14
  rule fun_funcsxx_case_0:
    `%%`([], [])

  ;; test.spectec:248.6-248.14
  rule fun_funcsxx_case_1{x : uN, xx_lst : externidx*, var_0 : typeidx*}:
    `%%`([FUNC_externidx(x)] ++ xx_lst, [x] ++ var_0)
    -- fun_funcsxx: `%%`(xx_lst, var_0)

  ;; test.spectec:248.6-248.14
  rule fun_funcsxx_case_2{v_externidx : externidx, xx_lst : externidx*, var_0 : typeidx*}:
    `%%`([v_externidx] ++ xx_lst, var_0)
    -- fun_funcsxx: `%%`(xx_lst, var_0)
}

;; test.spectec:248.1-248.86
rec {

;; test.spectec:248.6-248.14
relation funcsxx_is_wf: `%%`(var_0_lst : externidx*, ret_val_lst : typeidx*)
  ;; test.spectec:248.6-248.14
  rule funcsxx_is_wf_0{var_0_lst : externidx*, ret_val_lst : typeidx*, var_0 : typeidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_funcsxx: `%%`(var_0_lst, var_0)
    -- (wf_externidx: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:249.1-249.88
rec {

;; test.spectec:249.6-249.16
relation fun_globalsxx: `%%`(externidx*, globalidx*)
  ;; test.spectec:249.6-249.16
  rule fun_globalsxx_case_0:
    `%%`([], [])

  ;; test.spectec:249.6-249.16
  rule fun_globalsxx_case_1{x : uN, xx_lst : externidx*, var_0 : globalidx*}:
    `%%`([GLOBAL_externidx(x)] ++ xx_lst, [x] ++ var_0)
    -- fun_globalsxx: `%%`(xx_lst, var_0)

  ;; test.spectec:249.6-249.16
  rule fun_globalsxx_case_2{v_externidx : externidx, xx_lst : externidx*, var_0 : globalidx*}:
    `%%`([v_externidx] ++ xx_lst, var_0)
    -- fun_globalsxx: `%%`(xx_lst, var_0)
}

;; test.spectec:249.1-249.88
rec {

;; test.spectec:249.6-249.16
relation globalsxx_is_wf: `%%`(var_0_lst : externidx*, ret_val_lst : globalidx*)
  ;; test.spectec:249.6-249.16
  rule globalsxx_is_wf_0{var_0_lst : externidx*, ret_val_lst : globalidx*, var_0 : globalidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_globalsxx: `%%`(var_0_lst, var_0)
    -- (wf_externidx: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:250.1-250.87
rec {

;; test.spectec:250.6-250.15
relation fun_tablesxx: `%%`(externidx*, tableidx*)
  ;; test.spectec:250.6-250.15
  rule fun_tablesxx_case_0:
    `%%`([], [])

  ;; test.spectec:250.6-250.15
  rule fun_tablesxx_case_1{x : uN, xx_lst : externidx*, var_0 : tableidx*}:
    `%%`([TABLE_externidx(x)] ++ xx_lst, [x] ++ var_0)
    -- fun_tablesxx: `%%`(xx_lst, var_0)

  ;; test.spectec:250.6-250.15
  rule fun_tablesxx_case_2{v_externidx : externidx, xx_lst : externidx*, var_0 : tableidx*}:
    `%%`([v_externidx] ++ xx_lst, var_0)
    -- fun_tablesxx: `%%`(xx_lst, var_0)
}

;; test.spectec:250.1-250.87
rec {

;; test.spectec:250.6-250.15
relation tablesxx_is_wf: `%%`(var_0_lst : externidx*, ret_val_lst : tableidx*)
  ;; test.spectec:250.6-250.15
  rule tablesxx_is_wf_0{var_0_lst : externidx*, ret_val_lst : tableidx*, var_0 : tableidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_tablesxx: `%%`(var_0_lst, var_0)
    -- (wf_externidx: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:251.1-251.85
rec {

;; test.spectec:251.6-251.13
relation fun_memsxx: `%%`(externidx*, memidx*)
  ;; test.spectec:251.6-251.13
  rule fun_memsxx_case_0:
    `%%`([], [])

  ;; test.spectec:251.6-251.13
  rule fun_memsxx_case_1{x : uN, xx_lst : externidx*, var_0 : memidx*}:
    `%%`([MEM_externidx(x)] ++ xx_lst, [x] ++ var_0)
    -- fun_memsxx: `%%`(xx_lst, var_0)

  ;; test.spectec:251.6-251.13
  rule fun_memsxx_case_2{v_externidx : externidx, xx_lst : externidx*, var_0 : memidx*}:
    `%%`([v_externidx] ++ xx_lst, var_0)
    -- fun_memsxx: `%%`(xx_lst, var_0)
}

;; test.spectec:251.1-251.85
rec {

;; test.spectec:251.6-251.13
relation memsxx_is_wf: `%%`(var_0_lst : externidx*, ret_val_lst : memidx*)
  ;; test.spectec:251.6-251.13
  rule memsxx_is_wf_0{var_0_lst : externidx*, ret_val_lst : memidx*, var_0 : memidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_memsxx: `%%`(var_0_lst, var_0)
    -- (wf_externidx: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:252.1-252.85
rec {

;; test.spectec:252.6-252.13
relation fun_tagsxx: `%%`(externidx*, tagidx*)
  ;; test.spectec:252.6-252.13
  rule fun_tagsxx_case_0:
    `%%`([], [])

  ;; test.spectec:252.6-252.13
  rule fun_tagsxx_case_1{x : uN, xx_lst : externidx*, var_0 : tagidx*}:
    `%%`([TAG_externidx(x)] ++ xx_lst, [x] ++ var_0)
    -- fun_tagsxx: `%%`(xx_lst, var_0)

  ;; test.spectec:252.6-252.13
  rule fun_tagsxx_case_2{v_externidx : externidx, xx_lst : externidx*, var_0 : tagidx*}:
    `%%`([v_externidx] ++ xx_lst, var_0)
    -- fun_tagsxx: `%%`(xx_lst, var_0)
}

;; test.spectec:252.1-252.85
rec {

;; test.spectec:252.6-252.13
relation tagsxx_is_wf: `%%`(var_0_lst : externidx*, ret_val_lst : tagidx*)
  ;; test.spectec:252.6-252.13
  rule tagsxx_is_wf_0{var_0_lst : externidx*, ret_val_lst : tagidx*, var_0 : tagidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_tagsxx: `%%`(var_0_lst, var_0)
    -- (wf_externidx: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:277.1-288.4
syntax free = 
{
  TYPES typeidx*,
  FUNCS funcidx*,
  GLOBALS globalidx*,
  TABLES tableidx*,
  MEMS memidx*,
  ELEMS elemidx*,
  DATAS dataidx*,
  LOCALS localidx*,
  LABELS labelidx*,
  TAGS tagidx*
}

;; test.spectec:277.8-277.12
relation wf_free: `%`(free)
  ;; test.spectec:277.8-277.12
  rule free_case_{var_0_lst : typeidx*, var_1_lst : funcidx*, var_2_lst : globalidx*, var_3_lst : tableidx*, var_4_lst : memidx*, var_5_lst : elemidx*, var_6_lst : dataidx*, var_7_lst : localidx*, var_8_lst : labelidx*, var_9_lst : tagidx*}:
    `%`({TYPES var_0_lst, FUNCS var_1_lst, GLOBALS var_2_lst, TABLES var_3_lst, MEMS var_4_lst, ELEMS var_5_lst, DATAS var_6_lst, LOCALS var_7_lst, LABELS var_8_lst, TAGS var_9_lst})
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- var_0_lst}
    -- (wf_uN: `%%`(32, var_1))*{var_1 <- var_1_lst}
    -- (wf_uN: `%%`(32, var_2))*{var_2 <- var_2_lst}
    -- (wf_uN: `%%`(32, var_3))*{var_3 <- var_3_lst}
    -- (wf_uN: `%%`(32, var_4))*{var_4 <- var_4_lst}
    -- (wf_uN: `%%`(32, var_5))*{var_5 <- var_5_lst}
    -- (wf_uN: `%%`(32, var_6))*{var_6 <- var_6_lst}
    -- (wf_uN: `%%`(32, var_7))*{var_7 <- var_7_lst}
    -- (wf_uN: `%%`(32, var_8))*{var_8 <- var_8_lst}
    -- (wf_uN: `%%`(32, var_9))*{var_9 <- var_9_lst}

;; test.spectec:291.1-291.28
def $free_opt(var_0_opt : free?) : free
  ;; test.spectec:294.1-294.24
  def $free_opt(?()) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:295.1-295.27
  def $free_opt{v_free : free}(?(v_free)) = v_free

;; test.spectec:291.6-291.15
relation free_opt_is_wf: `%%`(var_0_opt : free?, ret_val : free)
  ;; test.spectec:291.6-291.15
  rule free_opt_is_wf_0{var_0_opt : free?, ret_val : free}:
    `%%`(var_0_opt, ret_val)
    -- (wf_free: `%`(var_0))?{var_0 <- var_0_opt}
    -- if (ret_val = $free_opt(var_0_opt))
    -- wf_free: `%`(ret_val)

;; test.spectec:292.1-292.29
rec {

;; test.spectec:292.6-292.16
relation fun_free_list: `%%`(free*, free)
  ;; test.spectec:292.6-292.16
  rule fun_free_list_case_0:
    `%%`([], {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:292.6-292.16
  rule fun_free_list_case_1{v_free : free, free'_lst : free*, var_0 : free}:
    `%%`([v_free] ++ free'_lst, v_free +++ var_0)
    -- fun_free_list: `%%`(free'_lst, var_0)
}

;; test.spectec:292.1-292.29
rec {

;; test.spectec:292.6-292.16
relation free_list_is_wf: `%%`(var_0_lst : free*, ret_val : free)
  ;; test.spectec:292.6-292.16
  rule free_list_is_wf_0{var_0_lst : free*, ret_val : free, var_0 : free}:
    `%%`(var_0_lst, ret_val)
    -- fun_free_list: `%%`(var_0_lst, var_0)
    -- (wf_free: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)
}

;; test.spectec:301.1-301.34
def $free_typeidx(v_typeidx : typeidx) : free
  ;; test.spectec:313.1-313.45
  def $free_typeidx{v_typeidx : uN}(v_typeidx) = {TYPES [v_typeidx], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:301.6-301.19
relation free_typeidx_is_wf: `%%`(v_typeidx : typeidx, ret_val : free)
  ;; test.spectec:301.6-301.19
  rule free_typeidx_is_wf_0{v_typeidx : typeidx, ret_val : free}:
    `%%`(v_typeidx, ret_val)
    -- wf_uN: `%%`(32, v_typeidx)
    -- if (ret_val = $free_typeidx(v_typeidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:302.1-302.34
def $free_funcidx(v_funcidx : funcidx) : free
  ;; test.spectec:314.1-314.45
  def $free_funcidx{v_funcidx : uN}(v_funcidx) = {TYPES [], FUNCS [v_funcidx], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:302.6-302.19
relation free_funcidx_is_wf: `%%`(v_funcidx : funcidx, ret_val : free)
  ;; test.spectec:302.6-302.19
  rule free_funcidx_is_wf_0{v_funcidx : funcidx, ret_val : free}:
    `%%`(v_funcidx, ret_val)
    -- wf_uN: `%%`(32, v_funcidx)
    -- if (ret_val = $free_funcidx(v_funcidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:303.1-303.38
def $free_globalidx(v_globalidx : globalidx) : free
  ;; test.spectec:315.1-315.53
  def $free_globalidx{v_globalidx : uN}(v_globalidx) = {TYPES [], FUNCS [], GLOBALS [v_globalidx], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:303.6-303.21
relation free_globalidx_is_wf: `%%`(v_globalidx : globalidx, ret_val : free)
  ;; test.spectec:303.6-303.21
  rule free_globalidx_is_wf_0{v_globalidx : globalidx, ret_val : free}:
    `%%`(v_globalidx, ret_val)
    -- wf_uN: `%%`(32, v_globalidx)
    -- if (ret_val = $free_globalidx(v_globalidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:304.1-304.36
def $free_tableidx(v_tableidx : tableidx) : free
  ;; test.spectec:316.1-316.49
  def $free_tableidx{v_tableidx : uN}(v_tableidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [v_tableidx], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:304.6-304.20
relation free_tableidx_is_wf: `%%`(v_tableidx : tableidx, ret_val : free)
  ;; test.spectec:304.6-304.20
  rule free_tableidx_is_wf_0{v_tableidx : tableidx, ret_val : free}:
    `%%`(v_tableidx, ret_val)
    -- wf_uN: `%%`(32, v_tableidx)
    -- if (ret_val = $free_tableidx(v_tableidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:305.1-305.32
def $free_memidx(v_memidx : memidx) : free
  ;; test.spectec:317.1-317.41
  def $free_memidx{v_memidx : uN}(v_memidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [v_memidx], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:305.6-305.18
relation free_memidx_is_wf: `%%`(v_memidx : memidx, ret_val : free)
  ;; test.spectec:305.6-305.18
  rule free_memidx_is_wf_0{v_memidx : memidx, ret_val : free}:
    `%%`(v_memidx, ret_val)
    -- wf_uN: `%%`(32, v_memidx)
    -- if (ret_val = $free_memidx(v_memidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:306.1-306.34
def $free_elemidx(v_elemidx : elemidx) : free
  ;; test.spectec:318.1-318.45
  def $free_elemidx{v_elemidx : uN}(v_elemidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [v_elemidx], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:306.6-306.19
relation free_elemidx_is_wf: `%%`(v_elemidx : elemidx, ret_val : free)
  ;; test.spectec:306.6-306.19
  rule free_elemidx_is_wf_0{v_elemidx : elemidx, ret_val : free}:
    `%%`(v_elemidx, ret_val)
    -- wf_uN: `%%`(32, v_elemidx)
    -- if (ret_val = $free_elemidx(v_elemidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:307.1-307.34
def $free_dataidx(v_dataidx : dataidx) : free
  ;; test.spectec:319.1-319.45
  def $free_dataidx{v_dataidx : uN}(v_dataidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [v_dataidx], LOCALS [], LABELS [], TAGS []}

;; test.spectec:307.6-307.19
relation free_dataidx_is_wf: `%%`(v_dataidx : dataidx, ret_val : free)
  ;; test.spectec:307.6-307.19
  rule free_dataidx_is_wf_0{v_dataidx : dataidx, ret_val : free}:
    `%%`(v_dataidx, ret_val)
    -- wf_uN: `%%`(32, v_dataidx)
    -- if (ret_val = $free_dataidx(v_dataidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:308.1-308.36
def $free_localidx(v_localidx : localidx) : free
  ;; test.spectec:320.1-320.49
  def $free_localidx{v_localidx : uN}(v_localidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [v_localidx], LABELS [], TAGS []}

;; test.spectec:308.6-308.20
relation free_localidx_is_wf: `%%`(v_localidx : localidx, ret_val : free)
  ;; test.spectec:308.6-308.20
  rule free_localidx_is_wf_0{v_localidx : localidx, ret_val : free}:
    `%%`(v_localidx, ret_val)
    -- wf_uN: `%%`(32, v_localidx)
    -- if (ret_val = $free_localidx(v_localidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:309.1-309.36
def $free_labelidx(v_labelidx : labelidx) : free
  ;; test.spectec:321.1-321.49
  def $free_labelidx{v_labelidx : uN}(v_labelidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [v_labelidx], TAGS []}

;; test.spectec:309.6-309.20
relation free_labelidx_is_wf: `%%`(v_labelidx : labelidx, ret_val : free)
  ;; test.spectec:309.6-309.20
  rule free_labelidx_is_wf_0{v_labelidx : labelidx, ret_val : free}:
    `%%`(v_labelidx, ret_val)
    -- wf_uN: `%%`(32, v_labelidx)
    -- if (ret_val = $free_labelidx(v_labelidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:311.1-311.32
def $free_tagidx(v_tagidx : tagidx) : free
  ;; test.spectec:322.1-322.41
  def $free_tagidx{v_tagidx : uN}(v_tagidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS [v_tagidx]}

;; test.spectec:311.6-311.18
relation free_tagidx_is_wf: `%%`(v_tagidx : tagidx, ret_val : free)
  ;; test.spectec:311.6-311.18
  rule free_tagidx_is_wf_0{v_tagidx : tagidx, ret_val : free}:
    `%%`(v_tagidx, ret_val)
    -- wf_uN: `%%`(32, v_tagidx)
    -- if (ret_val = $free_tagidx(v_tagidx))
    -- wf_free: `%`(ret_val)

;; test.spectec:310.1-310.38
def $free_externidx(v_externidx : externidx) : free
  ;; test.spectec:324.1-324.59
  def $free_externidx{v_funcidx : uN}(FUNC_externidx(v_funcidx)) = $free_funcidx(v_funcidx)
  ;; test.spectec:325.1-325.67
  def $free_externidx{v_globalidx : uN}(GLOBAL_externidx(v_globalidx)) = $free_globalidx(v_globalidx)
  ;; test.spectec:326.1-326.63
  def $free_externidx{v_tableidx : uN}(TABLE_externidx(v_tableidx)) = $free_tableidx(v_tableidx)
  ;; test.spectec:327.1-327.55
  def $free_externidx{v_memidx : uN}(MEM_externidx(v_memidx)) = $free_memidx(v_memidx)
  ;; test.spectec:328.1-328.55
  def $free_externidx{v_tagidx : uN}(TAG_externidx(v_tagidx)) = $free_tagidx(v_tagidx)

;; test.spectec:310.6-310.21
relation free_externidx_is_wf: `%%`(v_externidx : externidx, ret_val : free)
  ;; test.spectec:310.6-310.21
  rule free_externidx_is_wf_0{v_externidx : externidx, ret_val : free}:
    `%%`(v_externidx, ret_val)
    -- wf_externidx: `%`(v_externidx)
    -- if (ret_val = $free_externidx(v_externidx))
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

def $numtype_addrtype(var_0 : addrtype) : numtype
  def $numtype_addrtype(I32_addrtype) = I32_numtype
  def $numtype_addrtype(I64_addrtype) = I64_numtype

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

def $consttype_numtype(var_0 : numtype) : consttype
  def $consttype_numtype(I32_numtype) = I32_consttype
  def $consttype_numtype(I64_numtype) = I64_consttype
  def $consttype_numtype(F32_numtype) = F32_consttype
  def $consttype_numtype(F64_numtype) = F64_consttype

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
  | _IDX(v_typeidx : typeidx)
  | _DEF(v_rectype : rectype, v_n : n)
  | REC(v_n : n)

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
  | _IDX(v_typeidx : typeidx)
  | _DEF(v_rectype : rectype, v_n : n)
  | REC(v_n : n)

;; test.spectec:387.1-388.14
syntax valtype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(null_opt : null?, v_heaptype : heaptype)
  | BOT

;; test.spectec:428.1-428.66
syntax storagetype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(null_opt : null?, v_heaptype : heaptype)
  | BOT
  | I8
  | I16

;; test.spectec:448.1-448.61
syntax fieldtype = 
  | mk_fieldtype(mut_opt : mut?, v_storagetype : storagetype)

;; test.spectec:450.1-453.34
syntax comptype = 
  | STRUCT(list(syntax fieldtype))
  | ARRAY(v_fieldtype : fieldtype)
  | `FUNC%->%`(v_resulttype : list(syntax valtype), v_resulttype : list(syntax valtype))

;; test.spectec:455.1-456.33
syntax subtype = 
  | SUB(final_opt : final?, typeuse_lst : typeuse*, v_comptype : comptype)

;; test.spectec:458.1-459.22
syntax rectype = 
  | REC(list(syntax subtype))
}

;; test.spectec:438.1-439.16
syntax resulttype = list(syntax valtype)

def $heaptype_absheaptype(var_0 : absheaptype) : heaptype
  def $heaptype_absheaptype(ANY_absheaptype) = ANY_heaptype
  def $heaptype_absheaptype(EQ_absheaptype) = EQ_heaptype
  def $heaptype_absheaptype(I31_absheaptype) = I31_heaptype
  def $heaptype_absheaptype(STRUCT_absheaptype) = STRUCT_heaptype
  def $heaptype_absheaptype(ARRAY_absheaptype) = ARRAY_heaptype
  def $heaptype_absheaptype(NONE_absheaptype) = NONE_heaptype
  def $heaptype_absheaptype(FUNC_absheaptype) = FUNC_heaptype
  def $heaptype_absheaptype(NOFUNC_absheaptype) = NOFUNC_heaptype
  def $heaptype_absheaptype(EXN_absheaptype) = EXN_heaptype
  def $heaptype_absheaptype(NOEXN_absheaptype) = NOEXN_heaptype
  def $heaptype_absheaptype(EXTERN_absheaptype) = EXTERN_heaptype
  def $heaptype_absheaptype(NOEXTERN_absheaptype) = NOEXTERN_heaptype
  def $heaptype_absheaptype(BOT_absheaptype) = BOT_heaptype

def $valtype_addrtype(var_0 : addrtype) : valtype
  def $valtype_addrtype(I32_addrtype) = I32_valtype
  def $valtype_addrtype(I64_addrtype) = I64_valtype

def $storagetype_consttype(var_0 : consttype) : storagetype
  def $storagetype_consttype(I32_consttype) = I32_storagetype
  def $storagetype_consttype(I64_consttype) = I64_storagetype
  def $storagetype_consttype(F32_consttype) = F32_storagetype
  def $storagetype_consttype(F64_consttype) = F64_storagetype
  def $storagetype_consttype(V128_consttype) = V128_storagetype

def $storagetype_numtype(var_0 : numtype) : storagetype
  def $storagetype_numtype(I32_numtype) = I32_storagetype
  def $storagetype_numtype(I64_numtype) = I64_storagetype
  def $storagetype_numtype(F32_numtype) = F32_storagetype
  def $storagetype_numtype(F64_numtype) = F64_storagetype

def $valtype_numtype(var_0 : numtype) : valtype
  def $valtype_numtype(I32_numtype) = I32_valtype
  def $valtype_numtype(I64_numtype) = I64_valtype
  def $valtype_numtype(F32_numtype) = F32_valtype
  def $valtype_numtype(F64_numtype) = F64_valtype

def $heaptype_typeuse(var_0 : typeuse) : heaptype
  def $heaptype_typeuse{x0 : typeidx}(_IDX_typeuse(x0)) = _IDX_heaptype(x0)
  def $heaptype_typeuse{x0 : rectype, x1 : n}(_DEF_typeuse(x0, x1)) = _DEF_heaptype(x0, x1)
  def $heaptype_typeuse{x0 : n}(REC_typeuse(x0)) = REC_heaptype(x0)

def $storagetype_valtype(var_0 : valtype) : storagetype
  def $storagetype_valtype(I32_valtype) = I32_storagetype
  def $storagetype_valtype(I64_valtype) = I64_storagetype
  def $storagetype_valtype(F32_valtype) = F32_storagetype
  def $storagetype_valtype(F64_valtype) = F64_storagetype
  def $storagetype_valtype(V128_valtype) = V128_storagetype
  def $storagetype_valtype{x0 : null?, x1 : heaptype}(REF_valtype(x0, x1)) = REF_storagetype(x0, x1)
  def $storagetype_valtype(BOT_valtype) = BOT_storagetype

def $storagetype_vectype(var_0 : vectype) : storagetype
  def $storagetype_vectype(V128_vectype) = V128_storagetype

def $valtype_vectype(var_0 : vectype) : valtype
  def $valtype_vectype(V128_vectype) = V128_valtype

;; test.spectec:373.1-459.22
rec {

;; test.spectec:373.8-373.15
relation wf_typeuse: `%`(typeuse)
  ;; test.spectec:373.8-373.15
  rule typeuse_case_0{v_typeidx : typeidx}:
    `%`(_IDX_typeuse(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:373.8-373.15
  rule typeuse_case_1{v_rectype : rectype, v_n : n}:
    `%`(_DEF_typeuse(v_rectype, v_n))

  ;; test.spectec:373.8-373.15
  rule typeuse_case_2{v_n : n}:
    `%`(REC_typeuse(v_n))

;; test.spectec:379.8-379.16
relation wf_heaptype: `%`(heaptype)
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
  rule heaptype_case_13{v_typeidx : typeidx}:
    `%`(_IDX_heaptype(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:379.8-379.16
  rule heaptype_case_14{v_rectype : rectype, v_n : n}:
    `%`(_DEF_heaptype(v_rectype, v_n))

  ;; test.spectec:379.8-379.16
  rule heaptype_case_15{v_n : n}:
    `%`(REC_heaptype(v_n))

;; test.spectec:387.8-387.15
relation wf_valtype: `%`(valtype)
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
  rule valtype_case_5{null_opt : null?, v_heaptype : heaptype}:
    `%`(REF_valtype(null_opt, v_heaptype))
    -- wf_heaptype: `%`(v_heaptype)

  ;; test.spectec:387.8-387.15
  rule valtype_case_6:
    `%`(BOT_valtype)

;; test.spectec:428.8-428.19
relation wf_storagetype: `%`(storagetype)
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
  rule storagetype_case_5{null_opt : null?, v_heaptype : heaptype}:
    `%`(REF_storagetype(null_opt, v_heaptype))
    -- wf_heaptype: `%`(v_heaptype)

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
relation wf_fieldtype: `%`(fieldtype)
  ;; test.spectec:448.8-448.17
  rule fieldtype_case_0{mut_opt : mut?, v_storagetype : storagetype}:
    `%`(mk_fieldtype_fieldtype(mut_opt, v_storagetype))
    -- wf_storagetype: `%`(v_storagetype)

;; test.spectec:450.8-450.16
relation wf_comptype: `%`(comptype)
  ;; test.spectec:450.8-450.16
  rule comptype_case_0{var_0 : list(syntax fieldtype)}:
    `%`(STRUCT_comptype(var_0))

  ;; test.spectec:450.8-450.16
  rule comptype_case_1{v_fieldtype : fieldtype}:
    `%`(ARRAY_comptype(v_fieldtype))
    -- wf_fieldtype: `%`(v_fieldtype)

  ;; test.spectec:450.8-450.16
  rule comptype_case_2{v_resulttype : resulttype, resulttype_0 : resulttype}:
    `%`(`FUNC%->%`_comptype(v_resulttype, resulttype_0))

;; test.spectec:455.8-455.15
relation wf_subtype: `%`(subtype)
  ;; test.spectec:455.8-455.15
  rule subtype_case_0{final_opt : final?, typeuse_lst : typeuse*, v_comptype : comptype}:
    `%`(SUB_subtype(final_opt, typeuse_lst, v_comptype))
    -- (wf_typeuse: `%`(v_typeuse))*{v_typeuse <- typeuse_lst}
    -- wf_comptype: `%`(v_comptype)
}

;; test.spectec:368.1-369.34
syntax deftype = 
  | _DEF(v_rectype : rectype, v_n : n)

def $heaptype_deftype(var_0 : deftype) : heaptype
  def $heaptype_deftype{x0 : rectype, x1 : n}(_DEF_deftype(x0, x1)) = _DEF_heaptype(x0, x1)

def $typeuse_deftype(var_0 : deftype) : typeuse
  def $typeuse_deftype{x0 : rectype, x1 : n}(_DEF_deftype(x0, x1)) = _DEF_typeuse(x0, x1)

;; test.spectec:376.1-377.42
syntax typevar = 
  | _IDX(v_typeidx : typeidx)
  | REC(v_n : n)

def $typeuse_typevar(var_0 : typevar) : typeuse
  def $typeuse_typevar{x0 : typeidx}(_IDX_typevar(x0)) = _IDX_typeuse(x0)
  def $typeuse_typevar{x0 : n}(REC_typevar(x0)) = REC_typeuse(x0)

;; test.spectec:376.8-376.15
relation wf_typevar: `%`(typevar)
  ;; test.spectec:376.8-376.15
  rule typevar_case_0{v_typeidx : typeidx}:
    `%`(_IDX_typevar(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:376.8-376.15
  rule typevar_case_1{v_n : n}:
    `%`(REC_typevar(v_n))

;; test.spectec:382.1-383.23
syntax reftype = 
  | REF(null_opt : null?, v_heaptype : heaptype)

def $storagetype_reftype(var_0 : reftype) : storagetype
  def $storagetype_reftype{x0 : null?, x1 : heaptype}(REF_reftype(x0, x1)) = REF_storagetype(x0, x1)

def $valtype_reftype(var_0 : reftype) : valtype
  def $valtype_reftype{x0 : null?, x1 : heaptype}(REF_reftype(x0, x1)) = REF_valtype(x0, x1)

;; test.spectec:382.8-382.15
relation wf_reftype: `%`(reftype)
  ;; test.spectec:382.8-382.15
  rule reftype_case_0{null_opt : null?, v_heaptype : heaptype}:
    `%`(REF_reftype(null_opt, v_heaptype))
    -- wf_heaptype: `%`(v_heaptype)

;; test.spectec:391.1-391.55
syntax Inn = addrtype

;; test.spectec:392.1-392.56
syntax Fnn = 
  | F32
  | F64

def $numtype_Fnn(var_0 : Fnn) : numtype
  def $numtype_Fnn(F32_Fnn) = F32_numtype
  def $numtype_Fnn(F64_Fnn) = F64_numtype

;; test.spectec:393.1-393.54
syntax Vnn = vectype

;; test.spectec:394.1-394.42
syntax Cnn = 
  | I32
  | I64
  | F32
  | F64
  | V128

def $storagetype_Cnn(var_0 : Cnn) : storagetype
  def $storagetype_Cnn(I32_Cnn) = I32_storagetype
  def $storagetype_Cnn(I64_Cnn) = I64_storagetype
  def $storagetype_Cnn(F32_Cnn) = F32_storagetype
  def $storagetype_Cnn(F64_Cnn) = F64_storagetype
  def $storagetype_Cnn(V128_Cnn) = V128_storagetype

;; test.spectec:397.1-397.43
def $ANYREF : reftype
  ;; test.spectec:410.1-410.32
  def $ANYREF = REF_reftype(?(NULL_null), ANY_heaptype)

;; test.spectec:397.6-397.12
relation ANYREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:397.6-397.12
  rule ANYREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $ANYREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:398.1-398.42
def $EQREF : reftype
  ;; test.spectec:411.1-411.31
  def $EQREF = REF_reftype(?(NULL_null), EQ_heaptype)

;; test.spectec:398.6-398.11
relation EQREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:398.6-398.11
  rule EQREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $EQREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:399.1-399.43
def $I31REF : reftype
  ;; test.spectec:412.1-412.32
  def $I31REF = REF_reftype(?(NULL_null), I31_heaptype)

;; test.spectec:399.6-399.12
relation I31REF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:399.6-399.12
  rule I31REF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $I31REF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:400.1-400.46
def $STRUCTREF : reftype
  ;; test.spectec:413.1-413.35
  def $STRUCTREF = REF_reftype(?(NULL_null), STRUCT_heaptype)

;; test.spectec:400.6-400.15
relation STRUCTREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:400.6-400.15
  rule STRUCTREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $STRUCTREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:401.1-401.45
def $ARRAYREF : reftype
  ;; test.spectec:414.1-414.34
  def $ARRAYREF = REF_reftype(?(NULL_null), ARRAY_heaptype)

;; test.spectec:401.6-401.14
relation ARRAYREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:401.6-401.14
  rule ARRAYREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $ARRAYREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:402.1-402.44
def $FUNCREF : reftype
  ;; test.spectec:415.1-415.33
  def $FUNCREF = REF_reftype(?(NULL_null), FUNC_heaptype)

;; test.spectec:402.6-402.13
relation FUNCREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:402.6-402.13
  rule FUNCREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $FUNCREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:403.1-403.43
def $EXNREF : reftype
  ;; test.spectec:416.1-416.32
  def $EXNREF = REF_reftype(?(NULL_null), EXN_heaptype)

;; test.spectec:403.6-403.12
relation EXNREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:403.6-403.12
  rule EXNREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $EXNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:404.1-404.46
def $EXTERNREF : reftype
  ;; test.spectec:417.1-417.35
  def $EXTERNREF = REF_reftype(?(NULL_null), EXTERN_heaptype)

;; test.spectec:404.6-404.15
relation EXTERNREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:404.6-404.15
  rule EXTERNREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $EXTERNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:405.1-405.44
def $NULLREF : reftype
  ;; test.spectec:418.1-418.33
  def $NULLREF = REF_reftype(?(NULL_null), NONE_heaptype)

;; test.spectec:405.6-405.13
relation NULLREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:405.6-405.13
  rule NULLREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:406.1-406.50
def $NULLFUNCREF : reftype
  ;; test.spectec:419.1-419.37
  def $NULLFUNCREF = REF_reftype(?(NULL_null), NOFUNC_heaptype)

;; test.spectec:406.6-406.17
relation NULLFUNCREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:406.6-406.17
  rule NULLFUNCREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLFUNCREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:407.1-407.49
def $NULLEXNREF : reftype
  ;; test.spectec:420.1-420.36
  def $NULLEXNREF = REF_reftype(?(NULL_null), NOEXN_heaptype)

;; test.spectec:407.6-407.16
relation NULLEXNREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:407.6-407.16
  rule NULLEXNREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLEXNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:408.1-408.54
def $NULLEXTERNREF : reftype
  ;; test.spectec:421.1-421.41
  def $NULLEXTERNREF = REF_reftype(?(NULL_null), NOEXTERN_heaptype)

;; test.spectec:408.6-408.19
relation NULLEXTERNREF_is_wf: `%`(ret_val : reftype)
  ;; test.spectec:408.6-408.19
  rule NULLEXTERNREF_is_wf_0{ret_val : reftype}:
    `%`(ret_val)
    -- if (ret_val = $NULLEXTERNREF)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:426.1-426.52
syntax packtype = 
  | I8
  | I16

def $storagetype_packtype(var_0 : packtype) : storagetype
  def $storagetype_packtype(I8_packtype) = I8_storagetype
  def $storagetype_packtype(I16_packtype) = I16_storagetype

;; test.spectec:427.1-427.60
syntax lanetype = 
  | I32
  | I64
  | F32
  | F64
  | I8
  | I16

def $lanetype_Fnn(var_0 : Fnn) : lanetype
  def $lanetype_Fnn(F32_Fnn) = F32_lanetype
  def $lanetype_Fnn(F64_Fnn) = F64_lanetype

def $lanetype_addrtype(var_0 : addrtype) : lanetype
  def $lanetype_addrtype(I32_addrtype) = I32_lanetype
  def $lanetype_addrtype(I64_addrtype) = I64_lanetype

def $lanetype_numtype(var_0 : numtype) : lanetype
  def $lanetype_numtype(I32_numtype) = I32_lanetype
  def $lanetype_numtype(I64_numtype) = I64_lanetype
  def $lanetype_numtype(F32_numtype) = F32_lanetype
  def $lanetype_numtype(F64_numtype) = F64_lanetype

def $lanetype_packtype(var_0 : packtype) : lanetype
  def $lanetype_packtype(I8_packtype) = I8_lanetype
  def $lanetype_packtype(I16_packtype) = I16_lanetype

;; test.spectec:431.1-431.55
syntax Pnn = packtype

;; test.spectec:432.1-432.56
syntax Jnn = 
  | I32
  | I64
  | I8
  | I16

def $lanetype_Jnn(var_0 : Jnn) : lanetype
  def $lanetype_Jnn(I32_Jnn) = I32_lanetype
  def $lanetype_Jnn(I64_Jnn) = I64_lanetype
  def $lanetype_Jnn(I8_Jnn) = I8_lanetype
  def $lanetype_Jnn(I16_Jnn) = I16_lanetype

def $Jnn_addrtype(var_0 : addrtype) : Jnn
  def $Jnn_addrtype(I32_addrtype) = I32_Jnn
  def $Jnn_addrtype(I64_addrtype) = I64_Jnn

;; test.spectec:433.1-433.55
syntax Lnn = lanetype

;; test.spectec:464.1-464.74
syntax limits = 
  | mk_limits(v_u64 : u64, u64_opt : u64?)

;; test.spectec:464.8-464.14
relation wf_limits: `%`(limits)
  ;; test.spectec:464.8-464.14
  rule limits_case_0{v_u64 : u64, u64_opt : u64?}:
    `%`(mk_limits_limits(v_u64, u64_opt))
    -- wf_uN: `%%`(64, v_u64)

;; test.spectec:466.1-466.47
syntax tagtype = typeuse

;; test.spectec:467.1-467.58
syntax globaltype = 
  | mk_globaltype(mut_opt : mut?, v_valtype : valtype)

;; test.spectec:467.8-467.18
relation wf_globaltype: `%`(globaltype)
  ;; test.spectec:467.8-467.18
  rule globaltype_case_0{mut_opt : mut?, v_valtype : valtype}:
    `%`(mk_globaltype_globaltype(mut_opt, v_valtype))
    -- wf_valtype: `%`(v_valtype)

;; test.spectec:468.1-468.63
syntax memtype = 
  | `%%PAGE`(v_addrtype : addrtype, v_limits : limits)

;; test.spectec:468.8-468.15
relation wf_memtype: `%`(memtype)
  ;; test.spectec:468.8-468.15
  rule memtype_case_0{v_addrtype : addrtype, v_limits : limits}:
    `%`(`%%PAGE`_memtype(v_addrtype, v_limits))
    -- wf_limits: `%`(v_limits)

;; test.spectec:469.1-469.67
syntax tabletype = 
  | mk_tabletype(v_addrtype : addrtype, v_limits : limits, v_reftype : reftype)

;; test.spectec:469.8-469.17
relation wf_tabletype: `%`(tabletype)
  ;; test.spectec:469.8-469.17
  rule tabletype_case_0{v_addrtype : addrtype, v_limits : limits, v_reftype : reftype}:
    `%`(mk_tabletype_tabletype(v_addrtype, v_limits, v_reftype))
    -- wf_limits: `%`(v_limits)
    -- wf_reftype: `%`(v_reftype)

;; test.spectec:470.1-470.64
syntax datatype = 
  | OK

;; test.spectec:471.1-471.52
syntax elemtype = reftype

;; test.spectec:473.1-474.83
syntax externtype = 
  | TAG(v_tagtype : tagtype)
  | GLOBAL(v_globaltype : globaltype)
  | MEM(v_memtype : memtype)
  | TABLE(v_tabletype : tabletype)
  | FUNC(v_typeuse : typeuse)

;; test.spectec:473.8-473.18
relation wf_externtype: `%`(externtype)
  ;; test.spectec:473.8-473.18
  rule externtype_case_0{v_tagtype : tagtype}:
    `%`(TAG_externtype(v_tagtype))
    -- wf_typeuse: `%`(v_tagtype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_1{v_globaltype : globaltype}:
    `%`(GLOBAL_externtype(v_globaltype))
    -- wf_globaltype: `%`(v_globaltype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_2{v_memtype : memtype}:
    `%`(MEM_externtype(v_memtype))
    -- wf_memtype: `%`(v_memtype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_3{v_tabletype : tabletype}:
    `%`(TABLE_externtype(v_tabletype))
    -- wf_tabletype: `%`(v_tabletype)

  ;; test.spectec:473.8-473.18
  rule externtype_case_4{v_typeuse : typeuse}:
    `%`(FUNC_externtype(v_typeuse))
    -- wf_typeuse: `%`(v_typeuse)

;; test.spectec:476.1-477.47
syntax moduletype = 
  | mk_moduletype(externtype_lst : externtype*, externtype_lst : externtype*)

;; test.spectec:476.8-476.18
relation wf_moduletype: `%`(moduletype)
  ;; test.spectec:476.8-476.18
  rule moduletype_case_0{externtype_lst : externtype*, externtype_lst_0_lst : externtype*}:
    `%`(mk_moduletype_moduletype(externtype_lst, externtype_lst_0_lst))
    -- (wf_externtype: `%`(v_externtype))*{v_externtype <- externtype_lst}
    -- (wf_externtype: `%`(externtype_lst_0))*{externtype_lst_0 <- externtype_lst_0_lst}

;; test.spectec:515.1-515.65
def $IN(v_N : N) : Inn?
  ;; test.spectec:516.1-516.18
  def $IN(32) = ?(I32_Inn)
  ;; test.spectec:517.1-517.18
  def $IN(64) = ?(I64_Inn)
  def $IN{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:519.1-519.65
def $FN(v_N : N) : Fnn?
  ;; test.spectec:520.1-520.18
  def $FN(32) = ?(F32_Fnn)
  ;; test.spectec:521.1-521.18
  def $FN(64) = ?(F64_Fnn)
  def $FN{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:523.1-523.65
def $JN(v_N : N) : Jnn?
  ;; test.spectec:524.1-524.16
  def $JN(8) = ?(I8_Jnn)
  ;; test.spectec:525.1-525.18
  def $JN(16) = ?(I16_Jnn)
  ;; test.spectec:526.1-526.18
  def $JN(32) = ?(I32_Jnn)
  ;; test.spectec:527.1-527.18
  def $JN(64) = ?(I64_Jnn)
  def $JN{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:532.1-532.46
def $size(v_numtype : numtype) : nat
  ;; test.spectec:541.1-541.20
  def $size(I32_numtype) = 32
  ;; test.spectec:542.1-542.20
  def $size(I64_numtype) = 64
  ;; test.spectec:543.1-543.20
  def $size(F32_numtype) = 32
  ;; test.spectec:544.1-544.20
  def $size(F64_numtype) = 64

;; test.spectec:533.1-533.46
def $vsize(v_vectype : vectype) : nat
  ;; test.spectec:546.1-546.23
  def $vsize(V128_vectype) = 128

;; test.spectec:534.1-534.46
def $psize(v_packtype : packtype) : nat
  ;; test.spectec:548.1-548.19
  def $psize(I8_packtype) = 8
  ;; test.spectec:549.1-549.21
  def $psize(I16_packtype) = 16

;; test.spectec:535.1-535.46
def $lsize(v_lanetype : lanetype) : nat
  ;; test.spectec:551.1-551.37
  def $lsize(I32_lanetype) = $size(I32_numtype)
  ;; test.spectec:551.1-551.37
  def $lsize(I64_lanetype) = $size(I64_numtype)
  ;; test.spectec:551.1-551.37
  def $lsize(F32_lanetype) = $size(F32_numtype)
  ;; test.spectec:551.1-551.37
  def $lsize(F64_lanetype) = $size(F64_numtype)
  ;; test.spectec:552.1-552.40
  def $lsize(I8_lanetype) = $psize(I8_packtype)
  ;; test.spectec:552.1-552.40
  def $lsize(I16_lanetype) = $psize(I16_packtype)

;; test.spectec:536.1-536.60
def $zsize(v_storagetype : storagetype) : nat?
  ;; test.spectec:554.1-554.37
  def $zsize(I32_storagetype) = ?($size(I32_numtype))
  ;; test.spectec:554.1-554.37
  def $zsize(I64_storagetype) = ?($size(I64_numtype))
  ;; test.spectec:554.1-554.37
  def $zsize(F32_storagetype) = ?($size(F32_numtype))
  ;; test.spectec:554.1-554.37
  def $zsize(F64_storagetype) = ?($size(F64_numtype))
  ;; test.spectec:555.1-555.38
  def $zsize(V128_storagetype) = ?($vsize(V128_vectype))
  ;; test.spectec:556.1-556.40
  def $zsize(I8_storagetype) = ?($psize(I8_packtype))
  ;; test.spectec:556.1-556.40
  def $zsize(I16_storagetype) = ?($psize(I16_packtype))
  def $zsize{x0 : storagetype}(x0) = ?()
    -- otherwise

;; test.spectec:537.1-537.71
def $isize(v_Inn : Inn) : nat
  ;; test.spectec:558.1-558.29
  def $isize{v_Inn : addrtype}(v_Inn) = $size($numtype_addrtype(v_Inn))

;; test.spectec:538.1-538.71
def $jsize(v_Jnn : Jnn) : nat
  ;; test.spectec:560.1-560.30
  def $jsize{v_Jnn : Jnn}(v_Jnn) = $lsize($lanetype_Jnn(v_Jnn))

;; test.spectec:539.1-539.71
def $fsize(v_Fnn : Fnn) : nat
  ;; test.spectec:559.1-559.29
  def $fsize{v_Fnn : Fnn}(v_Fnn) = $size($numtype_Fnn(v_Fnn))

;; test.spectec:562.1-562.40
def $inv_isize(nat : nat) : Inn?
  ;; test.spectec:566.1-566.25
  def $inv_isize(32) = ?(I32_Inn)
  ;; test.spectec:567.1-567.25
  def $inv_isize(64) = ?(I64_Inn)
  def $inv_isize{x0 : nat}(x0) = ?()
    -- otherwise

;; test.spectec:563.1-563.40
def $inv_jsize(nat : nat) : Jnn?
  ;; test.spectec:570.1-570.24
  def $inv_jsize(8) = ?(I8_Jnn)
  ;; test.spectec:571.1-571.25
  def $inv_jsize(16) = ?(I16_Jnn)
  ;; test.spectec:572.1-572.34
  def $inv_jsize{v_n : nat}(v_n) = $Jnn_addrtype(iter_val_1)?{iter_val_1 <- $inv_isize(v_n)}

;; test.spectec:564.1-564.40
def $inv_fsize(nat : nat) : Fnn?
  ;; test.spectec:568.1-568.25
  def $inv_fsize(32) = ?(F32_Fnn)
  ;; test.spectec:569.1-569.25
  def $inv_fsize(64) = ?(F64_Fnn)
  def $inv_fsize{x0 : nat}(x0) = ?()
    -- otherwise

;; test.spectec:575.1-575.63
def $sizenn(v_numtype : numtype) : nat
  ;; test.spectec:578.1-578.28
  def $sizenn{nt : numtype}(nt) = $size(nt)

;; test.spectec:576.1-576.63
def $sizenn1(v_numtype : numtype) : nat
  ;; test.spectec:579.1-579.29
  def $sizenn1{nt : numtype}(nt) = $size(nt)

;; test.spectec:577.1-577.63
def $sizenn2(v_numtype : numtype) : nat
  ;; test.spectec:580.1-580.29
  def $sizenn2{nt : numtype}(nt) = $size(nt)

;; test.spectec:582.1-582.63
def $vsizenn(v_vectype : vectype) : nat
  ;; test.spectec:583.1-583.30
  def $vsizenn{vt : vectype}(vt) = $vsize(vt)

;; test.spectec:585.1-585.63
def $psizenn(v_packtype : packtype) : nat
  ;; test.spectec:586.1-586.30
  def $psizenn{pt : packtype}(pt) = $psize(pt)

;; test.spectec:588.1-588.63
def $lsizenn(v_lanetype : lanetype) : nat
  ;; test.spectec:591.1-591.30
  def $lsizenn{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:589.1-589.63
def $lsizenn1(v_lanetype : lanetype) : nat
  ;; test.spectec:592.1-592.31
  def $lsizenn1{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:590.1-590.63
def $lsizenn2(v_lanetype : lanetype) : nat
  ;; test.spectec:593.1-593.31
  def $lsizenn2{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:595.1-595.83
def $jsizenn(v_Jnn : Jnn) : nat
  ;; test.spectec:596.1-596.32
  def $jsizenn{v_Jnn : Jnn}(v_Jnn) = $lsize($lanetype_Jnn(v_Jnn))

;; test.spectec:598.1-598.42
def $inv_jsizenn(nat : nat) : Jnn?
  ;; test.spectec:599.1-599.36
  def $inv_jsizenn{v_n : nat}(v_n) = $inv_jsize(v_n)

;; test.spectec:604.1-604.56
def $lunpack(v_lanetype : lanetype) : numtype
  ;; test.spectec:605.1-605.32
  def $lunpack(I32_lanetype) = I32_numtype
  ;; test.spectec:605.1-605.32
  def $lunpack(I64_lanetype) = I64_numtype
  ;; test.spectec:605.1-605.32
  def $lunpack(F32_lanetype) = F32_numtype
  ;; test.spectec:605.1-605.32
  def $lunpack(F64_lanetype) = F64_numtype
  ;; test.spectec:606.1-606.29
  def $lunpack(I8_lanetype) = I32_numtype
  ;; test.spectec:606.1-606.29
  def $lunpack(I16_lanetype) = I32_numtype

;; test.spectec:608.1-608.35
def $unpack(v_storagetype : storagetype) : valtype
  ;; test.spectec:609.1-609.31
  def $unpack(BOT_storagetype) = BOT_valtype
  ;; test.spectec:609.1-609.31
  def $unpack{null_opt : null?, v_heaptype : heaptype}(REF_storagetype(null_opt, v_heaptype)) = REF_valtype(null_opt, v_heaptype)
  ;; test.spectec:609.1-609.31
  def $unpack(V128_storagetype) = V128_valtype
  ;; test.spectec:609.1-609.31
  def $unpack(F64_storagetype) = F64_valtype
  ;; test.spectec:609.1-609.31
  def $unpack(F32_storagetype) = F32_valtype
  ;; test.spectec:609.1-609.31
  def $unpack(I64_storagetype) = I64_valtype
  ;; test.spectec:609.1-609.31
  def $unpack(I32_storagetype) = I32_valtype
  ;; test.spectec:610.1-610.28
  def $unpack(I8_storagetype) = I32_valtype
  ;; test.spectec:610.1-610.28
  def $unpack(I16_storagetype) = I32_valtype

;; test.spectec:608.6-608.13
relation unpack_is_wf: `%%`(v_storagetype : storagetype, ret_val : valtype)
  ;; test.spectec:608.6-608.13
  rule unpack_is_wf_0{v_storagetype : storagetype, ret_val : valtype}:
    `%%`(v_storagetype, ret_val)
    -- wf_storagetype: `%`(v_storagetype)
    -- if (ret_val = $unpack(v_storagetype))
    -- wf_valtype: `%`(ret_val)

;; test.spectec:612.1-612.73
def $nunpack(v_storagetype : storagetype) : numtype?
  ;; test.spectec:613.1-613.32
  def $nunpack(I32_storagetype) = ?(I32_numtype)
  ;; test.spectec:613.1-613.32
  def $nunpack(I64_storagetype) = ?(I64_numtype)
  ;; test.spectec:613.1-613.32
  def $nunpack(F32_storagetype) = ?(F32_numtype)
  ;; test.spectec:613.1-613.32
  def $nunpack(F64_storagetype) = ?(F64_numtype)
  ;; test.spectec:614.1-614.29
  def $nunpack(I8_storagetype) = ?(I32_numtype)
  ;; test.spectec:614.1-614.29
  def $nunpack(I16_storagetype) = ?(I32_numtype)
  def $nunpack{x0 : storagetype}(x0) = ?()
    -- otherwise

;; test.spectec:616.1-616.73
def $vunpack(v_storagetype : storagetype) : vectype?
  ;; test.spectec:617.1-617.32
  def $vunpack(V128_storagetype) = ?(V128_vectype)
  def $vunpack{x0 : storagetype}(x0) = ?()
    -- otherwise

;; test.spectec:619.1-619.74
def $cunpack(v_storagetype : storagetype) : consttype?
  ;; test.spectec:620.1-620.36
  def $cunpack(I32_storagetype) = ?(I32_consttype)
  ;; test.spectec:620.1-620.36
  def $cunpack(I64_storagetype) = ?(I64_consttype)
  ;; test.spectec:620.1-620.36
  def $cunpack(F32_storagetype) = ?(F32_consttype)
  ;; test.spectec:620.1-620.36
  def $cunpack(F64_storagetype) = ?(F64_consttype)
  ;; test.spectec:620.1-620.36
  def $cunpack(V128_storagetype) = ?(V128_consttype)
  ;; test.spectec:621.1-621.29
  def $cunpack(I8_storagetype) = ?(I32_consttype)
  ;; test.spectec:621.1-621.29
  def $cunpack(I16_storagetype) = ?(I32_consttype)
  ;; test.spectec:622.1-622.44
  def $cunpack(I32_storagetype) = ?($consttype_numtype($lunpack(I32_lanetype)))
  ;; test.spectec:622.1-622.44
  def $cunpack(I64_storagetype) = ?($consttype_numtype($lunpack(I64_lanetype)))
  ;; test.spectec:622.1-622.44
  def $cunpack(F32_storagetype) = ?($consttype_numtype($lunpack(F32_lanetype)))
  ;; test.spectec:622.1-622.44
  def $cunpack(F64_storagetype) = ?($consttype_numtype($lunpack(F64_lanetype)))
  ;; test.spectec:622.1-622.44
  def $cunpack(I8_storagetype) = ?($consttype_numtype($lunpack(I8_lanetype)))
  ;; test.spectec:622.1-622.44
  def $cunpack(I16_storagetype) = ?($consttype_numtype($lunpack(I16_lanetype)))
  def $cunpack{x0 : storagetype}(x0) = ?()
    -- otherwise

;; test.spectec:627.1-627.90
def $minat(v_addrtype : addrtype, addrtype_0 : addrtype) : addrtype
  ;; test.spectec:628.1-628.64
  def $minat{at_1 : addrtype, at_2 : addrtype}(at_1, at_2) = (if ($size($numtype_addrtype(at_1)) <= $size($numtype_addrtype(at_2))) then at_1 else at_2)

;; test.spectec:631.1-631.82
def $diffrt(v_reftype : reftype, reftype_0 : reftype) : reftype
  ;; test.spectec:632.1-632.62
  def $diffrt{null_1_opt : null?, ht_1 : heaptype, ht_2 : heaptype}(REF_reftype(null_1_opt, ht_1), REF_reftype(?(NULL_null), ht_2)) = REF_reftype(?(), ht_1)
  ;; test.spectec:633.1-633.65
  def $diffrt{null_1_opt : null?, ht_1 : heaptype, ht_2 : heaptype}(REF_reftype(null_1_opt, ht_1), REF_reftype(?(), ht_2)) = REF_reftype(null_1_opt, ht_1)

;; test.spectec:631.6-631.13
relation diffrt_is_wf: `%%%`(v_reftype : reftype, reftype_0 : reftype, ret_val : reftype)
  ;; test.spectec:631.6-631.13
  rule diffrt_is_wf_0{v_reftype : reftype, reftype_0 : reftype, ret_val : reftype}:
    `%%%`(v_reftype, reftype_0, ret_val)
    -- wf_reftype: `%`(v_reftype)
    -- wf_reftype: `%`(reftype_0)
    -- if (ret_val = $diffrt(v_reftype, reftype_0))
    -- wf_reftype: `%`(ret_val)

;; test.spectec:636.1-636.63
def $as_deftype(v_typeuse : typeuse) : deftype?
  ;; test.spectec:637.1-637.25
  def $as_deftype{v_rectype : rectype, v_n : n}(_DEF_typeuse(v_rectype, v_n)) = ?(_DEF_deftype(v_rectype, v_n))
  def $as_deftype{x0 : typeuse}(x0) = ?()
    -- otherwise

;; test.spectec:644.1-644.87
rec {

;; test.spectec:644.6-644.13
relation fun_tagsxt: `%%`(externtype*, tagtype*)
  ;; test.spectec:644.6-644.13
  rule fun_tagsxt_case_0:
    `%%`([], [])

  ;; test.spectec:644.6-644.13
  rule fun_tagsxt_case_1{jt : typeuse, xt_lst : externtype*, var_0 : tagtype*}:
    `%%`([TAG_externtype(jt)] ++ xt_lst, [jt] ++ var_0)
    -- fun_tagsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:644.6-644.13
  rule fun_tagsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : tagtype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_tagsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:644.1-644.87
rec {

;; test.spectec:644.6-644.13
relation tagsxt_is_wf: `%%`(var_0_lst : externtype*, ret_val_lst : tagtype*)
  ;; test.spectec:644.6-644.13
  rule tagsxt_is_wf_0{var_0_lst : externtype*, ret_val_lst : tagtype*, var_0 : tagtype*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_tagsxt: `%%`(var_0_lst, var_0)
    -- (wf_externtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_typeuse: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:645.1-645.90
rec {

;; test.spectec:645.6-645.16
relation fun_globalsxt: `%%`(externtype*, globaltype*)
  ;; test.spectec:645.6-645.16
  rule fun_globalsxt_case_0:
    `%%`([], [])

  ;; test.spectec:645.6-645.16
  rule fun_globalsxt_case_1{gt : globaltype, xt_lst : externtype*, var_0 : globaltype*}:
    `%%`([GLOBAL_externtype(gt)] ++ xt_lst, [gt] ++ var_0)
    -- fun_globalsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:645.6-645.16
  rule fun_globalsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : globaltype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_globalsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:645.1-645.90
rec {

;; test.spectec:645.6-645.16
relation globalsxt_is_wf: `%%`(var_0_lst : externtype*, ret_val_lst : globaltype*)
  ;; test.spectec:645.6-645.16
  rule globalsxt_is_wf_0{var_0_lst : externtype*, ret_val_lst : globaltype*, var_0 : globaltype*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_globalsxt: `%%`(var_0_lst, var_0)
    -- (wf_externtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_globaltype: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:646.1-646.87
rec {

;; test.spectec:646.6-646.13
relation fun_memsxt: `%%`(externtype*, memtype*)
  ;; test.spectec:646.6-646.13
  rule fun_memsxt_case_0:
    `%%`([], [])

  ;; test.spectec:646.6-646.13
  rule fun_memsxt_case_1{mt : memtype, xt_lst : externtype*, var_0 : memtype*}:
    `%%`([MEM_externtype(mt)] ++ xt_lst, [mt] ++ var_0)
    -- fun_memsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:646.6-646.13
  rule fun_memsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : memtype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_memsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:646.1-646.87
rec {

;; test.spectec:646.6-646.13
relation memsxt_is_wf: `%%`(var_0_lst : externtype*, ret_val_lst : memtype*)
  ;; test.spectec:646.6-646.13
  rule memsxt_is_wf_0{var_0_lst : externtype*, ret_val_lst : memtype*, var_0 : memtype*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_memsxt: `%%`(var_0_lst, var_0)
    -- (wf_externtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_memtype: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:647.1-647.89
rec {

;; test.spectec:647.6-647.15
relation fun_tablesxt: `%%`(externtype*, tabletype*)
  ;; test.spectec:647.6-647.15
  rule fun_tablesxt_case_0:
    `%%`([], [])

  ;; test.spectec:647.6-647.15
  rule fun_tablesxt_case_1{tt : tabletype, xt_lst : externtype*, var_0 : tabletype*}:
    `%%`([TABLE_externtype(tt)] ++ xt_lst, [tt] ++ var_0)
    -- fun_tablesxt: `%%`(xt_lst, var_0)

  ;; test.spectec:647.6-647.15
  rule fun_tablesxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : tabletype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_tablesxt: `%%`(xt_lst, var_0)
}

;; test.spectec:647.1-647.89
rec {

;; test.spectec:647.6-647.15
relation tablesxt_is_wf: `%%`(var_0_lst : externtype*, ret_val_lst : tabletype*)
  ;; test.spectec:647.6-647.15
  rule tablesxt_is_wf_0{var_0_lst : externtype*, ret_val_lst : tabletype*, var_0 : tabletype*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_tablesxt: `%%`(var_0_lst, var_0)
    -- (wf_externtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_tabletype: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:648.1-648.88
rec {

;; test.spectec:648.6-648.14
relation fun_funcsxt: `%%`(externtype*, deftype*)
  ;; test.spectec:648.6-648.14
  rule fun_funcsxt_case_0:
    `%%`([], [])

  ;; test.spectec:648.6-648.14
  rule fun_funcsxt_case_1{v_rectype : rectype, v_n : n, xt_lst : externtype*, var_0 : deftype*}:
    `%%`([FUNC_externtype(_DEF_typeuse(v_rectype, v_n))] ++ xt_lst, [_DEF_deftype(v_rectype, v_n)] ++ var_0)
    -- fun_funcsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:648.6-648.14
  rule fun_funcsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : deftype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_funcsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:673.6-673.20
relation fun_subst_typevar_before_fun_subst_typevar_case_2: `%%%`(typevar, typevar*, typeuse*)
  ;; test.spectec:673.6-673.20
  rule fun_subst_typevar_case_1{tv : typevar, tv_1 : typevar, tv'_lst : typevar*, tu_1 : typeuse, tu'_lst : typeuse*, var_0 : typeuse?}:
    `%%%`(tv, [tv_1] ++ tv'_lst, [tu_1] ++ tu'_lst)

  ;; test.spectec:673.6-673.20
  rule fun_subst_typevar_case_0{tv : typevar}:
    `%%%`(tv, [], [])

;; test.spectec:673.1-673.126
rec {

;; test.spectec:673.6-673.20
relation fun_subst_typevar: `%%%%`(typevar, typevar*, typeuse*, typeuse?)
  ;; test.spectec:673.6-673.20
  rule fun_subst_typevar_case_0{tv : typevar}:
    `%%%%`(tv, [], [], ?($typeuse_typevar(tv)))

  ;; test.spectec:673.6-673.20
  rule fun_subst_typevar_case_1{tv : typevar, tv_1 : typevar, tv'_lst : typevar*, tu_1 : typeuse, tu'_lst : typeuse*, var_0 : typeuse?}:
    `%%%%`(tv, [tv_1] ++ tv'_lst, [tu_1] ++ tu'_lst, (if (tv = tv_1) then tu_1 else iter_val_2)?{iter_val_2 <- var_0})
    -- fun_subst_typevar: `%%%%`(tv, tv'_lst, tu'_lst, var_0)

  ;; test.spectec:673.6-673.20
  rule fun_subst_typevar_case_2{x0 : typevar, x1 : typevar*, x2 : typeuse*}:
    `%%%%`(x0, x1, x2, ?())
    -- ~ fun_subst_typevar_before_fun_subst_typevar_case_2: `%%%`(x0, x1, x2)
}

;; test.spectec:673.1-673.126
rec {

;; test.spectec:673.6-673.20
relation subst_typevar_is_wf: `%%%%`(v_typevar : typevar, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : typeuse)
  ;; test.spectec:673.6-673.20
  rule subst_typevar_is_wf_0{v_typevar : typevar, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : typeuse, var_0 : typeuse?}:
    `%%%%`(v_typevar, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_typevar: `%%%%`(v_typevar, var_0_lst, var_1_lst, var_0)
    -- wf_typevar: `%`(v_typevar)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (var_0 =/= ?())
    -- if (ret_val = !(var_0))
    -- wf_typeuse: `%`(ret_val)
}

;; test.spectec:737.1-737.87
rec {

;; test.spectec:737.1-737.87
def $minus_recs(var_0_lst : typevar*, var_1_lst : typeuse*) : (typevar*, typeuse*)?
  ;; test.spectec:738.1-738.39
  def $minus_recs([], []) = ?(([], []))
  ;; test.spectec:739.1-739.63
  def $minus_recs{v_n : nat, tv_lst : typevar*, tu_1 : typeuse, tu_lst : typeuse*}([REC_typevar(v_n)] ++ tv_lst, [tu_1] ++ tu_lst) = $minus_recs(tv_lst, tu_lst)
  ;; test.spectec:740.1-741.45
  def $minus_recs{x : uN, tv_lst : typevar*, tu_1 : typeuse, tu_lst : typeuse*}([_IDX_typevar(x)] ++ tv_lst, [tu_1] ++ tu_lst) = ?(([_IDX_typevar(x)] ++ tv'_lst, [tu_1] ++ tu'_lst))
    -- let{tv'_lst : typevar*, tu'_lst : typeuse*} (tv'_lst, tu'_lst) = !($minus_recs(tv_lst, tu_lst))
  def $minus_recs{x0 : typevar*, x1 : typeuse*}(x0, x1) = ?()
    -- otherwise
}

;; test.spectec:737.1-737.87
rec {

;; test.spectec:737.6-737.17
relation minus_recs_is_wf: `%%%`(var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : (typevar*, typeuse*))
  ;; test.spectec:737.6-737.17
  rule minus_recs_is_wf_0{var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : (typevar*, typeuse*)}:
    `%%%`(var_0_lst, var_1_lst, ret_val)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if ($minus_recs(var_0_lst, var_1_lst) =/= ?())
    -- if (ret_val = !($minus_recs(var_0_lst, var_1_lst)))
    -- (wf_typevar: `%`(iter))*{iter <- ret_val.0}
    -- (wf_typeuse: `%`(iter))*{iter <- ret_val.1}
}

;; test.spectec:683.1-683.112
def $subst_packtype(v_packtype : packtype, var_0_lst : typevar*, var_1_lst : typeuse*) : packtype
  ;; test.spectec:723.1-723.39
  def $subst_packtype{pt : packtype, tv_lst : typevar*, tu_lst : typeuse*}(pt, tv_lst, tu_lst) = pt

;; test.spectec:677.1-677.112
def $subst_numtype(v_numtype : numtype, var_0_lst : typevar*, var_1_lst : typeuse*) : numtype
  ;; test.spectec:709.1-709.38
  def $subst_numtype{nt : numtype, tv_lst : typevar*, tu_lst : typeuse*}(nt, tv_lst, tu_lst) = nt

;; test.spectec:678.1-678.112
def $subst_vectype(v_vectype : vectype, var_0_lst : typevar*, var_1_lst : typeuse*) : vectype
  ;; test.spectec:710.1-710.38
  def $subst_vectype{vt : vectype, tv_lst : typevar*, tu_lst : typeuse*}(vt, tv_lst, tu_lst) = vt

;; test.spectec:674.1-690.112
rec {

;; test.spectec:674.6-674.20
relation fun_subst_typeuse: `%%%%`(typeuse, typevar*, typeuse*, typeuse)
  ;; test.spectec:674.6-674.20
  rule fun_subst_typeuse_case_0{v_n : n, tv_lst : typevar*, tu_lst : typeuse*, var_0 : typeuse?}:
    `%%%%`(REC_typeuse(v_n), tv_lst, tu_lst, !(var_0))
    -- if (var_0 =/= ?())
    -- fun_subst_typevar: `%%%%`(REC_typevar(v_n), tv_lst, tu_lst, var_0)

  ;; test.spectec:674.6-674.20
  rule fun_subst_typeuse_case_1{v_typeidx : typeidx, tv_lst : typevar*, tu_lst : typeuse*, var_0 : typeuse?}:
    `%%%%`(_IDX_typeuse(v_typeidx), tv_lst, tu_lst, !(var_0))
    -- if (var_0 =/= ?())
    -- fun_subst_typevar: `%%%%`(_IDX_typevar(v_typeidx), tv_lst, tu_lst, var_0)

  ;; test.spectec:674.6-674.20
  rule fun_subst_typeuse_case_2{v_rectype : rectype, v_n : n, tv_lst : typevar*, tu_lst : typeuse*, var_0 : deftype}:
    `%%%%`(_DEF_typeuse(v_rectype, v_n), tv_lst, tu_lst, $typeuse_deftype(var_0))
    -- fun_subst_deftype: `%%%%`(_DEF_deftype(v_rectype, v_n), tv_lst, tu_lst, var_0)

;; test.spectec:679.6-679.21
relation fun_subst_heaptype: `%%%%`(heaptype, typevar*, typeuse*, heaptype)
  ;; test.spectec:679.6-679.21
  rule fun_subst_heaptype_case_0{v_n : n, tv_lst : typevar*, tu_lst : typeuse*, var_0 : typeuse?}:
    `%%%%`(REC_heaptype(v_n), tv_lst, tu_lst, $heaptype_typeuse(!(var_0)))
    -- if (var_0 =/= ?())
    -- fun_subst_typevar: `%%%%`(REC_typevar(v_n), tv_lst, tu_lst, var_0)

  ;; test.spectec:679.6-679.21
  rule fun_subst_heaptype_case_1{v_typeidx : typeidx, tv_lst : typevar*, tu_lst : typeuse*, var_0 : typeuse?}:
    `%%%%`(_IDX_heaptype(v_typeidx), tv_lst, tu_lst, $heaptype_typeuse(!(var_0)))
    -- if (var_0 =/= ?())
    -- fun_subst_typevar: `%%%%`(_IDX_typevar(v_typeidx), tv_lst, tu_lst, var_0)

  ;; test.spectec:679.6-679.21
  rule fun_subst_heaptype_case_2{v_rectype : rectype, v_n : n, tv_lst : typevar*, tu_lst : typeuse*, var_0 : deftype}:
    `%%%%`(_DEF_heaptype(v_rectype, v_n), tv_lst, tu_lst, $heaptype_deftype(var_0))
    -- fun_subst_deftype: `%%%%`(_DEF_deftype(v_rectype, v_n), tv_lst, tu_lst, var_0)

  ;; test.spectec:679.6-679.21
  rule fun_subst_heaptype_case_3{ht : heaptype, tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(ht, tv_lst, tu_lst, ht)

;; test.spectec:680.6-680.20
relation fun_subst_reftype: `%%%%`(reftype, typevar*, typeuse*, reftype)
  ;; test.spectec:680.6-680.20
  rule fun_subst_reftype_case_0{null_opt : null?, ht : heaptype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : heaptype}:
    `%%%%`(REF_reftype(null_opt, ht), tv_lst, tu_lst, REF_reftype(null_opt, var_0))
    -- fun_subst_heaptype: `%%%%`(ht, tv_lst, tu_lst, var_0)

;; test.spectec:681.6-681.20
relation fun_subst_valtype: `%%%%`(valtype, typevar*, typeuse*, valtype)
  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_0{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(I32_valtype, tv_lst, tu_lst, $valtype_numtype($subst_numtype(I32_numtype, tv_lst, tu_lst)))

  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_1{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(I64_valtype, tv_lst, tu_lst, $valtype_numtype($subst_numtype(I64_numtype, tv_lst, tu_lst)))

  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_2{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(F32_valtype, tv_lst, tu_lst, $valtype_numtype($subst_numtype(F32_numtype, tv_lst, tu_lst)))

  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_3{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(F64_valtype, tv_lst, tu_lst, $valtype_numtype($subst_numtype(F64_numtype, tv_lst, tu_lst)))

  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_4{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(V128_valtype, tv_lst, tu_lst, $valtype_vectype($subst_vectype(V128_vectype, tv_lst, tu_lst)))

  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_5{null_opt : null?, v_heaptype : heaptype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : reftype}:
    `%%%%`(REF_valtype(null_opt, v_heaptype), tv_lst, tu_lst, $valtype_reftype(var_0))
    -- fun_subst_reftype: `%%%%`(REF_reftype(null_opt, v_heaptype), tv_lst, tu_lst, var_0)

  ;; test.spectec:681.6-681.20
  rule fun_subst_valtype_case_6{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(BOT_valtype, tv_lst, tu_lst, BOT_valtype)

;; test.spectec:684.6-684.24
relation fun_subst_storagetype: `%%%%`(storagetype, typevar*, typeuse*, storagetype)
  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_0{tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(BOT_storagetype, tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(BOT_valtype, tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_1{null_opt : null?, v_heaptype : heaptype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(REF_storagetype(null_opt, v_heaptype), tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(REF_valtype(null_opt, v_heaptype), tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_2{tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(V128_storagetype, tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(V128_valtype, tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_3{tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(F64_storagetype, tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(F64_valtype, tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_4{tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(F32_storagetype, tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(F32_valtype, tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_5{tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(I64_storagetype, tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(I64_valtype, tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_6{tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(I32_storagetype, tv_lst, tu_lst, $storagetype_valtype(var_0))
    -- fun_subst_valtype: `%%%%`(I32_valtype, tv_lst, tu_lst, var_0)

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_7{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(I8_storagetype, tv_lst, tu_lst, $storagetype_packtype($subst_packtype(I8_packtype, tv_lst, tu_lst)))

  ;; test.spectec:684.6-684.24
  rule fun_subst_storagetype_case_8{tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(I16_storagetype, tv_lst, tu_lst, $storagetype_packtype($subst_packtype(I16_packtype, tv_lst, tu_lst)))

;; test.spectec:685.6-685.22
relation fun_subst_fieldtype: `%%%%`(fieldtype, typevar*, typeuse*, fieldtype)
  ;; test.spectec:685.6-685.22
  rule fun_subst_fieldtype_case_0{mut_opt : mut?, zt : storagetype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : storagetype}:
    `%%%%`(mk_fieldtype_fieldtype(mut_opt, zt), tv_lst, tu_lst, mk_fieldtype_fieldtype(mut_opt, var_0))
    -- fun_subst_storagetype: `%%%%`(zt, tv_lst, tu_lst, var_0)

;; test.spectec:687.6-687.21
relation fun_subst_comptype: `%%%%`(comptype, typevar*, typeuse*, comptype)
  ;; test.spectec:687.6-687.21
  rule fun_subst_comptype_case_0{ft_lst : fieldtype*, tv_lst : typevar*, tu_lst : typeuse*, var_0_lst : fieldtype*}:
    `%%%%`(STRUCT_comptype(mk_list_list(ft_lst)), tv_lst, tu_lst, STRUCT_comptype(mk_list_list(var_0_lst)))
    -- if (|var_0_lst| = |ft_lst|)
    -- (fun_subst_fieldtype: `%%%%`(ft, tv_lst, tu_lst, var_0))*{var_0 <- var_0_lst, ft <- ft_lst}

  ;; test.spectec:687.6-687.21
  rule fun_subst_comptype_case_1{ft : fieldtype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : fieldtype}:
    `%%%%`(ARRAY_comptype(ft), tv_lst, tu_lst, ARRAY_comptype(var_0))
    -- fun_subst_fieldtype: `%%%%`(ft, tv_lst, tu_lst, var_0)

  ;; test.spectec:687.6-687.21
  rule fun_subst_comptype_case_2{t_1_lst : valtype*, t_2_lst : valtype*, tv_lst : typevar*, tu_lst : typeuse*, var_1_lst : valtype*, var_0_lst : valtype*}:
    `%%%%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)), tv_lst, tu_lst, `FUNC%->%`_comptype(mk_list_resulttype(var_0_lst), mk_list_resulttype(var_1_lst)))
    -- if (|var_1_lst| = |t_2_lst|)
    -- (fun_subst_valtype: `%%%%`(t_2, tv_lst, tu_lst, var_1))*{var_1 <- var_1_lst, t_2 <- t_2_lst}
    -- if (|var_0_lst| = |t_1_lst|)
    -- (fun_subst_valtype: `%%%%`(t_1, tv_lst, tu_lst, var_0))*{var_0 <- var_0_lst, t_1 <- t_1_lst}

;; test.spectec:688.6-688.20
relation fun_subst_subtype: `%%%%`(subtype, typevar*, typeuse*, subtype)
  ;; test.spectec:688.6-688.20
  rule fun_subst_subtype_case_0{final_opt : final?, tu'_lst : typeuse*, ct : comptype, tv_lst : typevar*, tu_lst : typeuse*, var_1 : comptype, var_0_lst : typeuse*}:
    `%%%%`(SUB_subtype(final_opt, tu'_lst, ct), tv_lst, tu_lst, SUB_subtype(final_opt, var_0_lst, var_1))
    -- fun_subst_comptype: `%%%%`(ct, tv_lst, tu_lst, var_1)
    -- if (|var_0_lst| = |tu'_lst|)
    -- (fun_subst_typeuse: `%%%%`(tu', tv_lst, tu_lst, var_0))*{var_0 <- var_0_lst, tu' <- tu'_lst}

;; test.spectec:689.6-689.20
relation fun_subst_rectype: `%%%%`(rectype, typevar*, typeuse*, rectype)
  ;; test.spectec:689.6-689.20
  rule fun_subst_rectype_case_0{st_lst : subtype*, tv_lst : typevar*, tu_lst : typeuse*, tv'_lst : typevar*, tu'_lst : typeuse*, var_0_lst : subtype*}:
    `%%%%`(REC_rectype(mk_list_list(st_lst)), tv_lst, tu_lst, REC_rectype(mk_list_list(var_0_lst)))
    -- if (|var_0_lst| = |st_lst|)
    -- (fun_subst_subtype: `%%%%`(st, tv'_lst, tu'_lst, var_0))*{var_0 <- var_0_lst, st <- st_lst}
    -- if ($minus_recs(tv_lst, tu_lst) =/= ?())
    -- if ((tv'_lst, tu'_lst) = !($minus_recs(tv_lst, tu_lst)))

;; test.spectec:690.6-690.20
relation fun_subst_deftype: `%%%%`(deftype, typevar*, typeuse*, deftype)
  ;; test.spectec:690.6-690.20
  rule fun_subst_deftype_case_0{qt : rectype, i : nat, tv_lst : typevar*, tu_lst : typeuse*, var_0 : rectype}:
    `%%%%`(_DEF_deftype(qt, i), tv_lst, tu_lst, _DEF_deftype(var_0, i))
    -- fun_subst_rectype: `%%%%`(qt, tv_lst, tu_lst, var_0)
}

;; test.spectec:674.1-690.112
rec {

;; test.spectec:674.6-674.20
relation subst_typeuse_is_wf: `%%%%`(v_typeuse : typeuse, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : typeuse)
  ;; test.spectec:674.6-674.20
  rule subst_typeuse_is_wf_0{v_typeuse : typeuse, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : typeuse, var_0 : typeuse}:
    `%%%%`(v_typeuse, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_typeuse: `%%%%`(v_typeuse, var_0_lst, var_1_lst, var_0)
    -- wf_typeuse: `%`(v_typeuse)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:679.6-679.21
relation subst_heaptype_is_wf: `%%%%`(v_heaptype : heaptype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : heaptype)
  ;; test.spectec:679.6-679.21
  rule subst_heaptype_is_wf_0{v_heaptype : heaptype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : heaptype, var_0 : heaptype}:
    `%%%%`(v_heaptype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_heaptype: `%%%%`(v_heaptype, var_0_lst, var_1_lst, var_0)
    -- wf_heaptype: `%`(v_heaptype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_heaptype: `%`(ret_val)

;; test.spectec:680.6-680.20
relation subst_reftype_is_wf: `%%%%`(v_reftype : reftype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : reftype)
  ;; test.spectec:680.6-680.20
  rule subst_reftype_is_wf_0{v_reftype : reftype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : reftype, var_0 : reftype}:
    `%%%%`(v_reftype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_reftype: `%%%%`(v_reftype, var_0_lst, var_1_lst, var_0)
    -- wf_reftype: `%`(v_reftype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:681.6-681.20
relation subst_valtype_is_wf: `%%%%`(v_valtype : valtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : valtype)
  ;; test.spectec:681.6-681.20
  rule subst_valtype_is_wf_0{v_valtype : valtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : valtype, var_0 : valtype}:
    `%%%%`(v_valtype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_valtype: `%%%%`(v_valtype, var_0_lst, var_1_lst, var_0)
    -- wf_valtype: `%`(v_valtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_valtype: `%`(ret_val)

;; test.spectec:684.6-684.24
relation subst_storagetype_is_wf: `%%%%`(v_storagetype : storagetype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : storagetype)
  ;; test.spectec:684.6-684.24
  rule subst_storagetype_is_wf_0{v_storagetype : storagetype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : storagetype, var_0 : storagetype}:
    `%%%%`(v_storagetype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_storagetype: `%%%%`(v_storagetype, var_0_lst, var_1_lst, var_0)
    -- wf_storagetype: `%`(v_storagetype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_storagetype: `%`(ret_val)

;; test.spectec:685.6-685.22
relation subst_fieldtype_is_wf: `%%%%`(v_fieldtype : fieldtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : fieldtype)
  ;; test.spectec:685.6-685.22
  rule subst_fieldtype_is_wf_0{v_fieldtype : fieldtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : fieldtype, var_0 : fieldtype}:
    `%%%%`(v_fieldtype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_fieldtype: `%%%%`(v_fieldtype, var_0_lst, var_1_lst, var_0)
    -- wf_fieldtype: `%`(v_fieldtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_fieldtype: `%`(ret_val)

;; test.spectec:687.6-687.21
relation subst_comptype_is_wf: `%%%%`(v_comptype : comptype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : comptype)
  ;; test.spectec:687.6-687.21
  rule subst_comptype_is_wf_0{v_comptype : comptype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : comptype, var_0 : comptype}:
    `%%%%`(v_comptype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_comptype: `%%%%`(v_comptype, var_0_lst, var_1_lst, var_0)
    -- wf_comptype: `%`(v_comptype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_comptype: `%`(ret_val)

;; test.spectec:688.6-688.20
relation subst_subtype_is_wf: `%%%%`(v_subtype : subtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : subtype)
  ;; test.spectec:688.6-688.20
  rule subst_subtype_is_wf_0{v_subtype : subtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : subtype, var_0 : subtype}:
    `%%%%`(v_subtype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_subtype: `%%%%`(v_subtype, var_0_lst, var_1_lst, var_0)
    -- wf_subtype: `%`(v_subtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_subtype: `%`(ret_val)
}

;; test.spectec:676.1-676.112
def $subst_addrtype(v_addrtype : addrtype, var_0_lst : typevar*, var_1_lst : typeuse*) : addrtype
  ;; test.spectec:708.1-708.39
  def $subst_addrtype{at : addrtype, tv_lst : typevar*, tu_lst : typeuse*}(at, tv_lst, tu_lst) = at

;; test.spectec:692.6-692.20
relation fun_subst_tagtype: `%%%%`(tagtype, typevar*, typeuse*, tagtype)
  ;; test.spectec:692.6-692.20
  rule fun_subst_tagtype_case_0{tu' : typeuse, tv_lst : typevar*, tu_lst : typeuse*, var_0 : tagtype}:
    `%%%%`(tu', tv_lst, tu_lst, var_0)
    -- fun_subst_typeuse: `%%%%`(tu', tv_lst, tu_lst, var_0)

;; test.spectec:692.6-692.20
relation subst_tagtype_is_wf: `%%%%`(v_tagtype : tagtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : tagtype)
  ;; test.spectec:692.6-692.20
  rule subst_tagtype_is_wf_0{v_tagtype : tagtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : tagtype, var_0 : tagtype}:
    `%%%%`(v_tagtype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_tagtype: `%%%%`(v_tagtype, var_0_lst, var_1_lst, var_0)
    -- wf_typeuse: `%`(v_tagtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:693.6-693.23
relation fun_subst_globaltype: `%%%%`(globaltype, typevar*, typeuse*, globaltype)
  ;; test.spectec:693.6-693.23
  rule fun_subst_globaltype_case_0{mut_opt : mut?, t : valtype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : valtype}:
    `%%%%`(mk_globaltype_globaltype(mut_opt, t), tv_lst, tu_lst, mk_globaltype_globaltype(mut_opt, var_0))
    -- fun_subst_valtype: `%%%%`(t, tv_lst, tu_lst, var_0)

;; test.spectec:693.6-693.23
relation subst_globaltype_is_wf: `%%%%`(v_globaltype : globaltype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : globaltype)
  ;; test.spectec:693.6-693.23
  rule subst_globaltype_is_wf_0{v_globaltype : globaltype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : globaltype, var_0 : globaltype}:
    `%%%%`(v_globaltype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_globaltype: `%%%%`(v_globaltype, var_0_lst, var_1_lst, var_0)
    -- wf_globaltype: `%`(v_globaltype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_globaltype: `%`(ret_val)

;; test.spectec:694.1-694.112
def $subst_memtype(v_memtype : memtype, var_0_lst : typevar*, var_1_lst : typeuse*) : memtype
  ;; test.spectec:753.1-753.58
  def $subst_memtype{at : addrtype, lim : limits, tv_lst : typevar*, tu_lst : typeuse*}(`%%PAGE`_memtype(at, lim), tv_lst, tu_lst) = `%%PAGE`_memtype(at, lim)

;; test.spectec:694.6-694.20
relation subst_memtype_is_wf: `%%%%`(v_memtype : memtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : memtype)
  ;; test.spectec:694.6-694.20
  rule subst_memtype_is_wf_0{v_memtype : memtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : memtype}:
    `%%%%`(v_memtype, var_0_lst, var_1_lst, ret_val)
    -- wf_memtype: `%`(v_memtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = $subst_memtype(v_memtype, var_0_lst, var_1_lst))
    -- wf_memtype: `%`(ret_val)

;; test.spectec:695.6-695.22
relation fun_subst_tabletype: `%%%%`(tabletype, typevar*, typeuse*, tabletype)
  ;; test.spectec:695.6-695.22
  rule fun_subst_tabletype_case_0{at : addrtype, lim : limits, rt : reftype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : reftype}:
    `%%%%`(mk_tabletype_tabletype(at, lim, rt), tv_lst, tu_lst, mk_tabletype_tabletype(at, lim, var_0))
    -- fun_subst_reftype: `%%%%`(rt, tv_lst, tu_lst, var_0)

;; test.spectec:695.6-695.22
relation subst_tabletype_is_wf: `%%%%`(v_tabletype : tabletype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : tabletype)
  ;; test.spectec:695.6-695.22
  rule subst_tabletype_is_wf_0{v_tabletype : tabletype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : tabletype, var_0 : tabletype}:
    `%%%%`(v_tabletype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_tabletype: `%%%%`(v_tabletype, var_0_lst, var_1_lst, var_0)
    -- wf_tabletype: `%`(v_tabletype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_tabletype: `%`(ret_val)

;; test.spectec:697.6-697.23
relation fun_subst_externtype: `%%%%`(externtype, typevar*, typeuse*, externtype)
  ;; test.spectec:697.6-697.23
  rule fun_subst_externtype_case_0{jt : typeuse, tv_lst : typevar*, tu_lst : typeuse*, var_0 : tagtype}:
    `%%%%`(TAG_externtype(jt), tv_lst, tu_lst, TAG_externtype(var_0))
    -- fun_subst_tagtype: `%%%%`(jt, tv_lst, tu_lst, var_0)

  ;; test.spectec:697.6-697.23
  rule fun_subst_externtype_case_1{gt : globaltype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : globaltype}:
    `%%%%`(GLOBAL_externtype(gt), tv_lst, tu_lst, GLOBAL_externtype(var_0))
    -- fun_subst_globaltype: `%%%%`(gt, tv_lst, tu_lst, var_0)

  ;; test.spectec:697.6-697.23
  rule fun_subst_externtype_case_2{tt : tabletype, tv_lst : typevar*, tu_lst : typeuse*, var_0 : tabletype}:
    `%%%%`(TABLE_externtype(tt), tv_lst, tu_lst, TABLE_externtype(var_0))
    -- fun_subst_tabletype: `%%%%`(tt, tv_lst, tu_lst, var_0)

  ;; test.spectec:697.6-697.23
  rule fun_subst_externtype_case_3{mt : memtype, tv_lst : typevar*, tu_lst : typeuse*}:
    `%%%%`(MEM_externtype(mt), tv_lst, tu_lst, MEM_externtype($subst_memtype(mt, tv_lst, tu_lst)))

  ;; test.spectec:697.6-697.23
  rule fun_subst_externtype_case_4{tu' : typeuse, tv_lst : typevar*, tu_lst : typeuse*, var_0 : typeuse}:
    `%%%%`(FUNC_externtype(tu'), tv_lst, tu_lst, FUNC_externtype(var_0))
    -- fun_subst_typeuse: `%%%%`(tu', tv_lst, tu_lst, var_0)

;; test.spectec:697.6-697.23
relation subst_externtype_is_wf: `%%%%`(v_externtype : externtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : externtype)
  ;; test.spectec:697.6-697.23
  rule subst_externtype_is_wf_0{v_externtype : externtype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : externtype, var_0 : externtype}:
    `%%%%`(v_externtype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_externtype: `%%%%`(v_externtype, var_0_lst, var_1_lst, var_0)
    -- wf_externtype: `%`(v_externtype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_externtype: `%`(ret_val)

;; test.spectec:698.6-698.23
relation fun_subst_moduletype: `%%%%`(moduletype, typevar*, typeuse*, moduletype)
  ;; test.spectec:698.6-698.23
  rule fun_subst_moduletype_case_0{xt_1_lst : externtype*, xt_2_lst : externtype*, tv_lst : typevar*, tu_lst : typeuse*, var_1_lst : externtype*, var_0_lst : externtype*}:
    `%%%%`(mk_moduletype_moduletype(xt_1_lst, xt_2_lst), tv_lst, tu_lst, mk_moduletype_moduletype(var_0_lst, var_1_lst))
    -- if (|var_1_lst| = |xt_2_lst|)
    -- (fun_subst_externtype: `%%%%`(xt_2, tv_lst, tu_lst, var_1))*{var_1 <- var_1_lst, xt_2 <- xt_2_lst}
    -- if (|var_0_lst| = |xt_1_lst|)
    -- (fun_subst_externtype: `%%%%`(xt_1, tv_lst, tu_lst, var_0))*{var_0 <- var_0_lst, xt_1 <- xt_1_lst}

;; test.spectec:698.6-698.23
relation subst_moduletype_is_wf: `%%%%`(v_moduletype : moduletype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : moduletype)
  ;; test.spectec:698.6-698.23
  rule subst_moduletype_is_wf_0{v_moduletype : moduletype, var_0_lst : typevar*, var_1_lst : typeuse*, ret_val : moduletype, var_0 : moduletype}:
    `%%%%`(v_moduletype, var_0_lst, var_1_lst, ret_val)
    -- fun_subst_moduletype: `%%%%`(v_moduletype, var_0_lst, var_1_lst, var_0)
    -- wf_moduletype: `%`(v_moduletype)
    -- (wf_typevar: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_moduletype: `%`(ret_val)

;; test.spectec:767.6-767.24
relation fun_subst_all_valtype: `%%%`(valtype, typeuse*, valtype)
  ;; test.spectec:767.6-767.24
  rule fun_subst_all_valtype_case_0{t : valtype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : valtype}:
    `%%%`(t, tu_lst, var_0)
    -- fun_subst_valtype: `%%%%`(t, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:767.6-767.24
relation subst_all_valtype_is_wf: `%%%`(v_valtype : valtype, var_0_lst : typeuse*, ret_val : valtype)
  ;; test.spectec:767.6-767.24
  rule subst_all_valtype_is_wf_0{v_valtype : valtype, var_0_lst : typeuse*, ret_val : valtype, var_0 : valtype}:
    `%%%`(v_valtype, var_0_lst, ret_val)
    -- fun_subst_all_valtype: `%%%`(v_valtype, var_0_lst, var_0)
    -- wf_valtype: `%`(v_valtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_valtype: `%`(ret_val)

;; test.spectec:768.6-768.24
relation fun_subst_all_reftype: `%%%`(reftype, typeuse*, reftype)
  ;; test.spectec:768.6-768.24
  rule fun_subst_all_reftype_case_0{rt : reftype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : reftype}:
    `%%%`(rt, tu_lst, var_0)
    -- fun_subst_reftype: `%%%%`(rt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:768.6-768.24
relation subst_all_reftype_is_wf: `%%%`(v_reftype : reftype, var_0_lst : typeuse*, ret_val : reftype)
  ;; test.spectec:768.6-768.24
  rule subst_all_reftype_is_wf_0{v_reftype : reftype, var_0_lst : typeuse*, ret_val : reftype, var_0 : reftype}:
    `%%%`(v_reftype, var_0_lst, ret_val)
    -- fun_subst_all_reftype: `%%%`(v_reftype, var_0_lst, var_0)
    -- wf_reftype: `%`(v_reftype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:769.6-769.24
relation fun_subst_all_deftype: `%%%`(deftype, typeuse*, deftype)
  ;; test.spectec:769.6-769.24
  rule fun_subst_all_deftype_case_0{dt : deftype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : deftype}:
    `%%%`(dt, tu_lst, var_0)
    -- fun_subst_deftype: `%%%%`(dt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:770.6-770.24
relation fun_subst_all_tagtype: `%%%`(tagtype, typeuse*, tagtype)
  ;; test.spectec:770.6-770.24
  rule fun_subst_all_tagtype_case_0{jt : typeuse, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : tagtype}:
    `%%%`(jt, tu_lst, var_0)
    -- fun_subst_tagtype: `%%%%`(jt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:770.6-770.24
relation subst_all_tagtype_is_wf: `%%%`(v_tagtype : tagtype, var_0_lst : typeuse*, ret_val : tagtype)
  ;; test.spectec:770.6-770.24
  rule subst_all_tagtype_is_wf_0{v_tagtype : tagtype, var_0_lst : typeuse*, ret_val : tagtype, var_0 : tagtype}:
    `%%%`(v_tagtype, var_0_lst, ret_val)
    -- fun_subst_all_tagtype: `%%%`(v_tagtype, var_0_lst, var_0)
    -- wf_typeuse: `%`(v_tagtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:771.6-771.27
relation fun_subst_all_globaltype: `%%%`(globaltype, typeuse*, globaltype)
  ;; test.spectec:771.6-771.27
  rule fun_subst_all_globaltype_case_0{gt : globaltype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : globaltype}:
    `%%%`(gt, tu_lst, var_0)
    -- fun_subst_globaltype: `%%%%`(gt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:771.6-771.27
relation subst_all_globaltype_is_wf: `%%%`(v_globaltype : globaltype, var_0_lst : typeuse*, ret_val : globaltype)
  ;; test.spectec:771.6-771.27
  rule subst_all_globaltype_is_wf_0{v_globaltype : globaltype, var_0_lst : typeuse*, ret_val : globaltype, var_0 : globaltype}:
    `%%%`(v_globaltype, var_0_lst, ret_val)
    -- fun_subst_all_globaltype: `%%%`(v_globaltype, var_0_lst, var_0)
    -- wf_globaltype: `%`(v_globaltype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_globaltype: `%`(ret_val)

;; test.spectec:772.6-772.24
relation fun_subst_all_memtype: `%%%`(memtype, typeuse*, memtype)
  ;; test.spectec:772.6-772.24
  rule fun_subst_all_memtype_case_0{mt : memtype, v_n : nat, tu_lst : typeuse*, i : nat}:
    `%%%`(mt, tu_lst, $subst_memtype(mt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst))
    -- if (v_n = |tu_lst|)

;; test.spectec:772.6-772.24
relation subst_all_memtype_is_wf: `%%%`(v_memtype : memtype, var_0_lst : typeuse*, ret_val : memtype)
  ;; test.spectec:772.6-772.24
  rule subst_all_memtype_is_wf_0{v_memtype : memtype, var_0_lst : typeuse*, ret_val : memtype, var_0 : memtype}:
    `%%%`(v_memtype, var_0_lst, ret_val)
    -- fun_subst_all_memtype: `%%%`(v_memtype, var_0_lst, var_0)
    -- wf_memtype: `%`(v_memtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_memtype: `%`(ret_val)

;; test.spectec:773.6-773.26
relation fun_subst_all_tabletype: `%%%`(tabletype, typeuse*, tabletype)
  ;; test.spectec:773.6-773.26
  rule fun_subst_all_tabletype_case_0{tt : tabletype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : tabletype}:
    `%%%`(tt, tu_lst, var_0)
    -- fun_subst_tabletype: `%%%%`(tt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:773.6-773.26
relation subst_all_tabletype_is_wf: `%%%`(v_tabletype : tabletype, var_0_lst : typeuse*, ret_val : tabletype)
  ;; test.spectec:773.6-773.26
  rule subst_all_tabletype_is_wf_0{v_tabletype : tabletype, var_0_lst : typeuse*, ret_val : tabletype, var_0 : tabletype}:
    `%%%`(v_tabletype, var_0_lst, ret_val)
    -- fun_subst_all_tabletype: `%%%`(v_tabletype, var_0_lst, var_0)
    -- wf_tabletype: `%`(v_tabletype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_tabletype: `%`(ret_val)

;; test.spectec:774.6-774.27
relation fun_subst_all_externtype: `%%%`(externtype, typeuse*, externtype)
  ;; test.spectec:774.6-774.27
  rule fun_subst_all_externtype_case_0{xt : externtype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : externtype}:
    `%%%`(xt, tu_lst, var_0)
    -- fun_subst_externtype: `%%%%`(xt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:774.6-774.27
relation subst_all_externtype_is_wf: `%%%`(v_externtype : externtype, var_0_lst : typeuse*, ret_val : externtype)
  ;; test.spectec:774.6-774.27
  rule subst_all_externtype_is_wf_0{v_externtype : externtype, var_0_lst : typeuse*, ret_val : externtype, var_0 : externtype}:
    `%%%`(v_externtype, var_0_lst, ret_val)
    -- fun_subst_all_externtype: `%%%`(v_externtype, var_0_lst, var_0)
    -- wf_externtype: `%`(v_externtype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_externtype: `%`(ret_val)

;; test.spectec:775.6-775.27
relation fun_subst_all_moduletype: `%%%`(moduletype, typeuse*, moduletype)
  ;; test.spectec:775.6-775.27
  rule fun_subst_all_moduletype_case_0{mmt : moduletype, v_n : nat, tu_lst : typeuse*, i : nat, var_0 : moduletype}:
    `%%%`(mmt, tu_lst, var_0)
    -- fun_subst_moduletype: `%%%%`(mmt, _IDX_typevar(mk_uN_typeidx(i))^(i<v_n){}, tu_lst, var_0)
    -- if (v_n = |tu_lst|)

;; test.spectec:775.6-775.27
relation subst_all_moduletype_is_wf: `%%%`(v_moduletype : moduletype, var_0_lst : typeuse*, ret_val : moduletype)
  ;; test.spectec:775.6-775.27
  rule subst_all_moduletype_is_wf_0{v_moduletype : moduletype, var_0_lst : typeuse*, ret_val : moduletype, var_0 : moduletype}:
    `%%%`(v_moduletype, var_0_lst, ret_val)
    -- fun_subst_all_moduletype: `%%%`(v_moduletype, var_0_lst, var_0)
    -- wf_moduletype: `%`(v_moduletype)
    -- (wf_typeuse: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_moduletype: `%`(ret_val)

;; test.spectec:787.1-787.97
rec {

;; test.spectec:787.6-787.25
relation fun_subst_all_deftypes: `%%%`(deftype*, typeuse*, deftype*)
  ;; test.spectec:787.6-787.25
  rule fun_subst_all_deftypes_case_0{tu_lst : typeuse*}:
    `%%%`([], tu_lst, [])

  ;; test.spectec:787.6-787.25
  rule fun_subst_all_deftypes_case_1{dt_1 : deftype, dt_lst : deftype*, tu_lst : typeuse*, var_1 : deftype*, var_0 : deftype}:
    `%%%`([dt_1] ++ dt_lst, tu_lst, [var_0] ++ var_1)
    -- fun_subst_all_deftypes: `%%%`(dt_lst, tu_lst, var_1)
    -- fun_subst_all_deftype: `%%%`(dt_1, tu_lst, var_0)
}

;; test.spectec:794.6-794.13
relation fun_rollrt: `%%%`(typeidx, rectype, rectype)
  ;; test.spectec:794.6-794.13
  rule fun_rollrt_case_0{x : uN, v_rectype : rectype, i : nat, v_n : nat, subtype_lst : subtype*, var_0_lst : subtype*}:
    `%%%`(x, v_rectype, REC_rectype(mk_list_list(var_0_lst)))
    -- (fun_subst_subtype: `%%%%`(v_subtype, _IDX_typevar(mk_uN_typeidx(($proj_uN_0(x).0 + i)))^(i<v_n){}, REC_typeuse(i)^(i<v_n){}, var_0))^v_n{var_0 <- var_0_lst, v_subtype <- subtype_lst}
    -- if (v_rectype = REC_rectype(mk_list_list(subtype_lst)))

;; test.spectec:795.6-795.15
relation fun_unrollrt: `%%`(rectype, rectype)
  ;; test.spectec:795.6-795.15
  rule fun_unrollrt_case_0{v_rectype : rectype, i : nat, v_n : nat, subtype_lst : subtype*, var_0_lst : subtype*}:
    `%%`(v_rectype, REC_rectype(mk_list_list(var_0_lst)))
    -- (fun_subst_subtype: `%%%%`(v_subtype, REC_typevar(i)^(i<v_n){}, _DEF_typeuse(v_rectype, i)^(i<v_n){}, var_0))^v_n{var_0 <- var_0_lst, v_subtype <- subtype_lst}
    -- if (v_rectype = REC_rectype(mk_list_list(subtype_lst)))

;; test.spectec:796.6-796.13
relation fun_rolldt: `%%%`(typeidx, rectype, deftype*)
  ;; test.spectec:796.6-796.13
  rule fun_rolldt_case_0{x : uN, v_rectype : rectype, v_n : nat, subtype_lst : subtype*, var_0 : rectype}:
    `%%%`(x, v_rectype, _DEF_deftype(REC_rectype(mk_list_list(subtype_lst)), i)^(i<v_n){})
    -- fun_rollrt: `%%%`(x, v_rectype, var_0)
    -- if (var_0 = REC_rectype(mk_list_list(subtype_lst)))

;; test.spectec:797.6-797.15
relation fun_unrolldt: `%%`(deftype, subtype)
  ;; test.spectec:797.6-797.15
  rule fun_unrolldt_case_0{v_rectype : rectype, i : nat, subtype_lst : subtype*, var_0 : rectype}:
    `%%`(_DEF_deftype(v_rectype, i), subtype_lst[i])
    -- if (i < |subtype_lst|)
    -- fun_unrollrt: `%%`(v_rectype, var_0)
    -- if (REC_rectype(mk_list_list(subtype_lst)) = var_0)

;; test.spectec:797.6-797.15
relation unrolldt_is_wf: `%%`(v_deftype : deftype, ret_val : subtype)
  ;; test.spectec:797.6-797.15
  rule unrolldt_is_wf_0{v_deftype : deftype, ret_val : subtype, var_0 : subtype}:
    `%%`(v_deftype, ret_val)
    -- fun_unrolldt: `%%`(v_deftype, var_0)
    -- if (ret_val = var_0)
    -- wf_subtype: `%`(ret_val)

;; test.spectec:810.1-810.36
def $free_addrtype(v_addrtype : addrtype) : free
  ;; test.spectec:840.1-840.34
  def $free_addrtype{v_addrtype : addrtype}(v_addrtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:810.6-810.20
relation free_addrtype_is_wf: `%%`(v_addrtype : addrtype, ret_val : free)
  ;; test.spectec:810.6-810.20
  rule free_addrtype_is_wf_0{v_addrtype : addrtype, ret_val : free}:
    `%%`(v_addrtype, ret_val)
    -- if (ret_val = $free_addrtype(v_addrtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:811.1-811.34
def $free_numtype(v_numtype : numtype) : free
  ;; test.spectec:842.1-842.32
  def $free_numtype{v_numtype : numtype}(v_numtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:811.6-811.19
relation free_numtype_is_wf: `%%`(v_numtype : numtype, ret_val : free)
  ;; test.spectec:811.6-811.19
  rule free_numtype_is_wf_0{v_numtype : numtype, ret_val : free}:
    `%%`(v_numtype, ret_val)
    -- if (ret_val = $free_numtype(v_numtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:812.1-812.36
def $free_packtype(v_packtype : packtype) : free
  ;; test.spectec:844.1-844.34
  def $free_packtype{v_packtype : packtype}(v_packtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:812.6-812.20
relation free_packtype_is_wf: `%%`(v_packtype : packtype, ret_val : free)
  ;; test.spectec:812.6-812.20
  rule free_packtype_is_wf_0{v_packtype : packtype, ret_val : free}:
    `%%`(v_packtype, ret_val)
    -- if (ret_val = $free_packtype(v_packtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:813.1-813.36
def $free_lanetype(v_lanetype : lanetype) : free
  ;; test.spectec:846.1-846.53
  def $free_lanetype(I32_lanetype) = $free_numtype(I32_numtype)
  ;; test.spectec:846.1-846.53
  def $free_lanetype(I64_lanetype) = $free_numtype(I64_numtype)
  ;; test.spectec:846.1-846.53
  def $free_lanetype(F32_lanetype) = $free_numtype(F32_numtype)
  ;; test.spectec:846.1-846.53
  def $free_lanetype(F64_lanetype) = $free_numtype(F64_numtype)
  ;; test.spectec:847.1-847.56
  def $free_lanetype(I8_lanetype) = $free_packtype(I8_packtype)
  ;; test.spectec:847.1-847.56
  def $free_lanetype(I16_lanetype) = $free_packtype(I16_packtype)

;; test.spectec:813.6-813.20
relation free_lanetype_is_wf: `%%`(v_lanetype : lanetype, ret_val : free)
  ;; test.spectec:813.6-813.20
  rule free_lanetype_is_wf_0{v_lanetype : lanetype, ret_val : free}:
    `%%`(v_lanetype, ret_val)
    -- if (ret_val = $free_lanetype(v_lanetype))
    -- wf_free: `%`(ret_val)

;; test.spectec:814.1-814.34
def $free_vectype(v_vectype : vectype) : free
  ;; test.spectec:849.1-849.32
  def $free_vectype{v_vectype : vectype}(v_vectype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:814.6-814.19
relation free_vectype_is_wf: `%%`(v_vectype : vectype, ret_val : free)
  ;; test.spectec:814.6-814.19
  rule free_vectype_is_wf_0{v_vectype : vectype, ret_val : free}:
    `%%`(v_vectype, ret_val)
    -- if (ret_val = $free_vectype(v_vectype))
    -- wf_free: `%`(ret_val)

;; test.spectec:815.1-815.38
def $free_consttype(v_consttype : consttype) : free
  ;; test.spectec:851.1-851.54
  def $free_consttype(I32_consttype) = $free_numtype(I32_numtype)
  ;; test.spectec:851.1-851.54
  def $free_consttype(I64_consttype) = $free_numtype(I64_numtype)
  ;; test.spectec:851.1-851.54
  def $free_consttype(F32_consttype) = $free_numtype(F32_numtype)
  ;; test.spectec:851.1-851.54
  def $free_consttype(F64_consttype) = $free_numtype(F64_numtype)
  ;; test.spectec:852.1-852.54
  def $free_consttype(V128_consttype) = $free_vectype(V128_vectype)

;; test.spectec:815.6-815.21
relation free_consttype_is_wf: `%%`(v_consttype : consttype, ret_val : free)
  ;; test.spectec:815.6-815.21
  rule free_consttype_is_wf_0{v_consttype : consttype, ret_val : free}:
    `%%`(v_consttype, ret_val)
    -- if (ret_val = $free_consttype(v_consttype))
    -- wf_free: `%`(ret_val)

;; test.spectec:816.1-816.42
def $free_absheaptype(v_absheaptype : absheaptype) : free
  ;; test.spectec:854.1-854.40
  def $free_absheaptype{v_absheaptype : absheaptype}(v_absheaptype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:816.6-816.23
relation free_absheaptype_is_wf: `%%`(v_absheaptype : absheaptype, ret_val : free)
  ;; test.spectec:816.6-816.23
  rule free_absheaptype_is_wf_0{v_absheaptype : absheaptype, ret_val : free}:
    `%%`(v_absheaptype, ret_val)
    -- if (ret_val = $free_absheaptype(v_absheaptype))
    -- wf_free: `%`(ret_val)

;; test.spectec:819.1-819.34
def $free_typevar(v_typevar : typevar) : free
  ;; test.spectec:859.1-859.57
  def $free_typevar{v_typeidx : uN}(_IDX_typevar(v_typeidx)) = $free_typeidx(v_typeidx)
  ;; test.spectec:860.1-860.30
  def $free_typevar{v_n : nat}(REC_typevar(v_n)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:819.6-819.19
relation free_typevar_is_wf: `%%`(v_typevar : typevar, ret_val : free)
  ;; test.spectec:819.6-819.19
  rule free_typevar_is_wf_0{v_typevar : typevar, ret_val : free}:
    `%%`(v_typevar, ret_val)
    -- wf_typevar: `%`(v_typevar)
    -- if (ret_val = $free_typevar(v_typevar))
    -- wf_free: `%`(ret_val)

;; test.spectec:817.1-856.34
rec {

;; test.spectec:817.6-817.20
relation fun_free_heaptype: `%%`(heaptype, free)
  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_0:
    `%%`(ANY_heaptype, $free_absheaptype(ANY_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_1:
    `%%`(EQ_heaptype, $free_absheaptype(EQ_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_2:
    `%%`(I31_heaptype, $free_absheaptype(I31_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_3:
    `%%`(STRUCT_heaptype, $free_absheaptype(STRUCT_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_4:
    `%%`(ARRAY_heaptype, $free_absheaptype(ARRAY_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_5:
    `%%`(NONE_heaptype, $free_absheaptype(NONE_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_6:
    `%%`(FUNC_heaptype, $free_absheaptype(FUNC_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_7:
    `%%`(NOFUNC_heaptype, $free_absheaptype(NOFUNC_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_8:
    `%%`(EXN_heaptype, $free_absheaptype(EXN_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_9:
    `%%`(NOEXN_heaptype, $free_absheaptype(NOEXN_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_10:
    `%%`(EXTERN_heaptype, $free_absheaptype(EXTERN_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_11:
    `%%`(NOEXTERN_heaptype, $free_absheaptype(NOEXTERN_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_12:
    `%%`(BOT_heaptype, $free_absheaptype(BOT_absheaptype))

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_13{n_0 : n, var_0 : free}:
    `%%`(REC_heaptype(n_0), var_0)
    -- fun_free_typeuse: `%%`(REC_typeuse(n_0), var_0)

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_14{v_rectype : rectype, v_n : n, var_0 : free}:
    `%%`(_DEF_heaptype(v_rectype, v_n), var_0)
    -- fun_free_typeuse: `%%`(_DEF_typeuse(v_rectype, v_n), var_0)

  ;; test.spectec:817.6-817.20
  rule fun_free_heaptype_case_15{v_typeidx : typeidx, var_0 : free}:
    `%%`(_IDX_heaptype(v_typeidx), var_0)
    -- fun_free_typeuse: `%%`(_IDX_typeuse(v_typeidx), var_0)

;; test.spectec:818.6-818.19
relation fun_free_reftype: `%%`(reftype, free)
  ;; test.spectec:818.6-818.19
  rule fun_free_reftype_case_0{null_opt : null?, v_heaptype : heaptype, var_0 : free}:
    `%%`(REF_reftype(null_opt, v_heaptype), var_0)
    -- fun_free_heaptype: `%%`(v_heaptype, var_0)

;; test.spectec:820.6-820.19
relation fun_free_typeuse: `%%`(typeuse, free)
  ;; test.spectec:820.6-820.19
  rule fun_free_typeuse_case_0{v_n : n}:
    `%%`(REC_typeuse(v_n), $free_typevar(REC_typevar(v_n)))

  ;; test.spectec:820.6-820.19
  rule fun_free_typeuse_case_1{v_typeidx : typeidx}:
    `%%`(_IDX_typeuse(v_typeidx), $free_typevar(_IDX_typevar(v_typeidx)))

  ;; test.spectec:820.6-820.19
  rule fun_free_typeuse_case_2{v_rectype : rectype, v_n : n, var_0 : free}:
    `%%`(_DEF_typeuse(v_rectype, v_n), var_0)
    -- fun_free_deftype: `%%`(_DEF_deftype(v_rectype, v_n), var_0)

;; test.spectec:821.6-821.19
relation fun_free_valtype: `%%`(valtype, free)
  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_0:
    `%%`(I32_valtype, $free_numtype(I32_numtype))

  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_1:
    `%%`(I64_valtype, $free_numtype(I64_numtype))

  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_2:
    `%%`(F32_valtype, $free_numtype(F32_numtype))

  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_3:
    `%%`(F64_valtype, $free_numtype(F64_numtype))

  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_4:
    `%%`(V128_valtype, $free_vectype(V128_vectype))

  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_5{null_opt : null?, v_heaptype : heaptype, var_0 : free}:
    `%%`(REF_valtype(null_opt, v_heaptype), var_0)
    -- fun_free_reftype: `%%`(REF_reftype(null_opt, v_heaptype), var_0)

  ;; test.spectec:821.6-821.19
  rule fun_free_valtype_case_6:
    `%%`(BOT_valtype, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

;; test.spectec:823.6-823.22
relation fun_free_resulttype: `%%`(resulttype, free)
  ;; test.spectec:823.6-823.22
  rule fun_free_resulttype_case_0{valtype_lst : valtype*, var_1_lst : free*, var_0 : free}:
    `%%`(mk_list_resulttype(valtype_lst), var_0)
    -- if (|var_1_lst| = |valtype_lst|)
    -- (fun_free_valtype: `%%`(v_valtype, var_1))*{var_1 <- var_1_lst, v_valtype <- valtype_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:824.6-824.23
relation fun_free_storagetype: `%%`(storagetype, free)
  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_0{var_0 : free}:
    `%%`(BOT_storagetype, var_0)
    -- fun_free_valtype: `%%`(BOT_valtype, var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_1{null_opt : null?, v_heaptype : heaptype, var_0 : free}:
    `%%`(REF_storagetype(null_opt, v_heaptype), var_0)
    -- fun_free_valtype: `%%`(REF_valtype(null_opt, v_heaptype), var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_2{var_0 : free}:
    `%%`(V128_storagetype, var_0)
    -- fun_free_valtype: `%%`(V128_valtype, var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_3{var_0 : free}:
    `%%`(F64_storagetype, var_0)
    -- fun_free_valtype: `%%`(F64_valtype, var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_4{var_0 : free}:
    `%%`(F32_storagetype, var_0)
    -- fun_free_valtype: `%%`(F32_valtype, var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_5{var_0 : free}:
    `%%`(I64_storagetype, var_0)
    -- fun_free_valtype: `%%`(I64_valtype, var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_6{var_0 : free}:
    `%%`(I32_storagetype, var_0)
    -- fun_free_valtype: `%%`(I32_valtype, var_0)

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_7:
    `%%`(I8_storagetype, $free_packtype(I8_packtype))

  ;; test.spectec:824.6-824.23
  rule fun_free_storagetype_case_8:
    `%%`(I16_storagetype, $free_packtype(I16_packtype))

;; test.spectec:825.6-825.21
relation fun_free_fieldtype: `%%`(fieldtype, free)
  ;; test.spectec:825.6-825.21
  rule fun_free_fieldtype_case_0{mut_opt : mut?, v_storagetype : storagetype, var_0 : free}:
    `%%`(mk_fieldtype_fieldtype(mut_opt, v_storagetype), var_0)
    -- fun_free_storagetype: `%%`(v_storagetype, var_0)

;; test.spectec:826.6-826.20
relation fun_free_comptype: `%%`(comptype, free)
  ;; test.spectec:826.6-826.20
  rule fun_free_comptype_case_0{fieldtype_lst : fieldtype*, var_1_lst : free*, var_0 : free}:
    `%%`(STRUCT_comptype(mk_list_list(fieldtype_lst)), var_0)
    -- if (|var_1_lst| = |fieldtype_lst|)
    -- (fun_free_fieldtype: `%%`(v_fieldtype, var_1))*{var_1 <- var_1_lst, v_fieldtype <- fieldtype_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

  ;; test.spectec:826.6-826.20
  rule fun_free_comptype_case_1{v_fieldtype : fieldtype, var_0 : free}:
    `%%`(ARRAY_comptype(v_fieldtype), var_0)
    -- fun_free_fieldtype: `%%`(v_fieldtype, var_0)

  ;; test.spectec:826.6-826.20
  rule fun_free_comptype_case_2{resulttype_1 : list(syntax valtype), resulttype_2 : list(syntax valtype), var_1 : free, var_0 : free}:
    `%%`(`FUNC%->%`_comptype(resulttype_1, resulttype_2), var_0 +++ var_1)
    -- fun_free_resulttype: `%%`(resulttype_2, var_1)
    -- fun_free_resulttype: `%%`(resulttype_1, var_0)

;; test.spectec:827.6-827.19
relation fun_free_subtype: `%%`(subtype, free)
  ;; test.spectec:827.6-827.19
  rule fun_free_subtype_case_0{final_opt : final?, typeuse_lst : typeuse*, v_comptype : comptype, var_2 : free, var_1_lst : free*, var_0 : free}:
    `%%`(SUB_subtype(final_opt, typeuse_lst, v_comptype), var_0 +++ var_2)
    -- fun_free_comptype: `%%`(v_comptype, var_2)
    -- if (|var_1_lst| = |typeuse_lst|)
    -- (fun_free_typeuse: `%%`(v_typeuse, var_1))*{var_1 <- var_1_lst, v_typeuse <- typeuse_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:828.6-828.19
relation fun_free_rectype: `%%`(rectype, free)
  ;; test.spectec:828.6-828.19
  rule fun_free_rectype_case_0{subtype_lst : subtype*, var_1_lst : free*, var_0 : free}:
    `%%`(REC_rectype(mk_list_list(subtype_lst)), var_0)
    -- if (|var_1_lst| = |subtype_lst|)
    -- (fun_free_subtype: `%%`(v_subtype, var_1))*{var_1 <- var_1_lst, v_subtype <- subtype_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:856.6-856.19
relation fun_free_deftype: `%%`(deftype, free)
  ;; test.spectec:856.6-856.19
  rule fun_free_deftype_case_0{v_rectype : rectype, v_n : nat, var_0 : free}:
    `%%`(_DEF_deftype(v_rectype, v_n), var_0)
    -- fun_free_rectype: `%%`(v_rectype, var_0)
}

;; test.spectec:817.1-856.34
rec {

;; test.spectec:817.6-817.20
relation free_heaptype_is_wf: `%%`(v_heaptype : heaptype, ret_val : free)
  ;; test.spectec:817.6-817.20
  rule free_heaptype_is_wf_0{v_heaptype : heaptype, ret_val : free, var_0 : free}:
    `%%`(v_heaptype, ret_val)
    -- fun_free_heaptype: `%%`(v_heaptype, var_0)
    -- wf_heaptype: `%`(v_heaptype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:818.6-818.19
relation free_reftype_is_wf: `%%`(v_reftype : reftype, ret_val : free)
  ;; test.spectec:818.6-818.19
  rule free_reftype_is_wf_0{v_reftype : reftype, ret_val : free, var_0 : free}:
    `%%`(v_reftype, ret_val)
    -- fun_free_reftype: `%%`(v_reftype, var_0)
    -- wf_reftype: `%`(v_reftype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:820.6-820.19
relation free_typeuse_is_wf: `%%`(v_typeuse : typeuse, ret_val : free)
  ;; test.spectec:820.6-820.19
  rule free_typeuse_is_wf_0{v_typeuse : typeuse, ret_val : free, var_0 : free}:
    `%%`(v_typeuse, ret_val)
    -- fun_free_typeuse: `%%`(v_typeuse, var_0)
    -- wf_typeuse: `%`(v_typeuse)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:821.6-821.19
relation free_valtype_is_wf: `%%`(v_valtype : valtype, ret_val : free)
  ;; test.spectec:821.6-821.19
  rule free_valtype_is_wf_0{v_valtype : valtype, ret_val : free, var_0 : free}:
    `%%`(v_valtype, ret_val)
    -- fun_free_valtype: `%%`(v_valtype, var_0)
    -- wf_valtype: `%`(v_valtype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:823.6-823.22
relation free_resulttype_is_wf: `%%`(v_resulttype : resulttype, ret_val : free)
  ;; test.spectec:823.6-823.22
  rule free_resulttype_is_wf_0{v_resulttype : resulttype, ret_val : free, var_0 : free}:
    `%%`(v_resulttype, ret_val)
    -- fun_free_resulttype: `%%`(v_resulttype, var_0)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:824.6-824.23
relation free_storagetype_is_wf: `%%`(v_storagetype : storagetype, ret_val : free)
  ;; test.spectec:824.6-824.23
  rule free_storagetype_is_wf_0{v_storagetype : storagetype, ret_val : free, var_0 : free}:
    `%%`(v_storagetype, ret_val)
    -- fun_free_storagetype: `%%`(v_storagetype, var_0)
    -- wf_storagetype: `%`(v_storagetype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:825.6-825.21
relation free_fieldtype_is_wf: `%%`(v_fieldtype : fieldtype, ret_val : free)
  ;; test.spectec:825.6-825.21
  rule free_fieldtype_is_wf_0{v_fieldtype : fieldtype, ret_val : free, var_0 : free}:
    `%%`(v_fieldtype, ret_val)
    -- fun_free_fieldtype: `%%`(v_fieldtype, var_0)
    -- wf_fieldtype: `%`(v_fieldtype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:826.6-826.20
relation free_comptype_is_wf: `%%`(v_comptype : comptype, ret_val : free)
  ;; test.spectec:826.6-826.20
  rule free_comptype_is_wf_0{v_comptype : comptype, ret_val : free, var_0 : free}:
    `%%`(v_comptype, ret_val)
    -- fun_free_comptype: `%%`(v_comptype, var_0)
    -- wf_comptype: `%`(v_comptype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:827.6-827.19
relation free_subtype_is_wf: `%%`(v_subtype : subtype, ret_val : free)
  ;; test.spectec:827.6-827.19
  rule free_subtype_is_wf_0{v_subtype : subtype, ret_val : free, var_0 : free}:
    `%%`(v_subtype, ret_val)
    -- fun_free_subtype: `%%`(v_subtype, var_0)
    -- wf_subtype: `%`(v_subtype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:828.6-828.19
relation free_rectype_is_wf: `%%`(v_rectype : rectype, ret_val : free)
  ;; test.spectec:828.6-828.19
  rule free_rectype_is_wf_0{v_rectype : rectype, ret_val : free, var_0 : free}:
    `%%`(v_rectype, ret_val)
    -- fun_free_rectype: `%%`(v_rectype, var_0)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:856.6-856.19
relation free_deftype_is_wf: `%%`(v_deftype : deftype, ret_val : free)
  ;; test.spectec:856.6-856.19
  rule free_deftype_is_wf_0{v_deftype : deftype, ret_val : free, var_0 : free}:
    `%%`(v_deftype, ret_val)
    -- fun_free_deftype: `%%`(v_deftype, var_0)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)
}

;; test.spectec:830.6-830.19
relation fun_free_tagtype: `%%`(tagtype, free)
  ;; test.spectec:830.6-830.19
  rule fun_free_tagtype_case_0{v_rectype : rectype, v_n : n, var_0 : free}:
    `%%`(_DEF_tagtype(v_rectype, v_n), var_0)
    -- fun_free_deftype: `%%`(_DEF_deftype(v_rectype, v_n), var_0)

;; test.spectec:830.6-830.19
relation free_tagtype_is_wf: `%%`(v_tagtype : tagtype, ret_val : free)
  ;; test.spectec:830.6-830.19
  rule free_tagtype_is_wf_0{v_tagtype : tagtype, ret_val : free, var_0 : free}:
    `%%`(v_tagtype, ret_val)
    -- fun_free_tagtype: `%%`(v_tagtype, var_0)
    -- wf_typeuse: `%`(v_tagtype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:831.6-831.22
relation fun_free_globaltype: `%%`(globaltype, free)
  ;; test.spectec:831.6-831.22
  rule fun_free_globaltype_case_0{mut_opt : mut?, v_valtype : valtype, var_0 : free}:
    `%%`(mk_globaltype_globaltype(mut_opt, v_valtype), var_0)
    -- fun_free_valtype: `%%`(v_valtype, var_0)

;; test.spectec:831.6-831.22
relation free_globaltype_is_wf: `%%`(v_globaltype : globaltype, ret_val : free)
  ;; test.spectec:831.6-831.22
  rule free_globaltype_is_wf_0{v_globaltype : globaltype, ret_val : free, var_0 : free}:
    `%%`(v_globaltype, ret_val)
    -- fun_free_globaltype: `%%`(v_globaltype, var_0)
    -- wf_globaltype: `%`(v_globaltype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:832.1-832.34
def $free_memtype(v_memtype : memtype) : free
  ;; test.spectec:895.1-895.67
  def $free_memtype{v_addrtype : addrtype, v_limits : limits}(`%%PAGE`_memtype(v_addrtype, v_limits)) = $free_addrtype(v_addrtype)

;; test.spectec:832.6-832.19
relation free_memtype_is_wf: `%%`(v_memtype : memtype, ret_val : free)
  ;; test.spectec:832.6-832.19
  rule free_memtype_is_wf_0{v_memtype : memtype, ret_val : free}:
    `%%`(v_memtype, ret_val)
    -- wf_memtype: `%`(v_memtype)
    -- if (ret_val = $free_memtype(v_memtype))
    -- wf_free: `%`(ret_val)

;; test.spectec:833.6-833.21
relation fun_free_tabletype: `%%`(tabletype, free)
  ;; test.spectec:833.6-833.21
  rule fun_free_tabletype_case_0{v_addrtype : addrtype, v_limits : limits, v_reftype : reftype, var_0 : free}:
    `%%`(mk_tabletype_tabletype(v_addrtype, v_limits, v_reftype), $free_addrtype(v_addrtype) +++ var_0)
    -- fun_free_reftype: `%%`(v_reftype, var_0)

;; test.spectec:833.6-833.21
relation free_tabletype_is_wf: `%%`(v_tabletype : tabletype, ret_val : free)
  ;; test.spectec:833.6-833.21
  rule free_tabletype_is_wf_0{v_tabletype : tabletype, ret_val : free, var_0 : free}:
    `%%`(v_tabletype, ret_val)
    -- fun_free_tabletype: `%%`(v_tabletype, var_0)
    -- wf_tabletype: `%`(v_tabletype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:834.1-834.36
def $free_datatype(v_datatype : datatype) : free
  ;; test.spectec:900.1-900.28
  def $free_datatype(OK_datatype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:834.6-834.20
relation free_datatype_is_wf: `%%`(v_datatype : datatype, ret_val : free)
  ;; test.spectec:834.6-834.20
  rule free_datatype_is_wf_0{v_datatype : datatype, ret_val : free}:
    `%%`(v_datatype, ret_val)
    -- if (ret_val = $free_datatype(v_datatype))
    -- wf_free: `%`(ret_val)

;; test.spectec:835.6-835.20
relation fun_free_elemtype: `%%`(elemtype, free)
  ;; test.spectec:835.6-835.20
  rule fun_free_elemtype_case_0{v_reftype : reftype, var_0 : free}:
    `%%`(v_reftype, var_0)
    -- fun_free_reftype: `%%`(v_reftype, var_0)

;; test.spectec:835.6-835.20
relation free_elemtype_is_wf: `%%`(v_elemtype : elemtype, ret_val : free)
  ;; test.spectec:835.6-835.20
  rule free_elemtype_is_wf_0{v_elemtype : elemtype, ret_val : free, var_0 : free}:
    `%%`(v_elemtype, ret_val)
    -- fun_free_elemtype: `%%`(v_elemtype, var_0)
    -- wf_reftype: `%`(v_elemtype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:836.6-836.22
relation fun_free_externtype: `%%`(externtype, free)
  ;; test.spectec:836.6-836.22
  rule fun_free_externtype_case_0{v_tagtype : typeuse, var_0 : free}:
    `%%`(TAG_externtype(v_tagtype), var_0)
    -- fun_free_tagtype: `%%`(v_tagtype, var_0)

  ;; test.spectec:836.6-836.22
  rule fun_free_externtype_case_1{v_globaltype : globaltype, var_0 : free}:
    `%%`(GLOBAL_externtype(v_globaltype), var_0)
    -- fun_free_globaltype: `%%`(v_globaltype, var_0)

  ;; test.spectec:836.6-836.22
  rule fun_free_externtype_case_2{v_memtype : memtype}:
    `%%`(MEM_externtype(v_memtype), $free_memtype(v_memtype))

  ;; test.spectec:836.6-836.22
  rule fun_free_externtype_case_3{v_tabletype : tabletype, var_0 : free}:
    `%%`(TABLE_externtype(v_tabletype), var_0)
    -- fun_free_tabletype: `%%`(v_tabletype, var_0)

  ;; test.spectec:836.6-836.22
  rule fun_free_externtype_case_4{v_typeuse : typeuse, var_0 : free}:
    `%%`(FUNC_externtype(v_typeuse), var_0)
    -- fun_free_typeuse: `%%`(v_typeuse, var_0)

;; test.spectec:836.6-836.22
relation free_externtype_is_wf: `%%`(v_externtype : externtype, ret_val : free)
  ;; test.spectec:836.6-836.22
  rule free_externtype_is_wf_0{v_externtype : externtype, ret_val : free, var_0 : free}:
    `%%`(v_externtype, ret_val)
    -- fun_free_externtype: `%%`(v_externtype, var_0)
    -- wf_externtype: `%`(v_externtype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:837.6-837.22
relation fun_free_moduletype: `%%`(moduletype, free)
  ;; test.spectec:837.6-837.22
  rule fun_free_moduletype_case_0{externtype_1_lst : externtype*, externtype_2_lst : externtype*, var_3_lst : free*, var_2 : free, var_1_lst : free*, var_0 : free}:
    `%%`(mk_moduletype_moduletype(externtype_1_lst, externtype_2_lst), var_0 +++ var_2)
    -- if (|var_3_lst| = |externtype_2_lst|)
    -- (fun_free_externtype: `%%`(externtype_2, var_3))*{var_3 <- var_3_lst, externtype_2 <- externtype_2_lst}
    -- fun_free_list: `%%`(var_3_lst, var_2)
    -- if (|var_1_lst| = |externtype_1_lst|)
    -- (fun_free_externtype: `%%`(externtype_1, var_1))*{var_1 <- var_1_lst, externtype_1 <- externtype_1_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:837.6-837.22
relation free_moduletype_is_wf: `%%`(v_moduletype : moduletype, ret_val : free)
  ;; test.spectec:837.6-837.22
  rule free_moduletype_is_wf_0{v_moduletype : moduletype, ret_val : free, var_0 : free}:
    `%%`(v_moduletype, ret_val)
    -- fun_free_moduletype: `%%`(v_moduletype, var_0)
    -- wf_moduletype: `%`(v_moduletype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:927.1-927.21
syntax num_ = 
  | mk_num__0(v_Inn : Inn, var_x : iN)
  | mk_num__1(v_Fnn : Fnn, var_x : fN)

;; test.spectec:927.8-927.13
relation wf_num_: `%%`(numtype, num_)
  ;; test.spectec:927.8-927.13
  rule num__case_0{v_numtype : numtype, v_Inn : Inn, var_x : iN}:
    `%%`(v_numtype, mk_num__0_num_(v_Inn, var_x))
    -- wf_uN: `%%`($size($numtype_addrtype(v_Inn)), var_x)
    -- if (v_numtype = $numtype_addrtype(v_Inn))

  ;; test.spectec:927.8-927.13
  rule num__case_1{v_numtype : numtype, v_Fnn : Fnn, var_x : fN}:
    `%%`(v_numtype, mk_num__1_num_(v_Fnn, var_x))
    -- wf_fN: `%%`($sizenn($numtype_Fnn(v_Fnn)), var_x)
    -- if (v_numtype = $numtype_Fnn(v_Fnn))

;; test.spectec:927.1-927.21
def $proj_num__0(var_x : num_) : iN?
  ;; test.spectec:927.8-927.13
  def $proj_num__0{v_Inn : Inn, var_x : iN}(mk_num__0_num_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:927.8-927.13
  def $proj_num__0{var_x : num_}(var_x) = ?()

;; test.spectec:927.1-927.21
def $proj_num__1(var_x : num_) : fN?
  ;; test.spectec:927.8-927.13
  def $proj_num__1{v_Fnn : Fnn, var_x : fN}(mk_num__1_num_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:927.8-927.13
  def $proj_num__1{var_x : num_}(var_x) = ?()

;; test.spectec:931.1-931.38
syntax pack_ = iN

;; test.spectec:933.1-933.23
syntax lane_ = 
  | mk_lane__0(v_numtype : numtype, var_x : num_)
  | mk_lane__1(v_packtype : packtype, var_x : pack_)
  | mk_lane__2(v_Jnn : Jnn, var_x : iN)

;; test.spectec:933.8-933.14
relation wf_lane_: `%%`(lanetype, lane_)
  ;; test.spectec:933.8-933.14
  rule lane__case_0{v_lanetype : lanetype, v_numtype : numtype, var_x : num_}:
    `%%`(v_lanetype, mk_lane__0_lane_(v_numtype, var_x))
    -- wf_num_: `%%`(v_numtype, var_x)
    -- if (v_lanetype = $lanetype_numtype(v_numtype))

  ;; test.spectec:933.8-933.14
  rule lane__case_1{v_lanetype : lanetype, v_packtype : packtype, var_x : pack_}:
    `%%`(v_lanetype, mk_lane__1_lane_(v_packtype, var_x))
    -- wf_uN: `%%`($psize(v_packtype), var_x)
    -- if (v_lanetype = $lanetype_packtype(v_packtype))

  ;; test.spectec:933.8-933.14
  rule lane__case_2{v_lanetype : lanetype, v_Jnn : Jnn, var_x : iN}:
    `%%`(v_lanetype, mk_lane__2_lane_(v_Jnn, var_x))
    -- wf_uN: `%%`($lsize($lanetype_Jnn(v_Jnn)), var_x)
    -- if (v_lanetype = $lanetype_Jnn(v_Jnn))

;; test.spectec:933.1-933.23
def $proj_lane__0(var_x : lane_) : num_?
  ;; test.spectec:933.8-933.14
  def $proj_lane__0{v_numtype : numtype, var_x : num_}(mk_lane__0_lane_(v_numtype, var_x)) = ?(var_x)
  ;; test.spectec:933.8-933.14
  def $proj_lane__0{var_x : lane_}(var_x) = ?()

;; test.spectec:933.1-933.23
def $proj_lane__1(var_x : lane_) : pack_?
  ;; test.spectec:933.8-933.14
  def $proj_lane__1{v_packtype : packtype, var_x : pack_}(mk_lane__1_lane_(v_packtype, var_x)) = ?(var_x)
  ;; test.spectec:933.8-933.14
  def $proj_lane__1{var_x : lane_}(var_x) = ?()

;; test.spectec:933.1-933.23
def $proj_lane__2(var_x : lane_) : iN?
  ;; test.spectec:933.8-933.14
  def $proj_lane__2{v_Jnn : Jnn, var_x : iN}(mk_lane__2_lane_(v_Jnn, var_x)) = ?(var_x)
  ;; test.spectec:933.8-933.14
  def $proj_lane__2{var_x : lane_}(var_x) = ?()

;; test.spectec:938.1-938.35
syntax vec_ = vN

;; test.spectec:940.1-940.25
syntax lit_ = 
  | mk_lit__0(v_numtype : numtype, var_x : num_)
  | mk_lit__1(v_vectype : vectype, var_x : vec_)
  | mk_lit__2(v_packtype : packtype, var_x : pack_)

;; test.spectec:940.8-940.13
relation wf_lit_: `%%`(storagetype, lit_)
  ;; test.spectec:940.8-940.13
  rule lit__case_0{v_storagetype : storagetype, v_numtype : numtype, var_x : num_}:
    `%%`(v_storagetype, mk_lit__0_lit_(v_numtype, var_x))
    -- wf_num_: `%%`(v_numtype, var_x)
    -- if (v_storagetype = $storagetype_numtype(v_numtype))

  ;; test.spectec:940.8-940.13
  rule lit__case_1{v_storagetype : storagetype, v_vectype : vectype, var_x : vec_}:
    `%%`(v_storagetype, mk_lit__1_lit_(v_vectype, var_x))
    -- wf_uN: `%%`($vsize(v_vectype), var_x)
    -- if (v_storagetype = $storagetype_vectype(v_vectype))

  ;; test.spectec:940.8-940.13
  rule lit__case_2{v_storagetype : storagetype, v_packtype : packtype, var_x : pack_}:
    `%%`(v_storagetype, mk_lit__2_lit_(v_packtype, var_x))
    -- wf_uN: `%%`($psize(v_packtype), var_x)
    -- if (v_storagetype = $storagetype_packtype(v_packtype))

;; test.spectec:940.1-940.25
def $proj_lit__0(var_x : lit_) : num_?
  ;; test.spectec:940.8-940.13
  def $proj_lit__0{v_numtype : numtype, var_x : num_}(mk_lit__0_lit_(v_numtype, var_x)) = ?(var_x)
  ;; test.spectec:940.8-940.13
  def $proj_lit__0{var_x : lit_}(var_x) = ?()

;; test.spectec:940.1-940.25
def $proj_lit__1(var_x : lit_) : vec_?
  ;; test.spectec:940.8-940.13
  def $proj_lit__1{v_vectype : vectype, var_x : vec_}(mk_lit__1_lit_(v_vectype, var_x)) = ?(var_x)
  ;; test.spectec:940.8-940.13
  def $proj_lit__1{var_x : lit_}(var_x) = ?()

;; test.spectec:940.1-940.25
def $proj_lit__2(var_x : lit_) : pack_?
  ;; test.spectec:940.8-940.13
  def $proj_lit__2{v_packtype : packtype, var_x : pack_}(mk_lit__2_lit_(v_packtype, var_x)) = ?(var_x)
  ;; test.spectec:940.8-940.13
  def $proj_lit__2{var_x : lit_}(var_x) = ?()

;; test.spectec:948.1-948.56
syntax sz = 
  | mk_sz(i : nat)

;; test.spectec:948.1-948.56
def $proj_sz_0(x : sz) : (nat)
  ;; test.spectec:948.1-948.56
  def $proj_sz_0{v_num_0 : nat}(mk_sz_sz(v_num_0)) = (v_num_0)

;; test.spectec:948.8-948.10
relation wf_sz: `%`(sz)
  ;; test.spectec:948.8-948.10
  rule sz_case_0{i : nat}:
    `%`(mk_sz_sz(i))
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
  | EXTEND(v_sz : sz)

;; test.spectec:951.8-951.14
relation wf_unop_Inn: `%%`(Inn, unop_Inn)
  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_0{v_Inn : Inn}:
    `%%`(v_Inn, CLZ_unop_Inn)

  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_1{v_Inn : Inn}:
    `%%`(v_Inn, CTZ_unop_Inn)

  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_2{v_Inn : Inn}:
    `%%`(v_Inn, POPCNT_unop_Inn)

  ;; test.spectec:951.8-951.14
  rule unop_Inn_case_3{v_Inn : Inn, v_sz : sz}:
    `%%`(v_Inn, EXTEND_unop_Inn(v_sz))
    -- wf_sz: `%`(v_sz)
    -- if ($proj_sz_0(v_sz).0 < $sizenn($numtype_addrtype(v_Inn)))

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
  | mk_unop__0(v_Inn : Inn, var_x : unop_Inn)
  | mk_unop__1(v_Fnn : Fnn, var_x : unop_Fnn)

;; test.spectec:951.8-951.14
relation wf_unop_: `%%`(numtype, unop_)
  ;; test.spectec:951.8-951.14
  rule unop__case_0{v_numtype : numtype, v_Inn : Inn, var_x : unop_Inn}:
    `%%`(v_numtype, mk_unop__0_unop_(v_Inn, var_x))
    -- wf_unop_Inn: `%%`(v_Inn, var_x)
    -- if (v_numtype = $numtype_addrtype(v_Inn))

  ;; test.spectec:951.8-951.14
  rule unop__case_1{v_numtype : numtype, v_Fnn : Fnn, var_x : unop_Fnn}:
    `%%`(v_numtype, mk_unop__1_unop_(v_Fnn, var_x))
    -- if (v_numtype = $numtype_Fnn(v_Fnn))

;; test.spectec:951.1-951.22
def $proj_unop__0(var_x : unop_) : unop_Inn?
  ;; test.spectec:951.8-951.14
  def $proj_unop__0{v_Inn : Inn, var_x : unop_Inn}(mk_unop__0_unop_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:951.8-951.14
  def $proj_unop__0{var_x : unop_}(var_x) = ?()

;; test.spectec:951.1-951.22
def $proj_unop__1(var_x : unop_) : unop_Fnn?
  ;; test.spectec:951.8-951.14
  def $proj_unop__1{v_Fnn : Fnn, var_x : unop_Fnn}(mk_unop__1_unop_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:951.8-951.14
  def $proj_unop__1{var_x : unop_}(var_x) = ?()

;; test.spectec:955.1-955.23
syntax binop_Inn = 
  | ADD
  | SUB
  | MUL
  | DIV(v_sx : sx)
  | REM(v_sx : sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHR(v_sx : sx)
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
  | mk_binop__0(v_Inn : Inn, var_x : binop_Inn)
  | mk_binop__1(v_Fnn : Fnn, var_x : binop_Fnn)

;; test.spectec:955.8-955.15
relation wf_binop_: `%%`(numtype, binop_)
  ;; test.spectec:955.8-955.15
  rule binop__case_0{v_numtype : numtype, v_Inn : Inn, var_x : binop_Inn}:
    `%%`(v_numtype, mk_binop__0_binop_(v_Inn, var_x))
    -- if (v_numtype = $numtype_addrtype(v_Inn))

  ;; test.spectec:955.8-955.15
  rule binop__case_1{v_numtype : numtype, v_Fnn : Fnn, var_x : binop_Fnn}:
    `%%`(v_numtype, mk_binop__1_binop_(v_Fnn, var_x))
    -- if (v_numtype = $numtype_Fnn(v_Fnn))

;; test.spectec:955.1-955.23
def $proj_binop__0(var_x : binop_) : binop_Inn?
  ;; test.spectec:955.8-955.15
  def $proj_binop__0{v_Inn : Inn, var_x : binop_Inn}(mk_binop__0_binop_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:955.8-955.15
  def $proj_binop__0{var_x : binop_}(var_x) = ?()

;; test.spectec:955.1-955.23
def $proj_binop__1(var_x : binop_) : binop_Fnn?
  ;; test.spectec:955.8-955.15
  def $proj_binop__1{v_Fnn : Fnn, var_x : binop_Fnn}(mk_binop__1_binop_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:955.8-955.15
  def $proj_binop__1{var_x : binop_}(var_x) = ?()

;; test.spectec:962.1-962.24
syntax testop_Inn = 
  | EQZ

;; test.spectec:962.1-962.24
syntax testop_ = 
  | mk_testop__0(v_Inn : Inn, var_x : testop_Inn)

;; test.spectec:962.8-962.16
relation wf_testop_: `%%`(numtype, testop_)
  ;; test.spectec:962.8-962.16
  rule testop__case_0{v_numtype : numtype, v_Inn : Inn, var_x : testop_Inn}:
    `%%`(v_numtype, mk_testop__0_testop_(v_Inn, var_x))
    -- if (v_numtype = $numtype_addrtype(v_Inn))

;; test.spectec:962.1-962.24
def $proj_testop__0(var_x : testop_) : testop_Inn
  ;; test.spectec:962.8-962.16
  def $proj_testop__0{v_Inn : Inn, var_x : testop_Inn}(mk_testop__0_testop_(v_Inn, var_x)) = var_x

;; test.spectec:966.1-966.23
syntax relop_Inn = 
  | EQ
  | NE
  | LT(v_sx : sx)
  | GT(v_sx : sx)
  | LE(v_sx : sx)
  | GE(v_sx : sx)

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
  | mk_relop__0(v_Inn : Inn, var_x : relop_Inn)
  | mk_relop__1(v_Fnn : Fnn, var_x : relop_Fnn)

;; test.spectec:966.8-966.15
relation wf_relop_: `%%`(numtype, relop_)
  ;; test.spectec:966.8-966.15
  rule relop__case_0{v_numtype : numtype, v_Inn : Inn, var_x : relop_Inn}:
    `%%`(v_numtype, mk_relop__0_relop_(v_Inn, var_x))
    -- if (v_numtype = $numtype_addrtype(v_Inn))

  ;; test.spectec:966.8-966.15
  rule relop__case_1{v_numtype : numtype, v_Fnn : Fnn, var_x : relop_Fnn}:
    `%%`(v_numtype, mk_relop__1_relop_(v_Fnn, var_x))
    -- if (v_numtype = $numtype_Fnn(v_Fnn))

;; test.spectec:966.1-966.23
def $proj_relop__0(var_x : relop_) : relop_Inn?
  ;; test.spectec:966.8-966.15
  def $proj_relop__0{v_Inn : Inn, var_x : relop_Inn}(mk_relop__0_relop_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:966.8-966.15
  def $proj_relop__0{var_x : relop_}(var_x) = ?()

;; test.spectec:966.1-966.23
def $proj_relop__1(var_x : relop_) : relop_Fnn?
  ;; test.spectec:966.8-966.15
  def $proj_relop__1{v_Fnn : Fnn, var_x : relop_Fnn}(mk_relop__1_relop_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:966.8-966.15
  def $proj_relop__1{var_x : relop_}(var_x) = ?()

;; test.spectec:975.1-975.37
syntax cvtop__Inn_1_Inn_2 = 
  | EXTEND(v_sx : sx)
  | WRAP

;; test.spectec:975.8-975.16
relation wf_cvtop__Inn_1_Inn_2: `%%%`(Inn, Inn, cvtop__Inn_1_Inn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Inn_2_case_0{Inn_1 : Inn, Inn_2 : Inn, v_sx : sx}:
    `%%%`(Inn_1, Inn_2, EXTEND_cvtop__Inn_1_Inn_2(v_sx))
    -- if ($sizenn1($numtype_addrtype(Inn_1)) < $sizenn2($numtype_addrtype(Inn_2)))

  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Inn_2_case_1{Inn_1 : Inn, Inn_2 : Inn}:
    `%%%`(Inn_1, Inn_2, WRAP_cvtop__Inn_1_Inn_2)
    -- if ($sizenn1($numtype_addrtype(Inn_1)) > $sizenn2($numtype_addrtype(Inn_2)))

;; test.spectec:975.1-975.37
syntax cvtop__Inn_1_Fnn_2 = 
  | CONVERT(v_sx : sx)
  | REINTERPRET

;; test.spectec:975.8-975.16
relation wf_cvtop__Inn_1_Fnn_2: `%%%`(Inn, Fnn, cvtop__Inn_1_Fnn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Fnn_2_case_0{Inn_1 : Inn, Fnn_2 : Fnn, v_sx : sx}:
    `%%%`(Inn_1, Fnn_2, CONVERT_cvtop__Inn_1_Fnn_2(v_sx))

  ;; test.spectec:975.8-975.16
  rule cvtop__Inn_1_Fnn_2_case_1{Inn_1 : Inn, Fnn_2 : Fnn}:
    `%%%`(Inn_1, Fnn_2, REINTERPRET_cvtop__Inn_1_Fnn_2)
    -- if ($sizenn1($numtype_addrtype(Inn_1)) = $sizenn2($numtype_Fnn(Fnn_2)))

;; test.spectec:975.1-975.37
syntax cvtop__Fnn_1_Inn_2 = 
  | TRUNC(v_sx : sx)
  | TRUNC_SAT(v_sx : sx)
  | REINTERPRET

;; test.spectec:975.8-975.16
relation wf_cvtop__Fnn_1_Inn_2: `%%%`(Fnn, Inn, cvtop__Fnn_1_Inn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Inn_2_case_0{Fnn_1 : Fnn, Inn_2 : Inn, v_sx : sx}:
    `%%%`(Fnn_1, Inn_2, TRUNC_cvtop__Fnn_1_Inn_2(v_sx))

  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Inn_2_case_1{Fnn_1 : Fnn, Inn_2 : Inn, v_sx : sx}:
    `%%%`(Fnn_1, Inn_2, TRUNC_SAT_cvtop__Fnn_1_Inn_2(v_sx))

  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Inn_2_case_2{Fnn_1 : Fnn, Inn_2 : Inn}:
    `%%%`(Fnn_1, Inn_2, REINTERPRET_cvtop__Fnn_1_Inn_2)
    -- if ($sizenn1($numtype_Fnn(Fnn_1)) = $sizenn2($numtype_addrtype(Inn_2)))

;; test.spectec:975.1-975.37
syntax cvtop__Fnn_1_Fnn_2 = 
  | PROMOTE
  | DEMOTE

;; test.spectec:975.8-975.16
relation wf_cvtop__Fnn_1_Fnn_2: `%%%`(Fnn, Fnn, cvtop__Fnn_1_Fnn_2)
  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Fnn_2_case_0{Fnn_1 : Fnn, Fnn_2 : Fnn}:
    `%%%`(Fnn_1, Fnn_2, PROMOTE_cvtop__Fnn_1_Fnn_2)
    -- if ($sizenn1($numtype_Fnn(Fnn_1)) < $sizenn2($numtype_Fnn(Fnn_2)))

  ;; test.spectec:975.8-975.16
  rule cvtop__Fnn_1_Fnn_2_case_1{Fnn_1 : Fnn, Fnn_2 : Fnn}:
    `%%%`(Fnn_1, Fnn_2, DEMOTE_cvtop__Fnn_1_Fnn_2)
    -- if ($sizenn1($numtype_Fnn(Fnn_1)) > $sizenn2($numtype_Fnn(Fnn_2)))

;; test.spectec:975.1-975.37
syntax cvtop__ = 
  | mk_cvtop___0(Inn_1 : Inn, Inn_2 : Inn, var_x : cvtop__Inn_1_Inn_2)
  | mk_cvtop___1(Inn_1 : Inn, Fnn_2 : Fnn, var_x : cvtop__Inn_1_Fnn_2)
  | mk_cvtop___2(Fnn_1 : Fnn, Inn_2 : Inn, var_x : cvtop__Fnn_1_Inn_2)
  | mk_cvtop___3(Fnn_1 : Fnn, Fnn_2 : Fnn, var_x : cvtop__Fnn_1_Fnn_2)

;; test.spectec:975.8-975.16
relation wf_cvtop__: `%%%`(numtype, numtype, cvtop__)
  ;; test.spectec:975.8-975.16
  rule cvtop___case_0{numtype_1 : numtype, numtype_2 : numtype, Inn_1 : Inn, Inn_2 : Inn, var_x : cvtop__Inn_1_Inn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___0_cvtop__(Inn_1, Inn_2, var_x))
    -- wf_cvtop__Inn_1_Inn_2: `%%%`(Inn_1, Inn_2, var_x)
    -- if (numtype_1 = $numtype_addrtype(Inn_1))
    -- if (numtype_2 = $numtype_addrtype(Inn_2))

  ;; test.spectec:975.8-975.16
  rule cvtop___case_1{numtype_1 : numtype, numtype_2 : numtype, Inn_1 : Inn, Fnn_2 : Fnn, var_x : cvtop__Inn_1_Fnn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___1_cvtop__(Inn_1, Fnn_2, var_x))
    -- wf_cvtop__Inn_1_Fnn_2: `%%%`(Inn_1, Fnn_2, var_x)
    -- if (numtype_1 = $numtype_addrtype(Inn_1))
    -- if (numtype_2 = $numtype_Fnn(Fnn_2))

  ;; test.spectec:975.8-975.16
  rule cvtop___case_2{numtype_1 : numtype, numtype_2 : numtype, Fnn_1 : Fnn, Inn_2 : Inn, var_x : cvtop__Fnn_1_Inn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___2_cvtop__(Fnn_1, Inn_2, var_x))
    -- wf_cvtop__Fnn_1_Inn_2: `%%%`(Fnn_1, Inn_2, var_x)
    -- if (numtype_1 = $numtype_Fnn(Fnn_1))
    -- if (numtype_2 = $numtype_addrtype(Inn_2))

  ;; test.spectec:975.8-975.16
  rule cvtop___case_3{numtype_1 : numtype, numtype_2 : numtype, Fnn_1 : Fnn, Fnn_2 : Fnn, var_x : cvtop__Fnn_1_Fnn_2}:
    `%%%`(numtype_1, numtype_2, mk_cvtop___3_cvtop__(Fnn_1, Fnn_2, var_x))
    -- wf_cvtop__Fnn_1_Fnn_2: `%%%`(Fnn_1, Fnn_2, var_x)
    -- if (numtype_1 = $numtype_Fnn(Fnn_1))
    -- if (numtype_2 = $numtype_Fnn(Fnn_2))

;; test.spectec:975.1-975.37
def $proj_cvtop___0(var_x : cvtop__) : cvtop__Inn_1_Inn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___0{Inn_1 : Inn, Inn_2 : Inn, var_x : cvtop__Inn_1_Inn_2}(mk_cvtop___0_cvtop__(Inn_1, Inn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___0{var_x : cvtop__}(var_x) = ?()

;; test.spectec:975.1-975.37
def $proj_cvtop___1(var_x : cvtop__) : cvtop__Inn_1_Fnn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___1{Inn_1 : Inn, Fnn_2 : Fnn, var_x : cvtop__Inn_1_Fnn_2}(mk_cvtop___1_cvtop__(Inn_1, Fnn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___1{var_x : cvtop__}(var_x) = ?()

;; test.spectec:975.1-975.37
def $proj_cvtop___2(var_x : cvtop__) : cvtop__Fnn_1_Inn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___2{Fnn_1 : Fnn, Inn_2 : Inn, var_x : cvtop__Fnn_1_Inn_2}(mk_cvtop___2_cvtop__(Fnn_1, Inn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___2{var_x : cvtop__}(var_x) = ?()

;; test.spectec:975.1-975.37
def $proj_cvtop___3(var_x : cvtop__) : cvtop__Fnn_1_Fnn_2?
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___3{Fnn_1 : Fnn, Fnn_2 : Fnn, var_x : cvtop__Fnn_1_Fnn_2}(mk_cvtop___3_cvtop__(Fnn_1, Fnn_2, var_x)) = ?(var_x)
  ;; test.spectec:975.8-975.16
  def $proj_cvtop___3{var_x : cvtop__}(var_x) = ?()

;; test.spectec:993.1-993.60
syntax dim = 
  | mk_dim(i : nat)

;; test.spectec:993.1-993.60
def $proj_dim_0(x : dim) : (nat)
  ;; test.spectec:993.1-993.60
  def $proj_dim_0{v_num_0 : nat}(mk_dim_dim(v_num_0)) = (v_num_0)

;; test.spectec:993.8-993.11
relation wf_dim: `%`(dim)
  ;; test.spectec:993.8-993.11
  rule dim_case_0{i : nat}:
    `%`(mk_dim_dim(i))
    -- if (((((i = 1) \/ (i = 2)) \/ (i = 4)) \/ (i = 8)) \/ (i = 16))

;; test.spectec:994.1-995.40
syntax shape = 
  | `%X%`(v_lanetype : lanetype, v_dim : dim)

;; test.spectec:994.8-994.13
relation wf_shape: `%`(shape)
  ;; test.spectec:994.8-994.13
  rule shape_case_0{v_lanetype : lanetype, v_dim : dim}:
    `%`(`%X%`_shape(v_lanetype, v_dim))
    -- wf_dim: `%`(v_dim)
    -- if (($lsize(v_lanetype) * $proj_dim_0(v_dim).0) = 128)

;; test.spectec:998.1-998.43
def $fun_dim(v_shape : shape) : dim
  ;; test.spectec:999.1-999.22
  def $fun_dim{v_Lnn : lanetype, v_N : nat}(`%X%`_shape(v_Lnn, mk_dim_dim(v_N))) = mk_dim_dim(v_N)

;; test.spectec:998.6-998.10
relation dim_is_wf: `%%`(v_shape : shape, ret_val : dim)
  ;; test.spectec:998.6-998.10
  rule dim_is_wf_0{v_shape : shape, ret_val : dim}:
    `%%`(v_shape, ret_val)
    -- wf_shape: `%`(v_shape)
    -- if (ret_val = $fun_dim(v_shape))
    -- wf_dim: `%`(ret_val)

;; test.spectec:1001.1-1001.58
def $fun_lanetype(v_shape : shape) : lanetype
  ;; test.spectec:1002.1-1002.29
  def $fun_lanetype{v_Lnn : lanetype, v_N : nat}(`%X%`_shape(v_Lnn, mk_dim_dim(v_N))) = v_Lnn

;; test.spectec:1004.1-1004.57
def $unpackshape(v_shape : shape) : numtype
  ;; test.spectec:1005.1-1005.42
  def $unpackshape{v_Lnn : lanetype, v_N : nat}(`%X%`_shape(v_Lnn, mk_dim_dim(v_N))) = $lunpack(v_Lnn)

;; test.spectec:1008.1-1008.78
syntax ishape = 
  | mk_ishape(v_shape : shape)

;; test.spectec:1008.1-1008.78
def $proj_ishape_0(x : ishape) : (shape)
  ;; test.spectec:1008.1-1008.78
  def $proj_ishape_0{v_shape_0 : shape}(mk_ishape_ishape(v_shape_0)) = (v_shape_0)

;; test.spectec:1008.8-1008.14
relation wf_ishape: `%`(ishape)
  ;; test.spectec:1008.8-1008.14
  rule ishape_case_0{v_Jnn : Jnn, v_shape : shape}:
    `%`(mk_ishape_ishape(v_shape))
    -- wf_shape: `%`(v_shape)
    -- if ($fun_lanetype(v_shape) = $lanetype_Jnn(v_Jnn))

;; test.spectec:1009.1-1009.77
syntax bshape = 
  | mk_bshape(v_shape : shape)

;; test.spectec:1009.1-1009.77
def $proj_bshape_0(x : bshape) : (shape)
  ;; test.spectec:1009.1-1009.77
  def $proj_bshape_0{v_shape_0 : shape}(mk_bshape_bshape(v_shape_0)) = (v_shape_0)

;; test.spectec:1009.8-1009.14
relation wf_bshape: `%`(bshape)
  ;; test.spectec:1009.8-1009.14
  rule bshape_case_0{v_shape : shape}:
    `%`(mk_bshape_bshape(v_shape))
    -- wf_shape: `%`(v_shape)
    -- if ($fun_lanetype(v_shape) = I8_lanetype)

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
relation wf_vunop_Jnn_M: `%%%`(Jnn, M, vunop_Jnn_M)
  ;; test.spectec:1022.8-1022.15
  rule vunop_Jnn_M_case_0{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, ABS_vunop_Jnn_M)

  ;; test.spectec:1022.8-1022.15
  rule vunop_Jnn_M_case_1{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, NEG_vunop_Jnn_M)

  ;; test.spectec:1022.8-1022.15
  rule vunop_Jnn_M_case_2{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, POPCNT_vunop_Jnn_M)
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) = 8)

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
  | mk_vunop__0(v_Jnn : Jnn, v_M : M, var_x : vunop_Jnn_M)
  | mk_vunop__1(v_Fnn : Fnn, v_M : M, var_x : vunop_Fnn_M)

;; test.spectec:1022.8-1022.15
relation wf_vunop_: `%%`(shape, vunop_)
  ;; test.spectec:1022.8-1022.15
  rule vunop__case_0{v_shape : shape, v_Jnn : Jnn, v_M : M, var_x : vunop_Jnn_M}:
    `%%`(v_shape, mk_vunop__0_vunop_(v_Jnn, v_M, var_x))
    -- wf_vunop_Jnn_M: `%%%`(v_Jnn, v_M, var_x)
    -- if (v_shape = `%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M)))

  ;; test.spectec:1022.8-1022.15
  rule vunop__case_1{v_shape : shape, v_Fnn : Fnn, v_M : M, var_x : vunop_Fnn_M}:
    `%%`(v_shape, mk_vunop__1_vunop_(v_Fnn, v_M, var_x))
    -- if (v_shape = `%X%`_shape($lanetype_Fnn(v_Fnn), mk_dim_dim(v_M)))

;; test.spectec:1022.1-1022.42
def $proj_vunop__0(var_x : vunop_) : vunop_Jnn_M?
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__0{v_Jnn : Jnn, v_M : M, var_x : vunop_Jnn_M}(mk_vunop__0_vunop_(v_Jnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__0{var_x : vunop_}(var_x) = ?()

;; test.spectec:1022.1-1022.42
def $proj_vunop__1(var_x : vunop_) : vunop_Fnn_M?
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__1{v_Fnn : Fnn, v_M : M, var_x : vunop_Fnn_M}(mk_vunop__1_vunop_(v_Fnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1022.8-1022.15
  def $proj_vunop__1{var_x : vunop_}(var_x) = ?()

;; test.spectec:1028.1-1028.43
syntax vbinop_Jnn_M = 
  | ADD
  | SUB
  | ADD_SAT(v_sx : sx)
  | SUB_SAT(v_sx : sx)
  | MUL
  | AVGRU
  | Q15MULR_SATS
  | RELAXED_Q15MULRS
  | MIN(v_sx : sx)
  | MAX(v_sx : sx)

;; test.spectec:1028.8-1028.16
relation wf_vbinop_Jnn_M: `%%%`(Jnn, M, vbinop_Jnn_M)
  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_0{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, ADD_vbinop_Jnn_M)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_1{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, SUB_vbinop_Jnn_M)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_2{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, ADD_SAT_vbinop_Jnn_M(v_sx))
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) <= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_3{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, SUB_SAT_vbinop_Jnn_M(v_sx))
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) <= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_4{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, MUL_vbinop_Jnn_M)
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) >= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_5{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, AVGRU_vbinop_Jnn_M)
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) <= 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_6{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, Q15MULR_SATS_vbinop_Jnn_M)
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) = 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_7{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, RELAXED_Q15MULRS_vbinop_Jnn_M)
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) = 16)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_8{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, MIN_vbinop_Jnn_M(v_sx))
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) <= 32)

  ;; test.spectec:1028.8-1028.16
  rule vbinop_Jnn_M_case_9{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, MAX_vbinop_Jnn_M(v_sx))
    -- if ($lsizenn($lanetype_Jnn(v_Jnn)) <= 32)

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
  | mk_vbinop__0(v_Jnn : Jnn, v_M : M, var_x : vbinop_Jnn_M)
  | mk_vbinop__1(v_Fnn : Fnn, v_M : M, var_x : vbinop_Fnn_M)

;; test.spectec:1028.8-1028.16
relation wf_vbinop_: `%%`(shape, vbinop_)
  ;; test.spectec:1028.8-1028.16
  rule vbinop__case_0{v_shape : shape, v_Jnn : Jnn, v_M : M, var_x : vbinop_Jnn_M}:
    `%%`(v_shape, mk_vbinop__0_vbinop_(v_Jnn, v_M, var_x))
    -- wf_vbinop_Jnn_M: `%%%`(v_Jnn, v_M, var_x)
    -- if (v_shape = `%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M)))

  ;; test.spectec:1028.8-1028.16
  rule vbinop__case_1{v_shape : shape, v_Fnn : Fnn, v_M : M, var_x : vbinop_Fnn_M}:
    `%%`(v_shape, mk_vbinop__1_vbinop_(v_Fnn, v_M, var_x))
    -- if (v_shape = `%X%`_shape($lanetype_Fnn(v_Fnn), mk_dim_dim(v_M)))

;; test.spectec:1028.1-1028.43
def $proj_vbinop__0(var_x : vbinop_) : vbinop_Jnn_M?
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__0{v_Jnn : Jnn, v_M : M, var_x : vbinop_Jnn_M}(mk_vbinop__0_vbinop_(v_Jnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__0{var_x : vbinop_}(var_x) = ?()

;; test.spectec:1028.1-1028.43
def $proj_vbinop__1(var_x : vbinop_) : vbinop_Fnn_M?
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__1{v_Fnn : Fnn, v_M : M, var_x : vbinop_Fnn_M}(mk_vbinop__1_vbinop_(v_Fnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1028.8-1028.16
  def $proj_vbinop__1{var_x : vbinop_}(var_x) = ?()

;; test.spectec:1044.1-1044.44
syntax vternop_Jnn_M = 
  | RELAXED_LANESELECT

;; test.spectec:1044.1-1044.44
syntax vternop_Fnn_M = 
  | RELAXED_MADD
  | RELAXED_NMADD

;; test.spectec:1044.1-1044.44
syntax vternop_ = 
  | mk_vternop__0(v_Jnn : Jnn, v_M : M, var_x : vternop_Jnn_M)
  | mk_vternop__1(v_Fnn : Fnn, v_M : M, var_x : vternop_Fnn_M)

;; test.spectec:1044.8-1044.17
relation wf_vternop_: `%%`(shape, vternop_)
  ;; test.spectec:1044.8-1044.17
  rule vternop__case_0{v_shape : shape, v_Jnn : Jnn, v_M : M, var_x : vternop_Jnn_M}:
    `%%`(v_shape, mk_vternop__0_vternop_(v_Jnn, v_M, var_x))
    -- if (v_shape = `%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M)))

  ;; test.spectec:1044.8-1044.17
  rule vternop__case_1{v_shape : shape, v_Fnn : Fnn, v_M : M, var_x : vternop_Fnn_M}:
    `%%`(v_shape, mk_vternop__1_vternop_(v_Fnn, v_M, var_x))
    -- if (v_shape = `%X%`_shape($lanetype_Fnn(v_Fnn), mk_dim_dim(v_M)))

;; test.spectec:1044.1-1044.44
def $proj_vternop__0(var_x : vternop_) : vternop_Jnn_M?
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__0{v_Jnn : Jnn, v_M : M, var_x : vternop_Jnn_M}(mk_vternop__0_vternop_(v_Jnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__0{var_x : vternop_}(var_x) = ?()

;; test.spectec:1044.1-1044.44
def $proj_vternop__1(var_x : vternop_) : vternop_Fnn_M?
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__1{v_Fnn : Fnn, v_M : M, var_x : vternop_Fnn_M}(mk_vternop__1_vternop_(v_Fnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1044.8-1044.17
  def $proj_vternop__1{var_x : vternop_}(var_x) = ?()

;; test.spectec:1048.1-1048.44
syntax vtestop_Jnn_M = 
  | ALL_TRUE

;; test.spectec:1048.1-1048.44
syntax vtestop_ = 
  | mk_vtestop__0(v_Jnn : Jnn, v_M : M, var_x : vtestop_Jnn_M)

;; test.spectec:1048.8-1048.17
relation wf_vtestop_: `%%`(shape, vtestop_)
  ;; test.spectec:1048.8-1048.17
  rule vtestop__case_0{v_shape : shape, v_Jnn : Jnn, v_M : M, var_x : vtestop_Jnn_M}:
    `%%`(v_shape, mk_vtestop__0_vtestop_(v_Jnn, v_M, var_x))
    -- if (v_shape = `%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M)))

;; test.spectec:1048.1-1048.44
def $proj_vtestop__0(var_x : vtestop_) : vtestop_Jnn_M
  ;; test.spectec:1048.8-1048.17
  def $proj_vtestop__0{v_Jnn : Jnn, v_M : M, var_x : vtestop_Jnn_M}(mk_vtestop__0_vtestop_(v_Jnn, v_M, var_x)) = var_x

;; test.spectec:1052.1-1052.43
syntax vrelop_Jnn_M = 
  | EQ
  | NE
  | LT(v_sx : sx)
  | GT(v_sx : sx)
  | LE(v_sx : sx)
  | GE(v_sx : sx)

;; test.spectec:1052.8-1052.16
relation wf_vrelop_Jnn_M: `%%%`(Jnn, M, vrelop_Jnn_M)
  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_0{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, EQ_vrelop_Jnn_M)

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_1{v_Jnn : Jnn, v_M : M}:
    `%%%`(v_Jnn, v_M, NE_vrelop_Jnn_M)

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_2{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, LT_vrelop_Jnn_M(v_sx))
    -- if (($lsizenn($lanetype_Jnn(v_Jnn)) =/= 64) \/ (v_sx = S_sx))

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_3{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, GT_vrelop_Jnn_M(v_sx))
    -- if (($lsizenn($lanetype_Jnn(v_Jnn)) =/= 64) \/ (v_sx = S_sx))

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_4{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, LE_vrelop_Jnn_M(v_sx))
    -- if (($lsizenn($lanetype_Jnn(v_Jnn)) =/= 64) \/ (v_sx = S_sx))

  ;; test.spectec:1052.8-1052.16
  rule vrelop_Jnn_M_case_5{v_Jnn : Jnn, v_M : M, v_sx : sx}:
    `%%%`(v_Jnn, v_M, GE_vrelop_Jnn_M(v_sx))
    -- if (($lsizenn($lanetype_Jnn(v_Jnn)) =/= 64) \/ (v_sx = S_sx))

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
  | mk_vrelop__0(v_Jnn : Jnn, v_M : M, var_x : vrelop_Jnn_M)
  | mk_vrelop__1(v_Fnn : Fnn, v_M : M, var_x : vrelop_Fnn_M)

;; test.spectec:1052.8-1052.16
relation wf_vrelop_: `%%`(shape, vrelop_)
  ;; test.spectec:1052.8-1052.16
  rule vrelop__case_0{v_shape : shape, v_Jnn : Jnn, v_M : M, var_x : vrelop_Jnn_M}:
    `%%`(v_shape, mk_vrelop__0_vrelop_(v_Jnn, v_M, var_x))
    -- wf_vrelop_Jnn_M: `%%%`(v_Jnn, v_M, var_x)
    -- if (v_shape = `%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M)))

  ;; test.spectec:1052.8-1052.16
  rule vrelop__case_1{v_shape : shape, v_Fnn : Fnn, v_M : M, var_x : vrelop_Fnn_M}:
    `%%`(v_shape, mk_vrelop__1_vrelop_(v_Fnn, v_M, var_x))
    -- if (v_shape = `%X%`_shape($lanetype_Fnn(v_Fnn), mk_dim_dim(v_M)))

;; test.spectec:1052.1-1052.43
def $proj_vrelop__0(var_x : vrelop_) : vrelop_Jnn_M?
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__0{v_Jnn : Jnn, v_M : M, var_x : vrelop_Jnn_M}(mk_vrelop__0_vrelop_(v_Jnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__0{var_x : vrelop_}(var_x) = ?()

;; test.spectec:1052.1-1052.43
def $proj_vrelop__1(var_x : vrelop_) : vrelop_Fnn_M?
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__1{v_Fnn : Fnn, v_M : M, var_x : vrelop_Fnn_M}(mk_vrelop__1_vrelop_(v_Fnn, v_M, var_x)) = ?(var_x)
  ;; test.spectec:1052.8-1052.16
  def $proj_vrelop__1{var_x : vrelop_}(var_x) = ?()

;; test.spectec:1060.1-1060.46
syntax vshiftop_Jnn_M = 
  | SHL
  | SHR(v_sx : sx)

;; test.spectec:1060.1-1060.46
syntax vshiftop_ = 
  | mk_vshiftop__0(v_Jnn : Jnn, v_M : M, var_x : vshiftop_Jnn_M)

;; test.spectec:1060.8-1060.18
relation wf_vshiftop_: `%%`(ishape, vshiftop_)
  ;; test.spectec:1060.8-1060.18
  rule vshiftop__case_0{v_ishape : ishape, v_Jnn : Jnn, v_M : M, var_x : vshiftop_Jnn_M}:
    `%%`(v_ishape, mk_vshiftop__0_vshiftop_(v_Jnn, v_M, var_x))
    -- if (v_ishape = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))

;; test.spectec:1060.1-1060.46
def $proj_vshiftop__0(var_x : vshiftop_) : vshiftop_Jnn_M
  ;; test.spectec:1060.8-1060.18
  def $proj_vshiftop__0{v_Jnn : Jnn, v_M : M, var_x : vshiftop_Jnn_M}(mk_vshiftop__0_vshiftop_(v_Jnn, v_M, var_x)) = var_x

;; test.spectec:1063.1-1063.47
syntax vswizzlop_M = 
  | SWIZZLE
  | RELAXED_SWIZZLE

;; test.spectec:1063.1-1063.47
syntax vswizzlop_ = 
  | mk_vswizzlop__0(v_M : M, var_x : vswizzlop_M)

;; test.spectec:1063.8-1063.19
relation wf_vswizzlop_: `%%`(bshape, vswizzlop_)
  ;; test.spectec:1063.8-1063.19
  rule vswizzlop__case_0{v_bshape : bshape, v_M : M, var_x : vswizzlop_M}:
    `%%`(v_bshape, mk_vswizzlop__0_vswizzlop_(v_M, var_x))
    -- if (v_bshape = mk_bshape_bshape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))))

;; test.spectec:1063.1-1063.47
def $proj_vswizzlop__0(var_x : vswizzlop_) : vswizzlop_M
  ;; test.spectec:1063.8-1063.19
  def $proj_vswizzlop__0{v_M : M, var_x : vswizzlop_M}(mk_vswizzlop__0_vswizzlop_(v_M, var_x)) = var_x

;; test.spectec:1066.1-1066.59
syntax vextunop__Jnn_1_M_1_Jnn_2_M_2 = 
  | EXTADD_PAIRWISE(v_sx : sx)

;; test.spectec:1066.8-1066.19
relation wf_vextunop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn, M, Jnn, M, vextunop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1066.8-1066.19
  rule vextunop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_sx : sx}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx))
    -- if ((16 <= (2 * $lsizenn1($lanetype_Jnn(Jnn_1)))) /\ (((2 * $lsizenn1($lanetype_Jnn(Jnn_1))) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) <= 32)))

;; test.spectec:1066.1-1066.59
syntax vextunop__ = 
  | mk_vextunop___0(Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2)

;; test.spectec:1066.8-1066.19
relation wf_vextunop__: `%%%`(ishape, ishape, vextunop__)
  ;; test.spectec:1066.8-1066.19
  rule vextunop___case_0{ishape_1 : ishape, ishape_2 : ishape, Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(ishape_1, ishape_2, mk_vextunop___0_vextunop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vextunop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (ishape_1 = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(Jnn_1), mk_dim_dim(M_1))))
    -- if (ishape_2 = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(Jnn_2), mk_dim_dim(M_2))))

;; test.spectec:1066.1-1066.59
def $proj_vextunop___0(var_x : vextunop__) : vextunop__Jnn_1_M_1_Jnn_2_M_2
  ;; test.spectec:1066.8-1066.19
  def $proj_vextunop___0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextunop__Jnn_1_M_1_Jnn_2_M_2}(mk_vextunop___0_vextunop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = var_x

;; test.spectec:1071.1-1071.60
syntax vextbinop__Jnn_1_M_1_Jnn_2_M_2 = 
  | EXTMUL(v_half : half, v_sx : sx)
  | DOTS
  | RELAXED_DOTS

;; test.spectec:1071.8-1071.20
relation wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn, M, Jnn, M, vextbinop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1071.8-1071.20
  rule vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_half : half, v_sx : sx}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx))
    -- if (((2 * $lsizenn1($lanetype_Jnn(Jnn_1))) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) >= 16))

  ;; test.spectec:1071.8-1071.20
  rule vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_1{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2)
    -- if (((2 * $lsizenn1($lanetype_Jnn(Jnn_1))) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) = 32))

  ;; test.spectec:1071.8-1071.20
  rule vextbinop__Jnn_1_M_1_Jnn_2_M_2_case_2{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2)
    -- if (((2 * $lsizenn1($lanetype_Jnn(Jnn_1))) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) = 16))

;; test.spectec:1071.1-1071.60
syntax vextbinop__ = 
  | mk_vextbinop___0(Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2)

;; test.spectec:1071.8-1071.20
relation wf_vextbinop__: `%%%`(ishape, ishape, vextbinop__)
  ;; test.spectec:1071.8-1071.20
  rule vextbinop___case_0{ishape_1 : ishape, ishape_2 : ishape, Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(ishape_1, ishape_2, mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vextbinop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (ishape_1 = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(Jnn_1), mk_dim_dim(M_1))))
    -- if (ishape_2 = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(Jnn_2), mk_dim_dim(M_2))))

;; test.spectec:1071.1-1071.60
def $proj_vextbinop___0(var_x : vextbinop__) : vextbinop__Jnn_1_M_1_Jnn_2_M_2
  ;; test.spectec:1071.8-1071.20
  def $proj_vextbinop___0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextbinop__Jnn_1_M_1_Jnn_2_M_2}(mk_vextbinop___0_vextbinop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = var_x

;; test.spectec:1080.1-1080.61
syntax vextternop__Jnn_1_M_1_Jnn_2_M_2 = 
  | RELAXED_DOT_ADDS

;; test.spectec:1080.8-1080.21
relation wf_vextternop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn, M, Jnn, M, vextternop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1080.8-1080.21
  rule vextternop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2)
    -- if (((4 * $lsizenn1($lanetype_Jnn(Jnn_1))) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) = 32))

;; test.spectec:1080.1-1080.61
syntax vextternop__ = 
  | mk_vextternop___0(Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2)

;; test.spectec:1080.8-1080.21
relation wf_vextternop__: `%%%`(ishape, ishape, vextternop__)
  ;; test.spectec:1080.8-1080.21
  rule vextternop___case_0{ishape_1 : ishape, ishape_2 : ishape, Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(ishape_1, ishape_2, mk_vextternop___0_vextternop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vextternop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (ishape_1 = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(Jnn_1), mk_dim_dim(M_1))))
    -- if (ishape_2 = mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(Jnn_2), mk_dim_dim(M_2))))

;; test.spectec:1080.1-1080.61
def $proj_vextternop___0(var_x : vextternop__) : vextternop__Jnn_1_M_1_Jnn_2_M_2
  ;; test.spectec:1080.8-1080.21
  def $proj_vextternop___0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vextternop__Jnn_1_M_1_Jnn_2_M_2}(mk_vextternop___0_vextternop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = var_x

;; test.spectec:1085.1-1085.55
syntax vcvtop__Jnn_1_M_1_Jnn_2_M_2 = 
  | EXTEND(v_half : half, v_sx : sx)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn, M, Jnn, M, vcvtop__Jnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Jnn_1_M_1_Jnn_2_M_2_case_0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_half : half, v_sx : sx}:
    `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx))
    -- if ($lsizenn2($lanetype_Jnn(Jnn_2)) = (2 * $lsizenn1($lanetype_Jnn(Jnn_1))))

;; test.spectec:1085.1-1085.55
syntax vcvtop__Jnn_1_M_1_Fnn_2_M_2 = 
  | CONVERT(half_opt : half?, v_sx : sx)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2: `%%%%%`(Jnn, M, Fnn, M, vcvtop__Jnn_1_M_1_Fnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Jnn_1_M_1_Fnn_2_M_2_case_0{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, half_opt : half?, v_sx : sx}:
    `%%%%%`(Jnn_1, M_1, Fnn_2, M_2, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx))
    -- if (((($sizenn2($numtype_Fnn(Fnn_2)) = $lsizenn1($lanetype_Jnn(Jnn_1))) /\ ($lsizenn1($lanetype_Jnn(Jnn_1)) = 32)) /\ (half_opt = ?())) \/ (($sizenn2($numtype_Fnn(Fnn_2)) = (2 * $lsizenn1($lanetype_Jnn(Jnn_1)))) /\ (half_opt = ?(LOW_half))))

;; test.spectec:1085.1-1085.55
syntax vcvtop__Fnn_1_M_1_Jnn_2_M_2 = 
  | TRUNC_SAT(v_sx : sx, zero_opt : zero?)
  | RELAXED_TRUNC(v_sx : sx, zero_opt : zero?)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2: `%%%%%`(Fnn, M, Jnn, M, vcvtop__Fnn_1_M_1_Jnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_0{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_sx : sx, zero_opt : zero?}:
    `%%%%%`(Fnn_1, M_1, Jnn_2, M_2, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt))
    -- if (((($sizenn1($numtype_Fnn(Fnn_1)) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) = 32)) /\ (zero_opt = ?())) \/ (($sizenn1($numtype_Fnn(Fnn_1)) = (2 * $lsizenn2($lanetype_Jnn(Jnn_2)))) /\ (zero_opt = ?(ZERO_zero))))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Jnn_2_M_2_case_1{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_sx : sx, zero_opt : zero?}:
    `%%%%%`(Fnn_1, M_1, Jnn_2, M_2, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt))
    -- if (((($sizenn1($numtype_Fnn(Fnn_1)) = $lsizenn2($lanetype_Jnn(Jnn_2))) /\ ($lsizenn2($lanetype_Jnn(Jnn_2)) = 32)) /\ (zero_opt = ?())) \/ (($sizenn1($numtype_Fnn(Fnn_1)) = (2 * $lsizenn2($lanetype_Jnn(Jnn_2)))) /\ (zero_opt = ?(ZERO_zero))))

;; test.spectec:1085.1-1085.55
syntax vcvtop__Fnn_1_M_1_Fnn_2_M_2 = 
  | DEMOTE(v_zero : zero)
  | PROMOTELOW

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2: `%%%%%`(Fnn, M, Fnn, M, vcvtop__Fnn_1_M_1_Fnn_2_M_2)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_0{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, v_zero : zero}:
    `%%%%%`(Fnn_1, M_1, Fnn_2, M_2, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero))
    -- if ($sizenn1($numtype_Fnn(Fnn_1)) = (2 * $sizenn2($numtype_Fnn(Fnn_2))))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop__Fnn_1_M_1_Fnn_2_M_2_case_1{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}:
    `%%%%%`(Fnn_1, M_1, Fnn_2, M_2, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2)
    -- if ((2 * $sizenn1($numtype_Fnn(Fnn_1))) = $sizenn2($numtype_Fnn(Fnn_2)))

;; test.spectec:1085.1-1085.55
syntax vcvtop__ = 
  | mk_vcvtop___0(Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2)
  | mk_vcvtop___1(Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2)
  | mk_vcvtop___2(Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2)
  | mk_vcvtop___3(Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2)

;; test.spectec:1085.8-1085.17
relation wf_vcvtop__: `%%%`(shape, shape, vcvtop__)
  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_0{shape_1 : shape, shape_2 : shape, Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vcvtop__Jnn_1_M_1_Jnn_2_M_2: `%%%%%`(Jnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape($lanetype_Jnn(Jnn_1), mk_dim_dim(M_1)))
    -- if (shape_2 = `%X%`_shape($lanetype_Jnn(Jnn_2), mk_dim_dim(M_2)))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_1{shape_1 : shape, shape_2 : shape, Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, var_x))
    -- wf_vcvtop__Jnn_1_M_1_Fnn_2_M_2: `%%%%%`(Jnn_1, M_1, Fnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape($lanetype_Jnn(Jnn_1), mk_dim_dim(M_1)))
    -- if (shape_2 = `%X%`_shape($lanetype_Fnn(Fnn_2), mk_dim_dim(M_2)))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_2{shape_1 : shape, shape_2 : shape, Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, var_x))
    -- wf_vcvtop__Fnn_1_M_1_Jnn_2_M_2: `%%%%%`(Fnn_1, M_1, Jnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape($lanetype_Fnn(Fnn_1), mk_dim_dim(M_1)))
    -- if (shape_2 = `%X%`_shape($lanetype_Jnn(Jnn_2), mk_dim_dim(M_2)))

  ;; test.spectec:1085.8-1085.17
  rule vcvtop___case_3{shape_1 : shape, shape_2 : shape, Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2}:
    `%%%`(shape_1, shape_2, mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, var_x))
    -- wf_vcvtop__Fnn_1_M_1_Fnn_2_M_2: `%%%%%`(Fnn_1, M_1, Fnn_2, M_2, var_x)
    -- if (shape_1 = `%X%`_shape($lanetype_Fnn(Fnn_1), mk_dim_dim(M_1)))
    -- if (shape_2 = `%X%`_shape($lanetype_Fnn(Fnn_2), mk_dim_dim(M_2)))

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___0(var_x : vcvtop__) : vcvtop__Jnn_1_M_1_Jnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___0{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vcvtop__Jnn_1_M_1_Jnn_2_M_2}(mk_vcvtop___0_vcvtop__(Jnn_1, M_1, Jnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___0{var_x : vcvtop__}(var_x) = ?()

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___1(var_x : vcvtop__) : vcvtop__Jnn_1_M_1_Fnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___1{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, var_x : vcvtop__Jnn_1_M_1_Fnn_2_M_2}(mk_vcvtop___1_vcvtop__(Jnn_1, M_1, Fnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___1{var_x : vcvtop__}(var_x) = ?()

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___2(var_x : vcvtop__) : vcvtop__Fnn_1_M_1_Jnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___2{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, var_x : vcvtop__Fnn_1_M_1_Jnn_2_M_2}(mk_vcvtop___2_vcvtop__(Fnn_1, M_1, Jnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___2{var_x : vcvtop__}(var_x) = ?()

;; test.spectec:1085.1-1085.55
def $proj_vcvtop___3(var_x : vcvtop__) : vcvtop__Fnn_1_M_1_Fnn_2_M_2?
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___3{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, var_x : vcvtop__Fnn_1_M_1_Fnn_2_M_2}(mk_vcvtop___3_vcvtop__(Fnn_1, M_1, Fnn_2, M_2, var_x)) = ?(var_x)
  ;; test.spectec:1085.8-1085.17
  def $proj_vcvtop___3{var_x : vcvtop__}(var_x) = ?()

;; test.spectec:1109.1-1109.69
syntax memarg = 
{
  ALIGN u32,
  OFFSET u64
}

;; test.spectec:1109.8-1109.14
relation wf_memarg: `%`(memarg)
  ;; test.spectec:1109.8-1109.14
  rule memarg_case_{var_0 : u32, var_1 : u64}:
    `%`({ALIGN var_0, OFFSET var_1})
    -- wf_uN: `%%`(32, var_0)
    -- wf_uN: `%%`(64, var_1)

;; test.spectec:1113.1-1113.24
syntax loadop_Inn = 
  | mk_loadop_Inn(v_sz : sz, v_sx : sx)

;; test.spectec:1113.8-1113.16
relation wf_loadop_Inn: `%%`(Inn, loadop_Inn)
  ;; test.spectec:1113.8-1113.16
  rule loadop_Inn_case_0{v_Inn : Inn, v_sz : sz, v_sx : sx}:
    `%%`(v_Inn, mk_loadop_Inn_loadop_Inn(v_sz, v_sx))
    -- wf_sz: `%`(v_sz)
    -- if ($proj_sz_0(v_sz).0 < $sizenn($numtype_addrtype(v_Inn)))

;; test.spectec:1113.1-1113.24
syntax loadop_ = 
  | mk_loadop__0(v_Inn : Inn, var_x : loadop_Inn)

;; test.spectec:1113.8-1113.16
relation wf_loadop_: `%%`(numtype, loadop_)
  ;; test.spectec:1113.8-1113.16
  rule loadop__case_0{v_numtype : numtype, v_Inn : Inn, var_x : loadop_Inn}:
    `%%`(v_numtype, mk_loadop__0_loadop_(v_Inn, var_x))
    -- wf_loadop_Inn: `%%`(v_Inn, var_x)
    -- if (v_numtype = $numtype_addrtype(v_Inn))

;; test.spectec:1113.1-1113.24
def $proj_loadop__0(var_x : loadop_) : loadop_Inn
  ;; test.spectec:1113.8-1113.16
  def $proj_loadop__0{v_Inn : Inn, var_x : loadop_Inn}(mk_loadop__0_loadop_(v_Inn, var_x)) = var_x

;; test.spectec:1116.1-1116.25
syntax storeop_Inn = 
  | mk_storeop_Inn(v_sz : sz)

;; test.spectec:1116.8-1116.17
relation wf_storeop_Inn: `%%`(Inn, storeop_Inn)
  ;; test.spectec:1116.8-1116.17
  rule storeop_Inn_case_0{v_Inn : Inn, v_sz : sz}:
    `%%`(v_Inn, mk_storeop_Inn_storeop_Inn(v_sz))
    -- wf_sz: `%`(v_sz)
    -- if ($proj_sz_0(v_sz).0 < $sizenn($numtype_addrtype(v_Inn)))

;; test.spectec:1116.1-1116.25
syntax storeop_ = 
  | mk_storeop__0(v_Inn : Inn, var_x : storeop_Inn)

;; test.spectec:1116.8-1116.17
relation wf_storeop_: `%%`(numtype, storeop_)
  ;; test.spectec:1116.8-1116.17
  rule storeop__case_0{v_numtype : numtype, v_Inn : Inn, var_x : storeop_Inn}:
    `%%`(v_numtype, mk_storeop__0_storeop_(v_Inn, var_x))
    -- wf_storeop_Inn: `%%`(v_Inn, var_x)
    -- if (v_numtype = $numtype_addrtype(v_Inn))

;; test.spectec:1116.1-1116.25
def $proj_storeop__0(var_x : storeop_) : storeop_Inn
  ;; test.spectec:1116.8-1116.17
  def $proj_storeop__0{v_Inn : Inn, var_x : storeop_Inn}(mk_storeop__0_storeop_(v_Inn, var_x)) = var_x

;; test.spectec:1119.1-1122.59
syntax vloadop_ = 
  | `SHAPE%X%_%`(v_sz : sz, v_M : M, v_sx : sx)
  | SPLAT(v_sz : sz)
  | ZERO(v_sz : sz)

;; test.spectec:1119.8-1119.17
relation wf_vloadop_: `%%`(vectype, vloadop_)
  ;; test.spectec:1119.8-1119.17
  rule vloadop__case_0{v_vectype : vectype, v_sz : sz, v_M : M, v_sx : sx}:
    `%%`(v_vectype, `SHAPE%X%_%`_vloadop_(v_sz, v_M, v_sx))
    -- wf_sz: `%`(v_sz)
    -- if ((($proj_sz_0(v_sz).0 * v_M) : nat <:> rat) = (($vsize(v_vectype) : nat <:> rat) / (2 : nat <:> rat)))

  ;; test.spectec:1119.8-1119.17
  rule vloadop__case_1{v_vectype : vectype, v_sz : sz}:
    `%%`(v_vectype, SPLAT_vloadop_(v_sz))
    -- wf_sz: `%`(v_sz)

  ;; test.spectec:1119.8-1119.17
  rule vloadop__case_2{v_vectype : vectype, v_sz : sz}:
    `%%`(v_vectype, ZERO_vloadop_(v_sz))
    -- wf_sz: `%`(v_sz)
    -- if ($proj_sz_0(v_sz).0 >= 32)

;; test.spectec:1127.1-1129.17
syntax blocktype = 
  | _RESULT(valtype_opt : valtype?)
  | _IDX(v_typeidx : typeidx)

;; test.spectec:1127.8-1127.17
relation wf_blocktype: `%`(blocktype)
  ;; test.spectec:1127.8-1127.17
  rule blocktype_case_0{valtype_opt : valtype?}:
    `%`(_RESULT_blocktype(valtype_opt))
    -- (wf_valtype: `%`(v_valtype))?{v_valtype <- valtype_opt}

  ;; test.spectec:1127.8-1127.17
  rule blocktype_case_1{v_typeidx : typeidx}:
    `%`(_IDX_blocktype(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

;; test.spectec:4102.1-4102.39
syntax addr = nat

;; test.spectec:4111.1-4111.51
syntax arrayaddr = addr

;; test.spectec:1177.1-1181.27
syntax catch = 
  | CATCH(v_tagidx : tagidx, v_labelidx : labelidx)
  | CATCH_REF(v_tagidx : tagidx, v_labelidx : labelidx)
  | CATCH_ALL(v_labelidx : labelidx)
  | CATCH_ALL_REF(v_labelidx : labelidx)

;; test.spectec:1177.8-1177.13
relation wf_catch: `%`(catch)
  ;; test.spectec:1177.8-1177.13
  rule catch_case_0{v_tagidx : tagidx, v_labelidx : labelidx}:
    `%`(CATCH_catch(v_tagidx, v_labelidx))
    -- wf_uN: `%%`(32, v_tagidx)
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:1177.8-1177.13
  rule catch_case_1{v_tagidx : tagidx, v_labelidx : labelidx}:
    `%`(CATCH_REF_catch(v_tagidx, v_labelidx))
    -- wf_uN: `%%`(32, v_tagidx)
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:1177.8-1177.13
  rule catch_case_2{v_labelidx : labelidx}:
    `%`(CATCH_ALL_catch(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:1177.8-1177.13
  rule catch_case_3{v_labelidx : labelidx}:
    `%`(CATCH_ALL_REF_catch(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

;; test.spectec:4112.1-4112.53
syntax exnaddr = addr

;; test.spectec:4108.1-4108.49
syntax dataaddr = addr

;; test.spectec:4109.1-4109.49
syntax elemaddr = addr

;; test.spectec:4107.1-4107.53
syntax funcaddr = addr

;; test.spectec:4104.1-4104.53
syntax globaladdr = addr

;; test.spectec:4105.1-4105.50
syntax memaddr = addr

;; test.spectec:4106.1-4106.51
syntax tableaddr = addr

;; test.spectec:4103.1-4103.47
syntax tagaddr = addr

;; test.spectec:4115.1-4116.84
syntax externaddr = 
  | TAG(v_tagaddr : tagaddr)
  | GLOBAL(v_globaladdr : globaladdr)
  | MEM(v_memaddr : memaddr)
  | TABLE(v_tableaddr : tableaddr)
  | FUNC(v_funcaddr : funcaddr)

;; test.spectec:4176.1-4177.33
syntax exportinst = 
{
  NAME name,
  ADDR externaddr
}

;; test.spectec:4176.8-4176.18
relation wf_exportinst: `%`(exportinst)
  ;; test.spectec:4176.8-4176.18
  rule exportinst_case_{var_0 : name, var_1 : externaddr}:
    `%`({NAME var_0, ADDR var_1})
    -- wf_name: `%`(var_0)

;; test.spectec:4196.1-4205.26
syntax moduleinst = 
{
  TYPES deftype*,
  TAGS tagaddr*,
  GLOBALS globaladdr*,
  MEMS memaddr*,
  TABLES tableaddr*,
  FUNCS funcaddr*,
  DATAS dataaddr*,
  ELEMS elemaddr*,
  EXPORTS exportinst*
}

;; test.spectec:4196.8-4196.18
relation wf_moduleinst: `%`(moduleinst)
  ;; test.spectec:4196.8-4196.18
  rule moduleinst_case_{var_0_lst : deftype*, var_1_lst : tagaddr*, var_2_lst : globaladdr*, var_3_lst : memaddr*, var_4_lst : tableaddr*, var_5_lst : funcaddr*, var_6_lst : dataaddr*, var_7_lst : elemaddr*, var_8_lst : exportinst*}:
    `%`({TYPES var_0_lst, TAGS var_1_lst, GLOBALS var_2_lst, MEMS var_3_lst, TABLES var_4_lst, FUNCS var_5_lst, DATAS var_6_lst, ELEMS var_7_lst, EXPORTS var_8_lst})
    -- (wf_exportinst: `%`(var_8))*{var_8 <- var_8_lst}

;; test.spectec:4113.1-4113.49
syntax hostaddr = addr

;; test.spectec:4110.1-4110.56
syntax structaddr = addr

;; test.spectec:4130.1-4138.19
rec {

;; test.spectec:4130.1-4138.19
syntax ref = 
  | REF_I31_NUM(v_u31 : u31)
  | REF_NULL_ADDR
  | REF_STRUCT_ADDR(v_structaddr : structaddr)
  | REF_ARRAY_ADDR(v_arrayaddr : arrayaddr)
  | REF_FUNC_ADDR(v_funcaddr : funcaddr)
  | REF_EXN_ADDR(v_exnaddr : exnaddr)
  | REF_HOST_ADDR(v_hostaddr : hostaddr)
  | REF_EXTERN(v_ref : ref)
}

;; test.spectec:4130.1-4138.19
rec {

;; test.spectec:4130.8-4130.11
relation wf_ref: `%`(ref)
  ;; test.spectec:4130.8-4130.11
  rule ref_case_0{v_u31 : u31}:
    `%`(REF_I31_NUM_ref(v_u31))
    -- wf_uN: `%%`(31, v_u31)

  ;; test.spectec:4130.8-4130.11
  rule ref_case_1:
    `%`(REF_NULL_ADDR_ref)

  ;; test.spectec:4130.8-4130.11
  rule ref_case_2{v_structaddr : structaddr}:
    `%`(REF_STRUCT_ADDR_ref(v_structaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_3{v_arrayaddr : arrayaddr}:
    `%`(REF_ARRAY_ADDR_ref(v_arrayaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_4{v_funcaddr : funcaddr}:
    `%`(REF_FUNC_ADDR_ref(v_funcaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_5{v_exnaddr : exnaddr}:
    `%`(REF_EXN_ADDR_ref(v_exnaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_6{v_hostaddr : hostaddr}:
    `%`(REF_HOST_ADDR_ref(v_hostaddr))

  ;; test.spectec:4130.8-4130.11
  rule ref_case_7{v_ref : ref}:
    `%`(REF_EXTERN_ref(v_ref))
}

;; test.spectec:4140.1-4141.20
syntax val = 
  | CONST(v_numtype : numtype, num_)
  | VCONST(v_vectype : vectype, vec_)
  | REF_I31_NUM(v_u31 : u31)
  | REF_NULL_ADDR
  | REF_STRUCT_ADDR(v_structaddr : structaddr)
  | REF_ARRAY_ADDR(v_arrayaddr : arrayaddr)
  | REF_FUNC_ADDR(v_funcaddr : funcaddr)
  | REF_EXN_ADDR(v_exnaddr : exnaddr)
  | REF_HOST_ADDR(v_hostaddr : hostaddr)
  | REF_EXTERN(v_ref : ref)

def $val_ref(var_0 : ref) : val
  def $val_ref{x0 : u31}(REF_I31_NUM_ref(x0)) = REF_I31_NUM_val(x0)
  def $val_ref(REF_NULL_ADDR_ref) = REF_NULL_ADDR_val
  def $val_ref{x0 : structaddr}(REF_STRUCT_ADDR_ref(x0)) = REF_STRUCT_ADDR_val(x0)
  def $val_ref{x0 : arrayaddr}(REF_ARRAY_ADDR_ref(x0)) = REF_ARRAY_ADDR_val(x0)
  def $val_ref{x0 : funcaddr}(REF_FUNC_ADDR_ref(x0)) = REF_FUNC_ADDR_val(x0)
  def $val_ref{x0 : exnaddr}(REF_EXN_ADDR_ref(x0)) = REF_EXN_ADDR_val(x0)
  def $val_ref{x0 : hostaddr}(REF_HOST_ADDR_ref(x0)) = REF_HOST_ADDR_val(x0)
  def $val_ref{x0 : ref}(REF_EXTERN_ref(x0)) = REF_EXTERN_val(x0)

;; test.spectec:4140.8-4140.11
relation wf_val: `%`(val)
  ;; test.spectec:4140.8-4140.11
  rule val_case_0{v_numtype : numtype, var_0 : num_}:
    `%`(CONST_val(v_numtype, var_0))
    -- wf_num_: `%%`(v_numtype, var_0)

  ;; test.spectec:4140.8-4140.11
  rule val_case_1{v_vectype : vectype, var_0 : vec_}:
    `%`(VCONST_val(v_vectype, var_0))
    -- wf_uN: `%%`($vsize(v_vectype), var_0)

  ;; test.spectec:4140.8-4140.11
  rule val_case_2{v_u31 : u31}:
    `%`(REF_I31_NUM_val(v_u31))
    -- wf_uN: `%%`(31, v_u31)

  ;; test.spectec:4140.8-4140.11
  rule val_case_3:
    `%`(REF_NULL_ADDR_val)

  ;; test.spectec:4140.8-4140.11
  rule val_case_4{v_structaddr : structaddr}:
    `%`(REF_STRUCT_ADDR_val(v_structaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_5{v_arrayaddr : arrayaddr}:
    `%`(REF_ARRAY_ADDR_val(v_arrayaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_6{v_funcaddr : funcaddr}:
    `%`(REF_FUNC_ADDR_val(v_funcaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_7{v_exnaddr : exnaddr}:
    `%`(REF_EXN_ADDR_val(v_exnaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_8{v_hostaddr : hostaddr}:
    `%`(REF_HOST_ADDR_val(v_hostaddr))

  ;; test.spectec:4140.8-4140.11
  rule val_case_9{v_ref : ref}:
    `%`(REF_EXTERN_val(v_ref))
    -- wf_ref: `%`(v_ref)

;; test.spectec:4222.1-4223.40
syntax frame = 
{
  LOCALS val?*,
  MODULE moduleinst
}

;; test.spectec:4222.8-4222.13
relation wf_frame: `%`(frame)
  ;; test.spectec:4222.8-4222.13
  rule frame_case_{var_0_opt_lst : val?*, var_1 : moduleinst}:
    `%`({LOCALS var_0_opt_lst, MODULE var_1})
    -- (wf_val: `%`(var_0))?{var_0 <- var_0_opt}*{var_0_opt <- var_0_opt_lst}
    -- wf_moduleinst: `%`(var_1)

;; test.spectec:4228.1-4234.9
rec {

;; test.spectec:4228.1-4234.9
syntax instr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT(valtype_lst_opt : valtype*?)
  | BLOCK(v_blocktype : blocktype, instr_lst : instr*)
  | LOOP(v_blocktype : blocktype, instr_lst : instr*)
  | `IF%%ELSE%`(v_blocktype : blocktype, instr_lst : instr*, instr_lst : instr*)
  | BR(v_labelidx : labelidx)
  | BR_IF(v_labelidx : labelidx)
  | BR_TABLE(labelidx_lst : labelidx*, v_labelidx : labelidx)
  | BR_ON_NULL(v_labelidx : labelidx)
  | BR_ON_NON_NULL(v_labelidx : labelidx)
  | BR_ON_CAST(v_labelidx : labelidx, v_reftype : reftype, v_reftype : reftype)
  | BR_ON_CAST_FAIL(v_labelidx : labelidx, v_reftype : reftype, v_reftype : reftype)
  | CALL(v_funcidx : funcidx)
  | CALL_REF(v_typeuse : typeuse)
  | CALL_INDIRECT(v_tableidx : tableidx, v_typeuse : typeuse)
  | RETURN
  | RETURN_CALL(v_funcidx : funcidx)
  | RETURN_CALL_REF(v_typeuse : typeuse)
  | RETURN_CALL_INDIRECT(v_tableidx : tableidx, v_typeuse : typeuse)
  | THROW(v_tagidx : tagidx)
  | THROW_REF
  | TRY_TABLE(v_blocktype : blocktype, list(syntax catch), instr_lst : instr*)
  | LOCAL_GET(v_localidx : localidx)
  | LOCAL_SET(v_localidx : localidx)
  | LOCAL_TEE(v_localidx : localidx)
  | GLOBAL_GET(v_globalidx : globalidx)
  | GLOBAL_SET(v_globalidx : globalidx)
  | TABLE_GET(v_tableidx : tableidx)
  | TABLE_SET(v_tableidx : tableidx)
  | TABLE_SIZE(v_tableidx : tableidx)
  | TABLE_GROW(v_tableidx : tableidx)
  | TABLE_FILL(v_tableidx : tableidx)
  | TABLE_COPY(v_tableidx : tableidx, v_tableidx : tableidx)
  | TABLE_INIT(v_tableidx : tableidx, v_elemidx : elemidx)
  | ELEM_DROP(v_elemidx : elemidx)
  | LOAD(v_numtype : numtype, loadop_?, v_memidx : memidx, v_memarg : memarg)
  | STORE(v_numtype : numtype, storeop_?, v_memidx : memidx, v_memarg : memarg)
  | VLOAD(v_vectype : vectype, vloadop_?, v_memidx : memidx, v_memarg : memarg)
  | VLOAD_LANE(v_vectype : vectype, v_sz : sz, v_memidx : memidx, v_memarg : memarg, v_laneidx : laneidx)
  | VSTORE(v_vectype : vectype, v_memidx : memidx, v_memarg : memarg)
  | VSTORE_LANE(v_vectype : vectype, v_sz : sz, v_memidx : memidx, v_memarg : memarg, v_laneidx : laneidx)
  | MEMORY_SIZE(v_memidx : memidx)
  | MEMORY_GROW(v_memidx : memidx)
  | MEMORY_FILL(v_memidx : memidx)
  | MEMORY_COPY(v_memidx : memidx, v_memidx : memidx)
  | MEMORY_INIT(v_memidx : memidx, v_dataidx : dataidx)
  | DATA_DROP(v_dataidx : dataidx)
  | REF_NULL(v_heaptype : heaptype)
  | REF_IS_NULL
  | REF_AS_NON_NULL
  | REF_EQ
  | REF_TEST(v_reftype : reftype)
  | REF_CAST(v_reftype : reftype)
  | REF_FUNC(v_funcidx : funcidx)
  | REF_I31
  | I31_GET(v_sx : sx)
  | STRUCT_NEW(v_typeidx : typeidx)
  | STRUCT_NEW_DEFAULT(v_typeidx : typeidx)
  | STRUCT_GET(sx_opt : sx?, v_typeidx : typeidx, v_fieldidx : fieldidx)
  | STRUCT_SET(v_typeidx : typeidx, v_fieldidx : fieldidx)
  | ARRAY_NEW(v_typeidx : typeidx)
  | ARRAY_NEW_DEFAULT(v_typeidx : typeidx)
  | ARRAY_NEW_FIXED(v_typeidx : typeidx, v_u32 : u32)
  | ARRAY_NEW_DATA(v_typeidx : typeidx, v_dataidx : dataidx)
  | ARRAY_NEW_ELEM(v_typeidx : typeidx, v_elemidx : elemidx)
  | ARRAY_GET(sx_opt : sx?, v_typeidx : typeidx)
  | ARRAY_SET(v_typeidx : typeidx)
  | ARRAY_LEN
  | ARRAY_FILL(v_typeidx : typeidx)
  | ARRAY_COPY(v_typeidx : typeidx, v_typeidx : typeidx)
  | ARRAY_INIT_DATA(v_typeidx : typeidx, v_dataidx : dataidx)
  | ARRAY_INIT_ELEM(v_typeidx : typeidx, v_elemidx : elemidx)
  | EXTERN_CONVERT_ANY
  | ANY_CONVERT_EXTERN
  | CONST(v_numtype : numtype, num_)
  | UNOP(v_numtype : numtype, unop_)
  | BINOP(v_numtype : numtype, binop_)
  | TESTOP(v_numtype : numtype, testop_)
  | RELOP(v_numtype : numtype, relop_)
  | CVTOP(numtype_1 : numtype, numtype_2 : numtype, cvtop__)
  | VCONST(v_vectype : vectype, vec_)
  | VVUNOP(v_vectype : vectype, v_vvunop : vvunop)
  | VVBINOP(v_vectype : vectype, v_vvbinop : vvbinop)
  | VVTERNOP(v_vectype : vectype, v_vvternop : vvternop)
  | VVTESTOP(v_vectype : vectype, v_vvtestop : vvtestop)
  | VUNOP(v_shape : shape, vunop_)
  | VBINOP(v_shape : shape, vbinop_)
  | VTERNOP(v_shape : shape, vternop_)
  | VTESTOP(v_shape : shape, vtestop_)
  | VRELOP(v_shape : shape, vrelop_)
  | VSHIFTOP(v_ishape : ishape, vshiftop_)
  | VBITMASK(v_ishape : ishape)
  | VSWIZZLOP(v_bshape : bshape, vswizzlop_)
  | VSHUFFLE(v_bshape : bshape, laneidx_lst : laneidx*)
  | VEXTUNOP(ishape_1 : ishape, ishape_2 : ishape, vextunop__)
  | VEXTBINOP(ishape_1 : ishape, ishape_2 : ishape, vextbinop__)
  | VEXTTERNOP(ishape_1 : ishape, ishape_2 : ishape, vextternop__)
  | VNARROW(ishape_1 : ishape, ishape_2 : ishape, v_sx : sx)
  | VCVTOP(shape_1 : shape, shape_2 : shape, vcvtop__)
  | VSPLAT(v_shape : shape)
  | VEXTRACT_LANE(v_shape : shape, sx_opt : sx?, v_laneidx : laneidx)
  | VREPLACE_LANE(v_shape : shape, v_laneidx : laneidx)
  | REF_I31_NUM(v_u31 : u31)
  | REF_NULL_ADDR
  | REF_STRUCT_ADDR(v_structaddr : structaddr)
  | REF_ARRAY_ADDR(v_arrayaddr : arrayaddr)
  | REF_FUNC_ADDR(v_funcaddr : funcaddr)
  | REF_EXN_ADDR(v_exnaddr : exnaddr)
  | REF_HOST_ADDR(v_hostaddr : hostaddr)
  | REF_EXTERN(v_ref : ref)
  | `LABEL_%{%}%`(v_n : n, instr_lst : instr*, instr_lst : instr*)
  | `FRAME_%{%}%`(v_n : n, v_frame : frame, instr_lst : instr*)
  | `HANDLER_%{%}%`(v_n : n, catch_lst : catch*, instr_lst : instr*)
  | TRAP
}

;; test.spectec:4228.1-4234.9
rec {

;; test.spectec:4228.8-4228.13
relation wf_instr: `%`(instr)
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
  rule instr_case_3{valtype_lst_opt : valtype*?}:
    `%`(SELECT_instr(valtype_lst_opt))
    -- (wf_valtype: `%`(v_valtype))*{v_valtype <- valtype_lst}?{valtype_lst <- valtype_lst_opt}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_4{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(BLOCK_instr(v_blocktype, instr_lst))
    -- wf_blocktype: `%`(v_blocktype)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_5{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(LOOP_instr(v_blocktype, instr_lst))
    -- wf_blocktype: `%`(v_blocktype)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_6{v_blocktype : blocktype, instr_lst : instr*, instr_lst_0_lst : instr*}:
    `%`(`IF%%ELSE%`_instr(v_blocktype, instr_lst, instr_lst_0_lst))
    -- wf_blocktype: `%`(v_blocktype)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_instr: `%`(instr_lst_0))*{instr_lst_0 <- instr_lst_0_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_7{v_labelidx : labelidx}:
    `%`(BR_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_8{v_labelidx : labelidx}:
    `%`(BR_IF_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_9{labelidx_lst : labelidx*, v_labelidx : labelidx}:
    `%`(BR_TABLE_instr(labelidx_lst, v_labelidx))
    -- (wf_uN: `%%`(32, v_labelidx))*{v_labelidx <- labelidx_lst}
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_10{v_labelidx : labelidx}:
    `%`(BR_ON_NULL_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_11{v_labelidx : labelidx}:
    `%`(BR_ON_NON_NULL_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_12{v_labelidx : labelidx, v_reftype : reftype, reftype_0 : reftype}:
    `%`(BR_ON_CAST_instr(v_labelidx, v_reftype, reftype_0))
    -- wf_uN: `%%`(32, v_labelidx)
    -- wf_reftype: `%`(v_reftype)
    -- wf_reftype: `%`(reftype_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_13{v_labelidx : labelidx, v_reftype : reftype, reftype_0 : reftype}:
    `%`(BR_ON_CAST_FAIL_instr(v_labelidx, v_reftype, reftype_0))
    -- wf_uN: `%%`(32, v_labelidx)
    -- wf_reftype: `%`(v_reftype)
    -- wf_reftype: `%`(reftype_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_14{v_funcidx : funcidx}:
    `%`(CALL_instr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_15{v_typeuse : typeuse}:
    `%`(CALL_REF_instr(v_typeuse))
    -- wf_typeuse: `%`(v_typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_16{v_tableidx : tableidx, v_typeuse : typeuse}:
    `%`(CALL_INDIRECT_instr(v_tableidx, v_typeuse))
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_typeuse: `%`(v_typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_17:
    `%`(RETURN_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_18{v_funcidx : funcidx}:
    `%`(RETURN_CALL_instr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_19{v_typeuse : typeuse}:
    `%`(RETURN_CALL_REF_instr(v_typeuse))
    -- wf_typeuse: `%`(v_typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_20{v_tableidx : tableidx, v_typeuse : typeuse}:
    `%`(RETURN_CALL_INDIRECT_instr(v_tableidx, v_typeuse))
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_typeuse: `%`(v_typeuse)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_21{v_tagidx : tagidx}:
    `%`(THROW_instr(v_tagidx))
    -- wf_uN: `%%`(32, v_tagidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_22:
    `%`(THROW_REF_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_23{v_blocktype : blocktype, var_0 : list(syntax catch), instr_lst : instr*}:
    `%`(TRY_TABLE_instr(v_blocktype, var_0, instr_lst))
    -- wf_blocktype: `%`(v_blocktype)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_24{v_localidx : localidx}:
    `%`(LOCAL_GET_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_25{v_localidx : localidx}:
    `%`(LOCAL_SET_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_26{v_localidx : localidx}:
    `%`(LOCAL_TEE_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_27{v_globalidx : globalidx}:
    `%`(GLOBAL_GET_instr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_28{v_globalidx : globalidx}:
    `%`(GLOBAL_SET_instr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_29{v_tableidx : tableidx}:
    `%`(TABLE_GET_instr(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_30{v_tableidx : tableidx}:
    `%`(TABLE_SET_instr(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_31{v_tableidx : tableidx}:
    `%`(TABLE_SIZE_instr(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_32{v_tableidx : tableidx}:
    `%`(TABLE_GROW_instr(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_33{v_tableidx : tableidx}:
    `%`(TABLE_FILL_instr(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_34{v_tableidx : tableidx, tableidx_0 : tableidx}:
    `%`(TABLE_COPY_instr(v_tableidx, tableidx_0))
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_uN: `%%`(32, tableidx_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_35{v_tableidx : tableidx, v_elemidx : elemidx}:
    `%`(TABLE_INIT_instr(v_tableidx, v_elemidx))
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_uN: `%%`(32, v_elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_36{v_elemidx : elemidx}:
    `%`(ELEM_DROP_instr(v_elemidx))
    -- wf_uN: `%%`(32, v_elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_37{v_numtype : numtype, var_0_opt : loadop_?, v_memidx : memidx, v_memarg : memarg}:
    `%`(LOAD_instr(v_numtype, var_0_opt, v_memidx, v_memarg))
    -- (wf_loadop_: `%%`(v_numtype, var_0))?{var_0 <- var_0_opt}
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_memarg: `%`(v_memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_38{v_numtype : numtype, var_0_opt : storeop_?, v_memidx : memidx, v_memarg : memarg}:
    `%`(STORE_instr(v_numtype, var_0_opt, v_memidx, v_memarg))
    -- (wf_storeop_: `%%`(v_numtype, var_0))?{var_0 <- var_0_opt}
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_memarg: `%`(v_memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_39{v_vectype : vectype, var_0_opt : vloadop_?, v_memidx : memidx, v_memarg : memarg}:
    `%`(VLOAD_instr(v_vectype, var_0_opt, v_memidx, v_memarg))
    -- (wf_vloadop_: `%%`(v_vectype, var_0))?{var_0 <- var_0_opt}
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_memarg: `%`(v_memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_40{v_vectype : vectype, v_sz : sz, v_memidx : memidx, v_memarg : memarg, v_laneidx : laneidx}:
    `%`(VLOAD_LANE_instr(v_vectype, v_sz, v_memidx, v_memarg, v_laneidx))
    -- wf_sz: `%`(v_sz)
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_memarg: `%`(v_memarg)
    -- wf_uN: `%%`(8, v_laneidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_41{v_vectype : vectype, v_memidx : memidx, v_memarg : memarg}:
    `%`(VSTORE_instr(v_vectype, v_memidx, v_memarg))
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_memarg: `%`(v_memarg)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_42{v_vectype : vectype, v_sz : sz, v_memidx : memidx, v_memarg : memarg, v_laneidx : laneidx}:
    `%`(VSTORE_LANE_instr(v_vectype, v_sz, v_memidx, v_memarg, v_laneidx))
    -- wf_sz: `%`(v_sz)
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_memarg: `%`(v_memarg)
    -- wf_uN: `%%`(8, v_laneidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_43{v_memidx : memidx}:
    `%`(MEMORY_SIZE_instr(v_memidx))
    -- wf_uN: `%%`(32, v_memidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_44{v_memidx : memidx}:
    `%`(MEMORY_GROW_instr(v_memidx))
    -- wf_uN: `%%`(32, v_memidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_45{v_memidx : memidx}:
    `%`(MEMORY_FILL_instr(v_memidx))
    -- wf_uN: `%%`(32, v_memidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_46{v_memidx : memidx, memidx_0 : memidx}:
    `%`(MEMORY_COPY_instr(v_memidx, memidx_0))
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_uN: `%%`(32, memidx_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_47{v_memidx : memidx, v_dataidx : dataidx}:
    `%`(MEMORY_INIT_instr(v_memidx, v_dataidx))
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_uN: `%%`(32, v_dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_48{v_dataidx : dataidx}:
    `%`(DATA_DROP_instr(v_dataidx))
    -- wf_uN: `%%`(32, v_dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_49{v_heaptype : heaptype}:
    `%`(REF_NULL_instr(v_heaptype))
    -- wf_heaptype: `%`(v_heaptype)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_50:
    `%`(REF_IS_NULL_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_51:
    `%`(REF_AS_NON_NULL_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_52:
    `%`(REF_EQ_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_53{v_reftype : reftype}:
    `%`(REF_TEST_instr(v_reftype))
    -- wf_reftype: `%`(v_reftype)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_54{v_reftype : reftype}:
    `%`(REF_CAST_instr(v_reftype))
    -- wf_reftype: `%`(v_reftype)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_55{v_funcidx : funcidx}:
    `%`(REF_FUNC_instr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_56:
    `%`(REF_I31_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_57{v_sx : sx}:
    `%`(I31_GET_instr(v_sx))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_58{v_typeidx : typeidx}:
    `%`(STRUCT_NEW_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_59{v_typeidx : typeidx}:
    `%`(STRUCT_NEW_DEFAULT_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_60{sx_opt : sx?, v_typeidx : typeidx, v_fieldidx : fieldidx}:
    `%`(STRUCT_GET_instr(sx_opt, v_typeidx, v_fieldidx))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_fieldidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_61{v_typeidx : typeidx, v_fieldidx : fieldidx}:
    `%`(STRUCT_SET_instr(v_typeidx, v_fieldidx))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_fieldidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_62{v_typeidx : typeidx}:
    `%`(ARRAY_NEW_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_63{v_typeidx : typeidx}:
    `%`(ARRAY_NEW_DEFAULT_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_64{v_typeidx : typeidx, v_u32 : u32}:
    `%`(ARRAY_NEW_FIXED_instr(v_typeidx, v_u32))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_u32)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_65{v_typeidx : typeidx, v_dataidx : dataidx}:
    `%`(ARRAY_NEW_DATA_instr(v_typeidx, v_dataidx))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_66{v_typeidx : typeidx, v_elemidx : elemidx}:
    `%`(ARRAY_NEW_ELEM_instr(v_typeidx, v_elemidx))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_67{sx_opt : sx?, v_typeidx : typeidx}:
    `%`(ARRAY_GET_instr(sx_opt, v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_68{v_typeidx : typeidx}:
    `%`(ARRAY_SET_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_69:
    `%`(ARRAY_LEN_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_70{v_typeidx : typeidx}:
    `%`(ARRAY_FILL_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_71{v_typeidx : typeidx, typeidx_0 : typeidx}:
    `%`(ARRAY_COPY_instr(v_typeidx, typeidx_0))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, typeidx_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_72{v_typeidx : typeidx, v_dataidx : dataidx}:
    `%`(ARRAY_INIT_DATA_instr(v_typeidx, v_dataidx))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_dataidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_73{v_typeidx : typeidx, v_elemidx : elemidx}:
    `%`(ARRAY_INIT_ELEM_instr(v_typeidx, v_elemidx))
    -- wf_uN: `%%`(32, v_typeidx)
    -- wf_uN: `%%`(32, v_elemidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_74:
    `%`(EXTERN_CONVERT_ANY_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_75:
    `%`(ANY_CONVERT_EXTERN_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_76{v_numtype : numtype, var_0 : num_}:
    `%`(CONST_instr(v_numtype, var_0))
    -- wf_num_: `%%`(v_numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_77{v_numtype : numtype, var_0 : unop_}:
    `%`(UNOP_instr(v_numtype, var_0))
    -- wf_unop_: `%%`(v_numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_78{v_numtype : numtype, var_0 : binop_}:
    `%`(BINOP_instr(v_numtype, var_0))
    -- wf_binop_: `%%`(v_numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_79{v_numtype : numtype, var_0 : testop_}:
    `%`(TESTOP_instr(v_numtype, var_0))
    -- wf_testop_: `%%`(v_numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_80{v_numtype : numtype, var_0 : relop_}:
    `%`(RELOP_instr(v_numtype, var_0))
    -- wf_relop_: `%%`(v_numtype, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_81{numtype_1 : numtype, numtype_2 : numtype, var_0 : cvtop__}:
    `%`(CVTOP_instr(numtype_1, numtype_2, var_0))
    -- wf_cvtop__: `%%%`(numtype_2, numtype_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_82{v_vectype : vectype, var_0 : vec_}:
    `%`(VCONST_instr(v_vectype, var_0))
    -- wf_uN: `%%`($vsize(v_vectype), var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_83{v_vectype : vectype, v_vvunop : vvunop}:
    `%`(VVUNOP_instr(v_vectype, v_vvunop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_84{v_vectype : vectype, v_vvbinop : vvbinop}:
    `%`(VVBINOP_instr(v_vectype, v_vvbinop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_85{v_vectype : vectype, v_vvternop : vvternop}:
    `%`(VVTERNOP_instr(v_vectype, v_vvternop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_86{v_vectype : vectype, v_vvtestop : vvtestop}:
    `%`(VVTESTOP_instr(v_vectype, v_vvtestop))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_87{v_shape : shape, var_0 : vunop_}:
    `%`(VUNOP_instr(v_shape, var_0))
    -- wf_shape: `%`(v_shape)
    -- wf_vunop_: `%%`(v_shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_88{v_shape : shape, var_0 : vbinop_}:
    `%`(VBINOP_instr(v_shape, var_0))
    -- wf_shape: `%`(v_shape)
    -- wf_vbinop_: `%%`(v_shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_89{v_shape : shape, var_0 : vternop_}:
    `%`(VTERNOP_instr(v_shape, var_0))
    -- wf_shape: `%`(v_shape)
    -- wf_vternop_: `%%`(v_shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_90{v_shape : shape, var_0 : vtestop_}:
    `%`(VTESTOP_instr(v_shape, var_0))
    -- wf_shape: `%`(v_shape)
    -- wf_vtestop_: `%%`(v_shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_91{v_shape : shape, var_0 : vrelop_}:
    `%`(VRELOP_instr(v_shape, var_0))
    -- wf_shape: `%`(v_shape)
    -- wf_vrelop_: `%%`(v_shape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_92{v_ishape : ishape, var_0 : vshiftop_}:
    `%`(VSHIFTOP_instr(v_ishape, var_0))
    -- wf_ishape: `%`(v_ishape)
    -- wf_vshiftop_: `%%`(v_ishape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_93{v_ishape : ishape}:
    `%`(VBITMASK_instr(v_ishape))
    -- wf_ishape: `%`(v_ishape)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_94{v_bshape : bshape, var_0 : vswizzlop_}:
    `%`(VSWIZZLOP_instr(v_bshape, var_0))
    -- wf_bshape: `%`(v_bshape)
    -- wf_vswizzlop_: `%%`(v_bshape, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_95{v_bshape : bshape, laneidx_lst : laneidx*}:
    `%`(VSHUFFLE_instr(v_bshape, laneidx_lst))
    -- wf_bshape: `%`(v_bshape)
    -- (wf_uN: `%%`(8, v_laneidx))*{v_laneidx <- laneidx_lst}
    -- if (mk_dim_dim(|laneidx_lst|) = $fun_dim($proj_bshape_0(v_bshape).0))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_96{ishape_1 : ishape, ishape_2 : ishape, var_0 : vextunop__}:
    `%`(VEXTUNOP_instr(ishape_1, ishape_2, var_0))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextunop__: `%%%`(ishape_2, ishape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_97{ishape_1 : ishape, ishape_2 : ishape, var_0 : vextbinop__}:
    `%`(VEXTBINOP_instr(ishape_1, ishape_2, var_0))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextbinop__: `%%%`(ishape_2, ishape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_98{ishape_1 : ishape, ishape_2 : ishape, var_0 : vextternop__}:
    `%`(VEXTTERNOP_instr(ishape_1, ishape_2, var_0))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextternop__: `%%%`(ishape_2, ishape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_99{ishape_1 : ishape, ishape_2 : ishape, v_sx : sx}:
    `%`(VNARROW_instr(ishape_1, ishape_2, v_sx))
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- if (($lsize($fun_lanetype($proj_ishape_0(ishape_2).0)) = (2 * $lsize($fun_lanetype($proj_ishape_0(ishape_1).0)))) /\ ((2 * $lsize($fun_lanetype($proj_ishape_0(ishape_1).0))) <= 32))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_100{shape_1 : shape, shape_2 : shape, var_0 : vcvtop__}:
    `%`(VCVTOP_instr(shape_1, shape_2, var_0))
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_vcvtop__: `%%%`(shape_2, shape_1, var_0)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_101{v_shape : shape}:
    `%`(VSPLAT_instr(v_shape))
    -- wf_shape: `%`(v_shape)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_102{v_shape : shape, sx_opt : sx?, v_laneidx : laneidx}:
    `%`(VEXTRACT_LANE_instr(v_shape, sx_opt, v_laneidx))
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(8, v_laneidx)
    -- if (|[I32_lanetype I64_lanetype F32_lanetype F64_lanetype]| > 0)
    -- if ((sx_opt = ?()) <=> ($fun_lanetype(v_shape) <- [I32_lanetype I64_lanetype F32_lanetype F64_lanetype]))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_103{v_shape : shape, v_laneidx : laneidx}:
    `%`(VREPLACE_LANE_instr(v_shape, v_laneidx))
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(8, v_laneidx)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_104{v_u31 : u31}:
    `%`(REF_I31_NUM_instr(v_u31))
    -- wf_uN: `%%`(31, v_u31)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_105:
    `%`(REF_NULL_ADDR_instr)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_106{v_structaddr : structaddr}:
    `%`(REF_STRUCT_ADDR_instr(v_structaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_107{v_arrayaddr : arrayaddr}:
    `%`(REF_ARRAY_ADDR_instr(v_arrayaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_108{v_funcaddr : funcaddr}:
    `%`(REF_FUNC_ADDR_instr(v_funcaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_109{v_exnaddr : exnaddr}:
    `%`(REF_EXN_ADDR_instr(v_exnaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_110{v_hostaddr : hostaddr}:
    `%`(REF_HOST_ADDR_instr(v_hostaddr))

  ;; test.spectec:4228.8-4228.13
  rule instr_case_111{v_ref : ref}:
    `%`(REF_EXTERN_instr(v_ref))
    -- wf_ref: `%`(v_ref)

  ;; test.spectec:4228.8-4228.13
  rule instr_case_112{v_n : n, instr_lst : instr*, instr_lst_0_lst : instr*}:
    `%`(`LABEL_%{%}%`_instr(v_n, instr_lst, instr_lst_0_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_instr: `%`(instr_lst_0))*{instr_lst_0 <- instr_lst_0_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_113{v_n : n, v_frame : frame, instr_lst : instr*}:
    `%`(`FRAME_%{%}%`_instr(v_n, v_frame, instr_lst))
    -- wf_frame: `%`(v_frame)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_114{v_n : n, catch_lst : catch*, instr_lst : instr*}:
    `%`(`HANDLER_%{%}%`_instr(v_n, catch_lst, instr_lst))
    -- (wf_catch: `%`(v_catch))*{v_catch <- catch_lst}
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:4228.8-4228.13
  rule instr_case_115:
    `%`(TRAP_instr)
}

;; test.spectec:1314.1-1315.9
syntax expr = instr*

;; test.spectec:1326.1-1326.35
def $memarg0 : memarg
  ;; test.spectec:1327.1-1327.35
  def $memarg0 = {ALIGN mk_uN_u32(0), OFFSET mk_uN_u64(0)}

;; test.spectec:1326.6-1326.13
relation memarg0_is_wf: `%`(ret_val : memarg)
  ;; test.spectec:1326.6-1326.13
  rule memarg0_is_wf_0{ret_val : memarg}:
    `%`(ret_val)
    -- if (ret_val = $memarg0)
    -- wf_memarg: `%`(ret_val)

;; test.spectec:1329.1-1329.69
def $const(v_consttype : consttype, v_lit_ : lit_) : instr
  ;; test.spectec:1330.1-1330.43
  def $const{c : num_}(I32_consttype, mk_lit__0_lit_(I32_numtype, c)) = CONST_instr(I32_numtype, c)
  ;; test.spectec:1330.1-1330.43
  def $const{c : num_}(I64_consttype, mk_lit__0_lit_(I64_numtype, c)) = CONST_instr(I64_numtype, c)
  ;; test.spectec:1330.1-1330.43
  def $const{c : num_}(F32_consttype, mk_lit__0_lit_(F32_numtype, c)) = CONST_instr(F32_numtype, c)
  ;; test.spectec:1330.1-1330.43
  def $const{c : num_}(F64_consttype, mk_lit__0_lit_(F64_numtype, c)) = CONST_instr(F64_numtype, c)
  ;; test.spectec:1331.1-1331.44
  def $const{c : uN}(V128_consttype, mk_lit__1_lit_(V128_vectype, c)) = VCONST_instr(V128_vectype, c)

;; test.spectec:1329.6-1329.12
relation const_is_wf: `%%%`(v_consttype : consttype, v_lit_ : lit_, ret_val : instr)
  ;; test.spectec:1329.6-1329.12
  rule const_is_wf_0{v_consttype : consttype, v_lit_ : lit_, ret_val : instr}:
    `%%%`(v_consttype, v_lit_, ret_val)
    -- wf_lit_: `%%`($storagetype_consttype(v_consttype), v_lit_)
    -- if (ret_val = $const(v_consttype, v_lit_))
    -- wf_instr: `%`(ret_val)

;; test.spectec:1336.1-1336.30
def $free_shape(v_shape : shape) : free
  ;; test.spectec:1345.1-1345.59
  def $free_shape{v_lanetype : lanetype, v_dim : dim}(`%X%`_shape(v_lanetype, v_dim)) = $free_lanetype(v_lanetype)

;; test.spectec:1336.6-1336.17
relation free_shape_is_wf: `%%`(v_shape : shape, ret_val : free)
  ;; test.spectec:1336.6-1336.17
  rule free_shape_is_wf_0{v_shape : shape, ret_val : free}:
    `%%`(v_shape, ret_val)
    -- wf_shape: `%`(v_shape)
    -- if (ret_val = $free_shape(v_shape))
    -- wf_free: `%`(ret_val)

;; test.spectec:1337.6-1337.21
relation fun_free_blocktype: `%%`(blocktype, free)
  ;; test.spectec:1337.6-1337.21
  rule fun_free_blocktype_case_0{valtype_opt : valtype?, var_0_opt : free?}:
    `%%`(_RESULT_blocktype(valtype_opt), $free_opt(var_0_opt))
    -- if ((var_0_opt = ?()) <=> (valtype_opt = ?()))
    -- (fun_free_valtype: `%%`(v_valtype, var_0))?{var_0 <- var_0_opt, v_valtype <- valtype_opt}

  ;; test.spectec:1337.6-1337.21
  rule fun_free_blocktype_case_1{v_typeidx : uN}:
    `%%`(_IDX_blocktype(v_typeidx), $free_typeidx(v_typeidx))

;; test.spectec:1337.6-1337.21
relation free_blocktype_is_wf: `%%`(v_blocktype : blocktype, ret_val : free)
  ;; test.spectec:1337.6-1337.21
  rule free_blocktype_is_wf_0{v_blocktype : blocktype, ret_val : free, var_0 : free}:
    `%%`(v_blocktype, ret_val)
    -- fun_free_blocktype: `%%`(v_blocktype, var_0)
    -- wf_blocktype: `%`(v_blocktype)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1338.1-1338.30
def $free_catch(v_catch : catch) : free
  ;; test.spectec:1350.1-1350.90
  def $free_catch{v_tagidx : uN, v_labelidx : uN}(CATCH_catch(v_tagidx, v_labelidx)) = $free_tagidx(v_tagidx) +++ $free_labelidx(v_labelidx)
  ;; test.spectec:1351.1-1351.94
  def $free_catch{v_tagidx : uN, v_labelidx : uN}(CATCH_REF_catch(v_tagidx, v_labelidx)) = $free_tagidx(v_tagidx) +++ $free_labelidx(v_labelidx)
  ;; test.spectec:1352.1-1352.63
  def $free_catch{v_labelidx : uN}(CATCH_ALL_catch(v_labelidx)) = $free_labelidx(v_labelidx)
  ;; test.spectec:1353.1-1353.67
  def $free_catch{v_labelidx : uN}(CATCH_ALL_REF_catch(v_labelidx)) = $free_labelidx(v_labelidx)

;; test.spectec:1338.6-1338.17
relation free_catch_is_wf: `%%`(v_catch : catch, ret_val : free)
  ;; test.spectec:1338.6-1338.17
  rule free_catch_is_wf_0{v_catch : catch, ret_val : free}:
    `%%`(v_catch, ret_val)
    -- wf_catch: `%`(v_catch)
    -- if (ret_val = $free_catch(v_catch))
    -- wf_free: `%`(ret_val)

;; test.spectec:1504.1-1504.44
rec {

;; test.spectec:1504.6-1504.22
relation fun_shift_labelidxs: `%%`(labelidx*, labelidx*)
  ;; test.spectec:1504.6-1504.22
  rule fun_shift_labelidxs_case_0:
    `%%`([], [])

  ;; test.spectec:1504.6-1504.22
  rule fun_shift_labelidxs_case_1{labelidx'_lst : labelidx*, var_0 : labelidx*}:
    `%%`([mk_uN_labelidx(0)] ++ labelidx'_lst, var_0)
    -- fun_shift_labelidxs: `%%`(labelidx'_lst, var_0)

  ;; test.spectec:1504.6-1504.22
  rule fun_shift_labelidxs_case_2{v_labelidx : uN, labelidx'_lst : labelidx*, var_0 : labelidx*}:
    `%%`([v_labelidx] ++ labelidx'_lst, [mk_uN_labelidx(((($proj_uN_0(v_labelidx).0 : nat <:> int) - (1 : nat <:> int)) : int <:> nat))] ++ var_0)
    -- fun_shift_labelidxs: `%%`(labelidx'_lst, var_0)
}

;; test.spectec:1504.1-1504.44
rec {

;; test.spectec:1504.6-1504.22
relation shift_labelidxs_is_wf: `%%`(var_0_lst : labelidx*, ret_val_lst : labelidx*)
  ;; test.spectec:1504.6-1504.22
  rule shift_labelidxs_is_wf_0{var_0_lst : labelidx*, ret_val_lst : labelidx*, var_0 : labelidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_shift_labelidxs: `%%`(var_0_lst, var_0)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:1340.1-1341.31
rec {

;; test.spectec:1340.6-1340.17
relation fun_free_instr: `%%`(instr, free)
  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_0:
    `%%`(NOP_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_1:
    `%%`(UNREACHABLE_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_2:
    `%%`(DROP_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_3{valtype_lst_opt : valtype*?, var_1_lst_opt : free*?, var_0_opt : free?}:
    `%%`(SELECT_instr(valtype_lst_opt), $free_opt(var_0_opt))
    -- if ((var_1_lst_opt = ?()) <=> (valtype_lst_opt = ?()))
    -- (if (|var_1_lst| = |valtype_lst|))?{var_1_lst <- var_1_lst_opt, valtype_lst <- valtype_lst_opt}
    -- (fun_free_valtype: `%%`(v_valtype, var_1))*{var_1 <- var_1_lst, v_valtype <- valtype_lst}?{var_1_lst <- var_1_lst_opt, valtype_lst <- valtype_lst_opt}
    -- if ((var_1_lst_opt = ?()) <=> (var_0_opt = ?()))
    -- (fun_free_list: `%%`(var_1_lst, var_0))?{var_1_lst <- var_1_lst_opt, var_0 <- var_0_opt}

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_4{v_blocktype : blocktype, instr_lst : instr*, var_1 : free, var_0 : free}:
    `%%`(BLOCK_instr(v_blocktype, instr_lst), var_0 +++ var_1)
    -- fun_free_block: `%%`(instr_lst, var_1)
    -- fun_free_blocktype: `%%`(v_blocktype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_5{v_blocktype : blocktype, instr_lst : instr*, var_1 : free, var_0 : free}:
    `%%`(LOOP_instr(v_blocktype, instr_lst), var_0 +++ var_1)
    -- fun_free_block: `%%`(instr_lst, var_1)
    -- fun_free_blocktype: `%%`(v_blocktype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_6{v_blocktype : blocktype, instr_1_lst : instr*, instr_2_lst : instr*, var_2 : free, var_1 : free, var_0 : free}:
    `%%`(`IF%%ELSE%`_instr(v_blocktype, instr_1_lst, instr_2_lst), var_0 +++ var_1 +++ var_2)
    -- fun_free_block: `%%`(instr_2_lst, var_2)
    -- fun_free_block: `%%`(instr_1_lst, var_1)
    -- fun_free_blocktype: `%%`(v_blocktype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_7{v_labelidx : uN}:
    `%%`(BR_instr(v_labelidx), $free_labelidx(v_labelidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_8{v_labelidx : uN}:
    `%%`(BR_IF_instr(v_labelidx), $free_labelidx(v_labelidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_9{labelidx_lst : labelidx*, labelidx' : uN, var_0 : free}:
    `%%`(BR_TABLE_instr(labelidx_lst, labelidx'), var_0 +++ $free_labelidx(labelidx'))
    -- fun_free_list: `%%`($free_labelidx(v_labelidx)*{v_labelidx <- labelidx_lst}, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_10{v_labelidx : uN}:
    `%%`(BR_ON_NULL_instr(v_labelidx), $free_labelidx(v_labelidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_11{v_labelidx : uN}:
    `%%`(BR_ON_NON_NULL_instr(v_labelidx), $free_labelidx(v_labelidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_12{v_labelidx : uN, reftype_1 : reftype, reftype_2 : reftype, var_1 : free, var_0 : free}:
    `%%`(BR_ON_CAST_instr(v_labelidx, reftype_1, reftype_2), $free_labelidx(v_labelidx) +++ var_0 +++ var_1)
    -- fun_free_reftype: `%%`(reftype_2, var_1)
    -- fun_free_reftype: `%%`(reftype_1, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_13{v_labelidx : uN, reftype_1 : reftype, reftype_2 : reftype, var_1 : free, var_0 : free}:
    `%%`(BR_ON_CAST_FAIL_instr(v_labelidx, reftype_1, reftype_2), $free_labelidx(v_labelidx) +++ var_0 +++ var_1)
    -- fun_free_reftype: `%%`(reftype_2, var_1)
    -- fun_free_reftype: `%%`(reftype_1, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_14{v_funcidx : uN}:
    `%%`(CALL_instr(v_funcidx), $free_funcidx(v_funcidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_15{v_typeuse : typeuse, var_0 : free}:
    `%%`(CALL_REF_instr(v_typeuse), var_0)
    -- fun_free_typeuse: `%%`(v_typeuse, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_16{v_tableidx : uN, v_typeuse : typeuse, var_0 : free}:
    `%%`(CALL_INDIRECT_instr(v_tableidx, v_typeuse), $free_tableidx(v_tableidx) +++ var_0)
    -- fun_free_typeuse: `%%`(v_typeuse, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_17:
    `%%`(RETURN_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_18{v_funcidx : uN}:
    `%%`(RETURN_CALL_instr(v_funcidx), $free_funcidx(v_funcidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_19{v_typeuse : typeuse, var_0 : free}:
    `%%`(RETURN_CALL_REF_instr(v_typeuse), var_0)
    -- fun_free_typeuse: `%%`(v_typeuse, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_20{v_tableidx : uN, v_typeuse : typeuse, var_0 : free}:
    `%%`(RETURN_CALL_INDIRECT_instr(v_tableidx, v_typeuse), $free_tableidx(v_tableidx) +++ var_0)
    -- fun_free_typeuse: `%%`(v_typeuse, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_21{v_tagidx : uN}:
    `%%`(THROW_instr(v_tagidx), $free_tagidx(v_tagidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_22:
    `%%`(THROW_REF_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_23{v_blocktype : blocktype, catch_lst : catch*, instr_lst : instr*, var_3_lst : free*, var_2 : free, var_1 : free, var_0 : free}:
    `%%`(TRY_TABLE_instr(v_blocktype, mk_list_list(catch_lst), instr_lst), var_0 +++ var_1 +++ var_2)
    -- if (|var_3_lst| = |instr_lst|)
    -- (fun_free_instr: `%%`(v_instr, var_3))*{var_3 <- var_3_lst, v_instr <- instr_lst}
    -- fun_free_list: `%%`(var_3_lst, var_2)
    -- fun_free_list: `%%`($free_catch(v_catch)*{v_catch <- catch_lst}, var_1)
    -- fun_free_blocktype: `%%`(v_blocktype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_24{v_numtype : numtype, numlit : num_}:
    `%%`(CONST_instr(v_numtype, numlit), $free_numtype(v_numtype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_25{v_numtype : numtype, unop : unop_}:
    `%%`(UNOP_instr(v_numtype, unop), $free_numtype(v_numtype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_26{v_numtype : numtype, binop : binop_}:
    `%%`(BINOP_instr(v_numtype, binop), $free_numtype(v_numtype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_27{v_numtype : numtype, testop : testop_}:
    `%%`(TESTOP_instr(v_numtype, testop), $free_numtype(v_numtype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_28{v_numtype : numtype, relop : relop_}:
    `%%`(RELOP_instr(v_numtype, relop), $free_numtype(v_numtype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_29{numtype_1 : numtype, numtype_2 : numtype, cvtop : cvtop__}:
    `%%`(CVTOP_instr(numtype_1, numtype_2, cvtop), $free_numtype(numtype_1) +++ $free_numtype(numtype_2))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_30{v_vectype : vectype, veclit : uN}:
    `%%`(VCONST_instr(v_vectype, veclit), $free_vectype(v_vectype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_31{v_vectype : vectype, v_vvunop : vvunop}:
    `%%`(VVUNOP_instr(v_vectype, v_vvunop), $free_vectype(v_vectype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_32{v_vectype : vectype, v_vvbinop : vvbinop}:
    `%%`(VVBINOP_instr(v_vectype, v_vvbinop), $free_vectype(v_vectype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_33{v_vectype : vectype, v_vvternop : vvternop}:
    `%%`(VVTERNOP_instr(v_vectype, v_vvternop), $free_vectype(v_vectype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_34{v_vectype : vectype, v_vvtestop : vvtestop}:
    `%%`(VVTESTOP_instr(v_vectype, v_vvtestop), $free_vectype(v_vectype))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_35{v_shape : shape, vunop : vunop_}:
    `%%`(VUNOP_instr(v_shape, vunop), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_36{v_shape : shape, vbinop : vbinop_}:
    `%%`(VBINOP_instr(v_shape, vbinop), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_37{v_shape : shape, vternop : vternop_}:
    `%%`(VTERNOP_instr(v_shape, vternop), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_38{v_shape : shape, vtestop : vtestop_}:
    `%%`(VTESTOP_instr(v_shape, vtestop), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_39{v_shape : shape, vrelop : vrelop_}:
    `%%`(VRELOP_instr(v_shape, vrelop), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_40{v_ishape : ishape, vshiftop : vshiftop_}:
    `%%`(VSHIFTOP_instr(v_ishape, vshiftop), $free_shape($proj_ishape_0(v_ishape).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_41{v_ishape : ishape}:
    `%%`(VBITMASK_instr(v_ishape), $free_shape($proj_ishape_0(v_ishape).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_42{v_bshape : bshape, vswizzlop : vswizzlop_}:
    `%%`(VSWIZZLOP_instr(v_bshape, vswizzlop), $free_shape($proj_bshape_0(v_bshape).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_43{v_bshape : bshape, laneidx_lst : laneidx*}:
    `%%`(VSHUFFLE_instr(v_bshape, laneidx_lst), $free_shape($proj_bshape_0(v_bshape).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_44{ishape_1 : ishape, ishape_2 : ishape, vextunop : vextunop__}:
    `%%`(VEXTUNOP_instr(ishape_1, ishape_2, vextunop), $free_shape($proj_ishape_0(ishape_1).0) +++ $free_shape($proj_ishape_0(ishape_2).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_45{ishape_1 : ishape, ishape_2 : ishape, vextbinop : vextbinop__}:
    `%%`(VEXTBINOP_instr(ishape_1, ishape_2, vextbinop), $free_shape($proj_ishape_0(ishape_1).0) +++ $free_shape($proj_ishape_0(ishape_2).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_46{ishape_1 : ishape, ishape_2 : ishape, vextternop : vextternop__}:
    `%%`(VEXTTERNOP_instr(ishape_1, ishape_2, vextternop), $free_shape($proj_ishape_0(ishape_1).0) +++ $free_shape($proj_ishape_0(ishape_2).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_47{ishape_1 : ishape, ishape_2 : ishape, v_sx : sx}:
    `%%`(VNARROW_instr(ishape_1, ishape_2, v_sx), $free_shape($proj_ishape_0(ishape_1).0) +++ $free_shape($proj_ishape_0(ishape_2).0))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_48{shape_1 : shape, shape_2 : shape, vcvtop : vcvtop__}:
    `%%`(VCVTOP_instr(shape_1, shape_2, vcvtop), $free_shape(shape_1) +++ $free_shape(shape_2))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_49{v_shape : shape}:
    `%%`(VSPLAT_instr(v_shape), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_50{v_shape : shape, sx_opt : sx?, v_laneidx : uN}:
    `%%`(VEXTRACT_LANE_instr(v_shape, sx_opt, v_laneidx), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_51{v_shape : shape, v_laneidx : uN}:
    `%%`(VREPLACE_LANE_instr(v_shape, v_laneidx), $free_shape(v_shape))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_52{v_heaptype : heaptype, var_0 : free}:
    `%%`(REF_NULL_instr(v_heaptype), var_0)
    -- fun_free_heaptype: `%%`(v_heaptype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_53:
    `%%`(REF_IS_NULL_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_54:
    `%%`(REF_AS_NON_NULL_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_55:
    `%%`(REF_EQ_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_56{v_reftype : reftype, var_0 : free}:
    `%%`(REF_TEST_instr(v_reftype), var_0)
    -- fun_free_reftype: `%%`(v_reftype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_57{v_reftype : reftype, var_0 : free}:
    `%%`(REF_CAST_instr(v_reftype), var_0)
    -- fun_free_reftype: `%%`(v_reftype, var_0)

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_58{v_funcidx : uN}:
    `%%`(REF_FUNC_instr(v_funcidx), $free_funcidx(v_funcidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_59:
    `%%`(REF_I31_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_60{v_sx : sx}:
    `%%`(I31_GET_instr(v_sx), {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_61{v_typeidx : uN}:
    `%%`(STRUCT_NEW_instr(v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_62{v_typeidx : uN}:
    `%%`(STRUCT_NEW_DEFAULT_instr(v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_63{sx_opt : sx?, v_typeidx : uN, v_u32 : uN}:
    `%%`(STRUCT_GET_instr(sx_opt, v_typeidx, v_u32), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_64{v_typeidx : uN, v_u32 : uN}:
    `%%`(STRUCT_SET_instr(v_typeidx, v_u32), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_65{v_typeidx : uN}:
    `%%`(ARRAY_NEW_instr(v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_66{v_typeidx : uN}:
    `%%`(ARRAY_NEW_DEFAULT_instr(v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_67{v_typeidx : uN, v_u32 : uN}:
    `%%`(ARRAY_NEW_FIXED_instr(v_typeidx, v_u32), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_68{v_typeidx : uN, v_dataidx : uN}:
    `%%`(ARRAY_NEW_DATA_instr(v_typeidx, v_dataidx), $free_typeidx(v_typeidx) +++ $free_dataidx(v_dataidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_69{v_typeidx : uN, v_elemidx : uN}:
    `%%`(ARRAY_NEW_ELEM_instr(v_typeidx, v_elemidx), $free_typeidx(v_typeidx) +++ $free_elemidx(v_elemidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_70{sx_opt : sx?, v_typeidx : uN}:
    `%%`(ARRAY_GET_instr(sx_opt, v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_71{v_typeidx : uN}:
    `%%`(ARRAY_SET_instr(v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_72:
    `%%`(ARRAY_LEN_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_73{v_typeidx : uN}:
    `%%`(ARRAY_FILL_instr(v_typeidx), $free_typeidx(v_typeidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_74{typeidx_1 : uN, typeidx_2 : uN}:
    `%%`(ARRAY_COPY_instr(typeidx_1, typeidx_2), $free_typeidx(typeidx_1) +++ $free_typeidx(typeidx_2))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_75{v_typeidx : uN, v_dataidx : uN}:
    `%%`(ARRAY_INIT_DATA_instr(v_typeidx, v_dataidx), $free_typeidx(v_typeidx) +++ $free_dataidx(v_dataidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_76{v_typeidx : uN, v_elemidx : uN}:
    `%%`(ARRAY_INIT_ELEM_instr(v_typeidx, v_elemidx), $free_typeidx(v_typeidx) +++ $free_elemidx(v_elemidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_77:
    `%%`(EXTERN_CONVERT_ANY_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_78:
    `%%`(ANY_CONVERT_EXTERN_instr, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_79{v_localidx : uN}:
    `%%`(LOCAL_GET_instr(v_localidx), $free_localidx(v_localidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_80{v_localidx : uN}:
    `%%`(LOCAL_SET_instr(v_localidx), $free_localidx(v_localidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_81{v_localidx : uN}:
    `%%`(LOCAL_TEE_instr(v_localidx), $free_localidx(v_localidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_82{v_globalidx : uN}:
    `%%`(GLOBAL_GET_instr(v_globalidx), $free_globalidx(v_globalidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_83{v_globalidx : uN}:
    `%%`(GLOBAL_SET_instr(v_globalidx), $free_globalidx(v_globalidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_84{v_tableidx : uN}:
    `%%`(TABLE_GET_instr(v_tableidx), $free_tableidx(v_tableidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_85{v_tableidx : uN}:
    `%%`(TABLE_SET_instr(v_tableidx), $free_tableidx(v_tableidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_86{v_tableidx : uN}:
    `%%`(TABLE_SIZE_instr(v_tableidx), $free_tableidx(v_tableidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_87{v_tableidx : uN}:
    `%%`(TABLE_GROW_instr(v_tableidx), $free_tableidx(v_tableidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_88{v_tableidx : uN}:
    `%%`(TABLE_FILL_instr(v_tableidx), $free_tableidx(v_tableidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_89{tableidx_1 : uN, tableidx_2 : uN}:
    `%%`(TABLE_COPY_instr(tableidx_1, tableidx_2), $free_tableidx(tableidx_1) +++ $free_tableidx(tableidx_2))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_90{v_tableidx : uN, v_elemidx : uN}:
    `%%`(TABLE_INIT_instr(v_tableidx, v_elemidx), $free_tableidx(v_tableidx) +++ $free_elemidx(v_elemidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_91{v_elemidx : uN}:
    `%%`(ELEM_DROP_instr(v_elemidx), $free_elemidx(v_elemidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_92{v_numtype : numtype, loadop_opt : loadop_?, v_memidx : uN, v_memarg : memarg}:
    `%%`(LOAD_instr(v_numtype, loadop_opt, v_memidx, v_memarg), $free_numtype(v_numtype) +++ $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_93{v_numtype : numtype, storeop_opt : storeop_?, v_memidx : uN, v_memarg : memarg}:
    `%%`(STORE_instr(v_numtype, storeop_opt, v_memidx, v_memarg), $free_numtype(v_numtype) +++ $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_94{v_vectype : vectype, vloadop_opt : vloadop_?, v_memidx : uN, v_memarg : memarg}:
    `%%`(VLOAD_instr(v_vectype, vloadop_opt, v_memidx, v_memarg), $free_vectype(v_vectype) +++ $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_95{v_vectype : vectype, v_sz : sz, v_memidx : uN, v_memarg : memarg, v_laneidx : uN}:
    `%%`(VLOAD_LANE_instr(v_vectype, v_sz, v_memidx, v_memarg, v_laneidx), $free_vectype(v_vectype) +++ $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_96{v_vectype : vectype, v_memidx : uN, v_memarg : memarg}:
    `%%`(VSTORE_instr(v_vectype, v_memidx, v_memarg), $free_vectype(v_vectype) +++ $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_97{v_vectype : vectype, v_sz : sz, v_memidx : uN, v_memarg : memarg, v_laneidx : uN}:
    `%%`(VSTORE_LANE_instr(v_vectype, v_sz, v_memidx, v_memarg, v_laneidx), $free_vectype(v_vectype) +++ $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_98{v_memidx : uN}:
    `%%`(MEMORY_SIZE_instr(v_memidx), $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_99{v_memidx : uN}:
    `%%`(MEMORY_GROW_instr(v_memidx), $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_100{v_memidx : uN}:
    `%%`(MEMORY_FILL_instr(v_memidx), $free_memidx(v_memidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_101{memidx_1 : uN, memidx_2 : uN}:
    `%%`(MEMORY_COPY_instr(memidx_1, memidx_2), $free_memidx(memidx_1) +++ $free_memidx(memidx_2))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_102{v_memidx : uN, v_dataidx : uN}:
    `%%`(MEMORY_INIT_instr(v_memidx, v_dataidx), $free_memidx(v_memidx) +++ $free_dataidx(v_dataidx))

  ;; test.spectec:1340.6-1340.17
  rule fun_free_instr_case_103{v_dataidx : uN}:
    `%%`(DATA_DROP_instr(v_dataidx), $free_dataidx(v_dataidx))

;; test.spectec:1341.6-1341.17
relation fun_free_block: `%%`(instr*, free)
  ;; test.spectec:1341.6-1341.17
  rule fun_free_block_case_0{instr_lst : instr*, v_free : free, var_2_lst : free*, var_1 : free, var_0 : labelidx*}:
    `%%`(instr_lst, v_free[LABELS_free = var_0])
    -- if (|var_2_lst| = |instr_lst|)
    -- (fun_free_instr: `%%`(instr_5, var_2))*{var_2 <- var_2_lst, instr_5 <- instr_lst}
    -- fun_free_list: `%%`(var_2_lst, var_1)
    -- fun_shift_labelidxs: `%%`(v_free.LABELS_free, var_0)
    -- if (v_free = var_1)
}

;; test.spectec:1340.1-1341.31
rec {

;; test.spectec:1340.6-1340.17
relation free_instr_is_wf: `%%`(v_instr : instr, ret_val : free)
  ;; test.spectec:1340.6-1340.17
  rule free_instr_is_wf_0{v_instr : instr, ret_val : free, var_0 : free}:
    `%%`(v_instr, ret_val)
    -- fun_free_instr: `%%`(v_instr, var_0)
    -- wf_instr: `%`(v_instr)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1341.6-1341.17
relation free_block_is_wf: `%%`(var_0_lst : instr*, ret_val : free)
  ;; test.spectec:1341.6-1341.17
  rule free_block_is_wf_0{var_0_lst : instr*, ret_val : free, var_0 : free}:
    `%%`(var_0_lst, ret_val)
    -- fun_free_block: `%%`(var_0_lst, var_0)
    -- (wf_instr: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)
}

;; test.spectec:1342.6-1342.16
relation fun_free_expr: `%%`(expr, free)
  ;; test.spectec:1342.6-1342.16
  rule fun_free_expr_case_0{instr_lst : instr*, var_1_lst : free*, var_0 : free}:
    `%%`(instr_lst, var_0)
    -- if (|var_1_lst| = |instr_lst|)
    -- (fun_free_instr: `%%`(v_instr, var_1))*{var_1 <- var_1_lst, v_instr <- instr_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:1342.6-1342.16
relation free_expr_is_wf: `%%`(v_expr : expr, ret_val : free)
  ;; test.spectec:1342.6-1342.16
  rule free_expr_is_wf_0{v_expr : expr, ret_val : free, var_0 : free}:
    `%%`(v_expr, ret_val)
    -- fun_free_expr: `%%`(v_expr, var_0)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1526.1-1527.43
syntax elemmode = 
  | ACTIVE(v_tableidx : tableidx, v_expr : expr)
  | PASSIVE
  | DECLARE

;; test.spectec:1526.8-1526.16
relation wf_elemmode: `%`(elemmode)
  ;; test.spectec:1526.8-1526.16
  rule elemmode_case_0{v_tableidx : tableidx, v_expr : expr}:
    `%`(ACTIVE_elemmode(v_tableidx, v_expr))
    -- wf_uN: `%%`(32, v_tableidx)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

  ;; test.spectec:1526.8-1526.16
  rule elemmode_case_1:
    `%`(PASSIVE_elemmode)

  ;; test.spectec:1526.8-1526.16
  rule elemmode_case_2:
    `%`(DECLARE_elemmode)

;; test.spectec:1528.1-1529.31
syntax datamode = 
  | ACTIVE(v_memidx : memidx, v_expr : expr)
  | PASSIVE

;; test.spectec:1528.8-1528.16
relation wf_datamode: `%`(datamode)
  ;; test.spectec:1528.8-1528.16
  rule datamode_case_0{v_memidx : memidx, v_expr : expr}:
    `%`(ACTIVE_datamode(v_memidx, v_expr))
    -- wf_uN: `%%`(32, v_memidx)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

  ;; test.spectec:1528.8-1528.16
  rule datamode_case_1:
    `%`(PASSIVE_datamode)

;; test.spectec:1531.1-1532.15
syntax type = 
  | TYPE(v_rectype : rectype)

;; test.spectec:1534.1-1535.14
syntax tag = 
  | TAG(v_tagtype : tagtype)

;; test.spectec:1534.8-1534.11
relation wf_tag: `%`(tag)
  ;; test.spectec:1534.8-1534.11
  rule tag_case_0{v_tagtype : tagtype}:
    `%`(TAG_tag(v_tagtype))
    -- wf_typeuse: `%`(v_tagtype)

;; test.spectec:1537.1-1538.25
syntax global = 
  | GLOBAL(v_globaltype : globaltype, v_expr : expr)

;; test.spectec:1537.8-1537.14
relation wf_global: `%`(global)
  ;; test.spectec:1537.8-1537.14
  rule global_case_0{v_globaltype : globaltype, v_expr : expr}:
    `%`(GLOBAL_global(v_globaltype, v_expr))
    -- wf_globaltype: `%`(v_globaltype)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; test.spectec:1540.1-1541.17
syntax mem = 
  | MEMORY(v_memtype : memtype)

;; test.spectec:1540.8-1540.11
relation wf_mem: `%`(mem)
  ;; test.spectec:1540.8-1540.11
  rule mem_case_0{v_memtype : memtype}:
    `%`(MEMORY_mem(v_memtype))
    -- wf_memtype: `%`(v_memtype)

;; test.spectec:1543.1-1544.23
syntax table = 
  | TABLE(v_tabletype : tabletype, v_expr : expr)

;; test.spectec:1543.8-1543.13
relation wf_table: `%`(table)
  ;; test.spectec:1543.8-1543.13
  rule table_case_0{v_tabletype : tabletype, v_expr : expr}:
    `%`(TABLE_table(v_tabletype, v_expr))
    -- wf_tabletype: `%`(v_tabletype)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; test.spectec:1546.1-1547.22
syntax data = 
  | DATA(byte_lst : byte*, v_datamode : datamode)

;; test.spectec:1546.8-1546.12
relation wf_data: `%`(data)
  ;; test.spectec:1546.8-1546.12
  rule data_case_0{byte_lst : byte*, v_datamode : datamode}:
    `%`(DATA_data(byte_lst, v_datamode))
    -- (wf_byte: `%`(v_byte))*{v_byte <- byte_lst}
    -- wf_datamode: `%`(v_datamode)

;; test.spectec:1549.1-1550.16
syntax local = 
  | LOCAL(v_valtype : valtype)

;; test.spectec:1549.8-1549.13
relation wf_local: `%`(local)
  ;; test.spectec:1549.8-1549.13
  rule local_case_0{v_valtype : valtype}:
    `%`(LOCAL_local(v_valtype))
    -- wf_valtype: `%`(v_valtype)

;; test.spectec:1552.1-1553.27
syntax func = 
  | FUNC(v_typeidx : typeidx, local_lst : local*, v_expr : expr)

;; test.spectec:1552.8-1552.12
relation wf_func: `%`(func)
  ;; test.spectec:1552.8-1552.12
  rule func_case_0{v_typeidx : typeidx, local_lst : local*, v_expr : expr}:
    `%`(FUNC_func(v_typeidx, local_lst, v_expr))
    -- wf_uN: `%%`(32, v_typeidx)
    -- (wf_local: `%`(v_local))*{v_local <- local_lst}
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; test.spectec:1555.1-1556.30
syntax elem = 
  | ELEM(v_reftype : reftype, expr_lst : expr*, v_elemmode : elemmode)

;; test.spectec:1555.8-1555.12
relation wf_elem: `%`(elem)
  ;; test.spectec:1555.8-1555.12
  rule elem_case_0{v_reftype : reftype, expr_lst : expr*, v_elemmode : elemmode}:
    `%`(ELEM_elem(v_reftype, expr_lst, v_elemmode))
    -- wf_reftype: `%`(v_reftype)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}*{v_expr <- expr_lst}
    -- wf_elemmode: `%`(v_elemmode)

;; test.spectec:1558.1-1559.16
syntax start = 
  | START(v_funcidx : funcidx)

;; test.spectec:1558.8-1558.13
relation wf_start: `%`(start)
  ;; test.spectec:1558.8-1558.13
  rule start_case_0{v_funcidx : funcidx}:
    `%`(START_start(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

;; test.spectec:1561.1-1562.30
syntax import = 
  | IMPORT(v_name : name, v_name : name, v_externtype : externtype)

;; test.spectec:1561.8-1561.14
relation wf_import: `%`(import)
  ;; test.spectec:1561.8-1561.14
  rule import_case_0{v_name : name, name_0 : name, v_externtype : externtype}:
    `%`(IMPORT_import(v_name, name_0, v_externtype))
    -- wf_name: `%`(v_name)
    -- wf_name: `%`(name_0)
    -- wf_externtype: `%`(v_externtype)

;; test.spectec:1564.1-1565.24
syntax export = 
  | EXPORT(v_name : name, v_externidx : externidx)

;; test.spectec:1564.8-1564.14
relation wf_export: `%`(export)
  ;; test.spectec:1564.8-1564.14
  rule export_case_0{v_name : name, v_externidx : externidx}:
    `%`(EXPORT_export(v_name, v_externidx))
    -- wf_name: `%`(v_name)
    -- wf_externidx: `%`(v_externidx)

;; test.spectec:1567.1-1579.17
syntax module = 
  | MODULE(list(syntax type), list(syntax import), list(syntax tag), list(syntax global), list(syntax mem), list(syntax table), list(syntax func), list(syntax data), list(syntax elem), start_opt : start?, list(syntax export))

;; test.spectec:1567.8-1567.14
relation wf_module: `%`(module)
  ;; test.spectec:1567.8-1567.14
  rule module_case_0{var_0 : list(syntax type), var_1 : list(syntax import), var_2 : list(syntax tag), var_3 : list(syntax global), var_4 : list(syntax mem), var_5 : list(syntax table), var_6 : list(syntax func), var_7 : list(syntax data), var_8 : list(syntax elem), start_opt : start?, var_9 : list(syntax export)}:
    `%`(MODULE_module(var_0, var_1, var_2, var_3, var_4, var_5, var_6, var_7, var_8, start_opt, var_9))
    -- (wf_start: `%`(v_start))?{v_start <- start_opt}

;; test.spectec:1594.6-1594.16
relation fun_free_type: `%%`(type, free)
  ;; test.spectec:1594.6-1594.16
  rule fun_free_type_case_0{v_rectype : rectype, var_0 : free}:
    `%%`(TYPE_type(v_rectype), var_0)
    -- fun_free_rectype: `%%`(v_rectype, var_0)

;; test.spectec:1594.6-1594.16
relation free_type_is_wf: `%%`(v_type : type, ret_val : free)
  ;; test.spectec:1594.6-1594.16
  rule free_type_is_wf_0{v_type : type, ret_val : free, var_0 : free}:
    `%%`(v_type, ret_val)
    -- fun_free_type: `%%`(v_type, var_0)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1595.6-1595.15
relation fun_free_tag: `%%`(tag, free)
  ;; test.spectec:1595.6-1595.15
  rule fun_free_tag_case_0{v_tagtype : typeuse, var_0 : free}:
    `%%`(TAG_tag(v_tagtype), var_0)
    -- fun_free_tagtype: `%%`(v_tagtype, var_0)

;; test.spectec:1595.6-1595.15
relation free_tag_is_wf: `%%`(v_tag : tag, ret_val : free)
  ;; test.spectec:1595.6-1595.15
  rule free_tag_is_wf_0{v_tag : tag, ret_val : free, var_0 : free}:
    `%%`(v_tag, ret_val)
    -- fun_free_tag: `%%`(v_tag, var_0)
    -- wf_tag: `%`(v_tag)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1596.6-1596.18
relation fun_free_global: `%%`(global, free)
  ;; test.spectec:1596.6-1596.18
  rule fun_free_global_case_0{v_globaltype : globaltype, v_expr : instr*, var_1 : free, var_0 : free}:
    `%%`(GLOBAL_global(v_globaltype, v_expr), var_0 +++ var_1)
    -- fun_free_expr: `%%`(v_expr, var_1)
    -- fun_free_globaltype: `%%`(v_globaltype, var_0)

;; test.spectec:1596.6-1596.18
relation free_global_is_wf: `%%`(v_global : global, ret_val : free)
  ;; test.spectec:1596.6-1596.18
  rule free_global_is_wf_0{v_global : global, ret_val : free, var_0 : free}:
    `%%`(v_global, ret_val)
    -- fun_free_global: `%%`(v_global, var_0)
    -- wf_global: `%`(v_global)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1597.1-1597.26
def $free_mem(v_mem : mem) : free
  ;; test.spectec:1618.1-1618.55
  def $free_mem{v_memtype : memtype}(MEMORY_mem(v_memtype)) = $free_memtype(v_memtype)

;; test.spectec:1597.6-1597.15
relation free_mem_is_wf: `%%`(v_mem : mem, ret_val : free)
  ;; test.spectec:1597.6-1597.15
  rule free_mem_is_wf_0{v_mem : mem, ret_val : free}:
    `%%`(v_mem, ret_val)
    -- wf_mem: `%`(v_mem)
    -- if (ret_val = $free_mem(v_mem))
    -- wf_free: `%`(ret_val)

;; test.spectec:1598.6-1598.17
relation fun_free_table: `%%`(table, free)
  ;; test.spectec:1598.6-1598.17
  rule fun_free_table_case_0{v_tabletype : tabletype, v_expr : instr*, var_1 : free, var_0 : free}:
    `%%`(TABLE_table(v_tabletype, v_expr), var_0 +++ var_1)
    -- fun_free_expr: `%%`(v_expr, var_1)
    -- fun_free_tabletype: `%%`(v_tabletype, var_0)

;; test.spectec:1598.6-1598.17
relation free_table_is_wf: `%%`(v_table : table, ret_val : free)
  ;; test.spectec:1598.6-1598.17
  rule free_table_is_wf_0{v_table : table, ret_val : free, var_0 : free}:
    `%%`(v_table, ret_val)
    -- fun_free_table: `%%`(v_table, var_0)
    -- wf_table: `%`(v_table)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1599.6-1599.17
relation fun_free_local: `%%`(local, free)
  ;; test.spectec:1599.6-1599.17
  rule fun_free_local_case_0{t : valtype, var_0 : free}:
    `%%`(LOCAL_local(t), var_0)
    -- fun_free_valtype: `%%`(t, var_0)

;; test.spectec:1599.6-1599.17
relation free_local_is_wf: `%%`(v_local : local, ret_val : free)
  ;; test.spectec:1599.6-1599.17
  rule free_local_is_wf_0{v_local : local, ret_val : free, var_0 : free}:
    `%%`(v_local, ret_val)
    -- fun_free_local: `%%`(v_local, var_0)
    -- wf_local: `%`(v_local)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1600.6-1600.16
relation fun_free_func: `%%`(func, free)
  ;; test.spectec:1600.6-1600.16
  rule fun_free_func_case_0{v_typeidx : uN, local_lst : local*, v_expr : instr*, var_2 : free, var_1_lst : free*, var_0 : free}:
    `%%`(FUNC_func(v_typeidx, local_lst, v_expr), $free_typeidx(v_typeidx) +++ var_0 +++ var_2[LOCALS_free = []])
    -- fun_free_block: `%%`(v_expr, var_2)
    -- if (|var_1_lst| = |local_lst|)
    -- (fun_free_local: `%%`(v_local, var_1))*{var_1 <- var_1_lst, v_local <- local_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:1600.6-1600.16
relation free_func_is_wf: `%%`(v_func : func, ret_val : free)
  ;; test.spectec:1600.6-1600.16
  rule free_func_is_wf_0{v_func : func, ret_val : free, var_0 : free}:
    `%%`(v_func, ret_val)
    -- fun_free_func: `%%`(v_func, var_0)
    -- wf_func: `%`(v_func)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1603.6-1603.20
relation fun_free_datamode: `%%`(datamode, free)
  ;; test.spectec:1603.6-1603.20
  rule fun_free_datamode_case_0{v_memidx : uN, v_expr : instr*, var_0 : free}:
    `%%`(ACTIVE_datamode(v_memidx, v_expr), $free_memidx(v_memidx) +++ var_0)
    -- fun_free_expr: `%%`(v_expr, var_0)

  ;; test.spectec:1603.6-1603.20
  rule fun_free_datamode_case_1:
    `%%`(PASSIVE_datamode, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

;; test.spectec:1603.6-1603.20
relation free_datamode_is_wf: `%%`(v_datamode : datamode, ret_val : free)
  ;; test.spectec:1603.6-1603.20
  rule free_datamode_is_wf_0{v_datamode : datamode, ret_val : free, var_0 : free}:
    `%%`(v_datamode, ret_val)
    -- fun_free_datamode: `%%`(v_datamode, var_0)
    -- wf_datamode: `%`(v_datamode)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1601.6-1601.16
relation fun_free_data: `%%`(data, free)
  ;; test.spectec:1601.6-1601.16
  rule fun_free_data_case_0{byte_lst : byte*, v_datamode : datamode, var_0 : free}:
    `%%`(DATA_data(byte_lst, v_datamode), var_0)
    -- fun_free_datamode: `%%`(v_datamode, var_0)

;; test.spectec:1601.6-1601.16
relation free_data_is_wf: `%%`(v_data : data, ret_val : free)
  ;; test.spectec:1601.6-1601.16
  rule free_data_is_wf_0{v_data : data, ret_val : free, var_0 : free}:
    `%%`(v_data, ret_val)
    -- fun_free_data: `%%`(v_data, var_0)
    -- wf_data: `%`(v_data)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1604.6-1604.20
relation fun_free_elemmode: `%%`(elemmode, free)
  ;; test.spectec:1604.6-1604.20
  rule fun_free_elemmode_case_0{v_tableidx : uN, v_expr : instr*, var_0 : free}:
    `%%`(ACTIVE_elemmode(v_tableidx, v_expr), $free_tableidx(v_tableidx) +++ var_0)
    -- fun_free_expr: `%%`(v_expr, var_0)

  ;; test.spectec:1604.6-1604.20
  rule fun_free_elemmode_case_1:
    `%%`(PASSIVE_elemmode, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

  ;; test.spectec:1604.6-1604.20
  rule fun_free_elemmode_case_2:
    `%%`(DECLARE_elemmode, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []})

;; test.spectec:1604.6-1604.20
relation free_elemmode_is_wf: `%%`(v_elemmode : elemmode, ret_val : free)
  ;; test.spectec:1604.6-1604.20
  rule free_elemmode_is_wf_0{v_elemmode : elemmode, ret_val : free, var_0 : free}:
    `%%`(v_elemmode, ret_val)
    -- fun_free_elemmode: `%%`(v_elemmode, var_0)
    -- wf_elemmode: `%`(v_elemmode)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1602.6-1602.16
relation fun_free_elem: `%%`(elem, free)
  ;; test.spectec:1602.6-1602.16
  rule fun_free_elem_case_0{v_reftype : reftype, expr_lst : expr*, v_elemmode : elemmode, var_3 : free, var_2_lst : free*, var_1 : free, var_0 : free}:
    `%%`(ELEM_elem(v_reftype, expr_lst, v_elemmode), var_0 +++ var_1 +++ var_3)
    -- fun_free_elemmode: `%%`(v_elemmode, var_3)
    -- if (|var_2_lst| = |expr_lst|)
    -- (fun_free_expr: `%%`(v_expr, var_2))*{var_2 <- var_2_lst, v_expr <- expr_lst}
    -- fun_free_list: `%%`(var_2_lst, var_1)
    -- fun_free_reftype: `%%`(v_reftype, var_0)

;; test.spectec:1602.6-1602.16
relation free_elem_is_wf: `%%`(v_elem : elem, ret_val : free)
  ;; test.spectec:1602.6-1602.16
  rule free_elem_is_wf_0{v_elem : elem, ret_val : free, var_0 : free}:
    `%%`(v_elem, ret_val)
    -- fun_free_elem: `%%`(v_elem, var_0)
    -- wf_elem: `%`(v_elem)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1605.1-1605.30
def $free_start(v_start : start) : free
  ;; test.spectec:1642.1-1642.56
  def $free_start{v_funcidx : uN}(START_start(v_funcidx)) = $free_funcidx(v_funcidx)

;; test.spectec:1605.6-1605.17
relation free_start_is_wf: `%%`(v_start : start, ret_val : free)
  ;; test.spectec:1605.6-1605.17
  rule free_start_is_wf_0{v_start : start, ret_val : free}:
    `%%`(v_start, ret_val)
    -- wf_start: `%`(v_start)
    -- if (ret_val = $free_start(v_start))
    -- wf_free: `%`(ret_val)

;; test.spectec:1606.6-1606.18
relation fun_free_import: `%%`(import, free)
  ;; test.spectec:1606.6-1606.18
  rule fun_free_import_case_0{name_1 : name, name_2 : name, v_externtype : externtype, var_0 : free}:
    `%%`(IMPORT_import(name_1, name_2, v_externtype), var_0)
    -- fun_free_externtype: `%%`(v_externtype, var_0)

;; test.spectec:1606.6-1606.18
relation free_import_is_wf: `%%`(v_import : import, ret_val : free)
  ;; test.spectec:1606.6-1606.18
  rule free_import_is_wf_0{v_import : import, ret_val : free, var_0 : free}:
    `%%`(v_import, ret_val)
    -- fun_free_import: `%%`(v_import, var_0)
    -- wf_import: `%`(v_import)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1607.1-1607.32
def $free_export(v_export : export) : free
  ;; test.spectec:1646.1-1646.69
  def $free_export{v_name : name, v_externidx : externidx}(EXPORT_export(v_name, v_externidx)) = $free_externidx(v_externidx)

;; test.spectec:1607.6-1607.18
relation free_export_is_wf: `%%`(v_export : export, ret_val : free)
  ;; test.spectec:1607.6-1607.18
  rule free_export_is_wf_0{v_export : export, ret_val : free}:
    `%%`(v_export, ret_val)
    -- wf_export: `%`(v_export)
    -- if (ret_val = $free_export(v_export))
    -- wf_free: `%`(ret_val)

;; test.spectec:1608.6-1608.18
relation fun_free_module: `%%`(module, free)
  ;; test.spectec:1608.6-1608.18
  rule fun_free_module_case_0{type_lst : type*, import_lst : import*, tag_lst : tag*, global_lst : global*, mem_lst : mem*, table_lst : table*, func_lst : func*, data_lst : data*, elem_lst : elem*, start_opt : start?, export_lst : export*, var_17 : free, var_16_lst : free*, var_15 : free, var_14_lst : free*, var_13 : free, var_12_lst : free*, var_11 : free, var_10_lst : free*, var_9 : free, var_8_lst : free*, var_7 : free, var_6 : free, var_5_lst : free*, var_4 : free, var_3_lst : free*, var_2 : free, var_1_lst : free*, var_0 : free}:
    `%%`(MODULE_module(mk_list_list(type_lst), mk_list_list(import_lst), mk_list_list(tag_lst), mk_list_list(global_lst), mk_list_list(mem_lst), mk_list_list(table_lst), mk_list_list(func_lst), mk_list_list(data_lst), mk_list_list(elem_lst), start_opt, mk_list_list(export_lst)), var_0 +++ var_2 +++ var_4 +++ var_6 +++ var_7 +++ var_9 +++ var_11 +++ var_13 +++ $free_opt($free_start(v_start)?{v_start <- start_opt}) +++ var_15 +++ var_17)
    -- fun_free_list: `%%`($free_export(v_export)*{v_export <- export_lst}, var_17)
    -- if (|var_16_lst| = |import_lst|)
    -- (fun_free_import: `%%`(v_import, var_16))*{var_16 <- var_16_lst, v_import <- import_lst}
    -- fun_free_list: `%%`(var_16_lst, var_15)
    -- if (|var_14_lst| = |elem_lst|)
    -- (fun_free_elem: `%%`(v_elem, var_14))*{var_14 <- var_14_lst, v_elem <- elem_lst}
    -- fun_free_list: `%%`(var_14_lst, var_13)
    -- if (|var_12_lst| = |data_lst|)
    -- (fun_free_data: `%%`(v_data, var_12))*{var_12 <- var_12_lst, v_data <- data_lst}
    -- fun_free_list: `%%`(var_12_lst, var_11)
    -- if (|var_10_lst| = |func_lst|)
    -- (fun_free_func: `%%`(v_func, var_10))*{var_10 <- var_10_lst, v_func <- func_lst}
    -- fun_free_list: `%%`(var_10_lst, var_9)
    -- if (|var_8_lst| = |table_lst|)
    -- (fun_free_table: `%%`(v_table, var_8))*{var_8 <- var_8_lst, v_table <- table_lst}
    -- fun_free_list: `%%`(var_8_lst, var_7)
    -- fun_free_list: `%%`($free_mem(v_mem)*{v_mem <- mem_lst}, var_6)
    -- if (|var_5_lst| = |global_lst|)
    -- (fun_free_global: `%%`(v_global, var_5))*{var_5 <- var_5_lst, v_global <- global_lst}
    -- fun_free_list: `%%`(var_5_lst, var_4)
    -- if (|var_3_lst| = |tag_lst|)
    -- (fun_free_tag: `%%`(v_tag, var_3))*{var_3 <- var_3_lst, v_tag <- tag_lst}
    -- fun_free_list: `%%`(var_3_lst, var_2)
    -- if (|var_1_lst| = |type_lst|)
    -- (fun_free_type: `%%`(v_type, var_1))*{var_1 <- var_1_lst, v_type <- type_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:1608.6-1608.18
relation free_module_is_wf: `%%`(v_module : module, ret_val : free)
  ;; test.spectec:1608.6-1608.18
  rule free_module_is_wf_0{v_module : module, ret_val : free, var_0 : free}:
    `%%`(v_module, ret_val)
    -- fun_free_module: `%%`(v_module, var_0)
    -- wf_module: `%`(v_module)
    -- if (ret_val = var_0)
    -- wf_free: `%`(ret_val)

;; test.spectec:1662.6-1662.21
relation fun_funcidx_module: `%%`(module, funcidx*)
  ;; test.spectec:1662.6-1662.21
  rule fun_funcidx_module_case_0{v_module : module, var_0 : free}:
    `%%`(v_module, var_0.FUNCS_free)
    -- fun_free_module: `%%`(v_module, var_0)

;; test.spectec:1662.6-1662.21
relation funcidx_module_is_wf: `%%`(v_module : module, ret_val_lst : funcidx*)
  ;; test.spectec:1662.6-1662.21
  rule funcidx_module_is_wf_0{v_module : module, ret_val_lst : funcidx*, var_0 : funcidx*}:
    `%%`(v_module, ret_val_lst)
    -- fun_funcidx_module: `%%`(v_module, var_0)
    -- wf_module: `%`(v_module)
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:1665.6-1665.20
relation fun_dataidx_funcs: `%%`(func*, dataidx*)
  ;; test.spectec:1665.6-1665.20
  rule fun_dataidx_funcs_case_0{func_lst : func*, var_1_lst : free*, var_0 : free}:
    `%%`(func_lst, var_0.DATAS_free)
    -- if (|var_1_lst| = |func_lst|)
    -- (fun_free_func: `%%`(v_func, var_1))*{var_1 <- var_1_lst, v_func <- func_lst}
    -- fun_free_list: `%%`(var_1_lst, var_0)

;; test.spectec:1665.6-1665.20
relation dataidx_funcs_is_wf: `%%`(var_0_lst : func*, ret_val_lst : dataidx*)
  ;; test.spectec:1665.6-1665.20
  rule dataidx_funcs_is_wf_0{var_0_lst : func*, ret_val_lst : dataidx*, var_0 : dataidx*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_dataidx_funcs: `%%`(var_0_lst, var_0)
    -- (wf_func: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:1682.1-1683.16
syntax init = 
  | SET
  | UNSET

;; test.spectec:1685.1-1686.15
syntax localtype = 
  | mk_localtype(v_init : init, v_valtype : valtype)

;; test.spectec:1685.8-1685.17
relation wf_localtype: `%`(localtype)
  ;; test.spectec:1685.8-1685.17
  rule localtype_case_0{v_init : init, v_valtype : valtype}:
    `%`(mk_localtype_localtype(v_init, v_valtype))
    -- wf_valtype: `%`(v_valtype)

;; test.spectec:1688.1-1689.57
syntax instrtype = 
  | mk_instrtype(v_resulttype : resulttype, localidx_lst : localidx*, v_resulttype : resulttype)

;; test.spectec:1688.8-1688.17
relation wf_instrtype: `%`(instrtype)
  ;; test.spectec:1688.8-1688.17
  rule instrtype_case_0{v_resulttype : resulttype, localidx_lst : localidx*, resulttype_0 : resulttype}:
    `%`(mk_instrtype_instrtype(v_resulttype, localidx_lst, resulttype_0))
    -- (wf_uN: `%%`(32, v_localidx))*{v_localidx <- localidx_lst}

;; test.spectec:1714.1-1715.58
syntax context = 
{
  TYPES deftype*,
  TAGS tagtype*,
  GLOBALS globaltype*,
  MEMS memtype*,
  TABLES tabletype*,
  FUNCS deftype*,
  DATAS datatype*,
  ELEMS elemtype*,
  LOCALS localtype*,
  LABELS resulttype*,
  RETURN resulttype?,
  REFS funcidx*,
  RECS subtype*
}

;; test.spectec:1714.8-1714.15
relation wf_context: `%`(context)
  ;; test.spectec:1714.8-1714.15
  rule context_case_{var_0_lst : deftype*, var_1_lst : tagtype*, var_2_lst : globaltype*, var_3_lst : memtype*, var_4_lst : tabletype*, var_5_lst : deftype*, var_6_lst : datatype*, var_7_lst : elemtype*, var_8_lst : localtype*, var_9_lst : resulttype*, var_10_opt : resulttype?, var_11_lst : funcidx*, var_12_lst : subtype*}:
    `%`({TYPES var_0_lst, TAGS var_1_lst, GLOBALS var_2_lst, MEMS var_3_lst, TABLES var_4_lst, FUNCS var_5_lst, DATAS var_6_lst, ELEMS var_7_lst, LOCALS var_8_lst, LABELS var_9_lst, RETURN var_10_opt, REFS var_11_lst, RECS var_12_lst})
    -- (wf_typeuse: `%`(var_1))*{var_1 <- var_1_lst}
    -- (wf_globaltype: `%`(var_2))*{var_2 <- var_2_lst}
    -- (wf_memtype: `%`(var_3))*{var_3 <- var_3_lst}
    -- (wf_tabletype: `%`(var_4))*{var_4 <- var_4_lst}
    -- (wf_reftype: `%`(var_7))*{var_7 <- var_7_lst}
    -- (wf_localtype: `%`(var_8))*{var_8 <- var_8_lst}
    -- (wf_uN: `%%`(32, var_11))*{var_11 <- var_11_lst}
    -- (wf_subtype: `%`(var_12))*{var_12 <- var_12_lst}

;; test.spectec:1723.6-1723.18
relation fun_with_locals_before_fun_with_locals_case_2: `%%%`(context, localidx*, localtype*)
  ;; test.spectec:1723.6-1723.18
  rule fun_with_locals_case_1{C : context, x_1 : uN, x_lst : idx*, lct_1 : localtype, lct_lst : localtype*, var_0 : context?}:
    `%%%`(C, [x_1] ++ x_lst, [lct_1] ++ lct_lst)

  ;; test.spectec:1723.6-1723.18
  rule fun_with_locals_case_0{C : context}:
    `%%%`(C, [], [])

;; test.spectec:1723.1-1723.158
rec {

;; test.spectec:1723.6-1723.18
relation fun_with_locals: `%%%%`(context, localidx*, localtype*, context?)
  ;; test.spectec:1723.6-1723.18
  rule fun_with_locals_case_0{C : context}:
    `%%%%`(C, [], [], ?(C))

  ;; test.spectec:1723.6-1723.18
  rule fun_with_locals_case_1{C : context, x_1 : uN, x_lst : idx*, lct_1 : localtype, lct_lst : localtype*, var_0 : context?}:
    `%%%%`(C, [x_1] ++ x_lst, [lct_1] ++ lct_lst, var_0)
    -- fun_with_locals: `%%%%`(C[LOCALS_context[$proj_uN_0(x_1).0] = lct_1], x_lst, lct_lst, var_0)

  ;; test.spectec:1723.6-1723.18
  rule fun_with_locals_case_2{x0 : context, x1 : localidx*, x2 : localtype*}:
    `%%%%`(x0, x1, x2, ?())
    -- ~ fun_with_locals_before_fun_with_locals_case_2: `%%%`(x0, x1, x2)
}

;; test.spectec:1723.1-1723.158
rec {

;; test.spectec:1723.6-1723.18
relation with_locals_is_wf: `%%%%`(v_context : context, var_0_lst : localidx*, var_1_lst : localtype*, ret_val : context)
  ;; test.spectec:1723.6-1723.18
  rule with_locals_is_wf_0{v_context : context, var_0_lst : localidx*, var_1_lst : localtype*, ret_val : context, var_0 : context?}:
    `%%%%`(v_context, var_0_lst, var_1_lst, ret_val)
    -- fun_with_locals: `%%%%`(v_context, var_0_lst, var_1_lst, var_0)
    -- wf_context: `%`(v_context)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- var_0_lst}
    -- (wf_localtype: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (var_0 =/= ?())
    -- if (ret_val = !(var_0))
    -- wf_context: `%`(ret_val)
}

;; test.spectec:1736.1-1736.94
rec {

;; test.spectec:1736.6-1736.20
relation fun_clos_deftypes: `%%`(deftype*, deftype*)
  ;; test.spectec:1736.6-1736.20
  rule fun_clos_deftypes_case_0:
    `%%`([], [])

  ;; test.spectec:1736.6-1736.20
  rule fun_clos_deftypes_case_1{dt_lst : deftype*, dt_n : deftype, dt'_lst : deftype*, var_1 : deftype*, var_0 : deftype}:
    `%%`(dt_lst ++ [dt_n], dt'_lst ++ [var_0])
    -- fun_clos_deftypes: `%%`(dt_lst, var_1)
    -- fun_subst_all_deftype: `%%%`(dt_n, $typeuse_deftype(dt')*{dt' <- dt'_lst}, var_0)
    -- if (dt'_lst = var_1)
}

;; test.spectec:1731.6-1731.19
relation fun_clos_valtype: `%%%`(context, valtype, valtype)
  ;; test.spectec:1731.6-1731.19
  rule fun_clos_valtype_case_0{C : context, t : valtype, dt_lst : deftype*, var_1 : deftype*, var_0 : valtype}:
    `%%%`(C, t, var_0)
    -- fun_clos_deftypes: `%%`(C.TYPES_context, var_1)
    -- fun_subst_all_valtype: `%%%`(t, $typeuse_deftype(dt)*{dt <- dt_lst}, var_0)
    -- if (dt_lst = var_1)

;; test.spectec:1731.6-1731.19
relation clos_valtype_is_wf: `%%%`(v_context : context, v_valtype : valtype, ret_val : valtype)
  ;; test.spectec:1731.6-1731.19
  rule clos_valtype_is_wf_0{v_context : context, v_valtype : valtype, ret_val : valtype, var_0 : valtype}:
    `%%%`(v_context, v_valtype, ret_val)
    -- fun_clos_valtype: `%%%`(v_context, v_valtype, var_0)
    -- wf_context: `%`(v_context)
    -- wf_valtype: `%`(v_valtype)
    -- if (ret_val = var_0)
    -- wf_valtype: `%`(ret_val)

;; test.spectec:1732.6-1732.19
relation fun_clos_deftype: `%%%`(context, deftype, deftype)
  ;; test.spectec:1732.6-1732.19
  rule fun_clos_deftype_case_0{C : context, dt : deftype, dt'_lst : deftype*, var_1 : deftype*, var_0 : deftype}:
    `%%%`(C, dt, var_0)
    -- fun_clos_deftypes: `%%`(C.TYPES_context, var_1)
    -- fun_subst_all_deftype: `%%%`(dt, $typeuse_deftype(dt')*{dt' <- dt'_lst}, var_0)
    -- if (dt'_lst = var_1)

;; test.spectec:1733.6-1733.19
relation fun_clos_tagtype: `%%%`(context, tagtype, tagtype)
  ;; test.spectec:1733.6-1733.19
  rule fun_clos_tagtype_case_0{C : context, jt : typeuse, dt_lst : deftype*, var_1 : deftype*, var_0 : tagtype}:
    `%%%`(C, jt, var_0)
    -- fun_clos_deftypes: `%%`(C.TYPES_context, var_1)
    -- fun_subst_all_tagtype: `%%%`(jt, $typeuse_deftype(dt)*{dt <- dt_lst}, var_0)
    -- if (dt_lst = var_1)

;; test.spectec:1733.6-1733.19
relation clos_tagtype_is_wf: `%%%`(v_context : context, v_tagtype : tagtype, ret_val : tagtype)
  ;; test.spectec:1733.6-1733.19
  rule clos_tagtype_is_wf_0{v_context : context, v_tagtype : tagtype, ret_val : tagtype, var_0 : tagtype}:
    `%%%`(v_context, v_tagtype, ret_val)
    -- fun_clos_tagtype: `%%%`(v_context, v_tagtype, var_0)
    -- wf_context: `%`(v_context)
    -- wf_typeuse: `%`(v_tagtype)
    -- if (ret_val = var_0)
    -- wf_typeuse: `%`(ret_val)

;; test.spectec:1734.6-1734.22
relation fun_clos_externtype: `%%%`(context, externtype, externtype)
  ;; test.spectec:1734.6-1734.22
  rule fun_clos_externtype_case_0{C : context, xt : externtype, dt_lst : deftype*, var_1 : deftype*, var_0 : externtype}:
    `%%%`(C, xt, var_0)
    -- fun_clos_deftypes: `%%`(C.TYPES_context, var_1)
    -- fun_subst_all_externtype: `%%%`(xt, $typeuse_deftype(dt)*{dt <- dt_lst}, var_0)
    -- if (dt_lst = var_1)

;; test.spectec:1734.6-1734.22
relation clos_externtype_is_wf: `%%%`(v_context : context, v_externtype : externtype, ret_val : externtype)
  ;; test.spectec:1734.6-1734.22
  rule clos_externtype_is_wf_0{v_context : context, v_externtype : externtype, ret_val : externtype, var_0 : externtype}:
    `%%%`(v_context, v_externtype, ret_val)
    -- fun_clos_externtype: `%%%`(v_context, v_externtype, var_0)
    -- wf_context: `%`(v_context)
    -- wf_externtype: `%`(v_externtype)
    -- if (ret_val = var_0)
    -- wf_externtype: `%`(ret_val)

;; test.spectec:1735.6-1735.22
relation fun_clos_moduletype: `%%%`(context, moduletype, moduletype)
  ;; test.spectec:1735.6-1735.22
  rule fun_clos_moduletype_case_0{C : context, mmt : moduletype, dt_lst : deftype*, var_1 : deftype*, var_0 : moduletype}:
    `%%%`(C, mmt, var_0)
    -- fun_clos_deftypes: `%%`(C.TYPES_context, var_1)
    -- fun_subst_all_moduletype: `%%%`(mmt, $typeuse_deftype(dt)*{dt <- dt_lst}, var_0)
    -- if (dt_lst = var_1)

;; test.spectec:1735.6-1735.22
relation clos_moduletype_is_wf: `%%%`(v_context : context, v_moduletype : moduletype, ret_val : moduletype)
  ;; test.spectec:1735.6-1735.22
  rule clos_moduletype_is_wf_0{v_context : context, v_moduletype : moduletype, ret_val : moduletype, var_0 : moduletype}:
    `%%%`(v_context, v_moduletype, ret_val)
    -- fun_clos_moduletype: `%%%`(v_context, v_moduletype, var_0)
    -- wf_context: `%`(v_context)
    -- wf_moduletype: `%`(v_moduletype)
    -- if (ret_val = var_0)
    -- wf_moduletype: `%`(ret_val)

;; test.spectec:1761.1-1761.91
relation Numtype_ok: `%|-%:OK`(context, numtype)
  ;; test.spectec:1768.1-1769.20
  rule mk_Numtype_ok{C : context, v_numtype : numtype}:
    `%|-%:OK`(C, v_numtype)
    -- wf_context: `%`(C)

;; test.spectec:1762.1-1762.91
relation Vectype_ok: `%|-%:OK`(context, vectype)
  ;; test.spectec:1771.1-1772.20
  rule mk_Vectype_ok{C : context, v_vectype : vectype}:
    `%|-%:OK`(C, v_vectype)
    -- wf_context: `%`(C)

;; test.spectec:1842.1-1843.79
syntax oktypenat = 
  | OK(nat)

;; test.spectec:1845.1-1845.103
relation Packtype_ok: `%|-%:OK`(context, packtype)
  ;; test.spectec:1873.1-1874.21
  rule mk_Packtype_ok{C : context, v_packtype : packtype}:
    `%|-%:OK`(C, v_packtype)
    -- wf_context: `%`(C)

;; test.spectec:2168.1-2168.116
relation Packtype_sub: `%|-%<:%`(context, packtype, packtype)
  ;; test.spectec:2177.1-2178.28
  rule mk_Packtype_sub{C : context, v_packtype : packtype}:
    `%|-%<:%`(C, v_packtype, v_packtype)
    -- wf_context: `%`(C)

;; test.spectec:2026.1-2026.103
relation Numtype_sub: `%|-%<:%`(context, numtype, numtype)
  ;; test.spectec:2032.1-2033.26
  rule mk_Numtype_sub{C : context, v_numtype : numtype}:
    `%|-%<:%`(C, v_numtype, v_numtype)
    -- wf_context: `%`(C)

;; test.spectec:1827.1-1828.70
relation Expand: `%~~%`(deftype, comptype)
  ;; test.spectec:1832.1-1832.91
  rule mk_Expand{v_deftype : deftype, v_comptype : comptype, final_opt : final?, typeuse_lst : typeuse*, var_0 : subtype}:
    `%~~%`(v_deftype, v_comptype)
    -- fun_unrolldt: `%%`(v_deftype, var_0)
    -- if (var_0 = SUB_subtype(final_opt, typeuse_lst, v_comptype))
    -- wf_subtype: `%`(var_0)
    -- wf_subtype: `%`(SUB_subtype(final_opt, typeuse_lst, v_comptype))

;; test.spectec:2027.1-2027.103
relation Vectype_sub: `%|-%<:%`(context, vectype, vectype)
  ;; test.spectec:2035.1-2036.26
  rule mk_Vectype_sub{C : context, v_vectype : vectype}:
    `%|-%<:%`(C, v_vectype, v_vectype)
    -- wf_context: `%`(C)

;; test.spectec:1912.1-1912.70
def $before(v_typeuse : typeuse, nat : nat) : bool
  ;; test.spectec:1913.1-1913.30
  def $before{j : nat, i : nat}(REC_typeuse(j), i) = (j < i)
  ;; test.spectec:1914.1-1914.45
  def $before{v_typeuse : typeuse, i : nat}(v_typeuse, i) = true

;; test.spectec:1916.6-1916.16
relation fun_unrollht_: `%%%`(context, heaptype, subtype)
  ;; test.spectec:1916.6-1916.16
  rule fun_unrollht__case_0{v_rectype : rectype, v_n : n, C : context, var_0 : subtype}:
    `%%%`(C, _DEF_heaptype(v_rectype, v_n), var_0)
    -- fun_unrolldt: `%%`(_DEF_deftype(v_rectype, v_n), var_0)

  ;; test.spectec:1916.6-1916.16
  rule fun_unrollht__case_1{C : context, v_typeidx : uN, var_0 : subtype}:
    `%%%`(C, _IDX_heaptype(v_typeidx), var_0)
    -- if ($proj_uN_0(v_typeidx).0 < |C.TYPES_context|)
    -- fun_unrolldt: `%%`(C.TYPES_context[$proj_uN_0(v_typeidx).0], var_0)

  ;; test.spectec:1916.6-1916.16
  rule fun_unrollht__case_2{C : context, i : nat}:
    `%%%`(C, REC_heaptype(i), C.RECS_context[i])
    -- if (i < |C.RECS_context|)

;; test.spectec:1916.6-1916.16
relation unrollht__is_wf: `%%%`(v_context : context, v_heaptype : heaptype, ret_val : subtype)
  ;; test.spectec:1916.6-1916.16
  rule unrollht__is_wf_0{v_context : context, v_heaptype : heaptype, ret_val : subtype, var_0 : subtype}:
    `%%%`(v_context, v_heaptype, ret_val)
    -- fun_unrollht_: `%%%`(v_context, v_heaptype, var_0)
    -- wf_context: `%`(v_context)
    -- wf_heaptype: `%`(v_heaptype)
    -- if (ret_val = var_0)
    -- wf_subtype: `%`(ret_val)

;; test.spectec:1763.1-2170.117
rec {

;; test.spectec:1763.1-1763.92
relation Heaptype_ok: `%|-%:OK`(context, heaptype)
  ;; test.spectec:1774.1-1775.24
  rule abs{C : context, v_absheaptype : absheaptype}:
    `%|-%:OK`(C, $heaptype_absheaptype(v_absheaptype))
    -- wf_context: `%`(C)

  ;; test.spectec:1777.1-1779.35
  rule typeuse{C : context, v_typeuse : typeuse}:
    `%|-%:OK`(C, $heaptype_typeuse(v_typeuse))
    -- Typeuse_ok: `%|-%:OK`(C, v_typeuse)
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(v_typeuse)

  ;; test.spectec:1781.1-1782.16
  rule bot{C : context}:
    `%|-%:OK`(C, BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(BOT_heaptype)

;; test.spectec:1764.1-1764.91
relation Reftype_ok: `%|-%:OK`(context, reftype)
  ;; test.spectec:1784.1-1786.37
  rule mk_Reftype_ok{C : context, v_heaptype : heaptype}:
    `%|-%:OK`(C, REF_reftype(?(NULL_null), v_heaptype))
    -- Heaptype_ok: `%|-%:OK`(C, v_heaptype)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), v_heaptype))

;; test.spectec:1765.1-1765.91
relation Valtype_ok: `%|-%:OK`(context, valtype)
  ;; test.spectec:1788.1-1790.35
  rule num{C : context, v_numtype : numtype}:
    `%|-%:OK`(C, $valtype_numtype(v_numtype))
    -- Numtype_ok: `%|-%:OK`(C, v_numtype)
    -- wf_context: `%`(C)

  ;; test.spectec:1792.1-1794.35
  rule vec{C : context, v_vectype : vectype}:
    `%|-%:OK`(C, $valtype_vectype(v_vectype))
    -- Vectype_ok: `%|-%:OK`(C, v_vectype)
    -- wf_context: `%`(C)

  ;; test.spectec:1796.1-1798.35
  rule ref{C : context, v_reftype : reftype}:
    `%|-%:OK`(C, $valtype_reftype(v_reftype))
    -- Reftype_ok: `%|-%:OK`(C, v_reftype)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(v_reftype)

  ;; test.spectec:1800.1-1801.16
  rule bot{C : context}:
    `%|-%:OK`(C, BOT_valtype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(BOT_valtype)

;; test.spectec:1766.1-1766.94
relation Typeuse_ok: `%|-%:OK`(context, typeuse)
  ;; test.spectec:1860.1-1862.30
  rule typeidx{C : context, v_typeidx : typeidx, dt : deftype}:
    `%|-%:OK`(C, _IDX_typeuse(v_typeidx))
    -- if ($proj_uN_0(v_typeidx).0 < |C.TYPES_context|)
    -- if (C.TYPES_context[$proj_uN_0(v_typeidx).0] = dt)
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(_IDX_typeuse(v_typeidx))

  ;; test.spectec:1864.1-1866.23
  rule rec{C : context, i : n, st : subtype}:
    `%|-%:OK`(C, REC_typeuse(i))
    -- if (i < |C.RECS_context|)
    -- if (C.RECS_context[i] = st)
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(st)
    -- wf_typeuse: `%`(REC_typeuse(i))

  ;; test.spectec:1868.1-1870.35
  rule deftype{C : context, v_deftype : deftype}:
    `%|-%:OK`(C, $typeuse_deftype(v_deftype))
    -- Deftype_ok: `%|-%:OK`(C, v_deftype)
    -- wf_context: `%`(C)

;; test.spectec:1807.1-1807.100
relation Resulttype_ok: `%|-%:OK`(context, resulttype)
  ;; test.spectec:1814.1-1816.32
  rule mk_Resulttype_ok{C : context, t_lst : valtype*}:
    `%|-%:OK`(C, mk_list_resulttype(t_lst))
    -- (Valtype_ok: `%|-%:OK`(C, t))*{t <- t_lst}
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t))*{t <- t_lst}

;; test.spectec:1846.1-1846.104
relation Fieldtype_ok: `%|-%:OK`(context, fieldtype)
  ;; test.spectec:1884.1-1886.43
  rule mk_Fieldtype_ok{C : context, v_storagetype : storagetype}:
    `%|-%:OK`(C, mk_fieldtype_fieldtype(?(MUT_mut), v_storagetype))
    -- Storagetype_ok: `%|-%:OK`(C, v_storagetype)
    -- wf_context: `%`(C)
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(?(MUT_mut), v_storagetype))

;; test.spectec:1847.1-1847.106
relation Storagetype_ok: `%|-%:OK`(context, storagetype)
  ;; test.spectec:1876.1-1878.35
  rule val{C : context, v_valtype : valtype}:
    `%|-%:OK`(C, $storagetype_valtype(v_valtype))
    -- Valtype_ok: `%|-%:OK`(C, v_valtype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(v_valtype)

  ;; test.spectec:1880.1-1882.37
  rule pack{C : context, v_packtype : packtype}:
    `%|-%:OK`(C, $storagetype_packtype(v_packtype))
    -- Packtype_ok: `%|-%:OK`(C, v_packtype)
    -- wf_context: `%`(C)

;; test.spectec:1848.1-1848.103
relation Comptype_ok: `%|-%:OK`(context, comptype)
  ;; test.spectec:1889.1-1891.42
  rule struct{C : context, fieldtype_lst : fieldtype*}:
    `%|-%:OK`(C, STRUCT_comptype(mk_list_list(fieldtype_lst)))
    -- (Fieldtype_ok: `%|-%:OK`(C, v_fieldtype))*{v_fieldtype <- fieldtype_lst}
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(fieldtype_lst)))

  ;; test.spectec:1893.1-1895.39
  rule array{C : context, v_fieldtype : fieldtype}:
    `%|-%:OK`(C, ARRAY_comptype(v_fieldtype))
    -- Fieldtype_ok: `%|-%:OK`(C, v_fieldtype)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(ARRAY_comptype(v_fieldtype))

  ;; test.spectec:1897.1-1900.35
  rule func{C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:OK`(C, `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- Resulttype_ok: `%|-%:OK`(C, mk_list_resulttype(t_1_lst))
    -- Resulttype_ok: `%|-%:OK`(C, mk_list_resulttype(t_2_lst))
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

;; test.spectec:1851.1-1851.126
relation Subtype_ok2: `%|-%:%`(context, subtype, oktypenat)
  ;; test.spectec:1921.1-1930.49
  rule mk_Subtype_ok2{C : context, typeuse_lst : typeuse*, v_comptype : comptype, i : nat, comptype'_lst : comptype*, typeuse'_lst_lst : typeuse**, var_0_lst : subtype*}:
    `%|-%:%`(C, SUB_subtype(?(FINAL_final), typeuse_lst, v_comptype), OK_oktypenat(i))
    -- if (|var_0_lst| = |typeuse_lst|)
    -- (fun_unrollht_: `%%%`(C, $heaptype_typeuse(v_typeuse), var_0))*{var_0 <- var_0_lst, v_typeuse <- typeuse_lst}
    -- if (|typeuse_lst| <= 1)
    -- (Typeuse_ok: `%|-%:OK`(C, v_typeuse))*{v_typeuse <- typeuse_lst}
    -- (if $before(v_typeuse, i))*{v_typeuse <- typeuse_lst}
    -- if (|var_0_lst| = |comptype'_lst|)
    -- if (|var_0_lst| = |typeuse'_lst_lst|)
    -- (if (var_0 = SUB_subtype(?(), typeuse'_lst, comptype')))*{var_0 <- var_0_lst, comptype' <- comptype'_lst, typeuse'_lst <- typeuse'_lst_lst}
    -- Comptype_ok: `%|-%:OK`(C, v_comptype)
    -- (Comptype_sub: `%|-%<:%`(C, v_comptype, comptype'))*{comptype' <- comptype'_lst}
    -- wf_context: `%`(C)
    -- (wf_subtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- wf_subtype: `%`(SUB_subtype(?(FINAL_final), typeuse_lst, v_comptype))
    -- if (|comptype'_lst| = |typeuse'_lst_lst|)
    -- (wf_subtype: `%`(SUB_subtype(?(), typeuse'_lst, comptype')))*{comptype' <- comptype'_lst, typeuse'_lst <- typeuse'_lst_lst}

;; test.spectec:1852.1-1852.126
relation Rectype_ok2: `%|-%:%`(context, rectype, oktypenat)
  ;; test.spectec:1942.1-1943.23
  rule empty{C : context, i : nat}:
    `%|-%:%`(C, REC_rectype(mk_list_list([])), OK_oktypenat(i))
    -- wf_context: `%`(C)

  ;; test.spectec:1945.1-1948.49
  rule cons{C : context, subtype_1 : subtype, subtype_lst : subtype*, i : nat}:
    `%|-%:%`(C, REC_rectype(mk_list_list([subtype_1] ++ subtype_lst)), OK_oktypenat(i))
    -- Subtype_ok2: `%|-%:%`(C, subtype_1, OK_oktypenat(i))
    -- Rectype_ok2: `%|-%:%`(C, REC_rectype(mk_list_list(subtype_lst)), OK_oktypenat((i + 1)))
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(subtype_1)
    -- (wf_subtype: `%`(v_subtype))*{v_subtype <- subtype_lst}

;; test.spectec:1853.1-1853.102
relation Deftype_ok: `%|-%:OK`(context, deftype)
  ;; test.spectec:1951.1-1955.14
  rule mk_Deftype_ok{C : context, v_rectype : rectype, i : n, v_n : n, subtype_lst : subtype*}:
    `%|-%:OK`(C, _DEF_deftype(v_rectype, i))
    -- Rectype_ok2: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS subtype_lst} +++ C, v_rectype, OK_oktypenat(0))
    -- if (v_rectype = REC_rectype(mk_list_list(subtype_lst)))
    -- if (i < v_n)
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS subtype_lst})
    -- if (v_n = |subtype_lst|)

;; test.spectec:1856.1-1856.108
relation Comptype_sub: `%|-%<:%`(context, comptype, comptype)
  ;; test.spectec:2200.1-2202.41
  rule struct{C : context, ft_1_lst : fieldtype*, ft'_1_lst : fieldtype*, ft_2_lst : fieldtype*}:
    `%|-%<:%`(C, STRUCT_comptype(mk_list_list(ft_1_lst ++ ft'_1_lst)), STRUCT_comptype(mk_list_list(ft_2_lst)))
    -- if (|ft_1_lst| = |ft_2_lst|)
    -- (Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2))*{ft_1 <- ft_1_lst, ft_2 <- ft_2_lst}
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(ft_1_lst ++ ft'_1_lst)))
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(ft_2_lst)))

  ;; test.spectec:2204.1-2206.38
  rule array{C : context, ft_1 : fieldtype, ft_2 : fieldtype}:
    `%|-%<:%`(C, ARRAY_comptype(ft_1), ARRAY_comptype(ft_2))
    -- Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(ARRAY_comptype(ft_1))
    -- wf_comptype: `%`(ARRAY_comptype(ft_2))

  ;; test.spectec:2208.1-2211.41
  rule func{C : context, t_11_lst : valtype*, t_12_lst : valtype*, t_21_lst : valtype*, t_22_lst : valtype*}:
    `%|-%<:%`(C, `FUNC%->%`_comptype(mk_list_resulttype(t_11_lst), mk_list_resulttype(t_12_lst)), `FUNC%->%`_comptype(mk_list_resulttype(t_21_lst), mk_list_resulttype(t_22_lst)))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_21_lst), mk_list_resulttype(t_11_lst))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_12_lst), mk_list_resulttype(t_22_lst))
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_11_lst), mk_list_resulttype(t_12_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_21_lst), mk_list_resulttype(t_22_lst)))

;; test.spectec:1857.1-1857.107
relation Deftype_sub: `%|-%<:%`(context, deftype, deftype)
  ;; test.spectec:2214.1-2216.66
  rule refl{C : context, deftype_1 : deftype, deftype_2 : deftype, var_1 : deftype, var_0 : deftype}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- fun_clos_deftype: `%%%`(C, deftype_2, var_1)
    -- fun_clos_deftype: `%%%`(C, deftype_1, var_0)
    -- if (var_0 = var_1)
    -- wf_context: `%`(C)

  ;; test.spectec:2218.1-2221.49
  rule super{C : context, deftype_1 : deftype, deftype_2 : deftype, final_opt : final?, typeuse_lst : typeuse*, ct : comptype, i : nat, var_0 : subtype}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- fun_unrolldt: `%%`(deftype_1, var_0)
    -- if (var_0 = SUB_subtype(final_opt, typeuse_lst, ct))
    -- if (i < |typeuse_lst|)
    -- Heaptype_sub: `%|-%<:%`(C, $heaptype_typeuse(typeuse_lst[i]), $heaptype_deftype(deftype_2))
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(var_0)
    -- wf_subtype: `%`(SUB_subtype(final_opt, typeuse_lst, ct))

;; test.spectec:2028.1-2028.104
relation Heaptype_sub: `%|-%<:%`(context, heaptype, heaptype)
  ;; test.spectec:2039.1-2040.28
  rule refl{C : context, v_heaptype : heaptype}:
    `%|-%<:%`(C, v_heaptype, v_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)

  ;; test.spectec:2042.1-2046.48
  rule trans{C : context, heaptype_1 : heaptype, heaptype_2 : heaptype, heaptype' : heaptype}:
    `%|-%<:%`(C, heaptype_1, heaptype_2)
    -- Heaptype_ok: `%|-%:OK`(C, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype_1, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype', heaptype_2)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(heaptype_1)
    -- wf_heaptype: `%`(heaptype_2)
    -- wf_heaptype: `%`(heaptype')

  ;; test.spectec:2048.1-2049.17
  rule eq_any{C : context}:
    `%|-%<:%`(C, EQ_heaptype, ANY_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(EQ_heaptype)
    -- wf_heaptype: `%`(ANY_heaptype)

  ;; test.spectec:2051.1-2052.17
  rule i31_eq{C : context}:
    `%|-%<:%`(C, I31_heaptype, EQ_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(I31_heaptype)
    -- wf_heaptype: `%`(EQ_heaptype)

  ;; test.spectec:2054.1-2055.20
  rule struct_eq{C : context}:
    `%|-%<:%`(C, STRUCT_heaptype, EQ_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(STRUCT_heaptype)
    -- wf_heaptype: `%`(EQ_heaptype)

  ;; test.spectec:2057.1-2058.19
  rule array_eq{C : context}:
    `%|-%<:%`(C, ARRAY_heaptype, EQ_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(ARRAY_heaptype)
    -- wf_heaptype: `%`(EQ_heaptype)

  ;; test.spectec:2060.1-2062.42
  rule struct{C : context, v_deftype : deftype, fieldtype_lst : fieldtype*}:
    `%|-%<:%`(C, $heaptype_deftype(v_deftype), STRUCT_heaptype)
    -- Expand: `%~~%`(v_deftype, STRUCT_comptype(mk_list_list(fieldtype_lst)))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(STRUCT_heaptype)
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(fieldtype_lst)))

  ;; test.spectec:2064.1-2066.40
  rule array{C : context, v_deftype : deftype, v_fieldtype : fieldtype}:
    `%|-%<:%`(C, $heaptype_deftype(v_deftype), ARRAY_heaptype)
    -- Expand: `%~~%`(v_deftype, ARRAY_comptype(v_fieldtype))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(ARRAY_heaptype)
    -- wf_comptype: `%`(ARRAY_comptype(v_fieldtype))

  ;; test.spectec:2068.1-2070.42
  rule func{C : context, v_deftype : deftype, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%<:%`(C, $heaptype_deftype(v_deftype), FUNC_heaptype)
    -- Expand: `%~~%`(v_deftype, `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(FUNC_heaptype)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2072.1-2074.46
  rule def{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, $heaptype_deftype(deftype_1), $heaptype_deftype(deftype_2))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- wf_context: `%`(C)

  ;; test.spectec:2076.1-2078.53
  rule typeidx_l{C : context, v_typeidx : typeidx, v_heaptype : heaptype}:
    `%|-%<:%`(C, _IDX_heaptype(v_typeidx), v_heaptype)
    -- if ($proj_uN_0(v_typeidx).0 < |C.TYPES_context|)
    -- Heaptype_sub: `%|-%<:%`(C, $heaptype_deftype(C.TYPES_context[$proj_uN_0(v_typeidx).0]), v_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(_IDX_heaptype(v_typeidx))

  ;; test.spectec:2080.1-2082.53
  rule typeidx_r{C : context, v_heaptype : heaptype, v_typeidx : typeidx}:
    `%|-%<:%`(C, v_heaptype, _IDX_heaptype(v_typeidx))
    -- if ($proj_uN_0(v_typeidx).0 < |C.TYPES_context|)
    -- Heaptype_sub: `%|-%<:%`(C, v_heaptype, $heaptype_deftype(C.TYPES_context[$proj_uN_0(v_typeidx).0]))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(_IDX_heaptype(v_typeidx))

  ;; test.spectec:2084.1-2086.51
  rule rec_struct{C : context, i : n, final_opt : final?, fieldtype_lst : fieldtype*}:
    `%|-%<:%`(C, REC_heaptype(i), STRUCT_heaptype)
    -- if (i < |C.RECS_context|)
    -- if (C.RECS_context[i] = SUB_subtype(final_opt, [], STRUCT_comptype(mk_list_list(fieldtype_lst))))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_heaptype: `%`(STRUCT_heaptype)
    -- wf_subtype: `%`(SUB_subtype(final_opt, [], STRUCT_comptype(mk_list_list(fieldtype_lst))))

  ;; test.spectec:2088.1-2090.49
  rule rec_array{C : context, i : n, final_opt : final?, v_fieldtype : fieldtype}:
    `%|-%<:%`(C, REC_heaptype(i), ARRAY_heaptype)
    -- if (i < |C.RECS_context|)
    -- if (C.RECS_context[i] = SUB_subtype(final_opt, [], ARRAY_comptype(v_fieldtype)))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_heaptype: `%`(ARRAY_heaptype)
    -- wf_subtype: `%`(SUB_subtype(final_opt, [], ARRAY_comptype(v_fieldtype)))

  ;; test.spectec:2092.1-2094.51
  rule rec_func{C : context, i : n, final_opt : final?, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%<:%`(C, REC_heaptype(i), FUNC_heaptype)
    -- if (i < |C.RECS_context|)
    -- if (C.RECS_context[i] = SUB_subtype(final_opt, [], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst))))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_heaptype: `%`(FUNC_heaptype)
    -- wf_subtype: `%`(SUB_subtype(final_opt, [], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst))))

  ;; test.spectec:2096.1-2098.43
  rule rec_sub{C : context, i : n, typeuse_lst : typeuse*, j : nat, final_opt : final?, ct : comptype}:
    `%|-%<:%`(C, REC_heaptype(i), $heaptype_typeuse(typeuse_lst[j]))
    -- if (j < |typeuse_lst|)
    -- if (i < |C.RECS_context|)
    -- if (C.RECS_context[i] = SUB_subtype(final_opt, typeuse_lst, ct))
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(REC_heaptype(i))
    -- wf_subtype: `%`(SUB_subtype(final_opt, typeuse_lst, ct))

  ;; test.spectec:2100.1-2103.25
  rule none{C : context, v_heaptype : heaptype}:
    `%|-%<:%`(C, NONE_heaptype, v_heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, v_heaptype, ANY_heaptype)
    -- if (v_heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(NONE_heaptype)
    -- wf_heaptype: `%`(ANY_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2105.1-2108.25
  rule nofunc{C : context, v_heaptype : heaptype}:
    `%|-%<:%`(C, NOFUNC_heaptype, v_heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, v_heaptype, FUNC_heaptype)
    -- if (v_heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(NOFUNC_heaptype)
    -- wf_heaptype: `%`(FUNC_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2110.1-2113.25
  rule noexn{C : context, v_heaptype : heaptype}:
    `%|-%<:%`(C, NOEXN_heaptype, v_heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, v_heaptype, EXN_heaptype)
    -- if (v_heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(NOEXN_heaptype)
    -- wf_heaptype: `%`(EXN_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2115.1-2118.25
  rule noextern{C : context, v_heaptype : heaptype}:
    `%|-%<:%`(C, NOEXTERN_heaptype, v_heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, v_heaptype, EXTERN_heaptype)
    -- if (v_heaptype =/= BOT_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(NOEXTERN_heaptype)
    -- wf_heaptype: `%`(EXTERN_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

  ;; test.spectec:2120.1-2121.23
  rule bot{C : context, v_heaptype : heaptype}:
    `%|-%<:%`(C, BOT_heaptype, v_heaptype)
    -- wf_context: `%`(C)
    -- wf_heaptype: `%`(v_heaptype)
    -- wf_heaptype: `%`(BOT_heaptype)

;; test.spectec:2029.1-2029.103
relation Reftype_sub: `%|-%<:%`(context, reftype, reftype)
  ;; test.spectec:2124.1-2126.37
  rule nonnull{C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(?(), ht_1), REF_reftype(?(), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(REF_reftype(?(), ht_1))
    -- wf_reftype: `%`(REF_reftype(?(), ht_2))

  ;; test.spectec:2128.1-2130.37
  rule null{C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(?(NULL_null), ht_1), REF_reftype(?(NULL_null), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), ht_1))
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), ht_2))

;; test.spectec:2030.1-2030.103
relation Valtype_sub: `%|-%<:%`(context, valtype, valtype)
  ;; test.spectec:2133.1-2135.46
  rule num{C : context, numtype_1 : numtype, numtype_2 : numtype}:
    `%|-%<:%`(C, $valtype_numtype(numtype_1), $valtype_numtype(numtype_2))
    -- Numtype_sub: `%|-%<:%`(C, numtype_1, numtype_2)
    -- wf_context: `%`(C)

  ;; test.spectec:2137.1-2139.46
  rule vec{C : context, vectype_1 : vectype, vectype_2 : vectype}:
    `%|-%<:%`(C, $valtype_vectype(vectype_1), $valtype_vectype(vectype_2))
    -- Vectype_sub: `%|-%<:%`(C, vectype_1, vectype_2)
    -- wf_context: `%`(C)

  ;; test.spectec:2141.1-2143.46
  rule ref{C : context, reftype_1 : reftype, reftype_2 : reftype}:
    `%|-%<:%`(C, $valtype_reftype(reftype_1), $valtype_reftype(reftype_2))
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(reftype_1)
    -- wf_reftype: `%`(reftype_2)

  ;; test.spectec:2145.1-2146.22
  rule bot{C : context, v_valtype : valtype}:
    `%|-%<:%`(C, BOT_valtype, v_valtype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(v_valtype)
    -- wf_valtype: `%`(BOT_valtype)

;; test.spectec:2151.1-2151.115
relation Resulttype_sub: `%|-%<:%`(context, resulttype, resulttype)
  ;; test.spectec:2154.1-2156.37
  rule mk_Resulttype_sub{C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%<:%`(C, mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst))
    -- if (|t_1_lst| = |t_2_lst|)
    -- (Valtype_sub: `%|-%<:%`(C, t_1, t_2))*{t_1 <- t_1_lst, t_2 <- t_2_lst}
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t_1))*{t_1 <- t_1_lst}
    -- (wf_valtype: `%`(t_2))*{t_2 <- t_2_lst}

;; test.spectec:2169.1-2169.119
relation Storagetype_sub: `%|-%<:%`(context, storagetype, storagetype)
  ;; test.spectec:2181.1-2183.46
  rule val{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, $storagetype_valtype(valtype_1), $storagetype_valtype(valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(valtype_1)
    -- wf_valtype: `%`(valtype_2)

  ;; test.spectec:2185.1-2187.49
  rule pack{C : context, packtype_1 : packtype, packtype_2 : packtype}:
    `%|-%<:%`(C, $storagetype_packtype(packtype_1), $storagetype_packtype(packtype_2))
    -- Packtype_sub: `%|-%<:%`(C, packtype_1, packtype_2)
    -- wf_context: `%`(C)

;; test.spectec:2170.1-2170.117
relation Fieldtype_sub: `%|-%<:%`(context, fieldtype, fieldtype)
  ;; test.spectec:2190.1-2192.40
  rule const{C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, mk_fieldtype_fieldtype(?(), zt_1), mk_fieldtype_fieldtype(?(), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- wf_context: `%`(C)
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(?(), zt_1))
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(?(), zt_2))

  ;; test.spectec:2194.1-2197.40
  rule var{C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, mk_fieldtype_fieldtype(?(MUT_mut), zt_1), mk_fieldtype_fieldtype(?(MUT_mut), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)
    -- wf_context: `%`(C)
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(?(MUT_mut), zt_1))
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(?(MUT_mut), zt_2))
}

;; test.spectec:1806.1-1806.96
relation Localtype_ok: `%|-%:OK`(context, localtype)
  ;; test.spectec:1810.1-1812.29
  rule mk_Localtype_ok{C : context, v_init : init, t : valtype}:
    `%|-%:OK`(C, mk_localtype_localtype(v_init, t))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_localtype: `%`(mk_localtype_localtype(v_init, t))

;; test.spectec:1808.1-1808.99
relation Instrtype_ok: `%|-%:OK`(context, instrtype)
  ;; test.spectec:1818.1-1822.29
  rule mk_Instrtype_ok{C : context, t_1_lst : valtype*, x_lst : idx*, t_2_lst : valtype*, lct_lst : localtype*}:
    `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))
    -- Resulttype_ok: `%|-%:OK`(C, mk_list_resulttype(t_1_lst))
    -- Resulttype_ok: `%|-%:OK`(C, mk_list_resulttype(t_2_lst))
    -- if (|lct_lst| = |x_lst|)
    -- (if ($proj_uN_0(x).0 < |C.LOCALS_context|))*{x <- x_lst}
    -- (if (C.LOCALS_context[$proj_uN_0(x).0] = lct))*{lct <- lct_lst, x <- x_lst}
    -- wf_context: `%`(C)
    -- (wf_localtype: `%`(lct))*{lct <- lct_lst}
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))

;; test.spectec:1829.1-1830.70
relation Expand_use: `%~~_%%`(typeuse, context, comptype)
  ;; test.spectec:1834.1-1834.84
  rule deftype{v_deftype : deftype, C : context, v_comptype : comptype}:
    `%~~_%%`($typeuse_deftype(v_deftype), C, v_comptype)
    -- Expand: `%~~%`(v_deftype, v_comptype)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(v_comptype)

  ;; test.spectec:1835.1-1835.93
  rule typeidx{v_typeidx : typeidx, C : context, v_comptype : comptype}:
    `%~~_%%`(_IDX_typeuse(v_typeidx), C, v_comptype)
    -- if ($proj_uN_0(v_typeidx).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(v_typeidx).0], v_comptype)
    -- wf_context: `%`(C)
    -- wf_comptype: `%`(v_comptype)
    -- wf_typeuse: `%`(_IDX_typeuse(v_typeidx))

;; test.spectec:1840.1-1841.76
syntax oktypeidx = 
  | OK(v_typeidx : typeidx)

;; test.spectec:1840.8-1840.17
relation wf_oktypeidx: `%`(oktypeidx)
  ;; test.spectec:1840.8-1840.17
  rule oktypeidx_case_0{v_typeidx : typeidx}:
    `%`(OK_oktypeidx(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

;; test.spectec:1849.1-1849.126
relation Subtype_ok: `%|-%:%`(context, subtype, oktypeidx)
  ;; test.spectec:1903.1-1910.49
  rule mk_Subtype_ok{C : context, x_lst : idx*, v_comptype : comptype, x_0 : idx, comptype'_lst : comptype*, yy_lst_lst : typeuse**, var_0_lst : subtype*}:
    `%|-%:%`(C, SUB_subtype(?(FINAL_final), _IDX_typeuse(x)*{x <- x_lst}, v_comptype), OK_oktypeidx(x_0))
    -- if (|var_0_lst| = |x_lst|)
    -- (if ($proj_uN_0(x).0 < |C.TYPES_context|))*{x <- x_lst}
    -- (fun_unrolldt: `%%`(C.TYPES_context[$proj_uN_0(x).0], var_0))*{var_0 <- var_0_lst, x <- x_lst}
    -- if (|x_lst| <= 1)
    -- (if ($proj_uN_0(x).0 < $proj_uN_0(x_0).0))*{x <- x_lst}
    -- if (|var_0_lst| = |comptype'_lst|)
    -- if (|var_0_lst| = |yy_lst_lst|)
    -- (if (var_0 = SUB_subtype(?(), yy_lst, comptype')))*{var_0 <- var_0_lst, comptype' <- comptype'_lst, yy_lst <- yy_lst_lst}
    -- Comptype_ok: `%|-%:OK`(C, v_comptype)
    -- (Comptype_sub: `%|-%<:%`(C, v_comptype, comptype'))*{comptype' <- comptype'_lst}
    -- wf_context: `%`(C)
    -- (wf_subtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- wf_subtype: `%`(SUB_subtype(?(FINAL_final), _IDX_typeuse(x)*{x <- x_lst}, v_comptype))
    -- wf_oktypeidx: `%`(OK_oktypeidx(x_0))
    -- if (|comptype'_lst| = |yy_lst_lst|)
    -- (wf_subtype: `%`(SUB_subtype(?(), yy_lst, comptype')))*{comptype' <- comptype'_lst, yy_lst <- yy_lst_lst}

;; test.spectec:1850.1-1850.126
rec {

;; test.spectec:1850.1-1850.126
relation Rectype_ok: `%|-%:%`(context, rectype, oktypeidx)
  ;; test.spectec:1933.1-1934.23
  rule empty{C : context, x : idx}:
    `%|-%:%`(C, REC_rectype(mk_list_list([])), OK_oktypeidx(x))
    -- wf_context: `%`(C)
    -- wf_oktypeidx: `%`(OK_oktypeidx(x))

  ;; test.spectec:1936.1-1939.48
  rule cons{C : context, subtype_1 : subtype, subtype_lst : subtype*, x : idx}:
    `%|-%:%`(C, REC_rectype(mk_list_list([subtype_1] ++ subtype_lst)), OK_oktypeidx(x))
    -- Subtype_ok: `%|-%:%`(C, subtype_1, OK_oktypeidx(x))
    -- Rectype_ok: `%|-%:%`(C, REC_rectype(mk_list_list(subtype_lst)), OK_oktypeidx(mk_uN_typeidx(($proj_uN_0(x).0 + 1))))
    -- wf_context: `%`(C)
    -- wf_subtype: `%`(subtype_1)
    -- (wf_subtype: `%`(v_subtype))*{v_subtype <- subtype_lst}
    -- wf_oktypeidx: `%`(OK_oktypeidx(x))
    -- wf_oktypeidx: `%`(OK_oktypeidx(mk_uN_typeidx(($proj_uN_0(x).0 + 1))))
}

;; test.spectec:1960.1-1960.120
relation Limits_ok: `%|-%:%`(context, limits, nat)
  ;; test.spectec:1968.1-1971.23
  rule mk_Limits_ok{C : context, v_n : n, m_opt : m?, k : nat}:
    `%|-%:%`(C, mk_limits_limits(mk_uN_u64(v_n), mk_uN_u64(v_m)?{v_m <- m_opt}), k)
    -- if (v_n <= k)
    -- (if ((v_n <= v_m) /\ (v_m <= k)))?{v_m <- m_opt}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u64(v_n), mk_uN_u64(v_m)?{v_m <- m_opt}))

;; test.spectec:1961.1-1961.97
relation Tagtype_ok: `%|-%:OK`(context, tagtype)
  ;; test.spectec:1973.1-1976.54
  rule mk_Tagtype_ok{C : context, v_typeuse : typeuse, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:OK`(C, v_typeuse)
    -- Typeuse_ok: `%|-%:OK`(C, v_typeuse)
    -- Expand_use: `%~~_%%`(v_typeuse, C, `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(v_typeuse)
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

;; test.spectec:1962.1-1962.100
relation Globaltype_ok: `%|-%:OK`(context, globaltype)
  ;; test.spectec:1978.1-1980.29
  rule mk_Globaltype_ok{C : context, t : valtype}:
    `%|-%:OK`(C, mk_globaltype_globaltype(?(MUT_mut), t))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(MUT_mut), t))

;; test.spectec:1963.1-1963.97
relation Memtype_ok: `%|-%:OK`(context, memtype)
  ;; test.spectec:1982.1-1984.58
  rule mk_Memtype_ok{C : context, v_addrtype : addrtype, v_limits : limits}:
    `%|-%:OK`(C, `%%PAGE`_memtype(v_addrtype, v_limits))
    -- Limits_ok: `%|-%:%`(C, v_limits, (2 ^ ((($size($numtype_addrtype(v_addrtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))
    -- wf_context: `%`(C)
    -- wf_memtype: `%`(`%%PAGE`_memtype(v_addrtype, v_limits))

;; test.spectec:1964.1-1964.99
relation Tabletype_ok: `%|-%:OK`(context, tabletype)
  ;; test.spectec:1986.1-1989.35
  rule mk_Tabletype_ok{C : context, v_addrtype : addrtype, v_limits : limits, v_reftype : reftype}:
    `%|-%:OK`(C, mk_tabletype_tabletype(v_addrtype, v_limits, v_reftype))
    -- Limits_ok: `%|-%:%`(C, v_limits, ((((2 ^ $size($numtype_addrtype(v_addrtype))) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- Reftype_ok: `%|-%:OK`(C, v_reftype)
    -- wf_context: `%`(C)
    -- wf_tabletype: `%`(mk_tabletype_tabletype(v_addrtype, v_limits, v_reftype))

;; test.spectec:1965.1-1965.100
relation Externtype_ok: `%|-%:OK`(context, externtype)
  ;; test.spectec:1992.1-1994.35
  rule tag{C : context, v_tagtype : tagtype}:
    `%|-%:OK`(C, TAG_externtype(v_tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, v_tagtype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TAG_externtype(v_tagtype))

  ;; test.spectec:1996.1-1998.41
  rule global{C : context, v_globaltype : globaltype}:
    `%|-%:OK`(C, GLOBAL_externtype(v_globaltype))
    -- Globaltype_ok: `%|-%:OK`(C, v_globaltype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(GLOBAL_externtype(v_globaltype))

  ;; test.spectec:2000.1-2002.35
  rule mem{C : context, v_memtype : memtype}:
    `%|-%:OK`(C, MEM_externtype(v_memtype))
    -- Memtype_ok: `%|-%:OK`(C, v_memtype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(MEM_externtype(v_memtype))

  ;; test.spectec:2004.1-2006.39
  rule table{C : context, v_tabletype : tabletype}:
    `%|-%:OK`(C, TABLE_externtype(v_tabletype))
    -- Tabletype_ok: `%|-%:OK`(C, v_tabletype)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TABLE_externtype(v_tabletype))

  ;; test.spectec:2008.1-2011.54
  rule func{C : context, v_typeuse : typeuse, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:OK`(C, FUNC_externtype(v_typeuse))
    -- Typeuse_ok: `%|-%:OK`(C, v_typeuse)
    -- Expand_use: `%~~_%%`(v_typeuse, C, `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(FUNC_externtype(v_typeuse))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

;; test.spectec:2152.1-2152.114
relation Instrtype_sub: `%|-%<:%`(context, instrtype, instrtype)
  ;; test.spectec:2158.1-2163.31
  rule mk_Instrtype_sub{C : context, t_11_lst : valtype*, x_1_lst : idx*, t_12_lst : valtype*, t_21_lst : valtype*, x_2_lst : idx*, t_22_lst : valtype*, x_lst : idx*, t_lst : valtype*}:
    `%|-%<:%`(C, mk_instrtype_instrtype(mk_list_resulttype(t_11_lst), x_1_lst, mk_list_resulttype(t_12_lst)), mk_instrtype_instrtype(mk_list_resulttype(t_21_lst), x_2_lst, mk_list_resulttype(t_22_lst)))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_21_lst), mk_list_resulttype(t_11_lst))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_12_lst), mk_list_resulttype(t_22_lst))
    -- if (x_lst = $setminus_(syntax localidx, x_2_lst, x_1_lst))
    -- if (|t_lst| = |x_lst|)
    -- (if ($proj_uN_0(x).0 < |C.LOCALS_context|))*{x <- x_lst}
    -- (if (C.LOCALS_context[$proj_uN_0(x).0] = mk_localtype_localtype(SET_init, t)))*{t <- t_lst, x <- x_lst}
    -- wf_context: `%`(C)
    -- (wf_uN: `%%`(32, x))*{x <- x_lst}
    -- (wf_uN: `%%`(32, iter))*{iter <- $setminus_(syntax localidx, x_2_lst, x_1_lst)}
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_11_lst), x_1_lst, mk_list_resulttype(t_12_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_21_lst), x_2_lst, mk_list_resulttype(t_22_lst)))
    -- (wf_localtype: `%`(mk_localtype_localtype(SET_init, t)))*{t <- t_lst}

;; test.spectec:2226.1-2226.110
relation Limits_sub: `%|-%<:%`(context, limits, limits)
  ;; test.spectec:2234.1-2237.22
  rule max{C : context, n_1 : n, m_1 : m, n_2 : n, m_2_opt : m?}:
    `%|-%<:%`(C, mk_limits_limits(mk_uN_u64(n_1), ?(mk_uN_u64(m_1))), mk_limits_limits(mk_uN_u64(n_2), mk_uN_u64(m_2)?{m_2 <- m_2_opt}))
    -- if (n_1 >= n_2)
    -- (if (m_1 <= m_2))?{m_2 <- m_2_opt}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u64(n_1), ?(mk_uN_u64(m_1))))
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u64(n_2), mk_uN_u64(m_2)?{m_2 <- m_2_opt}))

  ;; test.spectec:2239.1-2241.19
  rule eps{C : context, n_1 : n, n_2 : n}:
    `%|-%<:%`(C, mk_limits_limits(mk_uN_u64(n_1), ?()), mk_limits_limits(mk_uN_u64(n_2), ?()))
    -- if (n_1 >= n_2)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u64(n_1), ?()))
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u64(n_2), ?()))

;; test.spectec:2227.1-2227.111
relation Tagtype_sub: `%|-%<:%`(context, tagtype, tagtype)
  ;; test.spectec:2244.1-2247.46
  rule mk_Tagtype_sub{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, $typeuse_deftype(deftype_1), $typeuse_deftype(deftype_2))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- Deftype_sub: `%|-%<:%`(C, deftype_2, deftype_1)
    -- wf_context: `%`(C)

;; test.spectec:2228.1-2228.114
relation Globaltype_sub: `%|-%<:%`(context, globaltype, globaltype)
  ;; test.spectec:2249.1-2251.46
  rule const{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, mk_globaltype_globaltype(?(), valtype_1), mk_globaltype_globaltype(?(), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- wf_context: `%`(C)
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(), valtype_1))
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(), valtype_2))

  ;; test.spectec:2253.1-2256.46
  rule var{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, mk_globaltype_globaltype(?(MUT_mut), valtype_1), mk_globaltype_globaltype(?(MUT_mut), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- Valtype_sub: `%|-%<:%`(C, valtype_2, valtype_1)
    -- wf_context: `%`(C)
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(MUT_mut), valtype_1))
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(MUT_mut), valtype_2))

;; test.spectec:2229.1-2229.111
relation Memtype_sub: `%|-%<:%`(context, memtype, memtype)
  ;; test.spectec:2258.1-2260.43
  rule mk_Memtype_sub{C : context, v_addrtype : addrtype, limits_1 : limits, limits_2 : limits}:
    `%|-%<:%`(C, `%%PAGE`_memtype(v_addrtype, limits_1), `%%PAGE`_memtype(v_addrtype, limits_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)
    -- wf_context: `%`(C)
    -- wf_memtype: `%`(`%%PAGE`_memtype(v_addrtype, limits_1))
    -- wf_memtype: `%`(`%%PAGE`_memtype(v_addrtype, limits_2))

;; test.spectec:2230.1-2230.113
relation Tabletype_sub: `%|-%<:%`(context, tabletype, tabletype)
  ;; test.spectec:2262.1-2266.46
  rule mk_Tabletype_sub{C : context, v_addrtype : addrtype, limits_1 : limits, reftype_1 : reftype, limits_2 : limits, reftype_2 : reftype}:
    `%|-%<:%`(C, mk_tabletype_tabletype(v_addrtype, limits_1, reftype_1), mk_tabletype_tabletype(v_addrtype, limits_2, reftype_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_2, reftype_1)
    -- wf_context: `%`(C)
    -- wf_tabletype: `%`(mk_tabletype_tabletype(v_addrtype, limits_1, reftype_1))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(v_addrtype, limits_2, reftype_2))

;; test.spectec:2231.1-2231.114
relation Externtype_sub: `%|-%<:%`(context, externtype, externtype)
  ;; test.spectec:2269.1-2271.46
  rule tag{C : context, tagtype_1 : tagtype, tagtype_2 : tagtype}:
    `%|-%<:%`(C, TAG_externtype(tagtype_1), TAG_externtype(tagtype_2))
    -- Tagtype_sub: `%|-%<:%`(C, tagtype_1, tagtype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TAG_externtype(tagtype_1))
    -- wf_externtype: `%`(TAG_externtype(tagtype_2))

  ;; test.spectec:2273.1-2275.55
  rule global{C : context, globaltype_1 : globaltype, globaltype_2 : globaltype}:
    `%|-%<:%`(C, GLOBAL_externtype(globaltype_1), GLOBAL_externtype(globaltype_2))
    -- Globaltype_sub: `%|-%<:%`(C, globaltype_1, globaltype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(GLOBAL_externtype(globaltype_1))
    -- wf_externtype: `%`(GLOBAL_externtype(globaltype_2))

  ;; test.spectec:2277.1-2279.46
  rule mem{C : context, memtype_1 : memtype, memtype_2 : memtype}:
    `%|-%<:%`(C, MEM_externtype(memtype_1), MEM_externtype(memtype_2))
    -- Memtype_sub: `%|-%<:%`(C, memtype_1, memtype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(MEM_externtype(memtype_1))
    -- wf_externtype: `%`(MEM_externtype(memtype_2))

  ;; test.spectec:2281.1-2283.52
  rule table{C : context, tabletype_1 : tabletype, tabletype_2 : tabletype}:
    `%|-%<:%`(C, TABLE_externtype(tabletype_1), TABLE_externtype(tabletype_2))
    -- Tabletype_sub: `%|-%<:%`(C, tabletype_1, tabletype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(TABLE_externtype(tabletype_1))
    -- wf_externtype: `%`(TABLE_externtype(tabletype_2))

  ;; test.spectec:2285.1-2287.46
  rule func{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, FUNC_externtype($typeuse_deftype(deftype_1)), FUNC_externtype($typeuse_deftype(deftype_2)))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(FUNC_externtype($typeuse_deftype(deftype_1)))
    -- wf_externtype: `%`(FUNC_externtype($typeuse_deftype(deftype_2)))

;; test.spectec:2337.1-2337.121
relation Blocktype_ok: `%|-%:%`(context, blocktype, instrtype)
  ;; test.spectec:2339.1-2341.38
  rule valtype{C : context, valtype_opt : valtype?}:
    `%|-%:%`(C, _RESULT_blocktype(valtype_opt), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype(lift(valtype_opt))))
    -- (Valtype_ok: `%|-%:OK`(C, v_valtype))?{v_valtype <- valtype_opt}
    -- wf_context: `%`(C)
    -- wf_blocktype: `%`(_RESULT_blocktype(valtype_opt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype(lift(valtype_opt))))

  ;; test.spectec:2343.1-2345.51
  rule typeidx{C : context, v_typeidx : typeidx, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, _IDX_blocktype(v_typeidx), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- if ($proj_uN_0(v_typeidx).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(v_typeidx).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_blocktype: `%`(_IDX_blocktype(v_typeidx))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

;; test.spectec:2459.1-2459.77
relation Catch_ok: `%|-%:OK`(context, catch)
  ;; test.spectec:2476.1-2479.44
  rule catch{C : context, x : idx, l : labelidx, t_lst : valtype*}:
    `%|-%:OK`(C, CATCH_catch(x, l))
    -- if ($as_deftype(C.TAGS_context[$proj_uN_0(x).0]) =/= ?())
    -- if ($proj_uN_0(x).0 < |C.TAGS_context|)
    -- Expand: `%~~%`(!($as_deftype(C.TAGS_context[$proj_uN_0(x).0])), `FUNC%->%`_comptype(mk_list_resulttype(t_lst), mk_list_resulttype([])))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_lst), C.LABELS_context[$proj_uN_0(l).0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_catch(x, l))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_lst), mk_list_resulttype([])))

  ;; test.spectec:2481.1-2484.54
  rule catch_ref{C : context, x : idx, l : labelidx, t_lst : valtype*}:
    `%|-%:OK`(C, CATCH_REF_catch(x, l))
    -- if ($as_deftype(C.TAGS_context[$proj_uN_0(x).0]) =/= ?())
    -- if ($proj_uN_0(x).0 < |C.TAGS_context|)
    -- Expand: `%~~%`(!($as_deftype(C.TAGS_context[$proj_uN_0(x).0])), `FUNC%->%`_comptype(mk_list_resulttype(t_lst), mk_list_resulttype([])))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_lst ++ [REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[$proj_uN_0(l).0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_REF_catch(x, l))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_lst), mk_list_resulttype([])))

  ;; test.spectec:2486.1-2488.45
  rule catch_all{C : context, l : labelidx}:
    `%|-%:OK`(C, CATCH_ALL_catch(l))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype([]), C.LABELS_context[$proj_uN_0(l).0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_ALL_catch(l))

  ;; test.spectec:2490.1-2492.51
  rule catch_all_ref{C : context, l : labelidx}:
    `%|-%:OK`(C, CATCH_ALL_REF_catch(l))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype([REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[$proj_uN_0(l).0])
    -- wf_context: `%`(C)
    -- wf_catch: `%`(CATCH_ALL_REF_catch(l))

;; test.spectec:4441.1-4441.44
def $default_(v_valtype : valtype) : val??
  ;; test.spectec:4442.1-4442.35
  def $default_(I32_valtype) = ?(?(CONST_val($numtype_addrtype(I32_Inn), mk_num__0_num_(I32_Inn, mk_uN_uN(0)))))
  ;; test.spectec:4442.1-4442.35
  def $default_(I64_valtype) = ?(?(CONST_val($numtype_addrtype(I64_Inn), mk_num__0_num_(I64_Inn, mk_uN_uN(0)))))
  ;; test.spectec:4443.1-4443.52
  def $default_(F32_valtype) = ?(?(CONST_val($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, $fzero($size($numtype_Fnn(F32_Fnn)))))))
  ;; test.spectec:4443.1-4443.52
  def $default_(F64_valtype) = ?(?(CONST_val($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, $fzero($size($numtype_Fnn(F64_Fnn)))))))
  ;; test.spectec:4444.1-4444.36
  def $default_(V128_valtype) = ?(?(VCONST_val(V128_vectype, mk_uN_vec_(0))))
  ;; test.spectec:4445.1-4445.43
  def $default_{ht : heaptype}(REF_valtype(?(NULL_null), ht)) = ?(?(REF_NULL_ADDR_val))
  ;; test.spectec:4446.1-4446.28
  def $default_{ht : heaptype}(REF_valtype(?(), ht)) = ?(?())
  def $default_{x0 : valtype}(x0) = ?()
    -- otherwise

;; test.spectec:4441.6-4441.15
relation default__is_wf: `%%`(v_valtype : valtype, ret_val_opt : val?)
  ;; test.spectec:4441.6-4441.15
  rule default__is_wf_0{v_valtype : valtype, ret_val_opt : val?}:
    `%%`(v_valtype, ret_val_opt)
    -- wf_valtype: `%`(v_valtype)
    -- if ($default_(v_valtype) =/= ?())
    -- if (ret_val_opt = !($default_(v_valtype)))
    -- (wf_val: `%`(ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:2304.1-2305.71
relation Defaultable: `|-%DEFAULTABLE`(valtype)
  ;; test.spectec:4449.1-4449.62
  rule mk_Defaultable{t : valtype}:
    `|-%DEFAULTABLE`(t)
    -- if ($default_(t) =/= ?())
    -- if (!($default_(t)) =/= ?())
    -- wf_valtype: `%`(t)
    -- (wf_val: `%`(iter))?{iter <- !($default_(t))}

;; test.spectec:2703.1-2703.131
relation Memarg_ok: `|-%:%->%`(memarg, addrtype, N)
  ;; test.spectec:2705.1-2708.27
  rule mk_Memarg_ok{v_n : n, v_m : m, at : addrtype, v_N : N}:
    `|-%:%->%`({ALIGN mk_uN_u32(v_n), OFFSET mk_uN_u64(v_m)}, at, v_N)
    -- if (((2 ^ v_n) : nat <:> rat) <= ((v_N : nat <:> rat) / (8 : nat <:> rat)))
    -- if (v_m < (2 ^ $size($numtype_addrtype(at))))
    -- wf_memarg: `%`({ALIGN mk_uN_u32(v_n), OFFSET mk_uN_u64(v_m)})

;; test.spectec:2550.1-2550.111
def $is_packtype(v_storagetype : storagetype) : bool
  ;; test.spectec:2551.1-2551.42
  def $is_packtype{zt : storagetype}(zt) = (zt =/= $storagetype_valtype($unpack(zt)))

;; test.spectec:2300.1-2301.96
rec {

;; test.spectec:2300.1-2300.95
relation Instr_ok: `%|-%:%`(context, instr, instrtype)
  ;; test.spectec:2313.1-2314.24
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(NOP_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))

  ;; test.spectec:2316.1-2318.42
  rule unreachable{C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNREACHABLE_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2320.1-2322.29
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, mk_instrtype_instrtype(mk_list_resulttype([t]), [], mk_list_resulttype([])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(DROP_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([t]), [], mk_list_resulttype([])))

  ;; test.spectec:2324.1-2326.29
  rule select_expl{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?([t])), mk_instrtype_instrtype(mk_list_resulttype([t t I32_valtype]), [], mk_list_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(SELECT_instr(?([t])))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([t t I32_valtype]), [], mk_list_resulttype([t])))

  ;; test.spectec:2328.1-2332.37
  rule select_impl{C : context, t : valtype, t' : valtype, v_numtype : numtype, v_vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), mk_instrtype_instrtype(mk_list_resulttype([t t I32_valtype]), [], mk_list_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- Valtype_sub: `%|-%<:%`(C, t, t')
    -- if ((t' = $valtype_numtype(v_numtype)) \/ (t' = $valtype_vectype(v_vectype)))
    -- wf_context: `%`(C)
    -- wf_valtype: `%`(t')
    -- wf_instr: `%`(SELECT_instr(?()))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([t t I32_valtype]), [], mk_list_resulttype([t])))

  ;; test.spectec:2348.1-2351.67
  rule block{C : context, bt : blocktype, instr_lst : instr*, t_1_lst : valtype*, t_2_lst : valtype*, x_lst : idx*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr_lst), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Blocktype_ok: `%|-%:%`(C, bt, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []} +++ C, instr_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BLOCK_instr(bt, instr_lst))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2353.1-2356.67
  rule loop{C : context, bt : blocktype, instr_lst : instr*, t_1_lst : valtype*, t_2_lst : valtype*, x_lst : idx*}:
    `%|-%:%`(C, LOOP_instr(bt, instr_lst), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Blocktype_ok: `%|-%:%`(C, bt, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_1_lst)], RETURN ?(), REFS [], RECS []} +++ C, instr_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOOP_instr(bt, instr_lst))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_1_lst)], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2358.1-2362.71
  rule if{C : context, bt : blocktype, instr_1_lst : instr*, instr_2_lst : instr*, t_1_lst : valtype*, t_2_lst : valtype*, x_1_lst : idx*, x_2_lst : idx*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(bt, instr_1_lst, instr_2_lst), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [I32_valtype]), [], mk_list_resulttype(t_2_lst)))
    -- Blocktype_ok: `%|-%:%`(C, bt, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []} +++ C, instr_1_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_1_lst, mk_list_resulttype(t_2_lst)))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []} +++ C, instr_2_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_2_lst, mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`IF%%ELSE%`_instr(bt, instr_1_lst, instr_2_lst))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [I32_valtype]), [], mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_1_lst, mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_2_lst, mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2367.1-2370.42
  rule br{C : context, l : labelidx, t_1_lst : valtype*, t_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, BR_instr(l), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst), [], mk_list_resulttype(t_2_lst)))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if ($proj_list_0(syntax valtype, C.LABELS_context[$proj_uN_0(l).0]).0 = t_lst)
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_instr(l))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2372.1-2374.25
  rule br_if{C : context, l : labelidx, t_lst : valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [I32_valtype]), [], mk_list_resulttype(t_lst)))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if ($proj_list_0(syntax valtype, C.LABELS_context[$proj_uN_0(l).0]).0 = t_lst)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_IF_instr(l))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [I32_valtype]), [], mk_list_resulttype(t_lst)))

  ;; test.spectec:2376.1-2380.49
  rule br_table{C : context, l_lst : labelidx*, l' : labelidx, t_1_lst : valtype*, t_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l_lst, l'), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst ++ [I32_valtype]), [], mk_list_resulttype(t_2_lst)))
    -- (if ($proj_uN_0(l).0 < |C.LABELS_context|))*{l <- l_lst}
    -- (Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_lst), C.LABELS_context[$proj_uN_0(l).0]))*{l <- l_lst}
    -- if ($proj_uN_0(l').0 < |C.LABELS_context|)
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_lst), C.LABELS_context[$proj_uN_0(l').0])
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst ++ [I32_valtype]), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_TABLE_instr(l_lst, l'))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst ++ [I32_valtype]), [], mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2382.1-2385.31
  rule br_on_null{C : context, l : labelidx, t_lst : valtype*, ht : heaptype}:
    `%|-%:%`(C, BR_ON_NULL_instr(l), mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype(t_lst ++ [REF_valtype(?(), ht)])))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if ($proj_list_0(syntax valtype, C.LABELS_context[$proj_uN_0(l).0]).0 = t_lst)
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_ON_NULL_instr(l))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype(t_lst ++ [REF_valtype(?(), ht)])))

  ;; test.spectec:2387.1-2389.40
  rule br_on_non_null{C : context, l : labelidx, t_lst : valtype*, ht : heaptype}:
    `%|-%:%`(C, BR_ON_NON_NULL_instr(l), mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype(t_lst)))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = mk_list_resulttype(t_lst ++ [REF_valtype(?(NULL_null), ht)]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_ON_NON_NULL_instr(l))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype(t_lst)))

  ;; test.spectec:2391.1-2397.34
  rule br_on_cast{C : context, l : labelidx, rt_1 : reftype, rt_2 : reftype, t_lst : valtype*, rt : reftype}:
    `%|-%:%`(C, BR_ON_CAST_instr(l, rt_1, rt_2), mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [$valtype_reftype(rt_1)]), [], mk_list_resulttype(t_lst ++ [$valtype_reftype($diffrt(rt_1, rt_2))])))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = mk_list_resulttype(t_lst ++ [$valtype_reftype(rt)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_instr: `%`(BR_ON_CAST_instr(l, rt_1, rt_2))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [$valtype_reftype(rt_1)]), [], mk_list_resulttype(t_lst ++ [$valtype_reftype($diffrt(rt_1, rt_2))])))

  ;; test.spectec:2399.1-2405.49
  rule br_on_cast_fail{C : context, l : labelidx, rt_1 : reftype, rt_2 : reftype, t_lst : valtype*, rt : reftype}:
    `%|-%:%`(C, BR_ON_CAST_FAIL_instr(l, rt_1, rt_2), mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [$valtype_reftype(rt_1)]), [], mk_list_resulttype(t_lst ++ [$valtype_reftype(rt_2)])))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = mk_list_resulttype(t_lst ++ [$valtype_reftype(rt)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, $diffrt(rt_1, rt_2), rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_reftype: `%`($diffrt(rt_1, rt_2))
    -- wf_instr: `%`(BR_ON_CAST_FAIL_instr(l, rt_1, rt_2))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ [$valtype_reftype(rt_1)]), [], mk_list_resulttype(t_lst ++ [$valtype_reftype(rt_2)])))

  ;; test.spectec:2410.1-2412.45
  rule call{C : context, x : idx, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, CALL_instr(x), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- Expand: `%~~%`(C.FUNCS_context[$proj_uN_0(x).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2414.1-2416.45
  rule call_ref{C : context, x : idx, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, CALL_REF_instr(_IDX_typeuse(x)), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], mk_list_resulttype(t_2_lst)))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_REF_instr(_IDX_typeuse(x)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], mk_list_resulttype(t_2_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2418.1-2422.45
  rule call_indirect{C : context, x : idx, y : idx, t_1_lst : valtype*, at : addrtype, t_2_lst : valtype*, lim : limits, rt : reftype}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, _IDX_typeuse(y)), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [$valtype_addrtype(at)]), [], mk_list_resulttype(t_2_lst)))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- if ($proj_uN_0(y).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(y).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_INDIRECT_instr(x, _IDX_typeuse(y)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [$valtype_addrtype(at)]), [], mk_list_resulttype(t_2_lst)))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), FUNC_heaptype))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2424.1-2427.42
  rule return{C : context, t_1_lst : valtype*, t_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, RETURN_instr, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst), [], mk_list_resulttype(t_2_lst)))
    -- if (C.RETURN_context = ?(mk_list_resulttype(t_lst)))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RETURN_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2430.1-2435.42
  rule return_call{C : context, x : idx, t_3_lst : valtype*, t_1_lst : valtype*, t_4_lst : valtype*, t_2_lst : valtype*, t'_2_lst : valtype*}:
    `%|-%:%`(C, RETURN_CALL_instr(x), mk_instrtype_instrtype(mk_list_resulttype(t_3_lst ++ t_1_lst), [], mk_list_resulttype(t_4_lst)))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- Expand: `%~~%`(C.FUNCS_context[$proj_uN_0(x).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- if (C.RETURN_context = ?(mk_list_resulttype(t'_2_lst)))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_2_lst), mk_list_resulttype(t'_2_lst))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_3_lst), [], mk_list_resulttype(t_4_lst)))
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t'_2))*{t'_2 <- t'_2_lst}
    -- wf_instr: `%`(RETURN_CALL_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_3_lst ++ t_1_lst), [], mk_list_resulttype(t_4_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_3_lst), [], mk_list_resulttype(t_4_lst)))

  ;; test.spectec:2438.1-2443.42
  rule return_call_ref{C : context, x : idx, t_3_lst : valtype*, t_1_lst : valtype*, t_4_lst : valtype*, t_2_lst : valtype*, t'_2_lst : valtype*}:
    `%|-%:%`(C, RETURN_CALL_REF_instr(_IDX_typeuse(x)), mk_instrtype_instrtype(mk_list_resulttype(t_3_lst ++ t_1_lst ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], mk_list_resulttype(t_4_lst)))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- if (C.RETURN_context = ?(mk_list_resulttype(t'_2_lst)))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_2_lst), mk_list_resulttype(t'_2_lst))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_3_lst), [], mk_list_resulttype(t_4_lst)))
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t'_2))*{t'_2 <- t'_2_lst}
    -- wf_instr: `%`(RETURN_CALL_REF_instr(_IDX_typeuse(x)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_3_lst ++ t_1_lst ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], mk_list_resulttype(t_4_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_3_lst), [], mk_list_resulttype(t_4_lst)))

  ;; test.spectec:2446.1-2454.42
  rule return_call_indirect{C : context, x : idx, y : idx, t_3_lst : valtype*, t_1_lst : valtype*, at : addrtype, t_4_lst : valtype*, lim : limits, rt : reftype, t_2_lst : valtype*, t'_2_lst : valtype*}:
    `%|-%:%`(C, RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y)), mk_instrtype_instrtype(mk_list_resulttype(t_3_lst ++ t_1_lst ++ [$valtype_addrtype(at)]), [], mk_list_resulttype(t_4_lst)))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- if ($proj_uN_0(y).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(y).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- if (C.RETURN_context = ?(mk_list_resulttype(t'_2_lst)))
    -- Resulttype_sub: `%|-%<:%`(C, mk_list_resulttype(t_2_lst), mk_list_resulttype(t'_2_lst))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_3_lst), [], mk_list_resulttype(t_4_lst)))
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`(t'_2))*{t'_2 <- t'_2_lst}
    -- wf_instr: `%`(RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_3_lst ++ t_1_lst ++ [$valtype_addrtype(at)]), [], mk_list_resulttype(t_4_lst)))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), FUNC_heaptype))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_3_lst), [], mk_list_resulttype(t_4_lst)))

  ;; test.spectec:2461.1-2464.42
  rule throw{C : context, x : idx, t_1_lst : valtype*, t_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, THROW_instr(x), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst), [], mk_list_resulttype(t_2_lst)))
    -- if ($as_deftype(C.TAGS_context[$proj_uN_0(x).0]) =/= ?())
    -- if ($proj_uN_0(x).0 < |C.TAGS_context|)
    -- Expand: `%~~%`(!($as_deftype(C.TAGS_context[$proj_uN_0(x).0])), `FUNC%->%`_comptype(mk_list_resulttype(t_lst), mk_list_resulttype([])))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(THROW_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ t_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_lst), mk_list_resulttype([])))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2466.1-2468.42
  rule throw_ref{C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, THROW_REF_instr, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [REF_valtype(?(NULL_null), EXN_heaptype)]), [], mk_list_resulttype(t_2_lst)))
    -- Instrtype_ok: `%|-%:OK`(C, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(THROW_REF_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst ++ [REF_valtype(?(NULL_null), EXN_heaptype)]), [], mk_list_resulttype(t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2470.1-2474.34
  rule try_table{C : context, bt : blocktype, catch_lst : catch*, instr_lst : instr*, t_1_lst : valtype*, t_2_lst : valtype*, x_lst : idx*}:
    `%|-%:%`(C, TRY_TABLE_instr(bt, mk_list_list(catch_lst), instr_lst), mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Blocktype_ok: `%|-%:%`(C, bt, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []} +++ C, instr_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))
    -- (Catch_ok: `%|-%:OK`(C, v_catch))*{v_catch <- catch_lst}
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TRY_TABLE_instr(bt, mk_list_list(catch_lst), instr_lst))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), [], mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(), REFS [], RECS []})
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))

  ;; test.spectec:2497.1-2499.31
  rule ref_null{C : context, ht : heaptype}:
    `%|-%:%`(C, REF_NULL_instr(ht), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([REF_valtype(?(NULL_null), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_NULL_instr(ht))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([REF_valtype(?(NULL_null), ht)])))

  ;; test.spectec:2501.1-2504.20
  rule ref_func{C : context, x : idx, dt : deftype}:
    `%|-%:%`(C, REF_FUNC_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([REF_valtype(?(), $heaptype_deftype(dt))])))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = dt)
    -- if (|C.REFS_context| > 0)
    -- if (x <- C.REFS_context)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_FUNC_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([REF_valtype(?(), $heaptype_deftype(dt))])))

  ;; test.spectec:2506.1-2507.34
  rule ref_i31{C : context}:
    `%|-%:%`(C, REF_I31_instr, mk_instrtype_instrtype(mk_list_resulttype([I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), I31_heaptype)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_I31_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), I31_heaptype)])))

  ;; test.spectec:2509.1-2511.31
  rule ref_is_null{C : context, ht : heaptype}:
    `%|-%:%`(C, REF_IS_NULL_instr, mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype([I32_valtype])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_IS_NULL_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2513.1-2515.31
  rule ref_as_non_null{C : context, ht : heaptype}:
    `%|-%:%`(C, REF_AS_NON_NULL_instr, mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype([REF_valtype(?(), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_AS_NON_NULL_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), ht)]), [], mk_list_resulttype([REF_valtype(?(), ht)])))

  ;; test.spectec:2517.1-2518.51
  rule ref_eq{C : context}:
    `%|-%:%`(C, REF_EQ_instr, mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), EQ_heaptype) REF_valtype(?(NULL_null), EQ_heaptype)]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_EQ_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), EQ_heaptype) REF_valtype(?(NULL_null), EQ_heaptype)]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2520.1-2524.33
  rule ref_test{C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, REF_TEST_instr(rt), mk_instrtype_instrtype(mk_list_resulttype([$valtype_reftype(rt')]), [], mk_list_resulttype([I32_valtype])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_TEST_instr(rt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_reftype(rt')]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2526.1-2530.33
  rule ref_cast{C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, REF_CAST_instr(rt), mk_instrtype_instrtype(mk_list_resulttype([$valtype_reftype(rt')]), [], mk_list_resulttype([$valtype_reftype(rt)])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_CAST_instr(rt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_reftype(rt')]), [], mk_list_resulttype([$valtype_reftype(rt)])))

  ;; test.spectec:2535.1-2536.42
  rule i31_get{C : context, v_sx : sx}:
    `%|-%:%`(C, I31_GET_instr(v_sx), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), I31_heaptype)]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(I31_GET_instr(v_sx))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), I31_heaptype)]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2541.1-2543.45
  rule struct_new{C : context, x : idx, zt_lst : storagetype*, mut_opt_lst : mut?*}:
    `%|-%:%`(C, STRUCT_NEW_instr(x), mk_instrtype_instrtype(mk_list_resulttype($unpack(zt)*{zt <- zt_lst}), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], STRUCT_comptype(mk_list_list(mk_fieldtype_fieldtype(mut_opt, zt)*{mut_opt <- mut_opt_lst, zt <- zt_lst})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STRUCT_NEW_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype($unpack(zt)*{zt <- zt_lst}), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(mk_fieldtype_fieldtype(mut_opt, zt)*{mut_opt <- mut_opt_lst, zt <- zt_lst})))

  ;; test.spectec:2545.1-2548.48
  rule struct_new_default{C : context, x : idx, mut_opt_lst : mut?*, zt_lst : storagetype*}:
    `%|-%:%`(C, STRUCT_NEW_DEFAULT_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], STRUCT_comptype(mk_list_list(mk_fieldtype_fieldtype(mut_opt, zt)*{mut_opt <- mut_opt_lst, zt <- zt_lst})))
    -- (Defaultable: `|-%DEFAULTABLE`($unpack(zt)))*{zt <- zt_lst}
    -- wf_context: `%`(C)
    -- (wf_valtype: `%`($unpack(zt)))*{zt <- zt_lst}
    -- wf_instr: `%`(STRUCT_NEW_DEFAULT_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(mk_fieldtype_fieldtype(mut_opt, zt)*{mut_opt <- mut_opt_lst, zt <- zt_lst})))

  ;; test.spectec:2553.1-2557.41
  rule struct_get{C : context, sx_opt : sx?, x : idx, i : fieldidx, zt : storagetype, ft_lst : fieldtype*, mut_opt : mut?}:
    `%|-%:%`(C, STRUCT_GET_instr(sx_opt, x, i), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], mk_list_resulttype([$unpack(zt)])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], STRUCT_comptype(mk_list_list(ft_lst)))
    -- if ($proj_uN_0(i).0 < |ft_lst|)
    -- if (ft_lst[$proj_uN_0(i).0] = mk_fieldtype_fieldtype(mut_opt, zt))
    -- if ((sx_opt =/= ?()) <=> $is_packtype(zt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STRUCT_GET_instr(sx_opt, x, i))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], mk_list_resulttype([$unpack(zt)])))
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(ft_lst)))
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(mut_opt, zt))

  ;; test.spectec:2559.1-2562.24
  rule struct_set{C : context, x : idx, i : fieldidx, zt : storagetype, ft_lst : fieldtype*}:
    `%|-%:%`(C, STRUCT_SET_instr(x, i), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) $unpack(zt)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], STRUCT_comptype(mk_list_list(ft_lst)))
    -- if ($proj_uN_0(i).0 < |ft_lst|)
    -- if (ft_lst[$proj_uN_0(i).0] = mk_fieldtype_fieldtype(?(MUT_mut), zt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STRUCT_SET_instr(x, i))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) $unpack(zt)]), [], mk_list_resulttype([])))
    -- wf_comptype: `%`(STRUCT_comptype(mk_list_list(ft_lst)))
    -- wf_fieldtype: `%`(mk_fieldtype_fieldtype(?(MUT_mut), zt))

  ;; test.spectec:2567.1-2569.43
  rule array_new{C : context, x : idx, zt : storagetype, mut_opt : mut?}:
    `%|-%:%`(C, ARRAY_NEW_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$unpack(zt) I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_NEW_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$unpack(zt) I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))

  ;; test.spectec:2571.1-2574.45
  rule array_new_default{C : context, x : idx, mut_opt : mut?, zt : storagetype}:
    `%|-%:%`(C, ARRAY_NEW_DEFAULT_instr(x), mk_instrtype_instrtype(mk_list_resulttype([I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))
    -- Defaultable: `|-%DEFAULTABLE`($unpack(zt))
    -- wf_context: `%`(C)
    -- wf_valtype: `%`($unpack(zt))
    -- wf_instr: `%`(ARRAY_NEW_DEFAULT_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))

  ;; test.spectec:2576.1-2578.43
  rule array_new_fixed{C : context, x : idx, v_n : n, zt : storagetype, mut_opt : mut?}:
    `%|-%:%`(C, ARRAY_NEW_FIXED_instr(x, mk_uN_u32(v_n)), mk_instrtype_instrtype(mk_list_resulttype($unpack(zt)^v_n{}), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_NEW_FIXED_instr(x, mk_uN_u32(v_n)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype($unpack(zt)^v_n{}), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))

  ;; test.spectec:2580.1-2583.40
  rule array_new_elem{C : context, x : idx, y : idx, mut_opt : mut?, rt : reftype}:
    `%|-%:%`(C, ARRAY_NEW_ELEM_instr(x, y), mk_instrtype_instrtype(mk_list_resulttype([I32_valtype I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, $storagetype_reftype(rt))))
    -- if ($proj_uN_0(y).0 < |C.ELEMS_context|)
    -- Reftype_sub: `%|-%<:%`(C, C.ELEMS_context[$proj_uN_0(y).0], rt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_NEW_ELEM_instr(x, y))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([I32_valtype I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, $storagetype_reftype(rt))))

  ;; test.spectec:2585.1-2589.24
  rule array_new_data{C : context, x : idx, y : idx, mut_opt : mut?, zt : storagetype, v_numtype : numtype, v_vectype : vectype}:
    `%|-%:%`(C, ARRAY_NEW_DATA_instr(x, y), mk_instrtype_instrtype(mk_list_resulttype([I32_valtype I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))
    -- if (($unpack(zt) = $valtype_numtype(v_numtype)) \/ ($unpack(zt) = $valtype_vectype(v_vectype)))
    -- if ($proj_uN_0(y).0 < |C.DATAS_context|)
    -- if (C.DATAS_context[$proj_uN_0(y).0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`($unpack(zt))
    -- wf_instr: `%`(ARRAY_NEW_DATA_instr(x, y))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([I32_valtype I32_valtype]), [], mk_list_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))

  ;; test.spectec:2591.1-2594.41
  rule array_get{C : context, sx_opt : sx?, x : idx, zt : storagetype, mut_opt : mut?}:
    `%|-%:%`(C, ARRAY_GET_instr(sx_opt, x), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype]), [], mk_list_resulttype([$unpack(zt)])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))
    -- if ((sx_opt =/= ?()) <=> $is_packtype(zt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_GET_instr(sx_opt, x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype]), [], mk_list_resulttype([$unpack(zt)])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt)))

  ;; test.spectec:2596.1-2598.42
  rule array_set{C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY_SET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_SET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt)]), [], mk_list_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2600.1-2601.43
  rule array_len{C : context}:
    `%|-%:%`(C, ARRAY_LEN_instr, mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), ARRAY_heaptype)]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_LEN_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), ARRAY_heaptype)]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2603.1-2605.42
  rule array_fill{C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY_FILL_instr(x), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt) I32_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_FILL_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt) I32_valtype]), [], mk_list_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2607.1-2611.40
  rule array_copy{C : context, x_1 : idx, x_2 : idx, zt_1 : storagetype, mut_opt : mut?, zt_2 : storagetype}:
    `%|-%:%`(C, ARRAY_COPY_instr(x_1, x_2), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x_1)) I32_valtype REF_valtype(?(NULL_null), _IDX_heaptype(x_2)) I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x_1).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x_1).0], ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt_1)))
    -- if ($proj_uN_0(x_2).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x_2).0], ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt_2)))
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_COPY_instr(x_1, x_2))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x_1)) I32_valtype REF_valtype(?(NULL_null), _IDX_heaptype(x_2)) I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt_1)))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(mut_opt, zt_2)))

  ;; test.spectec:2613.1-2616.44
  rule array_init_elem{C : context, x : idx, y : idx, zt : storagetype}:
    `%|-%:%`(C, ARRAY_INIT_ELEM_instr(x, y), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))
    -- if ($proj_uN_0(y).0 < |C.ELEMS_context|)
    -- Storagetype_sub: `%|-%<:%`(C, $storagetype_reftype(C.ELEMS_context[$proj_uN_0(y).0]), zt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_INIT_ELEM_instr(x, y))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2618.1-2622.24
  rule array_init_data{C : context, x : idx, y : idx, zt : storagetype, v_numtype : numtype, v_vectype : vectype}:
    `%|-%:%`(C, ARRAY_INIT_DATA_instr(x, y), mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))
    -- if (($unpack(zt) = $valtype_numtype(v_numtype)) \/ ($unpack(zt) = $valtype_vectype(v_vectype)))
    -- if ($proj_uN_0(y).0 < |C.DATAS_context|)
    -- if (C.DATAS_context[$proj_uN_0(y).0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_valtype: `%`($unpack(zt))
    -- wf_instr: `%`(ARRAY_INIT_DATA_instr(x, y))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- wf_comptype: `%`(ARRAY_comptype(mk_fieldtype_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2627.1-2629.26
  rule extern_convert_any{C : context, null_1_opt : null?, null_2_opt : null?}:
    `%|-%:%`(C, EXTERN_CONVERT_ANY_instr, mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(null_1_opt, ANY_heaptype)]), [], mk_list_resulttype([REF_valtype(null_2_opt, EXTERN_heaptype)])))
    -- if (null_1_opt = null_2_opt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(EXTERN_CONVERT_ANY_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(null_1_opt, ANY_heaptype)]), [], mk_list_resulttype([REF_valtype(null_2_opt, EXTERN_heaptype)])))

  ;; test.spectec:2631.1-2633.26
  rule any_convert_extern{C : context, null_1_opt : null?, null_2_opt : null?}:
    `%|-%:%`(C, ANY_CONVERT_EXTERN_instr, mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(null_1_opt, EXTERN_heaptype)]), [], mk_list_resulttype([REF_valtype(null_2_opt, ANY_heaptype)])))
    -- if (null_1_opt = null_2_opt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ANY_CONVERT_EXTERN_instr)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([REF_valtype(null_1_opt, EXTERN_heaptype)]), [], mk_list_resulttype([REF_valtype(null_2_opt, ANY_heaptype)])))

  ;; test.spectec:2638.1-2640.28
  rule local_get{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_GET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([t])))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = mk_localtype_localtype(SET_init, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_GET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([t])))
    -- wf_localtype: `%`(mk_localtype_localtype(SET_init, t))

  ;; test.spectec:2642.1-2644.29
  rule local_set{C : context, x : idx, t : valtype, v_init : init}:
    `%|-%:%`(C, LOCAL_SET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([t]), [x], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = mk_localtype_localtype(v_init, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_SET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([t]), [x], mk_list_resulttype([])))
    -- wf_localtype: `%`(mk_localtype_localtype(v_init, t))

  ;; test.spectec:2646.1-2648.29
  rule local_tee{C : context, x : idx, t : valtype, v_init : init}:
    `%|-%:%`(C, LOCAL_TEE_instr(x), mk_instrtype_instrtype(mk_list_resulttype([t]), [x], mk_list_resulttype([t])))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = mk_localtype_localtype(v_init, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_TEE_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([t]), [x], mk_list_resulttype([t])))
    -- wf_localtype: `%`(mk_localtype_localtype(v_init, t))

  ;; test.spectec:2653.1-2655.30
  rule global_get{C : context, x : idx, t : valtype, mut_opt : mut?}:
    `%|-%:%`(C, GLOBAL_GET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([t])))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(mut_opt, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_GET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([t])))
    -- wf_globaltype: `%`(mk_globaltype_globaltype(mut_opt, t))

  ;; test.spectec:2657.1-2659.29
  rule global_set{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, GLOBAL_SET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([t]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(?(MUT_mut), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_SET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([t]), [], mk_list_resulttype([])))
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(MUT_mut), t))

  ;; test.spectec:2664.1-2666.32
  rule table_get{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, TABLE_GET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_reftype(rt)])))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TABLE_GET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_reftype(rt)])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))

  ;; test.spectec:2668.1-2670.32
  rule table_set{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, TABLE_SET_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_reftype(rt)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TABLE_SET_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_reftype(rt)]), [], mk_list_resulttype([])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))

  ;; test.spectec:2672.1-2674.32
  rule table_size{C : context, x : idx, at : addrtype, lim : limits, rt : reftype}:
    `%|-%:%`(C, TABLE_SIZE_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TABLE_SIZE_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))

  ;; test.spectec:2676.1-2678.32
  rule table_grow{C : context, x : idx, rt : reftype, at : addrtype, lim : limits}:
    `%|-%:%`(C, TABLE_GROW_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$valtype_reftype(rt) $valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TABLE_GROW_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_reftype(rt) $valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))

  ;; test.spectec:2680.1-2682.32
  rule table_fill{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, TABLE_FILL_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_reftype(rt) $valtype_addrtype(at)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TABLE_FILL_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_reftype(rt) $valtype_addrtype(at)]), [], mk_list_resulttype([])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))

  ;; test.spectec:2684.1-2688.36
  rule table_copy{C : context, x_1 : idx, x_2 : idx, at_1 : addrtype, at_2 : addrtype, lim_1 : limits, rt_1 : reftype, lim_2 : limits, rt_2 : reftype}:
    `%|-%:%`(C, TABLE_COPY_instr(x_1, x_2), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at_1) $valtype_addrtype(at_2) $valtype_addrtype($minat(at_1, at_2))]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x_1).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x_1).0] = mk_tabletype_tabletype(at_1, lim_1, rt_1))
    -- if ($proj_uN_0(x_2).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x_2).0] = mk_tabletype_tabletype(at_2, lim_2, rt_2))
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TABLE_COPY_instr(x_1, x_2))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at_1) $valtype_addrtype(at_2) $valtype_addrtype($minat(at_1, at_2))]), [], mk_list_resulttype([])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at_1, lim_1, rt_1))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at_2, lim_2, rt_2))

  ;; test.spectec:2690.1-2694.36
  rule table_init{C : context, x : idx, y : idx, at : addrtype, lim : limits, rt_1 : reftype, rt_2 : reftype}:
    `%|-%:%`(C, TABLE_INIT_instr(x, y), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt_1))
    -- if ($proj_uN_0(y).0 < |C.ELEMS_context|)
    -- if (C.ELEMS_context[$proj_uN_0(y).0] = rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt_2)
    -- wf_instr: `%`(TABLE_INIT_instr(x, y))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt_1))

  ;; test.spectec:2696.1-2698.24
  rule elem_drop{C : context, x : idx, rt : reftype}:
    `%|-%:%`(C, ELEM_DROP_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.ELEMS_context|)
    -- if (C.ELEMS_context[$proj_uN_0(x).0] = rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_instr: `%`(ELEM_DROP_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))

  ;; test.spectec:2711.1-2713.32
  rule memory_size{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, MEMORY_SIZE_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(MEMORY_SIZE_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2715.1-2717.32
  rule memory_grow{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, MEMORY_GROW_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(MEMORY_GROW_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_addrtype(at)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2719.1-2721.32
  rule memory_fill{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, MEMORY_FILL_instr(x), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) I32_valtype $valtype_addrtype(at)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(MEMORY_FILL_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) I32_valtype $valtype_addrtype(at)]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2723.1-2726.38
  rule memory_copy{C : context, x_1 : idx, x_2 : idx, at_1 : addrtype, at_2 : addrtype, lim_1 : limits, lim_2 : limits}:
    `%|-%:%`(C, MEMORY_COPY_instr(x_1, x_2), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at_1) $valtype_addrtype(at_2) $valtype_addrtype($minat(at_1, at_2))]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x_1).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x_1).0] = `%%PAGE`_memtype(at_1, lim_1))
    -- if ($proj_uN_0(x_2).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x_2).0] = `%%PAGE`_memtype(at_2, lim_2))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(MEMORY_COPY_instr(x_1, x_2))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at_1) $valtype_addrtype(at_2) $valtype_addrtype($minat(at_1, at_2))]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at_1, lim_1))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at_2, lim_2))

  ;; test.spectec:2728.1-2731.24
  rule memory_init{C : context, x : idx, y : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, MEMORY_INIT_instr(x, y), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- if ($proj_uN_0(y).0 < |C.DATAS_context|)
    -- if (C.DATAS_context[$proj_uN_0(y).0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(MEMORY_INIT_instr(x, y))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) I32_valtype I32_valtype]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2733.1-2735.24
  rule data_drop{C : context, x : idx}:
    `%|-%:%`(C, DATA_DROP_instr(x), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.DATAS_context|)
    -- if (C.DATAS_context[$proj_uN_0(x).0] = OK_datatype)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(DATA_DROP_instr(x))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))

  ;; test.spectec:2746.1-2749.44
  rule load_val{C : context, nt : numtype, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, LOAD_instr(nt, ?(), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_numtype(nt)])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, $size(nt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOAD_instr(nt, ?(), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_numtype(nt)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2751.1-2754.36
  rule load_pack{C : context, v_Inn : Inn, v_M : M, v_sx : sx, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, LOAD_instr($numtype_addrtype(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_M), v_sx))), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_addrtype(v_Inn)])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, v_M)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOAD_instr($numtype_addrtype(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_M), v_sx))), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([$valtype_addrtype(v_Inn)])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2765.1-2768.44
  rule store_val{C : context, nt : numtype, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, STORE_instr(nt, ?(), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_numtype(nt)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, $size(nt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STORE_instr(nt, ?(), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_numtype(nt)]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2770.1-2773.36
  rule store_pack{C : context, v_Inn : Inn, v_M : M, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, STORE_instr($numtype_addrtype(v_Inn), ?(mk_storeop__0_storeop_(v_Inn, mk_storeop_Inn_storeop_Inn(mk_sz_sz(v_M)))), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_addrtype(v_Inn)]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, v_M)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STORE_instr($numtype_addrtype(v_Inn), ?(mk_storeop__0_storeop_(v_Inn, mk_storeop_Inn_storeop_Inn(mk_sz_sz(v_M)))), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) $valtype_addrtype(v_Inn)]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2775.1-2778.47
  rule vload_val{C : context, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, $vsize(V128_vectype))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2780.1-2783.41
  rule vload_pack{C : context, v_M : M, v_N : N, v_sx : sx, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(mk_sz_sz(v_M), v_N, v_sx)), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, (v_M * v_N))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(mk_sz_sz(v_M), v_N, v_sx)), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2785.1-2788.36
  rule vload_splat{C : context, v_N : N, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(mk_sz_sz(v_N))), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, v_N)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(mk_sz_sz(v_N))), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2790.1-2793.36
  rule vload_zero{C : context, v_N : N, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(mk_sz_sz(v_N))), x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, v_N)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(mk_sz_sz(v_N))), x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at)]), [], mk_list_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2795.1-2799.21
  rule vload_lane{C : context, v_N : N, x : idx, v_memarg : memarg, i : laneidx, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_LANE_instr(V128_vectype, mk_sz_sz(v_N), x, v_memarg, i), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, v_N)
    -- if (($proj_uN_0(i).0 : nat <:> rat) < ((128 : nat <:> rat) / (v_N : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VLOAD_LANE_instr(V128_vectype, mk_sz_sz(v_N), x, v_memarg, i))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2801.1-2804.47
  rule vstore{C : context, x : idx, v_memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VSTORE_instr(V128_vectype, x, v_memarg), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) V128_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, $vsize(V128_vectype))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSTORE_instr(V128_vectype, x, v_memarg))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) V128_valtype]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2806.1-2810.21
  rule vstore_lane{C : context, v_N : N, x : idx, v_memarg : memarg, i : laneidx, at : addrtype, lim : limits}:
    `%|-%:%`(C, VSTORE_LANE_instr(V128_vectype, mk_sz_sz(v_N), x, v_memarg, i), mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) V128_valtype]), [], mk_list_resulttype([])))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(v_memarg, at, v_N)
    -- if (($proj_uN_0(i).0 : nat <:> rat) < ((128 : nat <:> rat) / (v_N : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSTORE_LANE_instr(V128_vectype, mk_sz_sz(v_N), x, v_memarg, i))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_addrtype(at) V128_valtype]), [], mk_list_resulttype([])))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

  ;; test.spectec:2815.1-2816.33
  rule const{C : context, nt : numtype, c_nt : num_}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([$valtype_numtype(nt)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(nt, c_nt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([$valtype_numtype(nt)])))

  ;; test.spectec:2818.1-2819.34
  rule unop{C : context, nt : numtype, unop_nt : unop_}:
    `%|-%:%`(C, UNOP_instr(nt, unop_nt), mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt)]), [], mk_list_resulttype([$valtype_numtype(nt)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNOP_instr(nt, unop_nt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt)]), [], mk_list_resulttype([$valtype_numtype(nt)])))

  ;; test.spectec:2821.1-2822.39
  rule binop{C : context, nt : numtype, binop_nt : binop_}:
    `%|-%:%`(C, BINOP_instr(nt, binop_nt), mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt) $valtype_numtype(nt)]), [], mk_list_resulttype([$valtype_numtype(nt)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr(nt, binop_nt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt) $valtype_numtype(nt)]), [], mk_list_resulttype([$valtype_numtype(nt)])))

  ;; test.spectec:2824.1-2825.39
  rule testop{C : context, nt : numtype, testop_nt : testop_}:
    `%|-%:%`(C, TESTOP_instr(nt, testop_nt), mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt)]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TESTOP_instr(nt, testop_nt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt)]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2827.1-2828.40
  rule relop{C : context, nt : numtype, relop_nt : relop_}:
    `%|-%:%`(C, RELOP_instr(nt, relop_nt), mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt) $valtype_numtype(nt)]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RELOP_instr(nt, relop_nt))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt) $valtype_numtype(nt)]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2830.1-2831.44
  rule cvtop{C : context, nt_1 : numtype, nt_2 : numtype, cvtop : cvtop__}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, cvtop), mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt_2)]), [], mk_list_resulttype([$valtype_numtype(nt_1)])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, cvtop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype(nt_2)]), [], mk_list_resulttype([$valtype_numtype(nt_1)])))

  ;; test.spectec:2836.1-2837.35
  rule vconst{C : context, c : vec_}:
    `%|-%:%`(C, VCONST_instr(V128_vectype, c), mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VCONST_instr(V128_vectype, c))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2839.1-2840.41
  rule vvunop{C : context, v_vvunop : vvunop}:
    `%|-%:%`(C, VVUNOP_instr(V128_vectype, v_vvunop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVUNOP_instr(V128_vectype, v_vvunop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2842.1-2843.48
  rule vvbinop{C : context, v_vvbinop : vvbinop}:
    `%|-%:%`(C, VVBINOP_instr(V128_vectype, v_vvbinop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVBINOP_instr(V128_vectype, v_vvbinop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2845.1-2846.55
  rule vvternop{C : context, v_vvternop : vvternop}:
    `%|-%:%`(C, VVTERNOP_instr(V128_vectype, v_vvternop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVTERNOP_instr(V128_vectype, v_vvternop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2848.1-2849.44
  rule vvtestop{C : context, v_vvtestop : vvtestop}:
    `%|-%:%`(C, VVTESTOP_instr(V128_vectype, v_vvtestop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VVTESTOP_instr(V128_vectype, v_vvtestop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2851.1-2852.37
  rule vunop{C : context, sh : shape, vunop : vunop_}:
    `%|-%:%`(C, VUNOP_instr(sh, vunop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VUNOP_instr(sh, vunop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2854.1-2855.44
  rule vbinop{C : context, sh : shape, vbinop : vbinop_}:
    `%|-%:%`(C, VBINOP_instr(sh, vbinop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VBINOP_instr(sh, vbinop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2857.1-2858.51
  rule vternop{C : context, sh : shape, vternop : vternop_}:
    `%|-%:%`(C, VTERNOP_instr(sh, vternop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VTERNOP_instr(sh, vternop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2860.1-2861.40
  rule vtestop{C : context, sh : shape, vtestop : vtestop_}:
    `%|-%:%`(C, VTESTOP_instr(sh, vtestop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VTESTOP_instr(sh, vtestop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2863.1-2864.44
  rule vrelop{C : context, sh : shape, vrelop : vrelop_}:
    `%|-%:%`(C, VRELOP_instr(sh, vrelop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VRELOP_instr(sh, vrelop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2866.1-2867.47
  rule vshiftop{C : context, sh : ishape, vshiftop : vshiftop_}:
    `%|-%:%`(C, VSHIFTOP_instr(sh, vshiftop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype I32_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSHIFTOP_instr(sh, vshiftop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype I32_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2869.1-2870.33
  rule vbitmask{C : context, sh : ishape}:
    `%|-%:%`(C, VBITMASK_instr(sh), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([I32_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VBITMASK_instr(sh))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([I32_valtype])))

  ;; test.spectec:2872.1-2873.50
  rule vswizzlop{C : context, sh : bshape, vswizzlop : vswizzlop_}:
    `%|-%:%`(C, VSWIZZLOP_instr(sh, vswizzlop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSWIZZLOP_instr(sh, vswizzlop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2875.1-2877.29
  rule vshuffle{C : context, sh : bshape, i_lst : laneidx*}:
    `%|-%:%`(C, VSHUFFLE_instr(sh, i_lst), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- (if ($proj_uN_0(i).0 < (2 * $proj_dim_0($fun_dim($proj_bshape_0(sh).0)).0)))*{i <- i_lst}
    -- wf_context: `%`(C)
    -- wf_dim: `%`($fun_dim($proj_bshape_0(sh).0))
    -- wf_instr: `%`(VSHUFFLE_instr(sh, i_lst))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2879.1-2880.44
  rule vsplat{C : context, sh : shape}:
    `%|-%:%`(C, VSPLAT_instr(sh), mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype($unpackshape(sh))]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VSPLAT_instr(sh))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([$valtype_numtype($unpackshape(sh))]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2882.1-2884.21
  rule vextract_lane{C : context, sh : shape, sx_opt : sx?, i : laneidx}:
    `%|-%:%`(C, VEXTRACT_LANE_instr(sh, sx_opt, i), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([$valtype_numtype($unpackshape(sh))])))
    -- if ($proj_uN_0(i).0 < $proj_dim_0($fun_dim(sh)).0)
    -- wf_context: `%`(C)
    -- wf_dim: `%`($fun_dim(sh))
    -- wf_instr: `%`(VEXTRACT_LANE_instr(sh, sx_opt, i))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([$valtype_numtype($unpackshape(sh))])))

  ;; test.spectec:2886.1-2888.21
  rule vreplace_lane{C : context, sh : shape, i : laneidx}:
    `%|-%:%`(C, VREPLACE_LANE_instr(sh, i), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype $valtype_numtype($unpackshape(sh))]), [], mk_list_resulttype([V128_valtype])))
    -- if ($proj_uN_0(i).0 < $proj_dim_0($fun_dim(sh)).0)
    -- wf_context: `%`(C)
    -- wf_dim: `%`($fun_dim(sh))
    -- wf_instr: `%`(VREPLACE_LANE_instr(sh, i))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype $valtype_numtype($unpackshape(sh))]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2890.1-2891.50
  rule vextunop{C : context, sh_1 : ishape, sh_2 : ishape, vextunop : vextunop__}:
    `%|-%:%`(C, VEXTUNOP_instr(sh_1, sh_2, vextunop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VEXTUNOP_instr(sh_1, sh_2, vextunop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2893.1-2894.57
  rule vextbinop{C : context, sh_1 : ishape, sh_2 : ishape, vextbinop : vextbinop__}:
    `%|-%:%`(C, VEXTBINOP_instr(sh_1, sh_2, vextbinop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VEXTBINOP_instr(sh_1, sh_2, vextbinop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2896.1-2897.64
  rule vextternop{C : context, sh_1 : ishape, sh_2 : ishape, vextternop : vextternop__}:
    `%|-%:%`(C, VEXTTERNOP_instr(sh_1, sh_2, vextternop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VEXTTERNOP_instr(sh_1, sh_2, vextternop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2899.1-2900.48
  rule vnarrow{C : context, sh_1 : ishape, sh_2 : ishape, v_sx : sx}:
    `%|-%:%`(C, VNARROW_instr(sh_1, sh_2, v_sx), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VNARROW_instr(sh_1, sh_2, v_sx))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype V128_valtype]), [], mk_list_resulttype([V128_valtype])))

  ;; test.spectec:2902.1-2903.46
  rule vcvtop{C : context, sh_1 : shape, sh_2 : shape, vcvtop : vcvtop__}:
    `%|-%:%`(C, VCVTOP_instr(sh_1, sh_2, vcvtop), mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VCVTOP_instr(sh_1, sh_2, vcvtop))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([V128_valtype]), [], mk_list_resulttype([V128_valtype])))

;; test.spectec:2301.1-2301.96
relation Instrs_ok: `%|-%:%`(context, instr*, instrtype)
  ;; test.spectec:2908.1-2909.24
  rule empty{C : context}:
    `%|-%:%`(C, [], mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))
    -- wf_context: `%`(C)
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype([])))

  ;; test.spectec:2912.1-2916.82
  rule seq{C : context, instr_1 : instr, instr_2_lst : instr*, t_1_lst : valtype*, x_1_lst : idx*, x_2_lst : idx*, t_3_lst : valtype*, t_2_lst : valtype*, init_lst : init*, t_lst : valtype*, var_0 : context?}:
    `%|-%:%`(C, [instr_1] ++ instr_2_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_1_lst ++ x_2_lst, mk_list_resulttype(t_3_lst)))
    -- fun_with_locals: `%%%%`(C, x_1_lst, mk_localtype_localtype(SET_init, t)*{t <- t_lst}, var_0)
    -- Instr_ok: `%|-%:%`(C, instr_1, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_1_lst, mk_list_resulttype(t_2_lst)))
    -- if (|init_lst| = |t_lst|)
    -- if (|init_lst| = |x_1_lst|)
    -- (if ($proj_uN_0(x_1).0 < |C.LOCALS_context|))*{x_1 <- x_1_lst}
    -- (if (C.LOCALS_context[$proj_uN_0(x_1).0] = mk_localtype_localtype(v_init, t)))*{v_init <- init_lst, t <- t_lst, x_1 <- x_1_lst}
    -- if (var_0 =/= ?())
    -- Instrs_ok: `%|-%:%`(!(var_0), instr_2_lst, mk_instrtype_instrtype(mk_list_resulttype(t_2_lst), x_2_lst, mk_list_resulttype(t_3_lst)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(instr_1)
    -- (wf_instr: `%`(instr_2))*{instr_2 <- instr_2_lst}
    -- wf_context: `%`(!(var_0))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_1_lst ++ x_2_lst, mk_list_resulttype(t_3_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_1_lst, mk_list_resulttype(t_2_lst)))
    -- (wf_localtype: `%`(mk_localtype_localtype(v_init, t)))*{v_init <- init_lst, t <- t_lst}
    -- (wf_localtype: `%`(mk_localtype_localtype(SET_init, t)))*{t <- t_lst}
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_2_lst), x_2_lst, mk_list_resulttype(t_3_lst)))

  ;; test.spectec:2918.1-2922.33
  rule sub{C : context, instr_lst : instr*, it' : instrtype, it : instrtype}:
    `%|-%:%`(C, instr_lst, it')
    -- Instrs_ok: `%|-%:%`(C, instr_lst, it)
    -- Instrtype_sub: `%|-%<:%`(C, it, it')
    -- Instrtype_ok: `%|-%:OK`(C, it')
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- wf_instrtype: `%`(it')
    -- wf_instrtype: `%`(it)

  ;; test.spectec:2925.1-2928.33
  rule frame{C : context, instr_lst : instr*, t_lst : valtype*, t_1_lst : valtype*, x_lst : idx*, t_2_lst : valtype*}:
    `%|-%:%`(C, instr_lst, mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ t_1_lst), x_lst, mk_list_resulttype(t_lst ++ t_2_lst)))
    -- Instrs_ok: `%|-%:%`(C, instr_lst, mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))
    -- Resulttype_ok: `%|-%:OK`(C, mk_list_resulttype(t_lst))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_lst ++ t_1_lst), x_lst, mk_list_resulttype(t_lst ++ t_2_lst)))
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype(t_1_lst), x_lst, mk_list_resulttype(t_2_lst)))
}

;; test.spectec:2302.1-2302.94
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; test.spectec:2933.1-2935.40
  rule mk_Expr_ok{C : context, instr_lst : instr*, t_lst : valtype*}:
    `%|-%:%`(C, instr_lst, mk_list_resulttype(t_lst))
    -- Instrs_ok: `%|-%:%`(C, instr_lst, mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype(t_lst)))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- wf_instrtype: `%`(mk_instrtype_instrtype(mk_list_resulttype([]), [], mk_list_resulttype(t_lst)))

;; test.spectec:2307.1-2308.75
relation Nondefaultable: `|-%NONDEFAULTABLE`(valtype)
  ;; test.spectec:4452.1-4452.66
  rule mk_Nondefaultable{t : valtype}:
    `|-%NONDEFAULTABLE`(t)
    -- if ($default_(t) =/= ?())
    -- if (!($default_(t)) = ?())
    -- wf_valtype: `%`(t)
    -- (wf_val: `%`(iter))?{iter <- !($default_(t))}

;; test.spectec:2940.1-2940.104
relation Instr_const: `%|-%CONST`(context, instr)
  ;; test.spectec:2944.1-2945.29
  rule const{C : context, nt : numtype, c_nt : num_}:
    `%|-%CONST`(C, CONST_instr(nt, c_nt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(nt, c_nt))

  ;; test.spectec:2947.1-2948.30
  rule vconst{C : context, vt : vectype, c_vt : vec_}:
    `%|-%CONST`(C, VCONST_instr(vt, c_vt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(VCONST_instr(vt, c_vt))

  ;; test.spectec:2950.1-2951.27
  rule ref_null{C : context, ht : heaptype}:
    `%|-%CONST`(C, REF_NULL_instr(ht))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_NULL_instr(ht))

  ;; test.spectec:2953.1-2954.23
  rule ref_i31{C : context}:
    `%|-%CONST`(C, REF_I31_instr)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_I31_instr)

  ;; test.spectec:2956.1-2957.26
  rule ref_func{C : context, x : idx}:
    `%|-%CONST`(C, REF_FUNC_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(REF_FUNC_instr(x))

  ;; test.spectec:2959.1-2960.28
  rule struct_new{C : context, x : idx}:
    `%|-%CONST`(C, STRUCT_NEW_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STRUCT_NEW_instr(x))

  ;; test.spectec:2962.1-2963.36
  rule struct_new_default{C : context, x : idx}:
    `%|-%CONST`(C, STRUCT_NEW_DEFAULT_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(STRUCT_NEW_DEFAULT_instr(x))

  ;; test.spectec:2965.1-2966.27
  rule array_new{C : context, x : idx}:
    `%|-%CONST`(C, ARRAY_NEW_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_NEW_instr(x))

  ;; test.spectec:2968.1-2969.35
  rule array_new_default{C : context, x : idx}:
    `%|-%CONST`(C, ARRAY_NEW_DEFAULT_instr(x))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_NEW_DEFAULT_instr(x))

  ;; test.spectec:2971.1-2972.35
  rule array_new_fixed{C : context, x : idx, v_n : n}:
    `%|-%CONST`(C, ARRAY_NEW_FIXED_instr(x, mk_uN_u32(v_n)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ARRAY_NEW_FIXED_instr(x, mk_uN_u32(v_n)))

  ;; test.spectec:2974.1-2975.34
  rule any_convert_extern{C : context}:
    `%|-%CONST`(C, ANY_CONVERT_EXTERN_instr)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(ANY_CONVERT_EXTERN_instr)

  ;; test.spectec:2977.1-2978.34
  rule extern_convert_any{C : context}:
    `%|-%CONST`(C, EXTERN_CONVERT_ANY_instr)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(EXTERN_CONVERT_ANY_instr)

  ;; test.spectec:2980.1-2982.25
  rule global_get{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, GLOBAL_GET_instr(x))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(?(), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_GET_instr(x))
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(), t))

  ;; test.spectec:2984.1-2987.29
  rule binop{C : context, v_Inn : Inn, binop : binop_}:
    `%|-%CONST`(C, BINOP_instr($numtype_addrtype(v_Inn), binop))
    -- if (|[I32_Inn I64_Inn]| > 0)
    -- if (v_Inn <- [I32_Inn I64_Inn])
    -- if (|[mk_binop__0_binop_(v_Inn, ADD_binop_Inn) mk_binop__0_binop_(v_Inn, SUB_binop_Inn) mk_binop__0_binop_(v_Inn, MUL_binop_Inn)]| > 0)
    -- if (binop <- [mk_binop__0_binop_(v_Inn, ADD_binop_Inn) mk_binop__0_binop_(v_Inn, SUB_binop_Inn) mk_binop__0_binop_(v_Inn, MUL_binop_Inn)])
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr($numtype_addrtype(v_Inn), binop))
    -- wf_binop_: `%%`($numtype_addrtype(v_Inn), mk_binop__0_binop_(v_Inn, ADD_binop_Inn))
    -- wf_binop_: `%%`($numtype_addrtype(v_Inn), mk_binop__0_binop_(v_Inn, SUB_binop_Inn))
    -- wf_binop_: `%%`($numtype_addrtype(v_Inn), mk_binop__0_binop_(v_Inn, MUL_binop_Inn))

;; test.spectec:2941.1-2941.103
relation Expr_const: `%|-%CONST`(context, expr)
  ;; test.spectec:2990.1-2991.38
  rule mk_Expr_const{C : context, instr_lst : instr*}:
    `%|-%CONST`(C, instr_lst)
    -- (Instr_const: `%|-%CONST`(C, v_instr))*{v_instr <- instr_lst}
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

;; test.spectec:2942.1-2942.105
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; test.spectec:2994.1-2997.33
  rule mk_Expr_ok_const{C : context, v_expr : expr, t : valtype}:
    `%|-%:%CONST`(C, v_expr, t)
    -- Expr_ok: `%|-%:%`(C, v_expr, mk_list_resulttype([t]))
    -- Expr_const: `%|-%CONST`(C, v_expr)
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}
    -- wf_valtype: `%`(t)

;; test.spectec:3012.1-3012.97
relation Type_ok: `%|-%:%`(context, type, deftype*)
  ;; test.spectec:3025.1-3029.53
  rule mk_Type_ok{C : context, v_rectype : rectype, dt_lst : deftype*, x : idx, var_0 : deftype*}:
    `%|-%:%`(C, TYPE_type(v_rectype), dt_lst)
    -- fun_rolldt: `%%%`(x, v_rectype, var_0)
    -- if ($proj_uN_0(x).0 = |C.TYPES_context|)
    -- if (dt_lst = var_0)
    -- Rectype_ok: `%|-%:%`(C +++ {TYPES dt_lst, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, v_rectype, OK_oktypeidx(x))
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES dt_lst, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_oktypeidx: `%`(OK_oktypeidx(x))

;; test.spectec:3013.1-3013.96
relation Tag_ok: `%|-%:%`(context, tag, tagtype)
  ;; test.spectec:3031.1-3033.35
  rule mk_Tag_ok{C : context, v_tagtype : tagtype, var_0 : tagtype}:
    `%|-%:%`(C, TAG_tag(v_tagtype), var_0)
    -- fun_clos_tagtype: `%%%`(C, v_tagtype, var_0)
    -- Tagtype_ok: `%|-%:OK`(C, v_tagtype)
    -- wf_context: `%`(C)
    -- wf_typeuse: `%`(var_0)
    -- wf_tag: `%`(TAG_tag(v_tagtype))

;; test.spectec:3014.1-3014.99
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; test.spectec:3035.1-3039.40
  rule mk_Global_ok{C : context, v_globaltype : globaltype, v_expr : expr, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(v_globaltype, v_expr), v_globaltype)
    -- Globaltype_ok: `%|-%:OK`(C, v_globaltype)
    -- if (v_globaltype = mk_globaltype_globaltype(?(MUT_mut), t))
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, t)
    -- wf_context: `%`(C)
    -- wf_global: `%`(GLOBAL_global(v_globaltype, v_expr))
    -- wf_globaltype: `%`(mk_globaltype_globaltype(?(MUT_mut), t))

;; test.spectec:3015.1-3015.96
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; test.spectec:3041.1-3043.35
  rule mk_Mem_ok{C : context, v_memtype : memtype}:
    `%|-%:%`(C, MEMORY_mem(v_memtype), v_memtype)
    -- Memtype_ok: `%|-%:OK`(C, v_memtype)
    -- wf_context: `%`(C)
    -- wf_mem: `%`(MEMORY_mem(v_memtype))

;; test.spectec:3016.1-3016.98
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; test.spectec:3045.1-3049.41
  rule mk_Table_ok{C : context, v_tabletype : tabletype, v_expr : expr, at : addrtype, lim : limits, rt : reftype}:
    `%|-%:%`(C, TABLE_table(v_tabletype, v_expr), v_tabletype)
    -- Tabletype_ok: `%|-%:OK`(C, v_tabletype)
    -- if (v_tabletype = mk_tabletype_tabletype(at, lim, rt))
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, $valtype_reftype(rt))
    -- wf_context: `%`(C)
    -- wf_table: `%`(TABLE_table(v_tabletype, v_expr))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt))

;; test.spectec:3023.1-3023.98
relation Local_ok: `%|-%:%`(context, local, localtype)
  ;; test.spectec:3051.1-3053.35
  rule set{C : context, t : valtype}:
    `%|-%:%`(C, LOCAL_local(t), mk_localtype_localtype(SET_init, t))
    -- Defaultable: `|-%DEFAULTABLE`(t)
    -- wf_context: `%`(C)
    -- wf_local: `%`(LOCAL_local(t))
    -- wf_localtype: `%`(mk_localtype_localtype(SET_init, t))

  ;; test.spectec:3055.1-3057.41
  rule unset{C : context, t : valtype}:
    `%|-%:%`(C, LOCAL_local(t), mk_localtype_localtype(UNSET_init, t))
    -- Nondefaultable: `|-%NONDEFAULTABLE`(t)
    -- wf_context: `%`(C)
    -- wf_local: `%`(LOCAL_local(t))
    -- wf_localtype: `%`(mk_localtype_localtype(UNSET_init, t))

;; test.spectec:3017.1-3017.97
relation Func_ok: `%|-%:%`(context, func, deftype)
  ;; test.spectec:3059.1-3064.89
  rule mk_Func_ok{C : context, x : idx, local_lst : local*, v_expr : expr, t_1_lst : valtype*, t_2_lst : valtype*, lct_lst : localtype*}:
    `%|-%:%`(C, FUNC_func(x, local_lst, v_expr), C.TYPES_context[$proj_uN_0(x).0])
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- Expand: `%~~%`(C.TYPES_context[$proj_uN_0(x).0], `FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- if (|lct_lst| = |local_lst|)
    -- (Local_ok: `%|-%:%`(C, v_local, lct))*{lct <- lct_lst, v_local <- local_lst}
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS mk_localtype_localtype(SET_init, t_1)*{t_1 <- t_1_lst} ++ lct_lst, LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(mk_list_resulttype(t_2_lst)), REFS [], RECS []}, v_expr, mk_list_resulttype(t_2_lst))
    -- wf_context: `%`(C)
    -- wf_func: `%`(FUNC_func(x, local_lst, v_expr))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype(t_1_lst), mk_list_resulttype(t_2_lst)))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS mk_localtype_localtype(SET_init, t_1)*{t_1 <- t_1_lst} ++ lct_lst, LABELS [mk_list_resulttype(t_2_lst)], RETURN ?(mk_list_resulttype(t_2_lst)), REFS [], RECS []})

;; test.spectec:3020.1-3020.118
relation Datamode_ok: `%|-%:%`(context, datamode, datatype)
  ;; test.spectec:3076.1-3077.20
  rule passive{C : context}:
    `%|-%:%`(C, PASSIVE_datamode, OK_datatype)
    -- wf_context: `%`(C)
    -- wf_datamode: `%`(PASSIVE_datamode)

  ;; test.spectec:3079.1-3082.41
  rule active{C : context, x : idx, v_expr : expr, at : addrtype, lim : limits}:
    `%|-%:%`(C, ACTIVE_datamode(x, v_expr), OK_datatype)
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = `%%PAGE`_memtype(at, lim))
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, $valtype_addrtype(at))
    -- wf_context: `%`(C)
    -- wf_datamode: `%`(ACTIVE_datamode(x, v_expr))
    -- wf_memtype: `%`(`%%PAGE`_memtype(at, lim))

;; test.spectec:3018.1-3018.115
relation Data_ok: `%|-%:%`(context, data, datatype)
  ;; test.spectec:3066.1-3068.37
  rule mk_Data_ok{C : context, b_lst : byte*, v_datamode : datamode}:
    `%|-%:%`(C, DATA_data(b_lst, v_datamode), OK_datatype)
    -- Datamode_ok: `%|-%:%`(C, v_datamode, OK_datatype)
    -- wf_context: `%`(C)
    -- wf_data: `%`(DATA_data(b_lst, v_datamode))

;; test.spectec:3021.1-3021.101
relation Elemmode_ok: `%|-%:%`(context, elemmode, elemtype)
  ;; test.spectec:3084.1-3085.20
  rule passive{C : context, rt : reftype}:
    `%|-%:%`(C, PASSIVE_elemmode, rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_elemmode: `%`(PASSIVE_elemmode)

  ;; test.spectec:3087.1-3088.20
  rule declare{C : context, rt : reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_elemmode: `%`(DECLARE_elemmode)

  ;; test.spectec:3090.1-3094.41
  rule active{C : context, x : idx, v_expr : expr, rt : reftype, at : addrtype, lim : limits, rt' : reftype}:
    `%|-%:%`(C, ACTIVE_elemmode(x, v_expr), rt)
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = mk_tabletype_tabletype(at, lim, rt'))
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, $valtype_addrtype(at))
    -- wf_context: `%`(C)
    -- wf_reftype: `%`(rt)
    -- wf_elemmode: `%`(ACTIVE_elemmode(x, v_expr))
    -- wf_tabletype: `%`(mk_tabletype_tabletype(at, lim, rt'))

;; test.spectec:3019.1-3019.97
relation Elem_ok: `%|-%:%`(context, elem, elemtype)
  ;; test.spectec:3070.1-3074.43
  rule mk_Elem_ok{C : context, v_elemtype : elemtype, expr_lst : expr*, v_elemmode : elemmode}:
    `%|-%:%`(C, ELEM_elem(v_elemtype, expr_lst, v_elemmode), v_elemtype)
    -- Reftype_ok: `%|-%:OK`(C, v_elemtype)
    -- (Expr_ok_const: `%|-%:%CONST`(C, v_expr, $valtype_reftype(v_elemtype)))*{v_expr <- expr_lst}
    -- Elemmode_ok: `%|-%:%`(C, v_elemmode, v_elemtype)
    -- wf_context: `%`(C)
    -- wf_elem: `%`(ELEM_elem(v_elemtype, expr_lst, v_elemmode))

;; test.spectec:3022.1-3022.98
relation Start_ok: `%|-%:OK`(context, start)
  ;; test.spectec:3096.1-3098.43
  rule mk_Start_ok{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- Expand: `%~~%`(C.FUNCS_context[$proj_uN_0(x).0], `FUNC%->%`_comptype(mk_list_resulttype([]), mk_list_resulttype([])))
    -- wf_context: `%`(C)
    -- wf_start: `%`(START_start(x))
    -- wf_comptype: `%`(`FUNC%->%`_comptype(mk_list_resulttype([]), mk_list_resulttype([])))

;; test.spectec:3103.1-3103.105
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; test.spectec:3107.1-3109.33
  rule mk_Import_ok{C : context, name_1 : name, name_2 : name, xt : externtype, var_0 : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), var_0)
    -- fun_clos_externtype: `%%%`(C, xt, var_0)
    -- Externtype_ok: `%|-%:OK`(C, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(var_0)
    -- wf_import: `%`(IMPORT_import(name_1, name_2, xt))

;; test.spectec:3105.1-3105.108
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; test.spectec:3116.1-3118.23
  rule tag{C : context, x : idx, jt : tagtype}:
    `%|-%:%`(C, TAG_externidx(x), TAG_externtype(jt))
    -- if ($proj_uN_0(x).0 < |C.TAGS_context|)
    -- if (C.TAGS_context[$proj_uN_0(x).0] = jt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TAG_externidx(x))
    -- wf_externtype: `%`(TAG_externtype(jt))

  ;; test.spectec:3120.1-3122.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = gt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(GLOBAL_externidx(x))
    -- wf_externtype: `%`(GLOBAL_externtype(gt))

  ;; test.spectec:3124.1-3126.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = mt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(MEM_externidx(x))
    -- wf_externtype: `%`(MEM_externtype(mt))

  ;; test.spectec:3128.1-3130.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = tt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TABLE_externidx(x))
    -- wf_externtype: `%`(TABLE_externtype(tt))

  ;; test.spectec:3132.1-3134.24
  rule func{C : context, x : idx, dt : deftype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype($typeuse_deftype(dt)))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = dt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(FUNC_externidx(x))
    -- wf_externtype: `%`(FUNC_externtype($typeuse_deftype(dt)))

;; test.spectec:3104.1-3104.105
relation Export_ok: `%|-%:%%`(context, export, name, externtype)
  ;; test.spectec:3111.1-3113.39
  rule mk_Export_ok{C : context, v_name : name, v_externidx : externidx, xt : externtype}:
    `%|-%:%%`(C, EXPORT_export(v_name, v_externidx), v_name, xt)
    -- Externidx_ok: `%|-%:%`(C, v_externidx, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(xt)
    -- wf_export: `%`(EXPORT_export(v_name, v_externidx))

;; test.spectec:3141.1-3141.100
rec {

;; test.spectec:3141.1-3141.100
relation Globals_ok: `%|-%:%`(context, global*, globaltype*)
  ;; test.spectec:3186.1-3187.17
  rule empty{C : context}:
    `%|-%:%`(C, [], [])
    -- wf_context: `%`(C)

  ;; test.spectec:3189.1-3192.54
  rule cons{C : context, global_1 : global, global_lst : global*, gt_1 : globaltype, gt_lst : globaltype*}:
    `%|-%:%`(C, [global_1] ++ global_lst, [gt_1] ++ gt_lst)
    -- Global_ok: `%|-%:%`(C, global_1, gt_1)
    -- Globals_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [gt_1], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, global_lst, gt_lst)
    -- wf_context: `%`(C)
    -- wf_global: `%`(global_1)
    -- (wf_global: `%`(v_global))*{v_global <- global_lst}
    -- (wf_globaltype: `%`(gt))*{gt <- gt_lst}
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [gt_1], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:3140.1-3140.98
rec {

;; test.spectec:3140.1-3140.98
relation Types_ok: `%|-%:%`(context, type*, deftype*)
  ;; test.spectec:3178.1-3179.17
  rule empty{C : context}:
    `%|-%:%`(C, [], [])
    -- wf_context: `%`(C)

  ;; test.spectec:3181.1-3184.49
  rule cons{C : context, type_1 : type, type_lst : type*, dt_1_lst : deftype*, dt_lst : deftype*}:
    `%|-%:%`(C, [type_1] ++ type_lst, dt_1_lst ++ dt_lst)
    -- Type_ok: `%|-%:%`(C, type_1, dt_1_lst)
    -- Types_ok: `%|-%:%`(C +++ {TYPES dt_1_lst, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type_lst, dt_lst)
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES dt_1_lst, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:3144.1-3144.59
syntax nonfuncs = 
  | mk_nonfuncs(global_lst : global*, mem_lst : mem*, table_lst : table*, elem_lst : elem*, start_opt : start?, export_lst : export*)

;; test.spectec:3144.8-3144.16
relation wf_nonfuncs: `%`(nonfuncs)
  ;; test.spectec:3144.8-3144.16
  rule nonfuncs_case_0{global_lst : global*, mem_lst : mem*, table_lst : table*, elem_lst : elem*, start_opt : start?, export_lst : export*}:
    `%`(mk_nonfuncs_nonfuncs(global_lst, mem_lst, table_lst, elem_lst, start_opt, export_lst))
    -- (wf_global: `%`(v_global))*{v_global <- global_lst}
    -- (wf_mem: `%`(v_mem))*{v_mem <- mem_lst}
    -- (wf_table: `%`(v_table))*{v_table <- table_lst}
    -- (wf_elem: `%`(v_elem))*{v_elem <- elem_lst}
    -- (wf_start: `%`(v_start))?{v_start <- start_opt}
    -- (wf_export: `%`(v_export))*{v_export <- export_lst}

;; test.spectec:3145.6-3145.23
relation fun_funcidx_nonfuncs: `%%`(nonfuncs, funcidx*)
  ;; test.spectec:3145.6-3145.23
  rule fun_funcidx_nonfuncs_case_0{global_lst : global*, mem_lst : mem*, table_lst : table*, elem_lst : elem*, start_opt : start?, export_lst : export*, var_0 : funcidx*}:
    `%%`(mk_nonfuncs_nonfuncs(global_lst, mem_lst, table_lst, elem_lst, start_opt, export_lst), var_0)
    -- fun_funcidx_module: `%%`(MODULE_module(mk_list_list([]), mk_list_list([]), mk_list_list([]), mk_list_list(global_lst), mk_list_list(mem_lst), mk_list_list(table_lst), mk_list_list([]), mk_list_list([]), mk_list_list(elem_lst), start_opt, mk_list_list(export_lst)), var_0)

;; test.spectec:3145.6-3145.23
relation funcidx_nonfuncs_is_wf: `%%`(v_nonfuncs : nonfuncs, ret_val_lst : funcidx*)
  ;; test.spectec:3145.6-3145.23
  rule funcidx_nonfuncs_is_wf_0{v_nonfuncs : nonfuncs, ret_val_lst : funcidx*, var_0 : funcidx*}:
    `%%`(v_nonfuncs, ret_val_lst)
    -- fun_funcidx_nonfuncs: `%%`(v_nonfuncs, var_0)
    -- wf_nonfuncs: `%`(v_nonfuncs)
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(32, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3139.1-3139.99
relation Module_ok: `|-%:%`(module, moduletype)
  ;; test.spectec:3149.1-3175.32
  rule mk_Module_ok{type_lst : type*, import_lst : import*, tag_lst : tag*, global_lst : global*, mem_lst : mem*, table_lst : table*, func_lst : func*, data_lst : data*, elem_lst : elem*, start_opt : start?, export_lst : export*, C : context, xt_I_lst : externtype*, xt_E_lst : externtype*, dt'_lst : deftype*, C' : context, jt_lst : tagtype*, gt_lst : globaltype*, mt_lst : memtype*, tt_lst : tabletype*, dt_lst : deftype*, ok_lst : datatype*, rt_lst : reftype*, nm_lst : name*, jt_I_lst : tagtype*, mt_I_lst : memtype*, tt_I_lst : tabletype*, gt_I_lst : globaltype*, dt_I_lst : deftype*, x_lst : idx*, var_6 : deftype*, var_5 : tabletype*, var_4 : memtype*, var_3 : globaltype*, var_2 : tagtype*, var_1 : funcidx*, var_0 : moduletype}:
    `|-%:%`(MODULE_module(mk_list_list(type_lst), mk_list_list(import_lst), mk_list_list(tag_lst), mk_list_list(global_lst), mk_list_list(mem_lst), mk_list_list(table_lst), mk_list_list(func_lst), mk_list_list(data_lst), mk_list_list(elem_lst), start_opt, mk_list_list(export_lst)), var_0)
    -- fun_funcsxt: `%%`(xt_I_lst, var_6)
    -- fun_tablesxt: `%%`(xt_I_lst, var_5)
    -- fun_memsxt: `%%`(xt_I_lst, var_4)
    -- fun_globalsxt: `%%`(xt_I_lst, var_3)
    -- fun_tagsxt: `%%`(xt_I_lst, var_2)
    -- fun_funcidx_nonfuncs: `%%`(mk_nonfuncs_nonfuncs(global_lst, mem_lst, table_lst, elem_lst, start_opt, export_lst), var_1)
    -- fun_clos_moduletype: `%%%`(C, mk_moduletype_moduletype(xt_I_lst, xt_E_lst), var_0)
    -- Types_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type_lst, dt'_lst)
    -- if (|import_lst| = |xt_I_lst|)
    -- (Import_ok: `%|-%:%`({TYPES dt'_lst, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, v_import, xt_I))*{v_import <- import_lst, xt_I <- xt_I_lst}
    -- if (|jt_lst| = |tag_lst|)
    -- (Tag_ok: `%|-%:%`(C', v_tag, jt))*{jt <- jt_lst, v_tag <- tag_lst}
    -- Globals_ok: `%|-%:%`(C', global_lst, gt_lst)
    -- if (|mem_lst| = |mt_lst|)
    -- (Mem_ok: `%|-%:%`(C', v_mem, mt))*{v_mem <- mem_lst, mt <- mt_lst}
    -- if (|table_lst| = |tt_lst|)
    -- (Table_ok: `%|-%:%`(C', v_table, tt))*{v_table <- table_lst, tt <- tt_lst}
    -- if (|dt_lst| = |func_lst|)
    -- (Func_ok: `%|-%:%`(C, v_func, dt))*{dt <- dt_lst, v_func <- func_lst}
    -- if (|data_lst| = |ok_lst|)
    -- (Data_ok: `%|-%:%`(C, v_data, ok))*{v_data <- data_lst, ok <- ok_lst}
    -- if (|elem_lst| = |rt_lst|)
    -- (Elem_ok: `%|-%:%`(C, v_elem, rt))*{v_elem <- elem_lst, rt <- rt_lst}
    -- (Start_ok: `%|-%:OK`(C, v_start))?{v_start <- start_opt}
    -- if (|export_lst| = |nm_lst|)
    -- if (|export_lst| = |xt_E_lst|)
    -- (Export_ok: `%|-%:%%`(C, v_export, nm, xt_E))*{v_export <- export_lst, nm <- nm_lst, xt_E <- xt_E_lst}
    -- if $disjoint_(syntax name, nm_lst)
    -- if (C = C' +++ {TYPES [], TAGS jt_I_lst ++ jt_lst, GLOBALS gt_lst, MEMS mt_I_lst ++ mt_lst, TABLES tt_I_lst ++ tt_lst, FUNCS [], DATAS ok_lst, ELEMS rt_lst, LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- if (C' = {TYPES dt'_lst, TAGS [], GLOBALS gt_I_lst, MEMS [], TABLES [], FUNCS dt_I_lst ++ dt_lst, DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS x_lst, RECS []})
    -- if (x_lst = var_1)
    -- if (jt_I_lst = var_2)
    -- if (gt_I_lst = var_3)
    -- if (mt_I_lst = var_4)
    -- if (tt_I_lst = var_5)
    -- if (dt_I_lst = var_6)
    -- wf_context: `%`(C)
    -- wf_context: `%`(C')
    -- (wf_name: `%`(nm))*{nm <- nm_lst}
    -- wf_moduletype: `%`(var_0)
    -- (wf_uN: `%%`(32, iter))*{iter <- var_1}
    -- (wf_typeuse: `%`(iter))*{iter <- var_2}
    -- (wf_globaltype: `%`(iter))*{iter <- var_3}
    -- (wf_memtype: `%`(iter))*{iter <- var_4}
    -- (wf_tabletype: `%`(iter))*{iter <- var_5}
    -- wf_module: `%`(MODULE_module(mk_list_list(type_lst), mk_list_list(import_lst), mk_list_list(tag_lst), mk_list_list(global_lst), mk_list_list(mem_lst), mk_list_list(table_lst), mk_list_list(func_lst), mk_list_list(data_lst), mk_list_list(elem_lst), start_opt, mk_list_list(export_lst)))
    -- wf_moduletype: `%`(mk_moduletype_moduletype(xt_I_lst, xt_E_lst))
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_context: `%`({TYPES dt'_lst, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_context: `%`({TYPES [], TAGS jt_I_lst ++ jt_lst, GLOBALS gt_lst, MEMS mt_I_lst ++ mt_lst, TABLES tt_I_lst ++ tt_lst, FUNCS [], DATAS ok_lst, ELEMS rt_lst, LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- wf_context: `%`({TYPES dt'_lst, TAGS [], GLOBALS gt_I_lst, MEMS [], TABLES [], FUNCS dt_I_lst ++ dt_lst, DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS x_lst, RECS []})
    -- wf_nonfuncs: `%`(mk_nonfuncs_nonfuncs(global_lst, mem_lst, table_lst, elem_lst, start_opt, export_lst))

;; test.spectec:3205.1-3205.24
syntax relaxed2 = 
  | mk_relaxed2(i : nat)

;; test.spectec:3205.1-3205.24
def $proj_relaxed2_0(x : relaxed2) : (nat)
  ;; test.spectec:3205.1-3205.24
  def $proj_relaxed2_0{v_num_0 : nat}(mk_relaxed2_relaxed2(v_num_0)) = (v_num_0)

;; test.spectec:3205.8-3205.16
relation wf_relaxed2: `%`(relaxed2)
  ;; test.spectec:3205.8-3205.16
  rule relaxed2_case_0{i : nat}:
    `%`(mk_relaxed2_relaxed2(i))
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:3206.1-3206.32
syntax relaxed4 = 
  | mk_relaxed4(i : nat)

;; test.spectec:3206.1-3206.32
def $proj_relaxed4_0(x : relaxed4) : (nat)
  ;; test.spectec:3206.1-3206.32
  def $proj_relaxed4_0{v_num_0 : nat}(mk_relaxed4_relaxed4(v_num_0)) = (v_num_0)

;; test.spectec:3206.8-3206.16
relation wf_relaxed4: `%`(relaxed4)
  ;; test.spectec:3206.8-3206.16
  rule relaxed4_case_0{i : nat}:
    `%`(mk_relaxed4_relaxed4(i))
    -- if ((((i = 0) \/ (i = 1)) \/ (i = 2)) \/ (i = 3))

;; test.spectec:3208.1-3208.83
def $fun_relaxed2(v_relaxed2 : relaxed2, syntax r_X, X_0 : r_X, X_1 : r_X) : r_X
  ;; test.spectec:3211.1-3211.63
  def $fun_relaxed2{i : relaxed2, syntax r_X, X_1 : r_X, X_2 : r_X}(i, syntax r_X, X_1, X_2) = (if $ND then [X_1 X_2][$proj_relaxed2_0(i).0] else [X_1 X_2][0])

;; test.spectec:3209.1-3209.89
def $fun_relaxed4(v_relaxed4 : relaxed4, syntax r_X, X_0 : r_X, X_1 : r_X, X_2 : r_X, X_3 : r_X) : r_X
  ;; test.spectec:3214.1-3214.81
  def $fun_relaxed4{i : relaxed4, syntax r_X, X_1 : r_X, X_2 : r_X, X_3 : r_X, X_4 : r_X}(i, syntax r_X, X_1, X_2, X_3, X_4) = (if $ND then [X_1 X_2 X_3 X_4][$proj_relaxed4_0(i).0] else [X_1 X_2 X_3 X_4][0])

;; test.spectec:3218.1-3218.43
def $R_fmadd : relaxed2

;; test.spectec:3218.6-3218.13
relation R_fmadd_is_wf: `%`(ret_val : relaxed2)
  ;; test.spectec:3218.6-3218.13
  rule R_fmadd_is_wf_0{ret_val : relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_fmadd)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3219.1-3219.43
def $R_fmin : relaxed4

;; test.spectec:3219.6-3219.12
relation R_fmin_is_wf: `%`(ret_val : relaxed4)
  ;; test.spectec:3219.6-3219.12
  rule R_fmin_is_wf_0{ret_val : relaxed4}:
    `%`(ret_val)
    -- if (ret_val = $R_fmin)
    -- wf_relaxed4: `%`(ret_val)

;; test.spectec:3220.1-3220.43
def $R_fmax : relaxed4

;; test.spectec:3220.6-3220.12
relation R_fmax_is_wf: `%`(ret_val : relaxed4)
  ;; test.spectec:3220.6-3220.12
  rule R_fmax_is_wf_0{ret_val : relaxed4}:
    `%`(ret_val)
    -- if (ret_val = $R_fmax)
    -- wf_relaxed4: `%`(ret_val)

;; test.spectec:3221.1-3221.43
def $R_idot : relaxed2

;; test.spectec:3221.6-3221.12
relation R_idot_is_wf: `%`(ret_val : relaxed2)
  ;; test.spectec:3221.6-3221.12
  rule R_idot_is_wf_0{ret_val : relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_idot)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3222.1-3222.43
def $R_iq15mulr : relaxed2

;; test.spectec:3222.6-3222.16
relation R_iq15mulr_is_wf: `%`(ret_val : relaxed2)
  ;; test.spectec:3222.6-3222.16
  rule R_iq15mulr_is_wf_0{ret_val : relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_iq15mulr)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3223.1-3223.43
def $R_trunc_u : relaxed4

;; test.spectec:3223.6-3223.15
relation R_trunc_u_is_wf: `%`(ret_val : relaxed4)
  ;; test.spectec:3223.6-3223.15
  rule R_trunc_u_is_wf_0{ret_val : relaxed4}:
    `%`(ret_val)
    -- if (ret_val = $R_trunc_u)
    -- wf_relaxed4: `%`(ret_val)

;; test.spectec:3224.1-3224.43
def $R_trunc_s : relaxed2

;; test.spectec:3224.6-3224.15
relation R_trunc_s_is_wf: `%`(ret_val : relaxed2)
  ;; test.spectec:3224.6-3224.15
  rule R_trunc_s_is_wf_0{ret_val : relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_trunc_s)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3225.1-3225.43
def $R_swizzle : relaxed2

;; test.spectec:3225.6-3225.15
relation R_swizzle_is_wf: `%`(ret_val : relaxed2)
  ;; test.spectec:3225.6-3225.15
  rule R_swizzle_is_wf_0{ret_val : relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_swizzle)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3226.1-3226.43
def $R_laneselect : relaxed2

;; test.spectec:3226.6-3226.18
relation R_laneselect_is_wf: `%`(ret_val : relaxed2)
  ;; test.spectec:3226.6-3226.18
  rule R_laneselect_is_wf_0{ret_val : relaxed2}:
    `%`(ret_val)
    -- if (ret_val = $R_laneselect)
    -- wf_relaxed2: `%`(ret_val)

;; test.spectec:3241.1-3241.41
def $s33_to_u32(v_s33 : s33) : u32

;; test.spectec:3241.6-3241.17
relation s33_to_u32_is_wf: `%%`(v_s33 : s33, ret_val : u32)
  ;; test.spectec:3241.6-3241.17
  rule s33_to_u32_is_wf_0{v_s33 : s33, ret_val : u32}:
    `%%`(v_s33, ret_val)
    -- wf_sN: `%%`(33, v_s33)
    -- if (ret_val = $s33_to_u32(v_s33))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3246.1-3246.107
def $ibits_(v_N : N, v_iN : iN) : bit*

;; test.spectec:3246.6-3246.13
relation ibits__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val_lst : bit*)
  ;; test.spectec:3246.6-3246.13
  rule ibits__is_wf_0{v_N : N, v_iN : iN, ret_val_lst : bit*}:
    `%%%`(v_N, v_iN, ret_val_lst)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val_lst = $ibits_(v_N, v_iN))
    -- (wf_bit: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3247.1-3247.107
def $fbits_(v_N : N, v_fN : fN) : bit*

;; test.spectec:3247.6-3247.13
relation fbits__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : bit*)
  ;; test.spectec:3247.6-3247.13
  rule fbits__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : bit*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fbits_(v_N, v_fN))
    -- (wf_bit: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3248.1-3248.109
def $ibytes_(v_N : N, v_iN : iN) : byte*

;; test.spectec:3248.6-3248.14
relation ibytes__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val_lst : byte*)
  ;; test.spectec:3248.6-3248.14
  rule ibytes__is_wf_0{v_N : N, v_iN : iN, ret_val_lst : byte*}:
    `%%%`(v_N, v_iN, ret_val_lst)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val_lst = $ibytes_(v_N, v_iN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3249.1-3249.109
def $fbytes_(v_N : N, v_fN : fN) : byte*

;; test.spectec:3249.6-3249.14
relation fbytes__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : byte*)
  ;; test.spectec:3249.6-3249.14
  rule fbytes__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : byte*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fbytes_(v_N, v_fN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3250.1-3250.104
def $nbytes_(v_numtype : numtype, v_num_ : num_) : byte*

;; test.spectec:3250.6-3250.14
relation nbytes__is_wf: `%%%`(v_numtype : numtype, v_num_ : num_, ret_val_lst : byte*)
  ;; test.spectec:3250.6-3250.14
  rule nbytes__is_wf_0{v_numtype : numtype, v_num_ : num_, ret_val_lst : byte*}:
    `%%%`(v_numtype, v_num_, ret_val_lst)
    -- wf_num_: `%%`(v_numtype, v_num_)
    -- if (ret_val_lst = $nbytes_(v_numtype, v_num_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3251.1-3251.104
def $vbytes_(v_vectype : vectype, v_vec_ : vec_) : byte*

;; test.spectec:3251.6-3251.14
relation vbytes__is_wf: `%%%`(v_vectype : vectype, v_vec_ : vec_, ret_val_lst : byte*)
  ;; test.spectec:3251.6-3251.14
  rule vbytes__is_wf_0{v_vectype : vectype, v_vec_ : vec_, ret_val_lst : byte*}:
    `%%%`(v_vectype, v_vec_, ret_val_lst)
    -- wf_uN: `%%`($vsize(v_vectype), v_vec_)
    -- if (ret_val_lst = $vbytes_(v_vectype, v_vec_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3252.1-3252.104
def $zbytes_(v_storagetype : storagetype, v_lit_ : lit_) : byte*

;; test.spectec:3252.6-3252.14
relation zbytes__is_wf: `%%%`(v_storagetype : storagetype, v_lit_ : lit_, ret_val_lst : byte*)
  ;; test.spectec:3252.6-3252.14
  rule zbytes__is_wf_0{v_storagetype : storagetype, v_lit_ : lit_, ret_val_lst : byte*}:
    `%%%`(v_storagetype, v_lit_, ret_val_lst)
    -- wf_storagetype: `%`(v_storagetype)
    -- wf_lit_: `%%`(v_storagetype, v_lit_)
    -- if (ret_val_lst = $zbytes_(v_storagetype, v_lit_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3253.1-3253.104
def $cbytes_(v_Cnn : Cnn, v_lit_ : lit_) : byte*

;; test.spectec:3253.6-3253.14
relation cbytes__is_wf: `%%%`(v_Cnn : Cnn, v_lit_ : lit_, ret_val_lst : byte*)
  ;; test.spectec:3253.6-3253.14
  rule cbytes__is_wf_0{v_Cnn : Cnn, v_lit_ : lit_, ret_val_lst : byte*}:
    `%%%`(v_Cnn, v_lit_, ret_val_lst)
    -- wf_lit_: `%%`($storagetype_Cnn(v_Cnn), v_lit_)
    -- if (ret_val_lst = $cbytes_(v_Cnn, v_lit_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3255.1-3255.91
def $inv_ibits_(v_N : N, var_0_lst : bit*) : iN

;; test.spectec:3255.6-3255.17
relation inv_ibits__is_wf: `%%%`(v_N : N, var_0_lst : bit*, ret_val : iN)
  ;; test.spectec:3255.6-3255.17
  rule inv_ibits__is_wf_0{v_N : N, var_0_lst : bit*, ret_val : iN}:
    `%%%`(v_N, var_0_lst, ret_val)
    -- (wf_bit: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_ibits_(v_N, var_0_lst))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3256.1-3256.91
def $inv_fbits_(v_N : N, var_0_lst : bit*) : fN

;; test.spectec:3256.6-3256.17
relation inv_fbits__is_wf: `%%%`(v_N : N, var_0_lst : bit*, ret_val : fN)
  ;; test.spectec:3256.6-3256.17
  rule inv_fbits__is_wf_0{v_N : N, var_0_lst : bit*, ret_val : fN}:
    `%%%`(v_N, var_0_lst, ret_val)
    -- (wf_bit: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_fbits_(v_N, var_0_lst))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:3257.1-3257.92
def $inv_ibytes_(v_N : N, var_0_lst : byte*) : iN

;; test.spectec:3257.6-3257.18
relation inv_ibytes__is_wf: `%%%`(v_N : N, var_0_lst : byte*, ret_val : iN)
  ;; test.spectec:3257.6-3257.18
  rule inv_ibytes__is_wf_0{v_N : N, var_0_lst : byte*, ret_val : iN}:
    `%%%`(v_N, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_ibytes_(v_N, var_0_lst))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3258.1-3258.92
def $inv_fbytes_(v_N : N, var_0_lst : byte*) : fN

;; test.spectec:3258.6-3258.18
relation inv_fbytes__is_wf: `%%%`(v_N : N, var_0_lst : byte*, ret_val : fN)
  ;; test.spectec:3258.6-3258.18
  rule inv_fbytes__is_wf_0{v_N : N, var_0_lst : byte*, ret_val : fN}:
    `%%%`(v_N, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_fbytes_(v_N, var_0_lst))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:3259.1-3259.87
def $inv_nbytes_(v_numtype : numtype, var_0_lst : byte*) : num_

;; test.spectec:3259.6-3259.18
relation inv_nbytes__is_wf: `%%%`(v_numtype : numtype, var_0_lst : byte*, ret_val : num_)
  ;; test.spectec:3259.6-3259.18
  rule inv_nbytes__is_wf_0{v_numtype : numtype, var_0_lst : byte*, ret_val : num_}:
    `%%%`(v_numtype, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_nbytes_(v_numtype, var_0_lst))
    -- wf_num_: `%%`(v_numtype, ret_val)

;; test.spectec:3260.1-3260.87
def $inv_vbytes_(v_vectype : vectype, var_0_lst : byte*) : vec_

;; test.spectec:3260.6-3260.18
relation inv_vbytes__is_wf: `%%%`(v_vectype : vectype, var_0_lst : byte*, ret_val : vec_)
  ;; test.spectec:3260.6-3260.18
  rule inv_vbytes__is_wf_0{v_vectype : vectype, var_0_lst : byte*, ret_val : vec_}:
    `%%%`(v_vectype, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_vbytes_(v_vectype, var_0_lst))
    -- wf_uN: `%%`($vsize(v_vectype), ret_val)

;; test.spectec:3261.1-3261.92
def $inv_zbytes_(v_storagetype : storagetype, var_0_lst : byte*) : lit_

;; test.spectec:3261.6-3261.18
relation inv_zbytes__is_wf: `%%%`(v_storagetype : storagetype, var_0_lst : byte*, ret_val : lit_)
  ;; test.spectec:3261.6-3261.18
  rule inv_zbytes__is_wf_0{v_storagetype : storagetype, var_0_lst : byte*, ret_val : lit_}:
    `%%%`(v_storagetype, var_0_lst, ret_val)
    -- wf_storagetype: `%`(v_storagetype)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_zbytes_(v_storagetype, var_0_lst))
    -- wf_lit_: `%%`(v_storagetype, ret_val)

;; test.spectec:3262.1-3262.87
def $inv_cbytes_(v_Cnn : Cnn, var_0_lst : byte*) : lit_

;; test.spectec:3262.6-3262.18
relation inv_cbytes__is_wf: `%%%`(v_Cnn : Cnn, var_0_lst : byte*, ret_val : lit_)
  ;; test.spectec:3262.6-3262.18
  rule inv_cbytes__is_wf_0{v_Cnn : Cnn, var_0_lst : byte*, ret_val : lit_}:
    `%%%`(v_Cnn, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_cbytes_(v_Cnn, var_0_lst))
    -- wf_lit_: `%%`($storagetype_Cnn(v_Cnn), ret_val)

;; test.spectec:3286.6-3286.14
relation fun_signed_: `%%%`(N, nat, int)
  ;; test.spectec:3286.6-3286.14
  rule fun_signed__case_0{v_N : nat, i : nat}:
    `%%%`(v_N, i, (i : nat <:> int))
    -- if (i < (2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

  ;; test.spectec:3286.6-3286.14
  rule fun_signed__case_1{v_N : nat, i : nat}:
    `%%%`(v_N, i, ((i : nat <:> int) - ((2 ^ v_N) : nat <:> int)))
    -- if (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ v_N)))

;; test.spectec:3290.6-3290.18
relation fun_inv_signed_: `%%%`(N, int, nat)
  ;; test.spectec:3290.6-3290.18
  rule fun_inv_signed__case_0{v_N : nat, i : int}:
    `%%%`(v_N, i, (i : int <:> nat))
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))

  ;; test.spectec:3290.6-3290.18
  rule fun_inv_signed__case_1{v_N : nat, i : int}:
    `%%%`(v_N, i, ((i + ((2 ^ v_N) : nat <:> int)) : int <:> nat))
    -- if ((- ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; test.spectec:3295.1-3295.60
def $fun_sx(v_storagetype : storagetype) : sx??
  ;; test.spectec:3296.1-3296.25
  def $fun_sx(I32_storagetype) = ?(?())
  ;; test.spectec:3296.1-3296.25
  def $fun_sx(I64_storagetype) = ?(?())
  ;; test.spectec:3296.1-3296.25
  def $fun_sx(F32_storagetype) = ?(?())
  ;; test.spectec:3296.1-3296.25
  def $fun_sx(F64_storagetype) = ?(?())
  ;; test.spectec:3296.1-3296.25
  def $fun_sx(V128_storagetype) = ?(?())
  ;; test.spectec:3297.1-3297.22
  def $fun_sx(I8_storagetype) = ?(?(S_sx))
  ;; test.spectec:3297.1-3297.22
  def $fun_sx(I16_storagetype) = ?(?(S_sx))
  def $fun_sx{x0 : storagetype}(x0) = ?()
    -- otherwise

;; test.spectec:3302.1-3302.51
def $fun_zero(v_lanetype : lanetype) : lane_
  ;; test.spectec:3303.1-3303.19
  def $fun_zero(I32_lanetype) = mk_lane__2_lane_(I32_Jnn, mk_uN_uN(0))
  ;; test.spectec:3303.1-3303.19
  def $fun_zero(I64_lanetype) = mk_lane__2_lane_(I64_Jnn, mk_uN_uN(0))
  ;; test.spectec:3303.1-3303.19
  def $fun_zero(I8_lanetype) = mk_lane__2_lane_(I8_Jnn, mk_uN_uN(0))
  ;; test.spectec:3303.1-3303.19
  def $fun_zero(I16_lanetype) = mk_lane__2_lane_(I16_Jnn, mk_uN_uN(0))
  ;; test.spectec:3304.1-3304.36
  def $fun_zero(F32_lanetype) = mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, $fzero($size($numtype_Fnn(F32_Fnn)))))
  ;; test.spectec:3304.1-3304.36
  def $fun_zero(F64_lanetype) = mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, $fzero($size($numtype_Fnn(F64_Fnn)))))

;; test.spectec:3302.6-3302.11
relation zero_is_wf: `%%`(v_lanetype : lanetype, ret_val : lane_)
  ;; test.spectec:3302.6-3302.11
  rule zero_is_wf_0{v_lanetype : lanetype, ret_val : lane_}:
    `%%`(v_lanetype, ret_val)
    -- if (ret_val = $fun_zero(v_lanetype))
    -- wf_lane_: `%%`(v_lanetype, ret_val)

;; test.spectec:3306.1-3306.22
def $bool(v_bool : bool) : nat
  ;; test.spectec:3307.1-3307.21
  def $bool(false) = 0
  ;; test.spectec:3308.1-3308.20
  def $bool(true) = 1

;; test.spectec:3310.1-3310.23
def $truncz(rat : rat) : int

;; test.spectec:3314.1-3314.59
def $ceilz(rat : rat) : int

;; test.spectec:3321.1-3321.61
def $sat_u_(v_N : N, int : int) : nat
  ;; test.spectec:3322.1-3322.48
  def $sat_u_{v_N : nat, i : int}(v_N, i) = (if (i < (0 : nat <:> int)) then 0 else (if (i > (((2 ^ v_N) : nat <:> int) - (1 : nat <:> int))) then ((((2 ^ v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat) else (i : int <:> nat)))

;; test.spectec:3326.1-3326.61
def $sat_s_(v_N : N, int : int) : int
  ;; test.spectec:3327.1-3327.58
  def $sat_s_{v_N : nat, i : int}(v_N, i) = (if (i < - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) then - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) else (if (i > (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int))) then (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)) else i))

;; test.spectec:3334.1-3334.29
def $ineg_(v_N : N, v_iN : iN) : iN
  ;; test.spectec:3381.1-3381.42
  def $ineg_{v_N : nat, i_1 : uN}(v_N, i_1) = mk_uN_iN((((((2 ^ v_N) : nat <:> int) - ($proj_uN_0(i_1).0 : nat <:> int)) \ ((2 ^ v_N) : nat <:> int)) : int <:> nat))

;; test.spectec:3334.6-3334.12
relation ineg__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3334.6-3334.12
  rule ineg__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ineg_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3335.1-3335.29
def $iabs_(v_N : N, v_iN : iN) : iN
  ;; test.spectec:3383.1-3383.65
  def $iabs_{v_N : nat, i_1 : uN, var_0 : int}(v_N, i_1) = (if (var_0 >= (0 : nat <:> int)) then i_1 else $ineg_(v_N, i_1))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3335.6-3335.12
relation iabs__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3335.6-3335.12
  rule iabs__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $iabs_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3336.1-3336.29
def $iclz_(v_N : N, v_iN : iN) : iN

;; test.spectec:3336.6-3336.12
relation iclz__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3336.6-3336.12
  rule iclz__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $iclz_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3337.1-3337.29
def $ictz_(v_N : N, v_iN : iN) : iN

;; test.spectec:3337.6-3337.12
relation ictz__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3337.6-3337.12
  rule ictz__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ictz_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3338.1-3338.32
def $ipopcnt_(v_N : N, v_iN : iN) : iN

;; test.spectec:3338.6-3338.15
relation ipopcnt__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3338.6-3338.15
  rule ipopcnt__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ipopcnt_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3339.6-3339.15
relation fun_iextend_: `%%%%%`(N, M, sx, iN, iN)
  ;; test.spectec:3339.6-3339.15
  rule fun_iextend__case_0{v_N : nat, v_M : nat, i : uN}:
    `%%%%%`(v_N, v_M, U_sx, i, mk_uN_iN(($proj_uN_0(i).0 \ (2 ^ v_M))))

  ;; test.spectec:3339.6-3339.15
  rule fun_iextend__case_1{v_N : nat, v_M : nat, i : uN, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, v_M, S_sx, i, mk_uN_iN(var_0))
    -- fun_signed_: `%%%`(v_M, ($proj_uN_0(i).0 \ (2 ^ v_M)), var_1)
    -- fun_inv_signed_: `%%%`(v_N, var_1, var_0)

;; test.spectec:3339.6-3339.15
relation iextend__is_wf: `%%%%%`(v_N : N, v_M : M, v_sx : sx, v_iN : iN, ret_val : iN)
  ;; test.spectec:3339.6-3339.15
  rule iextend__is_wf_0{v_N : N, v_M : M, v_sx : sx, v_iN : iN, ret_val : iN, var_0 : iN}:
    `%%%%%`(v_N, v_M, v_sx, v_iN, ret_val)
    -- fun_iextend_: `%%%%%`(v_N, v_M, v_sx, v_iN, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3341.1-3341.36
def $iadd_(v_N : N, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3399.1-3399.47
  def $iadd_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_iN((($proj_uN_0(i_1).0 + $proj_uN_0(i_2).0) \ (2 ^ v_N)))

;; test.spectec:3341.6-3341.12
relation iadd__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3341.6-3341.12
  rule iadd__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iadd_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3342.1-3342.36
def $isub_(v_N : N, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3401.1-3401.53
  def $isub_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_iN(((((((2 ^ v_N) + $proj_uN_0(i_1).0) : nat <:> int) - ($proj_uN_0(i_2).0 : nat <:> int)) \ ((2 ^ v_N) : nat <:> int)) : int <:> nat))

;; test.spectec:3342.6-3342.12
relation isub__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3342.6-3342.12
  rule isub__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $isub_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3343.1-3343.36
def $imul_(v_N : N, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3403.1-3403.47
  def $imul_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_iN((($proj_uN_0(i_1).0 * $proj_uN_0(i_2).0) \ (2 ^ v_N)))

;; test.spectec:3343.6-3343.12
relation imul__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3343.6-3343.12
  rule imul__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $imul_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3344.6-3344.12
relation fun_idiv_: `%%%%%`(N, sx, iN, iN, iN?)
  ;; test.spectec:3344.6-3344.12
  rule fun_idiv__case_0{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, U_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:3344.6-3344.12
  rule fun_idiv__case_1{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, ?(mk_uN_iN(($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat))))

  ;; test.spectec:3344.6-3344.12
  rule fun_idiv__case_2{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, S_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:3344.6-3344.12
  rule fun_idiv__case_3{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?())
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- if (((var_0 : int <:> rat) / (var_1 : int <:> rat)) = ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))

  ;; test.spectec:3344.6-3344.12
  rule fun_idiv__case_4{v_N : nat, i_1 : uN, i_2 : uN, var_2 : int, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?(mk_uN_iN(var_0)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, $truncz(((var_1 : int <:> rat) / (var_2 : int <:> rat))), var_0)

;; test.spectec:3344.6-3344.12
relation idiv__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?)
  ;; test.spectec:3344.6-3344.12
  rule idiv__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?, var_0 : iN?}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val_opt)
    -- fun_idiv_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val_opt = var_0)
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:3345.6-3345.12
relation fun_irem_: `%%%%%`(N, sx, iN, iN, iN?)
  ;; test.spectec:3345.6-3345.12
  rule fun_irem__case_0{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, U_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:3345.6-3345.12
  rule fun_irem__case_1{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, ?(mk_uN_iN(((($proj_uN_0(i_1).0 : nat <:> int) - (($proj_uN_0(i_2).0 * ($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat))))

  ;; test.spectec:3345.6-3345.12
  rule fun_irem__case_2{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, S_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:3345.6-3345.12
  rule fun_irem__case_3{v_N : nat, i_1 : uN, i_2 : uN, j_1 : int, j_2 : int, var_2 : int, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?(mk_uN_iN(var_0)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))), var_0)
    -- if ((j_1 = var_1) /\ (j_2 = var_2))

;; test.spectec:3345.6-3345.12
relation irem__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?)
  ;; test.spectec:3345.6-3345.12
  rule irem__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?, var_0 : iN?}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val_opt)
    -- fun_irem_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val_opt = var_0)
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:3346.1-3346.83
def $imin_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3417.1-3417.51
  def $imin_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = i_1
    -- if ($proj_uN_0(i_1).0 <= $proj_uN_0(i_2).0)
  ;; test.spectec:3418.1-3418.50
  def $imin_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = i_2
    -- if ($proj_uN_0(i_1).0 > $proj_uN_0(i_2).0)
  ;; test.spectec:3419.1-3419.77
  def $imin_{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}(v_N, S_sx, i_1, i_2) = (if (var_0 <= var_1) then i_1 else i_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3346.6-3346.12
relation imin__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3346.6-3346.12
  rule imin__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $imin_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3347.1-3347.83
def $imax_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3422.1-3422.51
  def $imax_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = i_1
    -- if ($proj_uN_0(i_1).0 >= $proj_uN_0(i_2).0)
  ;; test.spectec:3423.1-3423.50
  def $imax_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = i_2
    -- if ($proj_uN_0(i_1).0 < $proj_uN_0(i_2).0)
  ;; test.spectec:3424.1-3424.77
  def $imax_{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}(v_N, S_sx, i_1, i_2) = (if (var_0 >= var_1) then i_1 else i_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3347.6-3347.12
relation imax__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3347.6-3347.12
  rule imax__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $imax_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3348.1-3348.88
def $iadd_sat_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3427.1-3427.58
  def $iadd_sat_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = mk_uN_iN($sat_u_(v_N, (($proj_uN_0(i_1).0 + $proj_uN_0(i_2).0) : nat <:> int)))
  ;; test.spectec:3428.1-3428.101
  def $iadd_sat_{v_N : nat, i_1 : uN, i_2 : uN, var_2 : int, var_1 : int, var_0 : nat}(v_N, S_sx, i_1, i_2) = mk_uN_iN(var_0)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, $sat_s_(v_N, (var_1 + var_2)), var_0)

;; test.spectec:3348.6-3348.16
relation iadd_sat__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3348.6-3348.16
  rule iadd_sat__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iadd_sat_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3349.1-3349.88
def $isub_sat_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:3430.1-3430.58
  def $isub_sat_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = mk_uN_iN($sat_u_(v_N, (($proj_uN_0(i_1).0 : nat <:> int) - ($proj_uN_0(i_2).0 : nat <:> int))))
  ;; test.spectec:3431.1-3431.101
  def $isub_sat_{v_N : nat, i_1 : uN, i_2 : uN, var_2 : int, var_1 : int, var_0 : nat}(v_N, S_sx, i_1, i_2) = mk_uN_iN(var_0)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, $sat_s_(v_N, (var_1 - var_2)), var_0)

;; test.spectec:3349.6-3349.16
relation isub_sat__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3349.6-3349.16
  rule isub_sat__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $isub_sat_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3350.1-3350.92
def $iq15mulr_sat_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3350.6-3350.20
relation iq15mulr_sat__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3350.6-3350.20
  rule iq15mulr_sat__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iq15mulr_sat_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3351.1-3351.101
def $irelaxed_q15mulr_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN*

;; test.spectec:3351.6-3351.24
relation irelaxed_q15mulr__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_lst : iN*)
  ;; test.spectec:3351.6-3351.24
  rule irelaxed_q15mulr__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_lst : iN*}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val_lst)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val_lst = $irelaxed_q15mulr_(v_N, v_sx, v_iN, iN_0))
    -- (wf_uN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3352.1-3352.84
def $iavgr_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3352.6-3352.13
relation iavgr__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3352.6-3352.13
  rule iavgr__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iavgr_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3354.1-3354.29
def $inot_(v_N : N, v_iN : iN) : iN

;; test.spectec:3354.6-3354.12
relation inot__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3354.6-3354.12
  rule inot__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $inot_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3355.1-3355.29
def $irev_(v_N : N, v_iN : iN) : iN

;; test.spectec:3355.6-3355.12
relation irev__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3355.6-3355.12
  rule irev__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $irev_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3356.1-3356.36
def $iand_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3356.6-3356.12
relation iand__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3356.6-3356.12
  rule iand__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iand_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3357.1-3357.39
def $iandnot_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3357.6-3357.15
relation iandnot__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3357.6-3357.15
  rule iandnot__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iandnot_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3358.1-3358.35
def $ior_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3358.6-3358.11
relation ior__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3358.6-3358.11
  rule ior__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ior_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3359.1-3359.36
def $ixor_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3359.6-3359.12
relation ixor__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3359.6-3359.12
  rule ixor__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ixor_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3360.1-3360.34
def $ishl_(v_N : N, v_iN : iN, v_u32 : u32) : iN

;; test.spectec:3360.6-3360.12
relation ishl__is_wf: `%%%%`(v_N : N, v_iN : iN, v_u32 : u32, ret_val : iN)
  ;; test.spectec:3360.6-3360.12
  rule ishl__is_wf_0{v_N : N, v_iN : iN, v_u32 : u32, ret_val : iN}:
    `%%%%`(v_N, v_iN, v_u32, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(32, v_u32)
    -- if (ret_val = $ishl_(v_N, v_iN, v_u32))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3361.1-3361.76
def $ishr_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN

;; test.spectec:3361.6-3361.12
relation ishr__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32, ret_val : iN)
  ;; test.spectec:3361.6-3361.12
  rule ishr__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, v_u32, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(32, v_u32)
    -- if (ret_val = $ishr_(v_N, v_sx, v_iN, v_u32))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3362.1-3362.37
def $irotl_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3362.6-3362.13
relation irotl__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3362.6-3362.13
  rule irotl__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $irotl_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3363.1-3363.37
def $irotr_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:3363.6-3363.13
relation irotr__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:3363.6-3363.13
  rule irotr__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $irotr_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3365.1-3365.49
def $ibitselect_(v_N : N, v_iN : iN, iN_0 : iN, iN_1 : iN) : iN

;; test.spectec:3365.6-3365.18
relation ibitselect__is_wf: `%%%%%`(v_N : N, v_iN : iN, iN_0 : iN, iN_1 : iN, ret_val : iN)
  ;; test.spectec:3365.6-3365.18
  rule ibitselect__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, iN_1 : iN, ret_val : iN}:
    `%%%%%`(v_N, v_iN, iN_0, iN_1, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- wf_uN: `%%`(v_N, iN_1)
    -- if (ret_val = $ibitselect_(v_N, v_iN, iN_0, iN_1))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3366.1-3366.59
def $irelaxed_laneselect_(v_N : N, v_iN : iN, iN_0 : iN, iN_1 : iN) : iN*

;; test.spectec:3366.6-3366.27
relation irelaxed_laneselect__is_wf: `%%%%%`(v_N : N, v_iN : iN, iN_0 : iN, iN_1 : iN, ret_val_lst : iN*)
  ;; test.spectec:3366.6-3366.27
  rule irelaxed_laneselect__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, iN_1 : iN, ret_val_lst : iN*}:
    `%%%%%`(v_N, v_iN, iN_0, iN_1, ret_val_lst)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- wf_uN: `%%`(v_N, iN_1)
    -- if (ret_val_lst = $irelaxed_laneselect_(v_N, v_iN, iN_0, iN_1))
    -- (wf_uN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3368.1-3368.27
def $ieqz_(v_N : N, v_iN : iN) : u32
  ;; test.spectec:3452.1-3452.36
  def $ieqz_{v_N : nat, i_1 : uN}(v_N, i_1) = mk_uN_u32($bool(($proj_uN_0(i_1).0 = 0)))

;; test.spectec:3368.6-3368.12
relation ieqz__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : u32)
  ;; test.spectec:3368.6-3368.12
  rule ieqz__is_wf_0{v_N : N, v_iN : iN, ret_val : u32}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ieqz_(v_N, v_iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3369.1-3369.27
def $inez_(v_N : N, v_iN : iN) : u32
  ;; test.spectec:3454.1-3454.38
  def $inez_{v_N : nat, i_1 : uN}(v_N, i_1) = mk_uN_u32($bool(($proj_uN_0(i_1).0 =/= 0)))

;; test.spectec:3369.6-3369.12
relation inez__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : u32)
  ;; test.spectec:3369.6-3369.12
  rule inez__is_wf_0{v_N : N, v_iN : iN, ret_val : u32}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $inez_(v_N, v_iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3371.1-3371.33
def $ieq_(v_N : N, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:3457.1-3457.42
  def $ieq_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_u32($bool((i_1 = i_2)))

;; test.spectec:3371.6-3371.11
relation ieq__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:3371.6-3371.11
  rule ieq__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ieq_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3372.1-3372.33
def $ine_(v_N : N, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:3459.1-3459.44
  def $ine_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_u32($bool((i_1 =/= i_2)))

;; test.spectec:3372.6-3372.11
relation ine__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:3372.6-3372.11
  rule ine__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ine_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3373.1-3373.75
def $ilt_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:3461.1-3461.45
  def $ilt_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = mk_uN_u32($bool(($proj_uN_0(i_1).0 < $proj_uN_0(i_2).0)))
  ;; test.spectec:3462.1-3462.71
  def $ilt_{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}(v_N, S_sx, i_1, i_2) = mk_uN_u32($bool((var_0 < var_1)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3373.6-3373.11
relation ilt__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:3373.6-3373.11
  rule ilt__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ilt_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3374.1-3374.75
def $igt_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:3464.1-3464.45
  def $igt_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = mk_uN_u32($bool(($proj_uN_0(i_1).0 > $proj_uN_0(i_2).0)))
  ;; test.spectec:3465.1-3465.71
  def $igt_{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}(v_N, S_sx, i_1, i_2) = mk_uN_u32($bool((var_0 > var_1)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3374.6-3374.11
relation igt__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:3374.6-3374.11
  rule igt__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $igt_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3375.1-3375.75
def $ile_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:3467.1-3467.46
  def $ile_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = mk_uN_u32($bool(($proj_uN_0(i_1).0 <= $proj_uN_0(i_2).0)))
  ;; test.spectec:3468.1-3468.72
  def $ile_{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}(v_N, S_sx, i_1, i_2) = mk_uN_u32($bool((var_0 <= var_1)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3375.6-3375.11
relation ile__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:3375.6-3375.11
  rule ile__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ile_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3376.1-3376.75
def $ige_(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:3470.1-3470.46
  def $ige_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, U_sx, i_1, i_2) = mk_uN_u32($bool(($proj_uN_0(i_1).0 >= $proj_uN_0(i_2).0)))
  ;; test.spectec:3471.1-3471.72
  def $ige_{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}(v_N, S_sx, i_1, i_2) = mk_uN_u32($bool((var_0 >= var_1)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:3376.6-3376.11
relation ige__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:3376.6-3376.11
  rule ige__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ige_(v_N, v_sx, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3476.1-3476.30
def $fabs_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3476.6-3476.12
relation fabs__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3476.6-3476.12
  rule fabs__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fabs_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3477.1-3477.30
def $fneg_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3477.6-3477.12
relation fneg__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3477.6-3477.12
  rule fneg__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fneg_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3478.1-3478.31
def $fsqrt_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3478.6-3478.13
relation fsqrt__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3478.6-3478.13
  rule fsqrt__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fsqrt_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3479.1-3479.31
def $fceil_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3479.6-3479.13
relation fceil__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3479.6-3479.13
  rule fceil__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fceil_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3480.1-3480.32
def $ffloor_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3480.6-3480.14
relation ffloor__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3480.6-3480.14
  rule ffloor__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $ffloor_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3481.1-3481.32
def $ftrunc_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3481.6-3481.14
relation ftrunc__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3481.6-3481.14
  rule ftrunc__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $ftrunc_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3482.1-3482.34
def $fnearest_(v_N : N, v_fN : fN) : fN*

;; test.spectec:3482.6-3482.16
relation fnearest__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3482.6-3482.16
  rule fnearest__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fnearest_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3484.1-3484.37
def $fadd_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3484.6-3484.12
relation fadd__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3484.6-3484.12
  rule fadd__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fadd_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3485.1-3485.37
def $fsub_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3485.6-3485.12
relation fsub__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3485.6-3485.12
  rule fsub__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fsub_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3486.1-3486.37
def $fmul_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3486.6-3486.12
relation fmul__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3486.6-3486.12
  rule fmul__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fmul_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3487.1-3487.37
def $fdiv_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3487.6-3487.12
relation fdiv__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3487.6-3487.12
  rule fdiv__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fdiv_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3488.1-3488.37
def $fmin_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3488.6-3488.12
relation fmin__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3488.6-3488.12
  rule fmin__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fmin_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3489.1-3489.37
def $fmax_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3489.6-3489.12
relation fmax__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3489.6-3489.12
  rule fmax__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fmax_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3490.1-3490.38
def $fpmin_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3490.6-3490.13
relation fpmin__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3490.6-3490.13
  rule fpmin__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fpmin_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3491.1-3491.38
def $fpmax_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3491.6-3491.13
relation fpmax__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3491.6-3491.13
  rule fpmax__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fpmax_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3492.1-3492.82
def $frelaxed_min_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3492.6-3492.20
relation frelaxed_min__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3492.6-3492.20
  rule frelaxed_min__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $frelaxed_min_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3493.1-3493.82
def $frelaxed_max_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3493.6-3493.20
relation frelaxed_max__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3493.6-3493.20
  rule frelaxed_max__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $frelaxed_max_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3494.1-3494.42
def $fcopysign_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:3494.6-3494.17
relation fcopysign__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:3494.6-3494.17
  rule fcopysign__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fcopysign_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3496.1-3496.33
def $feq_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:3496.6-3496.11
relation feq__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:3496.6-3496.11
  rule feq__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $feq_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3497.1-3497.33
def $fne_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:3497.6-3497.11
relation fne__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:3497.6-3497.11
  rule fne__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fne_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3498.1-3498.33
def $flt_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:3498.6-3498.11
relation flt__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:3498.6-3498.11
  rule flt__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $flt_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3499.1-3499.33
def $fgt_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:3499.6-3499.11
relation fgt__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:3499.6-3499.11
  rule fgt__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fgt_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3500.1-3500.33
def $fle_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:3500.6-3500.11
relation fle__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:3500.6-3500.11
  rule fle__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fle_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3501.1-3501.33
def $fge_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:3501.6-3501.11
relation fge__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:3501.6-3501.11
  rule fge__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fge_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3503.1-3503.91
def $frelaxed_madd_(v_N : N, v_fN : fN, fN_0 : fN, fN_1 : fN) : fN*

;; test.spectec:3503.6-3503.21
relation frelaxed_madd__is_wf: `%%%%%`(v_N : N, v_fN : fN, fN_0 : fN, fN_1 : fN, ret_val_lst : fN*)
  ;; test.spectec:3503.6-3503.21
  rule frelaxed_madd__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, fN_1 : fN, ret_val_lst : fN*}:
    `%%%%%`(v_N, v_fN, fN_0, fN_1, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- wf_fN: `%%`(v_N, fN_1)
    -- if (ret_val_lst = $frelaxed_madd_(v_N, v_fN, fN_0, fN_1))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3504.1-3504.92
def $frelaxed_nmadd_(v_N : N, v_fN : fN, fN_0 : fN, fN_1 : fN) : fN*

;; test.spectec:3504.6-3504.22
relation frelaxed_nmadd__is_wf: `%%%%%`(v_N : N, v_fN : fN, fN_0 : fN, fN_1 : fN, ret_val_lst : fN*)
  ;; test.spectec:3504.6-3504.22
  rule frelaxed_nmadd__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, fN_1 : fN, ret_val_lst : fN*}:
    `%%%%%`(v_N, v_fN, fN_0, fN_1, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- wf_fN: `%%`(v_N, fN_1)
    -- if (ret_val_lst = $frelaxed_nmadd_(v_N, v_fN, fN_0, fN_1))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3542.1-3542.33
def $wrap__(v_M : M, v_N : N, v_iN : iN) : iN

;; test.spectec:3542.6-3542.13
relation wrap___is_wf: `%%%%`(v_M : M, v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:3542.6-3542.13
  rule wrap___is_wf_0{v_M : M, v_N : N, v_iN : iN, ret_val : iN}:
    `%%%%`(v_M, v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $wrap__(v_M, v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3543.1-3543.90
def $extend__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : iN

;; test.spectec:3543.6-3543.15
relation extend___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : iN)
  ;; test.spectec:3543.6-3543.15
  rule extend___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : iN}:
    `%%%%%`(v_M, v_N, v_sx, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $extend__(v_M, v_N, v_sx, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3544.1-3544.89
def $trunc__(v_M : M, v_N : N, v_sx : sx, v_fN : fN) : iN?

;; test.spectec:3544.6-3544.14
relation trunc___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?)
  ;; test.spectec:3544.6-3544.14
  rule trunc___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?}:
    `%%%%%`(v_M, v_N, v_sx, v_fN, ret_val_opt)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_opt = $trunc__(v_M, v_N, v_sx, v_fN))
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:3545.1-3545.94
def $trunc_sat__(v_M : M, v_N : N, v_sx : sx, v_fN : fN) : iN?

;; test.spectec:3545.6-3545.18
relation trunc_sat___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?)
  ;; test.spectec:3545.6-3545.18
  rule trunc_sat___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?}:
    `%%%%%`(v_M, v_N, v_sx, v_fN, ret_val_opt)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_opt = $trunc_sat__(v_M, v_N, v_sx, v_fN))
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:3546.1-3546.98
def $relaxed_trunc__(v_M : M, v_N : N, v_sx : sx, v_fN : fN) : iN?

;; test.spectec:3546.6-3546.22
relation relaxed_trunc___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?)
  ;; test.spectec:3546.6-3546.22
  rule relaxed_trunc___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?}:
    `%%%%%`(v_M, v_N, v_sx, v_fN, ret_val_opt)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_opt = $relaxed_trunc__(v_M, v_N, v_sx, v_fN))
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:3547.1-3547.36
def $demote__(v_M : M, v_N : N, v_fN : fN) : fN*

;; test.spectec:3547.6-3547.15
relation demote___is_wf: `%%%%`(v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3547.6-3547.15
  rule demote___is_wf_0{v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%%`(v_M, v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_lst = $demote__(v_M, v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3548.1-3548.37
def $promote__(v_M : M, v_N : N, v_fN : fN) : fN*

;; test.spectec:3548.6-3548.16
relation promote___is_wf: `%%%%`(v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:3548.6-3548.16
  rule promote___is_wf_0{v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%%`(v_M, v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_lst = $promote__(v_M, v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3549.1-3549.91
def $convert__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : fN

;; test.spectec:3549.6-3549.16
relation convert___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : fN)
  ;; test.spectec:3549.6-3549.16
  rule convert___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : fN}:
    `%%%%%`(v_M, v_N, v_sx, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $convert__(v_M, v_N, v_sx, v_iN))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:3550.1-3550.88
def $narrow__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : iN

;; test.spectec:3550.6-3550.15
relation narrow___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : iN)
  ;; test.spectec:3550.6-3550.15
  rule narrow___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : iN}:
    `%%%%%`(v_M, v_N, v_sx, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $narrow__(v_M, v_N, v_sx, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3552.1-3552.76
def $reinterpret__(numtype_1 : numtype, numtype_2 : numtype, v_num_ : num_) : num_

;; test.spectec:3552.6-3552.20
relation reinterpret___is_wf: `%%%%`(numtype_1 : numtype, numtype_2 : numtype, v_num_ : num_, ret_val : num_)
  ;; test.spectec:3552.6-3552.20
  rule reinterpret___is_wf_0{numtype_1 : numtype, numtype_2 : numtype, v_num_ : num_, ret_val : num_}:
    `%%%%`(numtype_1, numtype_2, v_num_, ret_val)
    -- wf_num_: `%%`(numtype_1, v_num_)
    -- if (ret_val = $reinterpret__(numtype_1, numtype_2, v_num_))
    -- wf_num_: `%%`(numtype_2, ret_val)

;; test.spectec:3572.1-3573.49
def $lpacknum_(v_lanetype : lanetype, v_num_ : num_) : lane_
  ;; test.spectec:3577.1-3577.31
  def $lpacknum_{c : num_}(I32_lanetype, c) = mk_lane__0_lane_(I32_numtype, c)
  ;; test.spectec:3577.1-3577.31
  def $lpacknum_{c : num_}(I64_lanetype, c) = mk_lane__0_lane_(I64_numtype, c)
  ;; test.spectec:3577.1-3577.31
  def $lpacknum_{c : num_}(F32_lanetype, c) = mk_lane__0_lane_(F32_numtype, c)
  ;; test.spectec:3577.1-3577.31
  def $lpacknum_{c : num_}(F64_lanetype, c) = mk_lane__0_lane_(F64_numtype, c)
  ;; test.spectec:3578.1-3578.86
  def $lpacknum_{c : uN}(I8_lanetype, mk_num__0_num_(I32_Inn, c)) = mk_lane__1_lane_(I8_packtype, $wrap__($size($lunpack($lanetype_packtype(I8_packtype))), $psize(I8_packtype), c))
  ;; test.spectec:3578.1-3578.86
  def $lpacknum_{c : uN}(I16_lanetype, mk_num__0_num_(I32_Inn, c)) = mk_lane__1_lane_(I16_packtype, $wrap__($size($lunpack($lanetype_packtype(I16_packtype))), $psize(I16_packtype), c))

;; test.spectec:3572.6-3572.16
relation lpacknum__is_wf: `%%%`(v_lanetype : lanetype, v_num_ : num_, ret_val : lane_)
  ;; test.spectec:3572.6-3572.16
  rule lpacknum__is_wf_0{v_lanetype : lanetype, v_num_ : num_, ret_val : lane_}:
    `%%%`(v_lanetype, v_num_, ret_val)
    -- wf_num_: `%%`($lunpack(v_lanetype), v_num_)
    -- if (ret_val = $lpacknum_(v_lanetype, v_num_))
    -- wf_lane_: `%%`(v_lanetype, ret_val)

;; test.spectec:3574.1-3575.49
def $cpacknum_(v_storagetype : storagetype, v_lit_ : lit_) : lit_
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{c : lit_}(I32_storagetype, c) = c
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{c : lit_}(I64_storagetype, c) = c
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{c : lit_}(F32_storagetype, c) = c
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{c : lit_}(F64_storagetype, c) = c
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{c : lit_}(V128_storagetype, c) = c
  ;; test.spectec:3581.1-3581.86
  def $cpacknum_{c : uN}(I8_storagetype, mk_lit__0_lit_(I32_numtype, mk_num__0_num_(I32_Inn, c))) = mk_lit__2_lit_(I8_packtype, $wrap__($size($lunpack($lanetype_packtype(I8_packtype))), $psize(I8_packtype), c))
  ;; test.spectec:3581.1-3581.86
  def $cpacknum_{c : uN}(I16_storagetype, mk_lit__0_lit_(I32_numtype, mk_num__0_num_(I32_Inn, c))) = mk_lit__2_lit_(I16_packtype, $wrap__($size($lunpack($lanetype_packtype(I16_packtype))), $psize(I16_packtype), c))

;; test.spectec:3574.6-3574.16
relation cpacknum__is_wf: `%%%`(v_storagetype : storagetype, v_lit_ : lit_, ret_val : lit_)
  ;; test.spectec:3574.6-3574.16
  rule cpacknum__is_wf_0{v_storagetype : storagetype, v_lit_ : lit_, ret_val : lit_}:
    `%%%`(v_storagetype, v_lit_, ret_val)
    -- wf_storagetype: `%`(v_storagetype)
    -- if ($cunpack(v_storagetype) =/= ?())
    -- wf_lit_: `%%`($storagetype_consttype(!($cunpack(v_storagetype))), v_lit_)
    -- if (ret_val = $cpacknum_(v_storagetype, v_lit_))
    -- wf_lit_: `%%`(v_storagetype, ret_val)

;; test.spectec:3584.1-3585.53
def $lunpacknum_(v_lanetype : lanetype, v_lane_ : lane_) : num_
  ;; test.spectec:3589.1-3589.33
  def $lunpacknum_{c : num_}(I32_lanetype, mk_lane__0_lane_(I32_numtype, c)) = c
  ;; test.spectec:3589.1-3589.33
  def $lunpacknum_{c : num_}(I64_lanetype, mk_lane__0_lane_(I64_numtype, c)) = c
  ;; test.spectec:3589.1-3589.33
  def $lunpacknum_{c : num_}(F32_lanetype, mk_lane__0_lane_(F32_numtype, c)) = c
  ;; test.spectec:3589.1-3589.33
  def $lunpacknum_{c : num_}(F64_lanetype, mk_lane__0_lane_(F64_numtype, c)) = c
  ;; test.spectec:3590.1-3590.93
  def $lunpacknum_{c : uN}(I8_lanetype, mk_lane__1_lane_(I8_packtype, c)) = mk_num__0_num_(I32_Inn, $extend__($psize(I8_packtype), $size($lunpack($lanetype_packtype(I8_packtype))), U_sx, c))
  ;; test.spectec:3590.1-3590.93
  def $lunpacknum_{c : uN}(I16_lanetype, mk_lane__1_lane_(I16_packtype, c)) = mk_num__0_num_(I32_Inn, $extend__($psize(I16_packtype), $size($lunpack($lanetype_packtype(I16_packtype))), U_sx, c))

;; test.spectec:3584.6-3584.18
relation lunpacknum__is_wf: `%%%`(v_lanetype : lanetype, v_lane_ : lane_, ret_val : num_)
  ;; test.spectec:3584.6-3584.18
  rule lunpacknum__is_wf_0{v_lanetype : lanetype, v_lane_ : lane_, ret_val : num_}:
    `%%%`(v_lanetype, v_lane_, ret_val)
    -- wf_lane_: `%%`(v_lanetype, v_lane_)
    -- if (ret_val = $lunpacknum_(v_lanetype, v_lane_))
    -- wf_num_: `%%`($lunpack(v_lanetype), ret_val)

;; test.spectec:3586.1-3587.53
def $cunpacknum_(v_storagetype : storagetype, v_lit_ : lit_) : lit_
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{c : lit_}(I32_storagetype, c) = c
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{c : lit_}(I64_storagetype, c) = c
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{c : lit_}(F32_storagetype, c) = c
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{c : lit_}(F64_storagetype, c) = c
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{c : lit_}(V128_storagetype, c) = c
  ;; test.spectec:3593.1-3593.93
  def $cunpacknum_{c : uN}(I8_storagetype, mk_lit__2_lit_(I8_packtype, c)) = mk_lit__0_lit_(I32_numtype, mk_num__0_num_(I32_Inn, $extend__($psize(I8_packtype), $size($lunpack($lanetype_packtype(I8_packtype))), U_sx, c)))
  ;; test.spectec:3593.1-3593.93
  def $cunpacknum_{c : uN}(I16_storagetype, mk_lit__2_lit_(I16_packtype, c)) = mk_lit__0_lit_(I32_numtype, mk_num__0_num_(I32_Inn, $extend__($psize(I16_packtype), $size($lunpack($lanetype_packtype(I16_packtype))), U_sx, c)))

;; test.spectec:3586.6-3586.18
relation cunpacknum__is_wf: `%%%`(v_storagetype : storagetype, v_lit_ : lit_, ret_val : lit_)
  ;; test.spectec:3586.6-3586.18
  rule cunpacknum__is_wf_0{v_storagetype : storagetype, v_lit_ : lit_, ret_val : lit_}:
    `%%%`(v_storagetype, v_lit_, ret_val)
    -- wf_storagetype: `%`(v_storagetype)
    -- wf_lit_: `%%`(v_storagetype, v_lit_)
    -- if (ret_val = $cunpacknum_(v_storagetype, v_lit_))
    -- if ($cunpack(v_storagetype) =/= ?())
    -- wf_lit_: `%%`($storagetype_consttype(!($cunpack(v_storagetype))), ret_val)

;; test.spectec:3598.6-3598.12
relation fun_unop_: `%%%%`(numtype, unop_, num_, num_*)
  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_0{i : uN}:
    `%%%%`(I32_numtype, mk_unop__0_unop_(I32_Inn, CLZ_unop_Inn), mk_num__0_num_(I32_Inn, i), [mk_num__0_num_(I32_Inn, $iclz_($sizenn($numtype_addrtype(I32_Inn)), i))])

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_1{i : uN}:
    `%%%%`(I64_numtype, mk_unop__0_unop_(I64_Inn, CLZ_unop_Inn), mk_num__0_num_(I64_Inn, i), [mk_num__0_num_(I64_Inn, $iclz_($sizenn($numtype_addrtype(I64_Inn)), i))])

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_2{i : uN}:
    `%%%%`(I32_numtype, mk_unop__0_unop_(I32_Inn, CTZ_unop_Inn), mk_num__0_num_(I32_Inn, i), [mk_num__0_num_(I32_Inn, $ictz_($sizenn($numtype_addrtype(I32_Inn)), i))])

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_3{i : uN}:
    `%%%%`(I64_numtype, mk_unop__0_unop_(I64_Inn, CTZ_unop_Inn), mk_num__0_num_(I64_Inn, i), [mk_num__0_num_(I64_Inn, $ictz_($sizenn($numtype_addrtype(I64_Inn)), i))])

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_4{i : uN}:
    `%%%%`(I32_numtype, mk_unop__0_unop_(I32_Inn, POPCNT_unop_Inn), mk_num__0_num_(I32_Inn, i), [mk_num__0_num_(I32_Inn, $ipopcnt_($sizenn($numtype_addrtype(I32_Inn)), i))])

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_5{i : uN}:
    `%%%%`(I64_numtype, mk_unop__0_unop_(I64_Inn, POPCNT_unop_Inn), mk_num__0_num_(I64_Inn, i), [mk_num__0_num_(I64_Inn, $ipopcnt_($sizenn($numtype_addrtype(I64_Inn)), i))])

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_6{v_M : nat, i : uN, var_0 : uN}:
    `%%%%`(I32_numtype, mk_unop__0_unop_(I32_Inn, EXTEND_unop_Inn(mk_sz_sz(v_M))), mk_num__0_num_(I32_Inn, i), [mk_num__0_num_(I32_Inn, var_0)])
    -- fun_iextend_: `%%%%%`($sizenn($numtype_addrtype(I32_Inn)), v_M, S_sx, i, var_0)

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_7{v_M : nat, i : uN, var_0 : uN}:
    `%%%%`(I64_numtype, mk_unop__0_unop_(I64_Inn, EXTEND_unop_Inn(mk_sz_sz(v_M))), mk_num__0_num_(I64_Inn, i), [mk_num__0_num_(I64_Inn, var_0)])
    -- fun_iextend_: `%%%%%`($sizenn($numtype_addrtype(I64_Inn)), v_M, S_sx, i, var_0)

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_8{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, ABS_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_1)*{iter_0_1 <- $fabs_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_9{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, ABS_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_2)*{iter_0_2 <- $fabs_($sizenn($numtype_Fnn(F64_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_10{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, NEG_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_3)*{iter_0_3 <- $fneg_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_11{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, NEG_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_4)*{iter_0_4 <- $fneg_($sizenn($numtype_Fnn(F64_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_12{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, SQRT_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_5)*{iter_0_5 <- $fsqrt_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_13{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, SQRT_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_6)*{iter_0_6 <- $fsqrt_($sizenn($numtype_Fnn(F64_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_14{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, CEIL_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_7)*{iter_0_7 <- $fceil_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_15{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, CEIL_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_8)*{iter_0_8 <- $fceil_($sizenn($numtype_Fnn(F64_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_16{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, FLOOR_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_9)*{iter_0_9 <- $ffloor_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_17{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, FLOOR_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_10)*{iter_0_10 <- $ffloor_($sizenn($numtype_Fnn(F64_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_18{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, TRUNC_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_11)*{iter_0_11 <- $ftrunc_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_19{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, TRUNC_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_12)*{iter_0_12 <- $ftrunc_($sizenn($numtype_Fnn(F64_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_20{f : fN}:
    `%%%%`(F32_numtype, mk_unop__1_unop_(F32_Fnn, NEAREST_unop_Fnn), mk_num__1_num_(F32_Fnn, f), mk_num__1_num_(F32_Fnn, iter_0_13)*{iter_0_13 <- $fnearest_($sizenn($numtype_Fnn(F32_Fnn)), f)})

  ;; test.spectec:3598.6-3598.12
  rule fun_unop__case_21{f : fN}:
    `%%%%`(F64_numtype, mk_unop__1_unop_(F64_Fnn, NEAREST_unop_Fnn), mk_num__1_num_(F64_Fnn, f), mk_num__1_num_(F64_Fnn, iter_0_14)*{iter_0_14 <- $fnearest_($sizenn($numtype_Fnn(F64_Fnn)), f)})

;; test.spectec:3598.6-3598.12
relation unop__is_wf: `%%%%`(v_numtype : numtype, v_unop_ : unop_, v_num_ : num_, ret_val_lst : num_*)
  ;; test.spectec:3598.6-3598.12
  rule unop__is_wf_0{v_numtype : numtype, v_unop_ : unop_, v_num_ : num_, ret_val_lst : num_*, var_0 : num_*}:
    `%%%%`(v_numtype, v_unop_, v_num_, ret_val_lst)
    -- fun_unop_: `%%%%`(v_numtype, v_unop_, v_num_, var_0)
    -- wf_unop_: `%%`(v_numtype, v_unop_)
    -- wf_num_: `%%`(v_numtype, v_num_)
    -- if (ret_val_lst = var_0)
    -- (wf_num_: `%%`(v_numtype, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3600.6-3600.13
relation fun_binop_: `%%%%%`(numtype, binop_, num_, num_, num_*)
  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_0{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, ADD_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $iadd_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_1{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, ADD_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $iadd_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_2{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, SUB_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $isub_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_3{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, SUB_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $isub_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_4{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, MUL_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $imul_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_5{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, MUL_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $imul_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_6{v_sx : sx, i_1 : uN, i_2 : uN, var_0 : iN?}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), mk_num__0_num_(I32_Inn, iter_0_15)*{iter_0_15 <- lift(var_0)})
    -- fun_idiv_: `%%%%%`($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, i_2, var_0)

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_7{v_sx : sx, i_1 : uN, i_2 : uN, var_0 : iN?}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), mk_num__0_num_(I64_Inn, iter_0_16)*{iter_0_16 <- lift(var_0)})
    -- fun_idiv_: `%%%%%`($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, i_2, var_0)

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_8{v_sx : sx, i_1 : uN, i_2 : uN, var_0 : iN?}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), mk_num__0_num_(I32_Inn, iter_0_17)*{iter_0_17 <- lift(var_0)})
    -- fun_irem_: `%%%%%`($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, i_2, var_0)

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_9{v_sx : sx, i_1 : uN, i_2 : uN, var_0 : iN?}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), mk_num__0_num_(I64_Inn, iter_0_18)*{iter_0_18 <- lift(var_0)})
    -- fun_irem_: `%%%%%`($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, i_2, var_0)

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_10{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, AND_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $iand_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_11{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, AND_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $iand_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_12{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, OR_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $ior_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_13{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, OR_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $ior_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_14{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, XOR_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $ixor_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_15{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, XOR_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $ixor_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_16{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, SHL_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $ishl_($sizenn($numtype_addrtype(I32_Inn)), i_1, mk_uN_u32($proj_uN_0(i_2).0)))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_17{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, SHL_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $ishl_($sizenn($numtype_addrtype(I64_Inn)), i_1, mk_uN_u32($proj_uN_0(i_2).0)))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_18{v_sx : sx, i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $ishr_($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, mk_uN_u32($proj_uN_0(i_2).0)))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_19{v_sx : sx, i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $ishr_($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, mk_uN_u32($proj_uN_0(i_2).0)))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_20{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, ROTL_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $irotl_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_21{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, ROTL_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $irotl_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_22{i_1 : uN, i_2 : uN}:
    `%%%%%`(I32_numtype, mk_binop__0_binop_(I32_Inn, ROTR_binop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2), [mk_num__0_num_(I32_Inn, $irotr_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_23{i_1 : uN, i_2 : uN}:
    `%%%%%`(I64_numtype, mk_binop__0_binop_(I64_Inn, ROTR_binop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2), [mk_num__0_num_(I64_Inn, $irotr_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2))])

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_24{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, ADD_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_19)*{iter_0_19 <- $fadd_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_25{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, ADD_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_20)*{iter_0_20 <- $fadd_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_26{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, SUB_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_21)*{iter_0_21 <- $fsub_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_27{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, SUB_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_22)*{iter_0_22 <- $fsub_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_28{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, MUL_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_23)*{iter_0_23 <- $fmul_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_29{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, MUL_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_24)*{iter_0_24 <- $fmul_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_30{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, DIV_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_25)*{iter_0_25 <- $fdiv_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_31{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, DIV_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_26)*{iter_0_26 <- $fdiv_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_32{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, MIN_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_27)*{iter_0_27 <- $fmin_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_33{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, MIN_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_28)*{iter_0_28 <- $fmin_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_34{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, MAX_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_29)*{iter_0_29 <- $fmax_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_35{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, MAX_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_30)*{iter_0_30 <- $fmax_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_36{f_1 : fN, f_2 : fN}:
    `%%%%%`(F32_numtype, mk_binop__1_binop_(F32_Fnn, COPYSIGN_binop_Fnn), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2), mk_num__1_num_(F32_Fnn, iter_0_31)*{iter_0_31 <- $fcopysign_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)})

  ;; test.spectec:3600.6-3600.13
  rule fun_binop__case_37{f_1 : fN, f_2 : fN}:
    `%%%%%`(F64_numtype, mk_binop__1_binop_(F64_Fnn, COPYSIGN_binop_Fnn), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2), mk_num__1_num_(F64_Fnn, iter_0_32)*{iter_0_32 <- $fcopysign_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)})

;; test.spectec:3600.6-3600.13
relation binop__is_wf: `%%%%%`(v_numtype : numtype, v_binop_ : binop_, v_num_ : num_, num__0 : num_, ret_val_lst : num_*)
  ;; test.spectec:3600.6-3600.13
  rule binop__is_wf_0{v_numtype : numtype, v_binop_ : binop_, v_num_ : num_, num__0 : num_, ret_val_lst : num_*, var_0 : num_*}:
    `%%%%%`(v_numtype, v_binop_, v_num_, num__0, ret_val_lst)
    -- fun_binop_: `%%%%%`(v_numtype, v_binop_, v_num_, num__0, var_0)
    -- wf_binop_: `%%`(v_numtype, v_binop_)
    -- wf_num_: `%%`(v_numtype, v_num_)
    -- wf_num_: `%%`(v_numtype, num__0)
    -- if (ret_val_lst = var_0)
    -- (wf_num_: `%%`(v_numtype, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3602.1-3603.28
def $fun_testop_(v_numtype : numtype, v_testop_ : testop_, v_num_ : num_) : u32
  ;; test.spectec:3643.1-3643.52
  def $fun_testop_{i : uN}(I32_numtype, mk_testop__0_testop_(I32_Inn, EQZ_testop_Inn), mk_num__0_num_(I32_Inn, i)) = $ieqz_($sizenn($numtype_addrtype(I32_Inn)), i)
  ;; test.spectec:3643.1-3643.52
  def $fun_testop_{i : uN}(I64_numtype, mk_testop__0_testop_(I64_Inn, EQZ_testop_Inn), mk_num__0_num_(I64_Inn, i)) = $ieqz_($sizenn($numtype_addrtype(I64_Inn)), i)

;; test.spectec:3602.6-3602.14
relation testop__is_wf: `%%%%`(v_numtype : numtype, v_testop_ : testop_, v_num_ : num_, ret_val : u32)
  ;; test.spectec:3602.6-3602.14
  rule testop__is_wf_0{v_numtype : numtype, v_testop_ : testop_, v_num_ : num_, ret_val : u32}:
    `%%%%`(v_numtype, v_testop_, v_num_, ret_val)
    -- wf_testop_: `%%`(v_numtype, v_testop_)
    -- wf_num_: `%%`(v_numtype, v_num_)
    -- if (ret_val = $fun_testop_(v_numtype, v_testop_, v_num_))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3604.1-3605.32
def $fun_relop__I64(v_relop_ : relop_, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3645.1-3645.63
  def $fun_relop__I64{i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I64_Inn, EQ_relop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2)) = $ieq_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2)
  ;; test.spectec:3646.1-3646.63
  def $fun_relop__I64{i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I64_Inn, NE_relop_Inn), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2)) = $ine_($sizenn($numtype_addrtype(I64_Inn)), i_1, i_2)
  ;; test.spectec:3647.1-3647.70
  def $fun_relop__I64{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I64_Inn, LT_relop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2)) = $ilt_($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, i_2)
  ;; test.spectec:3648.1-3648.70
  def $fun_relop__I64{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I64_Inn, GT_relop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2)) = $igt_($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, i_2)
  ;; test.spectec:3649.1-3649.70
  def $fun_relop__I64{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I64_Inn, LE_relop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2)) = $ile_($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, i_2)
  ;; test.spectec:3650.1-3650.70
  def $fun_relop__I64{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I64_Inn, GE_relop_Inn(v_sx)), mk_num__0_num_(I64_Inn, i_1), mk_num__0_num_(I64_Inn, i_2)) = $ige_($sizenn($numtype_addrtype(I64_Inn)), v_sx, i_1, i_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__I32(v_relop_ : relop_, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3645.1-3645.63
  def $fun_relop__I32{i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I32_Inn, EQ_relop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2)) = $ieq_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2)
  ;; test.spectec:3646.1-3646.63
  def $fun_relop__I32{i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I32_Inn, NE_relop_Inn), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2)) = $ine_($sizenn($numtype_addrtype(I32_Inn)), i_1, i_2)
  ;; test.spectec:3647.1-3647.70
  def $fun_relop__I32{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I32_Inn, LT_relop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2)) = $ilt_($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, i_2)
  ;; test.spectec:3648.1-3648.70
  def $fun_relop__I32{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I32_Inn, GT_relop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2)) = $igt_($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, i_2)
  ;; test.spectec:3649.1-3649.70
  def $fun_relop__I32{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I32_Inn, LE_relop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2)) = $ile_($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, i_2)
  ;; test.spectec:3650.1-3650.70
  def $fun_relop__I32{v_sx : sx, i_1 : uN, i_2 : uN}(mk_relop__0_relop_(I32_Inn, GE_relop_Inn(v_sx)), mk_num__0_num_(I32_Inn, i_1), mk_num__0_num_(I32_Inn, i_2)) = $ige_($sizenn($numtype_addrtype(I32_Inn)), v_sx, i_1, i_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64_NE(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3653.1-3653.63
  def $fun_relop__F64_mk_relop__1_F64_NE{f_1 : fN, f_2 : fN}(mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2)) = $fne_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64_LT(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3654.1-3654.63
  def $fun_relop__F64_mk_relop__1_F64_LT{f_1 : fN, f_2 : fN}(mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2)) = $flt_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64_LE(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3656.1-3656.63
  def $fun_relop__F64_mk_relop__1_F64_LE{f_1 : fN, f_2 : fN}(mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2)) = $fle_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64_GT(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3655.1-3655.63
  def $fun_relop__F64_mk_relop__1_F64_GT{f_1 : fN, f_2 : fN}(mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2)) = $fgt_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64_GE(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3657.1-3657.63
  def $fun_relop__F64_mk_relop__1_F64_GE{f_1 : fN, f_2 : fN}(mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2)) = $fge_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64_EQ(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3652.1-3652.63
  def $fun_relop__F64_mk_relop__1_F64_EQ{f_1 : fN, f_2 : fN}(mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, f_2)) = $feq_($sizenn($numtype_Fnn(F64_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1_F64(mk_relop__1_argument_1 : relop_Fnn, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1_F64{v_num_ : num_, num__0 : num_}(NE_relop_Fnn, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64_NE(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1_F64{v_num_ : num_, num__0 : num_}(LT_relop_Fnn, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64_LT(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1_F64{v_num_ : num_, num__0 : num_}(LE_relop_Fnn, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64_LE(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1_F64{v_num_ : num_, num__0 : num_}(GT_relop_Fnn, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64_GT(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1_F64{v_num_ : num_, num__0 : num_}(GE_relop_Fnn, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64_GE(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1_F64{v_num_ : num_, num__0 : num_}(EQ_relop_Fnn, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64_EQ(v_num_, num__0)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64_mk_relop__1(mk_relop__1_argument_0 : Fnn, mk_relop__1_argument_1 : relop_Fnn, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64_mk_relop__1{mk_relop__1_argument_1 : relop_Fnn, v_num_ : num_, num__0 : num_}(F64_Fnn, mk_relop__1_argument_1, v_num_, num__0) = $fun_relop__F64_mk_relop__1_F64(mk_relop__1_argument_1, v_num_, num__0)

;; test.spectec:3604.1-3605.32
def $fun_relop__F64(v_relop_ : relop_, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F64{constructor_parameter_0 : Fnn, constructor_parameter_1 : relop_Fnn, v_num_ : num_, num__0 : num_}(mk_relop__1_relop_(constructor_parameter_0, constructor_parameter_1), v_num_, num__0) = $fun_relop__F64_mk_relop__1(constructor_parameter_0, constructor_parameter_1, v_num_, num__0)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32_NE(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3653.1-3653.63
  def $fun_relop__F32_mk_relop__1_F32_NE{f_1 : fN, f_2 : fN}(mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2)) = $fne_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32_LT(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3654.1-3654.63
  def $fun_relop__F32_mk_relop__1_F32_LT{f_1 : fN, f_2 : fN}(mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2)) = $flt_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32_LE(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3656.1-3656.63
  def $fun_relop__F32_mk_relop__1_F32_LE{f_1 : fN, f_2 : fN}(mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2)) = $fle_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32_GT(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3655.1-3655.63
  def $fun_relop__F32_mk_relop__1_F32_GT{f_1 : fN, f_2 : fN}(mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2)) = $fgt_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32_GE(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3657.1-3657.63
  def $fun_relop__F32_mk_relop__1_F32_GE{f_1 : fN, f_2 : fN}(mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2)) = $fge_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32_EQ(v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3652.1-3652.63
  def $fun_relop__F32_mk_relop__1_F32_EQ{f_1 : fN, f_2 : fN}(mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, f_2)) = $feq_($sizenn($numtype_Fnn(F32_Fnn)), f_1, f_2)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1_F32(mk_relop__1_argument_1 : relop_Fnn, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1_F32{v_num_ : num_, num__0 : num_}(NE_relop_Fnn, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32_NE(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1_F32{v_num_ : num_, num__0 : num_}(LT_relop_Fnn, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32_LT(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1_F32{v_num_ : num_, num__0 : num_}(LE_relop_Fnn, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32_LE(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1_F32{v_num_ : num_, num__0 : num_}(GT_relop_Fnn, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32_GT(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1_F32{v_num_ : num_, num__0 : num_}(GE_relop_Fnn, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32_GE(v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1_F32{v_num_ : num_, num__0 : num_}(EQ_relop_Fnn, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32_EQ(v_num_, num__0)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32_mk_relop__1(mk_relop__1_argument_0 : Fnn, mk_relop__1_argument_1 : relop_Fnn, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32_mk_relop__1{mk_relop__1_argument_1 : relop_Fnn, v_num_ : num_, num__0 : num_}(F32_Fnn, mk_relop__1_argument_1, v_num_, num__0) = $fun_relop__F32_mk_relop__1_F32(mk_relop__1_argument_1, v_num_, num__0)

;; test.spectec:3604.1-3605.32
def $fun_relop__F32(v_relop_ : relop_, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop__F32{constructor_parameter_0 : Fnn, constructor_parameter_1 : relop_Fnn, v_num_ : num_, num__0 : num_}(mk_relop__1_relop_(constructor_parameter_0, constructor_parameter_1), v_num_, num__0) = $fun_relop__F32_mk_relop__1(constructor_parameter_0, constructor_parameter_1, v_num_, num__0)

;; test.spectec:3604.1-3605.32
def $fun_relop_(v_numtype : numtype, v_relop_ : relop_, v_num_ : num_, num__0 : num_) : u32
  ;; test.spectec:3604.6-3604.13
  def $fun_relop_{v_relop_ : relop_, v_num_ : num_, num__0 : num_}(I64_numtype, v_relop_, v_num_, num__0) = $fun_relop__I64(v_relop_, v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop_{v_relop_ : relop_, v_num_ : num_, num__0 : num_}(I32_numtype, v_relop_, v_num_, num__0) = $fun_relop__I32(v_relop_, v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop_{v_relop_ : relop_, v_num_ : num_, num__0 : num_}(F64_numtype, v_relop_, v_num_, num__0) = $fun_relop__F64(v_relop_, v_num_, num__0)
  ;; test.spectec:3604.6-3604.13
  def $fun_relop_{v_relop_ : relop_, v_num_ : num_, num__0 : num_}(F32_numtype, v_relop_, v_num_, num__0) = $fun_relop__F32(v_relop_, v_num_, num__0)

;; test.spectec:3604.6-3604.13
relation relop__is_wf: `%%%%%`(v_numtype : numtype, v_relop_ : relop_, v_num_ : num_, num__0 : num_, ret_val : u32)
  ;; test.spectec:3604.6-3604.13
  rule relop__is_wf_0{v_numtype : numtype, v_relop_ : relop_, v_num_ : num_, num__0 : num_, ret_val : u32}:
    `%%%%%`(v_numtype, v_relop_, v_num_, num__0, ret_val)
    -- wf_relop_: `%%`(v_numtype, v_relop_)
    -- wf_num_: `%%`(v_numtype, v_num_)
    -- wf_num_: `%%`(v_numtype, num__0)
    -- if (ret_val = $fun_relop_(v_numtype, v_relop_, v_num_, num__0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3606.6-3606.14
relation fun_cvtop__: `%%%%%`(numtype, numtype, cvtop__, num_, num_*)
  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_0{v_sx : sx, i_1 : uN}:
    `%%%%%`(I32_numtype, I32_numtype, mk_cvtop___0_cvtop__(I32_Inn, I32_Inn, EXTEND_cvtop__Inn_1_Inn_2(v_sx)), mk_num__0_num_(I32_Inn, i_1), [mk_num__0_num_(I32_Inn, $extend__($sizenn1($numtype_addrtype(I32_Inn)), $sizenn2($numtype_addrtype(I32_Inn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_1{v_sx : sx, i_1 : uN}:
    `%%%%%`(I64_numtype, I32_numtype, mk_cvtop___0_cvtop__(I64_Inn, I32_Inn, EXTEND_cvtop__Inn_1_Inn_2(v_sx)), mk_num__0_num_(I64_Inn, i_1), [mk_num__0_num_(I32_Inn, $extend__($sizenn1($numtype_addrtype(I64_Inn)), $sizenn2($numtype_addrtype(I32_Inn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_2{v_sx : sx, i_1 : uN}:
    `%%%%%`(I32_numtype, I64_numtype, mk_cvtop___0_cvtop__(I32_Inn, I64_Inn, EXTEND_cvtop__Inn_1_Inn_2(v_sx)), mk_num__0_num_(I32_Inn, i_1), [mk_num__0_num_(I64_Inn, $extend__($sizenn1($numtype_addrtype(I32_Inn)), $sizenn2($numtype_addrtype(I64_Inn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_3{v_sx : sx, i_1 : uN}:
    `%%%%%`(I64_numtype, I64_numtype, mk_cvtop___0_cvtop__(I64_Inn, I64_Inn, EXTEND_cvtop__Inn_1_Inn_2(v_sx)), mk_num__0_num_(I64_Inn, i_1), [mk_num__0_num_(I64_Inn, $extend__($sizenn1($numtype_addrtype(I64_Inn)), $sizenn2($numtype_addrtype(I64_Inn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_4{i_1 : uN}:
    `%%%%%`(I32_numtype, I32_numtype, mk_cvtop___0_cvtop__(I32_Inn, I32_Inn, WRAP_cvtop__Inn_1_Inn_2), mk_num__0_num_(I32_Inn, i_1), [mk_num__0_num_(I32_Inn, $wrap__($sizenn1($numtype_addrtype(I32_Inn)), $sizenn2($numtype_addrtype(I32_Inn)), i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_5{i_1 : uN}:
    `%%%%%`(I64_numtype, I32_numtype, mk_cvtop___0_cvtop__(I64_Inn, I32_Inn, WRAP_cvtop__Inn_1_Inn_2), mk_num__0_num_(I64_Inn, i_1), [mk_num__0_num_(I32_Inn, $wrap__($sizenn1($numtype_addrtype(I64_Inn)), $sizenn2($numtype_addrtype(I32_Inn)), i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_6{i_1 : uN}:
    `%%%%%`(I32_numtype, I64_numtype, mk_cvtop___0_cvtop__(I32_Inn, I64_Inn, WRAP_cvtop__Inn_1_Inn_2), mk_num__0_num_(I32_Inn, i_1), [mk_num__0_num_(I64_Inn, $wrap__($sizenn1($numtype_addrtype(I32_Inn)), $sizenn2($numtype_addrtype(I64_Inn)), i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_7{i_1 : uN}:
    `%%%%%`(I64_numtype, I64_numtype, mk_cvtop___0_cvtop__(I64_Inn, I64_Inn, WRAP_cvtop__Inn_1_Inn_2), mk_num__0_num_(I64_Inn, i_1), [mk_num__0_num_(I64_Inn, $wrap__($sizenn1($numtype_addrtype(I64_Inn)), $sizenn2($numtype_addrtype(I64_Inn)), i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_8{v_sx : sx, f_1 : fN}:
    `%%%%%`(F32_numtype, I32_numtype, mk_cvtop___2_cvtop__(F32_Fnn, I32_Inn, TRUNC_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F32_Fnn, f_1), mk_num__0_num_(I32_Inn, iter_0_33)*{iter_0_33 <- lift($trunc__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_addrtype(I32_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_9{v_sx : sx, f_1 : fN}:
    `%%%%%`(F64_numtype, I32_numtype, mk_cvtop___2_cvtop__(F64_Fnn, I32_Inn, TRUNC_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F64_Fnn, f_1), mk_num__0_num_(I32_Inn, iter_0_34)*{iter_0_34 <- lift($trunc__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_addrtype(I32_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_10{v_sx : sx, f_1 : fN}:
    `%%%%%`(F32_numtype, I64_numtype, mk_cvtop___2_cvtop__(F32_Fnn, I64_Inn, TRUNC_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F32_Fnn, f_1), mk_num__0_num_(I64_Inn, iter_0_35)*{iter_0_35 <- lift($trunc__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_addrtype(I64_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_11{v_sx : sx, f_1 : fN}:
    `%%%%%`(F64_numtype, I64_numtype, mk_cvtop___2_cvtop__(F64_Fnn, I64_Inn, TRUNC_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F64_Fnn, f_1), mk_num__0_num_(I64_Inn, iter_0_36)*{iter_0_36 <- lift($trunc__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_addrtype(I64_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_12{v_sx : sx, f_1 : fN}:
    `%%%%%`(F32_numtype, I32_numtype, mk_cvtop___2_cvtop__(F32_Fnn, I32_Inn, TRUNC_SAT_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F32_Fnn, f_1), mk_num__0_num_(I32_Inn, iter_0_37)*{iter_0_37 <- lift($trunc_sat__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_addrtype(I32_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_13{v_sx : sx, f_1 : fN}:
    `%%%%%`(F64_numtype, I32_numtype, mk_cvtop___2_cvtop__(F64_Fnn, I32_Inn, TRUNC_SAT_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F64_Fnn, f_1), mk_num__0_num_(I32_Inn, iter_0_38)*{iter_0_38 <- lift($trunc_sat__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_addrtype(I32_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_14{v_sx : sx, f_1 : fN}:
    `%%%%%`(F32_numtype, I64_numtype, mk_cvtop___2_cvtop__(F32_Fnn, I64_Inn, TRUNC_SAT_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F32_Fnn, f_1), mk_num__0_num_(I64_Inn, iter_0_39)*{iter_0_39 <- lift($trunc_sat__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_addrtype(I64_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_15{v_sx : sx, f_1 : fN}:
    `%%%%%`(F64_numtype, I64_numtype, mk_cvtop___2_cvtop__(F64_Fnn, I64_Inn, TRUNC_SAT_cvtop__Fnn_1_Inn_2(v_sx)), mk_num__1_num_(F64_Fnn, f_1), mk_num__0_num_(I64_Inn, iter_0_40)*{iter_0_40 <- lift($trunc_sat__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_addrtype(I64_Inn)), v_sx, f_1))})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_16{v_sx : sx, i_1 : uN}:
    `%%%%%`(I32_numtype, F32_numtype, mk_cvtop___1_cvtop__(I32_Inn, F32_Fnn, CONVERT_cvtop__Inn_1_Fnn_2(v_sx)), mk_num__0_num_(I32_Inn, i_1), [mk_num__1_num_(F32_Fnn, $convert__($sizenn1($numtype_addrtype(I32_Inn)), $sizenn2($numtype_Fnn(F32_Fnn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_17{v_sx : sx, i_1 : uN}:
    `%%%%%`(I64_numtype, F32_numtype, mk_cvtop___1_cvtop__(I64_Inn, F32_Fnn, CONVERT_cvtop__Inn_1_Fnn_2(v_sx)), mk_num__0_num_(I64_Inn, i_1), [mk_num__1_num_(F32_Fnn, $convert__($sizenn1($numtype_addrtype(I64_Inn)), $sizenn2($numtype_Fnn(F32_Fnn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_18{v_sx : sx, i_1 : uN}:
    `%%%%%`(I32_numtype, F64_numtype, mk_cvtop___1_cvtop__(I32_Inn, F64_Fnn, CONVERT_cvtop__Inn_1_Fnn_2(v_sx)), mk_num__0_num_(I32_Inn, i_1), [mk_num__1_num_(F64_Fnn, $convert__($sizenn1($numtype_addrtype(I32_Inn)), $sizenn2($numtype_Fnn(F64_Fnn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_19{v_sx : sx, i_1 : uN}:
    `%%%%%`(I64_numtype, F64_numtype, mk_cvtop___1_cvtop__(I64_Inn, F64_Fnn, CONVERT_cvtop__Inn_1_Fnn_2(v_sx)), mk_num__0_num_(I64_Inn, i_1), [mk_num__1_num_(F64_Fnn, $convert__($sizenn1($numtype_addrtype(I64_Inn)), $sizenn2($numtype_Fnn(F64_Fnn)), v_sx, i_1))])

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_20{f_1 : fN}:
    `%%%%%`(F32_numtype, F32_numtype, mk_cvtop___3_cvtop__(F32_Fnn, F32_Fnn, PROMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, iter_0_41)*{iter_0_41 <- $promote__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_Fnn(F32_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_21{f_1 : fN}:
    `%%%%%`(F64_numtype, F32_numtype, mk_cvtop___3_cvtop__(F64_Fnn, F32_Fnn, PROMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F32_Fnn, iter_0_42)*{iter_0_42 <- $promote__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_Fnn(F32_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_22{f_1 : fN}:
    `%%%%%`(F32_numtype, F64_numtype, mk_cvtop___3_cvtop__(F32_Fnn, F64_Fnn, PROMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F64_Fnn, iter_0_43)*{iter_0_43 <- $promote__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_Fnn(F64_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_23{f_1 : fN}:
    `%%%%%`(F64_numtype, F64_numtype, mk_cvtop___3_cvtop__(F64_Fnn, F64_Fnn, PROMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, iter_0_44)*{iter_0_44 <- $promote__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_Fnn(F64_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_24{f_1 : fN}:
    `%%%%%`(F32_numtype, F32_numtype, mk_cvtop___3_cvtop__(F32_Fnn, F32_Fnn, DEMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F32_Fnn, iter_0_45)*{iter_0_45 <- $demote__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_Fnn(F32_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_25{f_1 : fN}:
    `%%%%%`(F64_numtype, F32_numtype, mk_cvtop___3_cvtop__(F64_Fnn, F32_Fnn, DEMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F32_Fnn, iter_0_46)*{iter_0_46 <- $demote__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_Fnn(F32_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_26{f_1 : fN}:
    `%%%%%`(F32_numtype, F64_numtype, mk_cvtop___3_cvtop__(F32_Fnn, F64_Fnn, DEMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F32_Fnn, f_1), mk_num__1_num_(F64_Fnn, iter_0_47)*{iter_0_47 <- $demote__($sizenn1($numtype_Fnn(F32_Fnn)), $sizenn2($numtype_Fnn(F64_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_27{f_1 : fN}:
    `%%%%%`(F64_numtype, F64_numtype, mk_cvtop___3_cvtop__(F64_Fnn, F64_Fnn, DEMOTE_cvtop__Fnn_1_Fnn_2), mk_num__1_num_(F64_Fnn, f_1), mk_num__1_num_(F64_Fnn, iter_0_48)*{iter_0_48 <- $demote__($sizenn1($numtype_Fnn(F64_Fnn)), $sizenn2($numtype_Fnn(F64_Fnn)), f_1)})

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_28{i_1 : uN}:
    `%%%%%`(I32_numtype, F32_numtype, mk_cvtop___1_cvtop__(I32_Inn, F32_Fnn, REINTERPRET_cvtop__Inn_1_Fnn_2), mk_num__0_num_(I32_Inn, i_1), [$reinterpret__($numtype_addrtype(I32_Inn), $numtype_Fnn(F32_Fnn), mk_num__0_num_(I32_Inn, i_1))])
    -- if ($size($numtype_addrtype(I32_Inn)) = $size($numtype_Fnn(F32_Fnn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_29{i_1 : uN}:
    `%%%%%`(I64_numtype, F32_numtype, mk_cvtop___1_cvtop__(I64_Inn, F32_Fnn, REINTERPRET_cvtop__Inn_1_Fnn_2), mk_num__0_num_(I64_Inn, i_1), [$reinterpret__($numtype_addrtype(I64_Inn), $numtype_Fnn(F32_Fnn), mk_num__0_num_(I64_Inn, i_1))])
    -- if ($size($numtype_addrtype(I64_Inn)) = $size($numtype_Fnn(F32_Fnn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_30{i_1 : uN}:
    `%%%%%`(I32_numtype, F64_numtype, mk_cvtop___1_cvtop__(I32_Inn, F64_Fnn, REINTERPRET_cvtop__Inn_1_Fnn_2), mk_num__0_num_(I32_Inn, i_1), [$reinterpret__($numtype_addrtype(I32_Inn), $numtype_Fnn(F64_Fnn), mk_num__0_num_(I32_Inn, i_1))])
    -- if ($size($numtype_addrtype(I32_Inn)) = $size($numtype_Fnn(F64_Fnn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_31{i_1 : uN}:
    `%%%%%`(I64_numtype, F64_numtype, mk_cvtop___1_cvtop__(I64_Inn, F64_Fnn, REINTERPRET_cvtop__Inn_1_Fnn_2), mk_num__0_num_(I64_Inn, i_1), [$reinterpret__($numtype_addrtype(I64_Inn), $numtype_Fnn(F64_Fnn), mk_num__0_num_(I64_Inn, i_1))])
    -- if ($size($numtype_addrtype(I64_Inn)) = $size($numtype_Fnn(F64_Fnn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_32{f_1 : fN}:
    `%%%%%`(F32_numtype, I32_numtype, mk_cvtop___2_cvtop__(F32_Fnn, I32_Inn, REINTERPRET_cvtop__Fnn_1_Inn_2), mk_num__1_num_(F32_Fnn, f_1), [$reinterpret__($numtype_Fnn(F32_Fnn), $numtype_addrtype(I32_Inn), mk_num__1_num_(F32_Fnn, f_1))])
    -- if ($size($numtype_Fnn(F32_Fnn)) = $size($numtype_addrtype(I32_Inn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_33{f_1 : fN}:
    `%%%%%`(F64_numtype, I32_numtype, mk_cvtop___2_cvtop__(F64_Fnn, I32_Inn, REINTERPRET_cvtop__Fnn_1_Inn_2), mk_num__1_num_(F64_Fnn, f_1), [$reinterpret__($numtype_Fnn(F64_Fnn), $numtype_addrtype(I32_Inn), mk_num__1_num_(F64_Fnn, f_1))])
    -- if ($size($numtype_Fnn(F64_Fnn)) = $size($numtype_addrtype(I32_Inn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_34{f_1 : fN}:
    `%%%%%`(F32_numtype, I64_numtype, mk_cvtop___2_cvtop__(F32_Fnn, I64_Inn, REINTERPRET_cvtop__Fnn_1_Inn_2), mk_num__1_num_(F32_Fnn, f_1), [$reinterpret__($numtype_Fnn(F32_Fnn), $numtype_addrtype(I64_Inn), mk_num__1_num_(F32_Fnn, f_1))])
    -- if ($size($numtype_Fnn(F32_Fnn)) = $size($numtype_addrtype(I64_Inn)))

  ;; test.spectec:3606.6-3606.14
  rule fun_cvtop___case_35{f_1 : fN}:
    `%%%%%`(F64_numtype, I64_numtype, mk_cvtop___2_cvtop__(F64_Fnn, I64_Inn, REINTERPRET_cvtop__Fnn_1_Inn_2), mk_num__1_num_(F64_Fnn, f_1), [$reinterpret__($numtype_Fnn(F64_Fnn), $numtype_addrtype(I64_Inn), mk_num__1_num_(F64_Fnn, f_1))])
    -- if ($size($numtype_Fnn(F64_Fnn)) = $size($numtype_addrtype(I64_Inn)))

;; test.spectec:3606.6-3606.14
relation cvtop___is_wf: `%%%%%`(numtype_1 : numtype, numtype_2 : numtype, v_cvtop__ : cvtop__, v_num_ : num_, ret_val_lst : num_*)
  ;; test.spectec:3606.6-3606.14
  rule cvtop___is_wf_0{numtype_1 : numtype, numtype_2 : numtype, v_cvtop__ : cvtop__, v_num_ : num_, ret_val_lst : num_*, var_0 : num_*}:
    `%%%%%`(numtype_1, numtype_2, v_cvtop__, v_num_, ret_val_lst)
    -- fun_cvtop__: `%%%%%`(numtype_1, numtype_2, v_cvtop__, v_num_, var_0)
    -- wf_cvtop__: `%%%`(numtype_1, numtype_2, v_cvtop__)
    -- wf_num_: `%%`(numtype_1, v_num_)
    -- if (ret_val_lst = var_0)
    -- (wf_num_: `%%`(numtype_2, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3694.1-3694.84
def $lanes_(v_shape : shape, v_vec_ : vec_) : lane_*

;; test.spectec:3694.6-3694.13
relation lanes__is_wf: `%%%`(v_shape : shape, v_vec_ : vec_, ret_val_lst : lane_*)
  ;; test.spectec:3694.6-3694.13
  rule lanes__is_wf_0{v_shape : shape, v_vec_ : vec_, ret_val_lst : lane_*}:
    `%%%`(v_shape, v_vec_, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val_lst = $lanes_(v_shape, v_vec_))
    -- (wf_lane_: `%%`($fun_lanetype(v_shape), ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3696.1-3697.37
def $inv_lanes_(v_shape : shape, var_0_lst : lane_*) : vec_

;; test.spectec:3696.6-3696.17
relation inv_lanes__is_wf: `%%%`(v_shape : shape, var_0_lst : lane_*, ret_val : vec_)
  ;; test.spectec:3696.6-3696.17
  rule inv_lanes__is_wf_0{v_shape : shape, var_0_lst : lane_*, ret_val : vec_}:
    `%%%`(v_shape, var_0_lst, ret_val)
    -- wf_shape: `%`(v_shape)
    -- (wf_lane_: `%%`($fun_lanetype(v_shape), var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_lanes_(v_shape, var_0_lst))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3703.6-3703.13
relation fun_zeroop: `%%%%`(shape, shape, vcvtop__, zero?)
  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_0{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_1{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_2{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_3{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_4{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_5{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_6{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_7{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_8{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_9{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_10{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_11{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_12{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_13{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_14{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_15{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_16{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I32_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_17{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I64_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_18{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I8_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_19{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I16_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_20{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I32_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_21{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I64_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_22{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I8_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_23{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I16_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_24{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I32_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_25{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I32_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_26{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I64_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_27{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I64_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_28{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I8_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_29{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I8_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_30{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I16_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_31{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I16_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_32{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I32_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_33{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I32_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_34{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I64_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_35{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I64_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_36{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I8_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_37{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I8_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_38{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I16_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_39{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I16_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), zero_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_40{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F32_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?(v_zero))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_41{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F32_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?(v_zero))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_42{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F64_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?(v_zero))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_43{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F64_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?(v_zero))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_44{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F32_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_45{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F32_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_46{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F64_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3703.6-3703.13
  rule fun_zeroop_case_47{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F64_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

;; test.spectec:3711.6-3711.13
relation fun_halfop: `%%%%`(shape, shape, vcvtop__, half?)
  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_0{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_1{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_2{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_3{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_4{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_5{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_6{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_7{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_8{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_9{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_10{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_11{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_12{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_13{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_14{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_15{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), ?(v_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_16{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I32_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_17{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I64_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_18{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I8_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_19{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I16_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_20{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I32_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_21{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I64_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_22{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I8_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_23{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I16_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), half_opt)
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_24{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I32_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_25{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I32_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_26{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I64_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_27{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I64_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_28{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I8_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_29{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I8_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_30{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I16_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_31{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I16_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_32{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I32_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_33{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I32_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_34{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I64_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_35{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I64_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_36{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I8_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_37{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I8_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_38{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I16_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_39{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I16_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_40{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F32_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_41{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F32_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_42{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F64_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_43{M_1 : nat, M_2 : nat, v_zero : zero, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F64_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(v_zero)), ?())
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_44{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F32_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?(LOW_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_45{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F32_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?(LOW_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_46{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F64_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?(LOW_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3711.6-3711.13
  rule fun_halfop_case_47{M_1 : nat, M_2 : nat, M_1_0 : nat, M_2_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F64_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), ?(LOW_half))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

;; test.spectec:3719.1-3719.32
def $fun_half(v_half : half, nat : nat, nat_0 : nat) : nat
  ;; test.spectec:3720.1-3720.25
  def $fun_half{i : nat, j : nat}(LOW_half, i, j) = i
  ;; test.spectec:3721.1-3721.26
  def $fun_half{i : nat, j : nat}(HIGH_half, i, j) = j

;; test.spectec:3724.1-3724.46
def $iswizzle_lane_(v_N : N, var_0_lst : iN*, v_iN : iN) : iN
  ;; test.spectec:3727.1-3727.62
  def $iswizzle_lane_{v_N : nat, c_lst : iN*, i : uN}(v_N, c_lst, i) = (if ($proj_uN_0(i).0 < |c_lst|) then c_lst[$proj_uN_0(i).0] else mk_uN_iN(0))

;; test.spectec:3724.6-3724.21
relation iswizzle_lane__is_wf: `%%%%`(v_N : N, var_0_lst : iN*, v_iN : iN, ret_val : iN)
  ;; test.spectec:3724.6-3724.21
  rule iswizzle_lane__is_wf_0{v_N : N, var_0_lst : iN*, v_iN : iN, ret_val : iN}:
    `%%%%`(v_N, var_0_lst, v_iN, ret_val)
    -- (wf_uN: `%%`(v_N, var_0))*{var_0 <- var_0_lst}
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $iswizzle_lane_(v_N, var_0_lst, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3725.1-3725.54
def $irelaxed_swizzle_lane_(v_N : N, var_0_lst : iN*, v_iN : iN) : iN
  ;; test.spectec:3730.1-3730.62
  def $irelaxed_swizzle_lane_{v_N : nat, c_lst : iN*, i : uN, var_0 : int}(v_N, c_lst, i) = (if ($proj_uN_0(i).0 < |c_lst|) then c_lst[$proj_uN_0(i).0] else (if (var_0 < (0 : nat <:> int)) then mk_uN_iN(0) else $fun_relaxed2($R_swizzle, syntax iN, mk_uN_iN(0), c_lst[($proj_uN_0(i).0 \ |c_lst|)])))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i).0, var_0)

;; test.spectec:3725.6-3725.29
relation irelaxed_swizzle_lane__is_wf: `%%%%`(v_N : N, var_0_lst : iN*, v_iN : iN, ret_val : iN)
  ;; test.spectec:3725.6-3725.29
  rule irelaxed_swizzle_lane__is_wf_0{v_N : N, var_0_lst : iN*, v_iN : iN, ret_val : iN}:
    `%%%%`(v_N, var_0_lst, v_iN, ret_val)
    -- (wf_uN: `%%`(v_N, var_0))*{var_0 <- var_0_lst}
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $irelaxed_swizzle_lane_(v_N, var_0_lst, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:3738.1-3738.87
def $ivunop_(v_shape : shape, def $f_(v_N : N, v_iN : iN) : iN, v_vec_ : vec_) : vec_*?
  ;; test.spectec:3761.1-3763.40
  def $ivunop_{v_M : nat, def $f_(v_N : N, v_iN : iN) : iN, v_1 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_1) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_4)*{c_4 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_2)))*{c_1_2 <- c_1_lst}
  ;; test.spectec:3761.1-3763.40
  def $ivunop_{v_M : nat, def $f_(v_N : N, v_iN : iN) : iN, v_1 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_1) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_6)*{c_6 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_4)))*{c_1_4 <- c_1_lst}
  ;; test.spectec:3761.1-3763.40
  def $ivunop_{v_M : nat, def $f_(v_N : N, v_iN : iN) : iN, v_1 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_1) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_8)*{c_8 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_6)))*{c_1_6 <- c_1_lst}
  ;; test.spectec:3761.1-3763.40
  def $ivunop_{v_M : nat, def $f_(v_N : N, v_iN : iN) : iN, v_1 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_1) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_10)*{c_10 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_8)))*{c_1_8 <- c_1_lst}
  def $ivunop_{x0 : shape, x2 : vec_}(x0, def $f_, x2) = ?()
    -- otherwise

;; test.spectec:3738.6-3738.14
relation ivunop__is_wf(def $f_(v_N : N, v_iN : iN) : iN): `%%%`(v_shape : shape, v_vec_ : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3738.6-3738.14
  rule ivunop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_iN : iN) : iN, v_vec_ : vec_, ret_val_lst : vec_*}:
    `%%%`(v_shape, v_vec_, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- if ($ivunop_(v_shape, def $f_, v_vec_) =/= ?())
    -- if (ret_val_lst = !($ivunop_(v_shape, def $f_, v_vec_)))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3739.1-3739.74
def $fvunop_(v_shape : shape, def $f_(v_N : N, v_fN : fN) : fN*, v_vec_ : vec_) : vec_*
  ;; test.spectec:3765.1-3767.66
  def $fvunop_{v_M : nat, def $f_(v_N : N, v_fN : fN) : fN*, v_1 : uN}(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), def $f_, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), c_lst_2)*{c_lst_2 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, iter_0_49))*{iter_0_49 <- $f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_10)))))}*{c_1_10 <- c_1_lst})
    -- (wf_lane_: `%%`($lanetype_Fnn(F32_Fnn), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, iter_0_50))))*{iter_0_50 <- $f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_11)))))}*{c_1_11 <- c_1_lst}
  ;; test.spectec:3765.1-3767.66
  def $fvunop_{v_M : nat, def $f_(v_N : N, v_fN : fN) : fN*, v_1 : uN}(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), def $f_, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), c_lst_4)*{c_lst_4 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, iter_0_51))*{iter_0_51 <- $f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_13)))))}*{c_1_13 <- c_1_lst})
    -- (wf_lane_: `%%`($lanetype_Fnn(F64_Fnn), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, iter_0_52))))*{iter_0_52 <- $f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_14)))))}*{c_1_14 <- c_1_lst}

;; test.spectec:3739.6-3739.14
relation fvunop__is_wf(def $f_(v_N : N, v_fN : fN) : fN*): `%%%`(v_shape : shape, v_vec_ : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3739.6-3739.14
  rule fvunop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_fN : fN) : fN*, v_vec_ : vec_, ret_val_lst : vec_*}:
    `%%%`(v_shape, v_vec_, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val_lst = $fvunop_(v_shape, def $f_, v_vec_))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3741.1-3741.107
def $ivbinop_(v_shape : shape, def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN, v_vec_ : vec_, vec__0 : vec_) : vec_*?
  ;; test.spectec:3770.1-3773.45
  def $ivbinop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_16)*{c_16 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_16)), !($proj_lane__2(c_2_2)))*{c_1_16 <- c_1_lst, c_2_2 <- c_2_lst}
  ;; test.spectec:3770.1-3773.45
  def $ivbinop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_18)*{c_18 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_18)), !($proj_lane__2(c_2_4)))*{c_1_18 <- c_1_lst, c_2_4 <- c_2_lst}
  ;; test.spectec:3770.1-3773.45
  def $ivbinop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_20)*{c_20 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_20)), !($proj_lane__2(c_2_6)))*{c_1_20 <- c_1_lst, c_2_6 <- c_2_lst}
  ;; test.spectec:3770.1-3773.45
  def $ivbinop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_22)*{c_22 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_22)), !($proj_lane__2(c_2_8)))*{c_1_22 <- c_1_lst, c_2_8 <- c_2_lst}
  def $ivbinop_{x0 : shape, x2 : vec_, x3 : vec_}(x0, def $f_, x2, x3) = ?()
    -- otherwise

;; test.spectec:3741.6-3741.15
relation ivbinop__is_wf(def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN): `%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3741.6-3741.15
  rule ivbinop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_iN : iN, v_iN : iN) : iN, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*}:
    `%%%%`(v_shape, v_vec_, vec__0, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if ($ivbinop_(v_shape, def $f_, v_vec_, vec__0) =/= ?())
    -- if (ret_val_lst = !($ivbinop_(v_shape, def $f_, v_vec_, vec__0)))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3742.1-3742.117
def $ivbinopsx_(v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN, v_sx : sx, v_vec_ : vec_, vec__0 : vec_) : vec_*?
  ;; test.spectec:3775.1-3778.49
  def $ivbinopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_24)*{c_24 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_24)), !($proj_lane__2(c_2_10)))*{c_1_24 <- c_1_lst, c_2_10 <- c_2_lst}
  ;; test.spectec:3775.1-3778.49
  def $ivbinopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_26)*{c_26 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_26)), !($proj_lane__2(c_2_12)))*{c_1_26 <- c_1_lst, c_2_12 <- c_2_lst}
  ;; test.spectec:3775.1-3778.49
  def $ivbinopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_28)*{c_28 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_28)), !($proj_lane__2(c_2_14)))*{c_1_28 <- c_1_lst, c_2_14 <- c_2_lst}
  ;; test.spectec:3775.1-3778.49
  def $ivbinopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = ?([$inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_30)*{c_30 <- c_lst})])
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_30)), !($proj_lane__2(c_2_16)))*{c_1_30 <- c_1_lst, c_2_16 <- c_2_lst}
  def $ivbinopsx_{x0 : shape, x2 : sx, x3 : vec_, x4 : vec_}(x0, def $f_, x2, x3, x4) = ?()
    -- otherwise

;; test.spectec:3742.6-3742.17
relation ivbinopsx__is_wf(def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN): `%%%%%`(v_shape : shape, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3742.6-3742.17
  rule ivbinopsx__is_wf_0{v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*}:
    `%%%%%`(v_shape, v_sx, v_vec_, vec__0, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if ($ivbinopsx_(v_shape, def $f_, v_sx, v_vec_, vec__0) =/= ?())
    -- if (ret_val_lst = !($ivbinopsx_(v_shape, def $f_, v_sx, v_vec_, vec__0)))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3743.1-3743.106
def $ivbinopsxnd_(v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*, v_sx : sx, v_vec_ : vec_, vec__0 : vec_) : vec_*
  ;; test.spectec:3780.1-3783.76
  def $ivbinopsxnd_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), c_lst_6)*{c_lst_6 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I32_Jnn, iter_0_53)*{iter_0_53 <- $f_($lsizenn($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_32)), !($proj_lane__2(c_2_18)))}*{c_1_32 <- c_1_lst, c_2_18 <- c_2_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I32_Jnn), mk_lane__2_lane_(I32_Jnn, iter_0_54)))*{iter_0_54 <- $f_($lsizenn($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_33)), !($proj_lane__2(c_2_19)))}*{c_1_33 <- c_1_lst, c_2_19 <- c_2_lst}
  ;; test.spectec:3780.1-3783.76
  def $ivbinopsxnd_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), c_lst_8)*{c_lst_8 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I64_Jnn, iter_0_55)*{iter_0_55 <- $f_($lsizenn($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_35)), !($proj_lane__2(c_2_21)))}*{c_1_35 <- c_1_lst, c_2_21 <- c_2_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I64_Jnn), mk_lane__2_lane_(I64_Jnn, iter_0_56)))*{iter_0_56 <- $f_($lsizenn($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_36)), !($proj_lane__2(c_2_22)))}*{c_1_36 <- c_1_lst, c_2_22 <- c_2_lst}
  ;; test.spectec:3780.1-3783.76
  def $ivbinopsxnd_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), c_lst_10)*{c_lst_10 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I8_Jnn, iter_0_57)*{iter_0_57 <- $f_($lsizenn($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_38)), !($proj_lane__2(c_2_24)))}*{c_1_38 <- c_1_lst, c_2_24 <- c_2_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I8_Jnn), mk_lane__2_lane_(I8_Jnn, iter_0_58)))*{iter_0_58 <- $f_($lsizenn($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_39)), !($proj_lane__2(c_2_25)))}*{c_1_39 <- c_1_lst, c_2_25 <- c_2_lst}
  ;; test.spectec:3780.1-3783.76
  def $ivbinopsxnd_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), c_lst_12)*{c_lst_12 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I16_Jnn, iter_0_59)*{iter_0_59 <- $f_($lsizenn($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_41)), !($proj_lane__2(c_2_27)))}*{c_1_41 <- c_1_lst, c_2_27 <- c_2_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I16_Jnn), mk_lane__2_lane_(I16_Jnn, iter_0_60)))*{iter_0_60 <- $f_($lsizenn($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_42)), !($proj_lane__2(c_2_28)))}*{c_1_42 <- c_1_lst, c_2_28 <- c_2_lst}

;; test.spectec:3743.6-3743.19
relation ivbinopsxnd__is_wf(def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*): `%%%%%`(v_shape : shape, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3743.6-3743.19
  rule ivbinopsxnd__is_wf_0{v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : iN*, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*}:
    `%%%%%`(v_shape, v_sx, v_vec_, vec__0, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val_lst = $ivbinopsxnd_(v_shape, def $f_, v_sx, v_vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3744.1-3744.94
def $fvbinop_(v_shape : shape, def $f_(v_N : N, v_fN : fN, v_fN : fN) : fN*, v_vec_ : vec_, vec__0 : vec_) : vec_*
  ;; test.spectec:3785.1-3788.71
  def $fvbinop_{v_M : nat, def $f_(v_N : N, v_fN : fN, v_fN : fN) : fN*, v_1 : uN, v_2 : uN}(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), c_lst_14)*{c_lst_14 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, iter_0_61))*{iter_0_61 <- $f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_44)))), !($proj_num__1(!($proj_lane__0(c_2_30)))))}*{c_1_44 <- c_1_lst, c_2_30 <- c_2_lst})
    -- (wf_lane_: `%%`($lanetype_Fnn(F32_Fnn), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, iter_0_62))))*{iter_0_62 <- $f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_45)))), !($proj_num__1(!($proj_lane__0(c_2_31)))))}*{c_1_45 <- c_1_lst, c_2_31 <- c_2_lst}
  ;; test.spectec:3785.1-3788.71
  def $fvbinop_{v_M : nat, def $f_(v_N : N, v_fN : fN, v_fN : fN) : fN*, v_1 : uN, v_2 : uN}(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), c_lst_16)*{c_lst_16 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, iter_0_63))*{iter_0_63 <- $f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_47)))), !($proj_num__1(!($proj_lane__0(c_2_33)))))}*{c_1_47 <- c_1_lst, c_2_33 <- c_2_lst})
    -- (wf_lane_: `%%`($lanetype_Fnn(F64_Fnn), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, iter_0_64))))*{iter_0_64 <- $f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_48)))), !($proj_num__1(!($proj_lane__0(c_2_34)))))}*{c_1_48 <- c_1_lst, c_2_34 <- c_2_lst}

;; test.spectec:3744.6-3744.15
relation fvbinop__is_wf(def $f_(v_N : N, v_fN : fN, v_fN : fN) : fN*): `%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3744.6-3744.15
  rule fvbinop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_fN : fN, v_fN : fN) : fN*, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*}:
    `%%%%`(v_shape, v_vec_, vec__0, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val_lst = $fvbinop_(v_shape, def $f_, v_vec_, vec__0))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3746.1-3746.116
def $ivternopnd_(v_shape : shape, def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_) : vec_*
  ;; test.spectec:3791.1-3795.77
  def $ivternopnd_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*, v_1 : uN, v_2 : uN, v_3 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), c_lst_18)*{c_lst_18 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_3_lst : lane_*} c_3_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_3)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I32_Jnn, iter_0_65)*{iter_0_65 <- $f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_50)), !($proj_lane__2(c_2_36)), !($proj_lane__2(c_3_2)))}*{c_1_50 <- c_1_lst, c_2_36 <- c_2_lst, c_3_2 <- c_3_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I32_Jnn), mk_lane__2_lane_(I32_Jnn, iter_0_66)))*{iter_0_66 <- $f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_51)), !($proj_lane__2(c_2_37)), !($proj_lane__2(c_3_3)))}*{c_1_51 <- c_1_lst, c_2_37 <- c_2_lst, c_3_3 <- c_3_lst}
  ;; test.spectec:3791.1-3795.77
  def $ivternopnd_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*, v_1 : uN, v_2 : uN, v_3 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), c_lst_20)*{c_lst_20 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_3_lst : lane_*} c_3_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_3)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I64_Jnn, iter_0_67)*{iter_0_67 <- $f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_53)), !($proj_lane__2(c_2_39)), !($proj_lane__2(c_3_5)))}*{c_1_53 <- c_1_lst, c_2_39 <- c_2_lst, c_3_5 <- c_3_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I64_Jnn), mk_lane__2_lane_(I64_Jnn, iter_0_68)))*{iter_0_68 <- $f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_54)), !($proj_lane__2(c_2_40)), !($proj_lane__2(c_3_6)))}*{c_1_54 <- c_1_lst, c_2_40 <- c_2_lst, c_3_6 <- c_3_lst}
  ;; test.spectec:3791.1-3795.77
  def $ivternopnd_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*, v_1 : uN, v_2 : uN, v_3 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), c_lst_22)*{c_lst_22 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_3_lst : lane_*} c_3_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_3)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I8_Jnn, iter_0_69)*{iter_0_69 <- $f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_56)), !($proj_lane__2(c_2_42)), !($proj_lane__2(c_3_8)))}*{c_1_56 <- c_1_lst, c_2_42 <- c_2_lst, c_3_8 <- c_3_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I8_Jnn), mk_lane__2_lane_(I8_Jnn, iter_0_70)))*{iter_0_70 <- $f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_57)), !($proj_lane__2(c_2_43)), !($proj_lane__2(c_3_9)))}*{c_1_57 <- c_1_lst, c_2_43 <- c_2_lst, c_3_9 <- c_3_lst}
  ;; test.spectec:3791.1-3795.77
  def $ivternopnd_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*, v_1 : uN, v_2 : uN, v_3 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), c_lst_24)*{c_lst_24 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_3_lst : lane_*} c_3_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_3)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__2_lane_(I16_Jnn, iter_0_71)*{iter_0_71 <- $f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_59)), !($proj_lane__2(c_2_45)), !($proj_lane__2(c_3_11)))}*{c_1_59 <- c_1_lst, c_2_45 <- c_2_lst, c_3_11 <- c_3_lst})
    -- (wf_lane_: `%%`($lanetype_Jnn(I16_Jnn), mk_lane__2_lane_(I16_Jnn, iter_0_72)))*{iter_0_72 <- $f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_60)), !($proj_lane__2(c_2_46)), !($proj_lane__2(c_3_12)))}*{c_1_60 <- c_1_lst, c_2_46 <- c_2_lst, c_3_12 <- c_3_lst}

;; test.spectec:3746.6-3746.18
relation ivternopnd__is_wf(def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*): `%%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3746.6-3746.18
  rule ivternopnd__is_wf_0{v_shape : shape, def $f_(v_N : N, v_iN : iN, v_iN : iN, v_iN : iN) : iN*, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*}:
    `%%%%%`(v_shape, v_vec_, vec__0, vec__1, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (ret_val_lst = $ivternopnd_(v_shape, def $f_, v_vec_, vec__0, vec__1))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3747.1-3747.114
def $fvternop_(v_shape : shape, def $f_(v_N : N, v_fN : fN, v_fN : fN, v_fN : fN) : fN*, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_) : vec_*
  ;; test.spectec:3797.1-3801.76
  def $fvternop_{v_M : nat, def $f_(v_N : N, v_fN : fN, v_fN : fN, v_fN : fN) : fN*, v_1 : uN, v_2 : uN, v_3 : uN}(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), c_lst_26)*{c_lst_26 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_2)
    -- let{c_3_lst : lane_*} c_3_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_3)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, iter_0_73))*{iter_0_73 <- $f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_62)))), !($proj_num__1(!($proj_lane__0(c_2_48)))), !($proj_num__1(!($proj_lane__0(c_3_14)))))}*{c_1_62 <- c_1_lst, c_2_48 <- c_2_lst, c_3_14 <- c_3_lst})
    -- (wf_lane_: `%%`($lanetype_Fnn(F32_Fnn), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, iter_0_74))))*{iter_0_74 <- $f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_63)))), !($proj_num__1(!($proj_lane__0(c_2_49)))), !($proj_num__1(!($proj_lane__0(c_3_15)))))}*{c_1_63 <- c_1_lst, c_2_49 <- c_2_lst, c_3_15 <- c_3_lst}
  ;; test.spectec:3797.1-3801.76
  def $fvternop_{v_M : nat, def $f_(v_N : N, v_fN : fN, v_fN : fN, v_fN : fN) : fN*, v_1 : uN, v_2 : uN, v_3 : uN}(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), c_lst_28)*{c_lst_28 <- c_lst_lst}
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_2)
    -- let{c_3_lst : lane_*} c_3_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_3)
    -- let{c_lst_lst : lane_**} c_lst_lst = $setproduct_(syntax lane_, mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, iter_0_75))*{iter_0_75 <- $f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_65)))), !($proj_num__1(!($proj_lane__0(c_2_51)))), !($proj_num__1(!($proj_lane__0(c_3_17)))))}*{c_1_65 <- c_1_lst, c_2_51 <- c_2_lst, c_3_17 <- c_3_lst})
    -- (wf_lane_: `%%`($lanetype_Fnn(F64_Fnn), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, iter_0_76))))*{iter_0_76 <- $f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_66)))), !($proj_num__1(!($proj_lane__0(c_2_52)))), !($proj_num__1(!($proj_lane__0(c_3_18)))))}*{c_1_66 <- c_1_lst, c_2_52 <- c_2_lst, c_3_18 <- c_3_lst}

;; test.spectec:3747.6-3747.16
relation fvternop__is_wf(def $f_(v_N : N, v_fN : fN, v_fN : fN, v_fN : fN) : fN*): `%%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3747.6-3747.16
  rule fvternop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_fN : fN, v_fN : fN, v_fN : fN) : fN*, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*}:
    `%%%%%`(v_shape, v_vec_, vec__0, vec__1, ret_val_lst)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (ret_val_lst = $fvternop_(v_shape, def $f_, v_vec_, vec__0, vec__1))
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3749.1-3749.90
def $ivrelop_(v_shape : shape, def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32, v_vec_ : vec_, vec__0 : vec_) : vec_
  ;; test.spectec:3804.1-3807.77
  def $ivrelop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_56)*{c_56 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I32_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_68)), !($proj_lane__2(c_2_54)))).0))*{c_1_68 <- c_1_lst, c_2_54 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_69)), !($proj_lane__2(c_2_55)))).0)))*{c_1_69 <- c_1_lst, c_2_55 <- c_2_lst}
  ;; test.spectec:3804.1-3807.77
  def $ivrelop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_58)*{c_58 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I64_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_71)), !($proj_lane__2(c_2_57)))).0))*{c_1_71 <- c_1_lst, c_2_57 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_72)), !($proj_lane__2(c_2_58)))).0)))*{c_1_72 <- c_1_lst, c_2_58 <- c_2_lst}
  ;; test.spectec:3804.1-3807.77
  def $ivrelop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_60)*{c_60 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I8_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_74)), !($proj_lane__2(c_2_60)))).0))*{c_1_74 <- c_1_lst, c_2_60 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_75)), !($proj_lane__2(c_2_61)))).0)))*{c_1_75 <- c_1_lst, c_2_61 <- c_2_lst}
  ;; test.spectec:3804.1-3807.77
  def $ivrelop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_62)*{c_62 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I16_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_77)), !($proj_lane__2(c_2_63)))).0))*{c_1_77 <- c_1_lst, c_2_63 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_78)), !($proj_lane__2(c_2_64)))).0)))*{c_1_78 <- c_1_lst, c_2_64 <- c_2_lst}

;; test.spectec:3749.6-3749.15
relation ivrelop__is_wf(def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32): `%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3749.6-3749.15
  rule ivrelop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_iN : iN, v_iN : iN) : u32, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%`(v_shape, v_vec_, vec__0, ret_val)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivrelop_(v_shape, def $f_, v_vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3750.1-3750.100
def $ivrelopsx_(v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32, v_sx : sx, v_vec_ : vec_, vec__0 : vec_) : vec_
  ;; test.spectec:3809.1-3812.81
  def $ivrelopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_64)*{c_64 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I32_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_80)), !($proj_lane__2(c_2_66)))).0))*{c_1_80 <- c_1_lst, c_2_66 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_81)), !($proj_lane__2(c_2_67)))).0)))*{c_1_81 <- c_1_lst, c_2_67 <- c_2_lst}
  ;; test.spectec:3809.1-3812.81
  def $ivrelopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_66)*{c_66 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I64_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_83)), !($proj_lane__2(c_2_69)))).0))*{c_1_83 <- c_1_lst, c_2_69 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_84)), !($proj_lane__2(c_2_70)))).0)))*{c_1_84 <- c_1_lst, c_2_70 <- c_2_lst}
  ;; test.spectec:3809.1-3812.81
  def $ivrelopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_68)*{c_68 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I8_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_86)), !($proj_lane__2(c_2_72)))).0))*{c_1_86 <- c_1_lst, c_2_72 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_87)), !($proj_lane__2(c_2_73)))).0)))*{c_1_87 <- c_1_lst, c_2_73 <- c_2_lst}
  ;; test.spectec:3809.1-3812.81
  def $ivrelopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32, v_sx : sx, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_70)*{c_70 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $lsizenn($lanetype_Jnn(I16_Jnn)), S_sx, mk_uN_iN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_89)), !($proj_lane__2(c_2_75)))).0))*{c_1_89 <- c_1_lst, c_2_75 <- c_2_lst}
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($lsizenn($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_90)), !($proj_lane__2(c_2_76)))).0)))*{c_1_90 <- c_1_lst, c_2_76 <- c_2_lst}

;; test.spectec:3750.6-3750.17
relation ivrelopsx__is_wf(def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32): `%%%%%`(v_shape : shape, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3750.6-3750.17
  rule ivrelopsx__is_wf_0{v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_iN : iN) : u32, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%%`(v_shape, v_sx, v_vec_, vec__0, ret_val)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivrelopsx_(v_shape, def $f_, v_sx, v_vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3751.1-3751.90
def $fvrelop_(v_shape : shape, def $f_(v_N : N, v_fN : fN, v_fN : fN) : u32, v_vec_ : vec_, vec__0 : vec_) : vec_
  ;; test.spectec:3814.1-3818.36
  def $fvrelop_{v_M : nat, def $f_(v_N : N, v_fN : fN, v_fN : fN) : u32, v_1 : uN, v_2 : uN, v_Inn : addrtype}(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_addrtype(v_Inn), mk_dim_dim(v_M)), mk_lane__0_lane_($numtype_addrtype(v_Inn), mk_num__0_num_(v_Inn, mk_uN_uN($proj_uN_0(c_72).0)))*{c_72 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $sizenn($numtype_Fnn(F32_Fnn)), S_sx, mk_uN_iN($proj_uN_0($f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_92)))), !($proj_num__1(!($proj_lane__0(c_2_78)))))).0))*{c_1_92 <- c_1_lst, c_2_78 <- c_2_lst}
    -- if ($isize(v_Inn) = $fsize(F32_Fnn))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)))
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($sizenn($numtype_Fnn(F32_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_93)))), !($proj_num__1(!($proj_lane__0(c_2_79)))))).0)))*{c_1_93 <- c_1_lst, c_2_79 <- c_2_lst}
  ;; test.spectec:3814.1-3818.36
  def $fvrelop_{v_M : nat, def $f_(v_N : N, v_fN : fN, v_fN : fN) : u32, v_1 : uN, v_2 : uN, v_Inn : addrtype}(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_addrtype(v_Inn), mk_dim_dim(v_M)), mk_lane__0_lane_($numtype_addrtype(v_Inn), mk_num__0_num_(v_Inn, mk_uN_uN($proj_uN_0(c_74).0)))*{c_74 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $extend__(1, $sizenn($numtype_Fnn(F64_Fnn)), S_sx, mk_uN_iN($proj_uN_0($f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_95)))), !($proj_num__1(!($proj_lane__0(c_2_81)))))).0))*{c_1_95 <- c_1_lst, c_2_81 <- c_2_lst}
    -- if ($isize(v_Inn) = $fsize(F64_Fnn))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)))
    -- (wf_uN: `%%`(1, mk_uN_uN($proj_uN_0($f_($sizenn($numtype_Fnn(F64_Fnn)), !($proj_num__1(!($proj_lane__0(c_1_96)))), !($proj_num__1(!($proj_lane__0(c_2_82)))))).0)))*{c_1_96 <- c_1_lst, c_2_82 <- c_2_lst}

;; test.spectec:3751.6-3751.15
relation fvrelop__is_wf(def $f_(v_N : N, v_fN : fN, v_fN : fN) : u32): `%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3751.6-3751.15
  rule fvrelop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_fN : fN, v_fN : fN) : u32, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%`(v_shape, v_vec_, vec__0, ret_val)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $fvrelop_(v_shape, def $f_, v_vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3753.1-3753.99
def $ivshiftop_(v_shape : shape, def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN, v_vec_ : vec_, v_u32 : u32) : vec_?
  ;; test.spectec:3821.1-3823.41
  def $ivshiftop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN, v_1 : uN, i : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_76)*{c_76 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_98)), i)*{c_1_98 <- c_1_lst}
  ;; test.spectec:3821.1-3823.41
  def $ivshiftop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN, v_1 : uN, i : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_78)*{c_78 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_100)), i)*{c_1_100 <- c_1_lst}
  ;; test.spectec:3821.1-3823.41
  def $ivshiftop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN, v_1 : uN, i : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_80)*{c_80 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_102)), i)*{c_1_102 <- c_1_lst}
  ;; test.spectec:3821.1-3823.41
  def $ivshiftop_{v_M : nat, def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN, v_1 : uN, i : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_82)*{c_82 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_104)), i)*{c_1_104 <- c_1_lst}
  def $ivshiftop_{x0 : shape, x2 : vec_, x3 : u32}(x0, def $f_, x2, x3) = ?()
    -- otherwise

;; test.spectec:3753.6-3753.17
relation ivshiftop__is_wf(def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN): `%%%%`(v_shape : shape, v_vec_ : vec_, v_u32 : u32, ret_val : vec_)
  ;; test.spectec:3753.6-3753.17
  rule ivshiftop__is_wf_0{v_shape : shape, def $f_(v_N : N, v_iN : iN, v_u32 : u32) : iN, v_vec_ : vec_, v_u32 : u32, ret_val : vec_}:
    `%%%%`(v_shape, v_vec_, v_u32, ret_val)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(32, v_u32)
    -- if ($ivshiftop_(v_shape, def $f_, v_vec_, v_u32) =/= ?())
    -- if (ret_val = !($ivshiftop_(v_shape, def $f_, v_vec_, v_u32)))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3754.1-3754.109
def $ivshiftopsx_(v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN, v_sx : sx, v_vec_ : vec_, v_u32 : u32) : vec_?
  ;; test.spectec:3825.1-3827.45
  def $ivshiftopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN, v_sx : sx, v_1 : uN, i : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_84)*{c_84 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_106)), i)*{c_1_106 <- c_1_lst}
  ;; test.spectec:3825.1-3827.45
  def $ivshiftopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN, v_sx : sx, v_1 : uN, i : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_86)*{c_86 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_108)), i)*{c_1_108 <- c_1_lst}
  ;; test.spectec:3825.1-3827.45
  def $ivshiftopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN, v_sx : sx, v_1 : uN, i : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_88)*{c_88 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_110)), i)*{c_1_110 <- c_1_lst}
  ;; test.spectec:3825.1-3827.45
  def $ivshiftopsx_{v_M : nat, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN, v_sx : sx, v_1 : uN, i : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_sx, v_1, i) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_90)*{c_90 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_112)), i)*{c_1_112 <- c_1_lst}
  def $ivshiftopsx_{x0 : shape, x2 : sx, x3 : vec_, x4 : u32}(x0, def $f_, x2, x3, x4) = ?()
    -- otherwise

;; test.spectec:3754.6-3754.19
relation ivshiftopsx__is_wf(def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN): `%%%%%`(v_shape : shape, v_sx : sx, v_vec_ : vec_, v_u32 : u32, ret_val : vec_)
  ;; test.spectec:3754.6-3754.19
  rule ivshiftopsx__is_wf_0{v_shape : shape, def $f_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN, v_sx : sx, v_vec_ : vec_, v_u32 : u32, ret_val : vec_}:
    `%%%%%`(v_shape, v_sx, v_vec_, v_u32, ret_val)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(32, v_u32)
    -- if ($ivshiftopsx_(v_shape, def $f_, v_sx, v_vec_, v_u32) =/= ?())
    -- if (ret_val = !($ivshiftopsx_(v_shape, def $f_, v_sx, v_vec_, v_u32)))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3756.6-3756.19
relation fun_ivbitmaskop_: `%%%`(shape, vec_, u32)
  ;; test.spectec:3756.6-3756.19
  rule fun_ivbitmaskop__case_0{v_M : nat, v_1 : uN, c : uN, c_1_lst : lane_*}:
    `%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), v_1, $irev_(32, c))
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1))
    -- (if ($proj_lane__2(c_1_114) =/= ?()))*{c_1_114 <- c_1_lst}
    -- if ($ibits_(32, c) = mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I32_Jnn)), S_sx, !($proj_lane__2(c_1_114)), mk_uN_iN(0))).0)*{c_1_114 <- c_1_lst} ++ mk_bit_bit(0)^(((32 : nat <:> int) - (v_M : nat <:> int)) : int <:> nat){})
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)))
    -- (if ($proj_lane__2(c_1_115) =/= ?()))*{c_1_115 <- c_1_lst}
    -- (wf_bit: `%`(mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I32_Jnn)), S_sx, !($proj_lane__2(c_1_115)), mk_uN_iN(0))).0)))*{c_1_115 <- c_1_lst}
    -- wf_bit: `%`(mk_bit_bit(0))

  ;; test.spectec:3756.6-3756.19
  rule fun_ivbitmaskop__case_1{v_M : nat, v_1 : uN, c : uN, c_1_lst : lane_*}:
    `%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), v_1, $irev_(32, c))
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1))
    -- (if ($proj_lane__2(c_1_117) =/= ?()))*{c_1_117 <- c_1_lst}
    -- if ($ibits_(32, c) = mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I64_Jnn)), S_sx, !($proj_lane__2(c_1_117)), mk_uN_iN(0))).0)*{c_1_117 <- c_1_lst} ++ mk_bit_bit(0)^(((32 : nat <:> int) - (v_M : nat <:> int)) : int <:> nat){})
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)))
    -- (if ($proj_lane__2(c_1_118) =/= ?()))*{c_1_118 <- c_1_lst}
    -- (wf_bit: `%`(mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I64_Jnn)), S_sx, !($proj_lane__2(c_1_118)), mk_uN_iN(0))).0)))*{c_1_118 <- c_1_lst}
    -- wf_bit: `%`(mk_bit_bit(0))

  ;; test.spectec:3756.6-3756.19
  rule fun_ivbitmaskop__case_2{v_M : nat, v_1 : uN, c : uN, c_1_lst : lane_*}:
    `%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), v_1, $irev_(32, c))
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1))
    -- (if ($proj_lane__2(c_1_120) =/= ?()))*{c_1_120 <- c_1_lst}
    -- if ($ibits_(32, c) = mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I8_Jnn)), S_sx, !($proj_lane__2(c_1_120)), mk_uN_iN(0))).0)*{c_1_120 <- c_1_lst} ++ mk_bit_bit(0)^(((32 : nat <:> int) - (v_M : nat <:> int)) : int <:> nat){})
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)))
    -- (if ($proj_lane__2(c_1_121) =/= ?()))*{c_1_121 <- c_1_lst}
    -- (wf_bit: `%`(mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I8_Jnn)), S_sx, !($proj_lane__2(c_1_121)), mk_uN_iN(0))).0)))*{c_1_121 <- c_1_lst}
    -- wf_bit: `%`(mk_bit_bit(0))

  ;; test.spectec:3756.6-3756.19
  rule fun_ivbitmaskop__case_3{v_M : nat, v_1 : uN, c : uN, c_1_lst : lane_*}:
    `%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), v_1, $irev_(32, c))
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1))
    -- (if ($proj_lane__2(c_1_123) =/= ?()))*{c_1_123 <- c_1_lst}
    -- if ($ibits_(32, c) = mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I16_Jnn)), S_sx, !($proj_lane__2(c_1_123)), mk_uN_iN(0))).0)*{c_1_123 <- c_1_lst} ++ mk_bit_bit(0)^(((32 : nat <:> int) - (v_M : nat <:> int)) : int <:> nat){})
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)))
    -- (if ($proj_lane__2(c_1_124) =/= ?()))*{c_1_124 <- c_1_lst}
    -- (wf_bit: `%`(mk_bit_bit($proj_uN_0($ilt_($lsizenn($lanetype_Jnn(I16_Jnn)), S_sx, !($proj_lane__2(c_1_124)), mk_uN_iN(0))).0)))*{c_1_124 <- c_1_lst}
    -- wf_bit: `%`(mk_bit_bit(0))

;; test.spectec:3756.6-3756.19
relation ivbitmaskop__is_wf: `%%%`(v_shape : shape, v_vec_ : vec_, ret_val : u32)
  ;; test.spectec:3756.6-3756.19
  rule ivbitmaskop__is_wf_0{v_shape : shape, v_vec_ : vec_, ret_val : u32, var_0 : u32}:
    `%%%`(v_shape, v_vec_, ret_val)
    -- fun_ivbitmaskop_: `%%%`(v_shape, v_vec_, var_0)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3757.1-3757.110
def $ivswizzlop_(v_shape : shape, def $f_(v_N : N, iN*, v_iN : iN) : iN, v_vec_ : vec_, vec__0 : vec_) : vec_?
  ;; test.spectec:3835.1-3838.44
  def $ivswizzlop_{v_M : nat, def $f_(v_N : N, iN*, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I32_Jnn, c_92)*{c_92 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I32_Jnn)), !($proj_lane__2(c_1_126))*{c_1_126 <- c_1_lst}, !($proj_lane__2(c_2_84)))*{c_2_84 <- c_2_lst}
  ;; test.spectec:3835.1-3838.44
  def $ivswizzlop_{v_M : nat, def $f_(v_N : N, iN*, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I64_Jnn, c_94)*{c_94 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I64_Jnn)), !($proj_lane__2(c_1_128))*{c_1_128 <- c_1_lst}, !($proj_lane__2(c_2_86)))*{c_2_86 <- c_2_lst}
  ;; test.spectec:3835.1-3838.44
  def $ivswizzlop_{v_M : nat, def $f_(v_N : N, iN*, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I8_Jnn, c_96)*{c_96 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I8_Jnn)), !($proj_lane__2(c_1_130))*{c_1_130 <- c_1_lst}, !($proj_lane__2(c_2_88)))*{c_2_88 <- c_2_lst}
  ;; test.spectec:3835.1-3838.44
  def $ivswizzlop_{v_M : nat, def $f_(v_N : N, iN*, v_iN : iN) : iN, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), def $f_, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), mk_lane__2_lane_(I16_Jnn, c_98)*{c_98 <- c_lst}))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : iN*} c_lst = $f_($lsizenn($lanetype_Jnn(I16_Jnn)), !($proj_lane__2(c_1_132))*{c_1_132 <- c_1_lst}, !($proj_lane__2(c_2_90)))*{c_2_90 <- c_2_lst}
  def $ivswizzlop_{x0 : shape, x2 : vec_, x3 : vec_}(x0, def $f_, x2, x3) = ?()
    -- otherwise

;; test.spectec:3757.6-3757.18
relation ivswizzlop__is_wf(def $f_(v_N : N, iN*, v_iN : iN) : iN): `%%%%`(v_shape : shape, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3757.6-3757.18
  rule ivswizzlop__is_wf_0{v_shape : shape, def $f_(v_N : N, iN*, v_iN : iN) : iN, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%`(v_shape, v_vec_, vec__0, ret_val)
    -- wf_shape: `%`(v_shape)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if ($ivswizzlop_(v_shape, def $f_, v_vec_, vec__0) =/= ?())
    -- if (ret_val = !($ivswizzlop_(v_shape, def $f_, v_vec_, vec__0)))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3758.1-3758.85
def $ivshufflop_(v_shape : shape, var_0_lst : laneidx*, v_vec_ : vec_, vec__0 : vec_) : vec_?
  ;; test.spectec:3841.1-3844.34
  def $ivshufflop_{v_M : nat, i_lst : laneidx*, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), i_lst, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), c_lst))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : lane_*} c_lst = c_1_lst ++ c_2_lst[$proj_uN_0(i_42250).0]*{i_42250 <- i_lst}
  ;; test.spectec:3841.1-3844.34
  def $ivshufflop_{v_M : nat, i_lst : laneidx*, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), i_lst, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), c_lst))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : lane_*} c_lst = c_1_lst ++ c_2_lst[$proj_uN_0(i_42256).0]*{i_42256 <- i_lst}
  ;; test.spectec:3841.1-3844.34
  def $ivshufflop_{v_M : nat, i_lst : laneidx*, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), i_lst, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), c_lst))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : lane_*} c_lst = c_1_lst ++ c_2_lst[$proj_uN_0(i_42262).0]*{i_42262 <- i_lst}
  ;; test.spectec:3841.1-3844.34
  def $ivshufflop_{v_M : nat, i_lst : laneidx*, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), i_lst, v_1, v_2) = ?($inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), c_lst))
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_1)
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v_2)
    -- let{c_lst : lane_*} c_lst = c_1_lst ++ c_2_lst[$proj_uN_0(i_42268).0]*{i_42268 <- i_lst}
  def $ivshufflop_{x0 : shape, x1 : laneidx*, x2 : vec_, x3 : vec_}(x0, x1, x2, x3) = ?()
    -- otherwise

;; test.spectec:3758.6-3758.18
relation ivshufflop__is_wf: `%%%%%`(v_shape : shape, var_0_lst : laneidx*, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3758.6-3758.18
  rule ivshufflop__is_wf_0{v_shape : shape, var_0_lst : laneidx*, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%%`(v_shape, var_0_lst, v_vec_, vec__0, ret_val)
    -- wf_shape: `%`(v_shape)
    -- (wf_uN: `%%`(8, var_0))*{var_0 <- var_0_lst}
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if ($ivshufflop_(v_shape, var_0_lst, v_vec_, vec__0) =/= ?())
    -- if (ret_val = !($ivshufflop_(v_shape, var_0_lst, v_vec_, vec__0)))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3849.1-3850.28
def $vvunop_(v_vectype : vectype, v_vvunop : vvunop, v_vec_ : vec_) : vec_*
  ;; test.spectec:3890.1-3890.53
  def $vvunop_{v_Vnn : vectype, v : uN}(v_Vnn, NOT_vvunop, v) = [$inot_($vsizenn(v_Vnn), v)]

;; test.spectec:3849.6-3849.14
relation vvunop__is_wf: `%%%%`(v_vectype : vectype, v_vvunop : vvunop, v_vec_ : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3849.6-3849.14
  rule vvunop__is_wf_0{v_vectype : vectype, v_vvunop : vvunop, v_vec_ : vec_, ret_val_lst : vec_*}:
    `%%%%`(v_vectype, v_vvunop, v_vec_, ret_val_lst)
    -- wf_uN: `%%`($vsize(v_vectype), v_vec_)
    -- if (ret_val_lst = $vvunop_(v_vectype, v_vvunop, v_vec_))
    -- (wf_uN: `%%`($vsize(v_vectype), ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3851.1-3852.31
def $vvbinop_(v_vectype : vectype, v_vvbinop : vvbinop, v_vec_ : vec_, vec__0 : vec_) : vec_*
  ;; test.spectec:3892.1-3892.68
  def $vvbinop_{v_Vnn : vectype, v_1 : uN, v_2 : uN}(v_Vnn, AND_vvbinop, v_1, v_2) = [$iand_($vsizenn(v_Vnn), v_1, v_2)]
  ;; test.spectec:3893.1-3893.74
  def $vvbinop_{v_Vnn : vectype, v_1 : uN, v_2 : uN}(v_Vnn, ANDNOT_vvbinop, v_1, v_2) = [$iandnot_($vsizenn(v_Vnn), v_1, v_2)]
  ;; test.spectec:3894.1-3894.66
  def $vvbinop_{v_Vnn : vectype, v_1 : uN, v_2 : uN}(v_Vnn, OR_vvbinop, v_1, v_2) = [$ior_($vsizenn(v_Vnn), v_1, v_2)]
  ;; test.spectec:3895.1-3895.68
  def $vvbinop_{v_Vnn : vectype, v_1 : uN, v_2 : uN}(v_Vnn, XOR_vvbinop, v_1, v_2) = [$ixor_($vsizenn(v_Vnn), v_1, v_2)]

;; test.spectec:3851.6-3851.15
relation vvbinop__is_wf: `%%%%%`(v_vectype : vectype, v_vvbinop : vvbinop, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3851.6-3851.15
  rule vvbinop__is_wf_0{v_vectype : vectype, v_vvbinop : vvbinop, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*}:
    `%%%%%`(v_vectype, v_vvbinop, v_vec_, vec__0, ret_val_lst)
    -- wf_uN: `%%`($vsize(v_vectype), v_vec_)
    -- wf_uN: `%%`($vsize(v_vectype), vec__0)
    -- if (ret_val_lst = $vvbinop_(v_vectype, v_vvbinop, v_vec_, vec__0))
    -- (wf_uN: `%%`($vsize(v_vectype), ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3853.1-3854.34
def $vvternop_(v_vectype : vectype, v_vvternop : vvternop, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_) : vec_*
  ;; test.spectec:3897.1-3897.91
  def $vvternop_{v_Vnn : vectype, v_1 : uN, v_2 : uN, v_3 : uN}(v_Vnn, BITSELECT_vvternop, v_1, v_2, v_3) = [$ibitselect_($vsizenn(v_Vnn), v_1, v_2, v_3)]

;; test.spectec:3853.6-3853.16
relation vvternop__is_wf: `%%%%%%`(v_vectype : vectype, v_vvternop : vvternop, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3853.6-3853.16
  rule vvternop__is_wf_0{v_vectype : vectype, v_vvternop : vvternop, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*}:
    `%%%%%%`(v_vectype, v_vvternop, v_vec_, vec__0, vec__1, ret_val_lst)
    -- wf_uN: `%%`($vsize(v_vectype), v_vec_)
    -- wf_uN: `%%`($vsize(v_vectype), vec__0)
    -- wf_uN: `%%`($vsize(v_vectype), vec__1)
    -- if (ret_val_lst = $vvternop_(v_vectype, v_vvternop, v_vec_, vec__0, vec__1))
    -- (wf_uN: `%%`($vsize(v_vectype), ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3856.6-3856.13
relation fun_vunop_: `%%%%`(shape, vunop_, vec_, vec_*)
  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_0{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, ABS_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fabs_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_1{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, ABS_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fabs_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_2{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, NEG_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fneg_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_3{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, NEG_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fneg_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_4{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, SQRT_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fsqrt_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_5{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, SQRT_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fsqrt_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_6{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, CEIL_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fceil_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_7{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, CEIL_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fceil_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_8{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, FLOOR_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $ffloor_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_9{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, FLOOR_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $ffloor_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_10{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, TRUNC_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $ftrunc_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_11{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, TRUNC_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $ftrunc_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_12{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F32_Fnn, M_0, NEAREST_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fnearest_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_13{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vunop__1_vunop_(F64_Fnn, M_0, NEAREST_vunop_Fnn_M), v, $fvunop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fnearest_, v))
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_14{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I32_Jnn, M_0, ABS_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iabs_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iabs_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_15{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I64_Jnn, M_0, ABS_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iabs_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iabs_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_16{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I8_Jnn, M_0, ABS_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iabs_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iabs_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_17{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I16_Jnn, M_0, ABS_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iabs_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iabs_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_18{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I32_Jnn, M_0, NEG_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ineg_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ineg_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_19{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I64_Jnn, M_0, NEG_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ineg_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ineg_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_20{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I8_Jnn, M_0, NEG_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ineg_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ineg_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_21{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I16_Jnn, M_0, NEG_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ineg_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ineg_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_22{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I32_Jnn, M_0, POPCNT_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_23{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I64_Jnn, M_0, POPCNT_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_24{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I8_Jnn, M_0, POPCNT_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3856.6-3856.13
  rule fun_vunop__case_25{v_M : nat, v : uN, M_0 : nat}:
    `%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vunop__0_vunop_(I16_Jnn, M_0, POPCNT_vunop_Jnn_M), v, !($ivunop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v)))
    -- if ($ivunop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ipopcnt_, v) =/= ?())
    -- if (v_M = M_0)

;; test.spectec:3856.6-3856.13
relation vunop__is_wf: `%%%%`(v_shape : shape, v_vunop_ : vunop_, v_vec_ : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3856.6-3856.13
  rule vunop__is_wf_0{v_shape : shape, v_vunop_ : vunop_, v_vec_ : vec_, ret_val_lst : vec_*, var_0 : vec_*}:
    `%%%%`(v_shape, v_vunop_, v_vec_, ret_val_lst)
    -- fun_vunop_: `%%%%`(v_shape, v_vunop_, v_vec_, var_0)
    -- wf_shape: `%`(v_shape)
    -- wf_vunop_: `%%`(v_shape, v_vunop_)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3858.6-3858.14
relation fun_vbinop_: `%%%%%`(shape, vbinop_, vec_, vec_, vec_*)
  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_0{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, ADD_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_1{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, ADD_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_2{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, ADD_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_3{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, ADD_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iadd_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_4{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, SUB_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_5{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, SUB_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_6{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, SUB_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_7{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, SUB_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $isub_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_8{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, MUL_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_9{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, MUL_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_10{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, MUL_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_11{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, MUL_vbinop_Jnn_M), v_1, v_2, !($ivbinop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2)))
    -- if ($ivbinop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $imul_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_12{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, ADD_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_13{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, ADD_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_14{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, ADD_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_15{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, ADD_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iadd_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_16{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, SUB_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_17{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, SUB_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_18{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, SUB_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_19{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, SUB_SAT_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $isub_sat_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_20{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, MIN_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_21{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, MIN_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_22{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, MIN_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_23{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, MIN_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $imin_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_24{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, MAX_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_25{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, MAX_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_26{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, MAX_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_27{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, MAX_vbinop_Jnn_M(v_sx)), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $imax_, v_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_28{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, AVGRU_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_29{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, AVGRU_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_30{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, AVGRU_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_31{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, AVGRU_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iavgr_, U_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_32{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, Q15MULR_SATS_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_33{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, Q15MULR_SATS_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_34{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, Q15MULR_SATS_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_35{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, Q15MULR_SATS_vbinop_Jnn_M), v_1, v_2, !($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2)))
    -- if ($ivbinopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $iq15mulr_sat_, S_sx, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_36{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I32_Jnn, M_0, RELAXED_Q15MULRS_vbinop_Jnn_M), v_1, v_2, $ivbinopsxnd_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_37{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I64_Jnn, M_0, RELAXED_Q15MULRS_vbinop_Jnn_M), v_1, v_2, $ivbinopsxnd_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_38{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I8_Jnn, M_0, RELAXED_Q15MULRS_vbinop_Jnn_M), v_1, v_2, $ivbinopsxnd_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_39{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vbinop__0_vbinop_(I16_Jnn, M_0, RELAXED_Q15MULRS_vbinop_Jnn_M), v_1, v_2, $ivbinopsxnd_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_40{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, ADD_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fadd_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_41{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, ADD_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fadd_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_42{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, SUB_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fsub_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_43{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, SUB_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fsub_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_44{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, MUL_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fmul_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_45{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, MUL_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fmul_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_46{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, DIV_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fdiv_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_47{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, DIV_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fdiv_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_48{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, MIN_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fmin_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_49{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, MIN_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fmin_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_50{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, MAX_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fmax_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_51{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, MAX_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fmax_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_52{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, PMIN_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fpmin_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_53{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, PMIN_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fpmin_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_54{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, PMAX_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fpmax_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_55{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, PMAX_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fpmax_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_56{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, RELAXED_MIN_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $frelaxed_min_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_57{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, RELAXED_MIN_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $frelaxed_min_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_58{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F32_Fnn, M_0, RELAXED_MAX_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $frelaxed_max_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3858.6-3858.14
  rule fun_vbinop__case_59{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vbinop__1_vbinop_(F64_Fnn, M_0, RELAXED_MAX_vbinop_Fnn_M), v_1, v_2, $fvbinop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $frelaxed_max_, v_1, v_2))
    -- if (v_M = M_0)

;; test.spectec:3858.6-3858.14
relation vbinop__is_wf: `%%%%%`(v_shape : shape, v_vbinop_ : vbinop_, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3858.6-3858.14
  rule vbinop__is_wf_0{v_shape : shape, v_vbinop_ : vbinop_, v_vec_ : vec_, vec__0 : vec_, ret_val_lst : vec_*, var_0 : vec_*}:
    `%%%%%`(v_shape, v_vbinop_, v_vec_, vec__0, ret_val_lst)
    -- fun_vbinop_: `%%%%%`(v_shape, v_vbinop_, v_vec_, vec__0, var_0)
    -- wf_shape: `%`(v_shape)
    -- wf_vbinop_: `%%`(v_shape, v_vbinop_)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3860.6-3860.15
relation fun_vternop_: `%%%%%%`(shape, vternop_, vec_, vec_, vec_, vec_*)
  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_0{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vternop__0_vternop_(I32_Jnn, M_0, RELAXED_LANESELECT_vternop_Jnn_M), v_1, v_2, v_3, $ivternopnd_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $irelaxed_laneselect_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_1{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vternop__0_vternop_(I64_Jnn, M_0, RELAXED_LANESELECT_vternop_Jnn_M), v_1, v_2, v_3, $ivternopnd_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $irelaxed_laneselect_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_2{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vternop__0_vternop_(I8_Jnn, M_0, RELAXED_LANESELECT_vternop_Jnn_M), v_1, v_2, v_3, $ivternopnd_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $irelaxed_laneselect_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_3{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vternop__0_vternop_(I16_Jnn, M_0, RELAXED_LANESELECT_vternop_Jnn_M), v_1, v_2, v_3, $ivternopnd_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $irelaxed_laneselect_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_4{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vternop__1_vternop_(F32_Fnn, M_0, RELAXED_MADD_vternop_Fnn_M), v_1, v_2, v_3, $fvternop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $frelaxed_madd_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_5{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vternop__1_vternop_(F64_Fnn, M_0, RELAXED_MADD_vternop_Fnn_M), v_1, v_2, v_3, $fvternop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $frelaxed_madd_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_6{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vternop__1_vternop_(F32_Fnn, M_0, RELAXED_NMADD_vternop_Fnn_M), v_1, v_2, v_3, $fvternop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $frelaxed_nmadd_, v_1, v_2, v_3))
    -- if (v_M = M_0)

  ;; test.spectec:3860.6-3860.15
  rule fun_vternop__case_7{v_M : nat, v_1 : uN, v_2 : uN, v_3 : uN, M_0 : nat}:
    `%%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vternop__1_vternop_(F64_Fnn, M_0, RELAXED_NMADD_vternop_Fnn_M), v_1, v_2, v_3, $fvternop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $frelaxed_nmadd_, v_1, v_2, v_3))
    -- if (v_M = M_0)

;; test.spectec:3860.6-3860.15
relation vternop__is_wf: `%%%%%%`(v_shape : shape, v_vternop_ : vternop_, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*)
  ;; test.spectec:3860.6-3860.15
  rule vternop__is_wf_0{v_shape : shape, v_vternop_ : vternop_, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val_lst : vec_*, var_0 : vec_*}:
    `%%%%%%`(v_shape, v_vternop_, v_vec_, vec__0, vec__1, ret_val_lst)
    -- fun_vternop_: `%%%%%%`(v_shape, v_vternop_, v_vec_, vec__0, vec__1, var_0)
    -- wf_shape: `%`(v_shape)
    -- wf_vternop_: `%%`(v_shape, v_vternop_)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (ret_val_lst = var_0)
    -- (wf_uN: `%%`(128, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3862.6-3862.14
relation fun_vrelop_: `%%%%%`(shape, vrelop_, vec_, vec_, vec_)
  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_0{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I32_Jnn, M_0, EQ_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ieq_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_1{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I64_Jnn, M_0, EQ_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ieq_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_2{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I8_Jnn, M_0, EQ_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ieq_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_3{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I16_Jnn, M_0, EQ_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ieq_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_4{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I32_Jnn, M_0, NE_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ine_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_5{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I64_Jnn, M_0, NE_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ine_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_6{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I8_Jnn, M_0, NE_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ine_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_7{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I16_Jnn, M_0, NE_vrelop_Jnn_M), v_1, v_2, $ivrelop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ine_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_8{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I32_Jnn, M_0, LT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ilt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_9{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I64_Jnn, M_0, LT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ilt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_10{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I8_Jnn, M_0, LT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ilt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_11{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I16_Jnn, M_0, LT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ilt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_12{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I32_Jnn, M_0, GT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $igt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_13{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I64_Jnn, M_0, GT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $igt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_14{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I8_Jnn, M_0, GT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $igt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_15{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I16_Jnn, M_0, GT_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $igt_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_16{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I32_Jnn, M_0, LE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ile_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_17{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I64_Jnn, M_0, LE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ile_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_18{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I8_Jnn, M_0, LE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ile_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_19{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I16_Jnn, M_0, LE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ile_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_20{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I32_Jnn, M_0, GE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ige_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_21{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I64_Jnn, M_0, GE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ige_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_22{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I8_Jnn, M_0, GE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ige_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_23{v_M : nat, v_sx : sx, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M)), mk_vrelop__0_vrelop_(I16_Jnn, M_0, GE_vrelop_Jnn_M(v_sx)), v_1, v_2, $ivrelopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ige_, v_sx, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_24{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F32_Fnn, M_0, EQ_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $feq_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_25{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F64_Fnn, M_0, EQ_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $feq_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_26{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F32_Fnn, M_0, NE_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fne_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_27{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F64_Fnn, M_0, NE_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fne_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_28{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F32_Fnn, M_0, LT_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $flt_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_29{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F64_Fnn, M_0, LT_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $flt_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_30{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F32_Fnn, M_0, GT_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fgt_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_31{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F64_Fnn, M_0, GT_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fgt_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_32{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F32_Fnn, M_0, LE_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fle_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_33{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F64_Fnn, M_0, LE_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fle_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_34{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F32_Fnn, M_0, GE_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F32_Fnn), mk_dim_dim(v_M)), def $fge_, v_1, v_2))
    -- if (v_M = M_0)

  ;; test.spectec:3862.6-3862.14
  rule fun_vrelop__case_35{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(v_M)), mk_vrelop__1_vrelop_(F64_Fnn, M_0, GE_vrelop_Fnn_M), v_1, v_2, $fvrelop_(`%X%`_shape($lanetype_Fnn(F64_Fnn), mk_dim_dim(v_M)), def $fge_, v_1, v_2))
    -- if (v_M = M_0)

;; test.spectec:3862.6-3862.14
relation vrelop__is_wf: `%%%%%`(v_shape : shape, v_vrelop_ : vrelop_, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3862.6-3862.14
  rule vrelop__is_wf_0{v_shape : shape, v_vrelop_ : vrelop_, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%`(v_shape, v_vrelop_, v_vec_, vec__0, ret_val)
    -- fun_vrelop_: `%%%%%`(v_shape, v_vrelop_, v_vec_, vec__0, var_0)
    -- wf_shape: `%`(v_shape)
    -- wf_vrelop_: `%%`(v_shape, v_vrelop_)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3865.6-3865.15
relation fun_lcvtop__: `%%%%%`(shape, shape, vcvtop__, lane_, lane_*)
  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_0{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I32_Jnn, c_1), [mk_lane__2_lane_(I32_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_1{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I64_Jnn, c_1), [mk_lane__2_lane_(I32_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_2{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I8_Jnn, c_1), [mk_lane__2_lane_(I32_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_3{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I16_Jnn, c_1), [mk_lane__2_lane_(I32_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_4{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I32_Jnn, c_1), [mk_lane__2_lane_(I64_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_5{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I64_Jnn, c_1), [mk_lane__2_lane_(I64_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_6{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I8_Jnn, c_1), [mk_lane__2_lane_(I64_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_7{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I16_Jnn, c_1), [mk_lane__2_lane_(I64_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_8{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I32_Jnn, c_1), [mk_lane__2_lane_(I8_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_9{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I64_Jnn, c_1), [mk_lane__2_lane_(I8_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_10{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I8_Jnn, c_1), [mk_lane__2_lane_(I8_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_11{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I16_Jnn, c_1), [mk_lane__2_lane_(I8_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_12{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I32_Jnn, c_1), [mk_lane__2_lane_(I16_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_13{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I64_Jnn, c_1), [mk_lane__2_lane_(I16_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_14{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I8_Jnn, c_1), [mk_lane__2_lane_(I16_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_15{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : iN}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), mk_vcvtop___0_vcvtop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, EXTEND_vcvtop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), mk_lane__2_lane_(I16_Jnn, c_1), [mk_lane__2_lane_(I16_Jnn, c)])
    -- if (c = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_16{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I32_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I32_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_17{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I64_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I64_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_18{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I8_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I8_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_19{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I16_Jnn, M_1_0, F32_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I16_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_20{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I32_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I32_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_21{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I64_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I64_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_22{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I8_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I8_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_23{M_1 : nat, M_2 : nat, half_opt : half?, v_sx : sx, c_1 : uN, M_1_0 : nat, M_2_0 : nat, c : fN}:
    `%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___1_vcvtop__(I16_Jnn, M_1_0, F64_Fnn, M_2_0, CONVERT_vcvtop__Jnn_1_M_1_Fnn_2_M_2(half_opt, v_sx)), mk_lane__2_lane_(I16_Jnn, c_1), [mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c))])
    -- if (c = $convert__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_24{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I32_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I32_Inn), mk_num__0_num_(I32_Inn, c_108))?{c_108 <- c_opt}))
    -- if (c_opt = $trunc_sat__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_addrtype(I32_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_25{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I64_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I64_Inn), mk_num__0_num_(I64_Inn, c_110))?{c_110 <- c_opt}))
    -- if (c_opt = $trunc_sat__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_addrtype(I64_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_26{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I32_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I32_Inn), mk_num__0_num_(I32_Inn, c_112))?{c_112 <- c_opt}))
    -- if (c_opt = $trunc_sat__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_addrtype(I32_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_27{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I64_Jnn, M_2_0, TRUNC_SAT_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I64_Inn), mk_num__0_num_(I64_Inn, c_114))?{c_114 <- c_opt}))
    -- if (c_opt = $trunc_sat__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_addrtype(I64_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_28{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I32_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I32_Inn), mk_num__0_num_(I32_Inn, c_116))?{c_116 <- c_opt}))
    -- if (c_opt = $relaxed_trunc__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_addrtype(I32_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_29{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F32_Fnn, M_1_0, I64_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I64_Inn), mk_num__0_num_(I64_Inn, c_118))?{c_118 <- c_opt}))
    -- if (c_opt = $relaxed_trunc__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_addrtype(I64_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_30{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I32_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I32_Inn), mk_num__0_num_(I32_Inn, c_120))?{c_120 <- c_opt}))
    -- if (c_opt = $relaxed_trunc__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_addrtype(I32_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_31{M_1 : nat, M_2 : nat, v_sx : sx, zero_opt : zero?, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_opt : iN?}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___2_vcvtop__(F64_Fnn, M_1_0, I64_Jnn, M_2_0, RELAXED_TRUNC_vcvtop__Fnn_1_M_1_Jnn_2_M_2(v_sx, zero_opt)), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), lift(mk_lane__0_lane_($numtype_addrtype(I64_Inn), mk_num__0_num_(I64_Inn, c_122))?{c_122 <- c_opt}))
    -- if (c_opt = $relaxed_trunc__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_addrtype(I64_Inn)), v_sx, c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_32{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F32_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(ZERO_zero)), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c_124))*{c_124 <- c_lst})
    -- if (c_lst = $demote__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_33{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F64_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(ZERO_zero)), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c_126))*{c_126 <- c_lst})
    -- if (c_lst = $demote__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_34{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F32_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(ZERO_zero)), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c_128))*{c_128 <- c_lst})
    -- if (c_lst = $demote__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_35{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F64_Fnn, M_2_0, DEMOTE_vcvtop__Fnn_1_M_1_Fnn_2_M_2(ZERO_zero)), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c_130))*{c_130 <- c_lst})
    -- if (c_lst = $demote__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_36{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F32_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c_132))*{c_132 <- c_lst})
    -- if (c_lst = $promote__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_37{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F32_Fnn, M_1_0, F64_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), mk_lane__0_lane_(F32_numtype, mk_num__1_num_(F32_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c_134))*{c_134 <- c_lst})
    -- if (c_lst = $promote__($lsizenn1($lanetype_Fnn(F32_Fnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_38{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F32_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F32_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F32_Fnn), mk_num__1_num_(F32_Fnn, c_136))*{c_136 <- c_lst})
    -- if (c_lst = $promote__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_Fnn(F32_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3865.6-3865.15
  rule fun_lcvtop___case_39{M_1 : nat, M_2 : nat, c_1 : fN, M_1_0 : nat, M_2_0 : nat, c_lst : fN*}:
    `%%%%%`(`%X%`_shape(F64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(F64_lanetype, mk_dim_dim(M_2)), mk_vcvtop___3_vcvtop__(F64_Fnn, M_1_0, F64_Fnn, M_2_0, PROMOTELOW_vcvtop__Fnn_1_M_1_Fnn_2_M_2), mk_lane__0_lane_(F64_numtype, mk_num__1_num_(F64_Fnn, c_1)), mk_lane__0_lane_($numtype_Fnn(F64_Fnn), mk_num__1_num_(F64_Fnn, c_138))*{c_138 <- c_lst})
    -- if (c_lst = $promote__($lsizenn1($lanetype_Fnn(F64_Fnn)), $lsizenn2($lanetype_Fnn(F64_Fnn)), c_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

;; test.spectec:3865.6-3865.15
relation lcvtop___is_wf: `%%%%%`(shape_1 : shape, shape_2 : shape, v_vcvtop__ : vcvtop__, v_lane_ : lane_, ret_val_lst : lane_*)
  ;; test.spectec:3865.6-3865.15
  rule lcvtop___is_wf_0{shape_1 : shape, shape_2 : shape, v_vcvtop__ : vcvtop__, v_lane_ : lane_, ret_val_lst : lane_*, var_0 : lane_*}:
    `%%%%%`(shape_1, shape_2, v_vcvtop__, v_lane_, ret_val_lst)
    -- fun_lcvtop__: `%%%%%`(shape_1, shape_2, v_vcvtop__, v_lane_, var_0)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_vcvtop__: `%%%`(shape_1, shape_2, v_vcvtop__)
    -- wf_lane_: `%%`($fun_lanetype(shape_1), v_lane_)
    -- if (ret_val_lst = var_0)
    -- (wf_lane_: `%%`($fun_lanetype(shape_2), ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3867.6-3867.15
relation fun_vcvtop__: `%%%%%`(shape, shape, vcvtop__, vec_, vec_)
  ;; test.spectec:3867.6-3867.15
  rule fun_vcvtop___case_0{Lnn_1 : lanetype, v_M : nat, Lnn_2 : lanetype, vcvtop : vcvtop__, v_1 : uN, v : uN, M_0 : nat, c_1_lst : lane_*, c_lst_lst : lane_**, var_2_lst : lane_**, var_1 : zero?, var_0 : half?}:
    `%%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(v_M)), `%X%`_shape(Lnn_2, mk_dim_dim(M_0)), vcvtop, v_1, v)
    -- if (|var_2_lst| = |c_1_lst|)
    -- (fun_lcvtop__: `%%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(v_M)), `%X%`_shape(Lnn_2, mk_dim_dim(v_M)), vcvtop, c_1_142, var_2))*{var_2 <- var_2_lst, c_1_142 <- c_1_lst}
    -- fun_zeroop: `%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(v_M)), `%X%`_shape(Lnn_2, mk_dim_dim(v_M)), vcvtop, var_1)
    -- fun_halfop: `%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(v_M)), `%X%`_shape(Lnn_2, mk_dim_dim(v_M)), vcvtop, var_0)
    -- if ((var_0 = ?()) /\ (var_1 = ?()))
    -- if (c_1_lst = $lanes_(`%X%`_shape(Lnn_1, mk_dim_dim(v_M)), v_1))
    -- if (c_lst_lst = $setproduct_(syntax lane_, var_2_lst))
    -- if (|$inv_lanes_(`%X%`_shape(Lnn_2, mk_dim_dim(v_M)), c_lst_30)*{c_lst_30 <- c_lst_lst}| > 0)
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, mk_dim_dim(v_M)), c_lst_30)*{c_lst_30 <- c_lst_lst})
    -- wf_shape: `%`(`%X%`_shape(Lnn_1, mk_dim_dim(v_M)))
    -- wf_shape: `%`(`%X%`_shape(Lnn_2, mk_dim_dim(v_M)))
    -- if (v_M = M_0)

  ;; test.spectec:3867.6-3867.15
  rule fun_vcvtop___case_1{Lnn_1 : lanetype, M_1 : nat, Lnn_2 : lanetype, M_2 : nat, vcvtop : vcvtop__, v_1 : uN, v : uN, v_half : half, c_1_lst : lane_*, c_lst_lst : lane_**, var_1_lst : lane_**, var_0 : half?}:
    `%%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), `%X%`_shape(Lnn_2, mk_dim_dim(M_2)), vcvtop, v_1, v)
    -- if (|var_1_lst| = |c_1_lst|)
    -- (fun_lcvtop__: `%%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), `%X%`_shape(Lnn_2, mk_dim_dim(M_2)), vcvtop, c_1_144, var_1))*{var_1 <- var_1_lst, c_1_144 <- c_1_lst}
    -- fun_halfop: `%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), `%X%`_shape(Lnn_2, mk_dim_dim(M_2)), vcvtop, var_0)
    -- if (var_0 = ?(v_half))
    -- if (c_1_lst = $lanes_(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), v_1)[$fun_half(v_half, 0, M_2) : M_2])
    -- if (c_lst_lst = $setproduct_(syntax lane_, var_1_lst))
    -- if (|$inv_lanes_(`%X%`_shape(Lnn_2, mk_dim_dim(M_2)), c_lst_32)*{c_lst_32 <- c_lst_lst}| > 0)
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, mk_dim_dim(M_2)), c_lst_32)*{c_lst_32 <- c_lst_lst})
    -- wf_shape: `%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape(Lnn_2, mk_dim_dim(M_2)))

  ;; test.spectec:3867.6-3867.15
  rule fun_vcvtop___case_2{Lnn_1 : lanetype, M_1 : nat, Lnn_2 : lanetype, M_2 : nat, vcvtop : vcvtop__, v_1 : uN, v : uN, c_1_lst : lane_*, c_lst_lst : lane_**, var_1_lst : lane_**, var_0 : zero?}:
    `%%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), `%X%`_shape(Lnn_2, mk_dim_dim(M_2)), vcvtop, v_1, v)
    -- if (|var_1_lst| = |c_1_lst|)
    -- (fun_lcvtop__: `%%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), `%X%`_shape(Lnn_2, mk_dim_dim(M_2)), vcvtop, c_1_146, var_1))*{var_1 <- var_1_lst, c_1_146 <- c_1_lst}
    -- fun_zeroop: `%%%%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), `%X%`_shape(Lnn_2, mk_dim_dim(M_2)), vcvtop, var_0)
    -- if (var_0 = ?(ZERO_zero))
    -- if (c_1_lst = $lanes_(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)), v_1))
    -- if (c_lst_lst = $setproduct_(syntax lane_, var_1_lst ++ [$fun_zero(Lnn_2)]^M_1{}))
    -- if (|$inv_lanes_(`%X%`_shape(Lnn_2, mk_dim_dim(M_2)), c_lst_34)*{c_lst_34 <- c_lst_lst}| > 0)
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, mk_dim_dim(M_2)), c_lst_34)*{c_lst_34 <- c_lst_lst})
    -- wf_shape: `%`(`%X%`_shape(Lnn_1, mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape(Lnn_2, mk_dim_dim(M_2)))

;; test.spectec:3867.6-3867.15
relation vcvtop___is_wf: `%%%%%`(shape_1 : shape, shape_2 : shape, v_vcvtop__ : vcvtop__, v_vec_ : vec_, ret_val : vec_)
  ;; test.spectec:3867.6-3867.15
  rule vcvtop___is_wf_0{shape_1 : shape, shape_2 : shape, v_vcvtop__ : vcvtop__, v_vec_ : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%`(shape_1, shape_2, v_vcvtop__, v_vec_, ret_val)
    -- fun_vcvtop__: `%%%%%`(shape_1, shape_2, v_vcvtop__, v_vec_, var_0)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_vcvtop__: `%%%`(shape_1, shape_2, v_vcvtop__)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3870.6-3870.16
relation fun_vshiftop_: `%%%%%`(ishape, vshiftop_, vec_, u32, vec_)
  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_0{v_M : nat, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I32_Jnn, M_0, SHL_vshiftop_Jnn_M), v, i, !($ivshiftop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i)))
    -- if ($ivshiftop_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_1{v_M : nat, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I64_Jnn, M_0, SHL_vshiftop_Jnn_M), v, i, !($ivshiftop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i)))
    -- if ($ivshiftop_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_2{v_M : nat, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I8_Jnn, M_0, SHL_vshiftop_Jnn_M), v, i, !($ivshiftop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i)))
    -- if ($ivshiftop_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_3{v_M : nat, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I16_Jnn, M_0, SHL_vshiftop_Jnn_M), v, i, !($ivshiftop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i)))
    -- if ($ivshiftop_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ishl_, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_4{v_M : nat, v_sx : sx, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I32_Jnn, M_0, SHR_vshiftop_Jnn_M(v_sx)), v, i, !($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i)))
    -- if ($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_5{v_M : nat, v_sx : sx, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I64_Jnn, M_0, SHR_vshiftop_Jnn_M(v_sx)), v, i, !($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i)))
    -- if ($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_6{v_M : nat, v_sx : sx, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I8_Jnn, M_0, SHR_vshiftop_Jnn_M(v_sx)), v, i, !($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i)))
    -- if ($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3870.6-3870.16
  rule fun_vshiftop__case_7{v_M : nat, v_sx : sx, v : uN, i : uN, M_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M))), mk_vshiftop__0_vshiftop_(I16_Jnn, M_0, SHR_vshiftop_Jnn_M(v_sx)), v, i, !($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i)))
    -- if ($ivshiftopsx_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), def $ishr_, v_sx, v, i) =/= ?())
    -- if (v_M = M_0)

;; test.spectec:3870.6-3870.16
relation vshiftop__is_wf: `%%%%%`(v_ishape : ishape, v_vshiftop_ : vshiftop_, v_vec_ : vec_, v_u32 : u32, ret_val : vec_)
  ;; test.spectec:3870.6-3870.16
  rule vshiftop__is_wf_0{v_ishape : ishape, v_vshiftop_ : vshiftop_, v_vec_ : vec_, v_u32 : u32, ret_val : vec_, var_0 : vec_}:
    `%%%%%`(v_ishape, v_vshiftop_, v_vec_, v_u32, ret_val)
    -- fun_vshiftop_: `%%%%%`(v_ishape, v_vshiftop_, v_vec_, v_u32, var_0)
    -- wf_ishape: `%`(v_ishape)
    -- wf_vshiftop_: `%%`(v_ishape, v_vshiftop_)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(32, v_u32)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3872.6-3872.18
relation fun_vbitmaskop_: `%%%`(ishape, vec_, u32)
  ;; test.spectec:3872.6-3872.18
  rule fun_vbitmaskop__case_0{v_M : nat, v : uN, var_0 : u32}:
    `%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(v_M))), v, var_0)
    -- fun_ivbitmaskop_: `%%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(v_M)), v, var_0)

  ;; test.spectec:3872.6-3872.18
  rule fun_vbitmaskop__case_1{v_M : nat, v : uN, var_0 : u32}:
    `%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(v_M))), v, var_0)
    -- fun_ivbitmaskop_: `%%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(v_M)), v, var_0)

  ;; test.spectec:3872.6-3872.18
  rule fun_vbitmaskop__case_2{v_M : nat, v : uN, var_0 : u32}:
    `%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))), v, var_0)
    -- fun_ivbitmaskop_: `%%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(v_M)), v, var_0)

  ;; test.spectec:3872.6-3872.18
  rule fun_vbitmaskop__case_3{v_M : nat, v : uN, var_0 : u32}:
    `%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(v_M))), v, var_0)
    -- fun_ivbitmaskop_: `%%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(v_M)), v, var_0)

;; test.spectec:3872.6-3872.18
relation vbitmaskop__is_wf: `%%%`(v_ishape : ishape, v_vec_ : vec_, ret_val : u32)
  ;; test.spectec:3872.6-3872.18
  rule vbitmaskop__is_wf_0{v_ishape : ishape, v_vec_ : vec_, ret_val : u32, var_0 : u32}:
    `%%%`(v_ishape, v_vec_, ret_val)
    -- fun_vbitmaskop_: `%%%`(v_ishape, v_vec_, var_0)
    -- wf_ishape: `%`(v_ishape)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:3874.6-3874.17
relation fun_vswizzlop_: `%%%%%`(bshape, vswizzlop_, vec_, vec_, vec_)
  ;; test.spectec:3874.6-3874.17
  rule fun_vswizzlop__case_0{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(mk_bshape_bshape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))), mk_vswizzlop__0_vswizzlop_(M_0, SWIZZLE_vswizzlop_M), v_1, v_2, !($ivswizzlop_(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $iswizzle_lane_, v_1, v_2)))
    -- if ($ivswizzlop_(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $iswizzle_lane_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

  ;; test.spectec:3874.6-3874.17
  rule fun_vswizzlop__case_1{v_M : nat, v_1 : uN, v_2 : uN, M_0 : nat}:
    `%%%%%`(mk_bshape_bshape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))), mk_vswizzlop__0_vswizzlop_(M_0, RELAXED_SWIZZLE_vswizzlop_M), v_1, v_2, !($ivswizzlop_(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $irelaxed_swizzle_lane_, v_1, v_2)))
    -- if ($ivswizzlop_(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), def $irelaxed_swizzle_lane_, v_1, v_2) =/= ?())
    -- if (v_M = M_0)

;; test.spectec:3874.6-3874.17
relation vswizzlop__is_wf: `%%%%%`(v_bshape : bshape, v_vswizzlop_ : vswizzlop_, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3874.6-3874.17
  rule vswizzlop__is_wf_0{v_bshape : bshape, v_vswizzlop_ : vswizzlop_, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%`(v_bshape, v_vswizzlop_, v_vec_, vec__0, ret_val)
    -- fun_vswizzlop_: `%%%%%`(v_bshape, v_vswizzlop_, v_vec_, vec__0, var_0)
    -- wf_bshape: `%`(v_bshape)
    -- wf_vswizzlop_: `%%`(v_bshape, v_vswizzlop_)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3876.1-3877.40
def $vshufflop_(v_bshape : bshape, var_0_lst : laneidx*, v_vec_ : vec_, vec__0 : vec_) : vec_?
  ;; test.spectec:3960.1-3960.75
  def $vshufflop_{v_M : nat, i_lst : laneidx*, v_1 : uN, v_2 : uN}(mk_bshape_bshape(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M))), i_lst, v_1, v_2) = $ivshufflop_(`%X%`_shape(I8_lanetype, mk_dim_dim(v_M)), i_lst, v_1, v_2)
  def $vshufflop_{x0 : bshape, x1 : laneidx*, x2 : vec_, x3 : vec_}(x0, x1, x2, x3) = ?()
    -- otherwise

;; test.spectec:3876.6-3876.17
relation vshufflop__is_wf: `%%%%%`(v_bshape : bshape, var_0_lst : laneidx*, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3876.6-3876.17
  rule vshufflop__is_wf_0{v_bshape : bshape, var_0_lst : laneidx*, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%%`(v_bshape, var_0_lst, v_vec_, vec__0, ret_val)
    -- wf_bshape: `%`(v_bshape)
    -- (wf_uN: `%%`(8, var_0))*{var_0 <- var_0_lst}
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if ($vshufflop_(v_bshape, var_0_lst, v_vec_, vec__0) =/= ?())
    -- if (ret_val = !($vshufflop_(v_bshape, var_0_lst, v_vec_, vec__0)))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3879.6-3879.18
relation fun_vnarrowop__: `%%%%%%`(shape, shape, sx, vec_, vec_, vec_)
  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_0{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_148) =/= ?()))*{c_1_148 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_148)))*{c_1_148 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_100) =/= ?()))*{c_2_100 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_2_100)))*{c_2_100 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c'_1_2)*{c'_1_2 <- c'_1_lst} ++ mk_lane__2_lane_(I32_Jnn, c'_2_2)*{c'_2_2 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_1_3)))*{c'_1_3 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_2_3)))*{c'_2_3 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_1{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_150) =/= ?()))*{c_1_150 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_150)))*{c_1_150 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_102) =/= ?()))*{c_2_102 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_2_102)))*{c_2_102 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c'_1_5)*{c'_1_5 <- c'_1_lst} ++ mk_lane__2_lane_(I32_Jnn, c'_2_5)*{c'_2_5 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_1_6)))*{c'_1_6 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_2_6)))*{c'_2_6 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_2{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_152) =/= ?()))*{c_1_152 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_152)))*{c_1_152 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_104) =/= ?()))*{c_2_104 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_2_104)))*{c_2_104 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c'_1_8)*{c'_1_8 <- c'_1_lst} ++ mk_lane__2_lane_(I32_Jnn, c'_2_8)*{c'_2_8 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_1_9)))*{c'_1_9 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_2_9)))*{c'_2_9 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_3{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_154) =/= ?()))*{c_1_154 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_154)))*{c_1_154 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_106) =/= ?()))*{c_2_106 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_2_106)))*{c_2_106 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c'_1_11)*{c'_1_11 <- c'_1_lst} ++ mk_lane__2_lane_(I32_Jnn, c'_2_11)*{c'_2_11 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_1_12)))*{c'_1_12 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I32_Jnn, c'_2_12)))*{c'_2_12 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_4{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_156) =/= ?()))*{c_1_156 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_156)))*{c_1_156 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_108) =/= ?()))*{c_2_108 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_2_108)))*{c_2_108 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c'_1_14)*{c'_1_14 <- c'_1_lst} ++ mk_lane__2_lane_(I64_Jnn, c'_2_14)*{c'_2_14 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_1_15)))*{c'_1_15 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_2_15)))*{c'_2_15 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_5{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_158) =/= ?()))*{c_1_158 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_158)))*{c_1_158 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_110) =/= ?()))*{c_2_110 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_2_110)))*{c_2_110 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c'_1_17)*{c'_1_17 <- c'_1_lst} ++ mk_lane__2_lane_(I64_Jnn, c'_2_17)*{c'_2_17 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_1_18)))*{c'_1_18 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_2_18)))*{c'_2_18 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_6{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_160) =/= ?()))*{c_1_160 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_160)))*{c_1_160 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_112) =/= ?()))*{c_2_112 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_2_112)))*{c_2_112 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c'_1_20)*{c'_1_20 <- c'_1_lst} ++ mk_lane__2_lane_(I64_Jnn, c'_2_20)*{c'_2_20 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_1_21)))*{c'_1_21 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_2_21)))*{c'_2_21 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_7{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_162) =/= ?()))*{c_1_162 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_162)))*{c_1_162 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_114) =/= ?()))*{c_2_114 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_2_114)))*{c_2_114 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c'_1_23)*{c'_1_23 <- c'_1_lst} ++ mk_lane__2_lane_(I64_Jnn, c'_2_23)*{c'_2_23 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_1_24)))*{c'_1_24 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I64_Jnn, c'_2_24)))*{c'_2_24 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_8{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_164) =/= ?()))*{c_1_164 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_164)))*{c_1_164 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_116) =/= ?()))*{c_2_116 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_2_116)))*{c_2_116 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c'_1_26)*{c'_1_26 <- c'_1_lst} ++ mk_lane__2_lane_(I8_Jnn, c'_2_26)*{c'_2_26 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_1_27)))*{c'_1_27 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_2_27)))*{c'_2_27 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_9{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_166) =/= ?()))*{c_1_166 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_166)))*{c_1_166 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_118) =/= ?()))*{c_2_118 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_2_118)))*{c_2_118 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c'_1_29)*{c'_1_29 <- c'_1_lst} ++ mk_lane__2_lane_(I8_Jnn, c'_2_29)*{c'_2_29 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_1_30)))*{c'_1_30 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_2_30)))*{c'_2_30 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_10{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_168) =/= ?()))*{c_1_168 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_168)))*{c_1_168 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_120) =/= ?()))*{c_2_120 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_2_120)))*{c_2_120 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c'_1_32)*{c'_1_32 <- c'_1_lst} ++ mk_lane__2_lane_(I8_Jnn, c'_2_32)*{c'_2_32 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_1_33)))*{c'_1_33 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_2_33)))*{c'_2_33 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_11{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_170) =/= ?()))*{c_1_170 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_170)))*{c_1_170 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_122) =/= ?()))*{c_2_122 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_2_122)))*{c_2_122 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c'_1_35)*{c'_1_35 <- c'_1_lst} ++ mk_lane__2_lane_(I8_Jnn, c'_2_35)*{c'_2_35 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_1_36)))*{c'_1_36 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I8_Jnn, c'_2_36)))*{c'_2_36 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_12{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_172) =/= ?()))*{c_1_172 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_172)))*{c_1_172 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_124) =/= ?()))*{c_2_124 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I32_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_2_124)))*{c_2_124 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c'_1_38)*{c'_1_38 <- c'_1_lst} ++ mk_lane__2_lane_(I16_Jnn, c'_2_38)*{c'_2_38 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_1_39)))*{c'_1_39 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_2_39)))*{c'_2_39 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_13{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_174) =/= ?()))*{c_1_174 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_174)))*{c_1_174 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_126) =/= ?()))*{c_2_126 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I64_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_2_126)))*{c_2_126 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c'_1_41)*{c'_1_41 <- c'_1_lst} ++ mk_lane__2_lane_(I16_Jnn, c'_2_41)*{c'_2_41 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_1_42)))*{c'_1_42 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_2_42)))*{c'_2_42 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_14{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_176) =/= ?()))*{c_1_176 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_176)))*{c_1_176 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_128) =/= ?()))*{c_2_128 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I8_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_2_128)))*{c_2_128 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c'_1_44)*{c'_1_44 <- c'_1_lst} ++ mk_lane__2_lane_(I16_Jnn, c'_2_44)*{c'_2_44 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_1_45)))*{c'_1_45 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_2_45)))*{c'_2_45 <- c'_2_lst}

  ;; test.spectec:3879.6-3879.18
  rule fun_vnarrowop___case_15{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, v_2 : uN, c_1_lst : lane_*, c_2_lst : lane_*, c'_1_lst : iN*, c'_2_lst : iN*, v : vec_}:
    `%%%%%%`(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), v_sx, v_1, v_2, v)
    -- if (c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1))
    -- if (c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2))
    -- (if ($proj_lane__2(c_1_178) =/= ?()))*{c_1_178 <- c_1_lst}
    -- if (c'_1_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_178)))*{c_1_178 <- c_1_lst})
    -- (if ($proj_lane__2(c_2_130) =/= ?()))*{c_2_130 <- c_2_lst}
    -- if (c'_2_lst = $narrow__($lsize($lanetype_Jnn(I16_Jnn)), $lsize($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_2_130)))*{c_2_130 <- c_2_lst})
    -- if (v = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c'_1_47)*{c'_1_47 <- c'_1_lst} ++ mk_lane__2_lane_(I16_Jnn, c'_2_47)*{c'_2_47 <- c'_2_lst}))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_1_48)))*{c'_1_48 <- c'_1_lst}
    -- (wf_lane_: `%%`($fun_lanetype(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_lane__2_lane_(I16_Jnn, c'_2_48)))*{c'_2_48 <- c'_2_lst}

;; test.spectec:3879.6-3879.18
relation vnarrowop___is_wf: `%%%%%%`(shape_1 : shape, shape_2 : shape, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3879.6-3879.18
  rule vnarrowop___is_wf_0{shape_1 : shape, shape_2 : shape, v_sx : sx, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%%`(shape_1, shape_2, v_sx, v_vec_, vec__0, ret_val)
    -- fun_vnarrowop__: `%%%%%%`(shape_1, shape_2, v_sx, v_vec_, vec__0, var_0)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4040.1-4040.76
def $ivadd_pairwise_(v_N : N, var_0_lst : iN*) : iN*
  ;; test.spectec:4041.1-4042.37
  def $ivadd_pairwise_{v_N : nat, i_lst : iN*, j_1_lst : N*, j_2_lst : N*}(v_N, i_lst) = $iadd_(v_N, mk_uN_iN(j_1), mk_uN_iN(j_2))*{j_1 <- j_1_lst, j_2 <- j_2_lst}
    -- if ($concat_(syntax N, [j_1_1 j_2_1]*{j_1_1 <- j_1_lst, j_2_1 <- j_2_lst}) = $proj_uN_0(i_42815).0*{i_42815 <- i_lst})

;; test.spectec:4040.6-4040.22
relation ivadd_pairwise__is_wf: `%%%`(v_N : N, var_0_lst : iN*, ret_val_lst : iN*)
  ;; test.spectec:4040.6-4040.22
  rule ivadd_pairwise__is_wf_0{v_N : N, var_0_lst : iN*, ret_val_lst : iN*}:
    `%%%`(v_N, var_0_lst, ret_val_lst)
    -- (wf_uN: `%%`(v_N, var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = $ivadd_pairwise_(v_N, var_0_lst))
    -- (wf_uN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4026.1-4026.93
def $ivextunop__(shape_1 : shape, shape_2 : shape, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_vec_ : vec_) : vec_
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_146)*{c_146 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_180)))*{c_1_180 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_148)*{c_148 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_182)))*{c_1_182 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_150)*{c_150 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_184)))*{c_1_184 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_152)*{c_152 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), v_sx, !($proj_lane__2(c_1_186)))*{c_1_186 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_154)*{c_154 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_188)))*{c_1_188 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_156)*{c_156 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_190)))*{c_1_190 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_158)*{c_158 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_192)))*{c_1_192 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_160)*{c_160 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), v_sx, !($proj_lane__2(c_1_194)))*{c_1_194 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_162)*{c_162 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_196)))*{c_1_196 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_164)*{c_164 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_198)))*{c_1_198 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_166)*{c_166 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_200)))*{c_1_200 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_168)*{c_168 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), v_sx, !($proj_lane__2(c_1_202)))*{c_1_202 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_170)*{c_170 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_204)))*{c_1_204 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_172)*{c_172 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_206)))*{c_1_206 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_174)*{c_174 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_208)))*{c_1_208 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_1 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, v_sx, v_1) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_176)*{c_176 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), v_sx, !($proj_lane__2(c_1_210)))*{c_1_210 <- c_1_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))

;; test.spectec:4026.6-4026.18
relation ivextunop___is_wf(def $f_(v_N : N, iN*) : iN*): `%%%%%`(shape_1 : shape, shape_2 : shape, v_sx : sx, v_vec_ : vec_, ret_val : vec_)
  ;; test.spectec:4026.6-4026.18
  rule ivextunop___is_wf_0{shape_1 : shape, shape_2 : shape, def $f_(v_N : N, iN*) : iN*, v_sx : sx, v_vec_ : vec_, ret_val : vec_}:
    `%%%%%`(shape_1, shape_2, v_sx, v_vec_, ret_val)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val = $ivextunop__(shape_1, shape_2, def $f_, v_sx, v_vec_))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3882.6-3882.17
relation fun_vextunop__: `%%%%%`(ishape, ishape, vextunop__, vec_, vec_)
  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_0{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_1{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_2{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_3{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_4{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_5{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_6{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_7{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_8{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_9{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_10{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_11{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_12{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_13{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_14{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3882.6-3882.17
  rule fun_vextunop___case_15{M_1 : nat, M_2 : nat, v_sx : sx, v_1 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(v_sx)), v_1, $ivextunop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivadd_pairwise_, v_sx, v_1))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

;; test.spectec:3882.6-3882.17
relation vextunop___is_wf: `%%%%%`(ishape_1 : ishape, ishape_2 : ishape, v_vextunop__ : vextunop__, v_vec_ : vec_, ret_val : vec_)
  ;; test.spectec:3882.6-3882.17
  rule vextunop___is_wf_0{ishape_1 : ishape, ishape_2 : ishape, v_vextunop__ : vextunop__, v_vec_ : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%`(ishape_1, ishape_2, v_vextunop__, v_vec_, ret_val)
    -- fun_vextunop__: `%%%%%`(ishape_1, ishape_2, v_vextunop__, v_vec_, var_0)
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextunop__: `%%%`(ishape_1, ishape_2, v_vextunop__)
    -- wf_uN: `%%`(128, v_vec_)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4047.1-4047.40
def $ivdot_(v_N : N, var_0_lst : iN*, var_1_lst : iN*) : iN*
  ;; test.spectec:4048.1-4049.59
  def $ivdot_{v_N : nat, i_1_lst : iN*, i_2_lst : iN*, j_1_lst : iN*, j_2_lst : iN*}(v_N, i_1_lst, i_2_lst) = $iadd_(v_N, j_1, j_2)*{j_1 <- j_1_lst, j_2 <- j_2_lst}
    -- if ($concat_(syntax iN, [j_1_2 j_2_2]*{j_1_2 <- j_1_lst, j_2_2 <- j_2_lst}) = $imul_(v_N, i_1_2, i_2_2)*{i_1_2 <- i_1_lst, i_2_2 <- i_2_lst})

;; test.spectec:4047.6-4047.13
relation ivdot__is_wf: `%%%%`(v_N : N, var_0_lst : iN*, var_1_lst : iN*, ret_val_lst : iN*)
  ;; test.spectec:4047.6-4047.13
  rule ivdot__is_wf_0{v_N : N, var_0_lst : iN*, var_1_lst : iN*, ret_val_lst : iN*}:
    `%%%%`(v_N, var_0_lst, var_1_lst, ret_val_lst)
    -- (wf_uN: `%%`(v_N, var_0))*{var_0 <- var_0_lst}
    -- (wf_uN: `%%`(v_N, var_1))*{var_1 <- var_1_lst}
    -- if (ret_val_lst = $ivdot_(v_N, var_0_lst, var_1_lst))
    -- (wf_uN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4051.1-4051.76
def $ivdot_sat_(v_N : N, var_0_lst : iN*, var_1_lst : iN*) : iN*
  ;; test.spectec:4052.1-4053.59
  def $ivdot_sat_{v_N : nat, i_1_lst : iN*, i_2_lst : iN*, j_1_lst : iN*, j_2_lst : iN*}(v_N, i_1_lst, i_2_lst) = $iadd_sat_(v_N, S_sx, j_1, j_2)*{j_1 <- j_1_lst, j_2 <- j_2_lst}
    -- if ($concat_(syntax iN, [j_1_3 j_2_3]*{j_1_3 <- j_1_lst, j_2_3 <- j_2_lst}) = $imul_(v_N, i_1_4, i_2_4)*{i_1_4 <- i_1_lst, i_2_4 <- i_2_lst})

;; test.spectec:4051.6-4051.17
relation ivdot_sat__is_wf: `%%%%`(v_N : N, var_0_lst : iN*, var_1_lst : iN*, ret_val_lst : iN*)
  ;; test.spectec:4051.6-4051.17
  rule ivdot_sat__is_wf_0{v_N : N, var_0_lst : iN*, var_1_lst : iN*, ret_val_lst : iN*}:
    `%%%%`(v_N, var_0_lst, var_1_lst, ret_val_lst)
    -- (wf_uN: `%%`(v_N, var_0))*{var_0 <- var_0_lst}
    -- (wf_uN: `%%`(v_N, var_1))*{var_1 <- var_1_lst}
    -- if (ret_val_lst = $ivdot_sat_(v_N, var_0_lst, var_1_lst))
    -- (wf_uN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4032.1-4032.136
def $ivextbinop__(shape_1 : shape, shape_2 : shape, def $f_(v_N : N, iN*, iN*) : iN*, v_sx : sx, sx_0 : sx, v_laneidx : laneidx, laneidx_0 : laneidx, v_vec_ : vec_, vec__0 : vec_) : vec_
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_178)*{c_178 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_1, !($proj_lane__2(c_1_212)))*{c_1_212 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_2, !($proj_lane__2(c_2_132)))*{c_2_132 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_180)*{c_180 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_1, !($proj_lane__2(c_1_214)))*{c_1_214 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_2, !($proj_lane__2(c_2_134)))*{c_2_134 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_182)*{c_182 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_1, !($proj_lane__2(c_1_216)))*{c_1_216 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_2, !($proj_lane__2(c_2_136)))*{c_2_136 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I32_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I32_Jnn, c_184)*{c_184 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_1, !($proj_lane__2(c_1_218)))*{c_1_218 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I32_Jnn)), sx_2, !($proj_lane__2(c_2_138)))*{c_2_138 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I32_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_186)*{c_186 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_1, !($proj_lane__2(c_1_220)))*{c_1_220 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_2, !($proj_lane__2(c_2_140)))*{c_2_140 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_188)*{c_188 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_1, !($proj_lane__2(c_1_222)))*{c_1_222 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_2, !($proj_lane__2(c_2_142)))*{c_2_142 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_190)*{c_190 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_1, !($proj_lane__2(c_1_224)))*{c_1_224 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_2, !($proj_lane__2(c_2_144)))*{c_2_144 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I64_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I64_Jnn, c_192)*{c_192 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_1, !($proj_lane__2(c_1_226)))*{c_1_226 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I64_Jnn)), sx_2, !($proj_lane__2(c_2_146)))*{c_2_146 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I64_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_194)*{c_194 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_1, !($proj_lane__2(c_1_228)))*{c_1_228 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_2, !($proj_lane__2(c_2_148)))*{c_2_148 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_196)*{c_196 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_1, !($proj_lane__2(c_1_230)))*{c_1_230 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_2, !($proj_lane__2(c_2_150)))*{c_2_150 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_198)*{c_198 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_1, !($proj_lane__2(c_1_232)))*{c_1_232 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_2, !($proj_lane__2(c_2_152)))*{c_2_152 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I8_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I8_Jnn, c_200)*{c_200 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_1, !($proj_lane__2(c_1_234)))*{c_1_234 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I8_Jnn)), sx_2, !($proj_lane__2(c_2_154)))*{c_2_154 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I8_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_202)*{c_202 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_1, !($proj_lane__2(c_1_236)))*{c_1_236 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I32_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_2, !($proj_lane__2(c_2_156)))*{c_2_156 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_204)*{c_204 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_1, !($proj_lane__2(c_1_238)))*{c_1_238 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I64_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_2, !($proj_lane__2(c_2_158)))*{c_2_158 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_206)*{c_206 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_1, !($proj_lane__2(c_1_240)))*{c_1_240 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I8_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_2, !($proj_lane__2(c_2_160)))*{c_2_160 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)))
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{M_1 : nat, M_2 : nat, def $f_(v_N : N, iN*, iN*) : iN*, sx_1 : sx, sx_2 : sx, i : uN, k : uN, v_1 : uN, v_2 : uN}(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1)), `%X%`_shape(I16_lanetype, mk_dim_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_lane__2_lane_(I16_Jnn, c_208)*{c_208 <- c_lst})
    -- let{c_1_lst : lane_*} c_1_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_1)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c_2_lst : lane_*} c_2_lst = $lanes_(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), v_2)[$proj_uN_0(i).0 : $proj_uN_0(k).0]
    -- let{c'_1_lst : iN*} c'_1_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_1, !($proj_lane__2(c_1_242)))*{c_1_242 <- c_1_lst}
    -- let{c'_2_lst : iN*} c'_2_lst = $extend__($lsizenn1($lanetype_Jnn(I16_Jnn)), $lsizenn2($lanetype_Jnn(I16_Jnn)), sx_2, !($proj_lane__2(c_2_162)))*{c_2_162 <- c_2_lst}
    -- let{c_lst : iN*} c_lst = $f_($lsizenn2($lanetype_Jnn(I16_Jnn)), c'_1_lst, c'_2_lst)
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)))

;; test.spectec:4032.6-4032.19
relation ivextbinop___is_wf(def $f_(v_N : N, iN*, iN*) : iN*): `%%%%%%%%%`(shape_1 : shape, shape_2 : shape, v_sx : sx, sx_0 : sx, v_laneidx : laneidx, laneidx_0 : laneidx, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:4032.6-4032.19
  rule ivextbinop___is_wf_0{shape_1 : shape, shape_2 : shape, def $f_(v_N : N, iN*, iN*) : iN*, v_sx : sx, sx_0 : sx, v_laneidx : laneidx, laneidx_0 : laneidx, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_}:
    `%%%%%%%%%`(shape_1, shape_2, v_sx, sx_0, v_laneidx, laneidx_0, v_vec_, vec__0, ret_val)
    -- wf_shape: `%`(shape_1)
    -- wf_shape: `%`(shape_2)
    -- wf_uN: `%%`(8, v_laneidx)
    -- wf_uN: `%%`(8, laneidx_0)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = $ivextbinop__(shape_1, shape_2, def $f_, v_sx, sx_0, v_laneidx, laneidx_0, v_vec_, vec__0))
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4044.1-4044.40
def $ivmul_(v_N : N, var_0_lst : iN*, var_1_lst : iN*) : iN*
  ;; test.spectec:4045.1-4045.50
  def $ivmul_{v_N : nat, i_1_lst : iN*, i_2_lst : iN*}(v_N, i_1_lst, i_2_lst) = $imul_(v_N, i_1, i_2)*{i_1 <- i_1_lst, i_2 <- i_2_lst}

;; test.spectec:4044.6-4044.13
relation ivmul__is_wf: `%%%%`(v_N : N, var_0_lst : iN*, var_1_lst : iN*, ret_val_lst : iN*)
  ;; test.spectec:4044.6-4044.13
  rule ivmul__is_wf_0{v_N : N, var_0_lst : iN*, var_1_lst : iN*, ret_val_lst : iN*}:
    `%%%%`(v_N, var_0_lst, var_1_lst, ret_val_lst)
    -- (wf_uN: `%%`(v_N, var_0))*{var_0 <- var_0_lst}
    -- (wf_uN: `%%`(v_N, var_1))*{var_1 <- var_1_lst}
    -- if (ret_val_lst = $ivmul_(v_N, var_0_lst, var_1_lst))
    -- (wf_uN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:3884.6-3884.18
relation fun_vextbinop__: `%%%%%%`(ishape, ishape, vextbinop__, vec_, vec_, vec_)
  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_0{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_1{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_2{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_3{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_4{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_5{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_6{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_7{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_8{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_9{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_10{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_11{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_12{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_13{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_14{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_15{M_1 : nat, M_2 : nat, v_half : half, v_sx : sx, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, EXTMUL_vextbinop__Jnn_1_M_1_Jnn_2_M_2(v_half, v_sx)), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivmul_, v_sx, v_sx, mk_uN_laneidx($fun_half(v_half, 0, M_2)), mk_uN_laneidx(M_2), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_16{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_17{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_18{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_19{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_20{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_21{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_22{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_23{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_24{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_25{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_26{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_27{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_28{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_29{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_30{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_31{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_, S_sx, S_sx, mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_32{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_33{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_34{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_35{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_36{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_37{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_38{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_39{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_40{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_41{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_42{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_43{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_44{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_45{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_46{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3884.6-3884.18
  rule fun_vextbinop___case_47{M_1 : nat, M_2 : nat, v_1 : uN, v_2 : uN, M_1_0 : nat, M_2_0 : nat}:
    `%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), v_1, v_2, $ivextbinop__(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1)), `%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), def $ivdot_sat_, S_sx, $fun_relaxed2($R_idot, syntax sx, S_sx, U_sx), mk_uN_laneidx(0), mk_uN_laneidx(M_1), v_1, v_2))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

;; test.spectec:3884.6-3884.18
relation vextbinop___is_wf: `%%%%%%`(ishape_1 : ishape, ishape_2 : ishape, v_vextbinop__ : vextbinop__, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_)
  ;; test.spectec:3884.6-3884.18
  rule vextbinop___is_wf_0{ishape_1 : ishape, ishape_2 : ishape, v_vextbinop__ : vextbinop__, v_vec_ : vec_, vec__0 : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%%`(ishape_1, ishape_2, v_vextbinop__, v_vec_, vec__0, ret_val)
    -- fun_vextbinop__: `%%%%%%`(ishape_1, ishape_2, v_vextbinop__, v_vec_, vec__0, var_0)
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextbinop__: `%%%`(ishape_1, ishape_2, v_vextbinop__)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:3886.6-3886.19
relation fun_vextternop__: `%%%%%%%`(ishape, ishape, vextternop__, vec_, vec_, vec_, vec_)
  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_0{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I32_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I32_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_1{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I64_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I64_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_2{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I8_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I8_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_3{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I16_Jnn, M_1_0, I32_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I16_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I32_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I32_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_4{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I32_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I32_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_5{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I64_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I64_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_6{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I8_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I8_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_7{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I16_Jnn, M_1_0, I64_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I16_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I64_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I64_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_8{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I32_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I32_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_9{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I64_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I64_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_10{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I8_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I8_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_11{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I16_Jnn, M_1_0, I8_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I16_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I8_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I8_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_12{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I32_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I32_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I32_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I32_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I32_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_13{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I64_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I64_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I64_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I64_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I64_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_14{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I8_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I8_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I8_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I8_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I8_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

  ;; test.spectec:3886.6-3886.19
  rule fun_vextternop___case_15{M_1 : nat, M_2 : nat, c_1 : uN, c_2 : uN, c_3 : uN, c : uN, v_Jnn : Jnn, M_1_0 : nat, M_2_0 : nat, v_M : M, c' : vec_, c'' : vec_, var_2 : vec_*, var_1 : vec_, var_0 : vec_}:
    `%%%%%%%`(mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape(I16_lanetype, mk_dim_dim(M_2))), mk_vextternop___0_vextternop__(I16_Jnn, M_1_0, I16_Jnn, M_2_0, RELAXED_DOT_ADDS_vextternop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, c_3, c)
    -- fun_vbinop_: `%%%%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M), c'', c_3, var_2)
    -- fun_vextunop__: `%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)), c', var_1)
    -- fun_vextbinop__: `%%%%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2), c_1, c_2, var_0)
    -- if ($jsizenn(v_Jnn) = (2 * $lsizenn1($lanetype_Jnn(I16_Jnn))))
    -- if (v_M = (2 * M_2))
    -- if (c' = var_0)
    -- if (c'' = var_1)
    -- if (|var_2| > 0)
    -- if (c <- var_2)
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))))
    -- wf_vextbinop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_1))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_vextbinop___0_vextbinop__(I16_Jnn, M_1, v_Jnn, v_M, RELAXED_DOTS_vextbinop__Jnn_1_M_1_Jnn_2_M_2))
    -- wf_ishape: `%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))))
    -- wf_vextunop__: `%%%`(mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(v_Jnn), mk_dim_dim(v_M))), mk_ishape_ishape(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2))), mk_vextunop___0_vextunop__(v_Jnn, v_M, I16_Jnn, M_2, EXTADD_PAIRWISE_vextunop__Jnn_1_M_1_Jnn_2_M_2(S_sx)))
    -- wf_shape: `%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)))
    -- wf_vbinop_: `%%`(`%X%`_shape($lanetype_Jnn(I16_Jnn), mk_dim_dim(M_2)), mk_vbinop__0_vbinop_(I16_Jnn, M_2, ADD_vbinop_Jnn_M))
    -- if (M_1 = M_1_0)
    -- if (M_2 = M_2_0)

;; test.spectec:3886.6-3886.19
relation vextternop___is_wf: `%%%%%%%`(ishape_1 : ishape, ishape_2 : ishape, v_vextternop__ : vextternop__, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val : vec_)
  ;; test.spectec:3886.6-3886.19
  rule vextternop___is_wf_0{ishape_1 : ishape, ishape_2 : ishape, v_vextternop__ : vextternop__, v_vec_ : vec_, vec__0 : vec_, vec__1 : vec_, ret_val : vec_, var_0 : vec_}:
    `%%%%%%%`(ishape_1, ishape_2, v_vextternop__, v_vec_, vec__0, vec__1, ret_val)
    -- fun_vextternop__: `%%%%%%%`(ishape_1, ishape_2, v_vextternop__, v_vec_, vec__0, vec__1, var_0)
    -- wf_ishape: `%`(ishape_1)
    -- wf_ishape: `%`(ishape_2)
    -- wf_vextternop__: `%%%`(ishape_1, ishape_2, v_vextternop__)
    -- wf_uN: `%%`(128, v_vec_)
    -- wf_uN: `%%`(128, vec__0)
    -- wf_uN: `%%`(128, vec__1)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(128, ret_val)

;; test.spectec:4124.1-4125.63
syntax num = 
  | CONST(v_numtype : numtype, num_)

def $val_num(var_0 : num) : val
  def $val_num{x0 : numtype, x1 : num_}(CONST_num(x0, x1)) = CONST_val(x0, x1)

;; test.spectec:4124.8-4124.11
relation wf_num: `%`(num)
  ;; test.spectec:4124.8-4124.11
  rule num_case_0{v_numtype : numtype, var_0 : num_}:
    `%`(CONST_num(v_numtype, var_0))
    -- wf_num_: `%%`(v_numtype, var_0)

;; test.spectec:4127.1-4128.87
syntax vec = 
  | VCONST(v_vectype : vectype, vec_)

def $val_vec(var_0 : vec) : val
  def $val_vec{x0 : vectype, x1 : vec_}(VCONST_vec(x0, x1)) = VCONST_val(x0, x1)

;; test.spectec:4127.8-4127.11
relation wf_vec: `%`(vec)
  ;; test.spectec:4127.8-4127.11
  rule vec_case_0{v_vectype : vectype, var_0 : vec_}:
    `%`(VCONST_vec(v_vectype, var_0))
    -- wf_uN: `%%`($vsize(v_vectype), var_0)

;; test.spectec:4143.1-4144.58
syntax result = 
  | _VALS(val_lst : val*)
  | `(REF_EXN_ADDR%)THROW_REF`(v_exnaddr : exnaddr)
  | TRAP

;; test.spectec:4143.8-4143.14
relation wf_result: `%`(result)
  ;; test.spectec:4143.8-4143.14
  rule result_case_0{val_lst : val*}:
    `%`(_VALS_result(val_lst))
    -- (wf_val: `%`(v_val))*{v_val <- val_lst}

  ;; test.spectec:4143.8-4143.14
  rule result_case_1{v_exnaddr : exnaddr}:
    `%`(`(REF_EXN_ADDR%)THROW_REF`_result(v_exnaddr))

  ;; test.spectec:4143.8-4143.14
  rule result_case_2:
    `%`(TRAP_result)

;; test.spectec:4152.1-4152.72
syntax hostfunc = 
  | mk_hostfunc

;; test.spectec:4153.1-4153.73
syntax funccode = 
  | FUNC(v_typeidx : typeidx, local_lst : local*, v_expr : expr)
  | mk_funccode

;; test.spectec:4153.8-4153.16
relation wf_funccode: `%`(funccode)
  ;; test.spectec:4153.8-4153.16
  rule funccode_case_0{v_typeidx : typeidx, local_lst : local*, v_expr : expr}:
    `%`(FUNC_funccode(v_typeidx, local_lst, v_expr))
    -- wf_uN: `%%`(32, v_typeidx)
    -- (wf_local: `%`(v_local))*{v_local <- local_lst}
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

  ;; test.spectec:4153.8-4153.16
  rule funccode_case_1:
    `%`(mk_funccode_funccode)

;; test.spectec:4155.1-4156.19
syntax taginst = 
{
  TYPE tagtype
}

;; test.spectec:4155.8-4155.15
relation wf_taginst: `%`(taginst)
  ;; test.spectec:4155.8-4155.15
  rule taginst_case_{var_0 : tagtype}:
    `%`({TYPE var_0})
    -- wf_typeuse: `%`(var_0)

;; test.spectec:4158.1-4159.33
syntax globalinst = 
{
  TYPE globaltype,
  VALUE val
}

;; test.spectec:4158.8-4158.18
relation wf_globalinst: `%`(globalinst)
  ;; test.spectec:4158.8-4158.18
  rule globalinst_case_{var_0 : globaltype, var_1 : val}:
    `%`({TYPE var_0, VALUE var_1})
    -- wf_globaltype: `%`(var_0)
    -- wf_val: `%`(var_1)

;; test.spectec:4161.1-4162.32
syntax meminst = 
{
  TYPE memtype,
  BYTES byte*
}

;; test.spectec:4161.8-4161.15
relation wf_meminst: `%`(meminst)
  ;; test.spectec:4161.8-4161.15
  rule meminst_case_{var_0 : memtype, var_1_lst : byte*}:
    `%`({TYPE var_0, BYTES var_1_lst})
    -- wf_memtype: `%`(var_0)
    -- (wf_byte: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:4164.1-4165.32
syntax tableinst = 
{
  TYPE tabletype,
  REFS ref*
}

;; test.spectec:4164.8-4164.17
relation wf_tableinst: `%`(tableinst)
  ;; test.spectec:4164.8-4164.17
  rule tableinst_case_{var_0 : tabletype, var_1_lst : ref*}:
    `%`({TYPE var_0, REFS var_1_lst})
    -- wf_tabletype: `%`(var_0)
    -- (wf_ref: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:4167.1-4168.53
syntax funcinst = 
{
  TYPE deftype,
  MODULE moduleinst,
  CODE funccode
}

;; test.spectec:4167.8-4167.16
relation wf_funcinst: `%`(funcinst)
  ;; test.spectec:4167.8-4167.16
  rule funcinst_case_{var_0 : deftype, var_1 : moduleinst, var_2 : funccode}:
    `%`({TYPE var_0, MODULE var_1, CODE var_2})
    -- wf_moduleinst: `%`(var_1)
    -- wf_funccode: `%`(var_2)

;; test.spectec:4170.1-4171.18
syntax datainst = 
{
  BYTES byte*
}

;; test.spectec:4170.8-4170.16
relation wf_datainst: `%`(datainst)
  ;; test.spectec:4170.8-4170.16
  rule datainst_case_{var_0_lst : byte*}:
    `%`({BYTES var_0_lst})
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}

;; test.spectec:4173.1-4174.31
syntax eleminst = 
{
  TYPE elemtype,
  REFS ref*
}

;; test.spectec:4173.8-4173.16
relation wf_eleminst: `%`(eleminst)
  ;; test.spectec:4173.8-4173.16
  rule eleminst_case_{var_0 : elemtype, var_1_lst : ref*}:
    `%`({TYPE var_0, REFS var_1_lst})
    -- wf_reftype: `%`(var_0)
    -- (wf_ref: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:4180.1-4181.64
syntax packval = 
  | PACK(v_packtype : packtype, iN)

;; test.spectec:4180.8-4180.15
relation wf_packval: `%`(packval)
  ;; test.spectec:4180.8-4180.15
  rule packval_case_0{v_packtype : packtype, var_0 : iN}:
    `%`(PACK_packval(v_packtype, var_0))
    -- wf_uN: `%%`($psize(v_packtype), var_0)

;; test.spectec:4183.1-4184.18
syntax fieldval = 
  | CONST(v_numtype : numtype, num_)
  | VCONST(v_vectype : vectype, vec_)
  | REF_I31_NUM(v_u31 : u31)
  | REF_NULL_ADDR
  | REF_STRUCT_ADDR(v_structaddr : structaddr)
  | REF_ARRAY_ADDR(v_arrayaddr : arrayaddr)
  | REF_FUNC_ADDR(v_funcaddr : funcaddr)
  | REF_EXN_ADDR(v_exnaddr : exnaddr)
  | REF_HOST_ADDR(v_hostaddr : hostaddr)
  | REF_EXTERN(v_ref : ref)
  | PACK(v_packtype : packtype, iN)

def $fieldval_packval(var_0 : packval) : fieldval
  def $fieldval_packval{x0 : packtype, x1 : iN}(PACK_packval(x0, x1)) = PACK_fieldval(x0, x1)

def $fieldval_val(var_0 : val) : fieldval
  def $fieldval_val{x0 : numtype, x1 : num_}(CONST_val(x0, x1)) = CONST_fieldval(x0, x1)
  def $fieldval_val{x0 : vectype, x1 : vec_}(VCONST_val(x0, x1)) = VCONST_fieldval(x0, x1)
  def $fieldval_val{x0 : u31}(REF_I31_NUM_val(x0)) = REF_I31_NUM_fieldval(x0)
  def $fieldval_val(REF_NULL_ADDR_val) = REF_NULL_ADDR_fieldval
  def $fieldval_val{x0 : structaddr}(REF_STRUCT_ADDR_val(x0)) = REF_STRUCT_ADDR_fieldval(x0)
  def $fieldval_val{x0 : arrayaddr}(REF_ARRAY_ADDR_val(x0)) = REF_ARRAY_ADDR_fieldval(x0)
  def $fieldval_val{x0 : funcaddr}(REF_FUNC_ADDR_val(x0)) = REF_FUNC_ADDR_fieldval(x0)
  def $fieldval_val{x0 : exnaddr}(REF_EXN_ADDR_val(x0)) = REF_EXN_ADDR_fieldval(x0)
  def $fieldval_val{x0 : hostaddr}(REF_HOST_ADDR_val(x0)) = REF_HOST_ADDR_fieldval(x0)
  def $fieldval_val{x0 : ref}(REF_EXTERN_val(x0)) = REF_EXTERN_fieldval(x0)

;; test.spectec:4183.8-4183.16
relation wf_fieldval: `%`(fieldval)
  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_0{v_numtype : numtype, var_0 : num_}:
    `%`(CONST_fieldval(v_numtype, var_0))
    -- wf_num_: `%%`(v_numtype, var_0)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_1{v_vectype : vectype, var_0 : vec_}:
    `%`(VCONST_fieldval(v_vectype, var_0))
    -- wf_uN: `%%`($vsize(v_vectype), var_0)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_2{v_u31 : u31}:
    `%`(REF_I31_NUM_fieldval(v_u31))
    -- wf_uN: `%%`(31, v_u31)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_3:
    `%`(REF_NULL_ADDR_fieldval)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_4{v_structaddr : structaddr}:
    `%`(REF_STRUCT_ADDR_fieldval(v_structaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_5{v_arrayaddr : arrayaddr}:
    `%`(REF_ARRAY_ADDR_fieldval(v_arrayaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_6{v_funcaddr : funcaddr}:
    `%`(REF_FUNC_ADDR_fieldval(v_funcaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_7{v_exnaddr : exnaddr}:
    `%`(REF_EXN_ADDR_fieldval(v_exnaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_8{v_hostaddr : hostaddr}:
    `%`(REF_HOST_ADDR_fieldval(v_hostaddr))

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_9{v_ref : ref}:
    `%`(REF_EXTERN_fieldval(v_ref))
    -- wf_ref: `%`(v_ref)

  ;; test.spectec:4183.8-4183.16
  rule fieldval_case_10{v_packtype : packtype, var_0 : iN}:
    `%`(PACK_fieldval(v_packtype, var_0))
    -- wf_uN: `%%`($psize(v_packtype), var_0)

;; test.spectec:4186.1-4187.37
syntax structinst = 
{
  TYPE deftype,
  FIELDS fieldval*
}

;; test.spectec:4186.8-4186.18
relation wf_structinst: `%`(structinst)
  ;; test.spectec:4186.8-4186.18
  rule structinst_case_{var_0 : deftype, var_1_lst : fieldval*}:
    `%`({TYPE var_0, FIELDS var_1_lst})
    -- (wf_fieldval: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:4189.1-4190.37
syntax arrayinst = 
{
  TYPE deftype,
  FIELDS fieldval*
}

;; test.spectec:4189.8-4189.17
relation wf_arrayinst: `%`(arrayinst)
  ;; test.spectec:4189.8-4189.17
  rule arrayinst_case_{var_0 : deftype, var_1_lst : fieldval*}:
    `%`({TYPE var_0, FIELDS var_1_lst})
    -- (wf_fieldval: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:4192.1-4193.31
syntax exninst = 
{
  TAG tagaddr,
  FIELDS val*
}

;; test.spectec:4192.8-4192.15
relation wf_exninst: `%`(exninst)
  ;; test.spectec:4192.8-4192.15
  rule exninst_case_{var_0 : tagaddr, var_1_lst : val*}:
    `%`({TAG var_0, FIELDS var_1_lst})
    -- (wf_val: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:4210.1-4220.20
syntax store = 
{
  TAGS taginst*,
  GLOBALS globalinst*,
  MEMS meminst*,
  TABLES tableinst*,
  FUNCS funcinst*,
  DATAS datainst*,
  ELEMS eleminst*,
  STRUCTS structinst*,
  ARRAYS arrayinst*,
  EXNS exninst*
}

;; test.spectec:4210.8-4210.13
relation wf_store: `%`(store)
  ;; test.spectec:4210.8-4210.13
  rule store_case_{var_0_lst : taginst*, var_1_lst : globalinst*, var_2_lst : meminst*, var_3_lst : tableinst*, var_4_lst : funcinst*, var_5_lst : datainst*, var_6_lst : eleminst*, var_7_lst : structinst*, var_8_lst : arrayinst*, var_9_lst : exninst*}:
    `%`({TAGS var_0_lst, GLOBALS var_1_lst, MEMS var_2_lst, TABLES var_3_lst, FUNCS var_4_lst, DATAS var_5_lst, ELEMS var_6_lst, STRUCTS var_7_lst, ARRAYS var_8_lst, EXNS var_9_lst})
    -- (wf_taginst: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_globalinst: `%`(var_1))*{var_1 <- var_1_lst}
    -- (wf_meminst: `%`(var_2))*{var_2 <- var_2_lst}
    -- (wf_tableinst: `%`(var_3))*{var_3 <- var_3_lst}
    -- (wf_funcinst: `%`(var_4))*{var_4 <- var_4_lst}
    -- (wf_datainst: `%`(var_5))*{var_5 <- var_5_lst}
    -- (wf_eleminst: `%`(var_6))*{var_6 <- var_6_lst}
    -- (wf_structinst: `%`(var_7))*{var_7 <- var_7_lst}
    -- (wf_arrayinst: `%`(var_8))*{var_8 <- var_8_lst}
    -- (wf_exninst: `%`(var_9))*{var_9 <- var_9_lst}

;; test.spectec:4239.1-4239.47
syntax state = 
  | mk_state(v_store : store, v_frame : frame)

;; test.spectec:4239.8-4239.13
relation wf_state: `%`(state)
  ;; test.spectec:4239.8-4239.13
  rule state_case_0{v_store : store, v_frame : frame}:
    `%`(mk_state_state(v_store, v_frame))
    -- wf_store: `%`(v_store)
    -- wf_frame: `%`(v_frame)

;; test.spectec:4240.1-4240.57
syntax config = 
  | mk_config(v_state : state, instr_lst : instr*)

;; test.spectec:4240.8-4240.14
relation wf_config: `%`(config)
  ;; test.spectec:4240.8-4240.14
  rule config_case_0{v_state : state, instr_lst : instr*}:
    `%`(mk_config_config(v_state, instr_lst))
    -- wf_state: `%`(v_state)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

;; test.spectec:4267.1-4267.31
def $Ki : nat
  ;; test.spectec:4268.1-4268.15
  def $Ki = 1024

;; test.spectec:4273.1-4273.114
def $packfield__V128(v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__V128{v_val : val}(v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield__REF(REF_argument_0 : null?, REF_argument_1 : heaptype, v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__REF{null_opt : null?, v_heaptype : heaptype, v_val : val}(null_opt, v_heaptype, v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield__I8(v_val : val) : fieldval?
  ;; test.spectec:4277.1-4277.88
  def $packfield__I8{i : uN}(CONST_val(I32_numtype, mk_num__0_num_(I32_Inn, i))) = ?(PACK_fieldval(I8_packtype, $wrap__(32, $psize(I8_packtype), i)))
  def $packfield__I8{x0 : storagetype, x1 : val}(x1) = ?()
    -- otherwise

;; test.spectec:4273.1-4273.114
def $packfield__I64(v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__I64{v_val : val}(v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield__I32(v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__I32{v_val : val}(v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield__I16(v_val : val) : fieldval?
  ;; test.spectec:4277.1-4277.88
  def $packfield__I16{i : uN}(CONST_val(I32_numtype, mk_num__0_num_(I32_Inn, i))) = ?(PACK_fieldval(I16_packtype, $wrap__(32, $psize(I16_packtype), i)))
  def $packfield__I16{x0 : storagetype, x1 : val}(x1) = ?()
    -- otherwise

;; test.spectec:4273.1-4273.114
def $packfield__F64(v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__F64{v_val : val}(v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield__F32(v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__F32{v_val : val}(v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield__BOT(v_val : val) : fieldval?
  ;; test.spectec:4276.1-4276.36
  def $packfield__BOT{v_val : val}(v_val) = ?($fieldval_val(v_val))

;; test.spectec:4273.1-4273.114
def $packfield_(v_storagetype : storagetype, v_val : val) : fieldval?
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(V128_storagetype, v_val) = $packfield__V128(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{constructor_parameter_0 : null?, constructor_parameter_1 : heaptype, v_val : val}(REF_storagetype(constructor_parameter_0, constructor_parameter_1), v_val) = $packfield__REF(constructor_parameter_0, constructor_parameter_1, v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(I8_storagetype, v_val) = $packfield__I8(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(I64_storagetype, v_val) = $packfield__I64(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(I32_storagetype, v_val) = $packfield__I32(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(I16_storagetype, v_val) = $packfield__I16(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(F64_storagetype, v_val) = $packfield__F64(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(F32_storagetype, v_val) = $packfield__F32(v_val)
  ;; test.spectec:4273.6-4273.17
  def $packfield_{v_val : val}(BOT_storagetype, v_val) = $packfield__BOT(v_val)

;; test.spectec:4273.6-4273.17
relation packfield__is_wf: `%%%`(v_storagetype : storagetype, v_val : val, ret_val : fieldval)
  ;; test.spectec:4273.6-4273.17
  rule packfield__is_wf_0{v_storagetype : storagetype, v_val : val, ret_val : fieldval}:
    `%%%`(v_storagetype, v_val, ret_val)
    -- wf_storagetype: `%`(v_storagetype)
    -- wf_val: `%`(v_val)
    -- if ($packfield_(v_storagetype, v_val) =/= ?())
    -- if (ret_val = !($packfield_(v_storagetype, v_val)))
    -- wf_fieldval: `%`(ret_val)

;; test.spectec:4274.1-4274.126
def $unpackfield__V128(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_ref : ref}(?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_hostaddr : hostaddr}(?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_exnaddr : exnaddr}(?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_funcaddr : funcaddr}(?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_arrayaddr : arrayaddr}(?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_structaddr : structaddr}(?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128(?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_u31 : u31}(?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_vectype : vectype, var_1 : vec_}(?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__V128{v_numtype : numtype, var_0 : num_}(?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__V128{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__REF(REF_argument_0 : null?, REF_argument_1 : heaptype, var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_ref : ref, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_hostaddr : hostaddr, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_exnaddr : exnaddr, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_funcaddr : funcaddr, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_arrayaddr : arrayaddr, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_structaddr : structaddr, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_u31 : u31, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_vectype : vectype, var_1 : vec_, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__REF{v_numtype : numtype, var_0 : num_, null_opt : null?, v_heaptype : heaptype}(null_opt, v_heaptype, ?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__REF{constructor_parameter_0 : null?, constructor_parameter_1 : heaptype, x0 : storagetype, x1 : sx?, x2 : fieldval}(constructor_parameter_0, constructor_parameter_1, x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__I8(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4280.1-4280.100
  def $unpackfield__I8{v_sx : sx, i : uN}(?(v_sx), PACK_fieldval(I8_packtype, i)) = ?(CONST_val(I32_numtype, mk_num__0_num_(I32_Inn, $extend__($psize(I8_packtype), 32, v_sx, i))))
  def $unpackfield__I8{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__I64(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_ref : ref}(?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_hostaddr : hostaddr}(?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_exnaddr : exnaddr}(?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_funcaddr : funcaddr}(?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_arrayaddr : arrayaddr}(?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_structaddr : structaddr}(?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64(?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_u31 : u31}(?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_vectype : vectype, var_1 : vec_}(?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I64{v_numtype : numtype, var_0 : num_}(?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__I64{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__I32(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_ref : ref}(?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_hostaddr : hostaddr}(?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_exnaddr : exnaddr}(?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_funcaddr : funcaddr}(?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_arrayaddr : arrayaddr}(?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_structaddr : structaddr}(?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32(?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_u31 : u31}(?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_vectype : vectype, var_1 : vec_}(?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__I32{v_numtype : numtype, var_0 : num_}(?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__I32{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__I16(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4280.1-4280.100
  def $unpackfield__I16{v_sx : sx, i : uN}(?(v_sx), PACK_fieldval(I16_packtype, i)) = ?(CONST_val(I32_numtype, mk_num__0_num_(I32_Inn, $extend__($psize(I16_packtype), 32, v_sx, i))))
  def $unpackfield__I16{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__F64(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_ref : ref}(?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_hostaddr : hostaddr}(?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_exnaddr : exnaddr}(?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_funcaddr : funcaddr}(?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_arrayaddr : arrayaddr}(?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_structaddr : structaddr}(?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64(?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_u31 : u31}(?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_vectype : vectype, var_1 : vec_}(?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F64{v_numtype : numtype, var_0 : num_}(?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__F64{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__F32(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_ref : ref}(?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_hostaddr : hostaddr}(?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_exnaddr : exnaddr}(?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_funcaddr : funcaddr}(?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_arrayaddr : arrayaddr}(?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_structaddr : structaddr}(?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32(?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_u31 : u31}(?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_vectype : vectype, var_1 : vec_}(?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__F32{v_numtype : numtype, var_0 : num_}(?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__F32{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield__BOT(var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_ref : ref}(?(), REF_EXTERN_fieldval(v_ref)) = ?(REF_EXTERN_val(v_ref))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_hostaddr : hostaddr}(?(), REF_HOST_ADDR_fieldval(v_hostaddr)) = ?(REF_HOST_ADDR_val(v_hostaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_exnaddr : exnaddr}(?(), REF_EXN_ADDR_fieldval(v_exnaddr)) = ?(REF_EXN_ADDR_val(v_exnaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_funcaddr : funcaddr}(?(), REF_FUNC_ADDR_fieldval(v_funcaddr)) = ?(REF_FUNC_ADDR_val(v_funcaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_arrayaddr : arrayaddr}(?(), REF_ARRAY_ADDR_fieldval(v_arrayaddr)) = ?(REF_ARRAY_ADDR_val(v_arrayaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_structaddr : structaddr}(?(), REF_STRUCT_ADDR_fieldval(v_structaddr)) = ?(REF_STRUCT_ADDR_val(v_structaddr))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT(?(), REF_NULL_ADDR_fieldval) = ?(REF_NULL_ADDR_val)
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_u31 : u31}(?(), REF_I31_NUM_fieldval(v_u31)) = ?(REF_I31_NUM_val(v_u31))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_vectype : vectype, var_1 : vec_}(?(), VCONST_fieldval(v_vectype, var_1)) = ?(VCONST_val(v_vectype, var_1))
  ;; test.spectec:4279.1-4279.43
  def $unpackfield__BOT{v_numtype : numtype, var_0 : num_}(?(), CONST_fieldval(v_numtype, var_0)) = ?(CONST_val(v_numtype, var_0))
  def $unpackfield__BOT{x0 : storagetype, x1 : sx?, x2 : fieldval}(x1, x2) = ?()
    -- otherwise

;; test.spectec:4274.1-4274.126
def $unpackfield_(v_storagetype : storagetype, var_0_opt : sx?, v_fieldval : fieldval) : val?
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(V128_storagetype, var_0_opt, v_fieldval) = $unpackfield__V128(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{constructor_parameter_0 : null?, constructor_parameter_1 : heaptype, var_0_opt : sx?, v_fieldval : fieldval}(REF_storagetype(constructor_parameter_0, constructor_parameter_1), var_0_opt, v_fieldval) = $unpackfield__REF(constructor_parameter_0, constructor_parameter_1, var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(I8_storagetype, var_0_opt, v_fieldval) = $unpackfield__I8(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(I64_storagetype, var_0_opt, v_fieldval) = $unpackfield__I64(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(I32_storagetype, var_0_opt, v_fieldval) = $unpackfield__I32(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(I16_storagetype, var_0_opt, v_fieldval) = $unpackfield__I16(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(F64_storagetype, var_0_opt, v_fieldval) = $unpackfield__F64(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(F32_storagetype, var_0_opt, v_fieldval) = $unpackfield__F32(var_0_opt, v_fieldval)
  ;; test.spectec:4274.6-4274.19
  def $unpackfield_{var_0_opt : sx?, v_fieldval : fieldval}(BOT_storagetype, var_0_opt, v_fieldval) = $unpackfield__BOT(var_0_opt, v_fieldval)

;; test.spectec:4274.6-4274.19
relation unpackfield__is_wf: `%%%%`(v_storagetype : storagetype, var_0_opt : sx?, v_fieldval : fieldval, ret_val : val)
  ;; test.spectec:4274.6-4274.19
  rule unpackfield__is_wf_0{v_storagetype : storagetype, var_0_opt : sx?, v_fieldval : fieldval, ret_val : val}:
    `%%%%`(v_storagetype, var_0_opt, v_fieldval, ret_val)
    -- wf_storagetype: `%`(v_storagetype)
    -- wf_fieldval: `%`(v_fieldval)
    -- if ($unpackfield_(v_storagetype, var_0_opt, v_fieldval) =/= ?())
    -- if (ret_val = !($unpackfield_(v_storagetype, var_0_opt, v_fieldval)))
    -- wf_val: `%`(ret_val)

;; test.spectec:4285.1-4285.86
rec {

;; test.spectec:4285.6-4285.13
relation fun_tagsxa: `%%`(externaddr*, tagaddr*)
  ;; test.spectec:4285.6-4285.13
  rule fun_tagsxa_case_0:
    `%%`([], [])

  ;; test.spectec:4285.6-4285.13
  rule fun_tagsxa_case_1{a : nat, xa_lst : externaddr*, var_0 : tagaddr*}:
    `%%`([TAG_externaddr(a)] ++ xa_lst, [a] ++ var_0)
    -- fun_tagsxa: `%%`(xa_lst, var_0)

  ;; test.spectec:4285.6-4285.13
  rule fun_tagsxa_case_2{v_externaddr : externaddr, xa_lst : externaddr*, var_0 : tagaddr*}:
    `%%`([v_externaddr] ++ xa_lst, var_0)
    -- fun_tagsxa: `%%`(xa_lst, var_0)
}

;; test.spectec:4286.1-4286.89
rec {

;; test.spectec:4286.6-4286.16
relation fun_globalsxa: `%%`(externaddr*, globaladdr*)
  ;; test.spectec:4286.6-4286.16
  rule fun_globalsxa_case_0:
    `%%`([], [])

  ;; test.spectec:4286.6-4286.16
  rule fun_globalsxa_case_1{a : nat, xa_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([GLOBAL_externaddr(a)] ++ xa_lst, [a] ++ var_0)
    -- fun_globalsxa: `%%`(xa_lst, var_0)

  ;; test.spectec:4286.6-4286.16
  rule fun_globalsxa_case_2{v_externaddr : externaddr, xa_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([v_externaddr] ++ xa_lst, var_0)
    -- fun_globalsxa: `%%`(xa_lst, var_0)
}

;; test.spectec:4287.1-4287.86
rec {

;; test.spectec:4287.6-4287.13
relation fun_memsxa: `%%`(externaddr*, memaddr*)
  ;; test.spectec:4287.6-4287.13
  rule fun_memsxa_case_0:
    `%%`([], [])

  ;; test.spectec:4287.6-4287.13
  rule fun_memsxa_case_1{a : nat, xa_lst : externaddr*, var_0 : memaddr*}:
    `%%`([MEM_externaddr(a)] ++ xa_lst, [a] ++ var_0)
    -- fun_memsxa: `%%`(xa_lst, var_0)

  ;; test.spectec:4287.6-4287.13
  rule fun_memsxa_case_2{v_externaddr : externaddr, xa_lst : externaddr*, var_0 : memaddr*}:
    `%%`([v_externaddr] ++ xa_lst, var_0)
    -- fun_memsxa: `%%`(xa_lst, var_0)
}

;; test.spectec:4288.1-4288.88
rec {

;; test.spectec:4288.6-4288.15
relation fun_tablesxa: `%%`(externaddr*, tableaddr*)
  ;; test.spectec:4288.6-4288.15
  rule fun_tablesxa_case_0:
    `%%`([], [])

  ;; test.spectec:4288.6-4288.15
  rule fun_tablesxa_case_1{a : nat, xa_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([TABLE_externaddr(a)] ++ xa_lst, [a] ++ var_0)
    -- fun_tablesxa: `%%`(xa_lst, var_0)

  ;; test.spectec:4288.6-4288.15
  rule fun_tablesxa_case_2{v_externaddr : externaddr, xa_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([v_externaddr] ++ xa_lst, var_0)
    -- fun_tablesxa: `%%`(xa_lst, var_0)
}

;; test.spectec:4289.1-4289.87
rec {

;; test.spectec:4289.6-4289.14
relation fun_funcsxa: `%%`(externaddr*, funcaddr*)
  ;; test.spectec:4289.6-4289.14
  rule fun_funcsxa_case_0:
    `%%`([], [])

  ;; test.spectec:4289.6-4289.14
  rule fun_funcsxa_case_1{a : nat, xa_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([FUNC_externaddr(a)] ++ xa_lst, [a] ++ var_0)
    -- fun_funcsxa: `%%`(xa_lst, var_0)

  ;; test.spectec:4289.6-4289.14
  rule fun_funcsxa_case_2{v_externaddr : externaddr, xa_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([v_externaddr] ++ xa_lst, var_0)
    -- fun_funcsxa: `%%`(xa_lst, var_0)
}

;; test.spectec:4314.1-4314.74
def $fun_store(v_state : state) : store
  ;; test.spectec:4317.1-4317.23
  def $fun_store{s : store, f : frame}(mk_state_state(s, f)) = s

;; test.spectec:4314.6-4314.12
relation store_is_wf: `%%`(v_state : state, ret_val : store)
  ;; test.spectec:4314.6-4314.12
  rule store_is_wf_0{v_state : state, ret_val : store}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fun_store(v_state))
    -- wf_store: `%`(ret_val)

;; test.spectec:4315.1-4315.74
def $fun_frame(v_state : state) : frame
  ;; test.spectec:4318.1-4318.23
  def $fun_frame{s : store, f : frame}(mk_state_state(s, f)) = f

;; test.spectec:4315.6-4315.12
relation frame_is_wf: `%%`(v_state : state, ret_val : frame)
  ;; test.spectec:4315.6-4315.12
  rule frame_is_wf_0{v_state : state, ret_val : frame}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fun_frame(v_state))
    -- wf_frame: `%`(ret_val)

;; test.spectec:4320.1-4320.80
def $fun_tagaddr(v_state : state) : tagaddr*
  ;; test.spectec:4321.1-4321.37
  def $fun_tagaddr{s : store, f : frame}(mk_state_state(s, f)) = f.MODULE_frame.TAGS_moduleinst

;; test.spectec:4323.1-4323.76
def $fun_moduleinst(v_state : state) : moduleinst
  ;; test.spectec:4335.1-4335.35
  def $fun_moduleinst{s : store, f : frame}(mk_state_state(s, f)) = f.MODULE_frame

;; test.spectec:4323.6-4323.17
relation moduleinst_is_wf: `%%`(v_state : state, ret_val : moduleinst)
  ;; test.spectec:4323.6-4323.17
  rule moduleinst_is_wf_0{v_state : state, ret_val : moduleinst}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fun_moduleinst(v_state))
    -- wf_moduleinst: `%`(ret_val)

;; test.spectec:4324.1-4324.76
def $fun_taginst(v_state : state) : taginst*
  ;; test.spectec:4336.1-4336.30
  def $fun_taginst{s : store, f : frame}(mk_state_state(s, f)) = s.TAGS_store

;; test.spectec:4324.6-4324.14
relation taginst_is_wf: `%%`(v_state : state, ret_val_lst : taginst*)
  ;; test.spectec:4324.6-4324.14
  rule taginst_is_wf_0{v_state : state, ret_val_lst : taginst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_taginst(v_state))
    -- (wf_taginst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4325.1-4325.76
def $fun_globalinst(v_state : state) : globalinst*
  ;; test.spectec:4337.1-4337.36
  def $fun_globalinst{s : store, f : frame}(mk_state_state(s, f)) = s.GLOBALS_store

;; test.spectec:4325.6-4325.17
relation globalinst_is_wf: `%%`(v_state : state, ret_val_lst : globalinst*)
  ;; test.spectec:4325.6-4325.17
  rule globalinst_is_wf_0{v_state : state, ret_val_lst : globalinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_globalinst(v_state))
    -- (wf_globalinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4326.1-4326.76
def $fun_meminst(v_state : state) : meminst*
  ;; test.spectec:4338.1-4338.30
  def $fun_meminst{s : store, f : frame}(mk_state_state(s, f)) = s.MEMS_store

;; test.spectec:4326.6-4326.14
relation meminst_is_wf: `%%`(v_state : state, ret_val_lst : meminst*)
  ;; test.spectec:4326.6-4326.14
  rule meminst_is_wf_0{v_state : state, ret_val_lst : meminst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_meminst(v_state))
    -- (wf_meminst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4327.1-4327.76
def $fun_tableinst(v_state : state) : tableinst*
  ;; test.spectec:4339.1-4339.34
  def $fun_tableinst{s : store, f : frame}(mk_state_state(s, f)) = s.TABLES_store

;; test.spectec:4327.6-4327.16
relation tableinst_is_wf: `%%`(v_state : state, ret_val_lst : tableinst*)
  ;; test.spectec:4327.6-4327.16
  rule tableinst_is_wf_0{v_state : state, ret_val_lst : tableinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_tableinst(v_state))
    -- (wf_tableinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4328.1-4328.76
def $fun_funcinst(v_state : state) : funcinst*
  ;; test.spectec:4340.1-4340.32
  def $fun_funcinst{s : store, f : frame}(mk_state_state(s, f)) = s.FUNCS_store

;; test.spectec:4328.6-4328.15
relation funcinst_is_wf: `%%`(v_state : state, ret_val_lst : funcinst*)
  ;; test.spectec:4328.6-4328.15
  rule funcinst_is_wf_0{v_state : state, ret_val_lst : funcinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_funcinst(v_state))
    -- (wf_funcinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4329.1-4329.76
def $fun_datainst(v_state : state) : datainst*
  ;; test.spectec:4341.1-4341.32
  def $fun_datainst{s : store, f : frame}(mk_state_state(s, f)) = s.DATAS_store

;; test.spectec:4329.6-4329.15
relation datainst_is_wf: `%%`(v_state : state, ret_val_lst : datainst*)
  ;; test.spectec:4329.6-4329.15
  rule datainst_is_wf_0{v_state : state, ret_val_lst : datainst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_datainst(v_state))
    -- (wf_datainst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4330.1-4330.76
def $fun_eleminst(v_state : state) : eleminst*
  ;; test.spectec:4342.1-4342.32
  def $fun_eleminst{s : store, f : frame}(mk_state_state(s, f)) = s.ELEMS_store

;; test.spectec:4330.6-4330.15
relation eleminst_is_wf: `%%`(v_state : state, ret_val_lst : eleminst*)
  ;; test.spectec:4330.6-4330.15
  rule eleminst_is_wf_0{v_state : state, ret_val_lst : eleminst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_eleminst(v_state))
    -- (wf_eleminst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4331.1-4331.76
def $fun_structinst(v_state : state) : structinst*
  ;; test.spectec:4343.1-4343.36
  def $fun_structinst{s : store, f : frame}(mk_state_state(s, f)) = s.STRUCTS_store

;; test.spectec:4331.6-4331.17
relation structinst_is_wf: `%%`(v_state : state, ret_val_lst : structinst*)
  ;; test.spectec:4331.6-4331.17
  rule structinst_is_wf_0{v_state : state, ret_val_lst : structinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_structinst(v_state))
    -- (wf_structinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4332.1-4332.76
def $fun_arrayinst(v_state : state) : arrayinst*
  ;; test.spectec:4344.1-4344.34
  def $fun_arrayinst{s : store, f : frame}(mk_state_state(s, f)) = s.ARRAYS_store

;; test.spectec:4332.6-4332.16
relation arrayinst_is_wf: `%%`(v_state : state, ret_val_lst : arrayinst*)
  ;; test.spectec:4332.6-4332.16
  rule arrayinst_is_wf_0{v_state : state, ret_val_lst : arrayinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_arrayinst(v_state))
    -- (wf_arrayinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4333.1-4333.76
def $fun_exninst(v_state : state) : exninst*
  ;; test.spectec:4345.1-4345.30
  def $fun_exninst{s : store, f : frame}(mk_state_state(s, f)) = s.EXNS_store

;; test.spectec:4333.6-4333.14
relation exninst_is_wf: `%%`(v_state : state, ret_val_lst : exninst*)
  ;; test.spectec:4333.6-4333.14
  rule exninst_is_wf_0{v_state : state, ret_val_lst : exninst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_exninst(v_state))
    -- (wf_exninst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:4359.1-4359.38
def $fof(v_state : state) : frame
  ;; test.spectec:4362.1-4362.24
  def $fof{z : state}(z) = $fun_frame(z)

;; test.spectec:4359.6-4359.10
relation fof_is_wf: `%%`(v_state : state, ret_val : frame)
  ;; test.spectec:4359.6-4359.10
  rule fof_is_wf_0{v_state : state, ret_val : frame}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fof(v_state))
    -- wf_frame: `%`(ret_val)

;; test.spectec:4348.1-4348.85
def $fun_type(v_state : state, v_typeidx : typeidx) : deftype
  ;; test.spectec:4364.1-4364.42
  def $fun_type{z : state, x : uN}(z, x) = $fof(z).MODULE_frame.TYPES_moduleinst[$proj_uN_0(x).0]

;; test.spectec:4358.1-4358.38
def $sof(v_state : state) : store
  ;; test.spectec:4361.1-4361.24
  def $sof{z : state}(z) = $fun_store(z)

;; test.spectec:4358.6-4358.10
relation sof_is_wf: `%%`(v_state : state, ret_val : store)
  ;; test.spectec:4358.6-4358.10
  rule sof_is_wf_0{v_state : state, ret_val : store}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $sof(v_state))
    -- wf_store: `%`(ret_val)

;; test.spectec:4349.1-4349.85
def $fun_tag(v_state : state, v_tagidx : tagidx) : taginst
  ;; test.spectec:4365.1-4365.54
  def $fun_tag{z : state, x : uN}(z, x) = $sof(z).TAGS_store[$fof(z).MODULE_frame.TAGS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4349.6-4349.10
relation tag_is_wf: `%%%`(v_state : state, v_tagidx : tagidx, ret_val : taginst)
  ;; test.spectec:4349.6-4349.10
  rule tag_is_wf_0{v_state : state, v_tagidx : tagidx, ret_val : taginst}:
    `%%%`(v_state, v_tagidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tagidx)
    -- if (ret_val = $fun_tag(v_state, v_tagidx))
    -- wf_taginst: `%`(ret_val)

;; test.spectec:4350.1-4350.85
def $fun_global(v_state : state, v_globalidx : globalidx) : globalinst
  ;; test.spectec:4366.1-4366.63
  def $fun_global{z : state, x : uN}(z, x) = $sof(z).GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4350.6-4350.13
relation global_is_wf: `%%%`(v_state : state, v_globalidx : globalidx, ret_val : globalinst)
  ;; test.spectec:4350.6-4350.13
  rule global_is_wf_0{v_state : state, v_globalidx : globalidx, ret_val : globalinst}:
    `%%%`(v_state, v_globalidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_globalidx)
    -- if (ret_val = $fun_global(v_state, v_globalidx))
    -- wf_globalinst: `%`(ret_val)

;; test.spectec:4351.1-4351.85
def $fun_mem(v_state : state, v_memidx : memidx) : meminst
  ;; test.spectec:4367.1-4367.54
  def $fun_mem{z : state, x : uN}(z, x) = $sof(z).MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4351.6-4351.10
relation mem_is_wf: `%%%`(v_state : state, v_memidx : memidx, ret_val : meminst)
  ;; test.spectec:4351.6-4351.10
  rule mem_is_wf_0{v_state : state, v_memidx : memidx, ret_val : meminst}:
    `%%%`(v_state, v_memidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_memidx)
    -- if (ret_val = $fun_mem(v_state, v_memidx))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:4352.1-4352.85
def $fun_table(v_state : state, v_tableidx : tableidx) : tableinst
  ;; test.spectec:4368.1-4368.60
  def $fun_table{z : state, x : uN}(z, x) = $sof(z).TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4352.6-4352.12
relation table_is_wf: `%%%`(v_state : state, v_tableidx : tableidx, ret_val : tableinst)
  ;; test.spectec:4352.6-4352.12
  rule table_is_wf_0{v_state : state, v_tableidx : tableidx, ret_val : tableinst}:
    `%%%`(v_state, v_tableidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- if (ret_val = $fun_table(v_state, v_tableidx))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:4353.1-4353.85
def $fun_func(v_state : state, v_funcidx : funcidx) : funcinst
  ;; test.spectec:4369.1-4369.57
  def $fun_func{z : state, x : uN}(z, x) = $sof(z).FUNCS_store[$fof(z).MODULE_frame.FUNCS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4353.6-4353.11
relation func_is_wf: `%%%`(v_state : state, v_funcidx : funcidx, ret_val : funcinst)
  ;; test.spectec:4353.6-4353.11
  rule func_is_wf_0{v_state : state, v_funcidx : funcidx, ret_val : funcinst}:
    `%%%`(v_state, v_funcidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_funcidx)
    -- if (ret_val = $fun_func(v_state, v_funcidx))
    -- wf_funcinst: `%`(ret_val)

;; test.spectec:4354.1-4354.85
def $fun_data(v_state : state, v_dataidx : dataidx) : datainst
  ;; test.spectec:4370.1-4370.57
  def $fun_data{z : state, x : uN}(z, x) = $sof(z).DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4354.6-4354.11
relation data_is_wf: `%%%`(v_state : state, v_dataidx : dataidx, ret_val : datainst)
  ;; test.spectec:4354.6-4354.11
  rule data_is_wf_0{v_state : state, v_dataidx : dataidx, ret_val : datainst}:
    `%%%`(v_state, v_dataidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_dataidx)
    -- if (ret_val = $fun_data(v_state, v_dataidx))
    -- wf_datainst: `%`(ret_val)

;; test.spectec:4355.1-4355.85
def $fun_elem(v_state : state, v_tableidx : tableidx) : eleminst
  ;; test.spectec:4371.1-4371.57
  def $fun_elem{z : state, x : uN}(z, x) = $sof(z).ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:4355.6-4355.11
relation elem_is_wf: `%%%`(v_state : state, v_tableidx : tableidx, ret_val : eleminst)
  ;; test.spectec:4355.6-4355.11
  rule elem_is_wf_0{v_state : state, v_tableidx : tableidx, ret_val : eleminst}:
    `%%%`(v_state, v_tableidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- if (ret_val = $fun_elem(v_state, v_tableidx))
    -- wf_eleminst: `%`(ret_val)

;; test.spectec:4356.1-4356.85
def $fun_local(v_state : state, v_localidx : localidx) : val?
  ;; test.spectec:4372.1-4372.37
  def $fun_local{z : state, x : uN}(z, x) = $fof(z).LOCALS_frame[$proj_uN_0(x).0]

;; test.spectec:4356.6-4356.12
relation local_is_wf: `%%%`(v_state : state, v_localidx : localidx, ret_val_opt : val?)
  ;; test.spectec:4356.6-4356.12
  rule local_is_wf_0{v_state : state, v_localidx : localidx, ret_val_opt : val?}:
    `%%%`(v_state, v_localidx, ret_val_opt)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_localidx)
    -- if (ret_val_opt = $fun_local(v_state, v_localidx))
    -- (wf_val: `%`(ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:4377.1-4377.165
def $with_local(v_state : state, v_localidx : localidx, v_val : val) : state
  ;; test.spectec:4388.1-4388.60
  def $with_local{z : state, x : uN, v : val}(z, x, v) = mk_state_state($sof(z), $fof(z)[LOCALS_frame[$proj_uN_0(x).0] = ?(v)])

;; test.spectec:4377.6-4377.17
relation with_local_is_wf: `%%%%`(v_state : state, v_localidx : localidx, v_val : val, ret_val : state)
  ;; test.spectec:4377.6-4377.17
  rule with_local_is_wf_0{v_state : state, v_localidx : localidx, v_val : val, ret_val : state}:
    `%%%%`(v_state, v_localidx, v_val, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_localidx)
    -- wf_val: `%`(v_val)
    -- if (ret_val = $with_local(v_state, v_localidx, v_val))
    -- wf_state: `%`(ret_val)

;; test.spectec:4378.1-4378.172
def $with_global(v_state : state, v_globalidx : globalidx, v_val : val) : state
  ;; test.spectec:4389.1-4389.92
  def $with_global{z : state, x : uN, v : val}(z, x, v) = mk_state_state($sof(z)[GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]].VALUE_globalinst = v], $fof(z))

;; test.spectec:4378.6-4378.18
relation with_global_is_wf: `%%%%`(v_state : state, v_globalidx : globalidx, v_val : val, ret_val : state)
  ;; test.spectec:4378.6-4378.18
  rule with_global_is_wf_0{v_state : state, v_globalidx : globalidx, v_val : val, ret_val : state}:
    `%%%%`(v_state, v_globalidx, v_val, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_globalidx)
    -- wf_val: `%`(v_val)
    -- if (ret_val = $with_global(v_state, v_globalidx, v_val))
    -- wf_state: `%`(ret_val)

;; test.spectec:4379.1-4379.174
def $with_table(v_state : state, v_tableidx : tableidx, nat : nat, v_ref : ref) : state
  ;; test.spectec:4390.1-4390.94
  def $with_table{z : state, x : uN, i : nat, r : ref}(z, x, i, r) = mk_state_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]].REFS_tableinst[i] = r], $fof(z))

;; test.spectec:4379.6-4379.17
relation with_table_is_wf: `%%%%%`(v_state : state, v_tableidx : tableidx, nat : nat, v_ref : ref, ret_val : state)
  ;; test.spectec:4379.6-4379.17
  rule with_table_is_wf_0{v_state : state, v_tableidx : tableidx, nat : nat, v_ref : ref, ret_val : state}:
    `%%%%%`(v_state, v_tableidx, nat, v_ref, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_ref: `%`(v_ref)
    -- if (ret_val = $with_table(v_state, v_tableidx, nat, v_ref))
    -- wf_state: `%`(ret_val)

;; test.spectec:4380.1-4380.165
def $with_tableinst(v_state : state, v_tableidx : tableidx, v_tableinst : tableinst) : state
  ;; test.spectec:4391.1-4391.89
  def $with_tableinst{z : state, x : uN, ti : tableinst}(z, x, ti) = mk_state_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]] = ti], $fof(z))

;; test.spectec:4380.6-4380.21
relation with_tableinst_is_wf: `%%%%`(v_state : state, v_tableidx : tableidx, v_tableinst : tableinst, ret_val : state)
  ;; test.spectec:4380.6-4380.21
  rule with_tableinst_is_wf_0{v_state : state, v_tableidx : tableidx, v_tableinst : tableinst, ret_val : state}:
    `%%%%`(v_state, v_tableidx, v_tableinst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_tableinst: `%`(v_tableinst)
    -- if (ret_val = $with_tableinst(v_state, v_tableidx, v_tableinst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4381.1-4381.176
def $with_mem(v_state : state, v_memidx : memidx, nat : nat, nat_0 : nat, var_0_lst : byte*) : state
  ;; test.spectec:4392.1-4392.98
  def $with_mem{z : state, x : uN, i : nat, j : nat, b_lst : byte*}(z, x, i, j, b_lst) = mk_state_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]].BYTES_meminst[i : j] = b_lst], $fof(z))

;; test.spectec:4381.6-4381.15
relation with_mem_is_wf: `%%%%%%`(v_state : state, v_memidx : memidx, nat : nat, nat_0 : nat, var_0_lst : byte*, ret_val : state)
  ;; test.spectec:4381.6-4381.15
  rule with_mem_is_wf_0{v_state : state, v_memidx : memidx, nat : nat, nat_0 : nat, var_0_lst : byte*, ret_val : state}:
    `%%%%%%`(v_state, v_memidx, nat, nat_0, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_memidx)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $with_mem(v_state, v_memidx, nat, nat_0, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4382.1-4382.167
def $with_meminst(v_state : state, v_memidx : memidx, v_meminst : meminst) : state
  ;; test.spectec:4393.1-4393.83
  def $with_meminst{z : state, x : uN, mi : meminst}(z, x, mi) = mk_state_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]] = mi], $fof(z))

;; test.spectec:4382.6-4382.19
relation with_meminst_is_wf: `%%%%`(v_state : state, v_memidx : memidx, v_meminst : meminst, ret_val : state)
  ;; test.spectec:4382.6-4382.19
  rule with_meminst_is_wf_0{v_state : state, v_memidx : memidx, v_meminst : meminst, ret_val : state}:
    `%%%%`(v_state, v_memidx, v_meminst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_meminst: `%`(v_meminst)
    -- if (ret_val = $with_meminst(v_state, v_memidx, v_meminst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4383.1-4383.169
def $with_elem(v_state : state, v_elemidx : elemidx, var_0_lst : ref*) : state
  ;; test.spectec:4394.1-4394.87
  def $with_elem{z : state, x : uN, r_lst : ref*}(z, x, r_lst) = mk_state_state($sof(z)[ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[$proj_uN_0(x).0]].REFS_eleminst = r_lst], $fof(z))

;; test.spectec:4383.6-4383.16
relation with_elem_is_wf: `%%%%`(v_state : state, v_elemidx : elemidx, var_0_lst : ref*, ret_val : state)
  ;; test.spectec:4383.6-4383.16
  rule with_elem_is_wf_0{v_state : state, v_elemidx : elemidx, var_0_lst : ref*, ret_val : state}:
    `%%%%`(v_state, v_elemidx, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_elemidx)
    -- (wf_ref: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $with_elem(v_state, v_elemidx, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4384.1-4384.170
def $with_data(v_state : state, v_dataidx : dataidx, var_0_lst : byte*) : state
  ;; test.spectec:4395.1-4395.88
  def $with_data{z : state, x : uN, b_lst : byte*}(z, x, b_lst) = mk_state_state($sof(z)[DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[$proj_uN_0(x).0]].BYTES_datainst = b_lst], $fof(z))

;; test.spectec:4384.6-4384.16
relation with_data_is_wf: `%%%%`(v_state : state, v_dataidx : dataidx, var_0_lst : byte*, ret_val : state)
  ;; test.spectec:4384.6-4384.16
  rule with_data_is_wf_0{v_state : state, v_dataidx : dataidx, var_0_lst : byte*, ret_val : state}:
    `%%%%`(v_state, v_dataidx, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_dataidx)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $with_data(v_state, v_dataidx, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4385.1-4385.181
def $with_struct(v_state : state, v_structaddr : structaddr, nat : nat, v_fieldval : fieldval) : state
  ;; test.spectec:4396.1-4396.77
  def $with_struct{z : state, a : nat, i : nat, fv : fieldval}(z, a, i, fv) = mk_state_state($sof(z)[STRUCTS_store[a].FIELDS_structinst[i] = fv], $fof(z))

;; test.spectec:4385.6-4385.18
relation with_struct_is_wf: `%%%%%`(v_state : state, v_structaddr : structaddr, nat : nat, v_fieldval : fieldval, ret_val : state)
  ;; test.spectec:4385.6-4385.18
  rule with_struct_is_wf_0{v_state : state, v_structaddr : structaddr, nat : nat, v_fieldval : fieldval, ret_val : state}:
    `%%%%%`(v_state, v_structaddr, nat, v_fieldval, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_fieldval: `%`(v_fieldval)
    -- if (ret_val = $with_struct(v_state, v_structaddr, nat, v_fieldval))
    -- wf_state: `%`(ret_val)

;; test.spectec:4386.1-4386.180
def $with_array(v_state : state, v_arrayaddr : arrayaddr, nat : nat, v_fieldval : fieldval) : state
  ;; test.spectec:4397.1-4397.75
  def $with_array{z : state, a : nat, i : nat, fv : fieldval}(z, a, i, fv) = mk_state_state($sof(z)[ARRAYS_store[a].FIELDS_arrayinst[i] = fv], $fof(z))

;; test.spectec:4386.6-4386.17
relation with_array_is_wf: `%%%%%`(v_state : state, v_arrayaddr : arrayaddr, nat : nat, v_fieldval : fieldval, ret_val : state)
  ;; test.spectec:4386.6-4386.17
  rule with_array_is_wf_0{v_state : state, v_arrayaddr : arrayaddr, nat : nat, v_fieldval : fieldval, ret_val : state}:
    `%%%%%`(v_state, v_arrayaddr, nat, v_fieldval, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_fieldval: `%`(v_fieldval)
    -- if (ret_val = $with_array(v_state, v_arrayaddr, nat, v_fieldval))
    -- wf_state: `%`(ret_val)

;; test.spectec:4400.1-4400.140
def $add_structinst(v_state : state, var_0_lst : structinst*) : state
  ;; test.spectec:4404.1-4404.65
  def $add_structinst{z : state, si_lst : structinst*}(z, si_lst) = mk_state_state($sof(z)[STRUCTS_store =++ si_lst], $fof(z))

;; test.spectec:4400.6-4400.21
relation add_structinst_is_wf: `%%%`(v_state : state, var_0_lst : structinst*, ret_val : state)
  ;; test.spectec:4400.6-4400.21
  rule add_structinst_is_wf_0{v_state : state, var_0_lst : structinst*, ret_val : state}:
    `%%%`(v_state, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- (wf_structinst: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $add_structinst(v_state, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4401.1-4401.139
def $add_arrayinst(v_state : state, var_0_lst : arrayinst*) : state
  ;; test.spectec:4405.1-4405.63
  def $add_arrayinst{z : state, ai_lst : arrayinst*}(z, ai_lst) = mk_state_state($sof(z)[ARRAYS_store =++ ai_lst], $fof(z))

;; test.spectec:4401.6-4401.20
relation add_arrayinst_is_wf: `%%%`(v_state : state, var_0_lst : arrayinst*, ret_val : state)
  ;; test.spectec:4401.6-4401.20
  rule add_arrayinst_is_wf_0{v_state : state, var_0_lst : arrayinst*, ret_val : state}:
    `%%%`(v_state, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- (wf_arrayinst: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $add_arrayinst(v_state, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4402.1-4402.137
def $add_exninst(v_state : state, var_0_lst : exninst*) : state
  ;; test.spectec:4406.1-4406.61
  def $add_exninst{z : state, exn_lst : exninst*}(z, exn_lst) = mk_state_state($sof(z)[EXNS_store =++ exn_lst], $fof(z))

;; test.spectec:4402.6-4402.18
relation add_exninst_is_wf: `%%%`(v_state : state, var_0_lst : exninst*, ret_val : state)
  ;; test.spectec:4402.6-4402.18
  rule add_exninst_is_wf_0{v_state : state, var_0_lst : exninst*, ret_val : state}:
    `%%%`(v_state, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- (wf_exninst: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $add_exninst(v_state, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:4411.6-4411.16
relation fun_growtable_before_fun_growtable_case_1: `%%%`(tableinst, nat, ref)
  ;; test.spectec:4411.6-4411.16
  rule fun_growtable_case_0{v_tableinst : tableinst, v_n : nat, r : ref, tableinst' : tableinst, i' : uN, at : addrtype, i : u64, j_opt : u64?, rt : reftype, r'_lst : ref*}:
    `%%%`(v_tableinst, v_n, r)
    -- if ({TYPE mk_tabletype_tabletype(at, mk_limits_limits(i, j_opt), rt), REFS r'_lst} = v_tableinst)
    -- if (tableinst' = {TYPE mk_tabletype_tabletype(at, mk_limits_limits(i', j_opt), rt), REFS r'_lst ++ r^v_n{}})
    -- if ($proj_uN_0(i').0 = (|r'_lst| + v_n))
    -- (if ($proj_uN_0(i').0 <= $proj_uN_0(j_3).0))?{j_3 <- j_opt}
    -- if (($proj_uN_0(i').0 : nat <:> int) <= (((2 ^ $size($numtype_addrtype(at))) : nat <:> int) - (1 : nat <:> int)))
    -- wf_tableinst: `%`({TYPE mk_tabletype_tabletype(at, mk_limits_limits(i, j_opt), rt), REFS r'_lst})
    -- wf_tableinst: `%`({TYPE mk_tabletype_tabletype(at, mk_limits_limits(i', j_opt), rt), REFS r'_lst ++ r^v_n{}})

;; test.spectec:4411.6-4411.16
relation fun_growtable: `%%%%`(tableinst, nat, ref, tableinst?)
  ;; test.spectec:4411.6-4411.16
  rule fun_growtable_case_0{v_tableinst : tableinst, v_n : nat, r : ref, tableinst' : tableinst, i' : uN, at : addrtype, i : u64, j_opt : u64?, rt : reftype, r'_lst : ref*}:
    `%%%%`(v_tableinst, v_n, r, ?(tableinst'))
    -- if ({TYPE mk_tabletype_tabletype(at, mk_limits_limits(i, j_opt), rt), REFS r'_lst} = v_tableinst)
    -- if (tableinst' = {TYPE mk_tabletype_tabletype(at, mk_limits_limits(i', j_opt), rt), REFS r'_lst ++ r^v_n{}})
    -- if ($proj_uN_0(i').0 = (|r'_lst| + v_n))
    -- (if ($proj_uN_0(i').0 <= $proj_uN_0(j_3).0))?{j_3 <- j_opt}
    -- if (($proj_uN_0(i').0 : nat <:> int) <= (((2 ^ $size($numtype_addrtype(at))) : nat <:> int) - (1 : nat <:> int)))
    -- wf_tableinst: `%`({TYPE mk_tabletype_tabletype(at, mk_limits_limits(i, j_opt), rt), REFS r'_lst})
    -- wf_tableinst: `%`({TYPE mk_tabletype_tabletype(at, mk_limits_limits(i', j_opt), rt), REFS r'_lst ++ r^v_n{}})

  ;; test.spectec:4411.6-4411.16
  rule fun_growtable_case_1{x0 : tableinst, x1 : nat, x2 : ref}:
    `%%%%`(x0, x1, x2, ?())
    -- ~ fun_growtable_before_fun_growtable_case_1: `%%%`(x0, x1, x2)

;; test.spectec:4411.6-4411.16
relation growtable_is_wf: `%%%%`(v_tableinst : tableinst, nat : nat, v_ref : ref, ret_val : tableinst)
  ;; test.spectec:4411.6-4411.16
  rule growtable_is_wf_0{v_tableinst : tableinst, nat : nat, v_ref : ref, ret_val : tableinst, var_0 : tableinst?}:
    `%%%%`(v_tableinst, nat, v_ref, ret_val)
    -- fun_growtable: `%%%%`(v_tableinst, nat, v_ref, var_0)
    -- wf_tableinst: `%`(v_tableinst)
    -- wf_ref: `%`(v_ref)
    -- if (var_0 =/= ?())
    -- if (ret_val = !(var_0))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:4412.6-4412.14
relation fun_growmem_before_fun_growmem_case_1: `%%`(meminst, nat)
  ;; test.spectec:4412.6-4412.14
  rule fun_growmem_case_0{v_meminst : meminst, v_n : nat, meminst' : meminst, i' : uN, at : addrtype, i : u64, j_opt : u64?, b_lst : byte*}:
    `%%`(v_meminst, v_n)
    -- if ({TYPE `%%PAGE`_memtype(at, mk_limits_limits(i, j_opt)), BYTES b_lst} = v_meminst)
    -- if (meminst' = {TYPE `%%PAGE`_memtype(at, mk_limits_limits(i', j_opt)), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})
    -- if (($proj_uN_0(i').0 : nat <:> rat) = (((|b_lst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (v_n : nat <:> rat)))
    -- (if ($proj_uN_0(i').0 <= $proj_uN_0(j_8).0))?{j_8 <- j_opt}
    -- if ($proj_uN_0(i').0 <= (2 ^ ((($size($numtype_addrtype(at)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))
    -- wf_meminst: `%`({TYPE `%%PAGE`_memtype(at, mk_limits_limits(i, j_opt)), BYTES b_lst})
    -- wf_meminst: `%`({TYPE `%%PAGE`_memtype(at, mk_limits_limits(i', j_opt)), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})

;; test.spectec:4412.6-4412.14
relation fun_growmem: `%%%`(meminst, nat, meminst?)
  ;; test.spectec:4412.6-4412.14
  rule fun_growmem_case_0{v_meminst : meminst, v_n : nat, meminst' : meminst, i' : uN, at : addrtype, i : u64, j_opt : u64?, b_lst : byte*}:
    `%%%`(v_meminst, v_n, ?(meminst'))
    -- if ({TYPE `%%PAGE`_memtype(at, mk_limits_limits(i, j_opt)), BYTES b_lst} = v_meminst)
    -- if (meminst' = {TYPE `%%PAGE`_memtype(at, mk_limits_limits(i', j_opt)), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})
    -- if (($proj_uN_0(i').0 : nat <:> rat) = (((|b_lst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (v_n : nat <:> rat)))
    -- (if ($proj_uN_0(i').0 <= $proj_uN_0(j_8).0))?{j_8 <- j_opt}
    -- if ($proj_uN_0(i').0 <= (2 ^ ((($size($numtype_addrtype(at)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))
    -- wf_meminst: `%`({TYPE `%%PAGE`_memtype(at, mk_limits_limits(i, j_opt)), BYTES b_lst})
    -- wf_meminst: `%`({TYPE `%%PAGE`_memtype(at, mk_limits_limits(i', j_opt)), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})

  ;; test.spectec:4412.6-4412.14
  rule fun_growmem_case_1{x0 : meminst, x1 : nat}:
    `%%%`(x0, x1, ?())
    -- ~ fun_growmem_before_fun_growmem_case_1: `%%`(x0, x1)

;; test.spectec:4412.6-4412.14
relation growmem_is_wf: `%%%`(v_meminst : meminst, nat : nat, ret_val : meminst)
  ;; test.spectec:4412.6-4412.14
  rule growmem_is_wf_0{v_meminst : meminst, nat : nat, ret_val : meminst, var_0 : meminst?}:
    `%%%`(v_meminst, nat, ret_val)
    -- fun_growmem: `%%%`(v_meminst, nat, var_0)
    -- wf_meminst: `%`(v_meminst)
    -- if (var_0 =/= ?())
    -- if (ret_val = !(var_0))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:4457.1-4457.60
relation Num_ok: `%|-%:%`(store, num, numtype)
  ;; test.spectec:4462.1-4463.23
  rule mk_Num_ok{s : store, nt : numtype, c : num_}:
    `%|-%:%`(s, CONST_num(nt, c), nt)
    -- wf_store: `%`(s)
    -- wf_num: `%`(CONST_num(nt, c))

;; test.spectec:4458.1-4458.60
relation Vec_ok: `%|-%:%`(store, vec, vectype)
  ;; test.spectec:4465.1-4466.24
  rule mk_Vec_ok{s : store, vt : vectype, c : vec_}:
    `%|-%:%`(s, VCONST_vec(vt, c), vt)
    -- wf_store: `%`(s)
    -- wf_vec: `%`(VCONST_vec(vt, c))

;; test.spectec:4459.1-4459.60
rec {

;; test.spectec:4459.1-4459.60
relation Ref_ok: `%|-%:%`(store, ref, reftype)
  ;; test.spectec:4469.1-4470.36
  rule null{s : store}:
    `%|-%:%`(s, REF_NULL_ADDR_ref, REF_reftype(?(NULL_null), BOT_heaptype))
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_NULL_ADDR_ref)
    -- wf_reftype: `%`(REF_reftype(?(NULL_null), BOT_heaptype))

  ;; test.spectec:4472.1-4473.31
  rule i31{s : store, i : u31}:
    `%|-%:%`(s, REF_I31_NUM_ref(i), REF_reftype(?(), I31_heaptype))
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_I31_NUM_ref(i))
    -- wf_reftype: `%`(REF_reftype(?(), I31_heaptype))

  ;; test.spectec:4475.1-4477.31
  rule struct{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, REF_STRUCT_ADDR_ref(a), REF_reftype(?(), $heaptype_deftype(dt)))
    -- if (a < |s.STRUCTS_store|)
    -- if (s.STRUCTS_store[a].TYPE_structinst = dt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_STRUCT_ADDR_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), $heaptype_deftype(dt)))

  ;; test.spectec:4479.1-4481.30
  rule array{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, REF_ARRAY_ADDR_ref(a), REF_reftype(?(), $heaptype_deftype(dt)))
    -- if (a < |s.ARRAYS_store|)
    -- if (s.ARRAYS_store[a].TYPE_arrayinst = dt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_ARRAY_ADDR_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), $heaptype_deftype(dt)))

  ;; test.spectec:4483.1-4485.29
  rule func{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, REF_FUNC_ADDR_ref(a), REF_reftype(?(), $heaptype_deftype(dt)))
    -- if (a < |s.FUNCS_store|)
    -- if (s.FUNCS_store[a].TYPE_funcinst = dt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_FUNC_ADDR_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), $heaptype_deftype(dt)))

  ;; test.spectec:4487.1-4489.24
  rule exn{s : store, a : addr, exn : exninst}:
    `%|-%:%`(s, REF_EXN_ADDR_ref(a), REF_reftype(?(), EXN_heaptype))
    -- if (a < |s.EXNS_store|)
    -- if (s.EXNS_store[a] = exn)
    -- wf_store: `%`(s)
    -- wf_exninst: `%`(exn)
    -- wf_ref: `%`(REF_EXN_ADDR_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), EXN_heaptype))

  ;; test.spectec:4491.1-4492.33
  rule host{s : store, a : addr}:
    `%|-%:%`(s, REF_HOST_ADDR_ref(a), REF_reftype(?(), ANY_heaptype))
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_HOST_ADDR_ref(a))
    -- wf_reftype: `%`(REF_reftype(?(), ANY_heaptype))

  ;; test.spectec:4494.1-4497.30
  rule extern{s : store, v_ref : ref}:
    `%|-%:%`(s, REF_EXTERN_ref(v_ref), REF_reftype(?(), EXTERN_heaptype))
    -- Ref_ok: `%|-%:%`(s, v_ref, REF_reftype(?(), ANY_heaptype))
    -- if (v_ref =/= REF_NULL_ADDR_ref)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(REF_EXTERN_ref(v_ref))
    -- wf_reftype: `%`(REF_reftype(?(), EXTERN_heaptype))
    -- wf_reftype: `%`(REF_reftype(?(), ANY_heaptype))
    -- wf_ref: `%`(REF_NULL_ADDR_ref)

  ;; test.spectec:4499.1-4503.34
  rule sub{s : store, v_ref : ref, rt : reftype, rt' : reftype}:
    `%|-%:%`(s, v_ref, rt)
    -- Ref_ok: `%|-%:%`(s, v_ref, rt')
    -- Reftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt)
    -- Reftype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt', rt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(v_ref)
    -- wf_reftype: `%`(rt)
    -- wf_reftype: `%`(rt')
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:4460.1-4460.60
relation Val_ok: `%|-%:%`(store, val, valtype)
  ;; test.spectec:4506.1-4508.27
  rule num{s : store, v_num : num, nt : numtype}:
    `%|-%:%`(s, $val_num(v_num), $valtype_numtype(nt))
    -- Num_ok: `%|-%:%`(s, v_num, nt)
    -- wf_store: `%`(s)
    -- wf_num: `%`(v_num)

  ;; test.spectec:4510.1-4512.27
  rule vec{s : store, v_vec : vec, vt : vectype}:
    `%|-%:%`(s, $val_vec(v_vec), $valtype_vectype(vt))
    -- Vec_ok: `%|-%:%`(s, v_vec, vt)
    -- wf_store: `%`(s)
    -- wf_vec: `%`(v_vec)

  ;; test.spectec:4514.1-4516.27
  rule ref{s : store, v_ref : ref, rt : reftype}:
    `%|-%:%`(s, $val_ref(v_ref), $valtype_reftype(rt))
    -- Ref_ok: `%|-%:%`(s, v_ref, rt)
    -- wf_store: `%`(s)
    -- wf_ref: `%`(v_ref)
    -- wf_reftype: `%`(rt)

;; test.spectec:4521.1-4521.49
relation Packval_ok: `%|-%:%`(store, packval, packtype)
  ;; test.spectec:4524.1-4525.22
  rule mk_Packval_ok{s : store, pt : packtype, c : iN}:
    `%|-%:%`(s, PACK_packval(pt, c), pt)
    -- wf_store: `%`(s)
    -- wf_packval: `%`(PACK_packval(pt, c))

;; test.spectec:4522.1-4522.54
relation Fieldval_ok: `%|-%:%`(store, fieldval, storagetype)
  ;; test.spectec:4527.1-4529.26
  rule val{s : store, v_val : val, t : valtype}:
    `%|-%:%`(s, $fieldval_val(v_val), $storagetype_valtype(t))
    -- Val_ok: `%|-%:%`(s, v_val, t)
    -- wf_store: `%`(s)
    -- wf_val: `%`(v_val)
    -- wf_valtype: `%`(t)

  ;; test.spectec:4531.1-4533.35
  rule packval{s : store, v_packval : packval, pt : packtype}:
    `%|-%:%`(s, $fieldval_packval(v_packval), $storagetype_packtype(pt))
    -- Packval_ok: `%|-%:%`(s, v_packval, pt)
    -- wf_store: `%`(s)
    -- wf_packval: `%`(v_packval)

;; test.spectec:4538.1-4538.84
rec {

;; test.spectec:4538.1-4538.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; test.spectec:4540.1-4542.28
  rule tag{s : store, a : addr, v_taginst : taginst}:
    `%|-%:%`(s, TAG_externaddr(a), TAG_externtype(v_taginst.TYPE_taginst))
    -- if (a < |s.TAGS_store|)
    -- if (s.TAGS_store[a] = v_taginst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TAG_externtype(v_taginst.TYPE_taginst))

  ;; test.spectec:4544.1-4546.34
  rule global{s : store, a : addr, v_globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(v_globalinst.TYPE_globalinst))
    -- if (a < |s.GLOBALS_store|)
    -- if (s.GLOBALS_store[a] = v_globalinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(GLOBAL_externtype(v_globalinst.TYPE_globalinst))

  ;; test.spectec:4548.1-4550.28
  rule mem{s : store, a : addr, v_meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(v_meminst.TYPE_meminst))
    -- if (a < |s.MEMS_store|)
    -- if (s.MEMS_store[a] = v_meminst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(MEM_externtype(v_meminst.TYPE_meminst))

  ;; test.spectec:4552.1-4554.32
  rule table{s : store, a : addr, v_tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(v_tableinst.TYPE_tableinst))
    -- if (a < |s.TABLES_store|)
    -- if (s.TABLES_store[a] = v_tableinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TABLE_externtype(v_tableinst.TYPE_tableinst))

  ;; test.spectec:4556.1-4558.30
  rule func{s : store, a : addr, v_funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype($typeuse_deftype(v_funcinst.TYPE_funcinst)))
    -- if (a < |s.FUNCS_store|)
    -- if (s.FUNCS_store[a] = v_funcinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(FUNC_externtype($typeuse_deftype(v_funcinst.TYPE_funcinst)))

  ;; test.spectec:4560.1-4564.37
  rule sub{s : store, v_externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, v_externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, v_externaddr, xt')
    -- Externtype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt)
    -- Externtype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt', xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_externtype: `%`(xt')
    -- wf_context: `%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
}

;; test.spectec:4577.6-4577.19
relation fun_inst_valtype: `%%%`(moduleinst, valtype, valtype)
  ;; test.spectec:4577.6-4577.19
  rule fun_inst_valtype_case_0{v_moduleinst : moduleinst, t : valtype, var_0 : valtype}:
    `%%%`(v_moduleinst, t, var_0)
    -- fun_subst_all_valtype: `%%%`(t, $typeuse_deftype(iter_val_3)*{iter_val_3 <- v_moduleinst.TYPES_moduleinst}, var_0)

;; test.spectec:4577.6-4577.19
relation inst_valtype_is_wf: `%%%`(v_moduleinst : moduleinst, v_valtype : valtype, ret_val : valtype)
  ;; test.spectec:4577.6-4577.19
  rule inst_valtype_is_wf_0{v_moduleinst : moduleinst, v_valtype : valtype, ret_val : valtype, var_0 : valtype}:
    `%%%`(v_moduleinst, v_valtype, ret_val)
    -- fun_inst_valtype: `%%%`(v_moduleinst, v_valtype, var_0)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_valtype: `%`(v_valtype)
    -- if (ret_val = var_0)
    -- wf_valtype: `%`(ret_val)

;; test.spectec:4578.6-4578.19
relation fun_inst_reftype: `%%%`(moduleinst, reftype, reftype)
  ;; test.spectec:4578.6-4578.19
  rule fun_inst_reftype_case_0{v_moduleinst : moduleinst, rt : reftype, var_0 : reftype}:
    `%%%`(v_moduleinst, rt, var_0)
    -- fun_subst_all_reftype: `%%%`(rt, $typeuse_deftype(iter_val_4)*{iter_val_4 <- v_moduleinst.TYPES_moduleinst}, var_0)

;; test.spectec:4578.6-4578.19
relation inst_reftype_is_wf: `%%%`(v_moduleinst : moduleinst, v_reftype : reftype, ret_val : reftype)
  ;; test.spectec:4578.6-4578.19
  rule inst_reftype_is_wf_0{v_moduleinst : moduleinst, v_reftype : reftype, ret_val : reftype, var_0 : reftype}:
    `%%%`(v_moduleinst, v_reftype, ret_val)
    -- fun_inst_reftype: `%%%`(v_moduleinst, v_reftype, var_0)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_reftype: `%`(v_reftype)
    -- if (ret_val = var_0)
    -- wf_reftype: `%`(ret_val)

;; test.spectec:4579.6-4579.22
relation fun_inst_globaltype: `%%%`(moduleinst, globaltype, globaltype)
  ;; test.spectec:4579.6-4579.22
  rule fun_inst_globaltype_case_0{v_moduleinst : moduleinst, gt : globaltype, var_0 : globaltype}:
    `%%%`(v_moduleinst, gt, var_0)
    -- fun_subst_all_globaltype: `%%%`(gt, $typeuse_deftype(iter_val_5)*{iter_val_5 <- v_moduleinst.TYPES_moduleinst}, var_0)

;; test.spectec:4579.6-4579.22
relation inst_globaltype_is_wf: `%%%`(v_moduleinst : moduleinst, v_globaltype : globaltype, ret_val : globaltype)
  ;; test.spectec:4579.6-4579.22
  rule inst_globaltype_is_wf_0{v_moduleinst : moduleinst, v_globaltype : globaltype, ret_val : globaltype, var_0 : globaltype}:
    `%%%`(v_moduleinst, v_globaltype, ret_val)
    -- fun_inst_globaltype: `%%%`(v_moduleinst, v_globaltype, var_0)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_globaltype: `%`(v_globaltype)
    -- if (ret_val = var_0)
    -- wf_globaltype: `%`(ret_val)

;; test.spectec:4580.6-4580.19
relation fun_inst_memtype: `%%%`(moduleinst, memtype, memtype)
  ;; test.spectec:4580.6-4580.19
  rule fun_inst_memtype_case_0{v_moduleinst : moduleinst, mt : memtype, var_0 : memtype}:
    `%%%`(v_moduleinst, mt, var_0)
    -- fun_subst_all_memtype: `%%%`(mt, $typeuse_deftype(iter_val_6)*{iter_val_6 <- v_moduleinst.TYPES_moduleinst}, var_0)

;; test.spectec:4580.6-4580.19
relation inst_memtype_is_wf: `%%%`(v_moduleinst : moduleinst, v_memtype : memtype, ret_val : memtype)
  ;; test.spectec:4580.6-4580.19
  rule inst_memtype_is_wf_0{v_moduleinst : moduleinst, v_memtype : memtype, ret_val : memtype, var_0 : memtype}:
    `%%%`(v_moduleinst, v_memtype, ret_val)
    -- fun_inst_memtype: `%%%`(v_moduleinst, v_memtype, var_0)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_memtype: `%`(v_memtype)
    -- if (ret_val = var_0)
    -- wf_memtype: `%`(ret_val)

;; test.spectec:4581.6-4581.21
relation fun_inst_tabletype: `%%%`(moduleinst, tabletype, tabletype)
  ;; test.spectec:4581.6-4581.21
  rule fun_inst_tabletype_case_0{v_moduleinst : moduleinst, tt : tabletype, var_0 : tabletype}:
    `%%%`(v_moduleinst, tt, var_0)
    -- fun_subst_all_tabletype: `%%%`(tt, $typeuse_deftype(iter_val_7)*{iter_val_7 <- v_moduleinst.TYPES_moduleinst}, var_0)

;; test.spectec:4581.6-4581.21
relation inst_tabletype_is_wf: `%%%`(v_moduleinst : moduleinst, v_tabletype : tabletype, ret_val : tabletype)
  ;; test.spectec:4581.6-4581.21
  rule inst_tabletype_is_wf_0{v_moduleinst : moduleinst, v_tabletype : tabletype, ret_val : tabletype, var_0 : tabletype}:
    `%%%`(v_moduleinst, v_tabletype, ret_val)
    -- fun_inst_tabletype: `%%%`(v_moduleinst, v_tabletype, var_0)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_tabletype: `%`(v_tabletype)
    -- if (ret_val = var_0)
    -- wf_tabletype: `%`(ret_val)

