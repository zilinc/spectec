
;; test.spectec:201.14-201.17
syntax r_MUT = 
  | MUT

;; test.spectec:7.1-7.27
syntax N = nat

;; test.spectec:8.1-8.27
syntax M = nat

;; test.spectec:9.1-9.27
syntax n = nat

;; test.spectec:10.1-10.27
syntax m = nat

;; test.spectec:15.1-15.14
def $Ki : nat
  ;; test.spectec:16.1-16.15
  def $Ki = 1024

;; test.spectec:21.1-21.25
def $min(nat : nat, nat_0 : nat) : nat
  ;; test.spectec:22.1-22.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:25.1-25.21
rec {

;; test.spectec:25.6-25.10
relation fun_sum: `%%`(nat*, nat)
  ;; test.spectec:25.6-25.10
  rule fun_sum_case_0:
    `%%`([], 0)

  ;; test.spectec:25.6-25.10
  rule fun_sum_case_1{v_n : nat, n'_lst : n*, var_0 : nat}:
    `%%`([v_n] ++ n'_lst, (v_n + var_0))
    -- fun_sum: `%%`(n'_lst, var_0)
}

;; test.spectec:32.1-32.58
def $opt_(syntax X, var_0_lst : X*) : X??
  ;; test.spectec:33.1-33.31
  def $opt_{syntax X}(syntax X, []) = ?(?())
  ;; test.spectec:34.1-34.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(?(w))
  def $opt_{syntax X, x1 : X*}(syntax X, x1) = ?()
    -- otherwise

;; test.spectec:36.1-36.45
def $list_(syntax X, var_0_opt : X?) : X*
  ;; test.spectec:37.1-37.32
  def $list_{syntax X}(syntax X, ?()) = []
  ;; test.spectec:38.1-38.28
  def $list_{syntax X, w : X}(syntax X, ?(w)) = [w]

;; test.spectec:40.1-40.59
rec {

;; test.spectec:40.1-40.59
def $concat_(syntax X, var_0_lst_lst : X**) : X*
  ;; test.spectec:41.1-41.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; test.spectec:42.1-42.61
  def $concat_{syntax X, w_lst : X*, w'_lst_lst : X**}(syntax X, [w_lst] ++ w'_lst_lst) = w_lst ++ $concat_(syntax X, w'_lst_lst)
}

;; test.spectec:44.1-44.78
rec {

;; test.spectec:44.1-44.78
def $disjoint_(syntax X, var_0_lst : X*) : bool
  ;; test.spectec:45.1-45.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; test.spectec:46.1-46.68
  def $disjoint_{syntax X, w : X, w'_lst : X*}(syntax X, [w] ++ w'_lst) = (~ (w <- w'_lst) /\ $disjoint_(syntax X, w'_lst))
}

;; test.spectec:52.1-52.28
relation Nat_ok: `%|-%`(nat, nat)
  ;; test.spectec:53.1-54.9
  rule refl{v_n : n}:
    `%|-%`(v_n, v_n)

;; test.spectec:56.1-56.31
relation Nats_ok: `%|-%`(nat*, nat*)
  ;; test.spectec:57.1-59.25
  rule all{n_lst : n*}:
    `%|-%`(n_lst, n_lst)
    -- (Nat_ok: `%|-%`(v_n, v_n))*{v_n <- n_lst}

;; test.spectec:65.1-65.29
relation Pair_ok: `%|-%`(nat, nat)
  ;; test.spectec:66.1-67.9
  rule eq{v_n : n}:
    `%|-%`(v_n, v_n)

;; test.spectec:69.1-69.32
relation Pairs_ok: `%|-%`(nat*, nat*)
  ;; test.spectec:70.1-72.26
  rule all{n_lst : n*, m_lst : m*}:
    `%|-%`(n_lst, m_lst)
    -- if (|m_lst| = |n_lst|)
    -- (Pair_ok: `%|-%`(v_n, v_m))*{v_m <- m_lst, v_n <- n_lst}

;; test.spectec:88.1-88.49
syntax list{syntax X}(syntax X) = 
  | mk_list(X_lst : X*)
    -- if (|X_lst| < (2 ^ 32))

;; test.spectec:97.1-97.50
syntax byte = 
  | mk_byte(i : nat)

;; test.spectec:97.1-97.50
def $proj_byte_0(x : byte) : (nat)
  ;; test.spectec:97.1-97.50
  def $proj_byte_0{v_num_0 : nat}(mk_byte_byte(v_num_0)) = (v_num_0)

;; test.spectec:97.8-97.12
relation wf_byte: `%`(byte)
  ;; test.spectec:97.8-97.12
  rule byte_case_0{i : nat}:
    `%`(mk_byte_byte(i))
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:99.1-100.25
syntax uN = 
  | mk_uN(i : nat)

;; test.spectec:99.1-100.25
def $proj_uN_0(x : uN) : (nat)
  ;; test.spectec:99.1-100.25
  def $proj_uN_0{v_num_0 : nat}(mk_uN_uN(v_num_0)) = (v_num_0)

;; test.spectec:99.8-99.11
relation wf_uN: `%%`(N, uN)
  ;; test.spectec:99.8-99.11
  rule uN_case_0{v_N : N, i : nat}:
    `%%`(v_N, mk_uN_uN(i))
    -- if ((i >= 0) /\ (i <= ((((2 ^ v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:101.1-102.49
syntax sN = 
  | mk_sN(i : int)

;; test.spectec:101.1-102.49
def $proj_sN_0(x : sN) : (int)
  ;; test.spectec:101.1-102.49
  def $proj_sN_0{v_num_0 : int}(mk_sN_sN(v_num_0)) = (v_num_0)

;; test.spectec:101.8-101.11
relation wf_sN: `%%`(N, sN)
  ;; test.spectec:101.8-101.11
  rule sN_case_0{v_N : N, i : int}:
    `%%`(v_N, mk_sN_sN(i))
    -- if ((((i >= - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; test.spectec:103.1-104.8
syntax iN = uN

;; test.spectec:106.1-106.20
syntax u31 = uN

;; test.spectec:107.1-107.20
syntax u32 = uN

;; test.spectec:108.1-108.20
syntax u64 = uN

;; test.spectec:110.1-110.20
syntax i32 = iN

;; test.spectec:111.1-111.20
syntax i64 = iN

;; test.spectec:118.1-118.35
def $signif(v_N : N) : nat?
  ;; test.spectec:119.1-119.21
  def $signif(32) = ?(23)
  ;; test.spectec:120.1-120.21
  def $signif(64) = ?(52)
  def $signif{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:122.1-122.34
def $expon(v_N : N) : nat?
  ;; test.spectec:123.1-123.19
  def $expon(32) = ?(8)
  ;; test.spectec:124.1-124.20
  def $expon(64) = ?(11)
  def $expon{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:126.1-126.30
def $fun_M(v_N : N) : nat
  ;; test.spectec:127.1-127.23
  def $fun_M{v_N : nat}(v_N) = !($signif(v_N))

;; test.spectec:129.1-129.30
def $E(v_N : N) : nat
  ;; test.spectec:130.1-130.22
  def $E{v_N : nat}(v_N) = !($expon(v_N))

;; test.spectec:136.1-136.30
syntax exp = int

;; test.spectec:137.1-141.84
syntax fNmag = 
  | NORM(v_m : m, v_exp : exp)
  | SUBNORM(v_m : m)
  | INF
  | NAN(v_m : m)

;; test.spectec:137.8-137.14
relation wf_fNmag: `%%`(N, fNmag)
  ;; test.spectec:137.8-137.14
  rule fNmag_case_0{v_N : N, v_m : m, v_exp : exp}:
    `%%`(v_N, NORM_fNmag(v_m, v_exp))
    -- if ((v_m < (2 ^ $fun_M(v_N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= v_exp) /\ (v_exp <= (((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

  ;; test.spectec:137.8-137.14
  rule fNmag_case_1{v_N : N, v_exp : exp, v_m : m}:
    `%%`(v_N, SUBNORM_fNmag(v_m))
    -- if ((v_m < (2 ^ $fun_M(v_N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = v_exp))

  ;; test.spectec:137.8-137.14
  rule fNmag_case_2{v_N : N}:
    `%%`(v_N, INF_fNmag)

  ;; test.spectec:137.8-137.14
  rule fNmag_case_3{v_N : N, v_m : m}:
    `%%`(v_N, NAN_fNmag(v_m))
    -- if ((1 <= v_m) /\ (v_m < (2 ^ $fun_M(v_N))))

;; test.spectec:132.1-134.35
syntax fN = 
  | POS(fNmag)
  | NEG(fNmag)

;; test.spectec:132.8-132.11
relation wf_fN: `%%`(N, fN)
  ;; test.spectec:132.8-132.11
  rule fN_case_0{v_N : N, var_0 : fNmag}:
    `%%`(v_N, POS_fN(var_0))
    -- wf_fNmag: `%%`(v_N, var_0)

  ;; test.spectec:132.8-132.11
  rule fN_case_1{v_N : N, var_0 : fNmag}:
    `%%`(v_N, NEG_fN(var_0))
    -- wf_fNmag: `%%`(v_N, var_0)

;; test.spectec:143.1-143.20
syntax f32 = fN

;; test.spectec:144.1-144.20
syntax f64 = fN

;; test.spectec:146.1-146.39
def $fzero(v_N : N) : fN
  ;; test.spectec:147.1-147.32
  def $fzero{v_N : nat}(v_N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:146.6-146.12
relation fzero_is_wf: `%%`(v_N : N, ret_val : fN)
  ;; test.spectec:146.6-146.12
  rule fzero_is_wf_0{v_N : N, ret_val : fN}:
    `%%`(v_N, ret_val)
    -- if (ret_val = $fzero(v_N))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:149.1-149.39
def $fone(v_N : N) : fN
  ;; test.spectec:150.1-150.30
  def $fone{v_N : nat}(v_N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:149.6-149.11
relation fone_is_wf: `%%`(v_N : N, ret_val : fN)
  ;; test.spectec:149.6-149.11
  rule fone_is_wf_0{v_N : N, ret_val : fN}:
    `%%`(v_N, ret_val)
    -- if (ret_val = $fone(v_N))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:152.1-152.21
def $canon_(v_N : N) : nat
  ;; test.spectec:153.1-153.37
  def $canon_{v_N : nat}(v_N) = (2 ^ (((!($signif(v_N)) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:160.1-160.85
syntax char = 
  | mk_char(i : nat)

;; test.spectec:160.1-160.85
def $proj_char_0(x : char) : (nat)
  ;; test.spectec:160.1-160.85
  def $proj_char_0{v_num_0 : nat}(mk_char_char(v_num_0)) = (v_num_0)

;; test.spectec:160.8-160.12
relation wf_char: `%`(char)
  ;; test.spectec:160.8-160.12
  rule char_case_0{i : nat}:
    `%`(mk_char_char(i))
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:162.1-162.25
rec {

;; test.spectec:162.6-162.11
relation fun_utf8: `%%`(char*, byte*)
  ;; test.spectec:162.6-162.11
  rule fun_utf8_case_0{ch : char, b : byte}:
    `%%`([ch], [b])
    -- if (($proj_char_0(ch).0 < 128) /\ (mk_byte_byte($proj_char_0(ch).0) = b))
    -- wf_byte: `%`(mk_byte_byte($proj_char_0(ch).0))

  ;; test.spectec:162.6-162.11
  rule fun_utf8_case_1{ch : char, b_1 : byte, b_2 : byte}:
    `%%`([ch], [b_1 b_2])
    -- if (((128 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 2048)) /\ ($proj_char_0(ch).0 = (((2 ^ 6) * ((($proj_byte_0(b_1).0 : nat <:> int) - (192 : nat <:> int)) : int <:> nat)) + ((($proj_byte_0(b_2).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))

  ;; test.spectec:162.6-162.11
  rule fun_utf8_case_2{ch : char, b_1 : byte, b_2 : byte, b_3 : byte}:
    `%%`([ch], [b_1 b_2 b_3])
    -- if ((((2048 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 55296)) \/ ((57344 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 65536))) /\ ($proj_char_0(ch).0 = ((((2 ^ 12) * ((($proj_byte_0(b_1).0 : nat <:> int) - (224 : nat <:> int)) : int <:> nat)) + ((2 ^ 6) * ((($proj_byte_0(b_2).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((($proj_byte_0(b_3).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))

  ;; test.spectec:162.6-162.11
  rule fun_utf8_case_3{ch : char, b_1 : byte, b_2 : byte, b_3 : byte, b_4 : byte}:
    `%%`([ch], [b_1 b_2 b_3 b_4])
    -- if (((65536 <= $proj_char_0(ch).0) /\ ($proj_char_0(ch).0 < 69632)) /\ ($proj_char_0(ch).0 = (((((2 ^ 18) * ((($proj_byte_0(b_1).0 : nat <:> int) - (240 : nat <:> int)) : int <:> nat)) + ((2 ^ 12) * ((($proj_byte_0(b_2).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((2 ^ 6) * ((($proj_byte_0(b_3).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((($proj_byte_0(b_4).0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))

  ;; test.spectec:162.6-162.11
  rule fun_utf8_case_4{ch_lst : char*, var_0_lst : byte**}:
    `%%`(ch_lst, $concat_(syntax byte, var_0_lst))
    -- if (|var_0_lst| = |ch_lst|)
    -- (fun_utf8: `%%`([ch], var_0))*{var_0 <- var_0_lst, ch <- ch_lst}
}

;; test.spectec:162.1-162.25
rec {

;; test.spectec:162.6-162.11
relation utf8_is_wf: `%%`(var_0_lst : char*, ret_val_lst : byte*)
  ;; test.spectec:162.6-162.11
  rule utf8_is_wf_0{var_0_lst : char*, ret_val_lst : byte*, var_0 : byte*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_utf8: `%%`(var_0_lst, var_0)
    -- (wf_char: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:164.1-164.70
syntax name = 
  | mk_name(char_lst : char*)

;; test.spectec:164.1-164.70
def $proj_name_0(x : name) : (char*)
  ;; test.spectec:164.1-164.70
  def $proj_name_0{v_char_list_0 : char*}(mk_name_name(v_char_list_0)) = (v_char_list_0)

;; test.spectec:164.8-164.12
relation wf_name: `%`(name)
  ;; test.spectec:164.8-164.12
  rule name_case_0{char_lst : char*, var_0 : byte*}:
    `%`(mk_name_name(char_lst))
    -- fun_utf8: `%%`(char_lst, var_0)
    -- (wf_char: `%`(v_char))*{v_char <- char_lst}
    -- if (|var_0| < (2 ^ 32))

;; test.spectec:173.1-173.36
syntax idx = u32

;; test.spectec:175.1-175.45
syntax typeidx = idx

;; test.spectec:176.1-176.49
syntax funcidx = idx

;; test.spectec:177.1-177.49
syntax globalidx = idx

;; test.spectec:178.1-178.47
syntax tableidx = idx

;; test.spectec:179.1-179.46
syntax memidx = idx

;; test.spectec:180.1-180.47
syntax labelidx = idx

;; test.spectec:181.1-181.47
syntax localidx = idx

;; test.spectec:190.1-191.26
syntax valtype = 
  | I32
  | I64
  | F32
  | F64

;; test.spectec:193.1-193.38
syntax Inn = 
  | I32
  | I64

def $valtype_Inn(var_0 : Inn) : valtype
  def $valtype_Inn(I32_Inn) = I32_valtype
  def $valtype_Inn(I64_Inn) = I64_valtype

;; test.spectec:194.1-194.38
syntax Fnn = 
  | F32
  | F64

def $valtype_Fnn(var_0 : Fnn) : valtype
  def $valtype_Fnn(F32_Fnn) = F32_valtype
  def $valtype_Fnn(F64_Fnn) = F64_valtype

;; test.spectec:198.1-199.11
syntax resulttype = valtype?

;; test.spectec:201.1-201.18
syntax mut = r_MUT?

;; test.spectec:203.1-204.17
syntax limits = 
  | mk_limits(v_u32 : u32, u32_opt : u32?)

;; test.spectec:203.8-203.14
relation wf_limits: `%`(limits)
  ;; test.spectec:203.8-203.14
  rule limits_case_0{v_u32 : u32, u32_opt : u32?}:
    `%`(mk_limits_limits(v_u32, u32_opt))
    -- wf_uN: `%%`(32, v_u32)

;; test.spectec:205.1-206.14
syntax globaltype = 
  | mk_globaltype(v_mut : mut, v_valtype : valtype)

;; test.spectec:207.1-208.23
syntax functype = 
  | mk_functype(valtype_lst : valtype*, valtype_lst : valtype*)

;; test.spectec:209.1-210.9
syntax tabletype = limits

;; test.spectec:211.1-212.9
syntax memtype = limits

;; test.spectec:213.1-214.70
syntax externtype = 
  | FUNC(v_functype : functype)
  | GLOBAL(v_globaltype : globaltype)
  | TABLE(v_tabletype : tabletype)
  | MEM(v_memtype : memtype)

;; test.spectec:213.8-213.18
relation wf_externtype: `%`(externtype)
  ;; test.spectec:213.8-213.18
  rule externtype_case_0{v_functype : functype}:
    `%`(FUNC_externtype(v_functype))

  ;; test.spectec:213.8-213.18
  rule externtype_case_1{v_globaltype : globaltype}:
    `%`(GLOBAL_externtype(v_globaltype))

  ;; test.spectec:213.8-213.18
  rule externtype_case_2{v_tabletype : tabletype}:
    `%`(TABLE_externtype(v_tabletype))
    -- wf_limits: `%`(v_tabletype)

  ;; test.spectec:213.8-213.18
  rule externtype_case_3{v_memtype : memtype}:
    `%`(MEM_externtype(v_memtype))
    -- wf_limits: `%`(v_memtype)

;; test.spectec:226.1-226.41
def $size(v_valtype : valtype) : nat
  ;; test.spectec:400.1-400.20
  def $size(I32_valtype) = 32
  ;; test.spectec:401.1-401.20
  def $size(I64_valtype) = 64
  ;; test.spectec:402.1-402.20
  def $size(F32_valtype) = 32
  ;; test.spectec:403.1-403.20
  def $size(F64_valtype) = 64

;; test.spectec:228.1-228.21
syntax val_ = 
  | mk_val__0(v_Inn : Inn, var_x : iN)
  | mk_val__1(v_Fnn : Fnn, var_x : fN)

;; test.spectec:228.8-228.13
relation wf_val_: `%%`(valtype, val_)
  ;; test.spectec:228.8-228.13
  rule val__case_0{v_valtype : valtype, v_Inn : Inn, var_x : iN}:
    `%%`(v_valtype, mk_val__0_val_(v_Inn, var_x))
    -- wf_uN: `%%`($size($valtype_Inn(v_Inn)), var_x)
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; test.spectec:228.8-228.13
  rule val__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : fN}:
    `%%`(v_valtype, mk_val__1_val_(v_Fnn, var_x))
    -- wf_fN: `%%`($size($valtype_Fnn(v_Fnn)), var_x)
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; test.spectec:228.1-228.21
def $proj_val__0(var_x : val_) : iN?
  ;; test.spectec:228.8-228.13
  def $proj_val__0{v_Inn : Inn, var_x : iN}(mk_val__0_val_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:228.8-228.13
  def $proj_val__0{var_x : val_}(var_x) = ?()

;; test.spectec:228.1-228.21
def $proj_val__1(var_x : val_) : fN?
  ;; test.spectec:228.8-228.13
  def $proj_val__1{v_Fnn : Fnn, var_x : fN}(mk_val__1_val_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:228.8-228.13
  def $proj_val__1{var_x : val_}(var_x) = ?()

;; test.spectec:235.1-235.42
syntax sx = 
  | U
  | S

;; test.spectec:236.1-236.56
syntax sz = 
  | mk_sz(i : nat)

;; test.spectec:236.1-236.56
def $proj_sz_0(x : sz) : (nat)
  ;; test.spectec:236.1-236.56
  def $proj_sz_0{v_num_0 : nat}(mk_sz_sz(v_num_0)) = (v_num_0)

;; test.spectec:236.8-236.10
relation wf_sz: `%`(sz)
  ;; test.spectec:236.8-236.10
  rule sz_case_0{i : nat}:
    `%`(mk_sz_sz(i))
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; test.spectec:238.1-238.22
syntax unop_Inn = 
  | CLZ
  | CTZ
  | POPCNT

;; test.spectec:238.1-238.22
syntax unop_Fnn = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST

;; test.spectec:238.1-238.22
syntax unop_ = 
  | mk_unop__0(v_Inn : Inn, var_x : unop_Inn)
  | mk_unop__1(v_Fnn : Fnn, var_x : unop_Fnn)

;; test.spectec:238.8-238.14
relation wf_unop_: `%%`(valtype, unop_)
  ;; test.spectec:238.8-238.14
  rule unop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : unop_Inn}:
    `%%`(v_valtype, mk_unop__0_unop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; test.spectec:238.8-238.14
  rule unop__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : unop_Fnn}:
    `%%`(v_valtype, mk_unop__1_unop_(v_Fnn, var_x))
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; test.spectec:238.1-238.22
def $proj_unop__0(var_x : unop_) : unop_Inn?
  ;; test.spectec:238.8-238.14
  def $proj_unop__0{v_Inn : Inn, var_x : unop_Inn}(mk_unop__0_unop_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:238.8-238.14
  def $proj_unop__0{var_x : unop_}(var_x) = ?()

;; test.spectec:238.1-238.22
def $proj_unop__1(var_x : unop_) : unop_Fnn?
  ;; test.spectec:238.8-238.14
  def $proj_unop__1{v_Fnn : Fnn, var_x : unop_Fnn}(mk_unop__1_unop_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:238.8-238.14
  def $proj_unop__1{var_x : unop_}(var_x) = ?()

;; test.spectec:242.1-242.23
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

;; test.spectec:242.1-242.23
syntax binop_Fnn = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN

;; test.spectec:242.1-242.23
syntax binop_ = 
  | mk_binop__0(v_Inn : Inn, var_x : binop_Inn)
  | mk_binop__1(v_Fnn : Fnn, var_x : binop_Fnn)

;; test.spectec:242.8-242.15
relation wf_binop_: `%%`(valtype, binop_)
  ;; test.spectec:242.8-242.15
  rule binop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : binop_Inn}:
    `%%`(v_valtype, mk_binop__0_binop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; test.spectec:242.8-242.15
  rule binop__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : binop_Fnn}:
    `%%`(v_valtype, mk_binop__1_binop_(v_Fnn, var_x))
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; test.spectec:242.1-242.23
def $proj_binop__0(var_x : binop_) : binop_Inn?
  ;; test.spectec:242.8-242.15
  def $proj_binop__0{v_Inn : Inn, var_x : binop_Inn}(mk_binop__0_binop_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:242.8-242.15
  def $proj_binop__0{var_x : binop_}(var_x) = ?()

;; test.spectec:242.1-242.23
def $proj_binop__1(var_x : binop_) : binop_Fnn?
  ;; test.spectec:242.8-242.15
  def $proj_binop__1{v_Fnn : Fnn, var_x : binop_Fnn}(mk_binop__1_binop_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:242.8-242.15
  def $proj_binop__1{var_x : binop_}(var_x) = ?()

;; test.spectec:249.1-249.24
syntax testop_Inn = 
  | EQZ

;; test.spectec:249.1-249.24
syntax testop_ = 
  | mk_testop__0(v_Inn : Inn, var_x : testop_Inn)

;; test.spectec:249.8-249.16
relation wf_testop_: `%%`(valtype, testop_)
  ;; test.spectec:249.8-249.16
  rule testop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : testop_Inn}:
    `%%`(v_valtype, mk_testop__0_testop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

;; test.spectec:249.1-249.24
def $proj_testop__0(var_x : testop_) : testop_Inn
  ;; test.spectec:249.8-249.16
  def $proj_testop__0{v_Inn : Inn, var_x : testop_Inn}(mk_testop__0_testop_(v_Inn, var_x)) = var_x

;; test.spectec:253.1-253.23
syntax relop_Inn = 
  | EQ
  | NE
  | LT(v_sx : sx)
  | GT(v_sx : sx)
  | LE(v_sx : sx)
  | GE(v_sx : sx)

;; test.spectec:253.1-253.23
syntax relop_Fnn = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE

;; test.spectec:253.1-253.23
syntax relop_ = 
  | mk_relop__0(v_Inn : Inn, var_x : relop_Inn)
  | mk_relop__1(v_Fnn : Fnn, var_x : relop_Fnn)

;; test.spectec:253.8-253.15
relation wf_relop_: `%%`(valtype, relop_)
  ;; test.spectec:253.8-253.15
  rule relop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : relop_Inn}:
    `%%`(v_valtype, mk_relop__0_relop_(v_Inn, var_x))
    -- if (v_valtype = $valtype_Inn(v_Inn))

  ;; test.spectec:253.8-253.15
  rule relop__case_1{v_valtype : valtype, v_Fnn : Fnn, var_x : relop_Fnn}:
    `%%`(v_valtype, mk_relop__1_relop_(v_Fnn, var_x))
    -- if (v_valtype = $valtype_Fnn(v_Fnn))

;; test.spectec:253.1-253.23
def $proj_relop__0(var_x : relop_) : relop_Inn?
  ;; test.spectec:253.8-253.15
  def $proj_relop__0{v_Inn : Inn, var_x : relop_Inn}(mk_relop__0_relop_(v_Inn, var_x)) = ?(var_x)
  ;; test.spectec:253.8-253.15
  def $proj_relop__0{var_x : relop_}(var_x) = ?()

;; test.spectec:253.1-253.23
def $proj_relop__1(var_x : relop_) : relop_Fnn?
  ;; test.spectec:253.8-253.15
  def $proj_relop__1{v_Fnn : Fnn, var_x : relop_Fnn}(mk_relop__1_relop_(v_Fnn, var_x)) = ?(var_x)
  ;; test.spectec:253.8-253.15
  def $proj_relop__1{var_x : relop_}(var_x) = ?()

;; test.spectec:261.1-262.78
syntax cvtop = 
  | EXTEND(v_sx : sx)
  | WRAP
  | CONVERT(v_sx : sx)
  | TRUNC(v_sx : sx)
  | PROMOTE
  | DEMOTE
  | REINTERPRET

;; test.spectec:267.1-267.69
syntax memarg = 
{
  ALIGN u32,
  OFFSET u32
}

;; test.spectec:267.8-267.14
relation wf_memarg: `%`(memarg)
  ;; test.spectec:267.8-267.14
  rule memarg_case_{var_0 : u32, var_1 : u32}:
    `%`({ALIGN var_0, OFFSET var_1})
    -- wf_uN: `%%`(32, var_0)
    -- wf_uN: `%%`(32, var_1)

;; test.spectec:271.1-271.24
syntax loadop_Inn = 
  | mk_loadop_Inn(v_sz : sz, v_sx : sx)

;; test.spectec:271.8-271.16
relation wf_loadop_Inn: `%%`(Inn, loadop_Inn)
  ;; test.spectec:271.8-271.16
  rule loadop_Inn_case_0{v_Inn : Inn, v_sz : sz, v_sx : sx}:
    `%%`(v_Inn, mk_loadop_Inn_loadop_Inn(v_sz, v_sx))
    -- wf_sz: `%`(v_sz)
    -- if ($proj_sz_0(v_sz).0 < $size($valtype_Inn(v_Inn)))

;; test.spectec:271.1-271.24
syntax loadop_ = 
  | mk_loadop__0(v_Inn : Inn, var_x : loadop_Inn)

;; test.spectec:271.8-271.16
relation wf_loadop_: `%%`(valtype, loadop_)
  ;; test.spectec:271.8-271.16
  rule loadop__case_0{v_valtype : valtype, v_Inn : Inn, var_x : loadop_Inn}:
    `%%`(v_valtype, mk_loadop__0_loadop_(v_Inn, var_x))
    -- wf_loadop_Inn: `%%`(v_Inn, var_x)
    -- if (v_valtype = $valtype_Inn(v_Inn))

;; test.spectec:271.1-271.24
def $proj_loadop__0(var_x : loadop_) : loadop_Inn
  ;; test.spectec:271.8-271.16
  def $proj_loadop__0{v_Inn : Inn, var_x : loadop_Inn}(mk_loadop__0_loadop_(v_Inn, var_x)) = var_x

;; test.spectec:277.1-277.52
syntax blocktype = valtype?

;; test.spectec:327.1-332.16
rec {

;; test.spectec:327.1-332.16
syntax instr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT
  | BLOCK(v_blocktype : blocktype, instr_lst : instr*)
  | LOOP(v_blocktype : blocktype, instr_lst : instr*)
  | `IF%%ELSE%`(v_blocktype : blocktype, instr_lst : instr*, instr_lst : instr*)
  | BR(v_labelidx : labelidx)
  | BR_IF(v_labelidx : labelidx)
  | BR_TABLE(labelidx_lst : labelidx*, v_labelidx : labelidx)
  | CALL(v_funcidx : funcidx)
  | CALL_INDIRECT(v_typeidx : typeidx)
  | RETURN
  | CONST(v_valtype : valtype, val_)
  | UNOP(v_valtype : valtype, unop_)
  | BINOP(v_valtype : valtype, binop_)
  | TESTOP(v_valtype : valtype, testop_)
  | RELOP(v_valtype : valtype, relop_)
  | CVTOP(valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop)
  | LOCAL_GET(v_localidx : localidx)
  | LOCAL_SET(v_localidx : localidx)
  | LOCAL_TEE(v_localidx : localidx)
  | GLOBAL_GET(v_globalidx : globalidx)
  | GLOBAL_SET(v_globalidx : globalidx)
  | LOAD(v_valtype : valtype, loadop_?, v_memarg : memarg)
  | STORE(v_valtype : valtype, sz_opt : sz?, v_memarg : memarg)
  | MEMORY_SIZE
  | MEMORY_GROW
}

;; test.spectec:327.1-332.16
rec {

;; test.spectec:327.8-327.13
relation wf_instr: `%`(instr)
  ;; test.spectec:327.8-327.13
  rule instr_case_0:
    `%`(NOP_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_1:
    `%`(UNREACHABLE_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_2:
    `%`(DROP_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_3:
    `%`(SELECT_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_4{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(BLOCK_instr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:327.8-327.13
  rule instr_case_5{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(LOOP_instr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:327.8-327.13
  rule instr_case_6{v_blocktype : blocktype, instr_lst : instr*, instr_lst_0_lst : instr*}:
    `%`(`IF%%ELSE%`_instr(v_blocktype, instr_lst, instr_lst_0_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_instr: `%`(instr_lst_0))*{instr_lst_0 <- instr_lst_0_lst}

  ;; test.spectec:327.8-327.13
  rule instr_case_7{v_labelidx : labelidx}:
    `%`(BR_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_8{v_labelidx : labelidx}:
    `%`(BR_IF_instr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_9{labelidx_lst : labelidx*, v_labelidx : labelidx}:
    `%`(BR_TABLE_instr(labelidx_lst, v_labelidx))
    -- (wf_uN: `%%`(32, v_labelidx))*{v_labelidx <- labelidx_lst}
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_10{v_funcidx : funcidx}:
    `%`(CALL_instr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_11{v_typeidx : typeidx}:
    `%`(CALL_INDIRECT_instr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_12:
    `%`(RETURN_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_13{v_valtype : valtype, var_0 : val_}:
    `%`(CONST_instr(v_valtype, var_0))
    -- wf_val_: `%%`(v_valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_14{v_valtype : valtype, var_0 : unop_}:
    `%`(UNOP_instr(v_valtype, var_0))
    -- wf_unop_: `%%`(v_valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_15{v_valtype : valtype, var_0 : binop_}:
    `%`(BINOP_instr(v_valtype, var_0))
    -- wf_binop_: `%%`(v_valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_16{v_valtype : valtype, var_0 : testop_}:
    `%`(TESTOP_instr(v_valtype, var_0))
    -- wf_testop_: `%%`(v_valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_17{v_valtype : valtype, var_0 : relop_}:
    `%`(RELOP_instr(v_valtype, var_0))
    -- wf_relop_: `%%`(v_valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_18{valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop}:
    `%`(CVTOP_instr(valtype_1, valtype_2, v_cvtop))
    -- if (valtype_1 =/= valtype_2)

  ;; test.spectec:327.8-327.13
  rule instr_case_19{v_localidx : localidx}:
    `%`(LOCAL_GET_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_20{v_localidx : localidx}:
    `%`(LOCAL_SET_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_21{v_localidx : localidx}:
    `%`(LOCAL_TEE_instr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_22{v_globalidx : globalidx}:
    `%`(GLOBAL_GET_instr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_23{v_globalidx : globalidx}:
    `%`(GLOBAL_SET_instr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_24{v_valtype : valtype, var_0_opt : loadop_?, v_memarg : memarg}:
    `%`(LOAD_instr(v_valtype, var_0_opt, v_memarg))
    -- (wf_loadop_: `%%`(v_valtype, var_0))?{var_0 <- var_0_opt}
    -- wf_memarg: `%`(v_memarg)

  ;; test.spectec:327.8-327.13
  rule instr_case_25{Inn_opt : Inn?, valtype_opt : valtype?, v_valtype : valtype, sz_opt : sz?, v_memarg : memarg}:
    `%`(STORE_instr(v_valtype, sz_opt, v_memarg))
    -- (wf_sz: `%`(v_sz))?{v_sz <- sz_opt}
    -- wf_memarg: `%`(v_memarg)
    -- if ((Inn_opt = ?()) <=> (sz_opt = ?()))
    -- if ((Inn_opt = ?()) <=> (valtype_opt = ?()))
    -- (if ((v_valtype = $valtype_Inn(v_Inn)) /\ ($proj_sz_0(v_sz).0 < $size($valtype_Inn(v_Inn)))))?{v_Inn <- Inn_opt, v_sz <- sz_opt, v_valtype <- valtype_opt}

  ;; test.spectec:327.8-327.13
  rule instr_case_26:
    `%`(MEMORY_SIZE_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_27:
    `%`(MEMORY_GROW_instr)
}

;; test.spectec:334.1-335.9
syntax expr = instr*

;; test.spectec:345.1-346.16
syntax type = 
  | TYPE(v_functype : functype)

;; test.spectec:347.1-348.16
syntax local = 
  | LOCAL(v_valtype : valtype)

;; test.spectec:349.1-350.27
syntax func = 
  | FUNC(v_typeidx : typeidx, local_lst : local*, v_expr : expr)

;; test.spectec:349.8-349.12
relation wf_func: `%`(func)
  ;; test.spectec:349.8-349.12
  rule func_case_0{v_typeidx : typeidx, local_lst : local*, v_expr : expr}:
    `%`(FUNC_func(v_typeidx, local_lst, v_expr))
    -- wf_uN: `%%`(32, v_typeidx)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; test.spectec:351.1-352.25
syntax global = 
  | GLOBAL(v_globaltype : globaltype, v_expr : expr)

;; test.spectec:351.8-351.14
relation wf_global: `%`(global)
  ;; test.spectec:351.8-351.14
  rule global_case_0{v_globaltype : globaltype, v_expr : expr}:
    `%`(GLOBAL_global(v_globaltype, v_expr))
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; test.spectec:353.1-354.18
syntax table = 
  | TABLE(v_tabletype : tabletype)

;; test.spectec:353.8-353.13
relation wf_table: `%`(table)
  ;; test.spectec:353.8-353.13
  rule table_case_0{v_tabletype : tabletype}:
    `%`(TABLE_table(v_tabletype))
    -- wf_limits: `%`(v_tabletype)

;; test.spectec:355.1-356.17
syntax mem = 
  | MEMORY(v_memtype : memtype)

;; test.spectec:355.8-355.11
relation wf_mem: `%`(mem)
  ;; test.spectec:355.8-355.11
  rule mem_case_0{v_memtype : memtype}:
    `%`(MEMORY_mem(v_memtype))
    -- wf_limits: `%`(v_memtype)

;; test.spectec:357.1-358.21
syntax elem = 
  | ELEM(v_expr : expr, funcidx_lst : funcidx*)

;; test.spectec:357.8-357.12
relation wf_elem: `%`(elem)
  ;; test.spectec:357.8-357.12
  rule elem_case_0{v_expr : expr, funcidx_lst : funcidx*}:
    `%`(ELEM_elem(v_expr, funcidx_lst))
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}
    -- (wf_uN: `%%`(32, v_funcidx))*{v_funcidx <- funcidx_lst}

;; test.spectec:359.1-360.18
syntax data = 
  | DATA(v_expr : expr, byte_lst : byte*)

;; test.spectec:359.8-359.12
relation wf_data: `%`(data)
  ;; test.spectec:359.8-359.12
  rule data_case_0{v_expr : expr, byte_lst : byte*}:
    `%`(DATA_data(v_expr, byte_lst))
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}
    -- (wf_byte: `%`(v_byte))*{v_byte <- byte_lst}

;; test.spectec:361.1-362.16
syntax start = 
  | START(v_funcidx : funcidx)

;; test.spectec:361.8-361.13
relation wf_start: `%`(start)
  ;; test.spectec:361.8-361.13
  rule start_case_0{v_funcidx : funcidx}:
    `%`(START_start(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

;; test.spectec:364.1-365.66
syntax externidx = 
  | FUNC(v_funcidx : funcidx)
  | GLOBAL(v_globalidx : globalidx)
  | TABLE(v_tableidx : tableidx)
  | MEM(v_memidx : memidx)

;; test.spectec:364.8-364.17
relation wf_externidx: `%`(externidx)
  ;; test.spectec:364.8-364.17
  rule externidx_case_0{v_funcidx : funcidx}:
    `%`(FUNC_externidx(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:364.8-364.17
  rule externidx_case_1{v_globalidx : globalidx}:
    `%`(GLOBAL_externidx(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:364.8-364.17
  rule externidx_case_2{v_tableidx : tableidx}:
    `%`(TABLE_externidx(v_tableidx))
    -- wf_uN: `%%`(32, v_tableidx)

  ;; test.spectec:364.8-364.17
  rule externidx_case_3{v_memidx : memidx}:
    `%`(MEM_externidx(v_memidx))
    -- wf_uN: `%%`(32, v_memidx)

;; test.spectec:366.1-367.24
syntax export = 
  | EXPORT(v_name : name, v_externidx : externidx)

;; test.spectec:366.8-366.14
relation wf_export: `%`(export)
  ;; test.spectec:366.8-366.14
  rule export_case_0{v_name : name, v_externidx : externidx}:
    `%`(EXPORT_export(v_name, v_externidx))
    -- wf_name: `%`(v_name)
    -- wf_externidx: `%`(v_externidx)

;; test.spectec:368.1-369.30
syntax import = 
  | IMPORT(v_name : name, v_name : name, v_externtype : externtype)

;; test.spectec:368.8-368.14
relation wf_import: `%`(import)
  ;; test.spectec:368.8-368.14
  rule import_case_0{v_name : name, name_0 : name, v_externtype : externtype}:
    `%`(IMPORT_import(v_name, name_0, v_externtype))
    -- wf_name: `%`(v_name)
    -- wf_name: `%`(name_0)
    -- wf_externtype: `%`(v_externtype)

;; test.spectec:371.1-372.76
syntax module = 
  | MODULE(type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*)

;; test.spectec:371.8-371.14
relation wf_module: `%`(module)
  ;; test.spectec:371.8-371.14
  rule module_case_0{type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*}:
    `%`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- (wf_import: `%`(v_import))*{v_import <- import_lst}
    -- (wf_func: `%`(v_func))*{v_func <- func_lst}
    -- (wf_global: `%`(v_global))*{v_global <- global_lst}
    -- (wf_table: `%`(v_table))*{v_table <- table_lst}
    -- (wf_mem: `%`(v_mem))*{v_mem <- mem_lst}
    -- (wf_elem: `%`(v_elem))*{v_elem <- elem_lst}
    -- (wf_data: `%`(v_data))*{v_data <- data_lst}
    -- (wf_start: `%`(v_start))?{v_start <- start_opt}
    -- (wf_export: `%`(v_export))*{v_export <- export_lst}

;; test.spectec:409.1-409.64
rec {

;; test.spectec:409.6-409.14
relation fun_funcsxt: `%%`(externtype*, functype*)
  ;; test.spectec:409.6-409.14
  rule fun_funcsxt_case_0:
    `%%`([], [])

  ;; test.spectec:409.6-409.14
  rule fun_funcsxt_case_1{ft : functype, xt_lst : externtype*, var_0 : functype*}:
    `%%`([FUNC_externtype(ft)] ++ xt_lst, [ft] ++ var_0)
    -- fun_funcsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:409.6-409.14
  rule fun_funcsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : functype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_funcsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:410.1-410.66
rec {

;; test.spectec:410.6-410.16
relation fun_globalsxt: `%%`(externtype*, globaltype*)
  ;; test.spectec:410.6-410.16
  rule fun_globalsxt_case_0:
    `%%`([], [])

  ;; test.spectec:410.6-410.16
  rule fun_globalsxt_case_1{gt : globaltype, xt_lst : externtype*, var_0 : globaltype*}:
    `%%`([GLOBAL_externtype(gt)] ++ xt_lst, [gt] ++ var_0)
    -- fun_globalsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:410.6-410.16
  rule fun_globalsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : globaltype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_globalsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:411.1-411.65
rec {

;; test.spectec:411.6-411.15
relation fun_tablesxt: `%%`(externtype*, tabletype*)
  ;; test.spectec:411.6-411.15
  rule fun_tablesxt_case_0:
    `%%`([], [])

  ;; test.spectec:411.6-411.15
  rule fun_tablesxt_case_1{tt : limits, xt_lst : externtype*, var_0 : tabletype*}:
    `%%`([TABLE_externtype(tt)] ++ xt_lst, [tt] ++ var_0)
    -- fun_tablesxt: `%%`(xt_lst, var_0)

  ;; test.spectec:411.6-411.15
  rule fun_tablesxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : tabletype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_tablesxt: `%%`(xt_lst, var_0)
}

;; test.spectec:411.1-411.65
rec {

;; test.spectec:411.6-411.15
relation tablesxt_is_wf: `%%`(var_0_lst : externtype*, ret_val_lst : tabletype*)
  ;; test.spectec:411.6-411.15
  rule tablesxt_is_wf_0{var_0_lst : externtype*, ret_val_lst : tabletype*, var_0 : tabletype*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_tablesxt: `%%`(var_0_lst, var_0)
    -- (wf_externtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_limits: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:412.1-412.63
rec {

;; test.spectec:412.6-412.13
relation fun_memsxt: `%%`(externtype*, memtype*)
  ;; test.spectec:412.6-412.13
  rule fun_memsxt_case_0:
    `%%`([], [])

  ;; test.spectec:412.6-412.13
  rule fun_memsxt_case_1{mt : limits, xt_lst : externtype*, var_0 : memtype*}:
    `%%`([MEM_externtype(mt)] ++ xt_lst, [mt] ++ var_0)
    -- fun_memsxt: `%%`(xt_lst, var_0)

  ;; test.spectec:412.6-412.13
  rule fun_memsxt_case_2{v_externtype : externtype, xt_lst : externtype*, var_0 : memtype*}:
    `%%`([v_externtype] ++ xt_lst, var_0)
    -- fun_memsxt: `%%`(xt_lst, var_0)
}

;; test.spectec:412.1-412.63
rec {

;; test.spectec:412.6-412.13
relation memsxt_is_wf: `%%`(var_0_lst : externtype*, ret_val_lst : memtype*)
  ;; test.spectec:412.6-412.13
  rule memsxt_is_wf_0{var_0_lst : externtype*, ret_val_lst : memtype*, var_0 : memtype*}:
    `%%`(var_0_lst, ret_val_lst)
    -- fun_memsxt: `%%`(var_0_lst, var_0)
    -- (wf_externtype: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = var_0)
    -- (wf_limits: `%`(ret_val))*{ret_val <- ret_val_lst}
}

;; test.spectec:438.1-438.35
def $memarg0 : memarg
  ;; test.spectec:439.1-439.35
  def $memarg0 = {ALIGN mk_uN_u32(0), OFFSET mk_uN_u32(0)}

;; test.spectec:438.6-438.13
relation memarg0_is_wf: `%`(ret_val : memarg)
  ;; test.spectec:438.6-438.13
  rule memarg0_is_wf_0{ret_val : memarg}:
    `%`(ret_val)
    -- if (ret_val = $memarg0)
    -- wf_memarg: `%`(ret_val)

;; test.spectec:451.1-451.22
def $bool(v_bool : bool) : nat
  ;; test.spectec:452.1-452.21
  def $bool(false) = 0
  ;; test.spectec:453.1-453.20
  def $bool(true) = 1

;; test.spectec:455.1-455.23
def $truncz(rat : rat) : int

;; test.spectec:462.6-462.14
relation fun_signed_: `%%%`(N, nat, int)
  ;; test.spectec:462.6-462.14
  rule fun_signed__case_0{v_N : nat, i : nat}:
    `%%%`(v_N, i, (i : nat <:> int))
    -- if (i < (2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

  ;; test.spectec:462.6-462.14
  rule fun_signed__case_1{v_N : nat, i : nat}:
    `%%%`(v_N, i, ((i : nat <:> int) - ((2 ^ v_N) : nat <:> int)))
    -- if (((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ v_N)))

;; test.spectec:466.6-466.18
relation fun_inv_signed_: `%%%`(N, int, nat)
  ;; test.spectec:466.6-466.18
  rule fun_inv_signed__case_0{v_N : nat, i : int}:
    `%%%`(v_N, i, (i : int <:> nat))
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))

  ;; test.spectec:466.6-466.18
  rule fun_inv_signed__case_1{v_N : nat, i : int}:
    `%%%`(v_N, i, ((i + ((2 ^ v_N) : nat <:> int)) : int <:> nat))
    -- if ((- ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; test.spectec:596.1-596.30
def $fabs_(v_N : N, v_fN : fN) : fN*

;; test.spectec:596.6-596.12
relation fabs__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:596.6-596.12
  rule fabs__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fabs_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:599.1-599.31
def $fceil_(v_N : N, v_fN : fN) : fN*

;; test.spectec:599.6-599.13
relation fceil__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:599.6-599.13
  rule fceil__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fceil_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:600.1-600.32
def $ffloor_(v_N : N, v_fN : fN) : fN*

;; test.spectec:600.6-600.14
relation ffloor__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:600.6-600.14
  rule ffloor__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $ffloor_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:602.1-602.34
def $fnearest_(v_N : N, v_fN : fN) : fN*

;; test.spectec:602.6-602.16
relation fnearest__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:602.6-602.16
  rule fnearest__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fnearest_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:597.1-597.30
def $fneg_(v_N : N, v_fN : fN) : fN*

;; test.spectec:597.6-597.12
relation fneg__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:597.6-597.12
  rule fneg__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fneg_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:598.1-598.31
def $fsqrt_(v_N : N, v_fN : fN) : fN*

;; test.spectec:598.6-598.13
relation fsqrt__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:598.6-598.13
  rule fsqrt__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fsqrt_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:601.1-601.32
def $ftrunc_(v_N : N, v_fN : fN) : fN*

;; test.spectec:601.6-601.14
relation ftrunc__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:601.6-601.14
  rule ftrunc__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $ftrunc_(v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:530.1-530.29
def $iclz_(v_N : N, v_iN : iN) : iN

;; test.spectec:530.6-530.12
relation iclz__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:530.6-530.12
  rule iclz__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $iclz_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:531.1-531.29
def $ictz_(v_N : N, v_iN : iN) : iN

;; test.spectec:531.6-531.12
relation ictz__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:531.6-531.12
  rule ictz__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ictz_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:532.1-532.32
def $ipopcnt_(v_N : N, v_iN : iN) : iN

;; test.spectec:532.6-532.15
relation ipopcnt__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:532.6-532.15
  rule ipopcnt__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ipopcnt_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:472.1-473.46
def $fun_unop_(v_valtype : valtype, v_unop_ : unop_, v_val_ : val_) : val_*?
  ;; test.spectec:646.1-646.50
  def $fun_unop_{v_iN : uN}(I32_valtype, mk_unop__0_unop_(I32_Inn, CLZ_unop_Inn), mk_val__0_val_(I32_Inn, v_iN)) = ?([mk_val__0_val_(I32_Inn, $iclz_($size($valtype_Inn(I32_Inn)), v_iN))])
  ;; test.spectec:646.1-646.50
  def $fun_unop_{v_iN : uN}(I64_valtype, mk_unop__0_unop_(I64_Inn, CLZ_unop_Inn), mk_val__0_val_(I64_Inn, v_iN)) = ?([mk_val__0_val_(I64_Inn, $iclz_($size($valtype_Inn(I64_Inn)), v_iN))])
  ;; test.spectec:647.1-647.50
  def $fun_unop_{v_iN : uN}(I32_valtype, mk_unop__0_unop_(I32_Inn, CTZ_unop_Inn), mk_val__0_val_(I32_Inn, v_iN)) = ?([mk_val__0_val_(I32_Inn, $ictz_($size($valtype_Inn(I32_Inn)), v_iN))])
  ;; test.spectec:647.1-647.50
  def $fun_unop_{v_iN : uN}(I64_valtype, mk_unop__0_unop_(I64_Inn, CTZ_unop_Inn), mk_val__0_val_(I64_Inn, v_iN)) = ?([mk_val__0_val_(I64_Inn, $ictz_($size($valtype_Inn(I64_Inn)), v_iN))])
  ;; test.spectec:648.1-648.56
  def $fun_unop_{v_iN : uN}(I32_valtype, mk_unop__0_unop_(I32_Inn, POPCNT_unop_Inn), mk_val__0_val_(I32_Inn, v_iN)) = ?([mk_val__0_val_(I32_Inn, $ipopcnt_($size($valtype_Inn(I32_Inn)), v_iN))])
  ;; test.spectec:648.1-648.56
  def $fun_unop_{v_iN : uN}(I64_valtype, mk_unop__0_unop_(I64_Inn, POPCNT_unop_Inn), mk_val__0_val_(I64_Inn, v_iN)) = ?([mk_val__0_val_(I64_Inn, $ipopcnt_($size($valtype_Inn(I64_Inn)), v_iN))])
  ;; test.spectec:665.1-665.50
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, ABS_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_1)*{iter_0_1 <- $fabs_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:665.1-665.50
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, ABS_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_2)*{iter_0_2 <- $fabs_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  ;; test.spectec:666.1-666.50
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEG_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_3)*{iter_0_3 <- $fneg_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:666.1-666.50
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEG_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_4)*{iter_0_4 <- $fneg_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  ;; test.spectec:667.1-667.52
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, SQRT_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_5)*{iter_0_5 <- $fsqrt_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:667.1-667.52
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, SQRT_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_6)*{iter_0_6 <- $fsqrt_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  ;; test.spectec:668.1-668.52
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, CEIL_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_7)*{iter_0_7 <- $fceil_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:668.1-668.52
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, CEIL_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_8)*{iter_0_8 <- $fceil_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  ;; test.spectec:669.1-669.54
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, FLOOR_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_9)*{iter_0_9 <- $ffloor_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:669.1-669.54
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, FLOOR_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_10)*{iter_0_10 <- $ffloor_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  ;; test.spectec:670.1-670.54
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, TRUNC_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_11)*{iter_0_11 <- $ftrunc_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:670.1-670.54
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, TRUNC_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_12)*{iter_0_12 <- $ftrunc_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  ;; test.spectec:671.1-671.58
  def $fun_unop_{v_fN : fN}(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEAREST_unop_Fnn), mk_val__1_val_(F32_Fnn, v_fN)) = ?(mk_val__1_val_(F32_Fnn, iter_0_13)*{iter_0_13 <- $fnearest_($size($valtype_Fnn(F32_Fnn)), v_fN)})
  ;; test.spectec:671.1-671.58
  def $fun_unop_{v_fN : fN}(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEAREST_unop_Fnn), mk_val__1_val_(F64_Fnn, v_fN)) = ?(mk_val__1_val_(F64_Fnn, iter_0_14)*{iter_0_14 <- $fnearest_($size($valtype_Fnn(F64_Fnn)), v_fN)})
  def $fun_unop_{x0 : valtype, x1 : unop_, x2 : val_}(x0, x1, x2) = ?()
    -- otherwise

;; test.spectec:472.6-472.12
relation unop__is_wf: `%%%%`(v_valtype : valtype, v_unop_ : unop_, v_val_ : val_, ret_val_lst : val_*)
  ;; test.spectec:472.6-472.12
  rule unop__is_wf_0{v_valtype : valtype, v_unop_ : unop_, v_val_ : val_, ret_val_lst : val_*}:
    `%%%%`(v_valtype, v_unop_, v_val_, ret_val_lst)
    -- wf_unop_: `%%`(v_valtype, v_unop_)
    -- wf_val_: `%%`(v_valtype, v_val_)
    -- if ($fun_unop_(v_valtype, v_unop_, v_val_) =/= ?())
    -- if (ret_val_lst = !($fun_unop_(v_valtype, v_unop_, v_val_)))
    -- (wf_val_: `%%`(v_valtype, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:589.1-589.37
def $fadd_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:589.6-589.12
relation fadd__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:589.6-589.12
  rule fadd__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fadd_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:595.1-595.42
def $fcopysign_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:595.6-595.17
relation fcopysign__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:595.6-595.17
  rule fcopysign__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fcopysign_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:592.1-592.37
def $fdiv_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:592.6-592.12
relation fdiv__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:592.6-592.12
  rule fdiv__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fdiv_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:594.1-594.37
def $fmax_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:594.6-594.12
relation fmax__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:594.6-594.12
  rule fmax__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fmax_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:593.1-593.37
def $fmin_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:593.6-593.12
relation fmin__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:593.6-593.12
  rule fmin__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fmin_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:591.1-591.37
def $fmul_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:591.6-591.12
relation fmul__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:591.6-591.12
  rule fmul__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fmul_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:590.1-590.37
def $fsub_(v_N : N, v_fN : fN, fN_0 : fN) : fN*

;; test.spectec:590.6-590.12
relation fsub__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*)
  ;; test.spectec:590.6-590.12
  rule fsub__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val_lst : fN*}:
    `%%%%`(v_N, v_fN, fN_0, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val_lst = $fsub_(v_N, v_fN, fN_0))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:517.1-517.36
def $iadd_(v_N : N, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:542.1-542.47
  def $iadd_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_iN((($proj_uN_0(i_1).0 + $proj_uN_0(i_2).0) \ (2 ^ v_N)))

;; test.spectec:517.6-517.12
relation iadd__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:517.6-517.12
  rule iadd__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iadd_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:523.1-523.36
def $iand_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:523.6-523.12
relation iand__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:523.6-523.12
  rule iand__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $iand_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:520.6-520.12
relation fun_idiv_: `%%%%%`(N, sx, iN, iN, iN?)
  ;; test.spectec:520.6-520.12
  rule fun_idiv__case_0{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, U_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:520.6-520.12
  rule fun_idiv__case_1{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, ?(mk_uN_iN(($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat))))

  ;; test.spectec:520.6-520.12
  rule fun_idiv__case_2{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, S_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:520.6-520.12
  rule fun_idiv__case_3{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?())
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)
    -- if (((var_0 : int <:> rat) / (var_1 : int <:> rat)) = ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))

  ;; test.spectec:520.6-520.12
  rule fun_idiv__case_4{v_N : nat, i_1 : uN, i_2 : uN, var_2 : int, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?(mk_uN_iN(var_0)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, $truncz(((var_1 : int <:> rat) / (var_2 : int <:> rat))), var_0)

;; test.spectec:520.6-520.12
relation idiv__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?)
  ;; test.spectec:520.6-520.12
  rule idiv__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?, var_0 : iN?}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val_opt)
    -- fun_idiv_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val_opt = var_0)
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:519.1-519.36
def $imul_(v_N : N, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:544.1-544.47
  def $imul_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_iN((($proj_uN_0(i_1).0 * $proj_uN_0(i_2).0) \ (2 ^ v_N)))

;; test.spectec:519.6-519.12
relation imul__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:519.6-519.12
  rule imul__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $imul_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:524.1-524.35
def $ior_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:524.6-524.11
relation ior__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:524.6-524.11
  rule ior__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ior_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:521.6-521.12
relation fun_irem_: `%%%%%`(N, sx, iN, iN, iN?)
  ;; test.spectec:521.6-521.12
  rule fun_irem__case_0{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, U_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:521.6-521.12
  rule fun_irem__case_1{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, ?(mk_uN_iN(((($proj_uN_0(i_1).0 : nat <:> int) - (($proj_uN_0(i_2).0 * ($truncz((($proj_uN_0(i_1).0 : nat <:> rat) / ($proj_uN_0(i_2).0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat))))

  ;; test.spectec:521.6-521.12
  rule fun_irem__case_2{v_N : nat, i_1 : uN}:
    `%%%%%`(v_N, S_sx, i_1, mk_uN_iN(0), ?())

  ;; test.spectec:521.6-521.12
  rule fun_irem__case_3{v_N : nat, i_1 : uN, i_2 : uN, j_1 : int, j_2 : int, var_2 : int, var_1 : int, var_0 : nat}:
    `%%%%%`(v_N, S_sx, i_1, i_2, ?(mk_uN_iN(var_0)))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_2)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_1)
    -- fun_inv_signed_: `%%%`(v_N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))), var_0)
    -- if ((j_1 = var_1) /\ (j_2 = var_2))

;; test.spectec:521.6-521.12
relation irem__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?)
  ;; test.spectec:521.6-521.12
  rule irem__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val_opt : iN?, var_0 : iN?}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val_opt)
    -- fun_irem_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val_opt = var_0)
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:528.1-528.37
def $irotl_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:528.6-528.13
relation irotl__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:528.6-528.13
  rule irotl__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $irotl_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:529.1-529.37
def $irotr_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:529.6-529.13
relation irotr__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:529.6-529.13
  rule irotr__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $irotr_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:526.1-526.34
def $ishl_(v_N : N, v_iN : iN, v_u32 : u32) : iN

;; test.spectec:526.6-526.12
relation ishl__is_wf: `%%%%`(v_N : N, v_iN : iN, v_u32 : u32, ret_val : iN)
  ;; test.spectec:526.6-526.12
  rule ishl__is_wf_0{v_N : N, v_iN : iN, v_u32 : u32, ret_val : iN}:
    `%%%%`(v_N, v_iN, v_u32, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(32, v_u32)
    -- if (ret_val = $ishl_(v_N, v_iN, v_u32))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:527.1-527.74
def $ishr_(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32) : iN

;; test.spectec:527.6-527.12
relation ishr__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32, ret_val : iN)
  ;; test.spectec:527.6-527.12
  rule ishr__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, v_u32 : u32, ret_val : iN}:
    `%%%%%`(v_N, v_sx, v_iN, v_u32, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(32, v_u32)
    -- if (ret_val = $ishr_(v_N, v_sx, v_iN, v_u32))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:518.1-518.36
def $isub_(v_N : N, v_iN : iN, iN_0 : iN) : iN
  ;; test.spectec:543.1-543.53
  def $isub_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_iN(((((((2 ^ v_N) + $proj_uN_0(i_1).0) : nat <:> int) - ($proj_uN_0(i_2).0 : nat <:> int)) \ ((2 ^ v_N) : nat <:> int)) : int <:> nat))

;; test.spectec:518.6-518.12
relation isub__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:518.6-518.12
  rule isub__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $isub_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:525.1-525.36
def $ixor_(v_N : N, v_iN : iN, iN_0 : iN) : iN

;; test.spectec:525.6-525.12
relation ixor__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:525.6-525.12
  rule ixor__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ixor_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:474.6-474.13
relation fun_binop_: `%%%%%`(valtype, binop_, val_, val_, val_*)
  ;; test.spectec:474.6-474.13
  rule fun_binop__case_0{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ADD_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $iadd_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_1{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ADD_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $iadd_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_2{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SUB_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $isub_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_3{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SUB_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $isub_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_4{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, MUL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $imul_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_5{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, MUL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $imul_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_6{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_15)?{iter_0_15 <- var_0}))
    -- fun_idiv_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_7{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_16)?{iter_0_16 <- var_0}))
    -- fun_idiv_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_8{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_17)?{iter_0_17 <- var_0}))
    -- fun_irem_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_9{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : iN?}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_18)?{iter_0_18 <- var_0}))
    -- fun_irem_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_10{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, AND_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $iand_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_11{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, AND_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $iand_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_12{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, OR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $ior_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_13{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, OR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $ior_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_14{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, XOR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $ixor_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_15{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, XOR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $ixor_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_16{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SHL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $ishl_($size($valtype_Inn(I32_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_17{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SHL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $ishl_($size($valtype_Inn(I64_Inn)), iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_18{v_sx : sx, iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $ishr_($size($valtype_Inn(I32_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_19{v_sx : sx, iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $ishr_($size($valtype_Inn(I64_Inn)), v_sx, iN_1, mk_uN_u32($proj_uN_0(iN_2).0)))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_20{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTL_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $irotl_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_21{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTL_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $irotl_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_22{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTR_binop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), [mk_val__0_val_(I32_Inn, $irotr_($size($valtype_Inn(I32_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_23{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTR_binop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), [mk_val__0_val_(I64_Inn, $irotr_($size($valtype_Inn(I64_Inn)), iN_1, iN_2))])

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_24{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, ADD_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_19)*{iter_0_19 <- $fadd_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_25{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, ADD_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_20)*{iter_0_20 <- $fadd_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_26{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, SUB_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_21)*{iter_0_21 <- $fsub_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_27{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, SUB_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_22)*{iter_0_22 <- $fsub_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_28{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MUL_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_23)*{iter_0_23 <- $fmul_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_29{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MUL_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_24)*{iter_0_24 <- $fmul_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_30{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, DIV_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_25)*{iter_0_25 <- $fdiv_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_31{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, DIV_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_26)*{iter_0_26 <- $fdiv_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_32{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MIN_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_27)*{iter_0_27 <- $fmin_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_33{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MIN_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_28)*{iter_0_28 <- $fmin_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_34{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, MAX_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_29)*{iter_0_29 <- $fmax_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_35{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, MAX_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_30)*{iter_0_30 <- $fmax_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_36{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_binop__1_binop_(F32_Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__1_val_(F32_Fnn, iter_0_31)*{iter_0_31 <- $fcopysign_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)})

  ;; test.spectec:474.6-474.13
  rule fun_binop__case_37{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_binop__1_binop_(F64_Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__1_val_(F64_Fnn, iter_0_32)*{iter_0_32 <- $fcopysign_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)})

;; test.spectec:474.6-474.13
relation binop__is_wf: `%%%%%`(v_valtype : valtype, v_binop_ : binop_, v_val_ : val_, val__0 : val_, ret_val_lst : val_*)
  ;; test.spectec:474.6-474.13
  rule binop__is_wf_0{v_valtype : valtype, v_binop_ : binop_, v_val_ : val_, val__0 : val_, ret_val_lst : val_*, var_0 : val_*}:
    `%%%%%`(v_valtype, v_binop_, v_val_, val__0, ret_val_lst)
    -- fun_binop_: `%%%%%`(v_valtype, v_binop_, v_val_, val__0, var_0)
    -- wf_binop_: `%%`(v_valtype, v_binop_)
    -- wf_val_: `%%`(v_valtype, v_val_)
    -- wf_val_: `%%`(v_valtype, val__0)
    -- if (ret_val_lst = var_0)
    -- (wf_val_: `%%`(v_valtype, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:533.1-533.27
def $ieqz_(v_N : N, v_iN : iN) : u32
  ;; test.spectec:571.1-571.36
  def $ieqz_{v_N : nat, i_1 : uN}(v_N, i_1) = mk_uN_u32($bool(($proj_uN_0(i_1).0 = 0)))

;; test.spectec:533.6-533.12
relation ieqz__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : u32)
  ;; test.spectec:533.6-533.12
  rule ieqz__is_wf_0{v_N : N, v_iN : iN, ret_val : u32}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $ieqz_(v_N, v_iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:476.1-477.46
def $fun_testop_(v_valtype : valtype, v_testop_ : testop_, v_val_ : val_) : val_?
  ;; test.spectec:649.1-649.52
  def $fun_testop_{v_iN : uN}(I32_valtype, mk_testop__0_testop_(I32_Inn, EQZ_testop_Inn), mk_val__0_val_(I32_Inn, v_iN)) = ?(mk_val__0_val_(I32_Inn, $ieqz_($size($valtype_Inn(I32_Inn)), v_iN)))
  ;; test.spectec:649.1-649.52
  def $fun_testop_{v_iN : uN}(I64_valtype, mk_testop__0_testop_(I64_Inn, EQZ_testop_Inn), mk_val__0_val_(I64_Inn, v_iN)) = ?(mk_val__0_val_(I32_Inn, $ieqz_($size($valtype_Inn(I64_Inn)), v_iN)))
  def $fun_testop_{x0 : valtype, x1 : testop_, x2 : val_}(x0, x1, x2) = ?()
    -- otherwise

;; test.spectec:476.6-476.14
relation testop__is_wf: `%%%%`(v_valtype : valtype, v_testop_ : testop_, v_val_ : val_, ret_val : val_)
  ;; test.spectec:476.6-476.14
  rule testop__is_wf_0{v_valtype : valtype, v_testop_ : testop_, v_val_ : val_, ret_val : val_}:
    `%%%%`(v_valtype, v_testop_, v_val_, ret_val)
    -- wf_testop_: `%%`(v_valtype, v_testop_)
    -- wf_val_: `%%`(v_valtype, v_val_)
    -- if ($fun_testop_(v_valtype, v_testop_, v_val_) =/= ?())
    -- if (ret_val = !($fun_testop_(v_valtype, v_testop_, v_val_)))
    -- wf_val_: `%%`(I32_valtype, ret_val)

;; test.spectec:603.1-603.33
def $feq_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:603.6-603.11
relation feq__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:603.6-603.11
  rule feq__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $feq_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:608.1-608.33
def $fge_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:608.6-608.11
relation fge__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:608.6-608.11
  rule fge__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fge_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:606.1-606.33
def $fgt_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:606.6-606.11
relation fgt__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:606.6-606.11
  rule fgt__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fgt_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:607.1-607.33
def $fle_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:607.6-607.11
relation fle__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:607.6-607.11
  rule fle__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fle_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:605.1-605.33
def $flt_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:605.6-605.11
relation flt__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:605.6-605.11
  rule flt__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $flt_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:604.1-604.33
def $fne_(v_N : N, v_fN : fN, fN_0 : fN) : u32

;; test.spectec:604.6-604.11
relation fne__is_wf: `%%%%`(v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:604.6-604.11
  rule fne__is_wf_0{v_N : N, v_fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(v_N, v_fN, fN_0, ret_val)
    -- wf_fN: `%%`(v_N, v_fN)
    -- wf_fN: `%%`(v_N, fN_0)
    -- if (ret_val = $fne_(v_N, v_fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:535.1-535.33
def $ieq_(v_N : N, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:574.1-574.42
  def $ieq_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_u32($bool((i_1 = i_2)))

;; test.spectec:535.6-535.11
relation ieq__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:535.6-535.11
  rule ieq__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ieq_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:540.6-540.11
relation fun_ige_: `%%%%%`(N, sx, iN, iN, u32)
  ;; test.spectec:540.6-540.11
  rule fun_ige__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 >= $proj_uN_0(i_2).0))))

  ;; test.spectec:540.6-540.11
  rule fun_ige__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 >= var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:540.6-540.11
relation ige__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:540.6-540.11
  rule ige__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32, var_0 : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- fun_ige_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:538.6-538.11
relation fun_igt_: `%%%%%`(N, sx, iN, iN, u32)
  ;; test.spectec:538.6-538.11
  rule fun_igt__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 > $proj_uN_0(i_2).0))))

  ;; test.spectec:538.6-538.11
  rule fun_igt__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 > var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:538.6-538.11
relation igt__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:538.6-538.11
  rule igt__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32, var_0 : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- fun_igt_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:539.6-539.11
relation fun_ile_: `%%%%%`(N, sx, iN, iN, u32)
  ;; test.spectec:539.6-539.11
  rule fun_ile__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 <= $proj_uN_0(i_2).0))))

  ;; test.spectec:539.6-539.11
  rule fun_ile__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 <= var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:539.6-539.11
relation ile__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:539.6-539.11
  rule ile__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32, var_0 : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- fun_ile_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:537.6-537.11
relation fun_ilt_: `%%%%%`(N, sx, iN, iN, u32)
  ;; test.spectec:537.6-537.11
  rule fun_ilt__case_0{v_N : nat, i_1 : uN, i_2 : uN}:
    `%%%%%`(v_N, U_sx, i_1, i_2, mk_uN_u32($bool(($proj_uN_0(i_1).0 < $proj_uN_0(i_2).0))))

  ;; test.spectec:537.6-537.11
  rule fun_ilt__case_1{v_N : nat, i_1 : uN, i_2 : uN, var_1 : int, var_0 : int}:
    `%%%%%`(v_N, S_sx, i_1, i_2, mk_uN_u32($bool((var_0 < var_1))))
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_2).0, var_1)
    -- fun_signed_: `%%%`(v_N, $proj_uN_0(i_1).0, var_0)

;; test.spectec:537.6-537.11
relation ilt__is_wf: `%%%%%`(v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:537.6-537.11
  rule ilt__is_wf_0{v_N : N, v_sx : sx, v_iN : iN, iN_0 : iN, ret_val : u32, var_0 : u32}:
    `%%%%%`(v_N, v_sx, v_iN, iN_0, ret_val)
    -- fun_ilt_: `%%%%%`(v_N, v_sx, v_iN, iN_0, var_0)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = var_0)
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:536.1-536.33
def $ine_(v_N : N, v_iN : iN, iN_0 : iN) : u32
  ;; test.spectec:575.1-575.44
  def $ine_{v_N : nat, i_1 : uN, i_2 : uN}(v_N, i_1, i_2) = mk_uN_u32($bool((i_1 =/= i_2)))

;; test.spectec:536.6-536.11
relation ine__is_wf: `%%%%`(v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:536.6-536.11
  rule ine__is_wf_0{v_N : N, v_iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%`(v_N, v_iN, iN_0, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- wf_uN: `%%`(v_N, iN_0)
    -- if (ret_val = $ine_(v_N, v_iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:478.6-478.13
relation fun_relop_: `%%%%%`(valtype, relop_, val_, val_, val_)
  ;; test.spectec:478.6-478.13
  rule fun_relop__case_0{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, EQ_relop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), mk_val__0_val_(I32_Inn, $ieq_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_1{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, EQ_relop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), mk_val__0_val_(I32_Inn, $ieq_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_2{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, NE_relop_Inn), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), mk_val__0_val_(I32_Inn, $ine_($size($valtype_Inn(I32_Inn)), iN_1, iN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_3{iN_1 : uN, iN_2 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, NE_relop_Inn), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), mk_val__0_val_(I32_Inn, $ine_($size($valtype_Inn(I64_Inn)), iN_1, iN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_4{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_ilt_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_5{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_ilt_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_6{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_igt_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_7{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_igt_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_8{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_ile_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_9{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_ile_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_10{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(v_sx)), mk_val__0_val_(I32_Inn, iN_1), mk_val__0_val_(I32_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_ige_: `%%%%%`($size($valtype_Inn(I32_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_11{v_sx : sx, iN_1 : uN, iN_2 : uN, var_0 : uN}:
    `%%%%%`(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(v_sx)), mk_val__0_val_(I64_Inn, iN_1), mk_val__0_val_(I64_Inn, iN_2), mk_val__0_val_(I32_Inn, var_0))
    -- fun_ige_: `%%%%%`($size($valtype_Inn(I64_Inn)), v_sx, iN_1, iN_2, var_0)

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_12{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, EQ_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_13{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, EQ_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__0_val_(I32_Inn, $feq_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_14{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, NE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_15{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, NE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fne_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_16{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, LT_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_17{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, LT_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__0_val_(I32_Inn, $flt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_18{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, GT_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_19{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, GT_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fgt_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_20{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, LE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_21{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, LE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fle_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_22{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F32_valtype, mk_relop__1_relop_(F32_Fnn, GE_relop_Fnn), mk_val__1_val_(F32_Fnn, fN_1), mk_val__1_val_(F32_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F32_Fnn)), fN_1, fN_2)))

  ;; test.spectec:478.6-478.13
  rule fun_relop__case_23{fN_1 : fN, fN_2 : fN}:
    `%%%%%`(F64_valtype, mk_relop__1_relop_(F64_Fnn, GE_relop_Fnn), mk_val__1_val_(F64_Fnn, fN_1), mk_val__1_val_(F64_Fnn, fN_2), mk_val__0_val_(I32_Inn, $fge_($size($valtype_Fnn(F64_Fnn)), fN_1, fN_2)))

;; test.spectec:478.6-478.13
relation relop__is_wf: `%%%%%`(v_valtype : valtype, v_relop_ : relop_, v_val_ : val_, val__0 : val_, ret_val : val_)
  ;; test.spectec:478.6-478.13
  rule relop__is_wf_0{v_valtype : valtype, v_relop_ : relop_, v_val_ : val_, val__0 : val_, ret_val : val_, var_0 : val_}:
    `%%%%%`(v_valtype, v_relop_, v_val_, val__0, ret_val)
    -- fun_relop_: `%%%%%`(v_valtype, v_relop_, v_val_, val__0, var_0)
    -- wf_relop_: `%%`(v_valtype, v_relop_)
    -- wf_val_: `%%`(v_valtype, v_val_)
    -- wf_val_: `%%`(v_valtype, val__0)
    -- if (ret_val = var_0)
    -- wf_val_: `%%`(I32_valtype, ret_val)

;; test.spectec:488.1-488.90
def $convert__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : fN

;; test.spectec:488.6-488.16
relation convert___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : fN)
  ;; test.spectec:488.6-488.16
  rule convert___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : fN}:
    `%%%%%`(v_M, v_N, v_sx, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $convert__(v_M, v_N, v_sx, v_iN))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:486.1-486.36
def $demote__(v_M : M, v_N : N, v_fN : fN) : fN*

;; test.spectec:486.6-486.15
relation demote___is_wf: `%%%%`(v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:486.6-486.15
  rule demote___is_wf_0{v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%%`(v_M, v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_lst = $demote__(v_M, v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:484.1-484.89
def $extend__(v_M : M, v_N : N, v_sx : sx, v_iN : iN) : iN

;; test.spectec:484.6-484.15
relation extend___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : iN)
  ;; test.spectec:484.6-484.15
  rule extend___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_iN : iN, ret_val : iN}:
    `%%%%%`(v_M, v_N, v_sx, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $extend__(v_M, v_N, v_sx, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:487.1-487.37
def $promote__(v_M : M, v_N : N, v_fN : fN) : fN*

;; test.spectec:487.6-487.16
relation promote___is_wf: `%%%%`(v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*)
  ;; test.spectec:487.6-487.16
  rule promote___is_wf_0{v_M : M, v_N : N, v_fN : fN, ret_val_lst : fN*}:
    `%%%%`(v_M, v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_lst = $promote__(v_M, v_N, v_fN))
    -- (wf_fN: `%%`(v_N, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:489.1-489.76
def $reinterpret__(valtype_1 : valtype, valtype_2 : valtype, v_val_ : val_) : val_

;; test.spectec:489.6-489.20
relation reinterpret___is_wf: `%%%%`(valtype_1 : valtype, valtype_2 : valtype, v_val_ : val_, ret_val : val_)
  ;; test.spectec:489.6-489.20
  rule reinterpret___is_wf_0{valtype_1 : valtype, valtype_2 : valtype, v_val_ : val_, ret_val : val_}:
    `%%%%`(valtype_1, valtype_2, v_val_, ret_val)
    -- wf_val_: `%%`(valtype_1, v_val_)
    -- if (ret_val = $reinterpret__(valtype_1, valtype_2, v_val_))
    -- wf_val_: `%%`(valtype_2, ret_val)

;; test.spectec:485.1-485.88
def $trunc__(v_M : M, v_N : N, v_sx : sx, v_fN : fN) : iN?

;; test.spectec:485.6-485.14
relation trunc___is_wf: `%%%%%`(v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?)
  ;; test.spectec:485.6-485.14
  rule trunc___is_wf_0{v_M : M, v_N : N, v_sx : sx, v_fN : fN, ret_val_opt : iN?}:
    `%%%%%`(v_M, v_N, v_sx, v_fN, ret_val_opt)
    -- wf_fN: `%%`(v_M, v_fN)
    -- if (ret_val_opt = $trunc__(v_M, v_N, v_sx, v_fN))
    -- (wf_uN: `%%`(v_N, ret_val))?{ret_val <- ret_val_opt}

;; test.spectec:483.1-483.33
def $wrap__(v_M : M, v_N : N, v_iN : iN) : iN

;; test.spectec:483.6-483.13
relation wrap___is_wf: `%%%%`(v_M : M, v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:483.6-483.13
  rule wrap___is_wf_0{v_M : M, v_N : N, v_iN : iN, ret_val : iN}:
    `%%%%`(v_M, v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_M, v_iN)
    -- if (ret_val = $wrap__(v_M, v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:480.6-480.14
relation fun_cvtop__: `%%%%%`(valtype, valtype, cvtop, val_, val_*)
  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_0{v_sx : sx, v_iN : uN}:
    `%%%%%`(I32_valtype, I64_valtype, EXTEND_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN), [mk_val__0_val_(I64_Inn, $extend__(32, 64, v_sx, v_iN))])

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_1{v_iN : uN}:
    `%%%%%`(I64_valtype, I32_valtype, WRAP_cvtop, mk_val__0_val_(I64_Inn, v_iN), [mk_val__0_val_(I32_Inn, $wrap__(64, 32, v_iN))])

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_2{v_sx : sx, v_fN : fN}:
    `%%%%%`(F32_valtype, I32_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F32_Fnn, v_fN), $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_33)?{iter_0_33 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_3{v_sx : sx, v_fN : fN}:
    `%%%%%`(F64_valtype, I32_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F64_Fnn, v_fN), $list_(syntax val_, mk_val__0_val_(I32_Inn, iter_0_34)?{iter_0_34 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I32_Inn)), v_sx, v_fN)}))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_4{v_sx : sx, v_fN : fN}:
    `%%%%%`(F32_valtype, I64_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F32_Fnn, v_fN), $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_35)?{iter_0_35 <- $trunc__($size($valtype_Fnn(F32_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_5{v_sx : sx, v_fN : fN}:
    `%%%%%`(F64_valtype, I64_valtype, TRUNC_cvtop(v_sx), mk_val__1_val_(F64_Fnn, v_fN), $list_(syntax val_, mk_val__0_val_(I64_Inn, iter_0_36)?{iter_0_36 <- $trunc__($size($valtype_Fnn(F64_Fnn)), $size($valtype_Inn(I64_Inn)), v_sx, v_fN)}))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_6{v_fN : fN}:
    `%%%%%`(F32_valtype, F64_valtype, PROMOTE_cvtop, mk_val__1_val_(F32_Fnn, v_fN), mk_val__1_val_(F64_Fnn, iter_0)*{iter_0 <- $promote__(32, 64, v_fN)})

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_7{v_fN : fN}:
    `%%%%%`(F64_valtype, F32_valtype, DEMOTE_cvtop, mk_val__1_val_(F64_Fnn, v_fN), mk_val__1_val_(F32_Fnn, iter_0)*{iter_0 <- $demote__(64, 32, v_fN)})

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_8{v_sx : sx, v_iN : uN}:
    `%%%%%`(I32_valtype, F32_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN), [mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN))])

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_9{v_sx : sx, v_iN : uN}:
    `%%%%%`(I64_valtype, F32_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I64_Inn, v_iN), [mk_val__1_val_(F32_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F32_Fnn)), v_sx, v_iN))])

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_10{v_sx : sx, v_iN : uN}:
    `%%%%%`(I32_valtype, F64_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I32_Inn, v_iN), [mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I32_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN))])

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_11{v_sx : sx, v_iN : uN}:
    `%%%%%`(I64_valtype, F64_valtype, CONVERT_cvtop(v_sx), mk_val__0_val_(I64_Inn, v_iN), [mk_val__1_val_(F64_Fnn, $convert__($size($valtype_Inn(I64_Inn)), $size($valtype_Fnn(F64_Fnn)), v_sx, v_iN))])

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_12{v_iN : uN}:
    `%%%%%`(I32_valtype, F32_valtype, REINTERPRET_cvtop, mk_val__0_val_(I32_Inn, v_iN), [$reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I32_Inn, v_iN))])
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F32_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_13{v_iN : uN}:
    `%%%%%`(I64_valtype, F32_valtype, REINTERPRET_cvtop, mk_val__0_val_(I64_Inn, v_iN), [$reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F32_Fnn), mk_val__0_val_(I64_Inn, v_iN))])
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F32_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_14{v_iN : uN}:
    `%%%%%`(I32_valtype, F64_valtype, REINTERPRET_cvtop, mk_val__0_val_(I32_Inn, v_iN), [$reinterpret__($valtype_Inn(I32_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I32_Inn, v_iN))])
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F64_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_15{v_iN : uN}:
    `%%%%%`(I64_valtype, F64_valtype, REINTERPRET_cvtop, mk_val__0_val_(I64_Inn, v_iN), [$reinterpret__($valtype_Inn(I64_Inn), $valtype_Fnn(F64_Fnn), mk_val__0_val_(I64_Inn, v_iN))])
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F64_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_16{v_fN : fN}:
    `%%%%%`(F32_valtype, I32_valtype, REINTERPRET_cvtop, mk_val__1_val_(F32_Fnn, v_fN), [$reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F32_Fnn, v_fN))])
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F32_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_17{v_fN : fN}:
    `%%%%%`(F64_valtype, I32_valtype, REINTERPRET_cvtop, mk_val__1_val_(F64_Fnn, v_fN), [$reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I32_Inn), mk_val__1_val_(F64_Fnn, v_fN))])
    -- if ($size($valtype_Inn(I32_Inn)) = $size($valtype_Fnn(F64_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_18{v_fN : fN}:
    `%%%%%`(F32_valtype, I64_valtype, REINTERPRET_cvtop, mk_val__1_val_(F32_Fnn, v_fN), [$reinterpret__($valtype_Fnn(F32_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F32_Fnn, v_fN))])
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F32_Fnn)))

  ;; test.spectec:480.6-480.14
  rule fun_cvtop___case_19{v_fN : fN}:
    `%%%%%`(F64_valtype, I64_valtype, REINTERPRET_cvtop, mk_val__1_val_(F64_Fnn, v_fN), [$reinterpret__($valtype_Fnn(F64_Fnn), $valtype_Inn(I64_Inn), mk_val__1_val_(F64_Fnn, v_fN))])
    -- if ($size($valtype_Inn(I64_Inn)) = $size($valtype_Fnn(F64_Fnn)))

;; test.spectec:480.6-480.14
relation cvtop___is_wf: `%%%%%`(valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop, v_val_ : val_, ret_val_lst : val_*)
  ;; test.spectec:480.6-480.14
  rule cvtop___is_wf_0{valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop, v_val_ : val_, ret_val_lst : val_*, var_0 : val_*}:
    `%%%%%`(valtype_1, valtype_2, v_cvtop, v_val_, ret_val_lst)
    -- fun_cvtop__: `%%%%%`(valtype_1, valtype_2, v_cvtop, v_val_, var_0)
    -- wf_val_: `%%`(valtype_1, v_val_)
    -- if (ret_val_lst = var_0)
    -- (wf_val_: `%%`(valtype_2, ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:500.1-500.102
def $ibytes_(v_N : N, v_iN : iN) : byte*

;; test.spectec:500.6-500.14
relation ibytes__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val_lst : byte*)
  ;; test.spectec:500.6-500.14
  rule ibytes__is_wf_0{v_N : N, v_iN : iN, ret_val_lst : byte*}:
    `%%%`(v_N, v_iN, ret_val_lst)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val_lst = $ibytes_(v_N, v_iN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:501.1-501.102
def $fbytes_(v_N : N, v_fN : fN) : byte*

;; test.spectec:501.6-501.14
relation fbytes__is_wf: `%%%`(v_N : N, v_fN : fN, ret_val_lst : byte*)
  ;; test.spectec:501.6-501.14
  rule fbytes__is_wf_0{v_N : N, v_fN : fN, ret_val_lst : byte*}:
    `%%%`(v_N, v_fN, ret_val_lst)
    -- wf_fN: `%%`(v_N, v_fN)
    -- if (ret_val_lst = $fbytes_(v_N, v_fN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:502.1-502.75
def $bytes_(v_valtype : valtype, v_val_ : val_) : byte*

;; test.spectec:502.6-502.13
relation bytes__is_wf: `%%%`(v_valtype : valtype, v_val_ : val_, ret_val_lst : byte*)
  ;; test.spectec:502.6-502.13
  rule bytes__is_wf_0{v_valtype : valtype, v_val_ : val_, ret_val_lst : byte*}:
    `%%%`(v_valtype, v_val_, ret_val_lst)
    -- wf_val_: `%%`(v_valtype, v_val_)
    -- if (ret_val_lst = $bytes_(v_valtype, v_val_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:504.1-504.75
def $inv_ibytes_(v_N : N, var_0_lst : byte*) : iN

;; test.spectec:504.6-504.18
relation inv_ibytes__is_wf: `%%%`(v_N : N, var_0_lst : byte*, ret_val : iN)
  ;; test.spectec:504.6-504.18
  rule inv_ibytes__is_wf_0{v_N : N, var_0_lst : byte*, ret_val : iN}:
    `%%%`(v_N, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_ibytes_(v_N, var_0_lst))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:505.1-505.75
def $inv_fbytes_(v_N : N, var_0_lst : byte*) : fN

;; test.spectec:505.6-505.18
relation inv_fbytes__is_wf: `%%%`(v_N : N, var_0_lst : byte*, ret_val : fN)
  ;; test.spectec:505.6-505.18
  rule inv_fbytes__is_wf_0{v_N : N, var_0_lst : byte*, ret_val : fN}:
    `%%%`(v_N, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_fbytes_(v_N, var_0_lst))
    -- wf_fN: `%%`(v_N, ret_val)

;; test.spectec:506.1-506.73
def $inv_bytes_(v_valtype : valtype, var_0_lst : byte*) : val_

;; test.spectec:506.6-506.17
relation inv_bytes__is_wf: `%%%`(v_valtype : valtype, var_0_lst : byte*, ret_val : val_)
  ;; test.spectec:506.6-506.17
  rule inv_bytes__is_wf_0{v_valtype : valtype, var_0_lst : byte*, ret_val : val_}:
    `%%%`(v_valtype, var_0_lst, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $inv_bytes_(v_valtype, var_0_lst))
    -- wf_val_: `%%`(v_valtype, ret_val)

;; test.spectec:522.1-522.29
def $inot_(v_N : N, v_iN : iN) : iN

;; test.spectec:522.6-522.12
relation inot__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : iN)
  ;; test.spectec:522.6-522.12
  rule inot__is_wf_0{v_N : N, v_iN : iN, ret_val : iN}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $inot_(v_N, v_iN))
    -- wf_uN: `%%`(v_N, ret_val)

;; test.spectec:534.1-534.27
def $inez_(v_N : N, v_iN : iN) : u32
  ;; test.spectec:572.1-572.38
  def $inez_{v_N : nat, i_1 : uN}(v_N, i_1) = mk_uN_u32($bool(($proj_uN_0(i_1).0 =/= 0)))

;; test.spectec:534.6-534.12
relation inez__is_wf: `%%%`(v_N : N, v_iN : iN, ret_val : u32)
  ;; test.spectec:534.6-534.12
  rule inez__is_wf_0{v_N : N, v_iN : iN, ret_val : u32}:
    `%%%`(v_N, v_iN, ret_val)
    -- wf_uN: `%%`(v_N, v_iN)
    -- if (ret_val = $inez_(v_N, v_iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:698.1-698.39
syntax addr = nat

;; test.spectec:699.1-699.53
syntax funcaddr = addr

;; test.spectec:700.1-700.53
syntax globaladdr = addr

;; test.spectec:701.1-701.51
syntax tableaddr = addr

;; test.spectec:702.1-702.50
syntax memaddr = addr

;; test.spectec:713.1-714.70
syntax externaddr = 
  | FUNC(v_funcaddr : funcaddr)
  | GLOBAL(v_globaladdr : globaladdr)
  | TABLE(v_tableaddr : tableaddr)
  | MEM(v_memaddr : memaddr)

;; test.spectec:725.1-726.55
syntax val = 
  | CONST(v_valtype : valtype, val_)

;; test.spectec:725.8-725.11
relation wf_val: `%`(val)
  ;; test.spectec:725.8-725.11
  rule val_case_0{v_valtype : valtype, var_0 : val_}:
    `%`(CONST_val(v_valtype, var_0))
    -- wf_val_: `%%`(v_valtype, var_0)

;; test.spectec:728.1-729.22
syntax result = 
  | _VALS(val_lst : val*)
  | TRAP

;; test.spectec:728.8-728.14
relation wf_result: `%`(result)
  ;; test.spectec:728.8-728.14
  rule result_case_0{val_lst : val*}:
    `%`(_VALS_result(val_lst))
    -- (wf_val: `%`(v_val))*{v_val <- val_lst}

  ;; test.spectec:728.8-728.14
  rule result_case_1:
    `%`(TRAP_result)

;; test.spectec:754.1-756.22
syntax exportinst = 
{
  NAME name,
  ADDR externaddr
}

;; test.spectec:754.8-754.18
relation wf_exportinst: `%`(exportinst)
  ;; test.spectec:754.8-754.18
  rule exportinst_case_{var_0 : name, var_1 : externaddr}:
    `%`({NAME var_0, ADDR var_1})
    -- wf_name: `%`(var_0)

;; test.spectec:758.1-764.26
syntax moduleinst = 
{
  TYPES functype*,
  FUNCS funcaddr*,
  GLOBALS globaladdr*,
  TABLES tableaddr*,
  MEMS memaddr*,
  EXPORTS exportinst*
}

;; test.spectec:758.8-758.18
relation wf_moduleinst: `%`(moduleinst)
  ;; test.spectec:758.8-758.18
  rule moduleinst_case_{var_0_lst : functype*, var_1_lst : funcaddr*, var_2_lst : globaladdr*, var_3_lst : tableaddr*, var_4_lst : memaddr*, var_5_lst : exportinst*}:
    `%`({TYPES var_0_lst, FUNCS var_1_lst, GLOBALS var_2_lst, TABLES var_3_lst, MEMS var_4_lst, EXPORTS var_5_lst})
    -- (wf_exportinst: `%`(var_5))*{var_5 <- var_5_lst}

;; test.spectec:741.1-744.16
syntax funcinst = 
{
  TYPE functype,
  MODULE moduleinst,
  CODE func
}

;; test.spectec:741.8-741.16
relation wf_funcinst: `%`(funcinst)
  ;; test.spectec:741.8-741.16
  rule funcinst_case_{var_0 : functype, var_1 : moduleinst, var_2 : func}:
    `%`({TYPE var_0, MODULE var_1, CODE var_2})
    -- wf_moduleinst: `%`(var_1)
    -- wf_func: `%`(var_2)

;; test.spectec:745.1-747.16
syntax globalinst = 
{
  TYPE globaltype,
  VALUE val
}

;; test.spectec:745.8-745.18
relation wf_globalinst: `%`(globalinst)
  ;; test.spectec:745.8-745.18
  rule globalinst_case_{var_0 : globaltype, var_1 : val}:
    `%`({TYPE var_0, VALUE var_1})
    -- wf_val: `%`(var_1)

;; test.spectec:748.1-750.24
syntax tableinst = 
{
  TYPE tabletype,
  REFS funcaddr?*
}

;; test.spectec:748.8-748.17
relation wf_tableinst: `%`(tableinst)
  ;; test.spectec:748.8-748.17
  rule tableinst_case_{var_0 : tabletype, var_1_opt_lst : funcaddr?*}:
    `%`({TYPE var_0, REFS var_1_opt_lst})
    -- wf_limits: `%`(var_0)

;; test.spectec:751.1-753.18
syntax meminst = 
{
  TYPE memtype,
  BYTES byte*
}

;; test.spectec:751.8-751.15
relation wf_meminst: `%`(meminst)
  ;; test.spectec:751.8-751.15
  rule meminst_case_{var_0 : memtype, var_1_lst : byte*}:
    `%`({TYPE var_0, BYTES var_1_lst})
    -- wf_limits: `%`(var_0)
    -- (wf_byte: `%`(var_1))*{var_1 <- var_1_lst}

;; test.spectec:776.1-780.20
syntax store = 
{
  FUNCS funcinst*,
  GLOBALS globalinst*,
  TABLES tableinst*,
  MEMS meminst*
}

;; test.spectec:776.8-776.13
relation wf_store: `%`(store)
  ;; test.spectec:776.8-776.13
  rule store_case_{var_0_lst : funcinst*, var_1_lst : globalinst*, var_2_lst : tableinst*, var_3_lst : meminst*}:
    `%`({FUNCS var_0_lst, GLOBALS var_1_lst, TABLES var_2_lst, MEMS var_3_lst})
    -- (wf_funcinst: `%`(var_0))*{var_0 <- var_0_lst}
    -- (wf_globalinst: `%`(var_1))*{var_1 <- var_1_lst}
    -- (wf_tableinst: `%`(var_2))*{var_2 <- var_2_lst}
    -- (wf_meminst: `%`(var_3))*{var_3 <- var_3_lst}

;; test.spectec:782.1-784.24
syntax frame = 
{
  LOCALS val*,
  MODULE moduleinst
}

;; test.spectec:782.8-782.13
relation wf_frame: `%`(frame)
  ;; test.spectec:782.8-782.13
  rule frame_case_{var_0_lst : val*, var_1 : moduleinst}:
    `%`({LOCALS var_0_lst, MODULE var_1})
    -- (wf_val: `%`(var_0))*{var_0 <- var_0_lst}
    -- wf_moduleinst: `%`(var_1)

;; test.spectec:786.1-786.47
syntax state = 
  | mk_state(v_store : store, v_frame : frame)

;; test.spectec:786.8-786.13
relation wf_state: `%`(state)
  ;; test.spectec:786.8-786.13
  rule state_case_0{v_store : store, v_frame : frame}:
    `%`(mk_state_state(v_store, v_frame))
    -- wf_store: `%`(v_store)
    -- wf_frame: `%`(v_frame)

;; test.spectec:798.1-803.9
rec {

;; test.spectec:798.1-803.9
syntax admininstr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT
  | BLOCK(v_blocktype : blocktype, instr_lst : instr*)
  | LOOP(v_blocktype : blocktype, instr_lst : instr*)
  | `IF%%ELSE%`(v_blocktype : blocktype, instr_lst : instr*, instr_lst : instr*)
  | BR(v_labelidx : labelidx)
  | BR_IF(v_labelidx : labelidx)
  | BR_TABLE(labelidx_lst : labelidx*, v_labelidx : labelidx)
  | CALL(v_funcidx : funcidx)
  | CALL_INDIRECT(v_typeidx : typeidx)
  | RETURN
  | CONST(v_valtype : valtype, val_)
  | UNOP(v_valtype : valtype, unop_)
  | BINOP(v_valtype : valtype, binop_)
  | TESTOP(v_valtype : valtype, testop_)
  | RELOP(v_valtype : valtype, relop_)
  | CVTOP(valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop)
  | LOCAL_GET(v_localidx : localidx)
  | LOCAL_SET(v_localidx : localidx)
  | LOCAL_TEE(v_localidx : localidx)
  | GLOBAL_GET(v_globalidx : globalidx)
  | GLOBAL_SET(v_globalidx : globalidx)
  | LOAD(v_valtype : valtype, loadop_?, v_memarg : memarg)
  | STORE(v_valtype : valtype, sz_opt : sz?, v_memarg : memarg)
  | MEMORY_SIZE
  | MEMORY_GROW
  | CALL_ADDR(v_funcaddr : funcaddr)
  | `LABEL_%{%}%`(v_n : n, instr_lst : instr*, admininstr_lst : admininstr*)
  | `FRAME_%{%}%`(v_n : n, v_frame : frame, admininstr_lst : admininstr*)
  | TRAP
}

def $admininstr_instr(var_0 : instr) : admininstr
  def $admininstr_instr(NOP_instr) = NOP_admininstr
  def $admininstr_instr(UNREACHABLE_instr) = UNREACHABLE_admininstr
  def $admininstr_instr(DROP_instr) = DROP_admininstr
  def $admininstr_instr(SELECT_instr) = SELECT_admininstr
  def $admininstr_instr{x0 : blocktype, x1 : instr*}(BLOCK_instr(x0, x1)) = BLOCK_admininstr(x0, x1)
  def $admininstr_instr{x0 : blocktype, x1 : instr*}(LOOP_instr(x0, x1)) = LOOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : blocktype, x1 : instr*, x2 : instr*}(`IF%%ELSE%`_instr(x0, x1, x2)) = `IF%%ELSE%`_admininstr(x0, x1, x2)
  def $admininstr_instr{x0 : labelidx}(BR_instr(x0)) = BR_admininstr(x0)
  def $admininstr_instr{x0 : labelidx}(BR_IF_instr(x0)) = BR_IF_admininstr(x0)
  def $admininstr_instr{x0 : labelidx*, x1 : labelidx}(BR_TABLE_instr(x0, x1)) = BR_TABLE_admininstr(x0, x1)
  def $admininstr_instr{x0 : funcidx}(CALL_instr(x0)) = CALL_admininstr(x0)
  def $admininstr_instr{x0 : typeidx}(CALL_INDIRECT_instr(x0)) = CALL_INDIRECT_admininstr(x0)
  def $admininstr_instr(RETURN_instr) = RETURN_admininstr
  def $admininstr_instr{x0 : valtype, x1 : val_}(CONST_instr(x0, x1)) = CONST_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : unop_}(UNOP_instr(x0, x1)) = UNOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : binop_}(BINOP_instr(x0, x1)) = BINOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : testop_}(TESTOP_instr(x0, x1)) = TESTOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : relop_}(RELOP_instr(x0, x1)) = RELOP_admininstr(x0, x1)
  def $admininstr_instr{x0 : valtype, x1 : valtype, x2 : cvtop}(CVTOP_instr(x0, x1, x2)) = CVTOP_admininstr(x0, x1, x2)
  def $admininstr_instr{x0 : localidx}(LOCAL_GET_instr(x0)) = LOCAL_GET_admininstr(x0)
  def $admininstr_instr{x0 : localidx}(LOCAL_SET_instr(x0)) = LOCAL_SET_admininstr(x0)
  def $admininstr_instr{x0 : localidx}(LOCAL_TEE_instr(x0)) = LOCAL_TEE_admininstr(x0)
  def $admininstr_instr{x0 : globalidx}(GLOBAL_GET_instr(x0)) = GLOBAL_GET_admininstr(x0)
  def $admininstr_instr{x0 : globalidx}(GLOBAL_SET_instr(x0)) = GLOBAL_SET_admininstr(x0)
  def $admininstr_instr{x0 : valtype, x1 : loadop_?, x2 : memarg}(LOAD_instr(x0, x1, x2)) = LOAD_admininstr(x0, x1, x2)
  def $admininstr_instr{x0 : valtype, x1 : sz?, x2 : memarg}(STORE_instr(x0, x1, x2)) = STORE_admininstr(x0, x1, x2)
  def $admininstr_instr(MEMORY_SIZE_instr) = MEMORY_SIZE_admininstr
  def $admininstr_instr(MEMORY_GROW_instr) = MEMORY_GROW_admininstr

def $admininstr_val(var_0 : val) : admininstr
  def $admininstr_val{x0 : valtype, x1 : val_}(CONST_val(x0, x1)) = CONST_admininstr(x0, x1)

;; test.spectec:798.1-803.9
rec {

;; test.spectec:798.8-798.18
relation wf_admininstr: `%`(admininstr)
  ;; test.spectec:798.8-798.18
  rule admininstr_case_0:
    `%`(NOP_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_1:
    `%`(UNREACHABLE_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_2:
    `%`(DROP_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_3:
    `%`(SELECT_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_4{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(BLOCK_admininstr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_5{v_blocktype : blocktype, instr_lst : instr*}:
    `%`(LOOP_admininstr(v_blocktype, instr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_6{v_blocktype : blocktype, instr_lst : instr*, instr_lst_0_lst : instr*}:
    `%`(`IF%%ELSE%`_admininstr(v_blocktype, instr_lst, instr_lst_0_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_instr: `%`(instr_lst_0))*{instr_lst_0 <- instr_lst_0_lst}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_7{v_labelidx : labelidx}:
    `%`(BR_admininstr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_8{v_labelidx : labelidx}:
    `%`(BR_IF_admininstr(v_labelidx))
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_9{labelidx_lst : labelidx*, v_labelidx : labelidx}:
    `%`(BR_TABLE_admininstr(labelidx_lst, v_labelidx))
    -- (wf_uN: `%%`(32, v_labelidx))*{v_labelidx <- labelidx_lst}
    -- wf_uN: `%%`(32, v_labelidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_10{v_funcidx : funcidx}:
    `%`(CALL_admininstr(v_funcidx))
    -- wf_uN: `%%`(32, v_funcidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_11{v_typeidx : typeidx}:
    `%`(CALL_INDIRECT_admininstr(v_typeidx))
    -- wf_uN: `%%`(32, v_typeidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_12:
    `%`(RETURN_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_13{v_valtype : valtype, var_0 : val_}:
    `%`(CONST_admininstr(v_valtype, var_0))
    -- wf_val_: `%%`(v_valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_14{v_valtype : valtype, var_0 : unop_}:
    `%`(UNOP_admininstr(v_valtype, var_0))
    -- wf_unop_: `%%`(v_valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_15{v_valtype : valtype, var_0 : binop_}:
    `%`(BINOP_admininstr(v_valtype, var_0))
    -- wf_binop_: `%%`(v_valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_16{v_valtype : valtype, var_0 : testop_}:
    `%`(TESTOP_admininstr(v_valtype, var_0))
    -- wf_testop_: `%%`(v_valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_17{v_valtype : valtype, var_0 : relop_}:
    `%`(RELOP_admininstr(v_valtype, var_0))
    -- wf_relop_: `%%`(v_valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_18{valtype_1 : valtype, valtype_2 : valtype, v_cvtop : cvtop}:
    `%`(CVTOP_admininstr(valtype_1, valtype_2, v_cvtop))
    -- if (valtype_1 =/= valtype_2)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_19{v_localidx : localidx}:
    `%`(LOCAL_GET_admininstr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_20{v_localidx : localidx}:
    `%`(LOCAL_SET_admininstr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_21{v_localidx : localidx}:
    `%`(LOCAL_TEE_admininstr(v_localidx))
    -- wf_uN: `%%`(32, v_localidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_22{v_globalidx : globalidx}:
    `%`(GLOBAL_GET_admininstr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_23{v_globalidx : globalidx}:
    `%`(GLOBAL_SET_admininstr(v_globalidx))
    -- wf_uN: `%%`(32, v_globalidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_24{v_valtype : valtype, var_0_opt : loadop_?, v_memarg : memarg}:
    `%`(LOAD_admininstr(v_valtype, var_0_opt, v_memarg))
    -- (wf_loadop_: `%%`(v_valtype, var_0))?{var_0 <- var_0_opt}
    -- wf_memarg: `%`(v_memarg)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_25{Inn_opt : Inn?, valtype_opt : valtype?, v_valtype : valtype, sz_opt : sz?, v_memarg : memarg}:
    `%`(STORE_admininstr(v_valtype, sz_opt, v_memarg))
    -- (wf_sz: `%`(v_sz))?{v_sz <- sz_opt}
    -- wf_memarg: `%`(v_memarg)
    -- if ((Inn_opt = ?()) <=> (sz_opt = ?()))
    -- if ((Inn_opt = ?()) <=> (valtype_opt = ?()))
    -- (if ((v_valtype = $valtype_Inn(v_Inn)) /\ ($proj_sz_0(v_sz).0 < $size($valtype_Inn(v_Inn)))))?{v_Inn <- Inn_opt, v_sz <- sz_opt, v_valtype <- valtype_opt}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_26:
    `%`(MEMORY_SIZE_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_27:
    `%`(MEMORY_GROW_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_28{v_funcaddr : funcaddr}:
    `%`(CALL_ADDR_admininstr(v_funcaddr))

  ;; test.spectec:798.8-798.18
  rule admininstr_case_29{v_n : n, instr_lst : instr*, admininstr_lst : admininstr*}:
    `%`(`LABEL_%{%}%`_admininstr(v_n, instr_lst, admininstr_lst))
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_30{v_n : n, v_frame : frame, admininstr_lst : admininstr*}:
    `%`(`FRAME_%{%}%`_admininstr(v_n, v_frame, admininstr_lst))
    -- wf_frame: `%`(v_frame)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_31:
    `%`(TRAP_admininstr)
}

;; test.spectec:787.1-787.62
syntax config = 
  | mk_config(v_state : state, admininstr_lst : admininstr*)

;; test.spectec:787.8-787.14
relation wf_config: `%`(config)
  ;; test.spectec:787.8-787.14
  rule config_case_0{v_state : state, admininstr_lst : admininstr*}:
    `%`(mk_config_config(v_state, admininstr_lst))
    -- wf_state: `%`(v_state)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

;; test.spectec:816.1-816.29
def $default_(v_valtype : valtype) : val
  ;; test.spectec:818.1-818.35
  def $default_(I32_valtype) = CONST_val(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(0)))
  ;; test.spectec:819.1-819.35
  def $default_(I64_valtype) = CONST_val(I64_valtype, mk_val__0_val_(I64_Inn, mk_uN_uN(0)))
  ;; test.spectec:820.1-820.44
  def $default_(F32_valtype) = CONST_val(F32_valtype, mk_val__1_val_(F32_Fnn, $fzero(32)))
  ;; test.spectec:821.1-821.44
  def $default_(F64_valtype) = CONST_val(F64_valtype, mk_val__1_val_(F64_Fnn, $fzero(64)))

;; test.spectec:816.6-816.15
relation default__is_wf: `%%`(v_valtype : valtype, ret_val : val)
  ;; test.spectec:816.6-816.15
  rule default__is_wf_0{v_valtype : valtype, ret_val : val}:
    `%%`(v_valtype, ret_val)
    -- if (ret_val = $default_(v_valtype))
    -- wf_val: `%`(ret_val)

;; test.spectec:826.1-826.63
rec {

;; test.spectec:826.6-826.14
relation fun_funcsxa: `%%`(externaddr*, funcaddr*)
  ;; test.spectec:826.6-826.14
  rule fun_funcsxa_case_0:
    `%%`([], [])

  ;; test.spectec:826.6-826.14
  rule fun_funcsxa_case_1{fa : nat, xv_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([FUNC_externaddr(fa)] ++ xv_lst, [fa] ++ var_0)
    -- fun_funcsxa: `%%`(xv_lst, var_0)

  ;; test.spectec:826.6-826.14
  rule fun_funcsxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_funcsxa: `%%`(xv_lst, var_0)
}

;; test.spectec:827.1-827.65
rec {

;; test.spectec:827.6-827.16
relation fun_globalsxa: `%%`(externaddr*, globaladdr*)
  ;; test.spectec:827.6-827.16
  rule fun_globalsxa_case_0:
    `%%`([], [])

  ;; test.spectec:827.6-827.16
  rule fun_globalsxa_case_1{ga : nat, xv_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([GLOBAL_externaddr(ga)] ++ xv_lst, [ga] ++ var_0)
    -- fun_globalsxa: `%%`(xv_lst, var_0)

  ;; test.spectec:827.6-827.16
  rule fun_globalsxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_globalsxa: `%%`(xv_lst, var_0)
}

;; test.spectec:828.1-828.64
rec {

;; test.spectec:828.6-828.15
relation fun_tablesxa: `%%`(externaddr*, tableaddr*)
  ;; test.spectec:828.6-828.15
  rule fun_tablesxa_case_0:
    `%%`([], [])

  ;; test.spectec:828.6-828.15
  rule fun_tablesxa_case_1{ta : nat, xv_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([TABLE_externaddr(ta)] ++ xv_lst, [ta] ++ var_0)
    -- fun_tablesxa: `%%`(xv_lst, var_0)

  ;; test.spectec:828.6-828.15
  rule fun_tablesxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_tablesxa: `%%`(xv_lst, var_0)
}

;; test.spectec:829.1-829.62
rec {

;; test.spectec:829.6-829.13
relation fun_memsxa: `%%`(externaddr*, memaddr*)
  ;; test.spectec:829.6-829.13
  rule fun_memsxa_case_0:
    `%%`([], [])

  ;; test.spectec:829.6-829.13
  rule fun_memsxa_case_1{ma : nat, xv_lst : externaddr*, var_0 : memaddr*}:
    `%%`([MEM_externaddr(ma)] ++ xv_lst, [ma] ++ var_0)
    -- fun_memsxa: `%%`(xv_lst, var_0)

  ;; test.spectec:829.6-829.13
  rule fun_memsxa_case_2{v_externaddr : externaddr, xv_lst : externaddr*, var_0 : memaddr*}:
    `%%`([v_externaddr] ++ xv_lst, var_0)
    -- fun_memsxa: `%%`(xv_lst, var_0)
}

;; test.spectec:855.1-855.57
def $fun_store(v_state : state) : store
  ;; test.spectec:858.1-858.23
  def $fun_store{s : store, f : frame}(mk_state_state(s, f)) = s

;; test.spectec:855.6-855.12
relation store_is_wf: `%%`(v_state : state, ret_val : store)
  ;; test.spectec:855.6-855.12
  rule store_is_wf_0{v_state : state, ret_val : store}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fun_store(v_state))
    -- wf_store: `%`(ret_val)

;; test.spectec:856.1-856.57
def $fun_frame(v_state : state) : frame
  ;; test.spectec:859.1-859.23
  def $fun_frame{s : store, f : frame}(mk_state_state(s, f)) = f

;; test.spectec:856.6-856.12
relation frame_is_wf: `%%`(v_state : state, ret_val : frame)
  ;; test.spectec:856.6-856.12
  rule frame_is_wf_0{v_state : state, ret_val : frame}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fun_frame(v_state))
    -- wf_frame: `%`(ret_val)

;; test.spectec:862.1-862.64
def $fun_funcaddr(v_state : state) : funcaddr*
  ;; test.spectec:863.1-863.39
  def $fun_funcaddr{s : store, f : frame}(mk_state_state(s, f)) = f.MODULE_frame.FUNCS_moduleinst

;; test.spectec:865.1-865.57
def $fun_funcinst(v_state : state) : funcinst*
  ;; test.spectec:871.1-871.32
  def $fun_funcinst{s : store, f : frame}(mk_state_state(s, f)) = s.FUNCS_store

;; test.spectec:865.6-865.15
relation funcinst_is_wf: `%%`(v_state : state, ret_val_lst : funcinst*)
  ;; test.spectec:865.6-865.15
  rule funcinst_is_wf_0{v_state : state, ret_val_lst : funcinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_funcinst(v_state))
    -- (wf_funcinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:866.1-866.59
def $fun_globalinst(v_state : state) : globalinst*
  ;; test.spectec:872.1-872.36
  def $fun_globalinst{s : store, f : frame}(mk_state_state(s, f)) = s.GLOBALS_store

;; test.spectec:866.6-866.17
relation globalinst_is_wf: `%%`(v_state : state, ret_val_lst : globalinst*)
  ;; test.spectec:866.6-866.17
  rule globalinst_is_wf_0{v_state : state, ret_val_lst : globalinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_globalinst(v_state))
    -- (wf_globalinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:867.1-867.58
def $fun_tableinst(v_state : state) : tableinst*
  ;; test.spectec:873.1-873.34
  def $fun_tableinst{s : store, f : frame}(mk_state_state(s, f)) = s.TABLES_store

;; test.spectec:867.6-867.16
relation tableinst_is_wf: `%%`(v_state : state, ret_val_lst : tableinst*)
  ;; test.spectec:867.6-867.16
  rule tableinst_is_wf_0{v_state : state, ret_val_lst : tableinst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_tableinst(v_state))
    -- (wf_tableinst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:868.1-868.56
def $fun_meminst(v_state : state) : meminst*
  ;; test.spectec:874.1-874.30
  def $fun_meminst{s : store, f : frame}(mk_state_state(s, f)) = s.MEMS_store

;; test.spectec:868.6-868.14
relation meminst_is_wf: `%%`(v_state : state, ret_val_lst : meminst*)
  ;; test.spectec:868.6-868.14
  rule meminst_is_wf_0{v_state : state, ret_val_lst : meminst*}:
    `%%`(v_state, ret_val_lst)
    -- wf_state: `%`(v_state)
    -- if (ret_val_lst = $fun_meminst(v_state))
    -- (wf_meminst: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:869.1-869.58
def $fun_moduleinst(v_state : state) : moduleinst
  ;; test.spectec:875.1-875.35
  def $fun_moduleinst{s : store, f : frame}(mk_state_state(s, f)) = f.MODULE_frame

;; test.spectec:869.6-869.17
relation moduleinst_is_wf: `%%`(v_state : state, ret_val : moduleinst)
  ;; test.spectec:869.6-869.17
  rule moduleinst_is_wf_0{v_state : state, ret_val : moduleinst}:
    `%%`(v_state, ret_val)
    -- wf_state: `%`(v_state)
    -- if (ret_val = $fun_moduleinst(v_state))
    -- wf_moduleinst: `%`(ret_val)

;; test.spectec:877.1-877.66
def $fun_type(v_state : state, v_typeidx : typeidx) : functype
  ;; test.spectec:884.1-884.41
  def $fun_type{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = f.MODULE_frame.TYPES_moduleinst[$proj_uN_0(x).0]

;; test.spectec:878.1-878.66
def $fun_func(v_state : state, v_funcidx : funcidx) : funcinst
  ;; test.spectec:885.1-885.50
  def $fun_func{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.FUNCS_store[f.MODULE_frame.FUNCS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:878.6-878.11
relation func_is_wf: `%%%`(v_state : state, v_funcidx : funcidx, ret_val : funcinst)
  ;; test.spectec:878.6-878.11
  rule func_is_wf_0{v_state : state, v_funcidx : funcidx, ret_val : funcinst}:
    `%%%`(v_state, v_funcidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_funcidx)
    -- if (ret_val = $fun_func(v_state, v_funcidx))
    -- wf_funcinst: `%`(ret_val)

;; test.spectec:879.1-879.68
def $fun_global(v_state : state, v_globalidx : globalidx) : globalinst
  ;; test.spectec:886.1-886.56
  def $fun_global{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:879.6-879.13
relation global_is_wf: `%%%`(v_state : state, v_globalidx : globalidx, ret_val : globalinst)
  ;; test.spectec:879.6-879.13
  rule global_is_wf_0{v_state : state, v_globalidx : globalidx, ret_val : globalinst}:
    `%%%`(v_state, v_globalidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_globalidx)
    -- if (ret_val = $fun_global(v_state, v_globalidx))
    -- wf_globalinst: `%`(ret_val)

;; test.spectec:880.1-880.67
def $fun_table(v_state : state, v_tableidx : tableidx) : tableinst
  ;; test.spectec:887.1-887.53
  def $fun_table{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:880.6-880.12
relation table_is_wf: `%%%`(v_state : state, v_tableidx : tableidx, ret_val : tableinst)
  ;; test.spectec:880.6-880.12
  rule table_is_wf_0{v_state : state, v_tableidx : tableidx, ret_val : tableinst}:
    `%%%`(v_state, v_tableidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- if (ret_val = $fun_table(v_state, v_tableidx))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:881.1-881.65
def $fun_mem(v_state : state, v_memidx : memidx) : meminst
  ;; test.spectec:888.1-888.47
  def $fun_mem{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = s.MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]]

;; test.spectec:881.6-881.10
relation mem_is_wf: `%%%`(v_state : state, v_memidx : memidx, ret_val : meminst)
  ;; test.spectec:881.6-881.10
  rule mem_is_wf_0{v_state : state, v_memidx : memidx, ret_val : meminst}:
    `%%%`(v_state, v_memidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_memidx)
    -- if (ret_val = $fun_mem(v_state, v_memidx))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:882.1-882.67
def $fun_local(v_state : state, v_localidx : localidx) : val
  ;; test.spectec:889.1-889.36
  def $fun_local{s : store, f : frame, x : uN}(mk_state_state(s, f), x) = f.LOCALS_frame[$proj_uN_0(x).0]

;; test.spectec:882.6-882.12
relation local_is_wf: `%%%`(v_state : state, v_localidx : localidx, ret_val : val)
  ;; test.spectec:882.6-882.12
  rule local_is_wf_0{v_state : state, v_localidx : localidx, ret_val : val}:
    `%%%`(v_state, v_localidx, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_localidx)
    -- if (ret_val = $fun_local(v_state, v_localidx))
    -- wf_val: `%`(ret_val)

;; test.spectec:894.1-894.89
def $with_local(v_state : state, v_localidx : localidx, v_val : val) : state
  ;; test.spectec:904.1-904.53
  def $with_local{s : store, f : frame, x : uN, v : val}(mk_state_state(s, f), x, v) = mk_state_state(s, f[LOCALS_frame[$proj_uN_0(x).0] = v])

;; test.spectec:894.6-894.17
relation with_local_is_wf: `%%%%`(v_state : state, v_localidx : localidx, v_val : val, ret_val : state)
  ;; test.spectec:894.6-894.17
  rule with_local_is_wf_0{v_state : state, v_localidx : localidx, v_val : val, ret_val : state}:
    `%%%%`(v_state, v_localidx, v_val, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_localidx)
    -- wf_val: `%`(v_val)
    -- if (ret_val = $with_local(v_state, v_localidx, v_val))
    -- wf_state: `%`(ret_val)

;; test.spectec:895.1-895.96
def $with_global(v_state : state, v_globalidx : globalidx, v_val : val) : state
  ;; test.spectec:905.1-905.79
  def $with_global{s : store, f : frame, x : uN, v : val}(mk_state_state(s, f), x, v) = mk_state_state(s[GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[$proj_uN_0(x).0]].VALUE_globalinst = v], f)

;; test.spectec:895.6-895.18
relation with_global_is_wf: `%%%%`(v_state : state, v_globalidx : globalidx, v_val : val, ret_val : state)
  ;; test.spectec:895.6-895.18
  rule with_global_is_wf_0{v_state : state, v_globalidx : globalidx, v_val : val, ret_val : state}:
    `%%%%`(v_state, v_globalidx, v_val, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_globalidx)
    -- wf_val: `%`(v_val)
    -- if (ret_val = $with_global(v_state, v_globalidx, v_val))
    -- wf_state: `%`(ret_val)

;; test.spectec:896.1-896.97
def $with_table(v_state : state, v_tableidx : tableidx, nat : nat, v_funcaddr : funcaddr) : state
  ;; test.spectec:906.1-906.81
  def $with_table{s : store, f : frame, x : uN, i : nat, a : nat}(mk_state_state(s, f), x, i, a) = mk_state_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]].REFS_tableinst[i] = ?(a)], f)

;; test.spectec:896.6-896.17
relation with_table_is_wf: `%%%%%`(v_state : state, v_tableidx : tableidx, nat : nat, v_funcaddr : funcaddr, ret_val : state)
  ;; test.spectec:896.6-896.17
  rule with_table_is_wf_0{v_state : state, v_tableidx : tableidx, nat : nat, v_funcaddr : funcaddr, ret_val : state}:
    `%%%%%`(v_state, v_tableidx, nat, v_funcaddr, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- if (ret_val = $with_table(v_state, v_tableidx, nat, v_funcaddr))
    -- wf_state: `%`(ret_val)

;; test.spectec:897.1-897.89
def $with_tableinst(v_state : state, v_tableidx : tableidx, v_tableinst : tableinst) : state
  ;; test.spectec:907.1-907.76
  def $with_tableinst{s : store, f : frame, x : uN, ti : tableinst}(mk_state_state(s, f), x, ti) = mk_state_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[$proj_uN_0(x).0]] = ti], f)

;; test.spectec:897.6-897.21
relation with_tableinst_is_wf: `%%%%`(v_state : state, v_tableidx : tableidx, v_tableinst : tableinst, ret_val : state)
  ;; test.spectec:897.6-897.21
  rule with_tableinst_is_wf_0{v_state : state, v_tableidx : tableidx, v_tableinst : tableinst, ret_val : state}:
    `%%%%`(v_state, v_tableidx, v_tableinst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_tableidx)
    -- wf_tableinst: `%`(v_tableinst)
    -- if (ret_val = $with_tableinst(v_state, v_tableidx, v_tableinst))
    -- wf_state: `%`(ret_val)

;; test.spectec:898.1-898.100
def $with_mem(v_state : state, v_memidx : memidx, nat : nat, nat_0 : nat, var_0_lst : byte*) : state
  ;; test.spectec:908.1-908.85
  def $with_mem{s : store, f : frame, x : uN, i : nat, j : nat, b_lst : byte*}(mk_state_state(s, f), x, i, j, b_lst) = mk_state_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]].BYTES_meminst[i : j] = b_lst], f)

;; test.spectec:898.6-898.15
relation with_mem_is_wf: `%%%%%%`(v_state : state, v_memidx : memidx, nat : nat, nat_0 : nat, var_0_lst : byte*, ret_val : state)
  ;; test.spectec:898.6-898.15
  rule with_mem_is_wf_0{v_state : state, v_memidx : memidx, nat : nat, nat_0 : nat, var_0_lst : byte*, ret_val : state}:
    `%%%%%%`(v_state, v_memidx, nat, nat_0, var_0_lst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_memidx)
    -- (wf_byte: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = $with_mem(v_state, v_memidx, nat, nat_0, var_0_lst))
    -- wf_state: `%`(ret_val)

;; test.spectec:899.1-899.87
def $with_meminst(v_state : state, v_memidx : memidx, v_meminst : meminst) : state
  ;; test.spectec:909.1-909.70
  def $with_meminst{s : store, f : frame, x : uN, mi : meminst}(mk_state_state(s, f), x, mi) = mk_state_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[$proj_uN_0(x).0]] = mi], f)

;; test.spectec:899.6-899.19
relation with_meminst_is_wf: `%%%%`(v_state : state, v_memidx : memidx, v_meminst : meminst, ret_val : state)
  ;; test.spectec:899.6-899.19
  rule with_meminst_is_wf_0{v_state : state, v_memidx : memidx, v_meminst : meminst, ret_val : state}:
    `%%%%`(v_state, v_memidx, v_meminst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_uN: `%%`(32, v_memidx)
    -- wf_meminst: `%`(v_meminst)
    -- if (ret_val = $with_meminst(v_state, v_memidx, v_meminst))
    -- wf_state: `%`(ret_val)

;; test.spectec:902.1-902.94
def $with_mems_elem(v_state : state, nat : nat, nat_0 : nat, nat_1 : nat, v_meminst : meminst) : state
  ;; test.spectec:910.1-910.70
  def $with_mems_elem{s : store, f : frame, i : nat, v_n : nat, k : nat, mi : meminst}(mk_state_state(s, f), i, v_n, k, mi) = mk_state_state(s[MEMS_store[i : v_n][k] = mi], f)

;; test.spectec:902.6-902.21
relation with_mems_elem_is_wf: `%%%%%%`(v_state : state, nat : nat, nat_0 : nat, nat_1 : nat, v_meminst : meminst, ret_val : state)
  ;; test.spectec:902.6-902.21
  rule with_mems_elem_is_wf_0{v_state : state, nat : nat, nat_0 : nat, nat_1 : nat, v_meminst : meminst, ret_val : state}:
    `%%%%%%`(v_state, nat, nat_0, nat_1, v_meminst, ret_val)
    -- wf_state: `%`(v_state)
    -- wf_meminst: `%`(v_meminst)
    -- if (ret_val = $with_mems_elem(v_state, nat, nat_0, nat_1, v_meminst))
    -- wf_state: `%`(ret_val)

;; test.spectec:915.6-915.16
relation fun_growtable_before_fun_growtable_case_1: `%%`(tableinst, nat)
  ;; test.spectec:915.6-915.16
  rule fun_growtable_case_0{ti : tableinst, v_n : nat, ti' : tableinst, i : uN, j_opt : u32?, a_lst : addr*, i' : nat}:
    `%%`(ti, v_n)
    -- if (ti = {TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_1)*{a_1 <- a_lst}})
    -- if (i' = (|a_lst| + v_n))
    -- if (ti' = {TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_3)*{a_3 <- a_lst} ++ ?()^v_n{}})
    -- (if (i' <= $proj_uN_0(j_3).0))?{j_3 <- j_opt}
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_4)*{a_4 <- a_lst}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_5)*{a_5 <- a_lst} ++ ?()^v_n{}})

;; test.spectec:915.6-915.16
relation fun_growtable: `%%%`(tableinst, nat, tableinst?)
  ;; test.spectec:915.6-915.16
  rule fun_growtable_case_0{ti : tableinst, v_n : nat, ti' : tableinst, i : uN, j_opt : u32?, a_lst : addr*, i' : nat}:
    `%%%`(ti, v_n, ?(ti'))
    -- if (ti = {TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_1)*{a_1 <- a_lst}})
    -- if (i' = (|a_lst| + v_n))
    -- if (ti' = {TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_3)*{a_3 <- a_lst} ++ ?()^v_n{}})
    -- (if (i' <= $proj_uN_0(j_3).0))?{j_3 <- j_opt}
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(i, j_opt), REFS ?(a_4)*{a_4 <- a_lst}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(i'), j_opt), REFS ?(a_5)*{a_5 <- a_lst} ++ ?()^v_n{}})

  ;; test.spectec:915.6-915.16
  rule fun_growtable_case_1{x0 : tableinst, x1 : nat}:
    `%%%`(x0, x1, ?())
    -- ~ fun_growtable_before_fun_growtable_case_1: `%%`(x0, x1)

;; test.spectec:915.6-915.16
relation growtable_is_wf: `%%%`(v_tableinst : tableinst, nat : nat, ret_val : tableinst)
  ;; test.spectec:915.6-915.16
  rule growtable_is_wf_0{v_tableinst : tableinst, nat : nat, ret_val : tableinst, var_0 : tableinst?}:
    `%%%`(v_tableinst, nat, ret_val)
    -- fun_growtable: `%%%`(v_tableinst, nat, var_0)
    -- wf_tableinst: `%`(v_tableinst)
    -- if (var_0 =/= ?())
    -- if (ret_val = !(var_0))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:916.6-916.17
relation fun_growmemory_before_fun_growmemory_case_1: `%%`(meminst, nat)
  ;; test.spectec:916.6-916.17
  rule fun_growmemory_case_0{mi : meminst, v_n : nat, mi' : meminst, i : u32, j_opt : u32?, b_lst : byte*, i' : rat}:
    `%%`(mi, v_n)
    -- if ({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst} = mi)
    -- if (i' = (((|b_lst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (v_n : nat <:> rat)))
    -- if (mi' = {TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})
    -- (if (i' <= ($proj_uN_0(j_8).0 : nat <:> rat)))?{j_8 <- j_opt}
    -- wf_meminst: `%`({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})

;; test.spectec:916.6-916.17
relation fun_growmemory: `%%%`(meminst, nat, meminst?)
  ;; test.spectec:916.6-916.17
  rule fun_growmemory_case_0{mi : meminst, v_n : nat, mi' : meminst, i : u32, j_opt : u32?, b_lst : byte*, i' : rat}:
    `%%%`(mi, v_n, ?(mi'))
    -- if ({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst} = mi)
    -- if (i' = (((|b_lst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (v_n : nat <:> rat)))
    -- if (mi' = {TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})
    -- (if (i' <= ($proj_uN_0(j_8).0 : nat <:> rat)))?{j_8 <- j_opt}
    -- wf_meminst: `%`({TYPE mk_limits_memtype(i, j_opt), BYTES b_lst})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32((i' : rat <:> nat)), j_opt), BYTES b_lst ++ mk_byte_byte(0)^(v_n * (64 * $Ki)){}})

  ;; test.spectec:916.6-916.17
  rule fun_growmemory_case_1{x0 : meminst, x1 : nat}:
    `%%%`(x0, x1, ?())
    -- ~ fun_growmemory_before_fun_growmemory_case_1: `%%`(x0, x1)

;; test.spectec:916.6-916.17
relation growmemory_is_wf: `%%%`(v_meminst : meminst, nat : nat, ret_val : meminst)
  ;; test.spectec:916.6-916.17
  rule growmemory_is_wf_0{v_meminst : meminst, nat : nat, ret_val : meminst, var_0 : meminst?}:
    `%%%`(v_meminst, nat, ret_val)
    -- fun_growmemory: `%%%`(v_meminst, nat, var_0)
    -- wf_meminst: `%`(v_meminst)
    -- if (var_0 =/= ?())
    -- if (ret_val = !(var_0))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:939.1-942.62
syntax context = 
{
  TYPES functype*,
  FUNCS functype*,
  GLOBALS globaltype*,
  TABLES tabletype*,
  MEMS memtype*,
  LOCALS valtype*,
  LABELS resulttype*,
  RETURN resulttype?
}

;; test.spectec:939.8-939.15
relation wf_context: `%`(context)
  ;; test.spectec:939.8-939.15
  rule context_case_{var_0_lst : functype*, var_1_lst : functype*, var_2_lst : globaltype*, var_3_lst : tabletype*, var_4_lst : memtype*, var_5_lst : valtype*, var_6_lst : resulttype*, var_7_opt : resulttype?}:
    `%`({TYPES var_0_lst, FUNCS var_1_lst, GLOBALS var_2_lst, TABLES var_3_lst, MEMS var_4_lst, LOCALS var_5_lst, LABELS var_6_lst, RETURN var_7_opt})
    -- (wf_limits: `%`(var_3))*{var_3 <- var_3_lst}
    -- (wf_limits: `%`(var_4))*{var_4 <- var_4_lst}

;; test.spectec:952.1-952.66
relation Limits_ok: `|-%:%`(limits, nat)
  ;; test.spectec:960.1-963.23
  rule mk_Limits_ok{v_n : n, m_opt : m?, k : nat}:
    `|-%:%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), k)
    -- if (v_n <= k)
    -- (if ((v_n <= v_m) /\ (v_m <= k)))?{v_m <- m_opt}
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))

;; test.spectec:953.1-953.64
relation Functype_ok: `|-%:OK`(functype)
  ;; test.spectec:965.1-966.23
  rule mk_Functype_ok{t_1_lst : valtype*, t_2_opt : valtype?}:
    `|-%:OK`(mk_functype_functype(t_1_lst, lift(t_2_opt)))

;; test.spectec:954.1-954.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; test.spectec:968.1-969.17
  rule mk_Globaltype_ok{t : valtype}:
    `|-%:OK`(mk_globaltype_globaltype(?(MUT_r_MUT), t))

;; test.spectec:955.1-955.65
relation Tabletype_ok: `|-%:OK`(tabletype)
  ;; test.spectec:971.1-973.38
  rule mk_Tabletype_ok{v_limits : limits}:
    `|-%:OK`(v_limits)
    -- Limits_ok: `|-%:%`(v_limits, ((((2 ^ 32) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- wf_limits: `%`(v_limits)

;; test.spectec:956.1-956.63
relation Memtype_ok: `|-%:OK`(memtype)
  ;; test.spectec:975.1-977.36
  rule mk_Memtype_ok{v_limits : limits}:
    `|-%:OK`(v_limits)
    -- Limits_ok: `|-%:%`(v_limits, (2 ^ 16))
    -- wf_limits: `%`(v_limits)

;; test.spectec:957.1-957.66
relation Externtype_ok: `|-%:OK`(externtype)
  ;; test.spectec:980.1-982.35
  rule func{v_functype : functype}:
    `|-%:OK`(FUNC_externtype(v_functype))
    -- Functype_ok: `|-%:OK`(v_functype)
    -- wf_externtype: `%`(FUNC_externtype(v_functype))

  ;; test.spectec:984.1-986.39
  rule global{v_globaltype : globaltype}:
    `|-%:OK`(GLOBAL_externtype(v_globaltype))
    -- Globaltype_ok: `|-%:OK`(v_globaltype)
    -- wf_externtype: `%`(GLOBAL_externtype(v_globaltype))

  ;; test.spectec:988.1-990.37
  rule table{v_tabletype : tabletype}:
    `|-%:OK`(TABLE_externtype(v_tabletype))
    -- Tabletype_ok: `|-%:OK`(v_tabletype)
    -- wf_externtype: `%`(TABLE_externtype(v_tabletype))

  ;; test.spectec:992.1-994.33
  rule mem{v_memtype : memtype}:
    `|-%:OK`(MEM_externtype(v_memtype))
    -- Memtype_ok: `|-%:OK`(v_memtype)
    -- wf_externtype: `%`(MEM_externtype(v_memtype))

;; test.spectec:1004.1-1004.75
relation Limits_sub: `|-%<:%`(limits, limits)
  ;; test.spectec:1012.1-1015.21
  rule mk_Limits_sub{n_11 : n, n_12 : n, n_21 : n, n_22 : n}:
    `|-%<:%`(mk_limits_limits(mk_uN_u32(n_11), ?(mk_uN_u32(n_12))), mk_limits_limits(mk_uN_u32(n_21), ?(mk_uN_u32(n_22))))
    -- if (n_11 >= n_21)
    -- if (n_12 <= n_22)
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(n_11), ?(mk_uN_u32(n_12))))
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(n_21), ?(mk_uN_u32(n_22))))

;; test.spectec:1005.1-1005.73
relation Functype_sub: `|-%<:%`(functype, functype)
  ;; test.spectec:1017.1-1018.14
  rule mk_Functype_sub{ft : functype}:
    `|-%<:%`(ft, ft)

;; test.spectec:1006.1-1006.75
relation Globaltype_sub: `|-%<:%`(globaltype, globaltype)
  ;; test.spectec:1020.1-1021.14
  rule mk_Globaltype_sub{gt : globaltype}:
    `|-%<:%`(gt, gt)

;; test.spectec:1007.1-1007.74
relation Tabletype_sub: `|-%<:%`(tabletype, tabletype)
  ;; test.spectec:1023.1-1025.35
  rule mk_Tabletype_sub{lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(lim_1, lim_2)
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
    -- wf_limits: `%`(lim_1)
    -- wf_limits: `%`(lim_2)

;; test.spectec:1008.1-1008.72
relation Memtype_sub: `|-%<:%`(memtype, memtype)
  ;; test.spectec:1027.1-1029.35
  rule mk_Memtype_sub{lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(lim_1, lim_2)
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
    -- wf_limits: `%`(lim_1)
    -- wf_limits: `%`(lim_2)

;; test.spectec:1009.1-1009.75
relation Externtype_sub: `|-%<:%`(externtype, externtype)
  ;; test.spectec:1032.1-1034.35
  rule func{ft_1 : functype, ft_2 : functype}:
    `|-%<:%`(FUNC_externtype(ft_1), FUNC_externtype(ft_2))
    -- Functype_sub: `|-%<:%`(ft_1, ft_2)
    -- wf_externtype: `%`(FUNC_externtype(ft_1))
    -- wf_externtype: `%`(FUNC_externtype(ft_2))

  ;; test.spectec:1036.1-1038.37
  rule global{gt_1 : globaltype, gt_2 : globaltype}:
    `|-%<:%`(GLOBAL_externtype(gt_1), GLOBAL_externtype(gt_2))
    -- Globaltype_sub: `|-%<:%`(gt_1, gt_2)
    -- wf_externtype: `%`(GLOBAL_externtype(gt_1))
    -- wf_externtype: `%`(GLOBAL_externtype(gt_2))

  ;; test.spectec:1040.1-1042.36
  rule table{tt_1 : tabletype, tt_2 : tabletype}:
    `|-%<:%`(TABLE_externtype(tt_1), TABLE_externtype(tt_2))
    -- Tabletype_sub: `|-%<:%`(tt_1, tt_2)
    -- wf_externtype: `%`(TABLE_externtype(tt_1))
    -- wf_externtype: `%`(TABLE_externtype(tt_2))

  ;; test.spectec:1044.1-1046.34
  rule mem{mt_1 : memtype, mt_2 : memtype}:
    `|-%<:%`(MEM_externtype(mt_1), MEM_externtype(mt_2))
    -- Memtype_sub: `|-%<:%`(mt_1, mt_2)
    -- wf_externtype: `%`(MEM_externtype(mt_1))
    -- wf_externtype: `%`(MEM_externtype(mt_2))

;; test.spectec:1054.1-1055.65
rec {

;; test.spectec:1054.1-1054.64
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; test.spectec:1083.1-1084.24
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, mk_functype_functype([], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(NOP_instr)

  ;; test.spectec:1086.1-1087.34
  rule unreachable{C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNREACHABLE_instr)

  ;; test.spectec:1089.1-1090.23
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, mk_functype_functype([t], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(DROP_instr)

  ;; test.spectec:1092.1-1093.29
  rule select{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr, mk_functype_functype([t t I32_valtype], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(SELECT_instr)

  ;; test.spectec:1098.1-1100.57
  rule block{C : context, t_opt : valtype?, instr_lst : instr*}:
    `%|-%:%`(C, BLOCK_instr(t_opt, instr_lst), mk_functype_functype([], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()} +++ C, instr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BLOCK_instr(t_opt, instr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()})

  ;; test.spectec:1102.1-1104.59
  rule loop{C : context, t_opt : valtype?, instr_lst : instr*}:
    `%|-%:%`(C, LOOP_instr(t_opt, instr_lst), mk_functype_functype([], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [?()], RETURN ?()} +++ C, instr_lst, mk_functype_functype([], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOOP_instr(t_opt, instr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [?()], RETURN ?()})

  ;; test.spectec:1106.1-1109.59
  rule if{C : context, t_opt : valtype?, instr_1_lst : instr*, instr_2_lst : instr*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(t_opt, instr_1_lst, instr_2_lst), mk_functype_functype([I32_valtype], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()} +++ C, instr_1_lst, mk_functype_functype([], lift(t_opt)))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()} +++ C, instr_2_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`IF%%ELSE%`_instr(t_opt, instr_1_lst, instr_2_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t_opt], RETURN ?()})

  ;; test.spectec:1114.1-1116.25
  rule br{C : context, l : labelidx, t_1_lst : valtype*, t_opt : valtype?, t_2_lst : valtype*}:
    `%|-%:%`(C, BR_instr(l), mk_functype_functype(t_1_lst ++ lift(t_opt), t_2_lst))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = t_opt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_instr(l))

  ;; test.spectec:1118.1-1120.25
  rule br_if{C : context, l : labelidx, t_opt : valtype?}:
    `%|-%:%`(C, BR_IF_instr(l), mk_functype_functype(lift(t_opt) ++ [I32_valtype], lift(t_opt)))
    -- if ($proj_uN_0(l).0 < |C.LABELS_context|)
    -- if (C.LABELS_context[$proj_uN_0(l).0] = t_opt)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_IF_instr(l))

  ;; test.spectec:1122.1-1125.28
  rule br_table{C : context, l_lst : labelidx*, l' : labelidx, t_1_lst : valtype*, t_opt : valtype?, t_2_lst : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l_lst, l'), mk_functype_functype(t_1_lst ++ lift(t_opt) ++ [I32_valtype], t_2_lst))
    -- if ($proj_uN_0(l').0 < |C.LABELS_context|)
    -- if (t_opt = C.LABELS_context[$proj_uN_0(l').0])
    -- (if ($proj_uN_0(l).0 < |C.LABELS_context|))*{l <- l_lst}
    -- (if (t_opt = C.LABELS_context[$proj_uN_0(l).0]))*{l <- l_lst}
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_TABLE_instr(l_lst, l'))

  ;; test.spectec:1130.1-1132.34
  rule call{C : context, x : idx, t_1_lst : valtype*, t_2_opt : valtype?}:
    `%|-%:%`(C, CALL_instr(x), mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_instr(x))

  ;; test.spectec:1134.1-1136.34
  rule call_indirect{C : context, x : idx, t_1_lst : valtype*, t_2_opt : valtype?}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x), mk_functype_functype(t_1_lst ++ [I32_valtype], lift(t_2_opt)))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- if (C.TYPES_context[$proj_uN_0(x).0] = mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_INDIRECT_instr(x))

  ;; test.spectec:1138.1-1140.24
  rule return{C : context, t_1_lst : valtype*, t_opt : valtype?, t_2_lst : valtype*}:
    `%|-%:%`(C, RETURN_instr, mk_functype_functype(t_1_lst ++ lift(t_opt), t_2_lst))
    -- if (C.RETURN_context = ?(t_opt))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RETURN_instr)

  ;; test.spectec:1145.1-1146.30
  rule const{C : context, t : valtype, c_t : val_}:
    `%|-%:%`(C, CONST_instr(t, c_t), mk_functype_functype([], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(t, c_t))

  ;; test.spectec:1148.1-1149.30
  rule unop{C : context, t : valtype, unop_t : unop_}:
    `%|-%:%`(C, UNOP_instr(t, unop_t), mk_functype_functype([t], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNOP_instr(t, unop_t))

  ;; test.spectec:1151.1-1152.34
  rule binop{C : context, t : valtype, binop_t : binop_}:
    `%|-%:%`(C, BINOP_instr(t, binop_t), mk_functype_functype([t t], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr(t, binop_t))

  ;; test.spectec:1154.1-1155.36
  rule testop{C : context, t : valtype, testop_t : testop_}:
    `%|-%:%`(C, TESTOP_instr(t, testop_t), mk_functype_functype([t], [I32_valtype]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TESTOP_instr(t, testop_t))

  ;; test.spectec:1157.1-1158.36
  rule relop{C : context, t : valtype, relop_t : relop_}:
    `%|-%:%`(C, RELOP_instr(t, relop_t), mk_functype_functype([t t], [I32_valtype]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RELOP_instr(t, relop_t))

  ;; test.spectec:1162.1-1164.34
  rule cvtop_reinterpret{C : context, nt_1 : valtype, nt_2 : valtype}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, REINTERPRET_cvtop), mk_functype_functype([nt_2], [nt_1]))
    -- if ($size(nt_1) = $size(nt_2))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, REINTERPRET_cvtop))

  ;; test.spectec:1166.1-1167.44
  rule cvtop_convert{C : context, nt_1 : valtype, nt_2 : valtype, v_cvtop : cvtop}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, v_cvtop), mk_functype_functype([nt_2], [nt_1]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, v_cvtop))

  ;; test.spectec:1172.1-1174.24
  rule local_get{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_GET_instr(x), mk_functype_functype([], [t]))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_GET_instr(x))

  ;; test.spectec:1176.1-1178.24
  rule local_set{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_SET_instr(x), mk_functype_functype([t], []))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_SET_instr(x))

  ;; test.spectec:1180.1-1182.24
  rule local_tee{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, LOCAL_TEE_instr(x), mk_functype_functype([t], [t]))
    -- if ($proj_uN_0(x).0 < |C.LOCALS_context|)
    -- if (C.LOCALS_context[$proj_uN_0(x).0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOCAL_TEE_instr(x))

  ;; test.spectec:1187.1-1189.29
  rule global_get{C : context, x : idx, t : valtype, v_mut : mut}:
    `%|-%:%`(C, GLOBAL_GET_instr(x), mk_functype_functype([], [t]))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(v_mut, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_GET_instr(x))

  ;; test.spectec:1191.1-1193.29
  rule global_set{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, GLOBAL_SET_instr(x), mk_functype_functype([t], []))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(?(MUT_r_MUT), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_SET_instr(x))

  ;; test.spectec:1198.1-1200.23
  rule memory_size{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_SIZE_instr, mk_functype_functype([], [I32_valtype]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(MEMORY_SIZE_instr)

  ;; test.spectec:1202.1-1204.23
  rule memory_grow{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_GROW_instr, mk_functype_functype([I32_valtype], [I32_valtype]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(MEMORY_GROW_instr)

  ;; test.spectec:1215.1-1218.42
  rule load_val{C : context, t : valtype, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr(t, ?(), v_memarg), mk_functype_functype([I32_valtype], [t]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= (($size(t) : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(LOAD_instr(t, ?(), v_memarg))

  ;; test.spectec:1220.1-1223.35
  rule load_pack{C : context, v_Inn : Inn, v_M : M, v_sx : sx, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_M), v_sx))), v_memarg), mk_functype_functype([I32_valtype], [$valtype_Inn(v_Inn)]))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= ((v_M : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(LOAD_instr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_M), v_sx))), v_memarg))

  ;; test.spectec:1234.1-1237.42
  rule store_val{C : context, t : valtype, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr(t, ?(), v_memarg), mk_functype_functype([I32_valtype t], []))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= (($size(t) : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(STORE_instr(t, ?(), v_memarg))

  ;; test.spectec:1239.1-1242.35
  rule store_pack{C : context, v_Inn : Inn, v_M : M, v_memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_M)), v_memarg), mk_functype_functype([I32_valtype $valtype_Inn(v_Inn)], []))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ $proj_uN_0(v_memarg.ALIGN_memarg).0) : nat <:> rat) <= ((v_M : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(STORE_instr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_M)), v_memarg))

;; test.spectec:1055.1-1055.65
relation Instrs_ok: `%|-%:%`(context, instr*, functype)
  ;; test.spectec:1068.1-1069.24
  rule empty{C : context}:
    `%|-%:%`(C, [], mk_functype_functype([], []))
    -- wf_context: `%`(C)

  ;; test.spectec:1071.1-1074.45
  rule seq{C : context, instr_1 : instr, instr_2_lst : instr*, t_1_lst : valtype*, t_3_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, [instr_1] ++ instr_2_lst, mk_functype_functype(t_1_lst, t_3_lst))
    -- Instr_ok: `%|-%:%`(C, instr_1, mk_functype_functype(t_1_lst, t_2_lst))
    -- Instrs_ok: `%|-%:%`(C, instr_2_lst, mk_functype_functype(t_2_lst, t_3_lst))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(instr_1)
    -- (wf_instr: `%`(instr_2))*{instr_2 <- instr_2_lst}

  ;; test.spectec:1076.1-1078.43
  rule frame{C : context, instr_lst : instr*, t_lst : valtype*, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%|-%:%`(C, instr_lst, mk_functype_functype(t_lst ++ t_1_lst, t_lst ++ t_2_lst))
    -- Instrs_ok: `%|-%:%`(C, instr_lst, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
}

;; test.spectec:1056.1-1056.69
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; test.spectec:1061.1-1063.40
  rule mk_Expr_ok{C : context, instr_lst : instr*, t_opt : valtype?}:
    `%|-%:%`(C, instr_lst, t_opt)
    -- Instrs_ok: `%|-%:%`(C, instr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

;; test.spectec:1249.1-1249.79
relation Instr_const: `%|-%CONST`(context, instr)
  ;; test.spectec:1253.1-1254.25
  rule const{C : context, t : valtype, c : val_}:
    `%|-%CONST`(C, CONST_instr(t, c))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(t, c))

  ;; test.spectec:1256.1-1258.25
  rule global_get{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, GLOBAL_GET_instr(x))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = mk_globaltype_globaltype(?(), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(GLOBAL_GET_instr(x))

;; test.spectec:1250.1-1250.78
relation Expr_const: `%|-%CONST`(context, expr)
  ;; test.spectec:1261.1-1262.38
  rule mk_Expr_const{C : context, instr_lst : instr*}:
    `%|-%CONST`(C, instr_lst)
    -- (Instr_const: `%|-%CONST`(C, v_instr))*{v_instr <- instr_lst}
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}

;; test.spectec:1251.1-1251.79
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype?)
  ;; test.spectec:1265.1-1268.33
  rule mk_Expr_ok_const{C : context, v_expr : expr, t_opt : valtype?}:
    `%|-%:%CONST`(C, v_expr, t_opt)
    -- Expr_ok: `%|-%:%`(C, v_expr, t_opt)
    -- Expr_const: `%|-%CONST`(C, v_expr)
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(v_expr))*{v_expr <- v_expr}

;; test.spectec:1275.1-1275.73
relation Type_ok: `|-%:%`(type, functype)
  ;; test.spectec:1287.1-1289.29
  rule mk_Type_ok{ft : functype}:
    `|-%:%`(TYPE_type(ft), ft)
    -- Functype_ok: `|-%:OK`(ft)

;; test.spectec:1276.1-1276.73
relation Func_ok: `%|-%:%`(context, func, functype)
  ;; test.spectec:1291.1-1294.81
  rule mk_Func_ok{C : context, x : idx, t_lst : valtype*, v_expr : expr, t_1_lst : valtype*, t_2_opt : valtype?}:
    `%|-%:%`(C, FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, v_expr), mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- if ($proj_uN_0(x).0 < |C.TYPES_context|)
    -- if (C.TYPES_context[$proj_uN_0(x).0] = mk_functype_functype(t_1_lst, lift(t_2_opt)))
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_1_lst ++ t_lst, LABELS [t_2_opt], RETURN ?(t_2_opt)}, v_expr, t_2_opt)
    -- wf_context: `%`(C)
    -- wf_func: `%`(FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, v_expr))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_1_lst ++ t_lst, LABELS [t_2_opt], RETURN ?(t_2_opt)})

;; test.spectec:1277.1-1277.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; test.spectec:1296.1-1300.40
  rule mk_Global_ok{C : context, gt : globaltype, v_expr : expr, v_mut : mut, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(gt, v_expr), gt)
    -- Globaltype_ok: `|-%:OK`(gt)
    -- if (gt = mk_globaltype_globaltype(v_mut, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, ?(t))
    -- wf_context: `%`(C)
    -- wf_global: `%`(GLOBAL_global(gt, v_expr))

;; test.spectec:1278.1-1278.74
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; test.spectec:1302.1-1304.30
  rule mk_Table_ok{C : context, tt : tabletype}:
    `%|-%:%`(C, TABLE_table(tt), tt)
    -- Tabletype_ok: `|-%:OK`(tt)
    -- wf_context: `%`(C)
    -- wf_table: `%`(TABLE_table(tt))

;; test.spectec:1279.1-1279.72
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; test.spectec:1306.1-1308.28
  rule mk_Mem_ok{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_mem(mt), mt)
    -- Memtype_ok: `|-%:OK`(mt)
    -- wf_context: `%`(C)
    -- wf_mem: `%`(MEMORY_mem(mt))

;; test.spectec:1280.1-1280.73
relation Elem_ok: `%|-%:OK`(context, elem)
  ;; test.spectec:1311.1-1315.27
  rule mk_Elem_ok{C : context, v_expr : expr, x_lst : idx*, lim : limits, ft_lst : functype*}:
    `%|-%:OK`(C, ELEM_elem(v_expr, x_lst))
    -- if (0 < |C.TABLES_context|)
    -- if (C.TABLES_context[0] = lim)
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, ?(I32_valtype))
    -- if (|ft_lst| = |x_lst|)
    -- (if ($proj_uN_0(x).0 < |C.FUNCS_context|))*{x <- x_lst}
    -- (if (C.FUNCS_context[$proj_uN_0(x).0] = ft))*{ft <- ft_lst, x <- x_lst}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(lim)
    -- wf_elem: `%`(ELEM_elem(v_expr, x_lst))

;; test.spectec:1281.1-1281.73
relation Data_ok: `%|-%:OK`(context, data)
  ;; test.spectec:1318.1-1321.42
  rule mk_Data_ok{C : context, v_expr : expr, b_lst : byte*, lim : limits}:
    `%|-%:OK`(C, DATA_data(v_expr, b_lst))
    -- if (0 < |C.MEMS_context|)
    -- if (C.MEMS_context[0] = lim)
    -- Expr_ok_const: `%|-%:%CONST`(C, v_expr, ?(I32_valtype))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(lim)
    -- wf_data: `%`(DATA_data(v_expr, b_lst))

;; test.spectec:1282.1-1282.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; test.spectec:1323.1-1325.32
  rule mk_Start_ok{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = mk_functype_functype([], []))
    -- wf_context: `%`(C)
    -- wf_start: `%`(START_start(x))

;; test.spectec:1330.1-1330.80
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; test.spectec:1334.1-1336.31
  rule mk_Import_ok{C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), xt)
    -- Externtype_ok: `|-%:OK`(xt)
    -- wf_context: `%`(C)
    -- wf_import: `%`(IMPORT_import(name_1, name_2, xt))

;; test.spectec:1332.1-1332.83
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; test.spectec:1343.1-1345.24
  rule func{C : context, x : idx, ft : functype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype(ft))
    -- if ($proj_uN_0(x).0 < |C.FUNCS_context|)
    -- if (C.FUNCS_context[$proj_uN_0(x).0] = ft)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(FUNC_externidx(x))
    -- wf_externtype: `%`(FUNC_externtype(ft))

  ;; test.spectec:1347.1-1349.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if ($proj_uN_0(x).0 < |C.GLOBALS_context|)
    -- if (C.GLOBALS_context[$proj_uN_0(x).0] = gt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(GLOBAL_externidx(x))
    -- wf_externtype: `%`(GLOBAL_externtype(gt))

  ;; test.spectec:1351.1-1353.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if ($proj_uN_0(x).0 < |C.TABLES_context|)
    -- if (C.TABLES_context[$proj_uN_0(x).0] = tt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TABLE_externidx(x))
    -- wf_externtype: `%`(TABLE_externtype(tt))

  ;; test.spectec:1355.1-1357.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if ($proj_uN_0(x).0 < |C.MEMS_context|)
    -- if (C.MEMS_context[$proj_uN_0(x).0] = mt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(MEM_externidx(x))
    -- wf_externtype: `%`(MEM_externtype(mt))

;; test.spectec:1331.1-1331.80
relation Export_ok: `%|-%:%`(context, export, externtype)
  ;; test.spectec:1338.1-1340.39
  rule mk_Export_ok{C : context, v_name : name, v_externidx : externidx, xt : externtype}:
    `%|-%:%`(C, EXPORT_export(v_name, v_externidx), xt)
    -- Externidx_ok: `%|-%:%`(C, v_externidx, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(xt)
    -- wf_export: `%`(EXPORT_export(v_name, v_externidx))

;; test.spectec:1362.1-1362.62
relation Module_ok: `|-%:OK`(module)
  ;; test.spectec:1364.1-1390.29
  rule mk_Module_ok{type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, ft'_lst : functype*, ixt_lst : externtype*, C' : context, gt_lst : globaltype*, C : context, ft_lst : functype*, tt_lst : tabletype*, mt_lst : memtype*, xt_lst : externtype*, ift_lst : functype*, igt_lst : globaltype*, itt_lst : tabletype*, imt_lst : memtype*, var_3 : memtype*, var_2 : tabletype*, var_1 : globaltype*, var_0 : functype*}:
    `|-%:OK`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- fun_memsxt: `%%`(ixt_lst, var_3)
    -- fun_tablesxt: `%%`(ixt_lst, var_2)
    -- fun_globalsxt: `%%`(ixt_lst, var_1)
    -- fun_funcsxt: `%%`(ixt_lst, var_0)
    -- if (|ft'_lst| = |type_lst|)
    -- (Type_ok: `|-%:%`(v_type, ft'))*{ft' <- ft'_lst, v_type <- type_lst}
    -- if (|import_lst| = |ixt_lst|)
    -- (Import_ok: `%|-%:%`({TYPES ft'_lst, FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()}, v_import, ixt))*{v_import <- import_lst, ixt <- ixt_lst}
    -- if (|global_lst| = |gt_lst|)
    -- (Global_ok: `%|-%:%`(C', v_global, gt))*{v_global <- global_lst, gt <- gt_lst}
    -- if (|ft_lst| = |func_lst|)
    -- (Func_ok: `%|-%:%`(C, v_func, ft))*{ft <- ft_lst, v_func <- func_lst}
    -- if (|table_lst| = |tt_lst|)
    -- (Table_ok: `%|-%:%`(C, v_table, tt))*{v_table <- table_lst, tt <- tt_lst}
    -- if (|mem_lst| = |mt_lst|)
    -- (Mem_ok: `%|-%:%`(C, v_mem, mt))*{v_mem <- mem_lst, mt <- mt_lst}
    -- (Elem_ok: `%|-%:OK`(C, v_elem))*{v_elem <- elem_lst}
    -- (Data_ok: `%|-%:OK`(C, v_data))*{v_data <- data_lst}
    -- (Start_ok: `%|-%:OK`(C, v_start))?{v_start <- start_opt}
    -- if (|export_lst| = |xt_lst|)
    -- (Export_ok: `%|-%:%`(C, v_export, xt))*{v_export <- export_lst, xt <- xt_lst}
    -- if (|tt_lst| <= 1)
    -- if (|mt_lst| <= 1)
    -- if (C = {TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst ++ gt_lst, TABLES itt_lst ++ tt_lst, MEMS imt_lst ++ mt_lst, LOCALS [], LABELS [], RETURN ?()})
    -- if (C' = {TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst, TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})
    -- if (ift_lst = var_0)
    -- if (igt_lst = var_1)
    -- if (itt_lst = var_2)
    -- if (imt_lst = var_3)
    -- (wf_externtype: `%`(ixt))*{ixt <- ixt_lst}
    -- wf_context: `%`(C')
    -- wf_context: `%`(C)
    -- (wf_externtype: `%`(xt))*{xt <- xt_lst}
    -- (wf_limits: `%`(iter))*{iter <- var_2}
    -- (wf_limits: `%`(iter))*{iter <- var_3}
    -- wf_module: `%`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- wf_context: `%`({TYPES ft'_lst, FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})
    -- wf_context: `%`({TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst ++ gt_lst, TABLES itt_lst ++ tt_lst, MEMS imt_lst ++ mt_lst, LOCALS [], LABELS [], RETURN ?()})
    -- wf_context: `%`({TYPES ft'_lst, FUNCS ift_lst ++ ft_lst, GLOBALS igt_lst, TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})

;; test.spectec:1402.1-1402.77
relation Step_pure: `%~>%`(admininstr*, admininstr*)
  ;; test.spectec:1438.1-1439.24
  rule unreachable:
    `%~>%`([UNREACHABLE_admininstr], [TRAP_admininstr])
    -- wf_admininstr: `%`(UNREACHABLE_admininstr)
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1441.1-1442.15
  rule nop:
    `%~>%`([NOP_admininstr], [])
    -- wf_admininstr: `%`(NOP_admininstr)

  ;; test.spectec:1444.1-1445.20
  rule drop{v_val : val}:
    `%~>%`([$admininstr_val(v_val) DROP_admininstr], [])
    -- wf_val: `%`(v_val)
    -- wf_admininstr: `%`(DROP_admininstr)

  ;; test.spectec:1448.1-1450.16
  rule select_true{val_1 : val, val_2 : val, c : val_}:
    `%~>%`([$admininstr_val(val_1) $admininstr_val(val_2) CONST_admininstr(I32_valtype, c) SELECT_admininstr], [$admininstr_val(val_1)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 =/= 0)
    -- wf_val: `%`(val_1)
    -- wf_val: `%`(val_2)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(SELECT_admininstr)

  ;; test.spectec:1452.1-1454.14
  rule select_false{val_1 : val, val_2 : val, c : val_}:
    `%~>%`([$admininstr_val(val_1) $admininstr_val(val_2) CONST_admininstr(I32_valtype, c) SELECT_admininstr], [$admininstr_val(val_2)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 = 0)
    -- wf_val: `%`(val_1)
    -- wf_val: `%`(val_2)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(SELECT_admininstr)

  ;; test.spectec:1466.1-1468.16
  rule if_true{c : val_, t_opt : valtype?, instr_1_lst : instr*, instr_2_lst : instr*}:
    `%~>%`([CONST_admininstr(I32_valtype, c) `IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst)], [BLOCK_admininstr(t_opt, instr_1_lst)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 =/= 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(`IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst))
    -- wf_admininstr: `%`(BLOCK_admininstr(t_opt, instr_1_lst))

  ;; test.spectec:1470.1-1472.14
  rule if_false{c : val_, t_opt : valtype?, instr_1_lst : instr*, instr_2_lst : instr*}:
    `%~>%`([CONST_admininstr(I32_valtype, c) `IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst)], [BLOCK_admininstr(t_opt, instr_2_lst)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 = 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(`IF%%ELSE%`_admininstr(t_opt, instr_1_lst, instr_2_lst))
    -- wf_admininstr: `%`(BLOCK_admininstr(t_opt, instr_2_lst))

  ;; test.spectec:1475.1-1476.38
  rule label_vals{v_n : n, instr_lst : instr*, val_lst : val*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr_lst, $admininstr_val(v_val)*{v_val <- val_lst})], $admininstr_val(v_val)*{v_val <- val_lst})
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr_lst, $admininstr_val(v_val)*{v_val <- val_lst}))

  ;; test.spectec:1482.1-1483.69
  rule br_zero{v_n : n, instr'_lst : instr*, val'_lst : val*, val_lst : val*, instr_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(0))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ $admininstr_instr(instr')*{instr' <- instr'_lst})
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(0))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- if (v_n = |val_lst|)

  ;; test.spectec:1485.1-1486.65
  rule br_succ{v_n : n, instr'_lst : instr*, val_lst : val*, l : labelidx, instr_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(($proj_uN_0(l).0 + 1)))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)*{v_val <- val_lst} ++ [BR_admininstr(l)])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [BR_admininstr(mk_uN_labelidx(($proj_uN_0(l).0 + 1)))] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- wf_admininstr: `%`(BR_admininstr(l))

  ;; test.spectec:1489.1-1491.16
  rule br_if_true{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 =/= 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(BR_IF_admininstr(l))
    -- wf_admininstr: `%`(BR_admininstr(l))

  ;; test.spectec:1493.1-1495.14
  rule br_if_false{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [])
    -- if ($proj_val__0(c) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(c))).0 = 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(BR_IF_admininstr(l))

  ;; test.spectec:1498.1-1500.17
  rule br_table_lt{i : val_, l_lst : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, i) BR_TABLE_admininstr(l_lst, l')], [BR_admininstr(l_lst[$proj_uN_0(!($proj_val__0(i))).0])])
    -- if ($proj_uN_0(!($proj_val__0(i))).0 < |l_lst|)
    -- if ($proj_val__0(i) =/= ?())
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, i))
    -- wf_admininstr: `%`(BR_TABLE_admininstr(l_lst, l'))
    -- wf_admininstr: `%`(BR_admininstr(l_lst[$proj_uN_0(!($proj_val__0(i))).0]))

  ;; test.spectec:1502.1-1504.18
  rule br_table_ge{i : val_, l_lst : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, i) BR_TABLE_admininstr(l_lst, l')], [BR_admininstr(l')])
    -- if ($proj_val__0(i) =/= ?())
    -- if ($proj_uN_0(!($proj_val__0(i))).0 >= |l_lst|)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, i))
    -- wf_admininstr: `%`(BR_TABLE_admininstr(l_lst, l'))
    -- wf_admininstr: `%`(BR_admininstr(l'))

  ;; test.spectec:1528.1-1529.35
  rule frame_vals{v_n : n, f : frame, val_lst : val*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(v_val)^v_n{v_val <- val_lst})], $admininstr_val(v_val)^v_n{v_val <- val_lst})
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(v_val)^v_n{v_val <- val_lst}))
    -- if (v_n = |val_lst|)

  ;; test.spectec:1531.1-1532.55
  rule return_frame{v_n : n, f : frame, val'_lst : val*, val_lst : val*, instr_lst : instr*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)^v_n{v_val <- val_lst})
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, $admininstr_val(val')*{val' <- val'_lst} ++ $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- if (v_n = |val_lst|)

  ;; test.spectec:1534.1-1535.60
  rule return_label{v_n : n, instr'_lst : instr*, val_lst : val*, instr_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst})], $admininstr_val(v_val)*{v_val <- val_lst} ++ [RETURN_admininstr])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, $admininstr_val(v_val)*{v_val <- val_lst} ++ [RETURN_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- wf_admininstr: `%`(RETURN_admininstr)

  ;; test.spectec:1540.1-1542.39
  rule trap_vals{val_lst : val*, instr_lst : instr*}:
    `%~>%`($admininstr_val(v_val)*{v_val <- val_lst} ++ [TRAP_admininstr] ++ $admininstr_instr(v_instr)*{v_instr <- instr_lst}, [TRAP_admininstr])
    -- if ((val_lst =/= []) \/ (instr_lst =/= []))
    -- (wf_val: `%`(v_val))*{v_val <- val_lst}
    -- (wf_instr: `%`(v_instr))*{v_instr <- instr_lst}
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1544.1-1545.39
  rule trap_label{v_n : n, instr'_lst : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(v_n, instr'_lst, [TRAP_admininstr])], [TRAP_admininstr])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, [TRAP_admininstr]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1547.1-1548.33
  rule trap_frame{v_n : n, f : frame}:
    `%~>%`([`FRAME_%{%}%`_admininstr(v_n, f, [TRAP_admininstr])], [TRAP_admininstr])
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, [TRAP_admininstr]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1569.1-1571.34
  rule unop_val{t : valtype, c_1 : val_, unop : unop_, c : val_}:
    `%~>%`([CONST_admininstr(t, c_1) UNOP_admininstr(t, unop)], [CONST_admininstr(t, c)])
    -- if (|!($fun_unop_(t, unop, c_1))| > 0)
    -- if ($fun_unop_(t, unop, c_1) =/= ?())
    -- if (c <- !($fun_unop_(t, unop, c_1)))
    -- (wf_val_: `%%`(t, iter))*{iter <- !($fun_unop_(t, unop, c_1))}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(UNOP_admininstr(t, unop))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))

  ;; test.spectec:1573.1-1575.35
  rule unop_trap{t : valtype, c_1 : val_, unop : unop_}:
    `%~>%`([CONST_admininstr(t, c_1) UNOP_admininstr(t, unop)], [TRAP_admininstr])
    -- if ($fun_unop_(t, unop, c_1) =/= ?())
    -- if (!($fun_unop_(t, unop, c_1)) = [])
    -- (wf_val_: `%%`(t, iter))*{iter <- !($fun_unop_(t, unop, c_1))}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(UNOP_admininstr(t, unop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1578.1-1580.41
  rule binop_val{t : valtype, c_1 : val_, c_2 : val_, binop : binop_, c : val_, var_0 : val_*}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) BINOP_admininstr(t, binop)], [CONST_admininstr(t, c)])
    -- fun_binop_: `%%%%%`(t, binop, c_1, c_2, var_0)
    -- if (|var_0| > 0)
    -- if (c <- var_0)
    -- (wf_val_: `%%`(t, iter))*{iter <- var_0}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(BINOP_admininstr(t, binop))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))

  ;; test.spectec:1582.1-1584.42
  rule binop_trap{t : valtype, c_1 : val_, c_2 : val_, binop : binop_, var_0 : val_*}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) BINOP_admininstr(t, binop)], [TRAP_admininstr])
    -- fun_binop_: `%%%%%`(t, binop, c_1, c_2, var_0)
    -- if (var_0 = [])
    -- (wf_val_: `%%`(t, iter))*{iter <- var_0}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(BINOP_admininstr(t, binop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1587.1-1589.37
  rule testop{t : valtype, c_1 : val_, testop : testop_, c : val_}:
    `%~>%`([CONST_admininstr(t, c_1) TESTOP_admininstr(t, testop)], [CONST_admininstr(I32_valtype, c)])
    -- if ($fun_testop_(t, testop, c_1) =/= ?())
    -- if (c = !($fun_testop_(t, testop, c_1)))
    -- wf_val_: `%%`(I32_valtype, !($fun_testop_(t, testop, c_1)))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(TESTOP_admininstr(t, testop))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))

  ;; test.spectec:1591.1-1593.40
  rule relop{t : valtype, c_1 : val_, c_2 : val_, relop : relop_, c : val_, var_0 : val_}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) RELOP_admininstr(t, relop)], [CONST_admininstr(I32_valtype, c)])
    -- fun_relop_: `%%%%%`(t, relop, c_1, c_2, var_0)
    -- if (c = var_0)
    -- wf_val_: `%%`(I32_valtype, var_0)
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(RELOP_admininstr(t, relop))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))

  ;; test.spectec:1596.1-1598.44
  rule cvtop_val{t_1 : valtype, c_1 : val_, t_2 : valtype, v_cvtop : cvtop, c : val_, var_0 : val_*}:
    `%~>%`([CONST_admininstr(t_1, c_1) CVTOP_admininstr(t_2, t_1, v_cvtop)], [CONST_admininstr(t_2, c)])
    -- fun_cvtop__: `%%%%%`(t_1, t_2, v_cvtop, c_1, var_0)
    -- if (|var_0| > 0)
    -- if (c <- var_0)
    -- (wf_val_: `%%`(t_2, iter))*{iter <- var_0}
    -- wf_admininstr: `%`(CONST_admininstr(t_1, c_1))
    -- wf_admininstr: `%`(CVTOP_admininstr(t_2, t_1, v_cvtop))
    -- wf_admininstr: `%`(CONST_admininstr(t_2, c))

  ;; test.spectec:1600.1-1602.45
  rule cvtop_trap{t_1 : valtype, c_1 : val_, t_2 : valtype, v_cvtop : cvtop, var_0 : val_*}:
    `%~>%`([CONST_admininstr(t_1, c_1) CVTOP_admininstr(t_2, t_1, v_cvtop)], [TRAP_admininstr])
    -- fun_cvtop__: `%%%%%`(t_1, t_2, v_cvtop, c_1, var_0)
    -- if (var_0 = [])
    -- (wf_val_: `%%`(t_2, iter))*{iter <- var_0}
    -- wf_admininstr: `%`(CONST_admininstr(t_1, c_1))
    -- wf_admininstr: `%`(CVTOP_admininstr(t_2, t_1, v_cvtop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1613.1-1614.47
  rule local_tee{v_val : val, x : idx}:
    `%~>%`([$admininstr_val(v_val) LOCAL_TEE_admininstr(x)], [$admininstr_val(v_val) $admininstr_val(v_val) LOCAL_SET_admininstr(x)])
    -- wf_val: `%`(v_val)
    -- wf_admininstr: `%`(LOCAL_TEE_admininstr(x))
    -- wf_admininstr: `%`(LOCAL_SET_admininstr(x))

;; test.spectec:1517.1-1519.15
relation Step_read_before_call_indirect_trap: `%`(config)
  ;; test.spectec:1512.1-1515.43
  rule call_indirect_call_0{z : state, i : val_, x : idx, a : addr}:
    `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- if ($proj_uN_0(!($proj_val__0(i))).0 < |$fun_table(z, mk_uN_tableidx(0)).REFS_tableinst|)
    -- if ($proj_val__0(i) =/= ?())
    -- if ($fun_table(z, mk_uN_tableidx(0)).REFS_tableinst[$proj_uN_0(!($proj_val__0(i))).0] = ?(a))
    -- if (a < |$fun_funcinst(z)|)
    -- if ($fun_type(z, x) = $fun_funcinst(z)[a].TYPE_funcinst)
    -- wf_tableinst: `%`($fun_table(z, mk_uN_tableidx(0)))
    -- (wf_funcinst: `%`(iter))*{iter <- $fun_funcinst(z)}
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(a))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

;; test.spectec:1403.1-1403.77
relation Step_read: `%~>%`(config, admininstr*)
  ;; test.spectec:1459.1-1461.49
  rule block{z : state, t_opt : valtype?, instr_lst : instr*, v_n : n}:
    `%~>%`(mk_config_config(z, [BLOCK_admininstr(t_opt, instr_lst)]), [`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst})])
    -- if (((t_opt = ?()) /\ (v_n = 0)) \/ ((t_opt =/= ?()) /\ (v_n = 1)))
    -- wf_config: `%`(mk_config_config(z, [BLOCK_admininstr(t_opt, instr_lst)]))
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst}))

  ;; test.spectec:1463.1-1464.63
  rule loop{z : state, t_opt : valtype?, instr_lst : instr*}:
    `%~>%`(mk_config_config(z, [LOOP_admininstr(t_opt, instr_lst)]), [`LABEL_%{%}%`_admininstr(0, [LOOP_instr(t_opt, instr_lst)], $admininstr_instr(v_instr)*{v_instr <- instr_lst})])
    -- wf_config: `%`(mk_config_config(z, [LOOP_admininstr(t_opt, instr_lst)]))
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(0, [LOOP_instr(t_opt, instr_lst)], $admininstr_instr(v_instr)*{v_instr <- instr_lst}))

  ;; test.spectec:1509.1-1510.47
  rule call{z : state, x : idx}:
    `%~>%`(mk_config_config(z, [CALL_admininstr(x)]), [CALL_ADDR_admininstr($fun_funcaddr(z)[$proj_uN_0(x).0])])
    -- if ($proj_uN_0(x).0 < |$fun_funcaddr(z)|)
    -- wf_config: `%`(mk_config_config(z, [CALL_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr($fun_funcaddr(z)[$proj_uN_0(x).0]))

  ;; test.spectec:1512.1-1515.43
  rule call_indirect_call{z : state, i : val_, x : idx, a : addr}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]), [CALL_ADDR_admininstr(a)])
    -- if ($proj_uN_0(!($proj_val__0(i))).0 < |$fun_table(z, mk_uN_tableidx(0)).REFS_tableinst|)
    -- if ($proj_val__0(i) =/= ?())
    -- if ($fun_table(z, mk_uN_tableidx(0)).REFS_tableinst[$proj_uN_0(!($proj_val__0(i))).0] = ?(a))
    -- if (a < |$fun_funcinst(z)|)
    -- if ($fun_type(z, x) = $fun_funcinst(z)[a].TYPE_funcinst)
    -- wf_tableinst: `%`($fun_table(z, mk_uN_tableidx(0)))
    -- (wf_funcinst: `%`(iter))*{iter <- $fun_funcinst(z)}
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(a))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1517.1-1519.15
  rule call_indirect_trap{z : state, i : val_, x : idx}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]), [TRAP_admininstr])
    -- ~ Step_read_before_call_indirect_trap: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1521.1-1525.54
  rule call_addr{z : state, k : nat, val_lst : val*, a : addr, v_n : n, f : frame, instr_lst : instr*, t_1_lst : valtype*, t_2_lst : valtype*, mm : moduleinst, v_func : func, x : idx, t_lst : valtype*}:
    `%~>%`(mk_config_config(z, $admininstr_val(v_val)^k{v_val <- val_lst} ++ [CALL_ADDR_admininstr(a)]), [`FRAME_%{%}%`_admininstr(v_n, f, [`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst})])])
    -- if (a < |$fun_funcinst(z)|)
    -- if ($fun_funcinst(z)[a] = {TYPE mk_functype_functype(t_1_lst, t_2_lst), MODULE mm, CODE v_func})
    -- if (v_func = FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, instr_lst))
    -- if (f = {LOCALS val_lst ++ $default_(t)*{t <- t_lst}, MODULE mm})
    -- (wf_funcinst: `%`(iter))*{iter <- $fun_funcinst(z)}
    -- wf_config: `%`(mk_config_config(z, $admininstr_val(v_val)^k{v_val <- val_lst} ++ [CALL_ADDR_admininstr(a)]))
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, [`LABEL_%{%}%`_admininstr(v_n, [], $admininstr_instr(v_instr)*{v_instr <- instr_lst})]))
    -- wf_funcinst: `%`({TYPE mk_functype_functype(t_1_lst, t_2_lst), MODULE mm, CODE v_func})
    -- wf_func: `%`(FUNC_func(x, LOCAL_local(t)*{t <- t_lst}, instr_lst))
    -- wf_frame: `%`({LOCALS val_lst ++ $default_(t)*{t <- t_lst}, MODULE mm})
    -- if (k = |val_lst|)
    -- if (k = |t_1_lst|)
    -- if (v_n = |t_2_lst|)

  ;; test.spectec:1607.1-1608.37
  rule local_get{z : state, x : idx}:
    `%~>%`(mk_config_config(z, [LOCAL_GET_admininstr(x)]), [$admininstr_val($fun_local(z, x))])
    -- wf_val: `%`($fun_local(z, x))
    -- wf_config: `%`(mk_config_config(z, [LOCAL_GET_admininstr(x)]))

  ;; test.spectec:1619.1-1620.45
  rule global_get{z : state, x : idx}:
    `%~>%`(mk_config_config(z, [GLOBAL_GET_admininstr(x)]), [$admininstr_val($fun_global(z, x).VALUE_globalinst)])
    -- wf_globalinst: `%`($fun_global(z, x))
    -- wf_config: `%`(mk_config_config(z, [GLOBAL_GET_admininstr(x)]))

  ;; test.spectec:1628.1-1630.59
  rule load_num_trap{z : state, i : val_, t : valtype, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]), [TRAP_admininstr])
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]))
    -- wf_admininstr: `%`(TRAP_admininstr)
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1632.1-1634.69
  rule load_num_val{z : state, i : val_, t : valtype, ao : memarg, c : val_}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]), [CONST_admininstr(t, c)])
    -- if ($proj_val__0(i) =/= ?())
    -- if ($bytes_(t, c) = $fun_mem(z, mk_uN_memidx(0)).BYTES_meminst[($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) : ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- (wf_byte: `%`(iter))*{iter <- $bytes_(t, c)}
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1636.1-1638.52
  rule load_pack_trap{z : state, i : val_, v_Inn : Inn, v_n : n, v_sx : sx, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]), [TRAP_admininstr])
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]))
    -- wf_admininstr: `%`(TRAP_admininstr)
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1640.1-1642.63
  rule load_pack_val{z : state, i : val_, v_Inn : Inn, v_n : n, v_sx : sx, ao : memarg, c : iN}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]), [CONST_admininstr($valtype_Inn(v_Inn), mk_val__0_val_(v_Inn, $extend__(v_n, $size($valtype_Inn(v_Inn)), v_sx, c)))])
    -- if ($proj_val__0(i) =/= ?())
    -- if ($ibytes_(v_n, c) = $fun_mem(z, mk_uN_memidx(0)).BYTES_meminst[($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) : (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- (wf_byte: `%`(iter))*{iter <- $ibytes_(v_n, c)}
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr($valtype_Inn(v_Inn), ?(mk_loadop__0_loadop_(v_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(v_n), v_sx))), ao)]))
    -- wf_admininstr: `%`(CONST_admininstr($valtype_Inn(v_Inn), mk_val__0_val_(v_Inn, $extend__(v_n, $size($valtype_Inn(v_Inn)), v_sx, c))))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1662.1-1664.45
  rule memory_size{z : state, v_n : n}:
    `%~>%`(mk_config_config(z, [MEMORY_SIZE_admininstr]), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n)))])
    -- if (((v_n * 64) * $Ki) = |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [MEMORY_SIZE_admininstr]))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

;; test.spectec:1401.1-1401.77
rec {

;; test.spectec:1401.1-1401.77
relation Step: `%~>%`(config, config)
  ;; test.spectec:1406.1-1408.44
  rule pure{z : state, admininstr_lst : admininstr*, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z, admininstr'_lst))
    -- Step_pure: `%~>%`(admininstr_lst, admininstr'_lst)
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr'_lst))

  ;; test.spectec:1410.1-1412.47
  rule read{z : state, admininstr_lst : admininstr*, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z, admininstr'_lst))
    -- Step_read: `%~>%`(mk_config_config(z, admininstr_lst), admininstr'_lst)
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr'_lst))

  ;; test.spectec:1553.1-1555.46
  rule ctxt_label{z : state, v_n : n, instr_0_lst : instr*, admininstr_lst : admininstr*, z' : state, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr_lst)]), mk_config_config(z', [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr'_lst)]))
    -- Step: `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z', admininstr'_lst))
    -- wf_config: `%`(mk_config_config(z, [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr_lst)]))
    -- wf_config: `%`(mk_config_config(z', [`LABEL_%{%}%`_admininstr(v_n, instr_0_lst, admininstr'_lst)]))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z', admininstr'_lst))

  ;; test.spectec:1557.1-1559.55
  rule ctxt_frame{s : store, f : frame, v_n : n, f' : frame, admininstr_lst : admininstr*, s' : store, f'' : frame, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(mk_state_state(s, f), [`FRAME_%{%}%`_admininstr(v_n, f', admininstr_lst)]), mk_config_config(mk_state_state(s', f), [`FRAME_%{%}%`_admininstr(v_n, f'', admininstr'_lst)]))
    -- Step: `%~>%`(mk_config_config(mk_state_state(s, f'), admininstr_lst), mk_config_config(mk_state_state(s', f''), admininstr'_lst))
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f), [`FRAME_%{%}%`_admininstr(v_n, f', admininstr_lst)]))
    -- wf_config: `%`(mk_config_config(mk_state_state(s', f), [`FRAME_%{%}%`_admininstr(v_n, f'', admininstr'_lst)]))
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f'), admininstr_lst))
    -- wf_config: `%`(mk_config_config(mk_state_state(s', f''), admininstr'_lst))

  ;; test.spectec:1561.1-1564.46
  rule ctxt_instrs{z : state, val_lst : val*, admininstr_lst : admininstr*, admininstr_1_lst : admininstr*, z' : state, admininstr'_lst : admininstr*}:
    `%~>%`(mk_config_config(z, $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr_lst ++ admininstr_1_lst), mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr'_lst ++ admininstr_1_lst))
    -- Step: `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z', admininstr'_lst))
    -- if ((val_lst =/= []) \/ (admininstr_1_lst =/= []))
    -- wf_config: `%`(mk_config_config(z, $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr_lst ++ admininstr_1_lst))
    -- wf_config: `%`(mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst} ++ admininstr'_lst ++ admininstr_1_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z', admininstr'_lst))

  ;; test.spectec:1610.1-1611.56
  rule local_set{z : state, v_val : val, x : idx}:
    `%~>%`(mk_config_config(z, [$admininstr_val(v_val) LOCAL_SET_admininstr(x)]), mk_config_config($with_local(z, x, v_val), []))
    -- wf_config: `%`(mk_config_config(z, [$admininstr_val(v_val) LOCAL_SET_admininstr(x)]))
    -- wf_config: `%`(mk_config_config($with_local(z, x, v_val), []))

  ;; test.spectec:1622.1-1623.58
  rule global_set{z : state, v_val : val, x : idx}:
    `%~>%`(mk_config_config(z, [$admininstr_val(v_val) GLOBAL_SET_admininstr(x)]), mk_config_config($with_global(z, x, v_val), []))
    -- wf_config: `%`(mk_config_config(z, [$admininstr_val(v_val) GLOBAL_SET_admininstr(x)]))
    -- wf_config: `%`(mk_config_config($with_global(z, x, v_val), []))

  ;; test.spectec:1645.1-1647.59
  rule store_num_trap{z : state, i : val_, t : valtype, c : val_, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]), mk_config_config(z, [TRAP_admininstr]))
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]))
    -- wf_config: `%`(mk_config_config(z, [TRAP_admininstr]))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1649.1-1651.27
  rule store_num_val{z : state, i : val_, t : valtype, c : val_, ao : memarg, b_lst : byte*}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]), mk_config_config($with_mem(z, mk_uN_memidx(0), ($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0), ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b_lst), []))
    -- if ($proj_val__0(i) =/= ?())
    -- if (b_lst = $bytes_(t, c))
    -- (wf_byte: `%`(iter))*{iter <- $bytes_(t, c)}
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]))
    -- wf_config: `%`(mk_config_config($with_mem(z, mk_uN_memidx(0), ($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0), ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b_lst), []))

  ;; test.spectec:1653.1-1655.52
  rule store_pack_trap{z : state, i : val_, v_Inn : Inn, c : val_, v_n : n, ao : memarg}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]), mk_config_config(z, [TRAP_admininstr]))
    -- if ($proj_val__0(i) =/= ?())
    -- if ((($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0) + (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]))
    -- wf_config: `%`(mk_config_config(z, [TRAP_admininstr]))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1657.1-1659.52
  rule store_pack_val{z : state, i : val_, v_Inn : Inn, c : val_, v_n : n, ao : memarg, b_lst : byte*}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]), mk_config_config($with_mem(z, mk_uN_memidx(0), ($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0), (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b_lst), []))
    -- if ($proj_val__0(i) =/= ?())
    -- if ($proj_val__0(c) =/= ?())
    -- if (b_lst = $ibytes_(v_n, $wrap__($size($valtype_Inn(v_Inn)), v_n, !($proj_val__0(c)))))
    -- (wf_byte: `%`(iter))*{iter <- $ibytes_(v_n, $wrap__($size($valtype_Inn(v_Inn)), v_n, !($proj_val__0(c))))}
    -- wf_uN: `%%`(v_n, $wrap__($size($valtype_Inn(v_Inn)), v_n, !($proj_val__0(c))))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr($valtype_Inn(v_Inn), c) STORE_admininstr($valtype_Inn(v_Inn), ?(mk_sz_sz(v_n)), ao)]))
    -- wf_config: `%`(mk_config_config($with_mem(z, mk_uN_memidx(0), ($proj_uN_0(!($proj_val__0(i))).0 + $proj_uN_0(ao.OFFSET_memarg).0), (((v_n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b_lst), []))

  ;; test.spectec:1667.1-1669.40
  rule memory_grow_succeed{z : state, v_n : n, mi : meminst, var_0 : meminst?}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]), mk_config_config($with_meminst(z, mk_uN_memidx(0), mi), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN((((|$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat))))]))
    -- fun_growmemory: `%%%`($fun_mem(z, mk_uN_memidx(0)), v_n, var_0)
    -- if (var_0 =/= ?())
    -- if (!(var_0) = mi)
    -- wf_meminst: `%`(!(var_0))
    -- wf_meminst: `%`($fun_mem(z, mk_uN_memidx(0)))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]))
    -- wf_config: `%`(mk_config_config($with_meminst(z, mk_uN_memidx(0), mi), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN((((|$fun_mem(z, mk_uN_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat))))]))
    -- wf_uN: `%%`(32, mk_uN_uN(0))

  ;; test.spectec:1671.1-1672.77
  rule memory_grow_fail{z : state, v_n : n, var_0 : nat}:
    `%~>%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]), mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(var_0)))]))
    -- fun_inv_signed_: `%%%`(32, - (1 : nat <:> int), var_0)
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(v_n))) MEMORY_GROW_admininstr]))
    -- wf_config: `%`(mk_config_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, mk_uN_uN(var_0)))]))
}

;; test.spectec:1404.1-1404.77
rec {

;; test.spectec:1404.1-1404.77
relation Steps: `%~>*%`(config, config)
  ;; test.spectec:1414.1-1415.36
  rule refl{z : state, admininstr_lst : admininstr*}:
    `%~>*%`(mk_config_config(z, admininstr_lst), mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))

  ;; test.spectec:1417.1-1420.54
  rule trans{z : state, admininstr_lst : admininstr*, z'' : state, admininstr''_lst : admininstr*, z' : state, admininstr'_lst : admininstr*}:
    `%~>*%`(mk_config_config(z, admininstr_lst), mk_config_config(z'', admininstr''_lst))
    -- Step: `%~>%`(mk_config_config(z, admininstr_lst), mk_config_config(z', admininstr'_lst))
    -- Steps: `%~>*%`(mk_config_config(z', admininstr'_lst), mk_config_config(z'', admininstr''_lst))
    -- wf_config: `%`(mk_config_config(z, admininstr_lst))
    -- wf_config: `%`(mk_config_config(z'', admininstr''_lst))
    -- wf_config: `%`(mk_config_config(z', admininstr'_lst))
}

;; test.spectec:1425.1-1425.83
relation Eval_expr: `%;%~>*%;%`(state, expr, state, val*)
  ;; test.spectec:1427.1-1429.37
  rule mk_Eval_expr{z : state, instr_lst : instr*, z' : state, val_lst : val*}:
    `%;%~>*%;%`(z, instr_lst, z', val_lst)
    -- Steps: `%~>*%`(mk_config_config(z, $admininstr_instr(v_instr)*{v_instr <- instr_lst}), mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst}))
    -- wf_config: `%`(mk_config_config(z, $admininstr_instr(v_instr)*{v_instr <- instr_lst}))
    -- wf_config: `%`(mk_config_config(z', $admininstr_val(v_val)*{v_val <- val_lst}))

;; test.spectec:1683.1-1683.36
rec {

;; test.spectec:1683.6-1683.12
relation fun_funcs: `%%`(externaddr*, funcaddr*)
  ;; test.spectec:1683.6-1683.12
  rule fun_funcs_case_0:
    `%%`([], [])

  ;; test.spectec:1683.6-1683.12
  rule fun_funcs_case_1{fa : nat, externaddr'_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([FUNC_externaddr(fa)] ++ externaddr'_lst, [fa] ++ var_0)
    -- fun_funcs: `%%`(externaddr'_lst, var_0)

  ;; test.spectec:1683.6-1683.12
  rule fun_funcs_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : funcaddr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_funcs: `%%`(externaddr'_lst, var_0)
}

;; test.spectec:1689.1-1689.40
rec {

;; test.spectec:1689.6-1689.14
relation fun_globals: `%%`(externaddr*, globaladdr*)
  ;; test.spectec:1689.6-1689.14
  rule fun_globals_case_0:
    `%%`([], [])

  ;; test.spectec:1689.6-1689.14
  rule fun_globals_case_1{ga : nat, externaddr'_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([GLOBAL_externaddr(ga)] ++ externaddr'_lst, [ga] ++ var_0)
    -- fun_globals: `%%`(externaddr'_lst, var_0)

  ;; test.spectec:1689.6-1689.14
  rule fun_globals_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : globaladdr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_globals: `%%`(externaddr'_lst, var_0)
}

;; test.spectec:1695.1-1695.38
rec {

;; test.spectec:1695.6-1695.13
relation fun_tables: `%%`(externaddr*, tableaddr*)
  ;; test.spectec:1695.6-1695.13
  rule fun_tables_case_0:
    `%%`([], [])

  ;; test.spectec:1695.6-1695.13
  rule fun_tables_case_1{ta : nat, externaddr'_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([TABLE_externaddr(ta)] ++ externaddr'_lst, [ta] ++ var_0)
    -- fun_tables: `%%`(externaddr'_lst, var_0)

  ;; test.spectec:1695.6-1695.13
  rule fun_tables_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : tableaddr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_tables: `%%`(externaddr'_lst, var_0)
}

;; test.spectec:1701.1-1701.34
rec {

;; test.spectec:1701.6-1701.11
relation fun_mems: `%%`(externaddr*, memaddr*)
  ;; test.spectec:1701.6-1701.11
  rule fun_mems_case_0:
    `%%`([], [])

  ;; test.spectec:1701.6-1701.11
  rule fun_mems_case_1{ma : nat, externaddr'_lst : externaddr*, var_0 : memaddr*}:
    `%%`([MEM_externaddr(ma)] ++ externaddr'_lst, [ma] ++ var_0)
    -- fun_mems: `%%`(externaddr'_lst, var_0)

  ;; test.spectec:1701.6-1701.11
  rule fun_mems_case_2{v_externaddr : externaddr, externaddr'_lst : externaddr*, var_0 : memaddr*}:
    `%%`([v_externaddr] ++ externaddr'_lst, var_0)
    -- fun_mems: `%%`(externaddr'_lst, var_0)
}

;; test.spectec:1714.6-1714.16
relation fun_allocfunc: `%%%%`(store, moduleinst, func, (store, funcaddr))
  ;; test.spectec:1714.6-1714.16
  rule fun_allocfunc_case_0{s : store, v_moduleinst : moduleinst, v_func : func, fi : funcinst, x : uN, local_lst : local*, v_expr : instr*}:
    `%%%%`(s, v_moduleinst, v_func, (s[FUNCS_store =++ [fi]], |s.FUNCS_store|))
    -- if ($proj_uN_0(x).0 < |v_moduleinst.TYPES_moduleinst|)
    -- if (fi = {TYPE v_moduleinst.TYPES_moduleinst[$proj_uN_0(x).0], MODULE v_moduleinst, CODE v_func})
    -- if (v_func = FUNC_func(x, local_lst, v_expr))
    -- wf_funcinst: `%`({TYPE v_moduleinst.TYPES_moduleinst[$proj_uN_0(x).0], MODULE v_moduleinst, CODE v_func})
    -- wf_func: `%`(FUNC_func(x, local_lst, v_expr))

;; test.spectec:1714.6-1714.16
relation allocfunc_is_wf: `%%%%`(v_store : store, v_moduleinst : moduleinst, v_func : func, ret_val : (store, funcaddr))
  ;; test.spectec:1714.6-1714.16
  rule allocfunc_is_wf_0{v_store : store, v_moduleinst : moduleinst, v_func : func, ret_val : (store, funcaddr), var_0 : (store, funcaddr)}:
    `%%%%`(v_store, v_moduleinst, v_func, ret_val)
    -- fun_allocfunc: `%%%%`(v_store, v_moduleinst, v_func, var_0)
    -- wf_store: `%`(v_store)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- wf_func: `%`(v_func)
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1719.1-1719.63
rec {

;; test.spectec:1719.6-1719.17
relation fun_allocfuncs: `%%%%`(store, moduleinst, func*, (store, funcaddr*))
  ;; test.spectec:1719.6-1719.17
  rule fun_allocfuncs_case_0{s : store, v_moduleinst : moduleinst}:
    `%%%%`(s, v_moduleinst, [], (s, []))

  ;; test.spectec:1719.6-1719.17
  rule fun_allocfuncs_case_1{s : store, v_moduleinst : moduleinst, v_func : func, func'_lst : func*, fa : funcaddr, s_1 : store, s_2 : store, fa'_lst : funcaddr*, var_1 : (store, funcaddr*), var_0 : (store, funcaddr)}:
    `%%%%`(s, v_moduleinst, [v_func] ++ func'_lst, (s_2, [fa] ++ fa'_lst))
    -- fun_allocfuncs: `%%%%`(s_1, v_moduleinst, func'_lst, var_1)
    -- fun_allocfunc: `%%%%`(s, v_moduleinst, v_func, var_0)
    -- if ((s_1, fa) = var_0)
    -- if ((s_2, fa'_lst) = var_1)
}

;; test.spectec:1719.1-1719.63
rec {

;; test.spectec:1719.6-1719.17
relation allocfuncs_is_wf: `%%%%`(v_store : store, v_moduleinst : moduleinst, var_0_lst : func*, ret_val : (store, funcaddr*))
  ;; test.spectec:1719.6-1719.17
  rule allocfuncs_is_wf_0{v_store : store, v_moduleinst : moduleinst, var_0_lst : func*, ret_val : (store, funcaddr*), var_0 : (store, funcaddr*)}:
    `%%%%`(v_store, v_moduleinst, var_0_lst, ret_val)
    -- fun_allocfuncs: `%%%%`(v_store, v_moduleinst, var_0_lst, var_0)
    -- wf_store: `%`(v_store)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- (wf_func: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1725.6-1725.18
relation fun_allocglobal: `%%%%`(store, globaltype, val, (store, globaladdr))
  ;; test.spectec:1725.6-1725.18
  rule fun_allocglobal_case_0{s : store, v_globaltype : globaltype, v_val : val, gi : globalinst}:
    `%%%%`(s, v_globaltype, v_val, (s[GLOBALS_store =++ [gi]], |s.GLOBALS_store|))
    -- if (gi = {TYPE v_globaltype, VALUE v_val})
    -- wf_globalinst: `%`({TYPE v_globaltype, VALUE v_val})

;; test.spectec:1725.6-1725.18
relation allocglobal_is_wf: `%%%%`(v_store : store, v_globaltype : globaltype, v_val : val, ret_val : (store, globaladdr))
  ;; test.spectec:1725.6-1725.18
  rule allocglobal_is_wf_0{v_store : store, v_globaltype : globaltype, v_val : val, ret_val : (store, globaladdr), var_0 : (store, globaladdr)}:
    `%%%%`(v_store, v_globaltype, v_val, ret_val)
    -- fun_allocglobal: `%%%%`(v_store, v_globaltype, v_val, var_0)
    -- wf_store: `%`(v_store)
    -- wf_val: `%`(v_val)
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1729.1-1729.67
rec {

;; test.spectec:1729.6-1729.19
relation fun_allocglobals: `%%%%`(store, globaltype*, val*, (store, globaladdr*))
  ;; test.spectec:1729.6-1729.19
  rule fun_allocglobals_case_0{s : store}:
    `%%%%`(s, [], [], (s, []))

  ;; test.spectec:1729.6-1729.19
  rule fun_allocglobals_case_1{s : store, v_globaltype : globaltype, globaltype'_lst : globaltype*, v_val : val, val'_lst : val*, ga : globaladdr, s_1 : store, s_2 : store, ga'_lst : globaladdr*, var_1 : (store, globaladdr*), var_0 : (store, globaladdr)}:
    `%%%%`(s, [v_globaltype] ++ globaltype'_lst, [v_val] ++ val'_lst, (s_2, [ga] ++ ga'_lst))
    -- fun_allocglobals: `%%%%`(s_1, globaltype'_lst, val'_lst, var_1)
    -- fun_allocglobal: `%%%%`(s, v_globaltype, v_val, var_0)
    -- if ((s_1, ga) = var_0)
    -- if ((s_2, ga'_lst) = var_1)
}

;; test.spectec:1729.1-1729.67
rec {

;; test.spectec:1729.6-1729.19
relation allocglobals_is_wf: `%%%%`(v_store : store, var_0_lst : globaltype*, var_1_lst : val*, ret_val : (store, globaladdr*))
  ;; test.spectec:1729.6-1729.19
  rule allocglobals_is_wf_0{v_store : store, var_0_lst : globaltype*, var_1_lst : val*, ret_val : (store, globaladdr*), var_0 : (store, globaladdr*)}:
    `%%%%`(v_store, var_0_lst, var_1_lst, ret_val)
    -- fun_allocglobals: `%%%%`(v_store, var_0_lst, var_1_lst, var_0)
    -- wf_store: `%`(v_store)
    -- (wf_val: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1735.6-1735.17
relation fun_alloctable: `%%%`(store, tabletype, (store, tableaddr))
  ;; test.spectec:1735.6-1735.17
  rule fun_alloctable_case_0{s : store, i : uN, j_opt : u32?, ti : tableinst}:
    `%%%`(s, mk_limits_tabletype(i, j_opt), (s[TABLES_store =++ [ti]], |s.TABLES_store|))
    -- if (ti = {TYPE mk_limits_tabletype(i, j_opt), REFS ?()^$proj_uN_0(i).0{}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(i, j_opt), REFS ?()^$proj_uN_0(i).0{}})

;; test.spectec:1735.6-1735.17
relation alloctable_is_wf: `%%%`(v_store : store, v_tabletype : tabletype, ret_val : (store, tableaddr))
  ;; test.spectec:1735.6-1735.17
  rule alloctable_is_wf_0{v_store : store, v_tabletype : tabletype, ret_val : (store, tableaddr), var_0 : (store, tableaddr)}:
    `%%%`(v_store, v_tabletype, ret_val)
    -- fun_alloctable: `%%%`(v_store, v_tabletype, var_0)
    -- wf_store: `%`(v_store)
    -- wf_limits: `%`(v_tabletype)
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1739.1-1739.58
rec {

;; test.spectec:1739.6-1739.18
relation fun_alloctables: `%%%`(store, tabletype*, (store, tableaddr*))
  ;; test.spectec:1739.6-1739.18
  rule fun_alloctables_case_0{s : store}:
    `%%%`(s, [], (s, []))

  ;; test.spectec:1739.6-1739.18
  rule fun_alloctables_case_1{s : store, v_tabletype : limits, tabletype'_lst : tabletype*, ta : tableaddr, s_1 : store, s_2 : store, ta'_lst : tableaddr*, var_1 : (store, tableaddr*), var_0 : (store, tableaddr)}:
    `%%%`(s, [v_tabletype] ++ tabletype'_lst, (s_2, [ta] ++ ta'_lst))
    -- fun_alloctables: `%%%`(s_1, tabletype'_lst, var_1)
    -- fun_alloctable: `%%%`(s, v_tabletype, var_0)
    -- if ((s_1, ta) = var_0)
    -- if ((s_2, ta'_lst) = var_1)
}

;; test.spectec:1739.1-1739.58
rec {

;; test.spectec:1739.6-1739.18
relation alloctables_is_wf: `%%%`(v_store : store, var_0_lst : tabletype*, ret_val : (store, tableaddr*))
  ;; test.spectec:1739.6-1739.18
  rule alloctables_is_wf_0{v_store : store, var_0_lst : tabletype*, ret_val : (store, tableaddr*), var_0 : (store, tableaddr*)}:
    `%%%`(v_store, var_0_lst, ret_val)
    -- fun_alloctables: `%%%`(v_store, var_0_lst, var_0)
    -- wf_store: `%`(v_store)
    -- (wf_limits: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1745.6-1745.15
relation fun_allocmem: `%%%`(store, memtype, (store, memaddr))
  ;; test.spectec:1745.6-1745.15
  rule fun_allocmem_case_0{s : store, i : uN, j_opt : u32?, mi : meminst}:
    `%%%`(s, mk_limits_memtype(i, j_opt), (s[MEMS_store =++ [mi]], |s.MEMS_store|))
    -- if (mi = {TYPE mk_limits_memtype(i, j_opt), BYTES mk_byte_byte(0)^($proj_uN_0(i).0 * (64 * $Ki)){}})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(i, j_opt), BYTES mk_byte_byte(0)^($proj_uN_0(i).0 * (64 * $Ki)){}})

;; test.spectec:1745.6-1745.15
relation allocmem_is_wf: `%%%`(v_store : store, v_memtype : memtype, ret_val : (store, memaddr))
  ;; test.spectec:1745.6-1745.15
  rule allocmem_is_wf_0{v_store : store, v_memtype : memtype, ret_val : (store, memaddr), var_0 : (store, memaddr)}:
    `%%%`(v_store, v_memtype, ret_val)
    -- fun_allocmem: `%%%`(v_store, v_memtype, var_0)
    -- wf_store: `%`(v_store)
    -- wf_limits: `%`(v_memtype)
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1749.1-1749.52
rec {

;; test.spectec:1749.6-1749.16
relation fun_allocmems: `%%%`(store, memtype*, (store, memaddr*))
  ;; test.spectec:1749.6-1749.16
  rule fun_allocmems_case_0{s : store}:
    `%%%`(s, [], (s, []))

  ;; test.spectec:1749.6-1749.16
  rule fun_allocmems_case_1{s : store, v_memtype : limits, memtype'_lst : memtype*, ma : memaddr, s_1 : store, s_2 : store, ma'_lst : memaddr*, var_1 : (store, memaddr*), var_0 : (store, memaddr)}:
    `%%%`(s, [v_memtype] ++ memtype'_lst, (s_2, [ma] ++ ma'_lst))
    -- fun_allocmems: `%%%`(s_1, memtype'_lst, var_1)
    -- fun_allocmem: `%%%`(s, v_memtype, var_0)
    -- if ((s_1, ma) = var_0)
    -- if ((s_2, ma'_lst) = var_1)
}

;; test.spectec:1749.1-1749.52
rec {

;; test.spectec:1749.6-1749.16
relation allocmems_is_wf: `%%%`(v_store : store, var_0_lst : memtype*, ret_val : (store, memaddr*))
  ;; test.spectec:1749.6-1749.16
  rule allocmems_is_wf_0{v_store : store, var_0_lst : memtype*, ret_val : (store, memaddr*), var_0 : (store, memaddr*)}:
    `%%%`(v_store, var_0_lst, ret_val)
    -- fun_allocmems: `%%%`(v_store, var_0_lst, var_0)
    -- wf_store: `%`(v_store)
    -- (wf_limits: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1758.1-1758.83
def $instexport(var_0_lst : funcaddr*, var_1_lst : globaladdr*, var_2_lst : tableaddr*, var_3_lst : memaddr*, v_export : export) : exportinst
  ;; test.spectec:1759.1-1759.94
  def $instexport{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, FUNC_externidx(x))) = {NAME v_name, ADDR FUNC_externaddr(fa_lst[$proj_uN_0(x).0])}
  ;; test.spectec:1760.1-1760.98
  def $instexport{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, GLOBAL_externidx(x))) = {NAME v_name, ADDR GLOBAL_externaddr(ga_lst[$proj_uN_0(x).0])}
  ;; test.spectec:1761.1-1761.96
  def $instexport{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, TABLE_externidx(x))) = {NAME v_name, ADDR TABLE_externaddr(ta_lst[$proj_uN_0(x).0])}
  ;; test.spectec:1762.1-1762.92
  def $instexport{fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, v_name : name, x : uN}(fa_lst, ga_lst, ta_lst, ma_lst, EXPORT_export(v_name, MEM_externidx(x))) = {NAME v_name, ADDR MEM_externaddr(ma_lst[$proj_uN_0(x).0])}

;; test.spectec:1758.6-1758.17
relation instexport_is_wf: `%%%%%%`(var_0_lst : funcaddr*, var_1_lst : globaladdr*, var_2_lst : tableaddr*, var_3_lst : memaddr*, v_export : export, ret_val : exportinst)
  ;; test.spectec:1758.6-1758.17
  rule instexport_is_wf_0{var_0_lst : funcaddr*, var_1_lst : globaladdr*, var_2_lst : tableaddr*, var_3_lst : memaddr*, v_export : export, ret_val : exportinst}:
    `%%%%%%`(var_0_lst, var_1_lst, var_2_lst, var_3_lst, v_export, ret_val)
    -- wf_export: `%`(v_export)
    -- if (ret_val = $instexport(var_0_lst, var_1_lst, var_2_lst, var_3_lst, v_export))
    -- wf_exportinst: `%`(ret_val)

;; test.spectec:1765.6-1765.18
relation fun_allocmodule: `%%%%%`(store, module, externaddr*, val*, (store, moduleinst))
  ;; test.spectec:1765.6-1765.18
  rule fun_allocmodule_case_0{s : store, v_module : module, externaddr_lst : externaddr*, val_lst : val*, s_4 : store, v_moduleinst : moduleinst, ft_lst : functype*, import_lst : import*, n_func : nat, func_lst : func*, n_global : nat, expr_1_lst : expr*, globaltype_lst : globaltype*, n_table : nat, tabletype_lst : tabletype*, n_mem : nat, memtype_lst : memtype*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, s_1 : store, s_2 : store, s_3 : store, fa_ex_lst : funcaddr*, ga_ex_lst : globaladdr*, ta_ex_lst : tableaddr*, ma_ex_lst : memaddr*, fa_lst : funcaddr*, ga_lst : globaladdr*, ta_lst : tableaddr*, ma_lst : memaddr*, xi_lst : exportinst*, var_7 : (store, memaddr*), var_6 : (store, tableaddr*), var_5 : (store, globaladdr*), var_4 : (store, funcaddr*), var_3 : memaddr*, var_2 : tableaddr*, var_1 : globaladdr*, var_0 : funcaddr*}:
    `%%%%%`(s, v_module, externaddr_lst, val_lst, (s_4, v_moduleinst))
    -- fun_allocmems: `%%%`(s_3, memtype_lst, var_7)
    -- fun_alloctables: `%%%`(s_2, tabletype_lst, var_6)
    -- fun_allocglobals: `%%%%`(s_1, globaltype_lst, val_lst, var_5)
    -- fun_allocfuncs: `%%%%`(s, v_moduleinst, func_lst, var_4)
    -- fun_mems: `%%`(externaddr_lst, var_3)
    -- fun_tables: `%%`(externaddr_lst, var_2)
    -- fun_globals: `%%`(externaddr_lst, var_1)
    -- fun_funcs: `%%`(externaddr_lst, var_0)
    -- if (v_module = MODULE_module(TYPE_type(ft_1)*{ft_1 <- ft_lst}, import_lst, func_lst, GLOBAL_global(globaltype_195, expr_1_1)^n_global{expr_1_1 <- expr_1_lst, globaltype_195 <- globaltype_lst}, TABLE_table(tabletype_241)^n_table{tabletype_241 <- tabletype_lst}, MEMORY_mem(memtype_293)^n_mem{memtype_293 <- memtype_lst}, elem_lst, data_lst, start_opt, export_lst))
    -- if (fa_ex_lst = var_0)
    -- if (ga_ex_lst = var_1)
    -- if (ta_ex_lst = var_2)
    -- if (ma_ex_lst = var_3)
    -- if (fa_lst = (|s.FUNCS_store| + i_func_1)^(i_func_1<n_func){})
    -- if (ga_lst = (|s.GLOBALS_store| + i_global_1)^(i_global_1<n_global){})
    -- if (ta_lst = (|s.TABLES_store| + i_table_1)^(i_table_1<n_table){})
    -- if (ma_lst = (|s.MEMS_store| + i_mem_1)^(i_mem_1<n_mem){})
    -- if (xi_lst = $instexport(fa_ex_lst ++ fa_lst, ga_ex_lst ++ ga_lst, ta_ex_lst ++ ta_lst, ma_ex_lst ++ ma_lst, export_2)*{export_2 <- export_lst})
    -- if (v_moduleinst = {TYPES ft_lst, FUNCS fa_ex_lst ++ fa_lst, GLOBALS ga_ex_lst ++ ga_lst, TABLES ta_ex_lst ++ ta_lst, MEMS ma_ex_lst ++ ma_lst, EXPORTS xi_lst})
    -- if ((s_1, fa_lst) = var_4)
    -- if ((s_2, ga_lst) = var_5)
    -- if ((s_3, ta_lst) = var_6)
    -- if ((s_4, ma_lst) = var_7)
    -- wf_store: `%`(s_1)
    -- wf_store: `%`(s_2)
    -- wf_store: `%`(s_3)
    -- wf_module: `%`(MODULE_module(TYPE_type(ft_3)*{ft_3 <- ft_lst}, import_lst, func_lst, GLOBAL_global(globaltype_198, expr_1_2)^n_global{expr_1_2 <- expr_1_lst, globaltype_198 <- globaltype_lst}, TABLE_table(tabletype_244)^n_table{tabletype_244 <- tabletype_lst}, MEMORY_mem(memtype_296)^n_mem{memtype_296 <- memtype_lst}, elem_lst, data_lst, start_opt, export_lst))
    -- wf_moduleinst: `%`({TYPES ft_lst, FUNCS fa_ex_lst ++ fa_lst, GLOBALS ga_ex_lst ++ ga_lst, TABLES ta_ex_lst ++ ta_lst, MEMS ma_ex_lst ++ ma_lst, EXPORTS xi_lst})

;; test.spectec:1765.6-1765.18
relation allocmodule_is_wf: `%%%%%`(v_store : store, v_module : module, var_0_lst : externaddr*, var_1_lst : val*, ret_val : (store, moduleinst))
  ;; test.spectec:1765.6-1765.18
  rule allocmodule_is_wf_0{v_store : store, v_module : module, var_0_lst : externaddr*, var_1_lst : val*, ret_val : (store, moduleinst), var_0 : (store, moduleinst)}:
    `%%%%%`(v_store, v_module, var_0_lst, var_1_lst, ret_val)
    -- fun_allocmodule: `%%%%%`(v_store, v_module, var_0_lst, var_1_lst, var_0)
    -- wf_store: `%`(v_store)
    -- wf_module: `%`(v_module)
    -- (wf_val: `%`(var_1))*{var_1 <- var_1_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val.0)
    -- wf_moduleinst: `%`(ret_val.1)

;; test.spectec:1806.1-1806.61
rec {

;; test.spectec:1806.6-1806.15
relation fun_initelem: `%%%%%`(store, moduleinst, u32*, funcaddr**, store)
  ;; test.spectec:1806.6-1806.15
  rule fun_initelem_case_0{s : store, v_moduleinst : moduleinst}:
    `%%%%%`(s, v_moduleinst, [], [], s)

  ;; test.spectec:1806.6-1806.15
  rule fun_initelem_case_1{s : store, v_moduleinst : moduleinst, i : uN, i'_lst : u32*, a_lst : addr*, a'_lst_lst : addr**, s_1 : store, s_2 : store, var_0 : store}:
    `%%%%%`(s, v_moduleinst, [i] ++ i'_lst, [a_lst] ++ a'_lst_lst, s_2)
    -- fun_initelem: `%%%%%`(s_1, v_moduleinst, i'_lst, a'_lst_lst, var_0)
    -- if (0 < |v_moduleinst.TABLES_moduleinst|)
    -- if (s_1 = s[TABLES_store[v_moduleinst.TABLES_moduleinst[0]].REFS_tableinst[$proj_uN_0(i).0 : |a_lst|] = ?(a_7)*{a_7 <- a_lst}])
    -- if (s_2 = var_0)
    -- wf_store: `%`(s_1)
}

;; test.spectec:1806.1-1806.61
rec {

;; test.spectec:1806.6-1806.15
relation initelem_is_wf: `%%%%%`(v_store : store, v_moduleinst : moduleinst, var_0_lst : u32*, var_1_lst_lst : funcaddr**, ret_val : store)
  ;; test.spectec:1806.6-1806.15
  rule initelem_is_wf_0{v_store : store, v_moduleinst : moduleinst, var_0_lst : u32*, var_1_lst_lst : funcaddr**, ret_val : store, var_0 : store}:
    `%%%%%`(v_store, v_moduleinst, var_0_lst, var_1_lst_lst, ret_val)
    -- fun_initelem: `%%%%%`(v_store, v_moduleinst, var_0_lst, var_1_lst_lst, var_0)
    -- wf_store: `%`(v_store)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val)
}

;; test.spectec:1812.1-1812.57
rec {

;; test.spectec:1812.6-1812.15
relation fun_initdata: `%%%%%`(store, moduleinst, u32*, byte**, store)
  ;; test.spectec:1812.6-1812.15
  rule fun_initdata_case_0{s : store, v_moduleinst : moduleinst}:
    `%%%%%`(s, v_moduleinst, [], [], s)

  ;; test.spectec:1812.6-1812.15
  rule fun_initdata_case_1{s : store, v_moduleinst : moduleinst, i : uN, i'_lst : u32*, b_lst : byte*, b'_lst_lst : byte**, s_1 : store, s_2 : store, var_0 : store}:
    `%%%%%`(s, v_moduleinst, [i] ++ i'_lst, [b_lst] ++ b'_lst_lst, s_2)
    -- fun_initdata: `%%%%%`(s_1, v_moduleinst, i'_lst, b'_lst_lst, var_0)
    -- if (0 < |v_moduleinst.MEMS_moduleinst|)
    -- if (s_1 = s[MEMS_store[v_moduleinst.MEMS_moduleinst[0]].BYTES_meminst[$proj_uN_0(i).0 : |b_lst|] = b_lst])
    -- if (s_2 = var_0)
}

;; test.spectec:1812.1-1812.57
rec {

;; test.spectec:1812.6-1812.15
relation initdata_is_wf: `%%%%%`(v_store : store, v_moduleinst : moduleinst, var_0_lst : u32*, var_1_lst_lst : byte**, ret_val : store)
  ;; test.spectec:1812.6-1812.15
  rule initdata_is_wf_0{v_store : store, v_moduleinst : moduleinst, var_0_lst : u32*, var_1_lst_lst : byte**, ret_val : store, var_0 : store}:
    `%%%%%`(v_store, v_moduleinst, var_0_lst, var_1_lst_lst, ret_val)
    -- fun_initdata: `%%%%%`(v_store, v_moduleinst, var_0_lst, var_1_lst_lst, var_0)
    -- wf_store: `%`(v_store)
    -- wf_moduleinst: `%`(v_moduleinst)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- var_0_lst}
    -- (wf_byte: `%`(var_1))*{var_1 <- var_1_lst}*{var_1_lst <- var_1_lst_lst}
    -- if (ret_val = var_0)
    -- wf_store: `%`(ret_val)
}

;; test.spectec:1818.6-1818.18
relation fun_instantiate: `%%%%`(store, module, externaddr*, config)
  ;; test.spectec:1818.6-1818.18
  rule fun_instantiate_case_0{s : store, v_module : module, externaddr_lst : externaddr*, f : frame, x'_opt : idx?, functype_lst : functype*, expr_G_lst : expr*, globaltype_lst : globaltype*, expr_E_lst : expr*, x_lst_lst : idx**, b_lst_lst : byte**, expr_D_lst : expr*, moduleinst_init : moduleinst, f_init : frame, val_lst : val*, i_E_lst : val_*, i_D_lst : val_*, type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, n_F : n, z : state, s_1 : store, v_moduleinst : moduleinst, s_2 : store, s_3 : store, var_6 : globaladdr*, var_5 : funcaddr*, var_4 : store, var_3 : store, var_2 : (store, moduleinst), var_1 : globaladdr*, var_0 : funcaddr*}:
    `%%%%`(s, v_module, externaddr_lst, mk_config_config(mk_state_state(s_3, f), lift(CALL_admininstr(x')?{x' <- x'_opt})))
    -- fun_globals: `%%`(externaddr_lst, var_6)
    -- fun_funcs: `%%`(externaddr_lst, var_5)
    -- (if ($proj_val__0(i_D_2) =/= ?()))*{i_D_2 <- i_D_lst}
    -- fun_initdata: `%%%%%`(s_2, v_moduleinst, !($proj_val__0(i_D_2))*{i_D_2 <- i_D_lst}, b_lst_lst, var_4)
    -- (if ($proj_val__0(i_E_2) =/= ?()))*{i_E_2 <- i_E_lst}
    -- (if ($proj_uN_0(x_2).0 < |v_moduleinst.FUNCS_moduleinst|))*{x_2 <- x_lst_2}*{x_lst_2 <- x_lst_lst}
    -- fun_initelem: `%%%%%`(s_1, v_moduleinst, !($proj_val__0(i_E_2))*{i_E_2 <- i_E_lst}, v_moduleinst.FUNCS_moduleinst[$proj_uN_0(x_2).0]*{x_2 <- x_lst_2}*{x_lst_2 <- x_lst_lst}, var_3)
    -- fun_allocmodule: `%%%%%`(s, v_module, externaddr_lst, val_lst, var_2)
    -- fun_globals: `%%`(externaddr_lst, var_1)
    -- fun_funcs: `%%`(externaddr_lst, var_0)
    -- if (MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst) = v_module)
    -- if (type_lst = TYPE_type(functype_49)*{functype_49 <- functype_lst})
    -- if (global_lst = GLOBAL_global(globaltype_200, expr_G_1)*{expr_G_1 <- expr_G_lst, globaltype_200 <- globaltype_lst})
    -- if (elem_lst = ELEM_elem(expr_E_1, x_lst_1)*{expr_E_1 <- expr_E_lst, x_lst_1 <- x_lst_lst})
    -- if (data_lst = DATA_data(expr_D_1, b_lst_1)*{b_lst_1 <- b_lst_lst, expr_D_1 <- expr_D_lst})
    -- if (start_opt = START_start(x'_1)?{x'_1 <- x'_opt})
    -- if (n_F = |func_lst|)
    -- if (moduleinst_init = {TYPES functype_lst, FUNCS var_0 ++ (|s.FUNCS_store| + i_F_1)^(i_F_1<n_F){}, GLOBALS var_1, TABLES [], MEMS [], EXPORTS []})
    -- if (f_init = {LOCALS [], MODULE moduleinst_init})
    -- if (z = mk_state_state(s, f_init))
    -- if (|expr_G_lst| = |val_lst|)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_G_2, z, [val_3]))*{expr_G_2 <- expr_G_lst, val_3 <- val_lst}
    -- if (|expr_E_lst| = |i_E_lst|)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_E_2, z, [CONST_val(I32_valtype, i_E_1)]))*{expr_E_2 <- expr_E_lst, i_E_1 <- i_E_lst}
    -- if (|expr_D_lst| = |i_D_lst|)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_D_2, z, [CONST_val(I32_valtype, i_D_1)]))*{expr_D_2 <- expr_D_lst, i_D_1 <- i_D_lst}
    -- if ((s_1, v_moduleinst) = var_2)
    -- if (s_2 = var_3)
    -- if (s_3 = var_4)
    -- if (f = {LOCALS [], MODULE v_moduleinst})
    -- (wf_val: `%`(val_5))*{val_5 <- val_lst}
    -- wf_module: `%`(MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst))
    -- if (|expr_G_lst| = |globaltype_lst|)
    -- (wf_global: `%`(GLOBAL_global(globaltype_202, expr_G_3)))*{expr_G_3 <- expr_G_lst, globaltype_202 <- globaltype_lst}
    -- if (|expr_E_lst| = |x_lst_lst|)
    -- (wf_elem: `%`(ELEM_elem(expr_E_3, x_lst_3)))*{expr_E_3 <- expr_E_lst, x_lst_3 <- x_lst_lst}
    -- if (|b_lst_lst| = |expr_D_lst|)
    -- (wf_data: `%`(DATA_data(expr_D_3, b_lst_3)))*{b_lst_3 <- b_lst_lst, expr_D_3 <- expr_D_lst}
    -- (wf_start: `%`(START_start(x'_2)))?{x'_2 <- x'_opt}
    -- wf_moduleinst: `%`({TYPES functype_lst, FUNCS var_5 ++ (|s.FUNCS_store| + i_F_2)^(i_F_2<n_F){}, GLOBALS var_6, TABLES [], MEMS [], EXPORTS []})
    -- wf_frame: `%`({LOCALS [], MODULE moduleinst_init})
    -- wf_state: `%`(mk_state_state(s, f_init))
    -- (wf_val: `%`(CONST_val(I32_valtype, i_E_3)))*{i_E_3 <- i_E_lst}
    -- (wf_val: `%`(CONST_val(I32_valtype, i_D_3)))*{i_D_3 <- i_D_lst}
    -- wf_frame: `%`({LOCALS [], MODULE v_moduleinst})

;; test.spectec:1818.6-1818.18
relation instantiate_is_wf: `%%%%`(v_store : store, v_module : module, var_0_lst : externaddr*, ret_val : config)
  ;; test.spectec:1818.6-1818.18
  rule instantiate_is_wf_0{v_store : store, v_module : module, var_0_lst : externaddr*, ret_val : config, var_0 : config}:
    `%%%%`(v_store, v_module, var_0_lst, ret_val)
    -- fun_instantiate: `%%%%`(v_store, v_module, var_0_lst, var_0)
    -- wf_store: `%`(v_store)
    -- wf_module: `%`(v_module)
    -- if (ret_val = var_0)
    -- wf_config: `%`(ret_val)

;; test.spectec:1847.6-1847.13
relation fun_invoke: `%%%%`(store, funcaddr, val*, config)
  ;; test.spectec:1847.6-1847.13
  rule fun_invoke_case_0{s : store, fa : nat, v_n : nat, val_lst : val*, f : frame, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%%%%`(s, fa, val_lst, mk_config_config(mk_state_state(s, f), $admininstr_val(v_val)^v_n{v_val <- val_lst} ++ [CALL_ADDR_admininstr(fa)]))
    -- if (f = {LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], EXPORTS []}})
    -- if (fa < |$fun_funcinst(mk_state_state(s, f))|)
    -- if ($fun_funcinst(mk_state_state(s, f))[fa].TYPE_funcinst = mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_frame: `%`({LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], EXPORTS []}})
    -- wf_state: `%`(mk_state_state(s, f))
    -- if (v_n = |val_lst|)

;; test.spectec:1847.6-1847.13
relation invoke_is_wf: `%%%%`(v_store : store, v_funcaddr : funcaddr, var_0_lst : val*, ret_val : config)
  ;; test.spectec:1847.6-1847.13
  rule invoke_is_wf_0{v_store : store, v_funcaddr : funcaddr, var_0_lst : val*, ret_val : config, var_0 : config}:
    `%%%%`(v_store, v_funcaddr, var_0_lst, ret_val)
    -- fun_invoke: `%%%%`(v_store, v_funcaddr, var_0_lst, var_0)
    -- wf_store: `%`(v_store)
    -- (wf_val: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val = var_0)
    -- wf_config: `%`(ret_val)

;; test.spectec:2339.1-2339.43
syntax startopt = start*

;; test.spectec:2356.1-2356.29
syntax code = (local*, expr)

;; test.spectec:2406.1-2406.61
relation Context_ok: `|-%:OK`(context)
  ;; test.spectec:2408.1-2424.34
  rule mk_Context_ok{C : context, ft_lst : functype*, ft_2_lst : functype*, gt_lst : globaltype*, tt_lst : tabletype*, mt_lst : memtype*, lct_lst : valtype*, rt_lst : valtype*, rt'_opt : valtype?}:
    `|-%:OK`(C)
    -- if (C = {TYPES ft_lst, FUNCS ft_2_lst, GLOBALS gt_lst, TABLES tt_lst, MEMS mt_lst, LOCALS lct_lst, LABELS ?(rt)*{rt <- rt_lst}, RETURN ?(rt'_opt)})
    -- (Functype_ok: `|-%:OK`(ft))*{ft <- ft_lst}
    -- (Globaltype_ok: `|-%:OK`(gt))*{gt <- gt_lst}
    -- (Memtype_ok: `|-%:OK`(mt))*{mt <- mt_lst}
    -- (Tabletype_ok: `|-%:OK`(tt))*{tt <- tt_lst}
    -- (Functype_ok: `|-%:OK`(ft_2))*{ft_2 <- ft_2_lst}
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES ft_lst, FUNCS ft_2_lst, GLOBALS gt_lst, TABLES tt_lst, MEMS mt_lst, LOCALS lct_lst, LABELS ?(rt)*{rt <- rt_lst}, RETURN ?(rt'_opt)})

;; test.spectec:2428.1-2428.34
relation Val_ok: `|-%:%`(val, valtype)
  ;; test.spectec:2430.1-2431.21
  rule mk_Val_ok{t : valtype, c_t : val_}:
    `|-%:%`(CONST_val(t, c_t), t)
    -- wf_val: `%`(CONST_val(t, c_t))

;; test.spectec:2436.1-2436.41
relation Result_ok: `|-%:%`(result, valtype*)
  ;; test.spectec:2438.1-2440.25
  rule result{v_lst : val*, t_lst : valtype*}:
    `|-%:%`(_VALS_result(v_lst), t_lst)
    -- if (|t_lst| = |v_lst|)
    -- (Val_ok: `|-%:%`(v, t))*{t <- t_lst, v <- v_lst}
    -- wf_result: `%`(_VALS_result(v_lst))

  ;; test.spectec:2442.1-2443.15
  rule trap{t_lst : valtype*}:
    `|-%:%`(TRAP_result, t_lst)
    -- wf_result: `%`(TRAP_result)

;; test.spectec:2447.1-2447.31
syntax adminexpr = admininstr*

;; test.spectec:2498.1-2498.84
rec {

;; test.spectec:2498.1-2498.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; test.spectec:2500.1-2502.34
  rule global{s : store, a : addr, v_globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(v_globalinst.TYPE_globalinst))
    -- if (a < |s.GLOBALS_store|)
    -- if (s.GLOBALS_store[a] = v_globalinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(GLOBAL_externtype(v_globalinst.TYPE_globalinst))

  ;; test.spectec:2504.1-2506.28
  rule mem{s : store, a : addr, v_meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(v_meminst.TYPE_meminst))
    -- if (a < |s.MEMS_store|)
    -- if (s.MEMS_store[a] = v_meminst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(MEM_externtype(v_meminst.TYPE_meminst))

  ;; test.spectec:2508.1-2510.32
  rule table{s : store, a : addr, v_tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(v_tableinst.TYPE_tableinst))
    -- if (a < |s.TABLES_store|)
    -- if (s.TABLES_store[a] = v_tableinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TABLE_externtype(v_tableinst.TYPE_tableinst))

  ;; test.spectec:2512.1-2514.30
  rule func{s : store, a : addr, v_funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype(v_funcinst.TYPE_funcinst))
    -- if (a < |s.FUNCS_store|)
    -- if (s.FUNCS_store[a] = v_funcinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(FUNC_externtype(v_funcinst.TYPE_funcinst))

  ;; test.spectec:2516.1-2519.34
  rule sub{s : store, v_externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, v_externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, v_externaddr, xt')
    -- Externtype_sub: `|-%<:%`(xt', xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_externtype: `%`(xt')
}

;; test.spectec:2527.1-2527.49
relation Exportinst_ok: `%|-%:OK`(store, exportinst)
  ;; test.spectec:2551.1-2553.33
  rule mk_Exportinst_ok{s : store, nm : name, xa : externaddr, xt : externtype}:
    `%|-%:OK`(s, {NAME nm, ADDR xa})
    -- Externaddr_ok: `%|-%:%`(s, xa, xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_exportinst: `%`({NAME nm, ADDR xa})

;; test.spectec:2558.1-2558.54
relation Moduleinst_ok: `%|-%:%`(store, moduleinst, context)
  ;; test.spectec:2560.1-2581.102
  rule mk_Moduleinst_ok{s : store, functype_lst : functype*, funcaddr_lst : funcaddr*, globaladdr_lst : globaladdr*, tableaddr_lst : tableaddr*, memaddr_lst : memaddr*, exportinst_lst : exportinst*, functype_F_lst : functype*, globaltype_lst : globaltype*, tabletype_lst : tabletype*, memtype_lst : memtype*}:
    `%|-%:%`(s, {TYPES functype_lst, FUNCS funcaddr_lst, GLOBALS globaladdr_lst, TABLES tableaddr_lst, MEMS memaddr_lst, EXPORTS exportinst_lst}, {TYPES functype_lst, FUNCS functype_F_lst, GLOBALS globaltype_lst, TABLES tabletype_lst, MEMS memtype_lst, LOCALS [], LABELS [], RETURN ?()})
    -- (Functype_ok: `|-%:OK`(v_functype))*{v_functype <- functype_lst}
    -- if (|globaladdr_lst| = |globaltype_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, GLOBAL_externaddr(v_globaladdr), GLOBAL_externtype(v_globaltype)))*{v_globaladdr <- globaladdr_lst, v_globaltype <- globaltype_lst}
    -- if (|funcaddr_lst| = |functype_F_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(v_funcaddr), FUNC_externtype(functype_F)))*{v_funcaddr <- funcaddr_lst, functype_F <- functype_F_lst}
    -- if (|memaddr_lst| = |memtype_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, MEM_externaddr(v_memaddr), MEM_externtype(v_memtype)))*{v_memaddr <- memaddr_lst, v_memtype <- memtype_lst}
    -- if (|tableaddr_lst| = |tabletype_lst|)
    -- (Externaddr_ok: `%|-%:%`(s, TABLE_externaddr(v_tableaddr), TABLE_externtype(v_tabletype)))*{v_tableaddr <- tableaddr_lst, v_tabletype <- tabletype_lst}
    -- (Exportinst_ok: `%|-%:OK`(s, v_exportinst))*{v_exportinst <- exportinst_lst}
    -- if $disjoint_(syntax name, v_exportinst.NAME_exportinst*{v_exportinst <- exportinst_lst})
    -- if (|GLOBAL_externaddr(v_globaladdr)*{v_globaladdr <- globaladdr_lst} ++ MEM_externaddr(v_memaddr)*{v_memaddr <- memaddr_lst} ++ TABLE_externaddr(v_tableaddr)*{v_tableaddr <- tableaddr_lst} ++ FUNC_externaddr(v_funcaddr)*{v_funcaddr <- funcaddr_lst}| > 0)
    -- (if (v_exportinst.ADDR_exportinst <- GLOBAL_externaddr(v_globaladdr)*{v_globaladdr <- globaladdr_lst} ++ MEM_externaddr(v_memaddr)*{v_memaddr <- memaddr_lst} ++ TABLE_externaddr(v_tableaddr)*{v_tableaddr <- tableaddr_lst} ++ FUNC_externaddr(v_funcaddr)*{v_funcaddr <- funcaddr_lst}))*{v_exportinst <- exportinst_lst}
    -- wf_store: `%`(s)
    -- wf_moduleinst: `%`({TYPES functype_lst, FUNCS funcaddr_lst, GLOBALS globaladdr_lst, TABLES tableaddr_lst, MEMS memaddr_lst, EXPORTS exportinst_lst})
    -- wf_context: `%`({TYPES functype_lst, FUNCS functype_F_lst, GLOBALS globaltype_lst, TABLES tabletype_lst, MEMS memtype_lst, LOCALS [], LABELS [], RETURN ?()})
    -- (wf_externtype: `%`(GLOBAL_externtype(v_globaltype)))*{v_globaltype <- globaltype_lst}
    -- (wf_externtype: `%`(FUNC_externtype(functype_F)))*{functype_F <- functype_F_lst}
    -- (wf_externtype: `%`(MEM_externtype(v_memtype)))*{v_memtype <- memtype_lst}
    -- (wf_externtype: `%`(TABLE_externtype(v_tabletype)))*{v_tabletype <- tabletype_lst}

;; test.spectec:2631.1-2631.44
relation Frame_ok: `%|-%:%`(store, frame, context)
  ;; test.spectec:2635.1-2638.27
  rule mk_Frame_ok{s : store, val_lst : val*, v_moduleinst : moduleinst, C : context, t_lst : valtype*}:
    `%|-%:%`(s, {LOCALS val_lst, MODULE v_moduleinst}, C +++ {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_lst, LABELS [], RETURN ?()})
    -- Moduleinst_ok: `%|-%:%`(s, v_moduleinst, C)
    -- if (|t_lst| = |val_lst|)
    -- (Val_ok: `|-%:%`(v_val, t))*{t <- t_lst, v_val <- val_lst}
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_frame: `%`({LOCALS val_lst, MODULE v_moduleinst})
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_lst, LABELS [], RETURN ?()})

;; test.spectec:2449.1-2454.36
rec {

;; test.spectec:2449.1-2450.36
relation Instr_ok2: `%;%|-%:%`(store, context, admininstr, functype)
  ;; test.spectec:2456.1-2458.41
  rule plain{s : store, C : context, v_instr : instr, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, $admininstr_instr(v_instr), mk_functype_functype(t_1_lst, t_2_lst))
    -- Instr_ok: `%|-%:%`(C, v_instr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(v_instr)

  ;; test.spectec:2460.1-2464.67
  rule label{s : store, C : context, v_n : n, instr'_lst : instr*, admininstr_lst : admininstr*, t_opt : valtype?, t'_opt : valtype?}:
    `%;%|-%:%`(s, C, `LABEL_%{%}%`_admininstr(v_n, instr'_lst, admininstr_lst), mk_functype_functype([], lift(t_opt)))
    -- if (|lift(t'_opt)| = v_n)
    -- Instrs_ok2: `%;%|-%:%`(s, C, $admininstr_instr(instr')*{instr' <- instr'_lst}, mk_functype_functype(lift(t'_opt), lift(t_opt)))
    -- Instrs_ok2: `%;%|-%:%`(s, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t'_opt], RETURN ?()} +++ C, admininstr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(v_n, instr'_lst, admininstr_lst))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t'_opt], RETURN ?()})

  ;; test.spectec:2466.1-2470.41
  rule frame{s : store, C : context, v_n : n, f : frame, admininstr_lst : admininstr*, t_opt : valtype?, C' : context}:
    `%;%|-%:%`(s, C, `FRAME_%{%}%`_admininstr(v_n, f, admininstr_lst), mk_functype_functype([], lift(t_opt)))
    -- if (|lift(t_opt)| = v_n)
    -- Frame_ok: `%|-%:%`(s, f, C')
    -- Expr_ok2: `%;%|-%:%`(s, C', admininstr_lst, t_opt)
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_context: `%`(C')
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(v_n, f, admininstr_lst))

  ;; test.spectec:2472.1-2474.60
  rule call_addr{s : store, C : context, v_funcaddr : funcaddr, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, CALL_ADDR_admininstr(v_funcaddr), mk_functype_functype(t_1_lst, t_2_lst))
    -- Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(v_funcaddr), FUNC_externtype(mk_functype_functype(t_1_lst, t_2_lst)))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(v_funcaddr))
    -- wf_externtype: `%`(FUNC_externtype(mk_functype_functype(t_1_lst, t_2_lst)))

  ;; test.spectec:2476.1-2477.30
  rule trap{s : store, C : context, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, TRAP_admininstr, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(TRAP_admininstr)

;; test.spectec:2451.1-2452.36
relation Instrs_ok2: `%;%|-%:%`(store, context, admininstr*, functype)
  ;; test.spectec:2480.1-2481.27
  rule empty{s : store, C : context}:
    `%;%|-%:%`(s, C, [], mk_functype_functype([], []))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)

  ;; test.spectec:2483.1-2486.54
  rule seq{s : store, C : context, admininstr_1 : admininstr, admininstr_2_lst : admininstr*, t_1_lst : valtype*, t_3_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, [admininstr_1] ++ admininstr_2_lst, mk_functype_functype(t_1_lst, t_3_lst))
    -- Instr_ok2: `%;%|-%:%`(s, C, admininstr_1, mk_functype_functype(t_1_lst, t_2_lst))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_2_lst, mk_functype_functype(t_2_lst, t_3_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(admininstr_1)
    -- (wf_admininstr: `%`(admininstr_2))*{admininstr_2 <- admininstr_2_lst}

  ;; test.spectec:2488.1-2490.52
  rule frame{s : store, C : context, admininstr_lst : admininstr*, t_lst : valtype*, t_1_lst : valtype*, t_2_lst : valtype*}:
    `%;%|-%:%`(s, C, admininstr_lst, mk_functype_functype(t_lst ++ t_1_lst, t_lst ++ t_2_lst))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_lst, mk_functype_functype(t_1_lst, t_2_lst))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}

;; test.spectec:2453.1-2454.36
relation Expr_ok2: `%;%|-%:%`(store, context, adminexpr, resulttype)
  ;; test.spectec:2492.1-2494.49
  rule mk_Expr_ok2{s : store, C : context, admininstr_lst : admininstr*, t_opt : valtype?}:
    `%;%|-%:%`(s, C, admininstr_lst, t_opt)
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_lst, mk_functype_functype([], lift(t_opt)))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(v_admininstr))*{v_admininstr <- admininstr_lst}
}

;; test.spectec:2523.1-2523.57
relation Globalinst_ok: `%|-%:%`(store, globalinst, globaltype)
  ;; test.spectec:2529.1-2532.24
  rule mk_Globalinst_ok{s : store, v_mut : mut, t : valtype, v_val : val}:
    `%|-%:%`(s, {TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val}, mk_globaltype_globaltype(v_mut, t))
    -- Globaltype_ok: `|-%:OK`(mk_globaltype_globaltype(v_mut, t))
    -- Val_ok: `|-%:%`(v_val, t)
    -- wf_store: `%`(s)
    -- wf_globalinst: `%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val})

;; test.spectec:2524.1-2524.48
relation Meminst_ok: `%|-%:%`(store, meminst, memtype)
  ;; test.spectec:2534.1-2537.37
  rule mk_Meminst_ok{s : store, v_n : n, m_opt : m?, b_lst : byte*}:
    `%|-%:%`(s, {TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst}, mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- Memtype_ok: `|-%:OK`(mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- if (|b_lst| = (v_n * (64 * $Ki)))
    -- wf_store: `%`(s)
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst})
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))

;; test.spectec:2525.1-2525.54
relation Tableinst_ok: `%|-%:%`(store, tableinst, tabletype)
  ;; test.spectec:2539.1-2543.21
  rule mk_Tableinst_ok{s : store, v_n : n, m_opt : m?, fa_opt_lst : funcaddr?*, ft_opt_lst : functype?*}:
    `%|-%:%`(s, {TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS fa_opt_lst}, mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- Tabletype_ok: `|-%:OK`(mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- if (|fa_opt_lst| = |ft_opt_lst|)
    -- (if ((fa_opt = ?()) <=> (ft_opt = ?())))*{fa_opt <- fa_opt_lst, ft_opt <- ft_opt_lst}
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(fa), FUNC_externtype(ft)))?{fa <- fa_opt, ft <- ft_opt}*{fa_opt <- fa_opt_lst, ft_opt <- ft_opt_lst}
    -- if (|fa_opt_lst| = v_n)
    -- wf_store: `%`(s)
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS fa_opt_lst})
    -- wf_limits: `%`(mk_limits_limits(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}))
    -- (wf_externtype: `%`(FUNC_externtype(ft)))?{ft <- ft_opt}*{ft_opt <- ft_opt_lst}

;; test.spectec:2526.1-2526.51
relation Funcinst_ok: `%|-%:%`(store, funcinst, functype)
  ;; test.spectec:2545.1-2549.29
  rule mk_Funcinst_ok{s : store, ft : functype, v_moduleinst : moduleinst, v_func : func, C : context}:
    `%|-%:%`(s, {TYPE ft, MODULE v_moduleinst, CODE v_func}, ft)
    -- Functype_ok: `|-%:OK`(ft)
    -- Moduleinst_ok: `%|-%:%`(s, v_moduleinst, C)
    -- Func_ok: `%|-%:%`(C, v_func, ft)
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_funcinst: `%`({TYPE ft, MODULE v_moduleinst, CODE v_func})

;; test.spectec:2586.1-2586.33
relation Store_ok: `|-%:OK`(store)
  ;; test.spectec:2588.1-2595.85
  rule mk_Store_ok{s : store, globalinst_lst : globalinst*, globaltype_lst : globaltype*, meminst_lst : meminst*, memtype_lst : memtype*, tableinst_lst : tableinst*, tabletype_lst : tabletype*, funcinst_lst : funcinst*, functype_lst : functype*}:
    `|-%:OK`(s)
    -- if (|globalinst_lst| = |globaltype_lst|)
    -- (Globalinst_ok: `%|-%:%`(s, v_globalinst, v_globaltype))*{v_globalinst <- globalinst_lst, v_globaltype <- globaltype_lst}
    -- if (|meminst_lst| = |memtype_lst|)
    -- (Meminst_ok: `%|-%:%`(s, v_meminst, v_memtype))*{v_meminst <- meminst_lst, v_memtype <- memtype_lst}
    -- if (|tableinst_lst| = |tabletype_lst|)
    -- (Tableinst_ok: `%|-%:%`(s, v_tableinst, v_tabletype))*{v_tableinst <- tableinst_lst, v_tabletype <- tabletype_lst}
    -- if (|funcinst_lst| = |functype_lst|)
    -- (Funcinst_ok: `%|-%:%`(s, v_funcinst, v_functype))*{v_funcinst <- funcinst_lst, v_functype <- functype_lst}
    -- if (s = {FUNCS funcinst_lst, GLOBALS globalinst_lst, TABLES tableinst_lst, MEMS meminst_lst})
    -- wf_store: `%`(s)
    -- (wf_limits: `%`(v_memtype))*{v_memtype <- memtype_lst}
    -- (wf_limits: `%`(v_tabletype))*{v_tabletype <- tabletype_lst}
    -- wf_store: `%`({FUNCS funcinst_lst, GLOBALS globalinst_lst, TABLES tableinst_lst, MEMS meminst_lst})

;; test.spectec:2599.1-2599.54
relation Extend_globalinst: `%<=%`(globalinst, globalinst)
  ;; test.spectec:2605.1-2607.32
  rule mk_Extend_globalinst{v_mut : mut, t : valtype, v_val : val, val' : val}:
    `%<=%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val}, {TYPE mk_globaltype_globaltype(v_mut, t), VALUE val'})
    -- if ((v_mut = ?(MUT_r_MUT)) \/ (v_val = val'))
    -- wf_globalinst: `%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE v_val})
    -- wf_globalinst: `%`({TYPE mk_globaltype_globaltype(v_mut, t), VALUE val'})

;; test.spectec:2600.1-2600.45
relation Extend_meminst: `%<=%`(meminst, meminst)
  ;; test.spectec:2609.1-2612.22
  rule mk_Extend_meminst{v_n : n, m_opt : m?, b_lst : byte*, n' : n, b'_lst : byte*}:
    `%<=%`({TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst}, {TYPE mk_limits_memtype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b'_lst})
    -- if (v_n <= n')
    -- if (|b_lst| <= |b'_lst|)
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b_lst})
    -- wf_meminst: `%`({TYPE mk_limits_memtype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), BYTES b'_lst})

;; test.spectec:2601.1-2601.51
relation Extend_tableinst: `%<=%`(tableinst, tableinst)
  ;; test.spectec:2614.1-2617.26
  rule mk_Extend_tableinst{v_n : n, m_opt : m?, ref_lst : funcaddr*, n' : n, ref'_lst : funcaddr*}:
    `%<=%`({TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref)*{ref <- ref_lst}}, {TYPE mk_limits_tabletype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref')*{ref' <- ref'_lst}})
    -- if (v_n <= n')
    -- if (|ref_lst| <= |ref'_lst|)
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(v_n), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref)*{ref <- ref_lst}})
    -- wf_tableinst: `%`({TYPE mk_limits_tabletype(mk_uN_u32(n'), mk_uN_u32(v_m)?{v_m <- m_opt}), REFS ?(ref')*{ref' <- ref'_lst}})

;; test.spectec:2602.1-2602.48
relation Extend_funcinst: `%<=%`(funcinst, funcinst)
  ;; test.spectec:2619.1-2620.66
  rule mk_Extend_funcinst{ft : functype, mm : moduleinst, fc : func}:
    `%<=%`({TYPE ft, MODULE mm, CODE fc}, {TYPE ft, MODULE mm, CODE fc})
    -- wf_funcinst: `%`({TYPE ft, MODULE mm, CODE fc})

;; test.spectec:2603.1-2603.39
relation Extend_store: `%<=%`(store, store)
  ;; test.spectec:2622.1-2627.66
  rule mk_Extend_store{s : store, s' : store}:
    `%<=%`(s, s')
    -- (if (a < |s.GLOBALS_store|))^(a<|s.GLOBALS_store|){}
    -- (if (a < |s'.GLOBALS_store|))^(a<|s.GLOBALS_store|){}
    -- (Extend_globalinst: `%<=%`(s.GLOBALS_store[a], s'.GLOBALS_store[a]))^(a<|s.GLOBALS_store|){}
    -- (if (a < |s.MEMS_store|))^(a<|s.MEMS_store|){}
    -- (if (a < |s'.MEMS_store|))^(a<|s.MEMS_store|){}
    -- (Extend_meminst: `%<=%`(s.MEMS_store[a], s'.MEMS_store[a]))^(a<|s.MEMS_store|){}
    -- (if (a < |s.TABLES_store|))^(a<|s.TABLES_store|){}
    -- (if (a < |s'.TABLES_store|))^(a<|s.TABLES_store|){}
    -- (Extend_tableinst: `%<=%`(s.TABLES_store[a], s'.TABLES_store[a]))^(a<|s.TABLES_store|){}
    -- (if (a < |s.FUNCS_store|))^(a<|s.FUNCS_store|){}
    -- (if (a < |s'.FUNCS_store|))^(a<|s.FUNCS_store|){}
    -- (Extend_funcinst: `%<=%`(s.FUNCS_store[a], s'.FUNCS_store[a]))^(a<|s.FUNCS_store|){}
    -- wf_store: `%`(s)
    -- wf_store: `%`(s')

;; test.spectec:2632.1-2632.38
relation State_ok: `|-%:%`(state, context)
  ;; test.spectec:2640.1-2643.26
  rule mk_State_ok{s : store, f : frame, C : context}:
    `|-%:%`(mk_state_state(s, f), C)
    -- Store_ok: `|-%:OK`(s)
    -- Frame_ok: `%|-%:%`(s, f, C)
    -- wf_context: `%`(C)
    -- wf_state: `%`(mk_state_state(s, f))

;; test.spectec:2633.1-2633.43
relation Config_ok: `|-%:%`(config, resulttype)
  ;; test.spectec:2645.1-2648.40
  rule mk_Config_ok{s : store, f : frame, admininstr_lst : admininstr*, t_opt : valtype?, C : context}:
    `|-%:%`(mk_config_config(mk_state_state(s, f), admininstr_lst), t_opt)
    -- State_ok: `|-%:%`(mk_state_state(s, f), C)
    -- Expr_ok2: `%;%|-%:%`(s, C, admininstr_lst, t_opt)
    -- wf_context: `%`(C)
    -- wf_config: `%`(mk_config_config(mk_state_state(s, f), admininstr_lst))
    -- wf_state: `%`(mk_state_state(s, f))

;; test.spectec:1874.1-1874.41
grammar Bbyte : byte
  ;; test.spectec:1874.24-1874.41
  prod{`<implicit_prod_result>` : nat} `<implicit_prod_result>`:(0x00 | ... | 0xFF) => mk_byte_byte(`<implicit_prod_result>`)

;; test.spectec:1876.1-1878.82
rec {

;; test.spectec:1876.1-1878.82
grammar BuN(v_N : N) : uN
  ;; test.spectec:1877.5-1877.83
  prod{v_n : n} mk_byte_byte(v_n):Bbyte => mk_uN_uN(v_n)
    -- if ((v_n < (2 ^ 7)) /\ (v_n < (2 ^ v_N)))
  ;; test.spectec:1878.5-1878.82
  prod{v_m : m, v_n : n} {{mk_byte_byte(v_n):Bbyte} {mk_uN_uN(v_m):BuN((((v_N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => mk_uN_uN((((2 ^ 7) * v_m) + (((v_n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)))
    -- if ((v_n >= (2 ^ 7)) /\ (v_N > 7))
}

;; test.spectec:1893.1-1893.29
grammar Bu32 : u32
  ;; test.spectec:1893.22-1893.29
  prod{`<implicit_prod_result>` : uN} `<implicit_prod_result>`:BuN(32) => `<implicit_prod_result>`

;; test.spectec:1863.1-1864.29
grammar Blist(syntax el, grammar BX : el) : el*
  ;; test.spectec:1864.5-1864.29
  prod{v_n : n, el_lst : el*} {{mk_uN_u32(v_n):Bu32} {el:BX^v_n{el <- el_lst}}} => el_lst

;; test.spectec:1880.1-1883.82
rec {

;; test.spectec:1880.1-1883.82
grammar BsN(v_N : N) : sN
  ;; test.spectec:1881.5-1881.87
  prod{v_n : n} mk_byte_byte(v_n):Bbyte => mk_sN_sN((v_n : nat <:> int))
    -- if ((v_n < (2 ^ 6)) /\ (v_n < (2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat))))
  ;; test.spectec:1882.5-1882.101
  prod{v_n : n} mk_byte_byte(v_n):Bbyte => mk_sN_sN(((v_n : nat <:> int) - ((2 ^ 7) : nat <:> int)))
    -- if ((((2 ^ 6) <= v_n) /\ (v_n < (2 ^ 7))) /\ ((v_n : nat <:> int) >= (((2 ^ 7) : nat <:> int) - ((2 ^ (((v_N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int))))
  ;; test.spectec:1883.5-1883.82
  prod{i : sN, v_n : n} {{mk_byte_byte(v_n):Bbyte} {i:BsN((((v_N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => mk_sN_sN(((((2 ^ 7) * ($proj_sN_0(i).0 : int <:> nat)) + (((v_n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)) : nat <:> int))
    -- if ((v_n >= (2 ^ 7)) /\ (v_N > 7))
}

;; test.spectec:1885.1-1886.50
grammar BiN(v_N : N) : iN
  ;; test.spectec:1886.5-1886.50
  prod{i : sN, var_0 : nat} i:BsN(v_N) => mk_uN_iN(var_0)
    -- fun_inv_signed_: `%%%`(v_N, $proj_sN_0(i).0, var_0)

;; test.spectec:1889.1-1890.43
grammar BfN(v_N : N) : fN
  ;; test.spectec:1890.5-1890.43
  prod{b_lst : byte*} b_lst:Bbyte^(((v_N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat){} => $inv_fbytes_(v_N, b_lst)

;; test.spectec:1894.1-1894.29
grammar Bu64 : u64
  ;; test.spectec:1894.22-1894.29
  prod{`<implicit_prod_result>` : uN} `<implicit_prod_result>`:BuN(64) => `<implicit_prod_result>`

;; test.spectec:1896.1-1896.29
grammar Bi32 : i32
  ;; test.spectec:1896.22-1896.29
  prod{`<implicit_prod_result>` : iN} `<implicit_prod_result>`:BiN(32) => `<implicit_prod_result>`

;; test.spectec:1897.1-1897.29
grammar Bi64 : i64
  ;; test.spectec:1897.22-1897.29
  prod{`<implicit_prod_result>` : iN} `<implicit_prod_result>`:BiN(64) => `<implicit_prod_result>`

;; test.spectec:1899.1-1899.29
grammar Bf32 : f32
  ;; test.spectec:1899.22-1899.29
  prod{`<implicit_prod_result>` : fN} `<implicit_prod_result>`:BfN(32) => `<implicit_prod_result>`

;; test.spectec:1900.1-1900.29
grammar Bf64 : f64
  ;; test.spectec:1900.22-1900.29
  prod{`<implicit_prod_result>` : fN} `<implicit_prod_result>`:BfN(64) => `<implicit_prod_result>`

;; test.spectec:1914.1-1915.52
grammar Bname : name
  ;; test.spectec:1915.5-1915.52
  prod{v_name : name, b_lst : byte*, var_0 : byte*} b_lst:Blist(syntax byte, grammar Bbyte) => v_name
    -- fun_utf8: `%%`($proj_name_0(v_name).0, var_0)
    -- if (var_0 = b_lst)

;; test.spectec:1920.1-1920.41
grammar Btypeidx : typeidx
  ;; test.spectec:1920.30-1920.41
  prod{x : idx} x:Bu32 => x

;; test.spectec:1921.1-1921.41
grammar Bfuncidx : funcidx
  ;; test.spectec:1921.30-1921.41
  prod{x : idx} x:Bu32 => x

;; test.spectec:1922.1-1922.45
grammar Bglobalidx : globalidx
  ;; test.spectec:1922.34-1922.45
  prod{x : idx} x:Bu32 => x

;; test.spectec:1923.1-1923.43
grammar Btableidx : tableidx
  ;; test.spectec:1923.32-1923.43
  prod{x : idx} x:Bu32 => x

;; test.spectec:1924.1-1924.39
grammar Bmemidx : memidx
  ;; test.spectec:1924.28-1924.39
  prod{x : idx} x:Bu32 => x

;; test.spectec:1925.1-1925.43
grammar Blocalidx : localidx
  ;; test.spectec:1925.32-1925.43
  prod{x : idx} x:Bu32 => x

;; test.spectec:1926.1-1926.43
grammar Blabelidx : labelidx
  ;; test.spectec:1926.32-1926.43
  prod{x : idx} x:Bu32 => x

;; test.spectec:1928.1-1932.34
grammar Bexternidx : externidx
  ;; test.spectec:1929.5-1929.30
  prod{x : idx} {{0x00} {x:Bfuncidx}} => FUNC_externidx(x)
  ;; test.spectec:1930.5-1930.32
  prod{x : idx} {{0x01} {x:Btableidx}} => TABLE_externidx(x)
  ;; test.spectec:1931.5-1931.28
  prod{x : idx} {{0x02} {x:Bmemidx}} => MEM_externidx(x)
  ;; test.spectec:1932.5-1932.34
  prod{x : idx} {{0x03} {x:Bglobalidx}} => GLOBAL_externidx(x)

;; test.spectec:1941.1-1945.16
grammar Bvaltype : valtype
  ;; test.spectec:1942.5-1942.16
  prod 0x7F => I32_valtype
  ;; test.spectec:1943.5-1943.16
  prod 0x7E => I64_valtype
  ;; test.spectec:1944.5-1944.16
  prod 0x7D => F32_valtype
  ;; test.spectec:1945.5-1945.16
  prod 0x7C => F64_valtype

;; test.spectec:1948.1-1949.29
grammar Bresulttype : valtype*
  ;; test.spectec:1949.5-1949.29
  prod{t_lst : valtype*} t_lst:Blist(syntax valtype, grammar Bvaltype) => t_lst

;; test.spectec:1954.1-1955.59
grammar Bfunctype : functype
  ;; test.spectec:1955.5-1955.59
  prod{t_1_lst : valtype*, t_2_lst : valtype*} {{0x60} {t_1_lst:Bresulttype} {t_2_lst:Bresulttype}} => mk_functype_functype(t_1_lst, t_2_lst)

;; test.spectec:1960.1-1962.16
grammar Bmut : mut
  ;; test.spectec:1961.5-1961.16
  prod 0x00 => ?()
  ;; test.spectec:1962.5-1962.16
  prod 0x01 => ?(MUT_r_MUT)

;; test.spectec:1964.1-1966.36
grammar Blimits : limits
  ;; test.spectec:1965.5-1965.31
  prod{v_n : n} {{0x00} {mk_uN_u32(v_n):Bu32}} => mk_limits_limits(mk_uN_u32(v_n), ?())
  ;; test.spectec:1966.5-1966.36
  prod{v_n : n, v_m : m} {{0x01} {mk_uN_u32(v_n):Bu32} {mk_uN_u32(v_m):Bu32}} => mk_limits_limits(mk_uN_u32(v_n), ?(mk_uN_u32(v_m)))

;; test.spectec:1968.1-1969.33
grammar Bglobaltype : globaltype
  ;; test.spectec:1969.5-1969.33
  prod{v_mut : mut, t : valtype} {{t:Bvaltype} {v_mut:Bmut}} => mk_globaltype_globaltype(v_mut, t)

;; test.spectec:1971.1-1972.28
grammar Btabletype : tabletype
  ;; test.spectec:1972.5-1972.28
  prod{lim : limits} {{0x70} {lim:Blimits}} => lim

;; test.spectec:1974.1-1975.23
grammar Bmemtype : memtype
  ;; test.spectec:1975.5-1975.23
  prod{lim : limits} lim:Blimits => lim

;; test.spectec:1978.1-1982.37
grammar Bexterntype : externtype
  ;; test.spectec:1979.5-1979.33
  prod{ft : functype} {{0x00} {ft:Bfunctype}} => FUNC_externtype(ft)
  ;; test.spectec:1980.5-1980.35
  prod{tt : tabletype} {{0x01} {tt:Btabletype}} => TABLE_externtype(tt)
  ;; test.spectec:1981.5-1981.31
  prod{mt : memtype} {{0x02} {mt:Bmemtype}} => MEM_externtype(mt)
  ;; test.spectec:1982.5-1982.37
  prod{gt : globaltype} {{0x03} {gt:Bglobaltype}} => GLOBAL_externtype(gt)

;; test.spectec:1991.1-1993.20
grammar Bblocktype : blocktype
  ;; test.spectec:1992.5-1992.16
  prod 0x40 => ?()
  ;; test.spectec:1993.5-1993.20
  prod{t : valtype} t:Bvaltype => ?(t)

;; test.spectec:2035.1-2036.41
grammar Bmemarg : memarg
  ;; test.spectec:2036.5-2036.41
  prod{v_n : n, v_m : m} {{mk_uN_u32(v_n):Bu32} {mk_uN_u32(v_m):Bu32}} => {ALIGN mk_uN_u32(v_n), OFFSET mk_uN_u32(v_m)}

;; test.spectec:2217.1-2242.38
rec {

;; test.spectec:2217.1-2242.38
grammar Binstr : instr
  ;; test.spectec:1999.5-1999.24
  prod 0x00 => UNREACHABLE_instr
  ;; test.spectec:2000.5-2000.16
  prod 0x01 => NOP_instr
  ;; test.spectec:2001.5-2001.57
  prod{bt : blocktype, in_lst : instr*} {{0x02} {bt:Bblocktype} {in:Binstr*{in <- in_lst}} {0x0B}} => BLOCK_instr(bt, in_lst)
  ;; test.spectec:2002.5-2002.56
  prod{bt : blocktype, in_lst : instr*} {{0x03} {bt:Bblocktype} {in:Binstr*{in <- in_lst}} {0x0B}} => LOOP_instr(bt, in_lst)
  ;; test.spectec:2003.5-2003.63
  prod{bt : blocktype, in_lst : instr*} {{0x04} {bt:Bblocktype} {in:Binstr*{in <- in_lst}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_lst, [])
  ;; test.spectec:2004.5-2004.89
  prod{bt : blocktype, in_1_lst : instr*, in_2_lst : instr*} {{0x04} {bt:Bblocktype} {in_1:Binstr*{in_1 <- in_1_lst}} {0x05} {in_2:Binstr*{in_2 <- in_2_lst}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_1_lst, in_2_lst)
  ;; test.spectec:2005.5-2005.29
  prod{l : labelidx} {{0x0C} {l:Blabelidx}} => BR_instr(l)
  ;; test.spectec:2006.5-2006.32
  prod{l : labelidx} {{0x0D} {l:Blabelidx}} => BR_IF_instr(l)
  ;; test.spectec:2007.5-2007.62
  prod{l_lst : labelidx*, l_N : labelidx} {{0x0E} {l_lst:Blist(syntax labelidx, grammar Blabelidx)} {l_N:Blabelidx}} => BR_TABLE_instr(l_lst, l_N)
  ;; test.spectec:2008.5-2008.19
  prod 0x0F => RETURN_instr
  ;; test.spectec:2009.5-2009.30
  prod{x : idx} {{0x10} {x:Bfuncidx}} => CALL_instr(x)
  ;; test.spectec:2010.5-2010.44
  prod{x : idx} {{0x11} {x:Btypeidx} {0x00}} => CALL_INDIRECT_instr(x)
  ;; test.spectec:2017.5-2017.17
  prod 0x1A => DROP_instr
  ;; test.spectec:2018.5-2018.19
  prod 0x1B => SELECT_instr
  ;; test.spectec:2025.5-2025.36
  prod{x : idx} {{0x20} {x:Blocalidx}} => LOCAL_GET_instr(x)
  ;; test.spectec:2026.5-2026.36
  prod{x : idx} {{0x21} {x:Blocalidx}} => LOCAL_SET_instr(x)
  ;; test.spectec:2027.5-2027.36
  prod{x : idx} {{0x22} {x:Blocalidx}} => LOCAL_TEE_instr(x)
  ;; test.spectec:2028.5-2028.38
  prod{x : idx} {{0x23} {x:Bglobalidx}} => GLOBAL_GET_instr(x)
  ;; test.spectec:2029.5-2029.38
  prod{x : idx} {{0x24} {x:Bglobalidx}} => GLOBAL_SET_instr(x)
  ;; test.spectec:2039.5-2039.35
  prod{ao : memarg} {{0x28} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(), ao)
  ;; test.spectec:2040.5-2040.35
  prod{ao : memarg} {{0x29} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(), ao)
  ;; test.spectec:2041.5-2041.35
  prod{ao : memarg} {{0x2A} {ao:Bmemarg}} => LOAD_instr(F32_valtype, ?(), ao)
  ;; test.spectec:2042.5-2042.35
  prod{ao : memarg} {{0x2B} {ao:Bmemarg}} => LOAD_instr(F64_valtype, ?(), ao)
  ;; test.spectec:2043.5-2043.43
  prod{ao : memarg} {{0x2C} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), S_sx))), ao)
  ;; test.spectec:2044.5-2044.43
  prod{ao : memarg} {{0x2D} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), U_sx))), ao)
  ;; test.spectec:2045.5-2045.44
  prod{ao : memarg} {{0x2E} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), S_sx))), ao)
  ;; test.spectec:2046.5-2046.44
  prod{ao : memarg} {{0x2F} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), U_sx))), ao)
  ;; test.spectec:2047.5-2047.43
  prod{ao : memarg} {{0x30} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), S_sx))), ao)
  ;; test.spectec:2048.5-2048.43
  prod{ao : memarg} {{0x31} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(8), U_sx))), ao)
  ;; test.spectec:2049.5-2049.44
  prod{ao : memarg} {{0x32} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), S_sx))), ao)
  ;; test.spectec:2050.5-2050.44
  prod{ao : memarg} {{0x33} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(16), U_sx))), ao)
  ;; test.spectec:2051.5-2051.44
  prod{ao : memarg} {{0x34} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(32), S_sx))), ao)
  ;; test.spectec:2052.5-2052.44
  prod{ao : memarg} {{0x35} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, mk_loadop_Inn_loadop_Inn(mk_sz_sz(32), U_sx))), ao)
  ;; test.spectec:2053.5-2053.36
  prod{ao : memarg} {{0x36} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(), ao)
  ;; test.spectec:2054.5-2054.36
  prod{ao : memarg} {{0x37} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(), ao)
  ;; test.spectec:2055.5-2055.36
  prod{ao : memarg} {{0x38} {ao:Bmemarg}} => STORE_instr(F32_valtype, ?(), ao)
  ;; test.spectec:2056.5-2056.36
  prod{ao : memarg} {{0x39} {ao:Bmemarg}} => STORE_instr(F64_valtype, ?(), ao)
  ;; test.spectec:2057.5-2057.38
  prod{ao : memarg} {{0x3A} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(mk_sz_sz(8)), ao)
  ;; test.spectec:2058.5-2058.39
  prod{ao : memarg} {{0x3B} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(mk_sz_sz(16)), ao)
  ;; test.spectec:2059.5-2059.38
  prod{ao : memarg} {{0x3C} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(mk_sz_sz(8)), ao)
  ;; test.spectec:2060.5-2060.39
  prod{ao : memarg} {{0x3D} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(mk_sz_sz(16)), ao)
  ;; test.spectec:2061.5-2061.39
  prod{ao : memarg} {{0x3E} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(mk_sz_sz(32)), ao)
  ;; test.spectec:2062.5-2062.29
  prod {{0x3F} {0x00}} => MEMORY_SIZE_instr
  ;; test.spectec:2063.5-2063.29
  prod {{0x40} {0x00}} => MEMORY_GROW_instr
  ;; test.spectec:2071.5-2071.31
  prod{i : i32} {{0x41} {i:Bi32}} => CONST_instr(I32_valtype, mk_val__0_val_(I32_Inn, i))
  ;; test.spectec:2072.5-2072.31
  prod{i : i64} {{0x42} {i:Bi64}} => CONST_instr(I64_valtype, mk_val__0_val_(I64_Inn, i))
  ;; test.spectec:2073.5-2073.31
  prod{p : f32} {{0x43} {p:Bf32}} => CONST_instr(F32_valtype, mk_val__1_val_(F32_Fnn, p))
  ;; test.spectec:2074.5-2074.31
  prod{p : f64} {{0x44} {p:Bf64}} => CONST_instr(F64_valtype, mk_val__1_val_(F64_Fnn, p))
  ;; test.spectec:2078.5-2078.27
  prod 0x45 => TESTOP_instr(I32_valtype, mk_testop__0_testop_(I32_Inn, EQZ_testop_Inn))
  ;; test.spectec:2082.5-2082.25
  prod 0x46 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, EQ_relop_Inn))
  ;; test.spectec:2083.5-2083.25
  prod 0x47 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, NE_relop_Inn))
  ;; test.spectec:2084.5-2084.29
  prod 0x48 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(S_sx)))
  ;; test.spectec:2085.5-2085.29
  prod 0x49 => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LT_relop_Inn(U_sx)))
  ;; test.spectec:2086.5-2086.29
  prod 0x4A => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(S_sx)))
  ;; test.spectec:2087.5-2087.29
  prod 0x4B => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GT_relop_Inn(U_sx)))
  ;; test.spectec:2088.5-2088.29
  prod 0x4C => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(S_sx)))
  ;; test.spectec:2089.5-2089.29
  prod 0x4D => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, LE_relop_Inn(U_sx)))
  ;; test.spectec:2090.5-2090.29
  prod 0x4E => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(S_sx)))
  ;; test.spectec:2091.5-2091.29
  prod 0x4F => RELOP_instr(I32_valtype, mk_relop__0_relop_(I32_Inn, GE_relop_Inn(U_sx)))
  ;; test.spectec:2095.5-2095.27
  prod 0x50 => TESTOP_instr(I64_valtype, mk_testop__0_testop_(I64_Inn, EQZ_testop_Inn))
  ;; test.spectec:2099.5-2099.25
  prod 0x51 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, EQ_relop_Inn))
  ;; test.spectec:2100.5-2100.25
  prod 0x52 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, NE_relop_Inn))
  ;; test.spectec:2101.5-2101.29
  prod 0x53 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(S_sx)))
  ;; test.spectec:2102.5-2102.29
  prod 0x54 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LT_relop_Inn(U_sx)))
  ;; test.spectec:2103.5-2103.29
  prod 0x55 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(S_sx)))
  ;; test.spectec:2104.5-2104.29
  prod 0x56 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GT_relop_Inn(U_sx)))
  ;; test.spectec:2105.5-2105.29
  prod 0x57 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(S_sx)))
  ;; test.spectec:2106.5-2106.29
  prod 0x58 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, LE_relop_Inn(U_sx)))
  ;; test.spectec:2107.5-2107.29
  prod 0x59 => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(S_sx)))
  ;; test.spectec:2108.5-2108.29
  prod 0x5A => RELOP_instr(I64_valtype, mk_relop__0_relop_(I64_Inn, GE_relop_Inn(U_sx)))
  ;; test.spectec:2112.5-2112.25
  prod 0x5B => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, EQ_relop_Fnn))
  ;; test.spectec:2113.5-2113.25
  prod 0x5C => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, NE_relop_Fnn))
  ;; test.spectec:2114.5-2114.25
  prod 0x5D => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, LT_relop_Fnn))
  ;; test.spectec:2115.5-2115.25
  prod 0x5E => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, GT_relop_Fnn))
  ;; test.spectec:2116.5-2116.25
  prod 0x5F => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, LE_relop_Fnn))
  ;; test.spectec:2117.5-2117.25
  prod 0x60 => RELOP_instr(F32_valtype, mk_relop__1_relop_(F32_Fnn, GE_relop_Fnn))
  ;; test.spectec:2121.5-2121.25
  prod 0x61 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, EQ_relop_Fnn))
  ;; test.spectec:2122.5-2122.25
  prod 0x62 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, NE_relop_Fnn))
  ;; test.spectec:2123.5-2123.25
  prod 0x63 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, LT_relop_Fnn))
  ;; test.spectec:2124.5-2124.25
  prod 0x64 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, GT_relop_Fnn))
  ;; test.spectec:2125.5-2125.25
  prod 0x65 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, LE_relop_Fnn))
  ;; test.spectec:2126.5-2126.25
  prod 0x66 => RELOP_instr(F64_valtype, mk_relop__1_relop_(F64_Fnn, GE_relop_Fnn))
  ;; test.spectec:2130.5-2130.25
  prod 0x67 => UNOP_instr(I32_valtype, mk_unop__0_unop_(I32_Inn, CLZ_unop_Inn))
  ;; test.spectec:2131.5-2131.25
  prod 0x68 => UNOP_instr(I32_valtype, mk_unop__0_unop_(I32_Inn, CTZ_unop_Inn))
  ;; test.spectec:2132.5-2132.28
  prod 0x69 => UNOP_instr(I32_valtype, mk_unop__0_unop_(I32_Inn, POPCNT_unop_Inn))
  ;; test.spectec:2136.5-2136.26
  prod 0x6A => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, ADD_binop_Inn))
  ;; test.spectec:2137.5-2137.26
  prod 0x6B => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SUB_binop_Inn))
  ;; test.spectec:2138.5-2138.26
  prod 0x6C => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, MUL_binop_Inn))
  ;; test.spectec:2139.5-2139.30
  prod 0x6D => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(S_sx)))
  ;; test.spectec:2140.5-2140.30
  prod 0x6E => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, DIV_binop_Inn(U_sx)))
  ;; test.spectec:2141.5-2141.30
  prod 0x6F => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(S_sx)))
  ;; test.spectec:2142.5-2142.30
  prod 0x70 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, REM_binop_Inn(U_sx)))
  ;; test.spectec:2143.5-2143.26
  prod 0x71 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, AND_binop_Inn))
  ;; test.spectec:2144.5-2144.25
  prod 0x72 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, OR_binop_Inn))
  ;; test.spectec:2145.5-2145.26
  prod 0x73 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, XOR_binop_Inn))
  ;; test.spectec:2146.5-2146.26
  prod 0x74 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SHL_binop_Inn))
  ;; test.spectec:2147.5-2147.30
  prod 0x75 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(S_sx)))
  ;; test.spectec:2148.5-2148.30
  prod 0x76 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, SHR_binop_Inn(U_sx)))
  ;; test.spectec:2149.5-2149.27
  prod 0x77 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTL_binop_Inn))
  ;; test.spectec:2150.5-2150.27
  prod 0x78 => BINOP_instr(I32_valtype, mk_binop__0_binop_(I32_Inn, ROTR_binop_Inn))
  ;; test.spectec:2154.5-2154.25
  prod 0x79 => UNOP_instr(I64_valtype, mk_unop__0_unop_(I64_Inn, CLZ_unop_Inn))
  ;; test.spectec:2155.5-2155.25
  prod 0x7A => UNOP_instr(I64_valtype, mk_unop__0_unop_(I64_Inn, CTZ_unop_Inn))
  ;; test.spectec:2156.5-2156.28
  prod 0x7B => UNOP_instr(I64_valtype, mk_unop__0_unop_(I64_Inn, POPCNT_unop_Inn))
  ;; test.spectec:2160.5-2160.26
  prod 0x7C => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, ADD_binop_Inn))
  ;; test.spectec:2161.5-2161.26
  prod 0x7D => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SUB_binop_Inn))
  ;; test.spectec:2162.5-2162.26
  prod 0x7E => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, MUL_binop_Inn))
  ;; test.spectec:2163.5-2163.30
  prod 0x7F => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(S_sx)))
  ;; test.spectec:2164.5-2164.30
  prod 0x80 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, DIV_binop_Inn(U_sx)))
  ;; test.spectec:2165.5-2165.30
  prod 0x81 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(S_sx)))
  ;; test.spectec:2166.5-2166.30
  prod 0x82 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, REM_binop_Inn(U_sx)))
  ;; test.spectec:2167.5-2167.26
  prod 0x83 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, AND_binop_Inn))
  ;; test.spectec:2168.5-2168.25
  prod 0x84 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, OR_binop_Inn))
  ;; test.spectec:2169.5-2169.26
  prod 0x85 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, XOR_binop_Inn))
  ;; test.spectec:2170.5-2170.26
  prod 0x86 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SHL_binop_Inn))
  ;; test.spectec:2171.5-2171.30
  prod 0x87 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(S_sx)))
  ;; test.spectec:2172.5-2172.30
  prod 0x88 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, SHR_binop_Inn(U_sx)))
  ;; test.spectec:2173.5-2173.27
  prod 0x89 => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTL_binop_Inn))
  ;; test.spectec:2174.5-2174.27
  prod 0x8A => BINOP_instr(I64_valtype, mk_binop__0_binop_(I64_Inn, ROTR_binop_Inn))
  ;; test.spectec:2178.5-2178.25
  prod 0x8B => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, ABS_unop_Fnn))
  ;; test.spectec:2179.5-2179.25
  prod 0x8C => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEG_unop_Fnn))
  ;; test.spectec:2180.5-2180.26
  prod 0x8D => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, CEIL_unop_Fnn))
  ;; test.spectec:2181.5-2181.27
  prod 0x8E => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, FLOOR_unop_Fnn))
  ;; test.spectec:2182.5-2182.27
  prod 0x8F => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, TRUNC_unop_Fnn))
  ;; test.spectec:2183.5-2183.29
  prod 0x90 => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, NEAREST_unop_Fnn))
  ;; test.spectec:2184.5-2184.26
  prod 0x91 => UNOP_instr(F32_valtype, mk_unop__1_unop_(F32_Fnn, SQRT_unop_Fnn))
  ;; test.spectec:2188.5-2188.26
  prod 0x92 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, ADD_binop_Fnn))
  ;; test.spectec:2189.5-2189.26
  prod 0x93 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, SUB_binop_Fnn))
  ;; test.spectec:2190.5-2190.26
  prod 0x94 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, MUL_binop_Fnn))
  ;; test.spectec:2191.5-2191.26
  prod 0x95 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, DIV_binop_Fnn))
  ;; test.spectec:2192.5-2192.26
  prod 0x96 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, MIN_binop_Fnn))
  ;; test.spectec:2193.5-2193.26
  prod 0x97 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, MAX_binop_Fnn))
  ;; test.spectec:2194.5-2194.31
  prod 0x98 => BINOP_instr(F32_valtype, mk_binop__1_binop_(F32_Fnn, COPYSIGN_binop_Fnn))
  ;; test.spectec:2198.5-2198.25
  prod 0x99 => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, ABS_unop_Fnn))
  ;; test.spectec:2199.5-2199.25
  prod 0x9A => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEG_unop_Fnn))
  ;; test.spectec:2200.5-2200.26
  prod 0x9B => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, CEIL_unop_Fnn))
  ;; test.spectec:2201.5-2201.27
  prod 0x9C => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, FLOOR_unop_Fnn))
  ;; test.spectec:2202.5-2202.27
  prod 0x9D => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, TRUNC_unop_Fnn))
  ;; test.spectec:2203.5-2203.29
  prod 0x9E => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, NEAREST_unop_Fnn))
  ;; test.spectec:2204.5-2204.26
  prod 0x9F => UNOP_instr(F64_valtype, mk_unop__1_unop_(F64_Fnn, SQRT_unop_Fnn))
  ;; test.spectec:2208.5-2208.26
  prod 0xA0 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, ADD_binop_Fnn))
  ;; test.spectec:2209.5-2209.26
  prod 0xA1 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, SUB_binop_Fnn))
  ;; test.spectec:2210.5-2210.26
  prod 0xA2 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, MUL_binop_Fnn))
  ;; test.spectec:2211.5-2211.26
  prod 0xA3 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, DIV_binop_Fnn))
  ;; test.spectec:2212.5-2212.26
  prod 0xA4 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, MIN_binop_Fnn))
  ;; test.spectec:2213.5-2213.26
  prod 0xA5 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, MAX_binop_Fnn))
  ;; test.spectec:2214.5-2214.31
  prod 0xA6 => BINOP_instr(F64_valtype, mk_binop__1_binop_(F64_Fnn, COPYSIGN_binop_Fnn))
  ;; test.spectec:2218.5-2218.31
  prod 0xA7 => CVTOP_instr(I32_valtype, I64_valtype, WRAP_cvtop)
  ;; test.spectec:2219.5-2219.36
  prod 0xA8 => CVTOP_instr(I32_valtype, F32_valtype, TRUNC_cvtop(S_sx))
  ;; test.spectec:2220.5-2220.36
  prod 0xA9 => CVTOP_instr(I32_valtype, F32_valtype, TRUNC_cvtop(U_sx))
  ;; test.spectec:2221.5-2221.36
  prod 0xAA => CVTOP_instr(I32_valtype, F64_valtype, TRUNC_cvtop(S_sx))
  ;; test.spectec:2222.5-2222.36
  prod 0xAB => CVTOP_instr(I32_valtype, F64_valtype, TRUNC_cvtop(U_sx))
  ;; test.spectec:2223.5-2223.37
  prod 0xAC => CVTOP_instr(I64_valtype, I32_valtype, EXTEND_cvtop(S_sx))
  ;; test.spectec:2224.5-2224.37
  prod 0xAD => CVTOP_instr(I64_valtype, I32_valtype, EXTEND_cvtop(U_sx))
  ;; test.spectec:2225.5-2225.36
  prod 0xAE => CVTOP_instr(I64_valtype, F32_valtype, TRUNC_cvtop(S_sx))
  ;; test.spectec:2226.5-2226.36
  prod 0xAF => CVTOP_instr(I64_valtype, F32_valtype, TRUNC_cvtop(U_sx))
  ;; test.spectec:2227.5-2227.36
  prod 0xB0 => CVTOP_instr(I64_valtype, F64_valtype, TRUNC_cvtop(S_sx))
  ;; test.spectec:2228.5-2228.36
  prod 0xB1 => CVTOP_instr(I64_valtype, F64_valtype, TRUNC_cvtop(U_sx))
  ;; test.spectec:2229.5-2229.38
  prod 0xB2 => CVTOP_instr(F32_valtype, I32_valtype, CONVERT_cvtop(S_sx))
  ;; test.spectec:2230.5-2230.38
  prod 0xB3 => CVTOP_instr(F32_valtype, I32_valtype, CONVERT_cvtop(U_sx))
  ;; test.spectec:2231.5-2231.38
  prod 0xB4 => CVTOP_instr(F32_valtype, I64_valtype, CONVERT_cvtop(S_sx))
  ;; test.spectec:2232.5-2232.38
  prod 0xB5 => CVTOP_instr(F32_valtype, I64_valtype, CONVERT_cvtop(U_sx))
  ;; test.spectec:2233.5-2233.33
  prod 0xB6 => CVTOP_instr(F32_valtype, F64_valtype, DEMOTE_cvtop)
  ;; test.spectec:2234.5-2234.38
  prod 0xB7 => CVTOP_instr(F64_valtype, I32_valtype, CONVERT_cvtop(S_sx))
  ;; test.spectec:2235.5-2235.38
  prod 0xB8 => CVTOP_instr(F64_valtype, I32_valtype, CONVERT_cvtop(U_sx))
  ;; test.spectec:2236.5-2236.38
  prod 0xB9 => CVTOP_instr(F64_valtype, I64_valtype, CONVERT_cvtop(S_sx))
  ;; test.spectec:2237.5-2237.38
  prod 0xBA => CVTOP_instr(F64_valtype, I64_valtype, CONVERT_cvtop(U_sx))
  ;; test.spectec:2238.5-2238.34
  prod 0xBB => CVTOP_instr(F32_valtype, F64_valtype, PROMOTE_cvtop)
  ;; test.spectec:2239.5-2239.38
  prod 0xBC => CVTOP_instr(I32_valtype, F32_valtype, REINTERPRET_cvtop)
  ;; test.spectec:2240.5-2240.38
  prod 0xBD => CVTOP_instr(I64_valtype, F64_valtype, REINTERPRET_cvtop)
  ;; test.spectec:2241.5-2241.38
  prod 0xBE => CVTOP_instr(F32_valtype, I32_valtype, REINTERPRET_cvtop)
  ;; test.spectec:2242.5-2242.38
  prod 0xBF => CVTOP_instr(F64_valtype, I64_valtype, REINTERPRET_cvtop)
}

;; test.spectec:2247.1-2248.29
grammar Bexpr : expr
  ;; test.spectec:2248.5-2248.29
  prod{in_lst : instr*} {{in:Binstr*{in <- in_lst}} {0x0B}} => in_lst

;; test.spectec:2260.1-2262.15
grammar Bsection_(v_N : N, syntax en, grammar BX : en*) : en*
  ;; test.spectec:2261.5-2261.55
  prod{en_lst : en*, len : nat} {{mk_byte_byte(v_N):Bbyte} {mk_uN_u32(len):Bu32} {en_lst:BX}} => en_lst
    -- if (len = 0)
  ;; test.spectec:2262.5-2262.15
  prod eps => []

;; test.spectec:2267.1-2268.23
grammar Bcustom : ()*
  ;; test.spectec:2268.5-2268.23
  prod {{Bname} {Bbyte*{}}} => []

;; test.spectec:2270.1-2271.32
grammar Bcustomsec : ()
  ;; test.spectec:2271.5-2271.32
  prod Bsection_(0, syntax (), grammar Bcustom) => ((), ()).1

;; test.spectec:2276.1-2277.28
grammar Btype : type
  ;; test.spectec:2277.5-2277.28
  prod{ft : functype} ft:Bfunctype => TYPE_type(ft)

;; test.spectec:2279.1-2280.42
grammar Btypesec : type*
  ;; test.spectec:2280.5-2280.42
  prod{ty_lst : type*} ty_lst:Bsection_(1, syntax type, grammar Blist(syntax type, grammar Btype)) => ty_lst

;; test.spectec:2285.1-2286.64
grammar Bimport : import
  ;; test.spectec:2286.5-2286.64
  prod{nm_1 : name, nm_2 : name, xt : externtype} {{nm_1:Bname} {nm_2:Bname} {xt:Bexterntype}} => IMPORT_import(nm_1, nm_2, xt)

;; test.spectec:2288.1-2289.44
grammar Bimportsec : import*
  ;; test.spectec:2289.5-2289.44
  prod{im_lst : import*} im_lst:Bsection_(2, syntax import, grammar Blist(syntax import, grammar Bimport)) => im_lst

;; test.spectec:2294.1-2295.43
grammar Bfuncsec : typeidx*
  ;; test.spectec:2295.5-2295.43
  prod{x_lst : idx*} x_lst:Bsection_(3, syntax typeidx, grammar Blist(syntax typeidx, grammar Btypeidx)) => x_lst

;; test.spectec:2300.1-2301.30
grammar Btable : table
  ;; test.spectec:2301.5-2301.30
  prod{tt : tabletype} tt:Btabletype => TABLE_table(tt)

;; test.spectec:2303.1-2304.45
grammar Btablesec : table*
  ;; test.spectec:2304.5-2304.45
  prod{tab_lst : table*} tab_lst:Bsection_(4, syntax table, grammar Blist(syntax table, grammar Btable)) => tab_lst

;; test.spectec:2309.1-2310.29
grammar Bmem : mem
  ;; test.spectec:2310.5-2310.29
  prod{mt : memtype} mt:Bmemtype => MEMORY_mem(mt)

;; test.spectec:2312.1-2313.43
grammar Bmemsec : mem*
  ;; test.spectec:2313.5-2313.43
  prod{mem_lst : mem*} mem_lst:Bsection_(5, syntax mem, grammar Blist(syntax mem, grammar Bmem)) => mem_lst

;; test.spectec:2318.1-2319.42
grammar Bglobal : global
  ;; test.spectec:2319.5-2319.42
  prod{gt : globaltype, e : expr} {{gt:Bglobaltype} {e:Bexpr}} => GLOBAL_global(gt, e)

;; test.spectec:2321.1-2322.48
grammar Bglobalsec : global*
  ;; test.spectec:2322.5-2322.48
  prod{glob_lst : global*} glob_lst:Bsection_(6, syntax global, grammar Blist(syntax global, grammar Bglobal)) => glob_lst

;; test.spectec:2327.1-2328.43
grammar Bexport : export
  ;; test.spectec:2328.5-2328.43
  prod{nm : name, xx : externidx} {{nm:Bname} {xx:Bexternidx}} => EXPORT_export(nm, xx)

;; test.spectec:2330.1-2331.44
grammar Bexportsec : export*
  ;; test.spectec:2331.5-2331.44
  prod{ex_lst : export*} ex_lst:Bsection_(7, syntax export, grammar Blist(syntax export, grammar Bexport)) => ex_lst

;; test.spectec:2336.1-2337.28
grammar Bstart : start*
  ;; test.spectec:2337.5-2337.28
  prod{x : idx} x:Bfuncidx => [START_start(x)]

;; test.spectec:2341.1-2342.60
grammar Bstartsec : start?
  ;; test.spectec:2342.5-2342.60
  prod{v_startopt : startopt} v_startopt:Bsection_(8, syntax start, grammar Bstart) => !($opt_(syntax start, v_startopt))

;; test.spectec:2347.1-2348.49
grammar Belem : elem
  ;; test.spectec:2348.5-2348.49
  prod{e : expr, x_lst : idx*} {{0x00} {e:Bexpr} {x_lst:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(e, x_lst)

;; test.spectec:2350.1-2351.46
grammar Belemsec : elem*
  ;; test.spectec:2351.5-2351.46
  prod{elem_lst : elem*} elem_lst:Bsection_(9, syntax elem, grammar Blist(syntax elem, grammar Belem)) => elem_lst

;; test.spectec:2358.1-2359.37
grammar Blocals : local*
  ;; test.spectec:2359.5-2359.37
  prod{t : valtype, v_n : n} {{mk_uN_u32(v_n):Bu32} {t:Bvaltype}} => LOCAL_local(t)^v_n{}

;; test.spectec:2361.1-2362.74
grammar Bfunc : code
  ;; test.spectec:2362.5-2362.74
  prod{local_lst_lst : local**, v_expr : expr} {{local_lst_lst:Blist(syntax local*, grammar Blocals)} {v_expr:Bexpr}} => ($concat_(syntax local, local_lst_lst), v_expr)

;; test.spectec:2364.1-2365.55
grammar Bcode : code
  ;; test.spectec:2365.5-2365.55
  prod{v_code : code, len : nat} {{mk_uN_u32(len):Bu32} {v_code:Bfunc}} => v_code
    -- if (len = 0)

;; test.spectec:2367.1-2368.47
grammar Bcodesec : code*
  ;; test.spectec:2368.5-2368.47
  prod{code_lst : code*} code_lst:Bsection_(10, syntax code, grammar Blist(syntax code, grammar Bcode)) => code_lst

;; test.spectec:2373.1-2374.46
grammar Bdata : data
  ;; test.spectec:2374.5-2374.46
  prod{e : expr, b_lst : byte*} {{0x00} {e:Bexpr} {b_lst:Blist(syntax byte, grammar Bbyte)}} => DATA_data(e, b_lst)

;; test.spectec:2376.1-2377.47
grammar Bdatasec : data*
  ;; test.spectec:2377.5-2377.47
  prod{data_lst : data*} data_lst:Bsection_(11, syntax data, grammar Blist(syntax data, grammar Bdata)) => data_lst

;; test.spectec:2382.1-2397.45
grammar Bmodule : module
  ;; test.spectec:2383.5-2397.45
  prod{type_lst : type*, import_lst : import*, func_lst : func*, global_lst : global*, table_lst : table*, mem_lst : mem*, elem_lst : elem*, data_lst : data*, start_opt : start?, export_lst : export*, typeidx_lst : typeidx*, expr_lst : expr*, local_lst_lst : local**} {{0x00} {0x61} {0x73} {0x6D} {mk_uN_u32(1):Bu32} {Bcustomsec*{}} {type_lst:Btypesec} {Bcustomsec*{}} {import_lst:Bimportsec} {Bcustomsec*{}} {typeidx_lst:Bfuncsec} {Bcustomsec*{}} {table_lst:Btablesec} {Bcustomsec*{}} {mem_lst:Bmemsec} {Bcustomsec*{}} {global_lst:Bglobalsec} {Bcustomsec*{}} {export_lst:Bexportsec} {Bcustomsec*{}} {start_opt:Bstartsec} {Bcustomsec*{}} {elem_lst:Belemsec} {Bcustomsec*{}} {(local_lst, v_expr)*{v_expr <- expr_lst, local_lst <- local_lst_lst}:Bcodesec} {Bcustomsec*{}} {data_lst:Bdatasec} {Bcustomsec*{}}} => MODULE_module(type_lst, import_lst, func_lst, global_lst, table_lst, mem_lst, elem_lst, data_lst, start_opt, export_lst)
    -- (if (v_func = FUNC_func(v_typeidx, local_lst, v_expr)))*{v_expr <- expr_lst, v_func <- func_lst, local_lst <- local_lst_lst, v_typeidx <- typeidx_lst}

