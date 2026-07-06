
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

;; test.spectec:97.8-97.12
relation wf_byte: `%`(byte)
  ;; test.spectec:97.8-97.12
  rule byte_case_0{i : nat}:
    `%`(mk_byte_byte(i))
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:99.1-100.25
syntax uN = 
  | mk_uN(i : nat)

;; test.spectec:99.8-99.11
relation wf_uN: `%%`(N, uN)
  ;; test.spectec:99.8-99.11
  rule uN_case_0{v_N : N, i : nat}:
    `%%`(v_N, mk_uN_uN(i))
    -- if ((i >= 0) /\ (i <= ((((2 ^ v_N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:101.1-102.49
syntax sN = 
  | mk_sN(i : int)

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

;; test.spectec:160.8-160.12
relation wf_char: `%`(char)
  ;; test.spectec:160.8-160.12
  rule char_case_0{i : nat}:
    `%`(mk_char_char(i))
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:162.1-162.25
def $utf8(var_0_lst : char*) : byte*

;; test.spectec:162.6-162.11
relation utf8_is_wf: `%%`(var_0_lst : char*, ret_val_lst : byte*)
  ;; test.spectec:162.6-162.11
  rule utf8_is_wf_0{var_0_lst : char*, ret_val_lst : byte*}:
    `%%`(var_0_lst, ret_val_lst)
    -- (wf_char: `%`(var_0))*{var_0 <- var_0_lst}
    -- if (ret_val_lst = $utf8(var_0_lst))
    -- (wf_byte: `%`(ret_val))*{ret_val <- ret_val_lst}

;; test.spectec:164.1-164.70
syntax name = 
  | mk_name(char_lst : char*)

;; test.spectec:164.8-164.12
relation wf_name: `%`(name)
  ;; test.spectec:164.8-164.12
  rule name_case_0{char_lst : char*}:
    `%`(mk_name_name(char_lst))
    -- (wf_char: `%`(v_char))*{v_char <- char_lst}
    -- if (|$utf8(char_lst)| < (2 ^ 32))

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

