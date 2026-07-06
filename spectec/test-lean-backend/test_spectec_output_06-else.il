
;; test.spectec:201.14-201.17
syntax MUT = 
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
def $min(nat : nat, nat : nat) : nat
  ;; test.spectec:22.1-22.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:25.1-25.21
rec {

;; test.spectec:25.1-25.21
def $sum(nat*) : nat
  ;; test.spectec:26.1-26.18
  def $sum([]) = 0
  ;; test.spectec:27.1-27.35
  def $sum{n : nat, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n + $sum(n'*{n' <- `n'*`}))
}

;; test.spectec:32.1-32.58
def $opt_(syntax X, X*) : X??
  ;; test.spectec:33.1-33.31
  def $opt_{syntax X}(syntax X, []) = ?(?())
  ;; test.spectec:34.1-34.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(?(w))
  def $opt_{syntax X, x1 : X*}(syntax X, x1) = ?()
    -- otherwise

;; test.spectec:36.1-36.45
def $list_(syntax X, X?) : X*
  ;; test.spectec:37.1-37.32
  def $list_{syntax X}(syntax X, ?()) = []
  ;; test.spectec:38.1-38.28
  def $list_{syntax X, w : X}(syntax X, ?(w)) = [w]

;; test.spectec:40.1-40.59
rec {

;; test.spectec:40.1-40.59
def $concat_(syntax X, X**) : X*
  ;; test.spectec:41.1-41.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; test.spectec:42.1-42.61
  def $concat_{syntax X, `w*` : X*, `w'**` : X**}(syntax X, [w*{w <- `w*`}] ++ w'*{w' <- `w'*`}*{`w'*` <- `w'**`}) = w*{w <- `w*`} ++ $concat_(syntax X, w'*{w' <- `w'*`}*{`w'*` <- `w'**`})
}

;; test.spectec:44.1-44.78
rec {

;; test.spectec:44.1-44.78
def $disjoint_(syntax X, X*) : bool
  ;; test.spectec:45.1-45.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; test.spectec:46.1-46.68
  def $disjoint_{syntax X, w : X, `w'*` : X*}(syntax X, [w] ++ w'*{w' <- `w'*`}) = (~ (w <- w'*{w' <- `w'*`}) /\ $disjoint_(syntax X, w'*{w' <- `w'*`}))
}

;; test.spectec:52.1-52.28
relation Nat_ok: `%|-%`(nat, nat)
  ;; test.spectec:53.1-54.9
  rule refl{n : n}:
    `%|-%`(n, n)

;; test.spectec:56.1-56.31
relation Nats_ok: `%|-%`(nat*, nat*)
  ;; test.spectec:57.1-59.25
  rule all{`n*` : n*}:
    `%|-%`(n*{n <- `n*`}, n*{n <- `n*`})
    -- (Nat_ok: `%|-%`(n, n))*{n <- `n*`}

;; test.spectec:65.1-65.29
relation Pair_ok: `%|-%`(nat, nat)
  ;; test.spectec:66.1-67.9
  rule eq{n : n}:
    `%|-%`(n, n)

;; test.spectec:69.1-69.32
relation Pairs_ok: `%|-%`(nat*, nat*)
  ;; test.spectec:70.1-72.26
  rule all{`n*` : n*, `m*` : m*}:
    `%|-%`(n*{n <- `n*`}, m*{m <- `m*`})
    -- (Pair_ok: `%|-%`(n, m))*{m <- `m*`, n <- `n*`}

;; test.spectec:88.1-88.49
syntax list{syntax X}(syntax X) = 
  | `%`(`X*` : X*)
    -- if (|X*{X <- `X*`}| < (2 ^ 32))

;; test.spectec:97.1-97.50
syntax byte = 
  | `%`(i : nat)

;; test.spectec:97.8-97.12
relation wf_byte: `%`(byte)
  ;; test.spectec:97.8-97.12
  rule byte_case_0{i : nat}:
    `%`(`%`_byte(i))
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:99.1-100.25
syntax uN = 
  | `%`(i : nat)

;; test.spectec:99.8-99.11
relation wf_uN: `%%`(N, uN)
  ;; test.spectec:99.8-99.11
  rule uN_case_0{N : N, i : nat}:
    `%%`(N, `%`_uN(i))
    -- if ((i >= 0) /\ (i <= ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:101.1-102.49
syntax sN = 
  | `%`(i : int)

;; test.spectec:101.8-101.11
relation wf_sN: `%%`(N, sN)
  ;; test.spectec:101.8-101.11
  rule sN_case_0{N : N, i : int}:
    `%%`(N, `%`_sN(i))
    -- if ((((i >= - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

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
def $signif(N : N) : nat?
  ;; test.spectec:119.1-119.21
  def $signif(32) = ?(23)
  ;; test.spectec:120.1-120.21
  def $signif(64) = ?(52)
  def $signif{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:122.1-122.34
def $expon(N : N) : nat?
  ;; test.spectec:123.1-123.19
  def $expon(32) = ?(8)
  ;; test.spectec:124.1-124.20
  def $expon(64) = ?(11)
  def $expon{x0 : N}(x0) = ?()
    -- otherwise

;; test.spectec:126.1-126.30
def $M(N : N) : nat
  ;; test.spectec:127.1-127.23
  def $M{N : nat}(N) = !($signif(N))

;; test.spectec:129.1-129.30
def $E(N : N) : nat
  ;; test.spectec:130.1-130.22
  def $E{N : nat}(N) = !($expon(N))

;; test.spectec:136.1-136.30
syntax exp = int

;; test.spectec:137.1-141.84
syntax fNmag = 
  | NORM(m : m, exp : exp)
  | SUBNORM(m : m)
  | INF
  | NAN(m : m)

;; test.spectec:137.8-137.14
relation wf_fNmag: `%%`(N, fNmag)
  ;; test.spectec:137.8-137.14
  rule fNmag_case_0{N : N, m : m, exp : exp}:
    `%%`(N, NORM_fNmag(m, exp))
    -- if ((m < (2 ^ $M(N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= exp) /\ (exp <= (((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

  ;; test.spectec:137.8-137.14
  rule fNmag_case_1{N : N, exp : exp, m : m}:
    `%%`(N, SUBNORM_fNmag(m))
    -- if ((m < (2 ^ $M(N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = exp))

  ;; test.spectec:137.8-137.14
  rule fNmag_case_2{N : N}:
    `%%`(N, INF_fNmag)

  ;; test.spectec:137.8-137.14
  rule fNmag_case_3{N : N, m : m}:
    `%%`(N, NAN_fNmag(m))
    -- if ((1 <= m) /\ (m < (2 ^ $M(N))))

;; test.spectec:132.1-134.35
syntax fN = 
  | POS(fNmag)
  | NEG(fNmag)

;; test.spectec:132.8-132.11
relation wf_fN: `%%`(N, fN)
  ;; test.spectec:132.8-132.11
  rule fN_case_0{N : N, var_0 : fNmag}:
    `%%`(N, POS_fN(var_0))
    -- wf_fNmag: `%%`(N, var_0)

  ;; test.spectec:132.8-132.11
  rule fN_case_1{N : N, var_0 : fNmag}:
    `%%`(N, NEG_fN(var_0))
    -- wf_fNmag: `%%`(N, var_0)

;; test.spectec:143.1-143.20
syntax f32 = fN

;; test.spectec:144.1-144.20
syntax f64 = fN

;; test.spectec:146.1-146.39
def $fzero(N : N) : fN
  ;; test.spectec:147.1-147.32
  def $fzero{N : nat}(N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:146.6-146.12
relation fzero_is_wf: `%%`(N : N, ret_val : fN)
  ;; test.spectec:146.6-146.12
  rule fzero_is_wf_0{N : N, ret_val : fN}:
    `%%`(N, ret_val)
    -- if (ret_val = $fzero(N))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:149.1-149.39
def $fone(N : N) : fN
  ;; test.spectec:150.1-150.30
  def $fone{N : nat}(N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:149.6-149.11
relation fone_is_wf: `%%`(N : N, ret_val : fN)
  ;; test.spectec:149.6-149.11
  rule fone_is_wf_0{N : N, ret_val : fN}:
    `%%`(N, ret_val)
    -- if (ret_val = $fone(N))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:152.1-152.21
def $canon_(N : N) : nat
  ;; test.spectec:153.1-153.37
  def $canon_{N : nat}(N) = (2 ^ (((!($signif(N)) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:160.1-160.85
syntax char = 
  | `%`(i : nat)

;; test.spectec:160.8-160.12
relation wf_char: `%`(char)
  ;; test.spectec:160.8-160.12
  rule char_case_0{i : nat}:
    `%`(`%`_char(i))
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:162.1-162.25
def $utf8(char*) : byte*

;; test.spectec:162.6-162.11
relation utf8_is_wf: `%%`(`var_0*` : char*, `ret_val*` : byte*)
  ;; test.spectec:162.6-162.11
  rule utf8_is_wf_0{`var_0*` : char*, `ret_val*` : byte*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_char: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $utf8(`var_0*`))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:164.1-164.70
syntax name = 
  | `%`(`char*` : char*)

;; test.spectec:164.8-164.12
relation wf_name: `%`(name)
  ;; test.spectec:164.8-164.12
  rule name_case_0{`char*` : char*}:
    `%`(`%`_name(`char*`))
    -- (wf_char: `%`(char))*{char <- `char*`}
    -- if (|$utf8(char*{char <- `char*`})| < (2 ^ 32))

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

;; test.spectec:194.1-194.38
syntax Fnn = 
  | F32
  | F64

;; test.spectec:198.1-199.11
syntax resulttype = valtype?

;; test.spectec:201.1-201.18
syntax mut = MUT?

;; test.spectec:203.1-204.17
syntax limits = 
  | `[%..%]`(u32 : u32, `u32?` : u32?)

;; test.spectec:203.8-203.14
relation wf_limits: `%`(limits)
  ;; test.spectec:203.8-203.14
  rule limits_case_0{u32 : u32, `u32?` : u32?}:
    `%`(`[%..%]`_limits(u32, `u32?`))
    -- wf_uN: `%%`(32, u32)
    -- (wf_uN: `%%`(32, u32))?{u32 <- `u32?`}

;; test.spectec:205.1-206.14
syntax globaltype = 
  | `%%`(mut : mut, valtype : valtype)

;; test.spectec:207.1-208.23
syntax functype = 
  | `%->%`(`valtype*` : valtype*, `valtype*` : valtype*)

;; test.spectec:209.1-210.9
syntax tabletype = limits

;; test.spectec:211.1-212.9
syntax memtype = limits

;; test.spectec:213.1-214.70
syntax externtype = 
  | FUNC(functype : functype)
  | GLOBAL(globaltype : globaltype)
  | TABLE(tabletype : tabletype)
  | MEM(memtype : memtype)

;; test.spectec:213.8-213.18
relation wf_externtype: `%`(externtype)
  ;; test.spectec:213.8-213.18
  rule externtype_case_0{functype : functype}:
    `%`(FUNC_externtype(functype))

  ;; test.spectec:213.8-213.18
  rule externtype_case_1{globaltype : globaltype}:
    `%`(GLOBAL_externtype(globaltype))

  ;; test.spectec:213.8-213.18
  rule externtype_case_2{tabletype : tabletype}:
    `%`(TABLE_externtype(tabletype))
    -- wf_limits: `%`(tabletype)

  ;; test.spectec:213.8-213.18
  rule externtype_case_3{memtype : memtype}:
    `%`(MEM_externtype(memtype))
    -- wf_limits: `%`(memtype)

;; test.spectec:226.1-226.41
def $size(valtype : valtype) : nat

;; test.spectec:228.1-228.21
syntax val_ = 
  | mk_val__0(Inn : Inn, var_x : iN)
  | mk_val__1(Fnn : Fnn, var_x : fN)

;; test.spectec:228.8-228.13
relation wf_val_: `%%`(valtype, val_)
  ;; test.spectec:228.8-228.13
  rule val__case_0{valtype : valtype, Inn : Inn, var_x : iN}:
    `%%`(valtype, mk_val__0_val_(Inn, var_x))
    -- wf_uN: `%%`($size((Inn : Inn <: valtype)), var_x)
    -- if (valtype = (Inn : Inn <: valtype))

  ;; test.spectec:228.8-228.13
  rule val__case_1{valtype : valtype, Fnn : Fnn, var_x : fN}:
    `%%`(valtype, mk_val__1_val_(Fnn, var_x))
    -- wf_fN: `%%`($size((Fnn : Fnn <: valtype)), var_x)
    -- if (valtype = (Fnn : Fnn <: valtype))

;; test.spectec:228.1-228.21
def $proj_val__0(var_x : val_) : iN?
  ;; test.spectec:228.8-228.13
  def $proj_val__0{Inn : Inn, var_x : iN}(mk_val__0_val_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:228.8-228.13
  def $proj_val__0{var_x : val_}(var_x) = ?()

;; test.spectec:228.1-228.21
def $proj_val__1(var_x : val_) : fN?
  ;; test.spectec:228.8-228.13
  def $proj_val__1{Fnn : Fnn, var_x : fN}(mk_val__1_val_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:228.8-228.13
  def $proj_val__1{var_x : val_}(var_x) = ?()

;; test.spectec:235.1-235.42
syntax sx = 
  | U
  | S

;; test.spectec:236.1-236.56
syntax sz = 
  | `%`(i : nat)

;; test.spectec:236.8-236.10
relation wf_sz: `%`(sz)
  ;; test.spectec:236.8-236.10
  rule sz_case_0{i : nat}:
    `%`(`%`_sz(i))
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
  | mk_unop__0(Inn : Inn, var_x : unop_Inn)
  | mk_unop__1(Fnn : Fnn, var_x : unop_Fnn)

;; test.spectec:238.8-238.14
relation wf_unop_: `%%`(valtype, unop_)
  ;; test.spectec:238.8-238.14
  rule unop__case_0{valtype : valtype, Inn : Inn, var_x : unop_Inn}:
    `%%`(valtype, mk_unop__0_unop_(Inn, var_x))
    -- if (valtype = (Inn : Inn <: valtype))

  ;; test.spectec:238.8-238.14
  rule unop__case_1{valtype : valtype, Fnn : Fnn, var_x : unop_Fnn}:
    `%%`(valtype, mk_unop__1_unop_(Fnn, var_x))
    -- if (valtype = (Fnn : Fnn <: valtype))

;; test.spectec:238.1-238.22
def $proj_unop__0(var_x : unop_) : unop_Inn?
  ;; test.spectec:238.8-238.14
  def $proj_unop__0{Inn : Inn, var_x : unop_Inn}(mk_unop__0_unop_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:238.8-238.14
  def $proj_unop__0{var_x : unop_}(var_x) = ?()

;; test.spectec:238.1-238.22
def $proj_unop__1(var_x : unop_) : unop_Fnn?
  ;; test.spectec:238.8-238.14
  def $proj_unop__1{Fnn : Fnn, var_x : unop_Fnn}(mk_unop__1_unop_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:238.8-238.14
  def $proj_unop__1{var_x : unop_}(var_x) = ?()

;; test.spectec:242.1-242.23
syntax binop_Inn = 
  | ADD
  | SUB
  | MUL
  | DIV(sx : sx)
  | REM(sx : sx)
  | AND
  | OR
  | XOR
  | SHL
  | SHR(sx : sx)
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
  | mk_binop__0(Inn : Inn, var_x : binop_Inn)
  | mk_binop__1(Fnn : Fnn, var_x : binop_Fnn)

;; test.spectec:242.8-242.15
relation wf_binop_: `%%`(valtype, binop_)
  ;; test.spectec:242.8-242.15
  rule binop__case_0{valtype : valtype, Inn : Inn, var_x : binop_Inn}:
    `%%`(valtype, mk_binop__0_binop_(Inn, var_x))
    -- if (valtype = (Inn : Inn <: valtype))

  ;; test.spectec:242.8-242.15
  rule binop__case_1{valtype : valtype, Fnn : Fnn, var_x : binop_Fnn}:
    `%%`(valtype, mk_binop__1_binop_(Fnn, var_x))
    -- if (valtype = (Fnn : Fnn <: valtype))

;; test.spectec:242.1-242.23
def $proj_binop__0(var_x : binop_) : binop_Inn?
  ;; test.spectec:242.8-242.15
  def $proj_binop__0{Inn : Inn, var_x : binop_Inn}(mk_binop__0_binop_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:242.8-242.15
  def $proj_binop__0{var_x : binop_}(var_x) = ?()

;; test.spectec:242.1-242.23
def $proj_binop__1(var_x : binop_) : binop_Fnn?
  ;; test.spectec:242.8-242.15
  def $proj_binop__1{Fnn : Fnn, var_x : binop_Fnn}(mk_binop__1_binop_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:242.8-242.15
  def $proj_binop__1{var_x : binop_}(var_x) = ?()

;; test.spectec:249.1-249.24
syntax testop_Inn = 
  | EQZ

;; test.spectec:249.1-249.24
syntax testop_ = 
  | mk_testop__0(Inn : Inn, var_x : testop_Inn)

;; test.spectec:249.8-249.16
relation wf_testop_: `%%`(valtype, testop_)
  ;; test.spectec:249.8-249.16
  rule testop__case_0{valtype : valtype, Inn : Inn, var_x : testop_Inn}:
    `%%`(valtype, mk_testop__0_testop_(Inn, var_x))
    -- if (valtype = (Inn : Inn <: valtype))

;; test.spectec:249.1-249.24
def $proj_testop__0(var_x : testop_) : testop_Inn
  ;; test.spectec:249.8-249.16
  def $proj_testop__0{Inn : Inn, var_x : testop_Inn}(mk_testop__0_testop_(Inn, var_x)) = var_x

;; test.spectec:253.1-253.23
syntax relop_Inn = 
  | EQ
  | NE
  | LT(sx : sx)
  | GT(sx : sx)
  | LE(sx : sx)
  | GE(sx : sx)

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
  | mk_relop__0(Inn : Inn, var_x : relop_Inn)
  | mk_relop__1(Fnn : Fnn, var_x : relop_Fnn)

;; test.spectec:253.8-253.15
relation wf_relop_: `%%`(valtype, relop_)
  ;; test.spectec:253.8-253.15
  rule relop__case_0{valtype : valtype, Inn : Inn, var_x : relop_Inn}:
    `%%`(valtype, mk_relop__0_relop_(Inn, var_x))
    -- if (valtype = (Inn : Inn <: valtype))

  ;; test.spectec:253.8-253.15
  rule relop__case_1{valtype : valtype, Fnn : Fnn, var_x : relop_Fnn}:
    `%%`(valtype, mk_relop__1_relop_(Fnn, var_x))
    -- if (valtype = (Fnn : Fnn <: valtype))

;; test.spectec:253.1-253.23
def $proj_relop__0(var_x : relop_) : relop_Inn?
  ;; test.spectec:253.8-253.15
  def $proj_relop__0{Inn : Inn, var_x : relop_Inn}(mk_relop__0_relop_(Inn, var_x)) = ?(var_x)
  ;; test.spectec:253.8-253.15
  def $proj_relop__0{var_x : relop_}(var_x) = ?()

;; test.spectec:253.1-253.23
def $proj_relop__1(var_x : relop_) : relop_Fnn?
  ;; test.spectec:253.8-253.15
  def $proj_relop__1{Fnn : Fnn, var_x : relop_Fnn}(mk_relop__1_relop_(Fnn, var_x)) = ?(var_x)
  ;; test.spectec:253.8-253.15
  def $proj_relop__1{var_x : relop_}(var_x) = ?()

;; test.spectec:261.1-262.78
syntax cvtop = 
  | EXTEND(sx : sx)
  | WRAP
  | CONVERT(sx : sx)
  | TRUNC(sx : sx)
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
  | `%_%`(sz : sz, sx : sx)

;; test.spectec:271.8-271.16
relation wf_loadop_Inn: `%%`(Inn, loadop_Inn)
  ;; test.spectec:271.8-271.16
  rule loadop_Inn_case_0{Inn : Inn, sz : sz, sx : sx}:
    `%%`(Inn, `%_%`_loadop_Inn(sz, sx))
    -- wf_sz: `%`(sz)
    -- if (sz!`%`_sz.0 < $size((Inn : Inn <: valtype)))

;; test.spectec:271.1-271.24
syntax loadop_ = 
  | mk_loadop__0(Inn : Inn, var_x : loadop_Inn)

;; test.spectec:271.8-271.16
relation wf_loadop_: `%%`(valtype, loadop_)
  ;; test.spectec:271.8-271.16
  rule loadop__case_0{valtype : valtype, Inn : Inn, var_x : loadop_Inn}:
    `%%`(valtype, mk_loadop__0_loadop_(Inn, var_x))
    -- wf_loadop_Inn: `%%`(Inn, var_x)
    -- if (valtype = (Inn : Inn <: valtype))

;; test.spectec:271.1-271.24
def $proj_loadop__0(var_x : loadop_) : loadop_Inn
  ;; test.spectec:271.8-271.16
  def $proj_loadop__0{Inn : Inn, var_x : loadop_Inn}(mk_loadop__0_loadop_(Inn, var_x)) = var_x

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
  | BLOCK(blocktype : blocktype, `instr*` : instr*)
  | LOOP(blocktype : blocktype, `instr*` : instr*)
  | `IF%%ELSE%`(blocktype : blocktype, `instr*` : instr*, `instr*` : instr*)
  | BR(labelidx : labelidx)
  | BR_IF(labelidx : labelidx)
  | BR_TABLE(`labelidx*` : labelidx*, labelidx : labelidx)
  | CALL(funcidx : funcidx)
  | CALL_INDIRECT(typeidx : typeidx)
  | RETURN
  | CONST(valtype : valtype, val_)
  | UNOP(valtype : valtype, unop_)
  | BINOP(valtype : valtype, binop_)
  | TESTOP(valtype : valtype, testop_)
  | RELOP(valtype : valtype, relop_)
  | CVTOP(valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop)
  | `LOCAL.GET`(localidx : localidx)
  | `LOCAL.SET`(localidx : localidx)
  | `LOCAL.TEE`(localidx : localidx)
  | `GLOBAL.GET`(globalidx : globalidx)
  | `GLOBAL.SET`(globalidx : globalidx)
  | LOAD(valtype : valtype, loadop_?, memarg : memarg)
  | STORE(valtype : valtype, `sz?` : sz?, memarg : memarg)
  | `MEMORY.SIZE`
  | `MEMORY.GROW`
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
  rule instr_case_4{blocktype : blocktype, `instr*` : instr*}:
    `%`(BLOCK_instr(blocktype, `instr*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:327.8-327.13
  rule instr_case_5{blocktype : blocktype, `instr*` : instr*}:
    `%`(LOOP_instr(blocktype, `instr*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:327.8-327.13
  rule instr_case_6{blocktype : blocktype, `instr*` : instr*, `instr*_0*` : instr*}:
    `%`(`IF%%ELSE%`_instr(blocktype, `instr*`, `instr*_0*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- (wf_instr: `%`(`instr*_0`))*{`instr*_0` <- `instr*_0*`}

  ;; test.spectec:327.8-327.13
  rule instr_case_7{labelidx : labelidx}:
    `%`(BR_instr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_8{labelidx : labelidx}:
    `%`(BR_IF_instr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_9{`labelidx*` : labelidx*, labelidx : labelidx}:
    `%`(BR_TABLE_instr(`labelidx*`, labelidx))
    -- (wf_uN: `%%`(32, labelidx))*{labelidx <- `labelidx*`}
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_10{funcidx : funcidx}:
    `%`(CALL_instr(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_11{typeidx : typeidx}:
    `%`(CALL_INDIRECT_instr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_12:
    `%`(RETURN_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_13{valtype : valtype, var_0 : val_}:
    `%`(CONST_instr(valtype, var_0))
    -- wf_val_: `%%`(valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_14{valtype : valtype, var_0 : unop_}:
    `%`(UNOP_instr(valtype, var_0))
    -- wf_unop_: `%%`(valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_15{valtype : valtype, var_0 : binop_}:
    `%`(BINOP_instr(valtype, var_0))
    -- wf_binop_: `%%`(valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_16{valtype : valtype, var_0 : testop_}:
    `%`(TESTOP_instr(valtype, var_0))
    -- wf_testop_: `%%`(valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_17{valtype : valtype, var_0 : relop_}:
    `%`(RELOP_instr(valtype, var_0))
    -- wf_relop_: `%%`(valtype, var_0)

  ;; test.spectec:327.8-327.13
  rule instr_case_18{valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop}:
    `%`(CVTOP_instr(valtype_1, valtype_2, cvtop))
    -- if (valtype_1 =/= valtype_2)

  ;; test.spectec:327.8-327.13
  rule instr_case_19{localidx : localidx}:
    `%`(`LOCAL.GET`_instr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_20{localidx : localidx}:
    `%`(`LOCAL.SET`_instr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_21{localidx : localidx}:
    `%`(`LOCAL.TEE`_instr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_22{globalidx : globalidx}:
    `%`(`GLOBAL.GET`_instr(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_23{globalidx : globalidx}:
    `%`(`GLOBAL.SET`_instr(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:327.8-327.13
  rule instr_case_24{valtype : valtype, `var_0?` : loadop_?, memarg : memarg}:
    `%`(LOAD_instr(valtype, `var_0?`, memarg))
    -- (wf_loadop_: `%%`(valtype, var_0))?{var_0 <- `var_0?`}
    -- wf_memarg: `%`(memarg)

  ;; test.spectec:327.8-327.13
  rule instr_case_25{`Inn?` : Inn?, `valtype?` : valtype?, valtype : valtype, `sz?` : sz?, memarg : memarg}:
    `%`(STORE_instr(valtype, `sz?`, memarg))
    -- (wf_sz: `%`(sz))?{sz <- `sz?`}
    -- wf_memarg: `%`(memarg)
    -- (if ((valtype = (Inn : Inn <: valtype)) /\ (sz!`%`_sz.0 < $size((Inn : Inn <: valtype)))))?{Inn <- `Inn?`, sz <- `sz?`, valtype <- `valtype?`}

  ;; test.spectec:327.8-327.13
  rule instr_case_26:
    `%`(`MEMORY.SIZE`_instr)

  ;; test.spectec:327.8-327.13
  rule instr_case_27:
    `%`(`MEMORY.GROW`_instr)
}

;; test.spectec:334.1-335.9
syntax expr = instr*

;; test.spectec:345.1-346.16
syntax type = 
  | TYPE(functype : functype)

;; test.spectec:347.1-348.16
syntax local = 
  | LOCAL(valtype : valtype)

;; test.spectec:349.1-350.27
syntax func = 
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)

;; test.spectec:349.8-349.12
relation wf_func: `%`(func)
  ;; test.spectec:349.8-349.12
  rule func_case_0{typeidx : typeidx, `local*` : local*, expr : expr}:
    `%`(FUNC_func(typeidx, `local*`, expr))
    -- wf_uN: `%%`(32, typeidx)
    -- (wf_instr: `%`(expr))*{expr <- expr}

;; test.spectec:351.1-352.25
syntax global = 
  | GLOBAL(globaltype : globaltype, expr : expr)

;; test.spectec:351.8-351.14
relation wf_global: `%`(global)
  ;; test.spectec:351.8-351.14
  rule global_case_0{globaltype : globaltype, expr : expr}:
    `%`(GLOBAL_global(globaltype, expr))
    -- (wf_instr: `%`(expr))*{expr <- expr}

;; test.spectec:353.1-354.18
syntax table = 
  | TABLE(tabletype : tabletype)

;; test.spectec:353.8-353.13
relation wf_table: `%`(table)
  ;; test.spectec:353.8-353.13
  rule table_case_0{tabletype : tabletype}:
    `%`(TABLE_table(tabletype))
    -- wf_limits: `%`(tabletype)

;; test.spectec:355.1-356.17
syntax mem = 
  | MEMORY(memtype : memtype)

;; test.spectec:355.8-355.11
relation wf_mem: `%`(mem)
  ;; test.spectec:355.8-355.11
  rule mem_case_0{memtype : memtype}:
    `%`(MEMORY_mem(memtype))
    -- wf_limits: `%`(memtype)

;; test.spectec:357.1-358.21
syntax elem = 
  | ELEM(expr : expr, `funcidx*` : funcidx*)

;; test.spectec:357.8-357.12
relation wf_elem: `%`(elem)
  ;; test.spectec:357.8-357.12
  rule elem_case_0{expr : expr, `funcidx*` : funcidx*}:
    `%`(ELEM_elem(expr, `funcidx*`))
    -- (wf_instr: `%`(expr))*{expr <- expr}
    -- (wf_uN: `%%`(32, funcidx))*{funcidx <- `funcidx*`}

;; test.spectec:359.1-360.18
syntax data = 
  | DATA(expr : expr, `byte*` : byte*)

;; test.spectec:359.8-359.12
relation wf_data: `%`(data)
  ;; test.spectec:359.8-359.12
  rule data_case_0{expr : expr, `byte*` : byte*}:
    `%`(DATA_data(expr, `byte*`))
    -- (wf_instr: `%`(expr))*{expr <- expr}
    -- (wf_byte: `%`(byte))*{byte <- `byte*`}

;; test.spectec:361.1-362.16
syntax start = 
  | START(funcidx : funcidx)

;; test.spectec:361.8-361.13
relation wf_start: `%`(start)
  ;; test.spectec:361.8-361.13
  rule start_case_0{funcidx : funcidx}:
    `%`(START_start(funcidx))
    -- wf_uN: `%%`(32, funcidx)

;; test.spectec:364.1-365.66
syntax externidx = 
  | FUNC(funcidx : funcidx)
  | GLOBAL(globalidx : globalidx)
  | TABLE(tableidx : tableidx)
  | MEM(memidx : memidx)

;; test.spectec:364.8-364.17
relation wf_externidx: `%`(externidx)
  ;; test.spectec:364.8-364.17
  rule externidx_case_0{funcidx : funcidx}:
    `%`(FUNC_externidx(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:364.8-364.17
  rule externidx_case_1{globalidx : globalidx}:
    `%`(GLOBAL_externidx(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:364.8-364.17
  rule externidx_case_2{tableidx : tableidx}:
    `%`(TABLE_externidx(tableidx))
    -- wf_uN: `%%`(32, tableidx)

  ;; test.spectec:364.8-364.17
  rule externidx_case_3{memidx : memidx}:
    `%`(MEM_externidx(memidx))
    -- wf_uN: `%%`(32, memidx)

;; test.spectec:366.1-367.24
syntax export = 
  | EXPORT(name : name, externidx : externidx)

;; test.spectec:366.8-366.14
relation wf_export: `%`(export)
  ;; test.spectec:366.8-366.14
  rule export_case_0{name : name, externidx : externidx}:
    `%`(EXPORT_export(name, externidx))
    -- wf_name: `%`(name)
    -- wf_externidx: `%`(externidx)

;; test.spectec:368.1-369.30
syntax import = 
  | IMPORT(name : name, name : name, externtype : externtype)

;; test.spectec:368.8-368.14
relation wf_import: `%`(import)
  ;; test.spectec:368.8-368.14
  rule import_case_0{name : name, name_0 : name, externtype : externtype}:
    `%`(IMPORT_import(name, name_0, externtype))
    -- wf_name: `%`(name)
    -- wf_name: `%`(name_0)
    -- wf_externtype: `%`(externtype)

;; test.spectec:371.1-372.76
syntax module = 
  | MODULE(`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*)

;; test.spectec:371.8-371.14
relation wf_module: `%`(module)
  ;; test.spectec:371.8-371.14
  rule module_case_0{`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*}:
    `%`(MODULE_module(`type*`, `import*`, `func*`, `global*`, `table*`, `mem*`, `elem*`, `data*`, `start?`, `export*`))
    -- (wf_import: `%`(import))*{import <- `import*`}
    -- (wf_func: `%`(func))*{func <- `func*`}
    -- (wf_global: `%`(global))*{global <- `global*`}
    -- (wf_table: `%`(table))*{table <- `table*`}
    -- (wf_mem: `%`(mem))*{mem <- `mem*`}
    -- (wf_elem: `%`(elem))*{elem <- `elem*`}
    -- (wf_data: `%`(data))*{data <- `data*`}
    -- (wf_start: `%`(start))?{start <- `start?`}
    -- (wf_export: `%`(export))*{export <- `export*`}

