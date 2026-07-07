
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
rec {

;; test.spectec:162.1-162.25
def $utf8(char*) : byte*
  ;; test.spectec:1908.1-1908.47
  def $utf8{ch : char, b : byte}([ch]) = [b]
    -- if ((ch!`%`_char.0 < 128) /\ (`%`_byte(ch!`%`_char.0) = b))
    -- wf_byte: `%`(`%`_byte(ch!`%`_char.0))
  ;; test.spectec:1909.1-1909.96
  def $utf8{ch : char, b_1 : byte, b_2 : byte}([ch]) = [b_1 b_2]
    -- if (((128 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 2048)) /\ (ch!`%`_char.0 = (((2 ^ 6) * (((b_1!`%`_byte.0 : nat <:> int) - (192 : nat <:> int)) : int <:> nat)) + (((b_2!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
  ;; test.spectec:1910.1-1910.148
  def $utf8{ch : char, b_1 : byte, b_2 : byte, b_3 : byte}([ch]) = [b_1 b_2 b_3]
    -- if ((((2048 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 55296)) \/ ((57344 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 65536))) /\ (ch!`%`_char.0 = ((((2 ^ 12) * (((b_1!`%`_byte.0 : nat <:> int) - (224 : nat <:> int)) : int <:> nat)) + ((2 ^ 6) * (((b_2!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + (((b_3!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
  ;; test.spectec:1911.1-1911.148
  def $utf8{ch : char, b_1 : byte, b_2 : byte, b_3 : byte, b_4 : byte}([ch]) = [b_1 b_2 b_3 b_4]
    -- if (((65536 <= ch!`%`_char.0) /\ (ch!`%`_char.0 < 69632)) /\ (ch!`%`_char.0 = (((((2 ^ 18) * (((b_1!`%`_byte.0 : nat <:> int) - (240 : nat <:> int)) : int <:> nat)) + ((2 ^ 12) * (((b_2!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + ((2 ^ 6) * (((b_3!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))) + (((b_4!`%`_byte.0 : nat <:> int) - (128 : nat <:> int)) : int <:> nat))))
  ;; test.spectec:1912.1-1912.44
  def $utf8{`ch*` : char*}(ch*{ch <- `ch*`}) = $concat_(syntax byte, $utf8([ch])*{ch <- `ch*`})
}

;; test.spectec:162.1-162.25
rec {

;; test.spectec:162.6-162.11
relation utf8_is_wf: `%%`(`var_0*` : char*, `ret_val*` : byte*)
  ;; test.spectec:162.6-162.11
  rule utf8_is_wf_0{`var_0*` : char*, `ret_val*` : byte*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_char: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $utf8(`var_0*`))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}
}

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

;; test.spectec:409.1-409.64
rec {

;; test.spectec:409.1-409.64
def $funcsxt(externtype*) : functype*
  ;; test.spectec:414.1-414.24
  def $funcsxt([]) = []
  ;; test.spectec:415.1-415.47
  def $funcsxt{ft : functype, `xt*` : externtype*}([FUNC_externtype(ft)] ++ xt*{xt <- `xt*`}) = [ft] ++ $funcsxt(xt*{xt <- `xt*`})
  ;; test.spectec:416.1-416.59
  def $funcsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $funcsxt(xt*{xt <- `xt*`})
}

;; test.spectec:410.1-410.66
rec {

;; test.spectec:410.1-410.66
def $globalsxt(externtype*) : globaltype*
  ;; test.spectec:418.1-418.26
  def $globalsxt([]) = []
  ;; test.spectec:419.1-419.53
  def $globalsxt{gt : globaltype, `xt*` : externtype*}([GLOBAL_externtype(gt)] ++ xt*{xt <- `xt*`}) = [gt] ++ $globalsxt(xt*{xt <- `xt*`})
  ;; test.spectec:420.1-420.63
  def $globalsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $globalsxt(xt*{xt <- `xt*`})
}

;; test.spectec:411.1-411.65
rec {

;; test.spectec:411.1-411.65
def $tablesxt(externtype*) : tabletype*
  ;; test.spectec:422.1-422.25
  def $tablesxt([]) = []
  ;; test.spectec:423.1-423.50
  def $tablesxt{tt : limits, `xt*` : externtype*}([TABLE_externtype(tt)] ++ xt*{xt <- `xt*`}) = [tt] ++ $tablesxt(xt*{xt <- `xt*`})
  ;; test.spectec:424.1-424.61
  def $tablesxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tablesxt(xt*{xt <- `xt*`})
}

;; test.spectec:411.1-411.65
rec {

;; test.spectec:411.6-411.15
relation tablesxt_is_wf: `%%`(`var_0*` : externtype*, `ret_val*` : tabletype*)
  ;; test.spectec:411.6-411.15
  rule tablesxt_is_wf_0{`var_0*` : externtype*, `ret_val*` : tabletype*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externtype: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $tablesxt(`var_0*`))
    -- (wf_limits: `%`(ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:412.1-412.63
rec {

;; test.spectec:412.1-412.63
def $memsxt(externtype*) : memtype*
  ;; test.spectec:426.1-426.23
  def $memsxt([]) = []
  ;; test.spectec:427.1-427.44
  def $memsxt{mt : limits, `xt*` : externtype*}([MEM_externtype(mt)] ++ xt*{xt <- `xt*`}) = [mt] ++ $memsxt(xt*{xt <- `xt*`})
  ;; test.spectec:428.1-428.57
  def $memsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $memsxt(xt*{xt <- `xt*`})
}

;; test.spectec:412.1-412.63
rec {

;; test.spectec:412.6-412.13
relation memsxt_is_wf: `%%`(`var_0*` : externtype*, `ret_val*` : memtype*)
  ;; test.spectec:412.6-412.13
  rule memsxt_is_wf_0{`var_0*` : externtype*, `ret_val*` : memtype*}:
    `%%`(`var_0*`, `ret_val*`)
    -- (wf_externtype: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (`ret_val*` = $memsxt(`var_0*`))
    -- (wf_limits: `%`(ret_val))*{ret_val <- `ret_val*`}
}

;; test.spectec:438.1-438.35
def $memarg0 : memarg
  ;; test.spectec:439.1-439.35
  def $memarg0 = {ALIGN `%`_u32(0), OFFSET `%`_u32(0)}

;; test.spectec:438.6-438.13
relation memarg0_is_wf: `%`(ret_val : memarg)
  ;; test.spectec:438.6-438.13
  rule memarg0_is_wf_0{ret_val : memarg}:
    `%`(ret_val)
    -- if (ret_val = $memarg0)
    -- wf_memarg: `%`(ret_val)

;; test.spectec:451.1-451.22
def $bool(bool : bool) : nat
  ;; test.spectec:452.1-452.21
  def $bool(false) = 0
  ;; test.spectec:453.1-453.20
  def $bool(true) = 1

;; test.spectec:455.1-455.23
def $truncz(rat : rat) : int

;; test.spectec:462.1-462.54
def $signed_(N : N, nat : nat) : int
  ;; test.spectec:463.1-463.54
  def $signed_{N : nat, i : nat}(N, i) = (i : nat <:> int)
    -- if (i < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))
  ;; test.spectec:464.1-464.61
  def $signed_{N : nat, i : nat}(N, i) = ((i : nat <:> int) - ((2 ^ N) : nat <:> int))
    -- if (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ N)))

;; test.spectec:466.1-466.68
def $inv_signed_(N : N, int : int) : nat
  ;; test.spectec:467.1-467.62
  def $inv_signed_{N : nat, i : int}(N, i) = (i : int <:> nat)
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))
  ;; test.spectec:468.1-468.63
  def $inv_signed_{N : nat, i : int}(N, i) = ((i + ((2 ^ N) : nat <:> int)) : int <:> nat)
    -- if ((- ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; test.spectec:596.1-596.30
def $fabs_(N : N, fN : fN) : fN*

;; test.spectec:596.6-596.12
relation fabs__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:596.6-596.12
  rule fabs__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fabs_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:599.1-599.31
def $fceil_(N : N, fN : fN) : fN*

;; test.spectec:599.6-599.13
relation fceil__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:599.6-599.13
  rule fceil__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fceil_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:600.1-600.32
def $ffloor_(N : N, fN : fN) : fN*

;; test.spectec:600.6-600.14
relation ffloor__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:600.6-600.14
  rule ffloor__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $ffloor_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:602.1-602.34
def $fnearest_(N : N, fN : fN) : fN*

;; test.spectec:602.6-602.16
relation fnearest__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:602.6-602.16
  rule fnearest__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fnearest_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:597.1-597.30
def $fneg_(N : N, fN : fN) : fN*

;; test.spectec:597.6-597.12
relation fneg__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:597.6-597.12
  rule fneg__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fneg_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:598.1-598.31
def $fsqrt_(N : N, fN : fN) : fN*

;; test.spectec:598.6-598.13
relation fsqrt__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:598.6-598.13
  rule fsqrt__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fsqrt_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:601.1-601.32
def $ftrunc_(N : N, fN : fN) : fN*

;; test.spectec:601.6-601.14
relation ftrunc__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:601.6-601.14
  rule ftrunc__is_wf_0{N : N, fN : fN, `ret_val*` : fN*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $ftrunc_(N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:530.1-530.29
def $iclz_(N : N, iN : iN) : iN

;; test.spectec:530.6-530.12
relation iclz__is_wf: `%%%`(N : N, iN : iN, ret_val : iN)
  ;; test.spectec:530.6-530.12
  rule iclz__is_wf_0{N : N, iN : iN, ret_val : iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $iclz_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:531.1-531.29
def $ictz_(N : N, iN : iN) : iN

;; test.spectec:531.6-531.12
relation ictz__is_wf: `%%%`(N : N, iN : iN, ret_val : iN)
  ;; test.spectec:531.6-531.12
  rule ictz__is_wf_0{N : N, iN : iN, ret_val : iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ictz_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:532.1-532.32
def $ipopcnt_(N : N, iN : iN) : iN

;; test.spectec:532.6-532.15
relation ipopcnt__is_wf: `%%%`(N : N, iN : iN, ret_val : iN)
  ;; test.spectec:532.6-532.15
  rule ipopcnt__is_wf_0{N : N, iN : iN, ret_val : iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ipopcnt_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:472.1-473.46
def $unop_(valtype : valtype, unop_ : unop_, val_ : val_) : val_*?
  ;; test.spectec:646.1-646.50
  def $unop_{Inn : Inn, iN : uN}((Inn : Inn <: valtype), mk_unop__0_unop_(Inn, CLZ_unop_Inn), mk_val__0_val_(Inn, iN)) = ?([mk_val__0_val_(Inn, $iclz_($size((Inn : Inn <: valtype)), iN))])
  ;; test.spectec:647.1-647.50
  def $unop_{Inn : Inn, iN : uN}((Inn : Inn <: valtype), mk_unop__0_unop_(Inn, CTZ_unop_Inn), mk_val__0_val_(Inn, iN)) = ?([mk_val__0_val_(Inn, $ictz_($size((Inn : Inn <: valtype)), iN))])
  ;; test.spectec:648.1-648.56
  def $unop_{Inn : Inn, iN : uN}((Inn : Inn <: valtype), mk_unop__0_unop_(Inn, POPCNT_unop_Inn), mk_val__0_val_(Inn, iN)) = ?([mk_val__0_val_(Inn, $ipopcnt_($size((Inn : Inn <: valtype)), iN))])
  ;; test.spectec:665.1-665.50
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, ABS_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fabs_($size((Fnn : Fnn <: valtype)), fN)})
  ;; test.spectec:666.1-666.50
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, NEG_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fneg_($size((Fnn : Fnn <: valtype)), fN)})
  ;; test.spectec:667.1-667.52
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, SQRT_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fsqrt_($size((Fnn : Fnn <: valtype)), fN)})
  ;; test.spectec:668.1-668.52
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, CEIL_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fceil_($size((Fnn : Fnn <: valtype)), fN)})
  ;; test.spectec:669.1-669.54
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, FLOOR_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $ffloor_($size((Fnn : Fnn <: valtype)), fN)})
  ;; test.spectec:670.1-670.54
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, TRUNC_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $ftrunc_($size((Fnn : Fnn <: valtype)), fN)})
  ;; test.spectec:671.1-671.58
  def $unop_{Fnn : Fnn, fN : fN}((Fnn : Fnn <: valtype), mk_unop__1_unop_(Fnn, NEAREST_unop_Fnn), mk_val__1_val_(Fnn, fN)) = ?(mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fnearest_($size((Fnn : Fnn <: valtype)), fN)})
  def $unop_{x0 : valtype, x1 : unop_, x2 : val_}(x0, x1, x2) = ?()
    -- otherwise

;; test.spectec:472.6-472.12
relation unop__is_wf: `%%%%`(valtype : valtype, unop_ : unop_, val_ : val_, `ret_val*` : val_*)
  ;; test.spectec:472.6-472.12
  rule unop__is_wf_0{valtype : valtype, unop_ : unop_, val_ : val_, `ret_val*` : val_*}:
    `%%%%`(valtype, unop_, val_, `ret_val*`)
    -- wf_unop_: `%%`(valtype, unop_)
    -- wf_val_: `%%`(valtype, val_)
    -- if (`ret_val*` = !($unop_(valtype, unop_, val_)))
    -- (wf_val_: `%%`(valtype, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:589.1-589.37
def $fadd_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:589.6-589.12
relation fadd__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:589.6-589.12
  rule fadd__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fadd_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:595.1-595.42
def $fcopysign_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:595.6-595.17
relation fcopysign__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:595.6-595.17
  rule fcopysign__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fcopysign_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:592.1-592.37
def $fdiv_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:592.6-592.12
relation fdiv__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:592.6-592.12
  rule fdiv__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fdiv_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:594.1-594.37
def $fmax_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:594.6-594.12
relation fmax__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:594.6-594.12
  rule fmax__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fmax_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:593.1-593.37
def $fmin_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:593.6-593.12
relation fmin__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:593.6-593.12
  rule fmin__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fmin_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:591.1-591.37
def $fmul_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:591.6-591.12
relation fmul__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:591.6-591.12
  rule fmul__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fmul_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:590.1-590.37
def $fsub_(N : N, fN : fN, fN : fN) : fN*

;; test.spectec:590.6-590.12
relation fsub__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*)
  ;; test.spectec:590.6-590.12
  rule fsub__is_wf_0{N : N, fN : fN, fN_0 : fN, `ret_val*` : fN*}:
    `%%%%`(N, fN, fN_0, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (`ret_val*` = $fsub_(N, fN, fN_0))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:517.1-517.36
def $iadd_(N : N, iN : iN, iN : iN) : iN
  ;; test.spectec:542.1-542.47
  def $iadd_{N : nat, i_1 : uN, i_2 : uN}(N, i_1, i_2) = `%`_iN(((i_1!`%`_uN.0 + i_2!`%`_uN.0) \ (2 ^ N)))

;; test.spectec:517.6-517.12
relation iadd__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:517.6-517.12
  rule iadd__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iadd_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:523.1-523.36
def $iand_(N : N, iN : iN, iN : iN) : iN

;; test.spectec:523.6-523.12
relation iand__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:523.6-523.12
  rule iand__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $iand_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:520.1-520.74
def $idiv_(N : N, sx : sx, iN : iN, iN : iN) : iN?
  ;; test.spectec:546.1-546.33
  def $idiv_{N : nat, i_1 : uN}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:547.1-547.51
  def $idiv_{N : nat, i_1 : uN, i_2 : uN}(N, U_sx, i_1, i_2) = ?(`%`_iN(($truncz(((i_1!`%`_uN.0 : nat <:> rat) / (i_2!`%`_uN.0 : nat <:> rat))) : int <:> nat)))
  ;; test.spectec:548.1-548.33
  def $idiv_{N : nat, i_1 : uN}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:549.1-549.96
  def $idiv_{N : nat, i_1 : uN, i_2 : uN}(N, S_sx, i_1, i_2) = ?()
    -- if ((($signed_(N, i_1!`%`_uN.0) : int <:> rat) / ($signed_(N, i_2!`%`_uN.0) : int <:> rat)) = ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))
  ;; test.spectec:550.1-550.94
  def $idiv_{N : nat, i_1 : uN, i_2 : uN}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, $truncz((($signed_(N, i_1!`%`_uN.0) : int <:> rat) / ($signed_(N, i_2!`%`_uN.0) : int <:> rat))))))

;; test.spectec:520.6-520.12
relation idiv__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, iN_0 : iN, `ret_val?` : iN?)
  ;; test.spectec:520.6-520.12
  rule idiv__is_wf_0{N : N, sx : sx, iN : iN, iN_0 : iN, `ret_val?` : iN?}:
    `%%%%%`(N, sx, iN, iN_0, `ret_val?`)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (`ret_val?` = $idiv_(N, sx, iN, iN_0))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:519.1-519.36
def $imul_(N : N, iN : iN, iN : iN) : iN
  ;; test.spectec:544.1-544.47
  def $imul_{N : nat, i_1 : uN, i_2 : uN}(N, i_1, i_2) = `%`_iN(((i_1!`%`_uN.0 * i_2!`%`_uN.0) \ (2 ^ N)))

;; test.spectec:519.6-519.12
relation imul__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:519.6-519.12
  rule imul__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $imul_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:524.1-524.35
def $ior_(N : N, iN : iN, iN : iN) : iN

;; test.spectec:524.6-524.11
relation ior__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:524.6-524.11
  rule ior__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ior_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:521.1-521.74
def $irem_(N : N, sx : sx, iN : iN, iN : iN) : iN?
  ;; test.spectec:552.1-552.33
  def $irem_{N : nat, i_1 : uN}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:553.1-553.66
  def $irem_{N : nat, i_1 : uN, i_2 : uN}(N, U_sx, i_1, i_2) = ?(`%`_iN((((i_1!`%`_uN.0 : nat <:> int) - ((i_2!`%`_uN.0 * ($truncz(((i_1!`%`_uN.0 : nat <:> rat) / (i_2!`%`_uN.0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat)))
  ;; test.spectec:554.1-554.33
  def $irem_{N : nat, i_1 : uN}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:555.1-556.84
  def $irem_{N : nat, i_1 : uN, i_2 : uN, j_1 : int, j_2 : int}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))))))
    -- if ((j_1 = $signed_(N, i_1!`%`_uN.0)) /\ (j_2 = $signed_(N, i_2!`%`_uN.0)))

;; test.spectec:521.6-521.12
relation irem__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, iN_0 : iN, `ret_val?` : iN?)
  ;; test.spectec:521.6-521.12
  rule irem__is_wf_0{N : N, sx : sx, iN : iN, iN_0 : iN, `ret_val?` : iN?}:
    `%%%%%`(N, sx, iN, iN_0, `ret_val?`)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (`ret_val?` = $irem_(N, sx, iN, iN_0))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:528.1-528.37
def $irotl_(N : N, iN : iN, iN : iN) : iN

;; test.spectec:528.6-528.13
relation irotl__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:528.6-528.13
  rule irotl__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $irotl_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:529.1-529.37
def $irotr_(N : N, iN : iN, iN : iN) : iN

;; test.spectec:529.6-529.13
relation irotr__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:529.6-529.13
  rule irotr__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $irotr_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:526.1-526.34
def $ishl_(N : N, iN : iN, u32 : u32) : iN

;; test.spectec:526.6-526.12
relation ishl__is_wf: `%%%%`(N : N, iN : iN, u32 : u32, ret_val : iN)
  ;; test.spectec:526.6-526.12
  rule ishl__is_wf_0{N : N, iN : iN, u32 : u32, ret_val : iN}:
    `%%%%`(N, iN, u32, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $ishl_(N, iN, u32))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:527.1-527.74
def $ishr_(N : N, sx : sx, iN : iN, u32 : u32) : iN

;; test.spectec:527.6-527.12
relation ishr__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, u32 : u32, ret_val : iN)
  ;; test.spectec:527.6-527.12
  rule ishr__is_wf_0{N : N, sx : sx, iN : iN, u32 : u32, ret_val : iN}:
    `%%%%%`(N, sx, iN, u32, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(32, u32)
    -- if (ret_val = $ishr_(N, sx, iN, u32))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:518.1-518.36
def $isub_(N : N, iN : iN, iN : iN) : iN
  ;; test.spectec:543.1-543.53
  def $isub_{N : nat, i_1 : uN, i_2 : uN}(N, i_1, i_2) = `%`_iN(((((((2 ^ N) + i_1!`%`_uN.0) : nat <:> int) - (i_2!`%`_uN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:518.6-518.12
relation isub__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:518.6-518.12
  rule isub__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $isub_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:525.1-525.36
def $ixor_(N : N, iN : iN, iN : iN) : iN

;; test.spectec:525.6-525.12
relation ixor__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : iN)
  ;; test.spectec:525.6-525.12
  rule ixor__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : iN}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ixor_(N, iN, iN_0))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:474.1-475.34
def $binop_(valtype : valtype, binop_ : binop_, val_ : val_, val_ : val_) : val_*
  ;; test.spectec:634.1-634.67
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, ADD_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $iadd_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:635.1-635.67
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, SUB_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $isub_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:636.1-636.67
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, MUL_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $imul_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:637.1-637.93
  def $binop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, DIV_binop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = $list_(syntax val_, mk_val__0_val_(Inn, iter_0)?{iter_0 <- $idiv_($size((Inn : Inn <: valtype)), sx, iN_1, iN_2)})
  ;; test.spectec:638.1-638.93
  def $binop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, REM_binop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = $list_(syntax val_, mk_val__0_val_(Inn, iter_0)?{iter_0 <- $irem_($size((Inn : Inn <: valtype)), sx, iN_1, iN_2)})
  ;; test.spectec:639.1-639.67
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, AND_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $iand_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:640.1-640.65
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, OR_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $ior_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:641.1-641.67
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, XOR_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $ixor_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:642.1-642.67
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, SHL_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $ishl_($size((Inn : Inn <: valtype)), iN_1, `%`_u32(iN_2!`%`_uN.0)))]
  ;; test.spectec:643.1-643.74
  def $binop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, SHR_binop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $ishr_($size((Inn : Inn <: valtype)), sx, iN_1, `%`_u32(iN_2!`%`_uN.0)))]
  ;; test.spectec:644.1-644.69
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, ROTL_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $irotl_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:645.1-645.69
  def $binop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_binop__0_binop_(Inn, ROTR_binop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = [mk_val__0_val_(Inn, $irotr_($size((Inn : Inn <: valtype)), iN_1, iN_2))]
  ;; test.spectec:657.1-657.67
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, ADD_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fadd_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}
  ;; test.spectec:658.1-658.67
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, SUB_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fsub_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}
  ;; test.spectec:659.1-659.67
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, MUL_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fmul_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}
  ;; test.spectec:660.1-660.67
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, DIV_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fdiv_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}
  ;; test.spectec:661.1-661.67
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, MIN_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fmin_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}
  ;; test.spectec:662.1-662.67
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, MAX_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fmax_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}
  ;; test.spectec:663.1-663.77
  def $binop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_binop__1_binop_(Fnn, COPYSIGN_binop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__1_val_(Fnn, iter_0)*{iter_0 <- $fcopysign_($size((Fnn : Fnn <: valtype)), fN_1, fN_2)}

;; test.spectec:474.6-474.13
relation binop__is_wf: `%%%%%`(valtype : valtype, binop_ : binop_, val_ : val_, val__0 : val_, `ret_val*` : val_*)
  ;; test.spectec:474.6-474.13
  rule binop__is_wf_0{valtype : valtype, binop_ : binop_, val_ : val_, val__0 : val_, `ret_val*` : val_*}:
    `%%%%%`(valtype, binop_, val_, val__0, `ret_val*`)
    -- wf_binop_: `%%`(valtype, binop_)
    -- wf_val_: `%%`(valtype, val_)
    -- wf_val_: `%%`(valtype, val__0)
    -- if (`ret_val*` = $binop_(valtype, binop_, val_, val__0))
    -- (wf_val_: `%%`(valtype, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:533.1-533.27
def $ieqz_(N : N, iN : iN) : u32
  ;; test.spectec:571.1-571.36
  def $ieqz_{N : nat, i_1 : uN}(N, i_1) = `%`_u32($bool((i_1!`%`_uN.0 = 0)))

;; test.spectec:533.6-533.12
relation ieqz__is_wf: `%%%`(N : N, iN : iN, ret_val : u32)
  ;; test.spectec:533.6-533.12
  rule ieqz__is_wf_0{N : N, iN : iN, ret_val : u32}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $ieqz_(N, iN))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:476.1-477.46
def $testop_(valtype : valtype, testop_ : testop_, val_ : val_) : val_?
  ;; test.spectec:649.1-649.52
  def $testop_{Inn : Inn, iN : uN}((Inn : Inn <: valtype), mk_testop__0_testop_(Inn, EQZ_testop_Inn), mk_val__0_val_(Inn, iN)) = ?(mk_val__0_val_(I32_Inn, $ieqz_($size((Inn : Inn <: valtype)), iN)))
  def $testop_{x0 : valtype, x1 : testop_, x2 : val_}(x0, x1, x2) = ?()
    -- otherwise

;; test.spectec:476.6-476.14
relation testop__is_wf: `%%%%`(valtype : valtype, testop_ : testop_, val_ : val_, ret_val : val_)
  ;; test.spectec:476.6-476.14
  rule testop__is_wf_0{valtype : valtype, testop_ : testop_, val_ : val_, ret_val : val_}:
    `%%%%`(valtype, testop_, val_, ret_val)
    -- wf_testop_: `%%`(valtype, testop_)
    -- wf_val_: `%%`(valtype, val_)
    -- if (ret_val = !($testop_(valtype, testop_, val_)))
    -- wf_val_: `%%`(I32_valtype, ret_val)

;; test.spectec:603.1-603.33
def $feq_(N : N, fN : fN, fN : fN) : u32

;; test.spectec:603.6-603.11
relation feq__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:603.6-603.11
  rule feq__is_wf_0{N : N, fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $feq_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:608.1-608.33
def $fge_(N : N, fN : fN, fN : fN) : u32

;; test.spectec:608.6-608.11
relation fge__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:608.6-608.11
  rule fge__is_wf_0{N : N, fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fge_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:606.1-606.33
def $fgt_(N : N, fN : fN, fN : fN) : u32

;; test.spectec:606.6-606.11
relation fgt__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:606.6-606.11
  rule fgt__is_wf_0{N : N, fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fgt_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:607.1-607.33
def $fle_(N : N, fN : fN, fN : fN) : u32

;; test.spectec:607.6-607.11
relation fle__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:607.6-607.11
  rule fle__is_wf_0{N : N, fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fle_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:605.1-605.33
def $flt_(N : N, fN : fN, fN : fN) : u32

;; test.spectec:605.6-605.11
relation flt__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:605.6-605.11
  rule flt__is_wf_0{N : N, fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $flt_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:604.1-604.33
def $fne_(N : N, fN : fN, fN : fN) : u32

;; test.spectec:604.6-604.11
relation fne__is_wf: `%%%%`(N : N, fN : fN, fN_0 : fN, ret_val : u32)
  ;; test.spectec:604.6-604.11
  rule fne__is_wf_0{N : N, fN : fN, fN_0 : fN, ret_val : u32}:
    `%%%%`(N, fN, fN_0, ret_val)
    -- wf_fN: `%%`(N, fN)
    -- wf_fN: `%%`(N, fN_0)
    -- if (ret_val = $fne_(N, fN, fN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:535.1-535.33
def $ieq_(N : N, iN : iN, iN : iN) : u32
  ;; test.spectec:574.1-574.42
  def $ieq_{N : nat, i_1 : uN, i_2 : uN}(N, i_1, i_2) = `%`_u32($bool((i_1 = i_2)))

;; test.spectec:535.6-535.11
relation ieq__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:535.6-535.11
  rule ieq__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ieq_(N, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:540.1-540.73
def $ige_(N : N, sx : sx, iN : iN, iN : iN) : u32
  ;; test.spectec:586.1-586.46
  def $ige_{N : nat, i_1 : uN, i_2 : uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 >= i_2!`%`_uN.0)))
  ;; test.spectec:587.1-587.72
  def $ige_{N : nat, i_1 : uN, i_2 : uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) >= $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:540.6-540.11
relation ige__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:540.6-540.11
  rule ige__is_wf_0{N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ige_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:538.1-538.73
def $igt_(N : N, sx : sx, iN : iN, iN : iN) : u32
  ;; test.spectec:580.1-580.45
  def $igt_{N : nat, i_1 : uN, i_2 : uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 > i_2!`%`_uN.0)))
  ;; test.spectec:581.1-581.71
  def $igt_{N : nat, i_1 : uN, i_2 : uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) > $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:538.6-538.11
relation igt__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:538.6-538.11
  rule igt__is_wf_0{N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $igt_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:539.1-539.73
def $ile_(N : N, sx : sx, iN : iN, iN : iN) : u32
  ;; test.spectec:583.1-583.46
  def $ile_{N : nat, i_1 : uN, i_2 : uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 <= i_2!`%`_uN.0)))
  ;; test.spectec:584.1-584.72
  def $ile_{N : nat, i_1 : uN, i_2 : uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) <= $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:539.6-539.11
relation ile__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:539.6-539.11
  rule ile__is_wf_0{N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ile_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:537.1-537.73
def $ilt_(N : N, sx : sx, iN : iN, iN : iN) : u32
  ;; test.spectec:577.1-577.45
  def $ilt_{N : nat, i_1 : uN, i_2 : uN}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_uN.0 < i_2!`%`_uN.0)))
  ;; test.spectec:578.1-578.71
  def $ilt_{N : nat, i_1 : uN, i_2 : uN}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_uN.0) < $signed_(N, i_2!`%`_uN.0))))

;; test.spectec:537.6-537.11
relation ilt__is_wf: `%%%%%`(N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:537.6-537.11
  rule ilt__is_wf_0{N : N, sx : sx, iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%%`(N, sx, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ilt_(N, sx, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:536.1-536.33
def $ine_(N : N, iN : iN, iN : iN) : u32
  ;; test.spectec:575.1-575.44
  def $ine_{N : nat, i_1 : uN, i_2 : uN}(N, i_1, i_2) = `%`_u32($bool((i_1 =/= i_2)))

;; test.spectec:536.6-536.11
relation ine__is_wf: `%%%%`(N : N, iN : iN, iN_0 : iN, ret_val : u32)
  ;; test.spectec:536.6-536.11
  rule ine__is_wf_0{N : N, iN : iN, iN_0 : iN, ret_val : u32}:
    `%%%%`(N, iN, iN_0, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- wf_uN: `%%`(N, iN_0)
    -- if (ret_val = $ine_(N, iN, iN_0))
    -- wf_uN: `%%`(32, ret_val)

;; test.spectec:478.1-479.34
def $relop_(valtype : valtype, relop_ : relop_, val_ : val_, val_ : val_) : val_
  ;; test.spectec:650.1-650.65
  def $relop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_relop__0_relop_(Inn, EQ_relop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = mk_val__0_val_(I32_Inn, $ieq_($size((Inn : Inn <: valtype)), iN_1, iN_2))
  ;; test.spectec:651.1-651.65
  def $relop_{Inn : Inn, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_relop__0_relop_(Inn, NE_relop_Inn), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = mk_val__0_val_(I32_Inn, $ine_($size((Inn : Inn <: valtype)), iN_1, iN_2))
  ;; test.spectec:652.1-652.72
  def $relop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_relop__0_relop_(Inn, LT_relop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = mk_val__0_val_(I32_Inn, $ilt_($size((Inn : Inn <: valtype)), sx, iN_1, iN_2))
  ;; test.spectec:653.1-653.72
  def $relop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_relop__0_relop_(Inn, GT_relop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = mk_val__0_val_(I32_Inn, $igt_($size((Inn : Inn <: valtype)), sx, iN_1, iN_2))
  ;; test.spectec:654.1-654.72
  def $relop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_relop__0_relop_(Inn, LE_relop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = mk_val__0_val_(I32_Inn, $ile_($size((Inn : Inn <: valtype)), sx, iN_1, iN_2))
  ;; test.spectec:655.1-655.72
  def $relop_{Inn : Inn, sx : sx, iN_1 : uN, iN_2 : uN}((Inn : Inn <: valtype), mk_relop__0_relop_(Inn, GE_relop_Inn(sx)), mk_val__0_val_(Inn, iN_1), mk_val__0_val_(Inn, iN_2)) = mk_val__0_val_(I32_Inn, $ige_($size((Inn : Inn <: valtype)), sx, iN_1, iN_2))
  ;; test.spectec:673.1-673.65
  def $relop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_relop__1_relop_(Fnn, EQ_relop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__0_val_(I32_Inn, $feq_($size((Fnn : Fnn <: valtype)), fN_1, fN_2))
  ;; test.spectec:674.1-674.65
  def $relop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_relop__1_relop_(Fnn, NE_relop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__0_val_(I32_Inn, $fne_($size((Fnn : Fnn <: valtype)), fN_1, fN_2))
  ;; test.spectec:675.1-675.65
  def $relop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_relop__1_relop_(Fnn, LT_relop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__0_val_(I32_Inn, $flt_($size((Fnn : Fnn <: valtype)), fN_1, fN_2))
  ;; test.spectec:676.1-676.65
  def $relop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_relop__1_relop_(Fnn, GT_relop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__0_val_(I32_Inn, $fgt_($size((Fnn : Fnn <: valtype)), fN_1, fN_2))
  ;; test.spectec:677.1-677.65
  def $relop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_relop__1_relop_(Fnn, LE_relop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__0_val_(I32_Inn, $fle_($size((Fnn : Fnn <: valtype)), fN_1, fN_2))
  ;; test.spectec:678.1-678.65
  def $relop_{Fnn : Fnn, fN_1 : fN, fN_2 : fN}((Fnn : Fnn <: valtype), mk_relop__1_relop_(Fnn, GE_relop_Fnn), mk_val__1_val_(Fnn, fN_1), mk_val__1_val_(Fnn, fN_2)) = mk_val__0_val_(I32_Inn, $fge_($size((Fnn : Fnn <: valtype)), fN_1, fN_2))

;; test.spectec:478.6-478.13
relation relop__is_wf: `%%%%%`(valtype : valtype, relop_ : relop_, val_ : val_, val__0 : val_, ret_val : val_)
  ;; test.spectec:478.6-478.13
  rule relop__is_wf_0{valtype : valtype, relop_ : relop_, val_ : val_, val__0 : val_, ret_val : val_}:
    `%%%%%`(valtype, relop_, val_, val__0, ret_val)
    -- wf_relop_: `%%`(valtype, relop_)
    -- wf_val_: `%%`(valtype, val_)
    -- wf_val_: `%%`(valtype, val__0)
    -- if (ret_val = $relop_(valtype, relop_, val_, val__0))
    -- wf_val_: `%%`(I32_valtype, ret_val)

;; test.spectec:488.1-488.90
def $convert__(M : M, N : N, sx : sx, iN : iN) : fN

;; test.spectec:488.6-488.16
relation convert___is_wf: `%%%%%`(M : M, N : N, sx : sx, iN : iN, ret_val : fN)
  ;; test.spectec:488.6-488.16
  rule convert___is_wf_0{M : M, N : N, sx : sx, iN : iN, ret_val : fN}:
    `%%%%%`(M, N, sx, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $convert__(M, N, sx, iN))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:486.1-486.36
def $demote__(M : M, N : N, fN : fN) : fN*

;; test.spectec:486.6-486.15
relation demote___is_wf: `%%%%`(M : M, N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:486.6-486.15
  rule demote___is_wf_0{M : M, N : N, fN : fN, `ret_val*` : fN*}:
    `%%%%`(M, N, fN, `ret_val*`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val*` = $demote__(M, N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:484.1-484.89
def $extend__(M : M, N : N, sx : sx, iN : iN) : iN

;; test.spectec:484.6-484.15
relation extend___is_wf: `%%%%%`(M : M, N : N, sx : sx, iN : iN, ret_val : iN)
  ;; test.spectec:484.6-484.15
  rule extend___is_wf_0{M : M, N : N, sx : sx, iN : iN, ret_val : iN}:
    `%%%%%`(M, N, sx, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $extend__(M, N, sx, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:487.1-487.37
def $promote__(M : M, N : N, fN : fN) : fN*

;; test.spectec:487.6-487.16
relation promote___is_wf: `%%%%`(M : M, N : N, fN : fN, `ret_val*` : fN*)
  ;; test.spectec:487.6-487.16
  rule promote___is_wf_0{M : M, N : N, fN : fN, `ret_val*` : fN*}:
    `%%%%`(M, N, fN, `ret_val*`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val*` = $promote__(M, N, fN))
    -- (wf_fN: `%%`(N, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:489.1-489.76
def $reinterpret__(valtype_1 : valtype, valtype_2 : valtype, val_ : val_) : val_

;; test.spectec:489.6-489.20
relation reinterpret___is_wf: `%%%%`(valtype_1 : valtype, valtype_2 : valtype, val_ : val_, ret_val : val_)
  ;; test.spectec:489.6-489.20
  rule reinterpret___is_wf_0{valtype_1 : valtype, valtype_2 : valtype, val_ : val_, ret_val : val_}:
    `%%%%`(valtype_1, valtype_2, val_, ret_val)
    -- wf_val_: `%%`(valtype_1, val_)
    -- if (ret_val = $reinterpret__(valtype_1, valtype_2, val_))
    -- wf_val_: `%%`(valtype_2, ret_val)

;; test.spectec:485.1-485.88
def $trunc__(M : M, N : N, sx : sx, fN : fN) : iN?

;; test.spectec:485.6-485.14
relation trunc___is_wf: `%%%%%`(M : M, N : N, sx : sx, fN : fN, `ret_val?` : iN?)
  ;; test.spectec:485.6-485.14
  rule trunc___is_wf_0{M : M, N : N, sx : sx, fN : fN, `ret_val?` : iN?}:
    `%%%%%`(M, N, sx, fN, `ret_val?`)
    -- wf_fN: `%%`(M, fN)
    -- if (`ret_val?` = $trunc__(M, N, sx, fN))
    -- (wf_uN: `%%`(N, ret_val))?{ret_val <- `ret_val?`}

;; test.spectec:483.1-483.33
def $wrap__(M : M, N : N, iN : iN) : iN

;; test.spectec:483.6-483.13
relation wrap___is_wf: `%%%%`(M : M, N : N, iN : iN, ret_val : iN)
  ;; test.spectec:483.6-483.13
  rule wrap___is_wf_0{M : M, N : N, iN : iN, ret_val : iN}:
    `%%%%`(M, N, iN, ret_val)
    -- wf_uN: `%%`(M, iN)
    -- if (ret_val = $wrap__(M, N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:480.1-481.36
def $cvtop__(valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop, val_ : val_) : val_*
  ;; test.spectec:680.1-680.66
  def $cvtop__{sx : sx, iN : uN}(I32_valtype, I64_valtype, EXTEND_cvtop(sx), mk_val__0_val_(I32_Inn, iN)) = [mk_val__0_val_(I64_Inn, $extend__(32, 64, sx, iN))]
  ;; test.spectec:681.1-681.55
  def $cvtop__{iN : uN}(I64_valtype, I32_valtype, WRAP_cvtop, mk_val__0_val_(I64_Inn, iN)) = [mk_val__0_val_(I32_Inn, $wrap__(64, 32, iN))]
  ;; test.spectec:682.1-682.99
  def $cvtop__{Fnn : Fnn, Inn : Inn, sx : sx, fN : fN}((Fnn : Fnn <: valtype), (Inn : Inn <: valtype), TRUNC_cvtop(sx), mk_val__1_val_(Fnn, fN)) = $list_(syntax val_, mk_val__0_val_(Inn, iter_0)?{iter_0 <- $trunc__($size((Fnn : Fnn <: valtype)), $size((Inn : Inn <: valtype)), sx, fN)})
  ;; test.spectec:683.1-683.61
  def $cvtop__{fN : fN}(F32_valtype, F64_valtype, PROMOTE_cvtop, mk_val__1_val_(F32_Fnn, fN)) = mk_val__1_val_(F64_Fnn, iter_0)*{iter_0 <- $promote__(32, 64, fN)}
  ;; test.spectec:684.1-684.59
  def $cvtop__{fN : fN}(F64_valtype, F32_valtype, DEMOTE_cvtop, mk_val__1_val_(F64_Fnn, fN)) = mk_val__1_val_(F32_Fnn, iter_0)*{iter_0 <- $demote__(64, 32, fN)}
  ;; test.spectec:685.1-685.84
  def $cvtop__{Inn : Inn, Fnn : Fnn, sx : sx, iN : uN}((Inn : Inn <: valtype), (Fnn : Fnn <: valtype), CONVERT_cvtop(sx), mk_val__0_val_(Inn, iN)) = [mk_val__1_val_(Fnn, $convert__($size((Inn : Inn <: valtype)), $size((Fnn : Fnn <: valtype)), sx, iN))]
  ;; test.spectec:686.1-686.101
  def $cvtop__{Inn : Inn, Fnn : Fnn, iN : uN}((Inn : Inn <: valtype), (Fnn : Fnn <: valtype), REINTERPRET_cvtop, mk_val__0_val_(Inn, iN)) = [$reinterpret__((Inn : Inn <: valtype), (Fnn : Fnn <: valtype), mk_val__0_val_(Inn, iN))]
    -- if ($size((Inn : Inn <: valtype)) = $size((Fnn : Fnn <: valtype)))
  ;; test.spectec:687.1-687.101
  def $cvtop__{Fnn : Fnn, Inn : Inn, fN : fN}((Fnn : Fnn <: valtype), (Inn : Inn <: valtype), REINTERPRET_cvtop, mk_val__1_val_(Fnn, fN)) = [$reinterpret__((Fnn : Fnn <: valtype), (Inn : Inn <: valtype), mk_val__1_val_(Fnn, fN))]
    -- if ($size((Inn : Inn <: valtype)) = $size((Fnn : Fnn <: valtype)))

;; test.spectec:480.6-480.14
relation cvtop___is_wf: `%%%%%`(valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop, val_ : val_, `ret_val*` : val_*)
  ;; test.spectec:480.6-480.14
  rule cvtop___is_wf_0{valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop, val_ : val_, `ret_val*` : val_*}:
    `%%%%%`(valtype_1, valtype_2, cvtop, val_, `ret_val*`)
    -- wf_val_: `%%`(valtype_1, val_)
    -- if (`ret_val*` = $cvtop__(valtype_1, valtype_2, cvtop, val_))
    -- (wf_val_: `%%`(valtype_2, ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:500.1-500.102
def $ibytes_(N : N, iN : iN) : byte*

;; test.spectec:500.6-500.14
relation ibytes__is_wf: `%%%`(N : N, iN : iN, `ret_val*` : byte*)
  ;; test.spectec:500.6-500.14
  rule ibytes__is_wf_0{N : N, iN : iN, `ret_val*` : byte*}:
    `%%%`(N, iN, `ret_val*`)
    -- wf_uN: `%%`(N, iN)
    -- if (`ret_val*` = $ibytes_(N, iN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:501.1-501.102
def $fbytes_(N : N, fN : fN) : byte*

;; test.spectec:501.6-501.14
relation fbytes__is_wf: `%%%`(N : N, fN : fN, `ret_val*` : byte*)
  ;; test.spectec:501.6-501.14
  rule fbytes__is_wf_0{N : N, fN : fN, `ret_val*` : byte*}:
    `%%%`(N, fN, `ret_val*`)
    -- wf_fN: `%%`(N, fN)
    -- if (`ret_val*` = $fbytes_(N, fN))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:502.1-502.75
def $bytes_(valtype : valtype, val_ : val_) : byte*

;; test.spectec:502.6-502.13
relation bytes__is_wf: `%%%`(valtype : valtype, val_ : val_, `ret_val*` : byte*)
  ;; test.spectec:502.6-502.13
  rule bytes__is_wf_0{valtype : valtype, val_ : val_, `ret_val*` : byte*}:
    `%%%`(valtype, val_, `ret_val*`)
    -- wf_val_: `%%`(valtype, val_)
    -- if (`ret_val*` = $bytes_(valtype, val_))
    -- (wf_byte: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:504.1-504.75
def $inv_ibytes_(N : N, byte*) : iN

;; test.spectec:504.6-504.18
relation inv_ibytes__is_wf: `%%%`(N : N, `var_0*` : byte*, ret_val : iN)
  ;; test.spectec:504.6-504.18
  rule inv_ibytes__is_wf_0{N : N, `var_0*` : byte*, ret_val : iN}:
    `%%%`(N, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_ibytes_(N, `var_0*`))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:505.1-505.75
def $inv_fbytes_(N : N, byte*) : fN

;; test.spectec:505.6-505.18
relation inv_fbytes__is_wf: `%%%`(N : N, `var_0*` : byte*, ret_val : fN)
  ;; test.spectec:505.6-505.18
  rule inv_fbytes__is_wf_0{N : N, `var_0*` : byte*, ret_val : fN}:
    `%%%`(N, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_fbytes_(N, `var_0*`))
    -- wf_fN: `%%`(N, ret_val)

;; test.spectec:506.1-506.73
def $inv_bytes_(valtype : valtype, byte*) : val_

;; test.spectec:506.6-506.17
relation inv_bytes__is_wf: `%%%`(valtype : valtype, `var_0*` : byte*, ret_val : val_)
  ;; test.spectec:506.6-506.17
  rule inv_bytes__is_wf_0{valtype : valtype, `var_0*` : byte*, ret_val : val_}:
    `%%%`(valtype, `var_0*`, ret_val)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $inv_bytes_(valtype, `var_0*`))
    -- wf_val_: `%%`(valtype, ret_val)

;; test.spectec:522.1-522.29
def $inot_(N : N, iN : iN) : iN

;; test.spectec:522.6-522.12
relation inot__is_wf: `%%%`(N : N, iN : iN, ret_val : iN)
  ;; test.spectec:522.6-522.12
  rule inot__is_wf_0{N : N, iN : iN, ret_val : iN}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $inot_(N, iN))
    -- wf_uN: `%%`(N, ret_val)

;; test.spectec:534.1-534.27
def $inez_(N : N, iN : iN) : u32
  ;; test.spectec:572.1-572.38
  def $inez_{N : nat, i_1 : uN}(N, i_1) = `%`_u32($bool((i_1!`%`_uN.0 =/= 0)))

;; test.spectec:534.6-534.12
relation inez__is_wf: `%%%`(N : N, iN : iN, ret_val : u32)
  ;; test.spectec:534.6-534.12
  rule inez__is_wf_0{N : N, iN : iN, ret_val : u32}:
    `%%%`(N, iN, ret_val)
    -- wf_uN: `%%`(N, iN)
    -- if (ret_val = $inez_(N, iN))
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
  | FUNC(funcaddr : funcaddr)
  | GLOBAL(globaladdr : globaladdr)
  | TABLE(tableaddr : tableaddr)
  | MEM(memaddr : memaddr)

;; test.spectec:725.1-726.55
syntax val = 
  | CONST(valtype : valtype, val_)

;; test.spectec:725.8-725.11
relation wf_val: `%`(val)
  ;; test.spectec:725.8-725.11
  rule val_case_0{valtype : valtype, var_0 : val_}:
    `%`(CONST_val(valtype, var_0))
    -- wf_val_: `%%`(valtype, var_0)

;; test.spectec:728.1-729.22
syntax result = 
  | _VALS(`val*` : val*)
  | TRAP

;; test.spectec:728.8-728.14
relation wf_result: `%`(result)
  ;; test.spectec:728.8-728.14
  rule result_case_0{`val*` : val*}:
    `%`(_VALS_result(`val*`))
    -- (wf_val: `%`(val))*{val <- `val*`}

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
  rule moduleinst_case_{`var_0*` : functype*, `var_1*` : funcaddr*, `var_2*` : globaladdr*, `var_3*` : tableaddr*, `var_4*` : memaddr*, `var_5*` : exportinst*}:
    `%`({TYPES `var_0*`, FUNCS `var_1*`, GLOBALS `var_2*`, TABLES `var_3*`, MEMS `var_4*`, EXPORTS `var_5*`})
    -- (wf_exportinst: `%`(var_5))*{var_5 <- `var_5*`}

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
  rule tableinst_case_{var_0 : tabletype, `var_1?*` : funcaddr?*}:
    `%`({TYPE var_0, REFS `var_1?*`})
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
  rule meminst_case_{var_0 : memtype, `var_1*` : byte*}:
    `%`({TYPE var_0, BYTES `var_1*`})
    -- wf_limits: `%`(var_0)
    -- (wf_byte: `%`(var_1))*{var_1 <- `var_1*`}

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
  rule store_case_{`var_0*` : funcinst*, `var_1*` : globalinst*, `var_2*` : tableinst*, `var_3*` : meminst*}:
    `%`({FUNCS `var_0*`, GLOBALS `var_1*`, TABLES `var_2*`, MEMS `var_3*`})
    -- (wf_funcinst: `%`(var_0))*{var_0 <- `var_0*`}
    -- (wf_globalinst: `%`(var_1))*{var_1 <- `var_1*`}
    -- (wf_tableinst: `%`(var_2))*{var_2 <- `var_2*`}
    -- (wf_meminst: `%`(var_3))*{var_3 <- `var_3*`}

;; test.spectec:782.1-784.24
syntax frame = 
{
  LOCALS val*,
  MODULE moduleinst
}

;; test.spectec:782.8-782.13
relation wf_frame: `%`(frame)
  ;; test.spectec:782.8-782.13
  rule frame_case_{`var_0*` : val*, var_1 : moduleinst}:
    `%`({LOCALS `var_0*`, MODULE var_1})
    -- (wf_val: `%`(var_0))*{var_0 <- `var_0*`}
    -- wf_moduleinst: `%`(var_1)

;; test.spectec:786.1-786.47
syntax state = 
  | `%;%`(store : store, frame : frame)

;; test.spectec:786.8-786.13
relation wf_state: `%`(state)
  ;; test.spectec:786.8-786.13
  rule state_case_0{store : store, frame : frame}:
    `%`(`%;%`_state(store, frame))
    -- wf_store: `%`(store)
    -- wf_frame: `%`(frame)

;; test.spectec:798.1-803.9
rec {

;; test.spectec:798.1-803.9
syntax admininstr = 
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
  | CALL_ADDR(funcaddr : funcaddr)
  | `LABEL_%{%}%`(n : n, `instr*` : instr*, `admininstr*` : admininstr*)
  | `FRAME_%{%}%`(n : n, frame : frame, `admininstr*` : admininstr*)
  | TRAP
}

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
  rule admininstr_case_4{blocktype : blocktype, `instr*` : instr*}:
    `%`(BLOCK_admininstr(blocktype, `instr*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_5{blocktype : blocktype, `instr*` : instr*}:
    `%`(LOOP_admininstr(blocktype, `instr*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_6{blocktype : blocktype, `instr*` : instr*, `instr*_0*` : instr*}:
    `%`(`IF%%ELSE%`_admininstr(blocktype, `instr*`, `instr*_0*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- (wf_instr: `%`(`instr*_0`))*{`instr*_0` <- `instr*_0*`}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_7{labelidx : labelidx}:
    `%`(BR_admininstr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_8{labelidx : labelidx}:
    `%`(BR_IF_admininstr(labelidx))
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_9{`labelidx*` : labelidx*, labelidx : labelidx}:
    `%`(BR_TABLE_admininstr(`labelidx*`, labelidx))
    -- (wf_uN: `%%`(32, labelidx))*{labelidx <- `labelidx*`}
    -- wf_uN: `%%`(32, labelidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_10{funcidx : funcidx}:
    `%`(CALL_admininstr(funcidx))
    -- wf_uN: `%%`(32, funcidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_11{typeidx : typeidx}:
    `%`(CALL_INDIRECT_admininstr(typeidx))
    -- wf_uN: `%%`(32, typeidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_12:
    `%`(RETURN_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_13{valtype : valtype, var_0 : val_}:
    `%`(CONST_admininstr(valtype, var_0))
    -- wf_val_: `%%`(valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_14{valtype : valtype, var_0 : unop_}:
    `%`(UNOP_admininstr(valtype, var_0))
    -- wf_unop_: `%%`(valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_15{valtype : valtype, var_0 : binop_}:
    `%`(BINOP_admininstr(valtype, var_0))
    -- wf_binop_: `%%`(valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_16{valtype : valtype, var_0 : testop_}:
    `%`(TESTOP_admininstr(valtype, var_0))
    -- wf_testop_: `%%`(valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_17{valtype : valtype, var_0 : relop_}:
    `%`(RELOP_admininstr(valtype, var_0))
    -- wf_relop_: `%%`(valtype, var_0)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_18{valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop}:
    `%`(CVTOP_admininstr(valtype_1, valtype_2, cvtop))
    -- if (valtype_1 =/= valtype_2)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_19{localidx : localidx}:
    `%`(`LOCAL.GET`_admininstr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_20{localidx : localidx}:
    `%`(`LOCAL.SET`_admininstr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_21{localidx : localidx}:
    `%`(`LOCAL.TEE`_admininstr(localidx))
    -- wf_uN: `%%`(32, localidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_22{globalidx : globalidx}:
    `%`(`GLOBAL.GET`_admininstr(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_23{globalidx : globalidx}:
    `%`(`GLOBAL.SET`_admininstr(globalidx))
    -- wf_uN: `%%`(32, globalidx)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_24{valtype : valtype, `var_0?` : loadop_?, memarg : memarg}:
    `%`(LOAD_admininstr(valtype, `var_0?`, memarg))
    -- (wf_loadop_: `%%`(valtype, var_0))?{var_0 <- `var_0?`}
    -- wf_memarg: `%`(memarg)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_25{`Inn?` : Inn?, `valtype?` : valtype?, valtype : valtype, `sz?` : sz?, memarg : memarg}:
    `%`(STORE_admininstr(valtype, `sz?`, memarg))
    -- (wf_sz: `%`(sz))?{sz <- `sz?`}
    -- wf_memarg: `%`(memarg)
    -- (if ((valtype = (Inn : Inn <: valtype)) /\ (sz!`%`_sz.0 < $size((Inn : Inn <: valtype)))))?{Inn <- `Inn?`, sz <- `sz?`, valtype <- `valtype?`}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_26:
    `%`(`MEMORY.SIZE`_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_27:
    `%`(`MEMORY.GROW`_admininstr)

  ;; test.spectec:798.8-798.18
  rule admininstr_case_28{funcaddr : funcaddr}:
    `%`(CALL_ADDR_admininstr(funcaddr))

  ;; test.spectec:798.8-798.18
  rule admininstr_case_29{n : n, `instr*` : instr*, `admininstr*` : admininstr*}:
    `%`(`LABEL_%{%}%`_admininstr(n, `instr*`, `admininstr*`))
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- (wf_admininstr: `%`(admininstr))*{admininstr <- `admininstr*`}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_30{n : n, frame : frame, `admininstr*` : admininstr*}:
    `%`(`FRAME_%{%}%`_admininstr(n, frame, `admininstr*`))
    -- wf_frame: `%`(frame)
    -- (wf_admininstr: `%`(admininstr))*{admininstr <- `admininstr*`}

  ;; test.spectec:798.8-798.18
  rule admininstr_case_31:
    `%`(TRAP_admininstr)
}

;; test.spectec:787.1-787.62
syntax config = 
  | `%;%`(state : state, `admininstr*` : admininstr*)

;; test.spectec:787.8-787.14
relation wf_config: `%`(config)
  ;; test.spectec:787.8-787.14
  rule config_case_0{state : state, `admininstr*` : admininstr*}:
    `%`(`%;%`_config(state, `admininstr*`))
    -- wf_state: `%`(state)
    -- (wf_admininstr: `%`(admininstr))*{admininstr <- `admininstr*`}

;; test.spectec:816.1-816.29
def $default_(valtype : valtype) : val
  ;; test.spectec:818.1-818.35
  def $default_(I32_valtype) = CONST_val(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(0)))
  ;; test.spectec:819.1-819.35
  def $default_(I64_valtype) = CONST_val(I64_valtype, mk_val__0_val_(I64_Inn, `%`_uN(0)))
  ;; test.spectec:820.1-820.44
  def $default_(F32_valtype) = CONST_val(F32_valtype, mk_val__1_val_(F32_Fnn, $fzero(32)))
  ;; test.spectec:821.1-821.44
  def $default_(F64_valtype) = CONST_val(F64_valtype, mk_val__1_val_(F64_Fnn, $fzero(64)))

;; test.spectec:816.6-816.15
relation default__is_wf: `%%`(valtype : valtype, ret_val : val)
  ;; test.spectec:816.6-816.15
  rule default__is_wf_0{valtype : valtype, ret_val : val}:
    `%%`(valtype, ret_val)
    -- if (ret_val = $default_(valtype))
    -- wf_val: `%`(ret_val)

;; test.spectec:826.1-826.63
rec {

;; test.spectec:826.1-826.63
def $funcsxa(externaddr*) : funcaddr*
  ;; test.spectec:831.1-831.24
  def $funcsxa([]) = []
  ;; test.spectec:832.1-832.47
  def $funcsxa{fa : nat, `xv*` : externaddr*}([FUNC_externaddr(fa)] ++ xv*{xv <- `xv*`}) = [fa] ++ $funcsxa(xv*{xv <- `xv*`})
  ;; test.spectec:833.1-833.59
  def $funcsxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $funcsxa(xv*{xv <- `xv*`})
}

;; test.spectec:827.1-827.65
rec {

;; test.spectec:827.1-827.65
def $globalsxa(externaddr*) : globaladdr*
  ;; test.spectec:835.1-835.26
  def $globalsxa([]) = []
  ;; test.spectec:836.1-836.53
  def $globalsxa{ga : nat, `xv*` : externaddr*}([GLOBAL_externaddr(ga)] ++ xv*{xv <- `xv*`}) = [ga] ++ $globalsxa(xv*{xv <- `xv*`})
  ;; test.spectec:837.1-837.63
  def $globalsxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $globalsxa(xv*{xv <- `xv*`})
}

;; test.spectec:828.1-828.64
rec {

;; test.spectec:828.1-828.64
def $tablesxa(externaddr*) : tableaddr*
  ;; test.spectec:839.1-839.25
  def $tablesxa([]) = []
  ;; test.spectec:840.1-840.50
  def $tablesxa{ta : nat, `xv*` : externaddr*}([TABLE_externaddr(ta)] ++ xv*{xv <- `xv*`}) = [ta] ++ $tablesxa(xv*{xv <- `xv*`})
  ;; test.spectec:841.1-841.61
  def $tablesxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $tablesxa(xv*{xv <- `xv*`})
}

;; test.spectec:829.1-829.62
rec {

;; test.spectec:829.1-829.62
def $memsxa(externaddr*) : memaddr*
  ;; test.spectec:843.1-843.23
  def $memsxa([]) = []
  ;; test.spectec:844.1-844.44
  def $memsxa{ma : nat, `xv*` : externaddr*}([MEM_externaddr(ma)] ++ xv*{xv <- `xv*`}) = [ma] ++ $memsxa(xv*{xv <- `xv*`})
  ;; test.spectec:845.1-845.57
  def $memsxa{externaddr : externaddr, `xv*` : externaddr*}([externaddr] ++ xv*{xv <- `xv*`}) = $memsxa(xv*{xv <- `xv*`})
}

;; test.spectec:855.1-855.57
def $store(state : state) : store
  ;; test.spectec:858.1-858.23
  def $store{s : store, f : frame}(`%;%`_state(s, f)) = s

;; test.spectec:855.6-855.12
relation store_is_wf: `%%`(state : state, ret_val : store)
  ;; test.spectec:855.6-855.12
  rule store_is_wf_0{state : state, ret_val : store}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $store(state))
    -- wf_store: `%`(ret_val)

;; test.spectec:856.1-856.57
def $frame(state : state) : frame
  ;; test.spectec:859.1-859.23
  def $frame{s : store, f : frame}(`%;%`_state(s, f)) = f

;; test.spectec:856.6-856.12
relation frame_is_wf: `%%`(state : state, ret_val : frame)
  ;; test.spectec:856.6-856.12
  rule frame_is_wf_0{state : state, ret_val : frame}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $frame(state))
    -- wf_frame: `%`(ret_val)

;; test.spectec:862.1-862.64
def $funcaddr(state : state) : funcaddr*
  ;; test.spectec:863.1-863.39
  def $funcaddr{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame.FUNCS_moduleinst

;; test.spectec:865.1-865.57
def $funcinst(state : state) : funcinst*
  ;; test.spectec:871.1-871.32
  def $funcinst{s : store, f : frame}(`%;%`_state(s, f)) = s.FUNCS_store

;; test.spectec:865.6-865.15
relation funcinst_is_wf: `%%`(state : state, `ret_val*` : funcinst*)
  ;; test.spectec:865.6-865.15
  rule funcinst_is_wf_0{state : state, `ret_val*` : funcinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $funcinst(state))
    -- (wf_funcinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:866.1-866.59
def $globalinst(state : state) : globalinst*
  ;; test.spectec:872.1-872.36
  def $globalinst{s : store, f : frame}(`%;%`_state(s, f)) = s.GLOBALS_store

;; test.spectec:866.6-866.17
relation globalinst_is_wf: `%%`(state : state, `ret_val*` : globalinst*)
  ;; test.spectec:866.6-866.17
  rule globalinst_is_wf_0{state : state, `ret_val*` : globalinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $globalinst(state))
    -- (wf_globalinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:867.1-867.58
def $tableinst(state : state) : tableinst*
  ;; test.spectec:873.1-873.34
  def $tableinst{s : store, f : frame}(`%;%`_state(s, f)) = s.TABLES_store

;; test.spectec:867.6-867.16
relation tableinst_is_wf: `%%`(state : state, `ret_val*` : tableinst*)
  ;; test.spectec:867.6-867.16
  rule tableinst_is_wf_0{state : state, `ret_val*` : tableinst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $tableinst(state))
    -- (wf_tableinst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:868.1-868.56
def $meminst(state : state) : meminst*
  ;; test.spectec:874.1-874.30
  def $meminst{s : store, f : frame}(`%;%`_state(s, f)) = s.MEMS_store

;; test.spectec:868.6-868.14
relation meminst_is_wf: `%%`(state : state, `ret_val*` : meminst*)
  ;; test.spectec:868.6-868.14
  rule meminst_is_wf_0{state : state, `ret_val*` : meminst*}:
    `%%`(state, `ret_val*`)
    -- wf_state: `%`(state)
    -- if (`ret_val*` = $meminst(state))
    -- (wf_meminst: `%`(ret_val))*{ret_val <- `ret_val*`}

;; test.spectec:869.1-869.58
def $moduleinst(state : state) : moduleinst
  ;; test.spectec:875.1-875.35
  def $moduleinst{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame

;; test.spectec:869.6-869.17
relation moduleinst_is_wf: `%%`(state : state, ret_val : moduleinst)
  ;; test.spectec:869.6-869.17
  rule moduleinst_is_wf_0{state : state, ret_val : moduleinst}:
    `%%`(state, ret_val)
    -- wf_state: `%`(state)
    -- if (ret_val = $moduleinst(state))
    -- wf_moduleinst: `%`(ret_val)

;; test.spectec:877.1-877.66
def $type(state : state, typeidx : typeidx) : functype
  ;; test.spectec:884.1-884.41
  def $type{s : store, f : frame, x : uN}(`%;%`_state(s, f), x) = f.MODULE_frame.TYPES_moduleinst[x!`%`_uN.0]

;; test.spectec:878.1-878.66
def $func(state : state, funcidx : funcidx) : funcinst
  ;; test.spectec:885.1-885.50
  def $func{s : store, f : frame, x : uN}(`%;%`_state(s, f), x) = s.FUNCS_store[f.MODULE_frame.FUNCS_moduleinst[x!`%`_uN.0]]

;; test.spectec:878.6-878.11
relation func_is_wf: `%%%`(state : state, funcidx : funcidx, ret_val : funcinst)
  ;; test.spectec:878.6-878.11
  rule func_is_wf_0{state : state, funcidx : funcidx, ret_val : funcinst}:
    `%%%`(state, funcidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, funcidx)
    -- if (ret_val = $func(state, funcidx))
    -- wf_funcinst: `%`(ret_val)

;; test.spectec:879.1-879.68
def $global(state : state, globalidx : globalidx) : globalinst
  ;; test.spectec:886.1-886.56
  def $global{s : store, f : frame, x : uN}(`%;%`_state(s, f), x) = s.GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[x!`%`_uN.0]]

;; test.spectec:879.6-879.13
relation global_is_wf: `%%%`(state : state, globalidx : globalidx, ret_val : globalinst)
  ;; test.spectec:879.6-879.13
  rule global_is_wf_0{state : state, globalidx : globalidx, ret_val : globalinst}:
    `%%%`(state, globalidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, globalidx)
    -- if (ret_val = $global(state, globalidx))
    -- wf_globalinst: `%`(ret_val)

;; test.spectec:880.1-880.67
def $table(state : state, tableidx : tableidx) : tableinst
  ;; test.spectec:887.1-887.53
  def $table{s : store, f : frame, x : uN}(`%;%`_state(s, f), x) = s.TABLES_store[f.MODULE_frame.TABLES_moduleinst[x!`%`_uN.0]]

;; test.spectec:880.6-880.12
relation table_is_wf: `%%%`(state : state, tableidx : tableidx, ret_val : tableinst)
  ;; test.spectec:880.6-880.12
  rule table_is_wf_0{state : state, tableidx : tableidx, ret_val : tableinst}:
    `%%%`(state, tableidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- if (ret_val = $table(state, tableidx))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:881.1-881.65
def $mem(state : state, memidx : memidx) : meminst
  ;; test.spectec:888.1-888.47
  def $mem{s : store, f : frame, x : uN}(`%;%`_state(s, f), x) = s.MEMS_store[f.MODULE_frame.MEMS_moduleinst[x!`%`_uN.0]]

;; test.spectec:881.6-881.10
relation mem_is_wf: `%%%`(state : state, memidx : memidx, ret_val : meminst)
  ;; test.spectec:881.6-881.10
  rule mem_is_wf_0{state : state, memidx : memidx, ret_val : meminst}:
    `%%%`(state, memidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, memidx)
    -- if (ret_val = $mem(state, memidx))
    -- wf_meminst: `%`(ret_val)

;; test.spectec:882.1-882.67
def $local(state : state, localidx : localidx) : val
  ;; test.spectec:889.1-889.36
  def $local{s : store, f : frame, x : uN}(`%;%`_state(s, f), x) = f.LOCALS_frame[x!`%`_uN.0]

;; test.spectec:882.6-882.12
relation local_is_wf: `%%%`(state : state, localidx : localidx, ret_val : val)
  ;; test.spectec:882.6-882.12
  rule local_is_wf_0{state : state, localidx : localidx, ret_val : val}:
    `%%%`(state, localidx, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, localidx)
    -- if (ret_val = $local(state, localidx))
    -- wf_val: `%`(ret_val)

;; test.spectec:894.1-894.89
def $with_local(state : state, localidx : localidx, val : val) : state
  ;; test.spectec:904.1-904.53
  def $with_local{s : store, f : frame, x : uN, v : val}(`%;%`_state(s, f), x, v) = `%;%`_state(s, f[LOCALS_frame[x!`%`_uN.0] = v])

;; test.spectec:894.6-894.17
relation with_local_is_wf: `%%%%`(state : state, localidx : localidx, val : val, ret_val : state)
  ;; test.spectec:894.6-894.17
  rule with_local_is_wf_0{state : state, localidx : localidx, val : val, ret_val : state}:
    `%%%%`(state, localidx, val, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, localidx)
    -- wf_val: `%`(val)
    -- if (ret_val = $with_local(state, localidx, val))
    -- wf_state: `%`(ret_val)

;; test.spectec:895.1-895.96
def $with_global(state : state, globalidx : globalidx, val : val) : state
  ;; test.spectec:905.1-905.79
  def $with_global{s : store, f : frame, x : uN, v : val}(`%;%`_state(s, f), x, v) = `%;%`_state(s[GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[x!`%`_uN.0]].VALUE_globalinst = v], f)

;; test.spectec:895.6-895.18
relation with_global_is_wf: `%%%%`(state : state, globalidx : globalidx, val : val, ret_val : state)
  ;; test.spectec:895.6-895.18
  rule with_global_is_wf_0{state : state, globalidx : globalidx, val : val, ret_val : state}:
    `%%%%`(state, globalidx, val, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, globalidx)
    -- wf_val: `%`(val)
    -- if (ret_val = $with_global(state, globalidx, val))
    -- wf_state: `%`(ret_val)

;; test.spectec:896.1-896.97
def $with_table(state : state, tableidx : tableidx, nat : nat, funcaddr : funcaddr) : state
  ;; test.spectec:906.1-906.81
  def $with_table{s : store, f : frame, x : uN, i : nat, a : nat}(`%;%`_state(s, f), x, i, a) = `%;%`_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[x!`%`_uN.0]].REFS_tableinst[i] = ?(a)], f)

;; test.spectec:896.6-896.17
relation with_table_is_wf: `%%%%%`(state : state, tableidx : tableidx, nat : nat, funcaddr : funcaddr, ret_val : state)
  ;; test.spectec:896.6-896.17
  rule with_table_is_wf_0{state : state, tableidx : tableidx, nat : nat, funcaddr : funcaddr, ret_val : state}:
    `%%%%%`(state, tableidx, nat, funcaddr, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- if (ret_val = $with_table(state, tableidx, nat, funcaddr))
    -- wf_state: `%`(ret_val)

;; test.spectec:897.1-897.89
def $with_tableinst(state : state, tableidx : tableidx, tableinst : tableinst) : state
  ;; test.spectec:907.1-907.76
  def $with_tableinst{s : store, f : frame, x : uN, ti : tableinst}(`%;%`_state(s, f), x, ti) = `%;%`_state(s[TABLES_store[f.MODULE_frame.TABLES_moduleinst[x!`%`_uN.0]] = ti], f)

;; test.spectec:897.6-897.21
relation with_tableinst_is_wf: `%%%%`(state : state, tableidx : tableidx, tableinst : tableinst, ret_val : state)
  ;; test.spectec:897.6-897.21
  rule with_tableinst_is_wf_0{state : state, tableidx : tableidx, tableinst : tableinst, ret_val : state}:
    `%%%%`(state, tableidx, tableinst, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, tableidx)
    -- wf_tableinst: `%`(tableinst)
    -- if (ret_val = $with_tableinst(state, tableidx, tableinst))
    -- wf_state: `%`(ret_val)

;; test.spectec:898.1-898.100
def $with_mem(state : state, memidx : memidx, nat : nat, nat : nat, byte*) : state
  ;; test.spectec:908.1-908.85
  def $with_mem{s : store, f : frame, x : uN, i : nat, j : nat, `b*` : byte*}(`%;%`_state(s, f), x, i, j, b*{b <- `b*`}) = `%;%`_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[x!`%`_uN.0]].BYTES_meminst[i : j] = b*{b <- `b*`}], f)

;; test.spectec:898.6-898.15
relation with_mem_is_wf: `%%%%%%`(state : state, memidx : memidx, nat : nat, nat_0 : nat, `var_0*` : byte*, ret_val : state)
  ;; test.spectec:898.6-898.15
  rule with_mem_is_wf_0{state : state, memidx : memidx, nat : nat, nat_0 : nat, `var_0*` : byte*, ret_val : state}:
    `%%%%%%`(state, memidx, nat, nat_0, `var_0*`, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, memidx)
    -- (wf_byte: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $with_mem(state, memidx, nat, nat_0, `var_0*`))
    -- wf_state: `%`(ret_val)

;; test.spectec:899.1-899.87
def $with_meminst(state : state, memidx : memidx, meminst : meminst) : state
  ;; test.spectec:909.1-909.70
  def $with_meminst{s : store, f : frame, x : uN, mi : meminst}(`%;%`_state(s, f), x, mi) = `%;%`_state(s[MEMS_store[f.MODULE_frame.MEMS_moduleinst[x!`%`_uN.0]] = mi], f)

;; test.spectec:899.6-899.19
relation with_meminst_is_wf: `%%%%`(state : state, memidx : memidx, meminst : meminst, ret_val : state)
  ;; test.spectec:899.6-899.19
  rule with_meminst_is_wf_0{state : state, memidx : memidx, meminst : meminst, ret_val : state}:
    `%%%%`(state, memidx, meminst, ret_val)
    -- wf_state: `%`(state)
    -- wf_uN: `%%`(32, memidx)
    -- wf_meminst: `%`(meminst)
    -- if (ret_val = $with_meminst(state, memidx, meminst))
    -- wf_state: `%`(ret_val)

;; test.spectec:902.1-902.94
def $with_mems_elem(state : state, nat : nat, nat : nat, nat : nat, meminst : meminst) : state
  ;; test.spectec:910.1-910.70
  def $with_mems_elem{s : store, f : frame, i : nat, n : nat, k : nat, mi : meminst}(`%;%`_state(s, f), i, n, k, mi) = `%;%`_state(s[MEMS_store[i : n][k] = mi], f)

;; test.spectec:902.6-902.21
relation with_mems_elem_is_wf: `%%%%%%`(state : state, nat : nat, nat_0 : nat, nat_1 : nat, meminst : meminst, ret_val : state)
  ;; test.spectec:902.6-902.21
  rule with_mems_elem_is_wf_0{state : state, nat : nat, nat_0 : nat, nat_1 : nat, meminst : meminst, ret_val : state}:
    `%%%%%%`(state, nat, nat_0, nat_1, meminst, ret_val)
    -- wf_state: `%`(state)
    -- wf_meminst: `%`(meminst)
    -- if (ret_val = $with_mems_elem(state, nat, nat_0, nat_1, meminst))
    -- wf_state: `%`(ret_val)

;; test.spectec:915.1-915.58
def $growtable(tableinst : tableinst, nat : nat) : tableinst?
  ;; test.spectec:918.1-922.19
  def $growtable{ti : tableinst, n : nat, ti' : tableinst, i : uN, `j?` : u32?, `a*` : addr*}(ti, n) = ?(ti')
    -- if (ti = {TYPE `[%..%]`_tabletype(i, j?{j <- `j?`}), REFS ?(a)*{a <- `a*`}})
    -- let{i' : nat} i' = (|a*{a <- `a*`}| + n)
    -- if (ti' = {TYPE `[%..%]`_tabletype(`%`_u32(i'), j?{j <- `j?`}), REFS ?(a)*{a <- `a*`} ++ ?()^n{}})
    -- (if (i' <= j!`%`_uN.0))?{j <- `j?`}
    -- wf_tableinst: `%`({TYPE `[%..%]`_tabletype(i, j?{j <- `j?`}), REFS ?(a)*{a <- `a*`}})
    -- wf_tableinst: `%`({TYPE `[%..%]`_tabletype(`%`_u32(i'), j?{j <- `j?`}), REFS ?(a)*{a <- `a*`} ++ ?()^n{}})
  def $growtable{x0 : tableinst, x1 : nat}(x0, x1) = ?()
    -- otherwise

;; test.spectec:915.6-915.16
relation growtable_is_wf: `%%%`(tableinst : tableinst, nat : nat, ret_val : tableinst)
  ;; test.spectec:915.6-915.16
  rule growtable_is_wf_0{tableinst : tableinst, nat : nat, ret_val : tableinst}:
    `%%%`(tableinst, nat, ret_val)
    -- wf_tableinst: `%`(tableinst)
    -- if (ret_val = !($growtable(tableinst, nat)))
    -- wf_tableinst: `%`(ret_val)

;; test.spectec:916.1-916.58
def $growmemory(meminst : meminst, nat : nat) : meminst?
  ;; test.spectec:924.1-928.19
  def $growmemory{mi : meminst, n : nat, mi' : meminst}(mi, n) = ?(mi')
    -- let{i : u32, `j?` : u32?, `b*` : byte*} {TYPE `[%..%]`_memtype(i, j?{j <- `j?`}), BYTES b*{b <- `b*`}} = mi
    -- let{i' : rat} i' = (((|b*{b <- `b*`}| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (n : nat <:> rat))
    -- if (mi' = {TYPE `[%..%]`_memtype(`%`_u32((i' : rat <:> nat)), j?{j <- `j?`}), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})
    -- (if (i' <= (j!`%`_uN.0 : nat <:> rat)))?{j <- `j?`}
    -- wf_meminst: `%`({TYPE `[%..%]`_memtype(i, j?{j <- `j?`}), BYTES b*{b <- `b*`}})
    -- wf_meminst: `%`({TYPE `[%..%]`_memtype(`%`_u32((i' : rat <:> nat)), j?{j <- `j?`}), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})
  def $growmemory{x0 : meminst, x1 : nat}(x0, x1) = ?()
    -- otherwise

;; test.spectec:916.6-916.17
relation growmemory_is_wf: `%%%`(meminst : meminst, nat : nat, ret_val : meminst)
  ;; test.spectec:916.6-916.17
  rule growmemory_is_wf_0{meminst : meminst, nat : nat, ret_val : meminst}:
    `%%%`(meminst, nat, ret_val)
    -- wf_meminst: `%`(meminst)
    -- if (ret_val = !($growmemory(meminst, nat)))
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
  rule context_case_{`var_0*` : functype*, `var_1*` : functype*, `var_2*` : globaltype*, `var_3*` : tabletype*, `var_4*` : memtype*, `var_5*` : valtype*, `var_6*` : resulttype*, `var_7?` : resulttype?}:
    `%`({TYPES `var_0*`, FUNCS `var_1*`, GLOBALS `var_2*`, TABLES `var_3*`, MEMS `var_4*`, LOCALS `var_5*`, LABELS `var_6*`, RETURN `var_7?`})
    -- (wf_limits: `%`(var_3))*{var_3 <- `var_3*`}
    -- (wf_limits: `%`(var_4))*{var_4 <- `var_4*`}

;; test.spectec:952.1-952.66
relation Limits_ok: `|-%:%`(limits, nat)
  ;; test.spectec:960.1-963.23
  rule _{n : n, `m?` : m?, k : nat}:
    `|-%:%`(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), k)
    -- if (n <= k)
    -- (if ((n <= m) /\ (m <= k)))?{m <- `m?`}
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))

;; test.spectec:953.1-953.64
relation Functype_ok: `|-%:OK`(functype)
  ;; test.spectec:965.1-966.23
  rule _{`t_1*` : valtype*, `t_2?` : valtype?}:
    `|-%:OK`(`%->%`_functype(t_1*{t_1 <- `t_1*`}, lift(t_2?{t_2 <- `t_2?`})))

;; test.spectec:954.1-954.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; test.spectec:968.1-969.17
  rule _{t : valtype}:
    `|-%:OK`(`%%`_globaltype(?(MUT_MUT), t))

;; test.spectec:955.1-955.65
relation Tabletype_ok: `|-%:OK`(tabletype)
  ;; test.spectec:971.1-973.38
  rule _{limits : limits}:
    `|-%:OK`(limits)
    -- Limits_ok: `|-%:%`(limits, ((((2 ^ 32) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- wf_limits: `%`(limits)

;; test.spectec:956.1-956.63
relation Memtype_ok: `|-%:OK`(memtype)
  ;; test.spectec:975.1-977.36
  rule _{limits : limits}:
    `|-%:OK`(limits)
    -- Limits_ok: `|-%:%`(limits, (2 ^ 16))
    -- wf_limits: `%`(limits)

;; test.spectec:957.1-957.66
relation Externtype_ok: `|-%:OK`(externtype)
  ;; test.spectec:980.1-982.35
  rule func{functype : functype}:
    `|-%:OK`(FUNC_externtype(functype))
    -- Functype_ok: `|-%:OK`(functype)
    -- wf_externtype: `%`(FUNC_externtype(functype))

  ;; test.spectec:984.1-986.39
  rule global{globaltype : globaltype}:
    `|-%:OK`(GLOBAL_externtype(globaltype))
    -- Globaltype_ok: `|-%:OK`(globaltype)
    -- wf_externtype: `%`(GLOBAL_externtype(globaltype))

  ;; test.spectec:988.1-990.37
  rule table{tabletype : tabletype}:
    `|-%:OK`(TABLE_externtype(tabletype))
    -- Tabletype_ok: `|-%:OK`(tabletype)
    -- wf_externtype: `%`(TABLE_externtype(tabletype))

  ;; test.spectec:992.1-994.33
  rule mem{memtype : memtype}:
    `|-%:OK`(MEM_externtype(memtype))
    -- Memtype_ok: `|-%:OK`(memtype)
    -- wf_externtype: `%`(MEM_externtype(memtype))

;; test.spectec:1004.1-1004.75
relation Limits_sub: `|-%<:%`(limits, limits)
  ;; test.spectec:1012.1-1015.21
  rule _{n_11 : n, n_12 : n, n_21 : n, n_22 : n}:
    `|-%<:%`(`[%..%]`_limits(`%`_u32(n_11), ?(`%`_u32(n_12))), `[%..%]`_limits(`%`_u32(n_21), ?(`%`_u32(n_22))))
    -- if (n_11 >= n_21)
    -- if (n_12 <= n_22)
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u32(n_11), ?(`%`_u32(n_12))))
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u32(n_21), ?(`%`_u32(n_22))))

;; test.spectec:1005.1-1005.73
relation Functype_sub: `|-%<:%`(functype, functype)
  ;; test.spectec:1017.1-1018.14
  rule _{ft : functype}:
    `|-%<:%`(ft, ft)

;; test.spectec:1006.1-1006.75
relation Globaltype_sub: `|-%<:%`(globaltype, globaltype)
  ;; test.spectec:1020.1-1021.14
  rule _{gt : globaltype}:
    `|-%<:%`(gt, gt)

;; test.spectec:1007.1-1007.74
relation Tabletype_sub: `|-%<:%`(tabletype, tabletype)
  ;; test.spectec:1023.1-1025.35
  rule _{lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(lim_1, lim_2)
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)
    -- wf_limits: `%`(lim_1)
    -- wf_limits: `%`(lim_2)

;; test.spectec:1008.1-1008.72
relation Memtype_sub: `|-%<:%`(memtype, memtype)
  ;; test.spectec:1027.1-1029.35
  rule _{lim_1 : limits, lim_2 : limits}:
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
    `%|-%:%`(C, NOP_instr, `%->%`_functype([], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(NOP_instr)

  ;; test.spectec:1086.1-1087.34
  rule unreachable{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNREACHABLE_instr)

  ;; test.spectec:1089.1-1090.23
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`_functype([t], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(DROP_instr)

  ;; test.spectec:1092.1-1093.29
  rule select{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr, `%->%`_functype([t t I32_valtype], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(SELECT_instr)

  ;; test.spectec:1098.1-1100.57
  rule block{C : context, `t?` : valtype?, `instr*` : instr*}:
    `%|-%:%`(C, BLOCK_instr(t?{t <- `t?`}, instr*{instr <- `instr*`}), `%->%`_functype([], lift(t?{t <- `t?`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t?{t <- `t?`}], RETURN ?()} +++ C, instr*{instr <- `instr*`}, `%->%`_functype([], lift(t?{t <- `t?`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BLOCK_instr(t?{t <- `t?`}, instr*{instr <- `instr*`}))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t?{t <- `t?`}], RETURN ?()})

  ;; test.spectec:1102.1-1104.59
  rule loop{C : context, `t?` : valtype?, `instr*` : instr*}:
    `%|-%:%`(C, LOOP_instr(t?{t <- `t?`}, instr*{instr <- `instr*`}), `%->%`_functype([], lift(t?{t <- `t?`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [?()], RETURN ?()} +++ C, instr*{instr <- `instr*`}, `%->%`_functype([], []))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(LOOP_instr(t?{t <- `t?`}, instr*{instr <- `instr*`}))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [?()], RETURN ?()})

  ;; test.spectec:1106.1-1109.59
  rule if{C : context, `t?` : valtype?, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}), `%->%`_functype([I32_valtype], lift(t?{t <- `t?`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t?{t <- `t?`}], RETURN ?()} +++ C, instr_1*{instr_1 <- `instr_1*`}, `%->%`_functype([], lift(t?{t <- `t?`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t?{t <- `t?`}], RETURN ?()} +++ C, instr_2*{instr_2 <- `instr_2*`}, `%->%`_functype([], lift(t?{t <- `t?`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`IF%%ELSE%`_instr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t?{t <- `t?`}], RETURN ?()})

  ;; test.spectec:1114.1-1116.25
  rule br{C : context, l : labelidx, `t_1*` : valtype*, `t?` : valtype?, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->%`_functype(t_1*{t_1 <- `t_1*`} ++ lift(t?{t <- `t?`}), t_2*{t_2 <- `t_2*`}))
    -- if (C.LABELS_context[l!`%`_uN.0] = t?{t <- `t?`})
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_instr(l))

  ;; test.spectec:1118.1-1120.25
  rule br_if{C : context, l : labelidx, `t?` : valtype?}:
    `%|-%:%`(C, BR_IF_instr(l), `%->%`_functype(lift(t?{t <- `t?`}) ++ [I32_valtype], lift(t?{t <- `t?`})))
    -- if (C.LABELS_context[l!`%`_uN.0] = t?{t <- `t?`})
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_IF_instr(l))

  ;; test.spectec:1122.1-1125.28
  rule br_table{C : context, `l*` : labelidx*, l' : labelidx, `t_1*` : valtype*, `t?` : valtype?, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l*{l <- `l*`}, l'), `%->%`_functype(t_1*{t_1 <- `t_1*`} ++ lift(t?{t <- `t?`}) ++ [I32_valtype], t_2*{t_2 <- `t_2*`}))
    -- if (t?{t <- `t?`} = C.LABELS_context[l'!`%`_uN.0])
    -- (if (t?{t <- `t?`} = C.LABELS_context[l!`%`_uN.0]))*{l <- `l*`}
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BR_TABLE_instr(l*{l <- `l*`}, l'))

  ;; test.spectec:1130.1-1132.34
  rule call{C : context, x : idx, `t_1*` : valtype*, `t_2?` : valtype?}:
    `%|-%:%`(C, CALL_instr(x), `%->%`_functype(t_1*{t_1 <- `t_1*`}, lift(t_2?{t_2 <- `t_2?`})))
    -- if (C.FUNCS_context[x!`%`_uN.0] = `%->%`_functype(t_1*{t_1 <- `t_1*`}, lift(t_2?{t_2 <- `t_2?`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_instr(x))

  ;; test.spectec:1134.1-1136.34
  rule call_indirect{C : context, x : idx, `t_1*` : valtype*, `t_2?` : valtype?}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x), `%->%`_functype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype], lift(t_2?{t_2 <- `t_2?`})))
    -- if (C.TYPES_context[x!`%`_uN.0] = `%->%`_functype(t_1*{t_1 <- `t_1*`}, lift(t_2?{t_2 <- `t_2?`})))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CALL_INDIRECT_instr(x))

  ;; test.spectec:1138.1-1140.24
  rule return{C : context, `t_1*` : valtype*, `t?` : valtype?, `t_2*` : valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->%`_functype(t_1*{t_1 <- `t_1*`} ++ lift(t?{t <- `t?`}), t_2*{t_2 <- `t_2*`}))
    -- if (C.RETURN_context = ?(t?{t <- `t?`}))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RETURN_instr)

  ;; test.spectec:1145.1-1146.30
  rule const{C : context, t : valtype, c_t : val_}:
    `%|-%:%`(C, CONST_instr(t, c_t), `%->%`_functype([], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(t, c_t))

  ;; test.spectec:1148.1-1149.30
  rule unop{C : context, t : valtype, unop_t : unop_}:
    `%|-%:%`(C, UNOP_instr(t, unop_t), `%->%`_functype([t], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(UNOP_instr(t, unop_t))

  ;; test.spectec:1151.1-1152.34
  rule binop{C : context, t : valtype, binop_t : binop_}:
    `%|-%:%`(C, BINOP_instr(t, binop_t), `%->%`_functype([t t], [t]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(BINOP_instr(t, binop_t))

  ;; test.spectec:1154.1-1155.36
  rule testop{C : context, t : valtype, testop_t : testop_}:
    `%|-%:%`(C, TESTOP_instr(t, testop_t), `%->%`_functype([t], [I32_valtype]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(TESTOP_instr(t, testop_t))

  ;; test.spectec:1157.1-1158.36
  rule relop{C : context, t : valtype, relop_t : relop_}:
    `%|-%:%`(C, RELOP_instr(t, relop_t), `%->%`_functype([t t], [I32_valtype]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(RELOP_instr(t, relop_t))

  ;; test.spectec:1162.1-1164.34
  rule `cvtop-reinterpret`{C : context, nt_1 : valtype, nt_2 : valtype}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, REINTERPRET_cvtop), `%->%`_functype([nt_2], [nt_1]))
    -- if ($size(nt_1) = $size(nt_2))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, REINTERPRET_cvtop))

  ;; test.spectec:1166.1-1167.44
  rule `cvtop-convert`{C : context, nt_1 : valtype, nt_2 : valtype, cvtop : cvtop}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, cvtop), `%->%`_functype([nt_2], [nt_1]))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CVTOP_instr(nt_1, nt_2, cvtop))

  ;; test.spectec:1172.1-1174.24
  rule `local.get`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.GET`_instr(x), `%->%`_functype([], [t]))
    -- if (C.LOCALS_context[x!`%`_uN.0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`LOCAL.GET`_instr(x))

  ;; test.spectec:1176.1-1178.24
  rule `local.set`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.SET`_instr(x), `%->%`_functype([t], []))
    -- if (C.LOCALS_context[x!`%`_uN.0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`LOCAL.SET`_instr(x))

  ;; test.spectec:1180.1-1182.24
  rule `local.tee`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.TEE`_instr(x), `%->%`_functype([t], [t]))
    -- if (C.LOCALS_context[x!`%`_uN.0] = t)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`LOCAL.TEE`_instr(x))

  ;; test.spectec:1187.1-1189.29
  rule `global.get`{C : context, x : idx, t : valtype, mut : mut}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->%`_functype([], [t]))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = `%%`_globaltype(mut, t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`GLOBAL.GET`_instr(x))

  ;; test.spectec:1191.1-1193.29
  rule `global.set`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `GLOBAL.SET`_instr(x), `%->%`_functype([t], []))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = `%%`_globaltype(?(MUT_MUT), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`GLOBAL.SET`_instr(x))

  ;; test.spectec:1198.1-1200.23
  rule `memory.size`{C : context, mt : memtype}:
    `%|-%:%`(C, `MEMORY.SIZE`_instr, `%->%`_functype([], [I32_valtype]))
    -- if (C.MEMS_context[0] = mt)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(`MEMORY.SIZE`_instr)

  ;; test.spectec:1202.1-1204.23
  rule `memory.grow`{C : context, mt : memtype}:
    `%|-%:%`(C, `MEMORY.GROW`_instr, `%->%`_functype([I32_valtype], [I32_valtype]))
    -- if (C.MEMS_context[0] = mt)
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(`MEMORY.GROW`_instr)

  ;; test.spectec:1215.1-1218.42
  rule `load-val`{C : context, t : valtype, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr(t, ?(), memarg), `%->%`_functype([I32_valtype], [t]))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_uN.0) : nat <:> rat) <= (($size(t) : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(LOAD_instr(t, ?(), memarg))

  ;; test.spectec:1220.1-1223.35
  rule `load-pack`{C : context, Inn : Inn, M : M, sx : sx, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, LOAD_instr((Inn : Inn <: valtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(M), sx))), memarg), `%->%`_functype([I32_valtype], [(Inn : Inn <: valtype)]))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_uN.0) : nat <:> rat) <= ((M : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(LOAD_instr((Inn : Inn <: valtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(M), sx))), memarg))

  ;; test.spectec:1234.1-1237.42
  rule `store-val`{C : context, t : valtype, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr(t, ?(), memarg), `%->%`_functype([I32_valtype t], []))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_uN.0) : nat <:> rat) <= (($size(t) : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(STORE_instr(t, ?(), memarg))

  ;; test.spectec:1239.1-1242.35
  rule `store-pack`{C : context, Inn : Inn, M : M, memarg : memarg, mt : memtype}:
    `%|-%:%`(C, STORE_instr((Inn : Inn <: valtype), ?(`%`_sz(M)), memarg), `%->%`_functype([I32_valtype (Inn : Inn <: valtype)], []))
    -- if (C.MEMS_context[0] = mt)
    -- if (((2 ^ memarg.ALIGN_memarg!`%`_uN.0) : nat <:> rat) <= ((M : nat <:> rat) / (8 : nat <:> rat)))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(mt)
    -- wf_instr: `%`(STORE_instr((Inn : Inn <: valtype), ?(`%`_sz(M)), memarg))

;; test.spectec:1055.1-1055.65
relation Instrs_ok: `%|-%:%`(context, instr*, functype)
  ;; test.spectec:1068.1-1069.24
  rule empty{C : context}:
    `%|-%:%`(C, [], `%->%`_functype([], []))
    -- wf_context: `%`(C)

  ;; test.spectec:1071.1-1074.45
  rule seq{C : context, instr_1 : instr, `instr_2*` : instr*, `t_1*` : valtype*, `t_3*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, [instr_1] ++ instr_2*{instr_2 <- `instr_2*`}, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_3*{t_3 <- `t_3*`}))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- Instrs_ok: `%|-%:%`(C, instr_2*{instr_2 <- `instr_2*`}, `%->%`_functype(t_2*{t_2 <- `t_2*`}, t_3*{t_3 <- `t_3*`}))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(instr_1)
    -- (wf_instr: `%`(instr_2))*{instr_2 <- `instr_2*`}

  ;; test.spectec:1076.1-1078.43
  rule frame{C : context, `instr*` : instr*, `t*` : valtype*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}, t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`}))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
}

;; test.spectec:1056.1-1056.69
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; test.spectec:1061.1-1063.40
  rule _{C : context, `instr*` : instr*, `t?` : valtype?}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, t?{t <- `t?`})
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->%`_functype([], lift(t?{t <- `t?`})))
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

;; test.spectec:1249.1-1249.79
relation Instr_const: `%|-%CONST`(context, instr)
  ;; test.spectec:1253.1-1254.25
  rule const{C : context, t : valtype, c : val_}:
    `%|-%CONST`(C, CONST_instr(t, c))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(CONST_instr(t, c))

  ;; test.spectec:1256.1-1258.25
  rule `global.get`{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, `GLOBAL.GET`_instr(x))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = `%%`_globaltype(?(), t))
    -- wf_context: `%`(C)
    -- wf_instr: `%`(`GLOBAL.GET`_instr(x))

;; test.spectec:1250.1-1250.78
relation Expr_const: `%|-%CONST`(context, expr)
  ;; test.spectec:1261.1-1262.38
  rule _{C : context, `instr*` : instr*}:
    `%|-%CONST`(C, instr*{instr <- `instr*`})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr <- `instr*`}
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}

;; test.spectec:1251.1-1251.79
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype?)
  ;; test.spectec:1265.1-1268.33
  rule _{C : context, expr : expr, `t?` : valtype?}:
    `%|-%:%CONST`(C, expr, t?{t <- `t?`})
    -- Expr_ok: `%|-%:%`(C, expr, t?{t <- `t?`})
    -- Expr_const: `%|-%CONST`(C, expr)
    -- wf_context: `%`(C)
    -- (wf_instr: `%`(expr))*{expr <- expr}

;; test.spectec:1275.1-1275.73
relation Type_ok: `|-%:%`(type, functype)
  ;; test.spectec:1287.1-1289.29
  rule _{ft : functype}:
    `|-%:%`(TYPE_type(ft), ft)
    -- Functype_ok: `|-%:OK`(ft)

;; test.spectec:1276.1-1276.73
relation Func_ok: `%|-%:%`(context, func, functype)
  ;; test.spectec:1291.1-1294.81
  rule _{C : context, x : idx, `t*` : valtype*, expr : expr, `t_1*` : valtype*, `t_2?` : valtype?}:
    `%|-%:%`(C, FUNC_func(x, LOCAL_local(t)*{t <- `t*`}, expr), `%->%`_functype(t_1*{t_1 <- `t_1*`}, lift(t_2?{t_2 <- `t_2?`})))
    -- if (C.TYPES_context[x!`%`_uN.0] = `%->%`_functype(t_1*{t_1 <- `t_1*`}, lift(t_2?{t_2 <- `t_2?`})))
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}, LABELS [t_2?{t_2 <- `t_2?`}], RETURN ?(t_2?{t_2 <- `t_2?`})}, expr, t_2?{t_2 <- `t_2?`})
    -- wf_context: `%`(C)
    -- wf_func: `%`(FUNC_func(x, LOCAL_local(t)*{t <- `t*`}, expr))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}, LABELS [t_2?{t_2 <- `t_2?`}], RETURN ?(t_2?{t_2 <- `t_2?`})})

;; test.spectec:1277.1-1277.75
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; test.spectec:1296.1-1300.40
  rule _{C : context, gt : globaltype, expr : expr, mut : mut, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(gt, expr), gt)
    -- Globaltype_ok: `|-%:OK`(gt)
    -- if (gt = `%%`_globaltype(mut, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, ?(t))
    -- wf_context: `%`(C)
    -- wf_global: `%`(GLOBAL_global(gt, expr))

;; test.spectec:1278.1-1278.74
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; test.spectec:1302.1-1304.30
  rule _{C : context, tt : tabletype}:
    `%|-%:%`(C, TABLE_table(tt), tt)
    -- Tabletype_ok: `|-%:OK`(tt)
    -- wf_context: `%`(C)
    -- wf_table: `%`(TABLE_table(tt))

;; test.spectec:1279.1-1279.72
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; test.spectec:1306.1-1308.28
  rule _{C : context, mt : memtype}:
    `%|-%:%`(C, MEMORY_mem(mt), mt)
    -- Memtype_ok: `|-%:OK`(mt)
    -- wf_context: `%`(C)
    -- wf_mem: `%`(MEMORY_mem(mt))

;; test.spectec:1280.1-1280.73
relation Elem_ok: `%|-%:OK`(context, elem)
  ;; test.spectec:1311.1-1315.27
  rule _{C : context, expr : expr, `x*` : idx*, lim : limits, `ft*` : functype*}:
    `%|-%:OK`(C, ELEM_elem(expr, x*{x <- `x*`}))
    -- if (C.TABLES_context[0] = lim)
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, ?(I32_valtype))
    -- (if (C.FUNCS_context[x!`%`_uN.0] = ft))*{ft <- `ft*`, x <- `x*`}
    -- wf_context: `%`(C)
    -- wf_limits: `%`(lim)
    -- wf_elem: `%`(ELEM_elem(expr, x*{x <- `x*`}))

;; test.spectec:1281.1-1281.73
relation Data_ok: `%|-%:OK`(context, data)
  ;; test.spectec:1318.1-1321.42
  rule _{C : context, expr : expr, `b*` : byte*, lim : limits}:
    `%|-%:OK`(C, DATA_data(expr, b*{b <- `b*`}))
    -- if (C.MEMS_context[0] = lim)
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, ?(I32_valtype))
    -- wf_context: `%`(C)
    -- wf_limits: `%`(lim)
    -- wf_data: `%`(DATA_data(expr, b*{b <- `b*`}))

;; test.spectec:1282.1-1282.74
relation Start_ok: `%|-%:OK`(context, start)
  ;; test.spectec:1323.1-1325.32
  rule _{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- if (C.FUNCS_context[x!`%`_uN.0] = `%->%`_functype([], []))
    -- wf_context: `%`(C)
    -- wf_start: `%`(START_start(x))

;; test.spectec:1330.1-1330.80
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; test.spectec:1334.1-1336.31
  rule _{C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), xt)
    -- Externtype_ok: `|-%:OK`(xt)
    -- wf_context: `%`(C)
    -- wf_import: `%`(IMPORT_import(name_1, name_2, xt))

;; test.spectec:1332.1-1332.83
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; test.spectec:1343.1-1345.24
  rule func{C : context, x : idx, ft : functype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype(ft))
    -- if (C.FUNCS_context[x!`%`_uN.0] = ft)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(FUNC_externidx(x))
    -- wf_externtype: `%`(FUNC_externtype(ft))

  ;; test.spectec:1347.1-1349.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if (C.GLOBALS_context[x!`%`_uN.0] = gt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(GLOBAL_externidx(x))
    -- wf_externtype: `%`(GLOBAL_externtype(gt))

  ;; test.spectec:1351.1-1353.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if (C.TABLES_context[x!`%`_uN.0] = tt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(TABLE_externidx(x))
    -- wf_externtype: `%`(TABLE_externtype(tt))

  ;; test.spectec:1355.1-1357.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if (C.MEMS_context[x!`%`_uN.0] = mt)
    -- wf_context: `%`(C)
    -- wf_externidx: `%`(MEM_externidx(x))
    -- wf_externtype: `%`(MEM_externtype(mt))

;; test.spectec:1331.1-1331.80
relation Export_ok: `%|-%:%`(context, export, externtype)
  ;; test.spectec:1338.1-1340.39
  rule _{C : context, name : name, externidx : externidx, xt : externtype}:
    `%|-%:%`(C, EXPORT_export(name, externidx), xt)
    -- Externidx_ok: `%|-%:%`(C, externidx, xt)
    -- wf_context: `%`(C)
    -- wf_externtype: `%`(xt)
    -- wf_export: `%`(EXPORT_export(name, externidx))

;; test.spectec:1362.1-1362.62
relation Module_ok: `|-%:OK`(module)
  ;; test.spectec:1364.1-1390.29
  rule _{`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*, `ft'*` : functype*, `ixt*` : externtype*, C' : context, `gt*` : globaltype*, C : context, `ft*` : functype*, `tt*` : tabletype*, `mt*` : memtype*, `xt*` : externtype*, `ift*` : functype*, `igt*` : globaltype*, `itt*` : tabletype*, `imt*` : memtype*}:
    `|-%:OK`(MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- (Type_ok: `|-%:%`(type, ft'))*{ft' <- `ft'*`, type <- `type*`}
    -- (Import_ok: `%|-%:%`({TYPES ft'*{ft' <- `ft'*`}, FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()}, import, ixt))*{import <- `import*`, ixt <- `ixt*`}
    -- (Global_ok: `%|-%:%`(C', global, gt))*{global <- `global*`, gt <- `gt*`}
    -- (Func_ok: `%|-%:%`(C, func, ft))*{ft <- `ft*`, func <- `func*`}
    -- (Table_ok: `%|-%:%`(C, table, tt))*{table <- `table*`, tt <- `tt*`}
    -- (Mem_ok: `%|-%:%`(C, mem, mt))*{mem <- `mem*`, mt <- `mt*`}
    -- (Elem_ok: `%|-%:OK`(C, elem))*{elem <- `elem*`}
    -- (Data_ok: `%|-%:OK`(C, data))*{data <- `data*`}
    -- (Start_ok: `%|-%:OK`(C, start))?{start <- `start?`}
    -- (Export_ok: `%|-%:%`(C, export, xt))*{export <- `export*`, xt <- `xt*`}
    -- if (|tt*{tt <- `tt*`}| <= 1)
    -- if (|mt*{mt <- `mt*`}| <= 1)
    -- if (C = {TYPES ft'*{ft' <- `ft'*`}, FUNCS ift*{ift <- `ift*`} ++ ft*{ft <- `ft*`}, GLOBALS igt*{igt <- `igt*`} ++ gt*{gt <- `gt*`}, TABLES itt*{itt <- `itt*`} ++ tt*{tt <- `tt*`}, MEMS imt*{imt <- `imt*`} ++ mt*{mt <- `mt*`}, LOCALS [], LABELS [], RETURN ?()})
    -- if (C' = {TYPES ft'*{ft' <- `ft'*`}, FUNCS ift*{ift <- `ift*`} ++ ft*{ft <- `ft*`}, GLOBALS igt*{igt <- `igt*`}, TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})
    -- if (ift*{ift <- `ift*`} = $funcsxt(ixt*{ixt <- `ixt*`}))
    -- if (igt*{igt <- `igt*`} = $globalsxt(ixt*{ixt <- `ixt*`}))
    -- if (itt*{itt <- `itt*`} = $tablesxt(ixt*{ixt <- `ixt*`}))
    -- if (imt*{imt <- `imt*`} = $memsxt(ixt*{ixt <- `ixt*`}))
    -- (wf_externtype: `%`(ixt))*{ixt <- `ixt*`}
    -- wf_context: `%`(C')
    -- wf_context: `%`(C)
    -- (wf_externtype: `%`(xt))*{xt <- `xt*`}
    -- (wf_limits: `%`(iter))*{iter <- $tablesxt(ixt*{ixt <- `ixt*`})}
    -- (wf_limits: `%`(iter))*{iter <- $memsxt(ixt*{ixt <- `ixt*`})}
    -- wf_module: `%`(MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- wf_context: `%`({TYPES ft'*{ft' <- `ft'*`}, FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})
    -- wf_context: `%`({TYPES ft'*{ft' <- `ft'*`}, FUNCS ift*{ift <- `ift*`} ++ ft*{ft <- `ft*`}, GLOBALS igt*{igt <- `igt*`} ++ gt*{gt <- `gt*`}, TABLES itt*{itt <- `itt*`} ++ tt*{tt <- `tt*`}, MEMS imt*{imt <- `imt*`} ++ mt*{mt <- `mt*`}, LOCALS [], LABELS [], RETURN ?()})
    -- wf_context: `%`({TYPES ft'*{ft' <- `ft'*`}, FUNCS ift*{ift <- `ift*`} ++ ft*{ft <- `ft*`}, GLOBALS igt*{igt <- `igt*`}, TABLES [], MEMS [], LOCALS [], LABELS [], RETURN ?()})

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
  rule drop{val : val}:
    `%~>%`([(val : val <: admininstr) DROP_admininstr], [])
    -- wf_val: `%`(val)
    -- wf_admininstr: `%`(DROP_admininstr)

  ;; test.spectec:1448.1-1450.16
  rule `select-true`{val_1 : val, val_2 : val, c : val_}:
    `%~>%`([(val_1 : val <: admininstr) (val_2 : val <: admininstr) CONST_admininstr(I32_valtype, c) SELECT_admininstr], [(val_1 : val <: admininstr)])
    -- if (!($proj_val__0(c))!`%`_uN.0 =/= 0)
    -- wf_val: `%`(val_1)
    -- wf_val: `%`(val_2)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(SELECT_admininstr)

  ;; test.spectec:1452.1-1454.14
  rule `select-false`{val_1 : val, val_2 : val, c : val_}:
    `%~>%`([(val_1 : val <: admininstr) (val_2 : val <: admininstr) CONST_admininstr(I32_valtype, c) SELECT_admininstr], [(val_2 : val <: admininstr)])
    -- if (!($proj_val__0(c))!`%`_uN.0 = 0)
    -- wf_val: `%`(val_1)
    -- wf_val: `%`(val_2)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(SELECT_admininstr)

  ;; test.spectec:1466.1-1468.16
  rule `if-true`{c : val_, `t?` : valtype?, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%~>%`([CONST_admininstr(I32_valtype, c) `IF%%ELSE%`_admininstr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})], [BLOCK_admininstr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`})])
    -- if (!($proj_val__0(c))!`%`_uN.0 =/= 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(`IF%%ELSE%`_admininstr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}))
    -- wf_admininstr: `%`(BLOCK_admininstr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}))

  ;; test.spectec:1470.1-1472.14
  rule `if-false`{c : val_, `t?` : valtype?, `instr_1*` : instr*, `instr_2*` : instr*}:
    `%~>%`([CONST_admininstr(I32_valtype, c) `IF%%ELSE%`_admininstr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})], [BLOCK_admininstr(t?{t <- `t?`}, instr_2*{instr_2 <- `instr_2*`})])
    -- if (!($proj_val__0(c))!`%`_uN.0 = 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(`IF%%ELSE%`_admininstr(t?{t <- `t?`}, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}))
    -- wf_admininstr: `%`(BLOCK_admininstr(t?{t <- `t?`}, instr_2*{instr_2 <- `instr_2*`}))

  ;; test.spectec:1475.1-1476.38
  rule `label-vals`{n : n, `instr*` : instr*, `val*` : val*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr*{instr <- `instr*`}, (val : val <: admininstr)*{val <- `val*`})], (val : val <: admininstr)*{val <- `val*`})
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, instr*{instr <- `instr*`}, (val : val <: admininstr)*{val <- `val*`}))

  ;; test.spectec:1482.1-1483.69
  rule `br-zero`{n : n, `instr'*` : instr*, `val'*` : val*, `val*` : val*, `instr*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val' : val <: admininstr)*{val' <- `val'*`} ++ (val : val <: admininstr)^n{val <- `val*`} ++ [BR_admininstr(`%`_labelidx(0))] ++ (instr : instr <: admininstr)*{instr <- `instr*`})], (val : val <: admininstr)^n{val <- `val*`} ++ (instr' : instr <: admininstr)*{instr' <- `instr'*`})
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val' : val <: admininstr)*{val' <- `val'*`} ++ (val : val <: admininstr)^n{val <- `val*`} ++ [BR_admininstr(`%`_labelidx(0))] ++ (instr : instr <: admininstr)*{instr <- `instr*`}))

  ;; test.spectec:1485.1-1486.65
  rule `br-succ`{n : n, `instr'*` : instr*, `val*` : val*, l : labelidx, `instr*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val : val <: admininstr)*{val <- `val*`} ++ [BR_admininstr(`%`_labelidx((l!`%`_uN.0 + 1)))] ++ (instr : instr <: admininstr)*{instr <- `instr*`})], (val : val <: admininstr)*{val <- `val*`} ++ [BR_admininstr(l)])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val : val <: admininstr)*{val <- `val*`} ++ [BR_admininstr(`%`_labelidx((l!`%`_uN.0 + 1)))] ++ (instr : instr <: admininstr)*{instr <- `instr*`}))
    -- wf_admininstr: `%`(BR_admininstr(l))

  ;; test.spectec:1489.1-1491.16
  rule `br_if-true`{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [BR_admininstr(l)])
    -- if (!($proj_val__0(c))!`%`_uN.0 =/= 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(BR_IF_admininstr(l))
    -- wf_admininstr: `%`(BR_admininstr(l))

  ;; test.spectec:1493.1-1495.14
  rule `br_if-false`{c : val_, l : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, c) BR_IF_admininstr(l)], [])
    -- if (!($proj_val__0(c))!`%`_uN.0 = 0)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))
    -- wf_admininstr: `%`(BR_IF_admininstr(l))

  ;; test.spectec:1498.1-1500.17
  rule `br_table-lt`{i : val_, `l*` : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, i) BR_TABLE_admininstr(l*{l <- `l*`}, l')], [BR_admininstr(l*{l <- `l*`}[!($proj_val__0(i))!`%`_uN.0])])
    -- if (!($proj_val__0(i))!`%`_uN.0 < |l*{l <- `l*`}|)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, i))
    -- wf_admininstr: `%`(BR_TABLE_admininstr(l*{l <- `l*`}, l'))
    -- wf_admininstr: `%`(BR_admininstr(l*{l <- `l*`}[!($proj_val__0(i))!`%`_uN.0]))

  ;; test.spectec:1502.1-1504.18
  rule `br_table-ge`{i : val_, `l*` : labelidx*, l' : labelidx}:
    `%~>%`([CONST_admininstr(I32_valtype, i) BR_TABLE_admininstr(l*{l <- `l*`}, l')], [BR_admininstr(l')])
    -- if (!($proj_val__0(i))!`%`_uN.0 >= |l*{l <- `l*`}|)
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, i))
    -- wf_admininstr: `%`(BR_TABLE_admininstr(l*{l <- `l*`}, l'))
    -- wf_admininstr: `%`(BR_admininstr(l'))

  ;; test.spectec:1528.1-1529.35
  rule `frame-vals`{n : n, f : frame, `val*` : val*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(n, f, (val : val <: admininstr)^n{val <- `val*`})], (val : val <: admininstr)^n{val <- `val*`})
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(n, f, (val : val <: admininstr)^n{val <- `val*`}))

  ;; test.spectec:1531.1-1532.55
  rule `return-frame`{n : n, f : frame, `val'*` : val*, `val*` : val*, `instr*` : instr*}:
    `%~>%`([`FRAME_%{%}%`_admininstr(n, f, (val' : val <: admininstr)*{val' <- `val'*`} ++ (val : val <: admininstr)^n{val <- `val*`} ++ [RETURN_admininstr] ++ (instr : instr <: admininstr)*{instr <- `instr*`})], (val : val <: admininstr)^n{val <- `val*`})
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(n, f, (val' : val <: admininstr)*{val' <- `val'*`} ++ (val : val <: admininstr)^n{val <- `val*`} ++ [RETURN_admininstr] ++ (instr : instr <: admininstr)*{instr <- `instr*`}))

  ;; test.spectec:1534.1-1535.60
  rule `return-label`{n : n, `instr'*` : instr*, `val*` : val*, `instr*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val : val <: admininstr)*{val <- `val*`} ++ [RETURN_admininstr] ++ (instr : instr <: admininstr)*{instr <- `instr*`})], (val : val <: admininstr)*{val <- `val*`} ++ [RETURN_admininstr])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, (val : val <: admininstr)*{val <- `val*`} ++ [RETURN_admininstr] ++ (instr : instr <: admininstr)*{instr <- `instr*`}))
    -- wf_admininstr: `%`(RETURN_admininstr)

  ;; test.spectec:1540.1-1542.39
  rule `trap-vals`{`val*` : val*, `instr*` : instr*}:
    `%~>%`((val : val <: admininstr)*{val <- `val*`} ++ [TRAP_admininstr] ++ (instr : instr <: admininstr)*{instr <- `instr*`}, [TRAP_admininstr])
    -- if ((val*{val <- `val*`} =/= []) \/ (instr*{instr <- `instr*`} =/= []))
    -- (wf_val: `%`(val))*{val <- `val*`}
    -- (wf_instr: `%`(instr))*{instr <- `instr*`}
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1544.1-1545.39
  rule `trap-label`{n : n, `instr'*` : instr*}:
    `%~>%`([`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, [TRAP_admininstr])], [TRAP_admininstr])
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, [TRAP_admininstr]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1547.1-1548.33
  rule `trap-frame`{n : n, f : frame}:
    `%~>%`([`FRAME_%{%}%`_admininstr(n, f, [TRAP_admininstr])], [TRAP_admininstr])
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(n, f, [TRAP_admininstr]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1569.1-1571.34
  rule `unop-val`{t : valtype, c_1 : val_, unop : unop_, c : val_}:
    `%~>%`([CONST_admininstr(t, c_1) UNOP_admininstr(t, unop)], [CONST_admininstr(t, c)])
    -- if (c <- !($unop_(t, unop, c_1)))
    -- (wf_val_: `%%`(t, iter))*{iter <- !($unop_(t, unop, c_1))}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(UNOP_admininstr(t, unop))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))

  ;; test.spectec:1573.1-1575.35
  rule `unop-trap`{t : valtype, c_1 : val_, unop : unop_}:
    `%~>%`([CONST_admininstr(t, c_1) UNOP_admininstr(t, unop)], [TRAP_admininstr])
    -- if (!($unop_(t, unop, c_1)) = [])
    -- (wf_val_: `%%`(t, iter))*{iter <- !($unop_(t, unop, c_1))}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(UNOP_admininstr(t, unop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1578.1-1580.41
  rule `binop-val`{t : valtype, c_1 : val_, c_2 : val_, binop : binop_, c : val_}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) BINOP_admininstr(t, binop)], [CONST_admininstr(t, c)])
    -- if (c <- $binop_(t, binop, c_1, c_2))
    -- (wf_val_: `%%`(t, iter))*{iter <- $binop_(t, binop, c_1, c_2)}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(BINOP_admininstr(t, binop))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))

  ;; test.spectec:1582.1-1584.42
  rule `binop-trap`{t : valtype, c_1 : val_, c_2 : val_, binop : binop_}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) BINOP_admininstr(t, binop)], [TRAP_admininstr])
    -- if ($binop_(t, binop, c_1, c_2) = [])
    -- (wf_val_: `%%`(t, iter))*{iter <- $binop_(t, binop, c_1, c_2)}
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(BINOP_admininstr(t, binop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1587.1-1589.37
  rule testop{t : valtype, c_1 : val_, testop : testop_, c : val_}:
    `%~>%`([CONST_admininstr(t, c_1) TESTOP_admininstr(t, testop)], [CONST_admininstr(I32_valtype, c)])
    -- if (c = !($testop_(t, testop, c_1)))
    -- wf_val_: `%%`(I32_valtype, !($testop_(t, testop, c_1)))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(TESTOP_admininstr(t, testop))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))

  ;; test.spectec:1591.1-1593.40
  rule relop{t : valtype, c_1 : val_, c_2 : val_, relop : relop_, c : val_}:
    `%~>%`([CONST_admininstr(t, c_1) CONST_admininstr(t, c_2) RELOP_admininstr(t, relop)], [CONST_admininstr(I32_valtype, c)])
    -- if (c = $relop_(t, relop, c_1, c_2))
    -- wf_val_: `%%`(I32_valtype, $relop_(t, relop, c_1, c_2))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_1))
    -- wf_admininstr: `%`(CONST_admininstr(t, c_2))
    -- wf_admininstr: `%`(RELOP_admininstr(t, relop))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, c))

  ;; test.spectec:1596.1-1598.44
  rule `cvtop-val`{t_1 : valtype, c_1 : val_, t_2 : valtype, cvtop : cvtop, c : val_}:
    `%~>%`([CONST_admininstr(t_1, c_1) CVTOP_admininstr(t_2, t_1, cvtop)], [CONST_admininstr(t_2, c)])
    -- if (c <- $cvtop__(t_1, t_2, cvtop, c_1))
    -- (wf_val_: `%%`(t_2, iter))*{iter <- $cvtop__(t_1, t_2, cvtop, c_1)}
    -- wf_admininstr: `%`(CONST_admininstr(t_1, c_1))
    -- wf_admininstr: `%`(CVTOP_admininstr(t_2, t_1, cvtop))
    -- wf_admininstr: `%`(CONST_admininstr(t_2, c))

  ;; test.spectec:1600.1-1602.45
  rule `cvtop-trap`{t_1 : valtype, c_1 : val_, t_2 : valtype, cvtop : cvtop}:
    `%~>%`([CONST_admininstr(t_1, c_1) CVTOP_admininstr(t_2, t_1, cvtop)], [TRAP_admininstr])
    -- if ($cvtop__(t_1, t_2, cvtop, c_1) = [])
    -- (wf_val_: `%%`(t_2, iter))*{iter <- $cvtop__(t_1, t_2, cvtop, c_1)}
    -- wf_admininstr: `%`(CONST_admininstr(t_1, c_1))
    -- wf_admininstr: `%`(CVTOP_admininstr(t_2, t_1, cvtop))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1613.1-1614.47
  rule `local.tee`{val : val, x : idx}:
    `%~>%`([(val : val <: admininstr) `LOCAL.TEE`_admininstr(x)], [(val : val <: admininstr) (val : val <: admininstr) `LOCAL.SET`_admininstr(x)])
    -- wf_val: `%`(val)
    -- wf_admininstr: `%`(`LOCAL.TEE`_admininstr(x))
    -- wf_admininstr: `%`(`LOCAL.SET`_admininstr(x))

;; test.spectec:1517.1-1519.15
relation `Step_read_before_call_indirect-trap`: `%`(config)
  ;; test.spectec:1512.1-1515.43
  rule `call_indirect-call_0`{z : state, i : val_, x : idx, a : addr}:
    `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- if ($table(z, `%`_tableidx(0)).REFS_tableinst[!($proj_val__0(i))!`%`_uN.0] = ?(a))
    -- if ($type(z, x) = $funcinst(z)[a].TYPE_funcinst)
    -- wf_tableinst: `%`($table(z, `%`_tableidx(0)))
    -- (wf_funcinst: `%`(iter))*{iter <- $funcinst(z)}
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(a))
    -- wf_uN: `%%`(32, `%`_uN(0))

;; test.spectec:1403.1-1403.77
relation Step_read: `%~>%`(config, admininstr*)
  ;; test.spectec:1459.1-1461.49
  rule block{z : state, `t?` : valtype?, `instr*` : instr*, n : n}:
    `%~>%`(`%;%`_config(z, [BLOCK_admininstr(t?{t <- `t?`}, instr*{instr <- `instr*`})]), [`LABEL_%{%}%`_admininstr(n, [], (instr : instr <: admininstr)*{instr <- `instr*`})])
    -- if (((t?{t <- `t?`} = ?()) /\ (n = 0)) \/ ((t?{t <- `t?`} =/= ?()) /\ (n = 1)))
    -- wf_config: `%`(`%;%`_config(z, [BLOCK_admininstr(t?{t <- `t?`}, instr*{instr <- `instr*`})]))
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, [], (instr : instr <: admininstr)*{instr <- `instr*`}))

  ;; test.spectec:1463.1-1464.63
  rule loop{z : state, `t?` : valtype?, `instr*` : instr*}:
    `%~>%`(`%;%`_config(z, [LOOP_admininstr(t?{t <- `t?`}, instr*{instr <- `instr*`})]), [`LABEL_%{%}%`_admininstr(0, [LOOP_instr(t?{t <- `t?`}, instr*{instr <- `instr*`})], (instr : instr <: admininstr)*{instr <- `instr*`})])
    -- wf_config: `%`(`%;%`_config(z, [LOOP_admininstr(t?{t <- `t?`}, instr*{instr <- `instr*`})]))
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(0, [LOOP_instr(t?{t <- `t?`}, instr*{instr <- `instr*`})], (instr : instr <: admininstr)*{instr <- `instr*`}))

  ;; test.spectec:1509.1-1510.47
  rule call{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [CALL_admininstr(x)]), [CALL_ADDR_admininstr($funcaddr(z)[x!`%`_uN.0])])
    -- wf_config: `%`(`%;%`_config(z, [CALL_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr($funcaddr(z)[x!`%`_uN.0]))

  ;; test.spectec:1512.1-1515.43
  rule `call_indirect-call`{z : state, i : val_, x : idx, a : addr}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]), [CALL_ADDR_admininstr(a)])
    -- if ($table(z, `%`_tableidx(0)).REFS_tableinst[!($proj_val__0(i))!`%`_uN.0] = ?(a))
    -- if ($type(z, x) = $funcinst(z)[a].TYPE_funcinst)
    -- wf_tableinst: `%`($table(z, `%`_tableidx(0)))
    -- (wf_funcinst: `%`(iter))*{iter <- $funcinst(z)}
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(a))
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1517.1-1519.15
  rule `call_indirect-trap`{z : state, i : val_, x : idx}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]), [TRAP_admininstr])
    -- ~ `Step_read_before_call_indirect-trap`: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CALL_INDIRECT_admininstr(x)]))
    -- wf_admininstr: `%`(TRAP_admininstr)

  ;; test.spectec:1521.1-1525.54
  rule call_addr{z : state, k : nat, `val*` : val*, a : addr, n : n, f : frame, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, mm : moduleinst, func : func, x : idx, `t*` : valtype*}:
    `%~>%`(`%;%`_config(z, (val : val <: admininstr)^k{val <- `val*`} ++ [CALL_ADDR_admininstr(a)]), [`FRAME_%{%}%`_admininstr(n, f, [`LABEL_%{%}%`_admininstr(n, [], (instr : instr <: admininstr)*{instr <- `instr*`})])])
    -- if ($funcinst(z)[a] = {TYPE `%->%`_functype(t_1^k{t_1 <- `t_1*`}, t_2^n{t_2 <- `t_2*`}), MODULE mm, CODE func})
    -- if (func = FUNC_func(x, LOCAL_local(t)*{t <- `t*`}, instr*{instr <- `instr*`}))
    -- if (f = {LOCALS val^k{val <- `val*`} ++ $default_(t)*{t <- `t*`}, MODULE mm})
    -- (wf_funcinst: `%`(iter))*{iter <- $funcinst(z)}
    -- wf_config: `%`(`%;%`_config(z, (val : val <: admininstr)^k{val <- `val*`} ++ [CALL_ADDR_admininstr(a)]))
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(n, f, [`LABEL_%{%}%`_admininstr(n, [], (instr : instr <: admininstr)*{instr <- `instr*`})]))
    -- wf_funcinst: `%`({TYPE `%->%`_functype(t_1^k{t_1 <- `t_1*`}, t_2^n{t_2 <- `t_2*`}), MODULE mm, CODE func})
    -- wf_func: `%`(FUNC_func(x, LOCAL_local(t)*{t <- `t*`}, instr*{instr <- `instr*`}))
    -- wf_frame: `%`({LOCALS val^k{val <- `val*`} ++ $default_(t)*{t <- `t*`}, MODULE mm})

  ;; test.spectec:1607.1-1608.37
  rule `local.get`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`LOCAL.GET`_admininstr(x)]), [($local(z, x) : val <: admininstr)])
    -- wf_val: `%`($local(z, x))
    -- wf_config: `%`(`%;%`_config(z, [`LOCAL.GET`_admininstr(x)]))

  ;; test.spectec:1619.1-1620.45
  rule `global.get`{z : state, x : idx}:
    `%~>%`(`%;%`_config(z, [`GLOBAL.GET`_admininstr(x)]), [($global(z, x).VALUE_globalinst : val <: admininstr)])
    -- wf_globalinst: `%`($global(z, x))
    -- wf_config: `%`(`%;%`_config(z, [`GLOBAL.GET`_admininstr(x)]))

  ;; test.spectec:1628.1-1630.59
  rule `load-num-trap`{z : state, i : val_, t : valtype, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]), [TRAP_admininstr])
    -- if (((!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0) + ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]))
    -- wf_admininstr: `%`(TRAP_admininstr)
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1632.1-1634.69
  rule `load-num-val`{z : state, i : val_, t : valtype, ao : memarg, c : val_}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]), [CONST_admininstr(t, c)])
    -- if ($bytes_(t, c) = $mem(z, `%`_memidx(0)).BYTES_meminst[(!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0) : ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- (wf_byte: `%`(iter))*{iter <- $bytes_(t, c)}
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr(t, ?(), ao)]))
    -- wf_admininstr: `%`(CONST_admininstr(t, c))
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1636.1-1638.52
  rule `load-pack-trap`{z : state, i : val_, Inn : Inn, n : n, sx : sx, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr((Inn : Inn <: valtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(n), sx))), ao)]), [TRAP_admininstr])
    -- if (((!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0) + (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr((Inn : Inn <: valtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(n), sx))), ao)]))
    -- wf_admininstr: `%`(TRAP_admininstr)
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1640.1-1642.63
  rule `load-pack-val`{z : state, i : val_, Inn : Inn, n : n, sx : sx, ao : memarg, c : iN}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr((Inn : Inn <: valtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(n), sx))), ao)]), [CONST_admininstr((Inn : Inn <: valtype), mk_val__0_val_(Inn, $extend__(n, $size((Inn : Inn <: valtype)), sx, c)))])
    -- if ($ibytes_(n, c) = $mem(z, `%`_memidx(0)).BYTES_meminst[(!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0) : (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)])
    -- (wf_byte: `%`(iter))*{iter <- $ibytes_(n, c)}
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) LOAD_admininstr((Inn : Inn <: valtype), ?(mk_loadop__0_loadop_(Inn, `%_%`_loadop_Inn(`%`_sz(n), sx))), ao)]))
    -- wf_admininstr: `%`(CONST_admininstr((Inn : Inn <: valtype), mk_val__0_val_(Inn, $extend__(n, $size((Inn : Inn <: valtype)), sx, c))))
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1662.1-1664.45
  rule `memory.size`{z : state, n : n}:
    `%~>%`(`%;%`_config(z, [`MEMORY.SIZE`_admininstr]), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(n)))])
    -- if (((n * 64) * $Ki) = |$mem(z, `%`_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [`MEMORY.SIZE`_admininstr]))
    -- wf_admininstr: `%`(CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(n))))
    -- wf_uN: `%%`(32, `%`_uN(0))

;; test.spectec:1401.1-1401.77
rec {

;; test.spectec:1401.1-1401.77
relation Step: `%~>%`(config, config)
  ;; test.spectec:1406.1-1408.44
  rule pure{z : state, `admininstr*` : admininstr*, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z, admininstr'*{admininstr' <- `admininstr'*`}))
    -- Step_pure: `%~>%`(admininstr*{admininstr <- `admininstr*`}, admininstr'*{admininstr' <- `admininstr'*`})
    -- wf_config: `%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(z, admininstr'*{admininstr' <- `admininstr'*`}))

  ;; test.spectec:1410.1-1412.47
  rule read{z : state, `admininstr*` : admininstr*, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z, admininstr'*{admininstr' <- `admininstr'*`}))
    -- Step_read: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), admininstr'*{admininstr' <- `admininstr'*`})
    -- wf_config: `%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(z, admininstr'*{admininstr' <- `admininstr'*`}))

  ;; test.spectec:1553.1-1555.46
  rule `ctxt-label`{z : state, n : n, `instr_0*` : instr*, `admininstr*` : admininstr*, z' : state, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, [`LABEL_%{%}%`_admininstr(n, instr_0*{instr_0 <- `instr_0*`}, admininstr*{admininstr <- `admininstr*`})]), `%;%`_config(z', [`LABEL_%{%}%`_admininstr(n, instr_0*{instr_0 <- `instr_0*`}, admininstr'*{admininstr' <- `admininstr'*`})]))
    -- Step: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))
    -- wf_config: `%`(`%;%`_config(z, [`LABEL_%{%}%`_admininstr(n, instr_0*{instr_0 <- `instr_0*`}, admininstr*{admininstr <- `admininstr*`})]))
    -- wf_config: `%`(`%;%`_config(z', [`LABEL_%{%}%`_admininstr(n, instr_0*{instr_0 <- `instr_0*`}, admininstr'*{admininstr' <- `admininstr'*`})]))
    -- wf_config: `%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))

  ;; test.spectec:1557.1-1559.55
  rule `ctxt-frame`{s : store, f : frame, n : n, f' : frame, `admininstr*` : admininstr*, s' : store, f'' : frame, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(`%;%`_state(s, f), [`FRAME_%{%}%`_admininstr(n, f', admininstr*{admininstr <- `admininstr*`})]), `%;%`_config(`%;%`_state(s', f), [`FRAME_%{%}%`_admininstr(n, f'', admininstr'*{admininstr' <- `admininstr'*`})]))
    -- Step: `%~>%`(`%;%`_config(`%;%`_state(s, f'), admininstr*{admininstr <- `admininstr*`}), `%;%`_config(`%;%`_state(s', f''), admininstr'*{admininstr' <- `admininstr'*`}))
    -- wf_config: `%`(`%;%`_config(`%;%`_state(s, f), [`FRAME_%{%}%`_admininstr(n, f', admininstr*{admininstr <- `admininstr*`})]))
    -- wf_config: `%`(`%;%`_config(`%;%`_state(s', f), [`FRAME_%{%}%`_admininstr(n, f'', admininstr'*{admininstr' <- `admininstr'*`})]))
    -- wf_config: `%`(`%;%`_config(`%;%`_state(s, f'), admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(`%;%`_state(s', f''), admininstr'*{admininstr' <- `admininstr'*`}))

  ;; test.spectec:1561.1-1564.46
  rule `ctxt-instrs`{z : state, `val*` : val*, `admininstr*` : admininstr*, `admininstr_1*` : admininstr*, z' : state, `admininstr'*` : admininstr*}:
    `%~>%`(`%;%`_config(z, (val : val <: admininstr)*{val <- `val*`} ++ admininstr*{admininstr <- `admininstr*`} ++ admininstr_1*{admininstr_1 <- `admininstr_1*`}), `%;%`_config(z', (val : val <: admininstr)*{val <- `val*`} ++ admininstr'*{admininstr' <- `admininstr'*`} ++ admininstr_1*{admininstr_1 <- `admininstr_1*`}))
    -- Step: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))
    -- if ((val*{val <- `val*`} =/= []) \/ (admininstr_1*{admininstr_1 <- `admininstr_1*`} =/= []))
    -- wf_config: `%`(`%;%`_config(z, (val : val <: admininstr)*{val <- `val*`} ++ admininstr*{admininstr <- `admininstr*`} ++ admininstr_1*{admininstr_1 <- `admininstr_1*`}))
    -- wf_config: `%`(`%;%`_config(z', (val : val <: admininstr)*{val <- `val*`} ++ admininstr'*{admininstr' <- `admininstr'*`} ++ admininstr_1*{admininstr_1 <- `admininstr_1*`}))
    -- wf_config: `%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))

  ;; test.spectec:1610.1-1611.56
  rule `local.set`{z : state, val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [(val : val <: admininstr) `LOCAL.SET`_admininstr(x)]), `%;%`_config($with_local(z, x, val), []))
    -- wf_config: `%`(`%;%`_config(z, [(val : val <: admininstr) `LOCAL.SET`_admininstr(x)]))
    -- wf_config: `%`(`%;%`_config($with_local(z, x, val), []))

  ;; test.spectec:1622.1-1623.58
  rule `global.set`{z : state, val : val, x : idx}:
    `%~>%`(`%;%`_config(z, [(val : val <: admininstr) `GLOBAL.SET`_admininstr(x)]), `%;%`_config($with_global(z, x, val), []))
    -- wf_config: `%`(`%;%`_config(z, [(val : val <: admininstr) `GLOBAL.SET`_admininstr(x)]))
    -- wf_config: `%`(`%;%`_config($with_global(z, x, val), []))

  ;; test.spectec:1645.1-1647.59
  rule `store-num-trap`{z : state, i : val_, t : valtype, c : val_, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (((!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0) + ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]))
    -- wf_config: `%`(`%;%`_config(z, [TRAP_admininstr]))
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1649.1-1651.27
  rule `store-num-val`{z : state, i : val_, t : valtype, c : val_, ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]), `%;%`_config($with_mem(z, `%`_memidx(0), (!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0), ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $bytes_(t, c))
    -- (wf_byte: `%`(iter))*{iter <- $bytes_(t, c)}
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr(t, c) STORE_admininstr(t, ?(), ao)]))
    -- wf_config: `%`(`%;%`_config($with_mem(z, `%`_memidx(0), (!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0), ((($size(t) : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))

  ;; test.spectec:1653.1-1655.52
  rule `store-pack-trap`{z : state, i : val_, Inn : Inn, c : val_, n : n, ao : memarg}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr((Inn : Inn <: valtype), c) STORE_admininstr((Inn : Inn <: valtype), ?(`%`_sz(n)), ao)]), `%;%`_config(z, [TRAP_admininstr]))
    -- if (((!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0) + (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat)) > |$mem(z, `%`_memidx(0)).BYTES_meminst|)
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr((Inn : Inn <: valtype), c) STORE_admininstr((Inn : Inn <: valtype), ?(`%`_sz(n)), ao)]))
    -- wf_config: `%`(`%;%`_config(z, [TRAP_admininstr]))
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1657.1-1659.52
  rule `store-pack-val`{z : state, i : val_, Inn : Inn, c : val_, n : n, ao : memarg, `b*` : byte*}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr((Inn : Inn <: valtype), c) STORE_admininstr((Inn : Inn <: valtype), ?(`%`_sz(n)), ao)]), `%;%`_config($with_mem(z, `%`_memidx(0), (!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0), (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))
    -- if (b*{b <- `b*`} = $ibytes_(n, $wrap__($size((Inn : Inn <: valtype)), n, !($proj_val__0(c)))))
    -- (wf_byte: `%`(iter))*{iter <- $ibytes_(n, $wrap__($size((Inn : Inn <: valtype)), n, !($proj_val__0(c))))}
    -- wf_uN: `%%`(n, $wrap__($size((Inn : Inn <: valtype)), n, !($proj_val__0(c))))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, i) CONST_admininstr((Inn : Inn <: valtype), c) STORE_admininstr((Inn : Inn <: valtype), ?(`%`_sz(n)), ao)]))
    -- wf_config: `%`(`%;%`_config($with_mem(z, `%`_memidx(0), (!($proj_val__0(i))!`%`_uN.0 + ao.OFFSET_memarg!`%`_uN.0), (((n : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat), b*{b <- `b*`}), []))

  ;; test.spectec:1667.1-1669.40
  rule `memory.grow-succeed`{z : state, n : n, mi : meminst}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(n))) `MEMORY.GROW`_admininstr]), `%;%`_config($with_meminst(z, `%`_memidx(0), mi), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN((((|$mem(z, `%`_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat))))]))
    -- if (!($growmemory($mem(z, `%`_memidx(0)), n)) = mi)
    -- wf_meminst: `%`(!($growmemory($mem(z, `%`_memidx(0)), n)))
    -- wf_meminst: `%`($mem(z, `%`_memidx(0)))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(n))) `MEMORY.GROW`_admininstr]))
    -- wf_config: `%`(`%;%`_config($with_meminst(z, `%`_memidx(0), mi), [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN((((|$mem(z, `%`_memidx(0)).BYTES_meminst| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) : rat <:> nat))))]))
    -- wf_uN: `%%`(32, `%`_uN(0))

  ;; test.spectec:1671.1-1672.77
  rule `memory.grow-fail`{z : state, n : n}:
    `%~>%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(n))) `MEMORY.GROW`_admininstr]), `%;%`_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN($inv_signed_(32, - (1 : nat <:> int)))))]))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN(n))) `MEMORY.GROW`_admininstr]))
    -- wf_config: `%`(`%;%`_config(z, [CONST_admininstr(I32_valtype, mk_val__0_val_(I32_Inn, `%`_uN($inv_signed_(32, - (1 : nat <:> int)))))]))
}

;; test.spectec:1404.1-1404.77
rec {

;; test.spectec:1404.1-1404.77
relation Steps: `%~>*%`(config, config)
  ;; test.spectec:1414.1-1415.36
  rule refl{z : state, `admininstr*` : admininstr*}:
    `%~>*%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))

  ;; test.spectec:1417.1-1420.54
  rule trans{z : state, `admininstr*` : admininstr*, z'' : state, `admininstr''*` : admininstr*, z' : state, `admininstr'*` : admininstr*}:
    `%~>*%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z'', admininstr''*{admininstr'' <- `admininstr''*`}))
    -- Step: `%~>%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}), `%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))
    -- Steps: `%~>*%`(`%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}), `%;%`_config(z'', admininstr''*{admininstr'' <- `admininstr''*`}))
    -- wf_config: `%`(`%;%`_config(z, admininstr*{admininstr <- `admininstr*`}))
    -- wf_config: `%`(`%;%`_config(z'', admininstr''*{admininstr'' <- `admininstr''*`}))
    -- wf_config: `%`(`%;%`_config(z', admininstr'*{admininstr' <- `admininstr'*`}))
}

;; test.spectec:1425.1-1425.83
relation Eval_expr: `%;%~>*%;%`(state, expr, state, val*)
  ;; test.spectec:1427.1-1429.37
  rule _{z : state, `instr*` : instr*, z' : state, `val*` : val*}:
    `%;%~>*%;%`(z, instr*{instr <- `instr*`}, z', val*{val <- `val*`})
    -- Steps: `%~>*%`(`%;%`_config(z, (instr : instr <: admininstr)*{instr <- `instr*`}), `%;%`_config(z', (val : val <: admininstr)*{val <- `val*`}))
    -- wf_config: `%`(`%;%`_config(z, (instr : instr <: admininstr)*{instr <- `instr*`}))
    -- wf_config: `%`(`%;%`_config(z', (val : val <: admininstr)*{val <- `val*`}))

;; test.spectec:1683.1-1683.36
rec {

;; test.spectec:1683.1-1683.36
def $funcs(externaddr*) : funcaddr*
  ;; test.spectec:1684.1-1684.22
  def $funcs([]) = []
  ;; test.spectec:1685.1-1685.61
  def $funcs{fa : nat, `externaddr'*` : externaddr*}([FUNC_externaddr(fa)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [fa] ++ $funcs(externaddr'*{externaddr' <- `externaddr'*`})
  ;; test.spectec:1686.1-1687.15
  def $funcs{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $funcs(externaddr'*{externaddr' <- `externaddr'*`})
}

;; test.spectec:1689.1-1689.40
rec {

;; test.spectec:1689.1-1689.40
def $globals(externaddr*) : globaladdr*
  ;; test.spectec:1690.1-1690.24
  def $globals([]) = []
  ;; test.spectec:1691.1-1691.67
  def $globals{ga : nat, `externaddr'*` : externaddr*}([GLOBAL_externaddr(ga)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [ga] ++ $globals(externaddr'*{externaddr' <- `externaddr'*`})
  ;; test.spectec:1692.1-1693.15
  def $globals{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $globals(externaddr'*{externaddr' <- `externaddr'*`})
}

;; test.spectec:1695.1-1695.38
rec {

;; test.spectec:1695.1-1695.38
def $tables(externaddr*) : tableaddr*
  ;; test.spectec:1696.1-1696.23
  def $tables([]) = []
  ;; test.spectec:1697.1-1697.64
  def $tables{ta : nat, `externaddr'*` : externaddr*}([TABLE_externaddr(ta)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [ta] ++ $tables(externaddr'*{externaddr' <- `externaddr'*`})
  ;; test.spectec:1698.1-1699.15
  def $tables{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $tables(externaddr'*{externaddr' <- `externaddr'*`})
}

;; test.spectec:1701.1-1701.34
rec {

;; test.spectec:1701.1-1701.34
def $mems(externaddr*) : memaddr*
  ;; test.spectec:1702.1-1702.21
  def $mems([]) = []
  ;; test.spectec:1703.1-1703.58
  def $mems{ma : nat, `externaddr'*` : externaddr*}([MEM_externaddr(ma)] ++ externaddr'*{externaddr' <- `externaddr'*`}) = [ma] ++ $mems(externaddr'*{externaddr' <- `externaddr'*`})
  ;; test.spectec:1704.1-1705.15
  def $mems{externaddr : externaddr, `externaddr'*` : externaddr*}([externaddr] ++ externaddr'*{externaddr' <- `externaddr'*`}) = $mems(externaddr'*{externaddr' <- `externaddr'*`})
}

;; test.spectec:1714.1-1714.60
def $allocfunc(store : store, moduleinst : moduleinst, func : func) : (store, funcaddr)
  ;; test.spectec:1715.1-1717.34
  def $allocfunc{s : store, moduleinst : moduleinst, func : func, fi : funcinst, x : uN, `local*` : local*, expr : instr*}(s, moduleinst, func) = (s[FUNCS_store =++ [fi]], |s.FUNCS_store|)
    -- if (fi = {TYPE moduleinst.TYPES_moduleinst[x!`%`_uN.0], MODULE moduleinst, CODE func})
    -- if (func = FUNC_func(x, local*{local <- `local*`}, expr))
    -- wf_funcinst: `%`({TYPE moduleinst.TYPES_moduleinst[x!`%`_uN.0], MODULE moduleinst, CODE func})
    -- wf_func: `%`(FUNC_func(x, local*{local <- `local*`}, expr))

;; test.spectec:1714.6-1714.16
relation allocfunc_is_wf: `%%%%`(store : store, moduleinst : moduleinst, func : func, ret_val : (store, funcaddr))
  ;; test.spectec:1714.6-1714.16
  rule allocfunc_is_wf_0{store : store, moduleinst : moduleinst, func : func, ret_val : (store, funcaddr)}:
    `%%%%`(store, moduleinst, func, ret_val)
    -- wf_store: `%`(store)
    -- wf_moduleinst: `%`(moduleinst)
    -- wf_func: `%`(func)
    -- if (ret_val = $allocfunc(store, moduleinst, func))
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1719.1-1719.63
rec {

;; test.spectec:1719.1-1719.63
def $allocfuncs(store : store, moduleinst : moduleinst, func*) : (store, funcaddr*)
  ;; test.spectec:1720.1-1720.47
  def $allocfuncs{s : store, moduleinst : moduleinst}(s, moduleinst, []) = (s, [])
  ;; test.spectec:1721.1-1723.59
  def $allocfuncs{s : store, moduleinst : moduleinst, func : func, `func'*` : func*}(s, moduleinst, [func] ++ func'*{func' <- `func'*`}) = (s_2, [fa] ++ fa'*{fa' <- `fa'*`})
    -- let{fa : funcaddr, s_1 : store} (s_1, fa) = $allocfunc(s, moduleinst, func)
    -- let{s_2 : store, `fa'*` : funcaddr*} (s_2, fa'*{fa' <- `fa'*`}) = $allocfuncs(s_1, moduleinst, func'*{func' <- `func'*`})
}

;; test.spectec:1719.1-1719.63
rec {

;; test.spectec:1719.6-1719.17
relation allocfuncs_is_wf: `%%%%`(store : store, moduleinst : moduleinst, `var_0*` : func*, ret_val : (store, funcaddr*))
  ;; test.spectec:1719.6-1719.17
  rule allocfuncs_is_wf_0{store : store, moduleinst : moduleinst, `var_0*` : func*, ret_val : (store, funcaddr*)}:
    `%%%%`(store, moduleinst, `var_0*`, ret_val)
    -- wf_store: `%`(store)
    -- wf_moduleinst: `%`(moduleinst)
    -- (wf_func: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $allocfuncs(store, moduleinst, `var_0*`))
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1725.1-1725.63
def $allocglobal(store : store, globaltype : globaltype, val : val) : (store, globaladdr)
  ;; test.spectec:1726.1-1727.44
  def $allocglobal{s : store, globaltype : globaltype, val : val, gi : globalinst}(s, globaltype, val) = (s[GLOBALS_store =++ [gi]], |s.GLOBALS_store|)
    -- if (gi = {TYPE globaltype, VALUE val})
    -- wf_globalinst: `%`({TYPE globaltype, VALUE val})

;; test.spectec:1725.6-1725.18
relation allocglobal_is_wf: `%%%%`(store : store, globaltype : globaltype, val : val, ret_val : (store, globaladdr))
  ;; test.spectec:1725.6-1725.18
  rule allocglobal_is_wf_0{store : store, globaltype : globaltype, val : val, ret_val : (store, globaladdr)}:
    `%%%%`(store, globaltype, val, ret_val)
    -- wf_store: `%`(store)
    -- wf_val: `%`(val)
    -- if (ret_val = $allocglobal(store, globaltype, val))
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1729.1-1729.67
rec {

;; test.spectec:1729.1-1729.67
def $allocglobals(store : store, globaltype*, val*) : (store, globaladdr*)
  ;; test.spectec:1730.1-1730.42
  def $allocglobals{s : store}(s, [], []) = (s, [])
  ;; test.spectec:1731.1-1733.62
  def $allocglobals{s : store, globaltype : globaltype, `globaltype'*` : globaltype*, val : val, `val'*` : val*}(s, [globaltype] ++ globaltype'*{globaltype' <- `globaltype'*`}, [val] ++ val'*{val' <- `val'*`}) = (s_2, [ga] ++ ga'*{ga' <- `ga'*`})
    -- let{ga : globaladdr, s_1 : store} (s_1, ga) = $allocglobal(s, globaltype, val)
    -- let{s_2 : store, `ga'*` : globaladdr*} (s_2, ga'*{ga' <- `ga'*`}) = $allocglobals(s_1, globaltype'*{globaltype' <- `globaltype'*`}, val'*{val' <- `val'*`})
}

;; test.spectec:1729.1-1729.67
rec {

;; test.spectec:1729.6-1729.19
relation allocglobals_is_wf: `%%%%`(store : store, `var_0*` : globaltype*, `var_1*` : val*, ret_val : (store, globaladdr*))
  ;; test.spectec:1729.6-1729.19
  rule allocglobals_is_wf_0{store : store, `var_0*` : globaltype*, `var_1*` : val*, ret_val : (store, globaladdr*)}:
    `%%%%`(store, `var_0*`, `var_1*`, ret_val)
    -- wf_store: `%`(store)
    -- (wf_val: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $allocglobals(store, `var_0*`, `var_1*`))
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1735.1-1735.55
def $alloctable(store : store, tabletype : tabletype) : (store, tableaddr)
  ;; test.spectec:1736.1-1737.45
  def $alloctable{s : store, i : uN, `j?` : u32?, ti : tableinst}(s, `[%..%]`_tabletype(i, j?{j <- `j?`})) = (s[TABLES_store =++ [ti]], |s.TABLES_store|)
    -- if (ti = {TYPE `[%..%]`_tabletype(i, j?{j <- `j?`}), REFS ?()^i!`%`_uN.0{}})
    -- wf_tableinst: `%`({TYPE `[%..%]`_tabletype(i, j?{j <- `j?`}), REFS ?()^i!`%`_uN.0{}})

;; test.spectec:1735.6-1735.17
relation alloctable_is_wf: `%%%`(store : store, tabletype : tabletype, ret_val : (store, tableaddr))
  ;; test.spectec:1735.6-1735.17
  rule alloctable_is_wf_0{store : store, tabletype : tabletype, ret_val : (store, tableaddr)}:
    `%%%`(store, tabletype, ret_val)
    -- wf_store: `%`(store)
    -- wf_limits: `%`(tabletype)
    -- if (ret_val = $alloctable(store, tabletype))
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1739.1-1739.58
rec {

;; test.spectec:1739.1-1739.58
def $alloctables(store : store, tabletype*) : (store, tableaddr*)
  ;; test.spectec:1740.1-1740.36
  def $alloctables{s : store}(s, []) = (s, [])
  ;; test.spectec:1741.1-1743.53
  def $alloctables{s : store, tabletype : limits, `tabletype'*` : tabletype*}(s, [tabletype] ++ tabletype'*{tabletype' <- `tabletype'*`}) = (s_2, [ta] ++ ta'*{ta' <- `ta'*`})
    -- let{ta : tableaddr, s_1 : store} (s_1, ta) = $alloctable(s, tabletype)
    -- let{s_2 : store, `ta'*` : tableaddr*} (s_2, ta'*{ta' <- `ta'*`}) = $alloctables(s_1, tabletype'*{tabletype' <- `tabletype'*`})
}

;; test.spectec:1739.1-1739.58
rec {

;; test.spectec:1739.6-1739.18
relation alloctables_is_wf: `%%%`(store : store, `var_0*` : tabletype*, ret_val : (store, tableaddr*))
  ;; test.spectec:1739.6-1739.18
  rule alloctables_is_wf_0{store : store, `var_0*` : tabletype*, ret_val : (store, tableaddr*)}:
    `%%%`(store, `var_0*`, ret_val)
    -- wf_store: `%`(store)
    -- (wf_limits: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $alloctables(store, `var_0*`))
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1745.1-1745.49
def $allocmem(store : store, memtype : memtype) : (store, memaddr)
  ;; test.spectec:1746.1-1747.63
  def $allocmem{s : store, i : uN, `j?` : u32?, mi : meminst}(s, `[%..%]`_memtype(i, j?{j <- `j?`})) = (s[MEMS_store =++ [mi]], |s.MEMS_store|)
    -- if (mi = {TYPE `[%..%]`_memtype(i, j?{j <- `j?`}), BYTES `%`_byte(0)^(i!`%`_uN.0 * (64 * $Ki)){}})
    -- wf_meminst: `%`({TYPE `[%..%]`_memtype(i, j?{j <- `j?`}), BYTES `%`_byte(0)^(i!`%`_uN.0 * (64 * $Ki)){}})

;; test.spectec:1745.6-1745.15
relation allocmem_is_wf: `%%%`(store : store, memtype : memtype, ret_val : (store, memaddr))
  ;; test.spectec:1745.6-1745.15
  rule allocmem_is_wf_0{store : store, memtype : memtype, ret_val : (store, memaddr)}:
    `%%%`(store, memtype, ret_val)
    -- wf_store: `%`(store)
    -- wf_limits: `%`(memtype)
    -- if (ret_val = $allocmem(store, memtype))
    -- wf_store: `%`(ret_val.0)

;; test.spectec:1749.1-1749.52
rec {

;; test.spectec:1749.1-1749.52
def $allocmems(store : store, memtype*) : (store, memaddr*)
  ;; test.spectec:1750.1-1750.34
  def $allocmems{s : store}(s, []) = (s, [])
  ;; test.spectec:1751.1-1753.49
  def $allocmems{s : store, memtype : limits, `memtype'*` : memtype*}(s, [memtype] ++ memtype'*{memtype' <- `memtype'*`}) = (s_2, [ma] ++ ma'*{ma' <- `ma'*`})
    -- let{ma : memaddr, s_1 : store} (s_1, ma) = $allocmem(s, memtype)
    -- let{s_2 : store, `ma'*` : memaddr*} (s_2, ma'*{ma' <- `ma'*`}) = $allocmems(s_1, memtype'*{memtype' <- `memtype'*`})
}

;; test.spectec:1749.1-1749.52
rec {

;; test.spectec:1749.6-1749.16
relation allocmems_is_wf: `%%%`(store : store, `var_0*` : memtype*, ret_val : (store, memaddr*))
  ;; test.spectec:1749.6-1749.16
  rule allocmems_is_wf_0{store : store, `var_0*` : memtype*, ret_val : (store, memaddr*)}:
    `%%%`(store, `var_0*`, ret_val)
    -- wf_store: `%`(store)
    -- (wf_limits: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $allocmems(store, `var_0*`))
    -- wf_store: `%`(ret_val.0)
}

;; test.spectec:1758.1-1758.83
def $instexport(funcaddr*, globaladdr*, tableaddr*, memaddr*, export : export) : exportinst
  ;; test.spectec:1759.1-1759.94
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : uN}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, FUNC_externidx(x))) = {NAME name, ADDR FUNC_externaddr(fa*{fa <- `fa*`}[x!`%`_uN.0])}
  ;; test.spectec:1760.1-1760.98
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : uN}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, GLOBAL_externidx(x))) = {NAME name, ADDR GLOBAL_externaddr(ga*{ga <- `ga*`}[x!`%`_uN.0])}
  ;; test.spectec:1761.1-1761.96
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : uN}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, TABLE_externidx(x))) = {NAME name, ADDR TABLE_externaddr(ta*{ta <- `ta*`}[x!`%`_uN.0])}
  ;; test.spectec:1762.1-1762.92
  def $instexport{`fa*` : funcaddr*, `ga*` : globaladdr*, `ta*` : tableaddr*, `ma*` : memaddr*, name : name, x : uN}(fa*{fa <- `fa*`}, ga*{ga <- `ga*`}, ta*{ta <- `ta*`}, ma*{ma <- `ma*`}, EXPORT_export(name, MEM_externidx(x))) = {NAME name, ADDR MEM_externaddr(ma*{ma <- `ma*`}[x!`%`_uN.0])}

;; test.spectec:1758.6-1758.17
relation instexport_is_wf: `%%%%%%`(`var_0*` : funcaddr*, `var_1*` : globaladdr*, `var_2*` : tableaddr*, `var_3*` : memaddr*, export : export, ret_val : exportinst)
  ;; test.spectec:1758.6-1758.17
  rule instexport_is_wf_0{`var_0*` : funcaddr*, `var_1*` : globaladdr*, `var_2*` : tableaddr*, `var_3*` : memaddr*, export : export, ret_val : exportinst}:
    `%%%%%%`(`var_0*`, `var_1*`, `var_2*`, `var_3*`, export, ret_val)
    -- wf_export: `%`(export)
    -- if (ret_val = $instexport(`var_0*`, `var_1*`, `var_2*`, `var_3*`, export))
    -- wf_exportinst: `%`(ret_val)

;; test.spectec:1765.1-1765.73
def $allocmodule(store : store, module : module, externaddr*, val*) : (store, moduleinst)
  ;; test.spectec:1766.1-1799.52
  def $allocmodule{s : store, module : module, `externaddr*` : externaddr*, `val*` : val*, s_4 : store, moduleinst : moduleinst, `ft*` : functype*, `import*` : import*, n_func : nat, `func*` : func*, n_global : nat, `expr_1*` : expr*, `globaltype*` : globaltype*, n_table : nat, `tabletype*` : tabletype*, n_mem : nat, `memtype*` : memtype*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*, s_1 : store, s_2 : store, s_3 : store}(s, module, externaddr*{externaddr <- `externaddr*`}, val*{val <- `val*`}) = (s_4, moduleinst)
    -- if (module = MODULE_module(TYPE_type(ft)*{ft <- `ft*`}, import*{import <- `import*`}, func^n_func{func <- `func*`}, GLOBAL_global(globaltype, expr_1)^n_global{expr_1 <- `expr_1*`, globaltype <- `globaltype*`}, TABLE_table(tabletype)^n_table{tabletype <- `tabletype*`}, MEMORY_mem(memtype)^n_mem{memtype <- `memtype*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- let{`fa_ex*` : funcaddr*} fa_ex*{fa_ex <- `fa_ex*`} = $funcs(externaddr*{externaddr <- `externaddr*`})
    -- let{`ga_ex*` : globaladdr*} ga_ex*{ga_ex <- `ga_ex*`} = $globals(externaddr*{externaddr <- `externaddr*`})
    -- let{`ta_ex*` : tableaddr*} ta_ex*{ta_ex <- `ta_ex*`} = $tables(externaddr*{externaddr <- `externaddr*`})
    -- let{`ma_ex*` : memaddr*} ma_ex*{ma_ex <- `ma_ex*`} = $mems(externaddr*{externaddr <- `externaddr*`})
    -- let{`fa*` : funcaddr*} fa*{fa <- `fa*`} = (|s.FUNCS_store| + i_func)^(i_func<n_func){}
    -- let{`ga*` : globaladdr*} ga*{ga <- `ga*`} = (|s.GLOBALS_store| + i_global)^(i_global<n_global){}
    -- let{`ta*` : tableaddr*} ta*{ta <- `ta*`} = (|s.TABLES_store| + i_table)^(i_table<n_table){}
    -- let{`ma*` : memaddr*} ma*{ma <- `ma*`} = (|s.MEMS_store| + i_mem)^(i_mem<n_mem){}
    -- let{`xi*` : exportinst*} xi*{xi <- `xi*`} = $instexport(fa_ex*{fa_ex <- `fa_ex*`} ++ fa*{fa <- `fa*`}, ga_ex*{ga_ex <- `ga_ex*`} ++ ga*{ga <- `ga*`}, ta_ex*{ta_ex <- `ta_ex*`} ++ ta*{ta <- `ta*`}, ma_ex*{ma_ex <- `ma_ex*`} ++ ma*{ma <- `ma*`}, export)*{export <- `export*`}
    -- if (moduleinst = {TYPES ft*{ft <- `ft*`}, FUNCS fa_ex*{fa_ex <- `fa_ex*`} ++ fa*{fa <- `fa*`}, GLOBALS ga_ex*{ga_ex <- `ga_ex*`} ++ ga*{ga <- `ga*`}, TABLES ta_ex*{ta_ex <- `ta_ex*`} ++ ta*{ta <- `ta*`}, MEMS ma_ex*{ma_ex <- `ma_ex*`} ++ ma*{ma <- `ma*`}, EXPORTS xi*{xi <- `xi*`}})
    -- if ((s_1, fa*{fa <- `fa*`}) = $allocfuncs(s, moduleinst, func^n_func{func <- `func*`}))
    -- if ((s_2, ga*{ga <- `ga*`}) = $allocglobals(s_1, globaltype^n_global{globaltype <- `globaltype*`}, val*{val <- `val*`}))
    -- if ((s_3, ta*{ta <- `ta*`}) = $alloctables(s_2, tabletype^n_table{tabletype <- `tabletype*`}))
    -- if ((s_4, ma*{ma <- `ma*`}) = $allocmems(s_3, memtype^n_mem{memtype <- `memtype*`}))
    -- wf_store: `%`(s_1)
    -- wf_store: `%`(s_2)
    -- wf_store: `%`(s_3)
    -- wf_module: `%`(MODULE_module(TYPE_type(ft)*{ft <- `ft*`}, import*{import <- `import*`}, func^n_func{func <- `func*`}, GLOBAL_global(globaltype, expr_1)^n_global{expr_1 <- `expr_1*`, globaltype <- `globaltype*`}, TABLE_table(tabletype)^n_table{tabletype <- `tabletype*`}, MEMORY_mem(memtype)^n_mem{memtype <- `memtype*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- wf_moduleinst: `%`({TYPES ft*{ft <- `ft*`}, FUNCS fa_ex*{fa_ex <- `fa_ex*`} ++ fa*{fa <- `fa*`}, GLOBALS ga_ex*{ga_ex <- `ga_ex*`} ++ ga*{ga <- `ga*`}, TABLES ta_ex*{ta_ex <- `ta_ex*`} ++ ta*{ta <- `ta*`}, MEMS ma_ex*{ma_ex <- `ma_ex*`} ++ ma*{ma <- `ma*`}, EXPORTS xi*{xi <- `xi*`}})

;; test.spectec:1765.6-1765.18
relation allocmodule_is_wf: `%%%%%`(store : store, module : module, `var_0*` : externaddr*, `var_1*` : val*, ret_val : (store, moduleinst))
  ;; test.spectec:1765.6-1765.18
  rule allocmodule_is_wf_0{store : store, module : module, `var_0*` : externaddr*, `var_1*` : val*, ret_val : (store, moduleinst)}:
    `%%%%%`(store, module, `var_0*`, `var_1*`, ret_val)
    -- wf_store: `%`(store)
    -- wf_module: `%`(module)
    -- (wf_val: `%`(var_1))*{var_1 <- `var_1*`}
    -- if (ret_val = $allocmodule(store, module, `var_0*`, `var_1*`))
    -- wf_store: `%`(ret_val.0)
    -- wf_moduleinst: `%`(ret_val.1)

;; test.spectec:1806.1-1806.61
rec {

;; test.spectec:1806.1-1806.61
def $initelem(store : store, moduleinst : moduleinst, u32*, funcaddr**) : store
  ;; test.spectec:1807.1-1807.43
  def $initelem{s : store, moduleinst : moduleinst}(s, moduleinst, [], []) = s
  ;; test.spectec:1808.1-1810.54
  def $initelem{s : store, moduleinst : moduleinst, i : uN, `i'*` : u32*, `a*` : addr*, `a'**` : addr**, s_1 : store}(s, moduleinst, [i] ++ i'*{i' <- `i'*`}, [a*{a <- `a*`}] ++ a'*{a' <- `a'*`}*{`a'*` <- `a'**`}) = s_2
    -- if (s_1 = s[TABLES_store[moduleinst.TABLES_moduleinst[0]].REFS_tableinst[i!`%`_uN.0 : |a*{a <- `a*`}|] = ?(a)*{a <- `a*`}])
    -- let{s_2 : store} s_2 = $initelem(s_1, moduleinst, i'*{i' <- `i'*`}, a'*{a' <- `a'*`}*{`a'*` <- `a'**`})
    -- wf_store: `%`(s_1)
}

;; test.spectec:1806.1-1806.61
rec {

;; test.spectec:1806.6-1806.15
relation initelem_is_wf: `%%%%%`(store : store, moduleinst : moduleinst, `var_0*` : u32*, `var_1**` : funcaddr**, ret_val : store)
  ;; test.spectec:1806.6-1806.15
  rule initelem_is_wf_0{store : store, moduleinst : moduleinst, `var_0*` : u32*, `var_1**` : funcaddr**, ret_val : store}:
    `%%%%%`(store, moduleinst, `var_0*`, `var_1**`, ret_val)
    -- wf_store: `%`(store)
    -- wf_moduleinst: `%`(moduleinst)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $initelem(store, moduleinst, `var_0*`, `var_1**`))
    -- wf_store: `%`(ret_val)
}

;; test.spectec:1812.1-1812.57
rec {

;; test.spectec:1812.1-1812.57
def $initdata(store : store, moduleinst : moduleinst, u32*, byte**) : store
  ;; test.spectec:1813.1-1813.43
  def $initdata{s : store, moduleinst : moduleinst}(s, moduleinst, [], []) = s
  ;; test.spectec:1814.1-1816.54
  def $initdata{s : store, moduleinst : moduleinst, i : uN, `i'*` : u32*, `b*` : byte*, `b'**` : byte**}(s, moduleinst, [i] ++ i'*{i' <- `i'*`}, [b*{b <- `b*`}] ++ b'*{b' <- `b'*`}*{`b'*` <- `b'**`}) = s_2
    -- let{s_1 : store} s_1 = s[MEMS_store[moduleinst.MEMS_moduleinst[0]].BYTES_meminst[i!`%`_uN.0 : |b*{b <- `b*`}|] = b*{b <- `b*`}]
    -- let{s_2 : store} s_2 = $initdata(s_1, moduleinst, i'*{i' <- `i'*`}, b'*{b' <- `b'*`}*{`b'*` <- `b'**`})
}

;; test.spectec:1812.1-1812.57
rec {

;; test.spectec:1812.6-1812.15
relation initdata_is_wf: `%%%%%`(store : store, moduleinst : moduleinst, `var_0*` : u32*, `var_1**` : byte**, ret_val : store)
  ;; test.spectec:1812.6-1812.15
  rule initdata_is_wf_0{store : store, moduleinst : moduleinst, `var_0*` : u32*, `var_1**` : byte**, ret_val : store}:
    `%%%%%`(store, moduleinst, `var_0*`, `var_1**`, ret_val)
    -- wf_store: `%`(store)
    -- wf_moduleinst: `%`(moduleinst)
    -- (wf_uN: `%%`(32, var_0))*{var_0 <- `var_0*`}
    -- (wf_byte: `%`(var_1))*{var_1 <- `var_1*`}*{`var_1*` <- `var_1**`}
    -- if (ret_val = $initdata(store, moduleinst, `var_0*`, `var_1**`))
    -- wf_store: `%`(ret_val)
}

;; test.spectec:1818.1-1818.54
def $instantiate(store : store, module : module, externaddr*) : config
  ;; test.spectec:1819.1-1840.34
  def $instantiate{s : store, module : module, `externaddr*` : externaddr*, f : frame, `x'?` : idx?, `functype*` : functype*, `expr_G*` : expr*, `globaltype*` : globaltype*, `expr_E*` : expr*, `x**` : idx**, `b**` : byte**, `expr_D*` : expr*, moduleinst_init : moduleinst, f_init : frame, `val*` : val*, `i_E*` : val_*, `i_D*` : val_*}(s, module, externaddr*{externaddr <- `externaddr*`}) = `%;%`_config(`%;%`_state(s_3, f), lift(CALL_admininstr(x')?{x' <- `x'?`}))
    -- let{`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*} MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}) = module
    -- if (type*{type <- `type*`} = TYPE_type(functype)*{functype <- `functype*`})
    -- if (global*{global <- `global*`} = GLOBAL_global(globaltype, expr_G)*{expr_G <- `expr_G*`, globaltype <- `globaltype*`})
    -- if (elem*{elem <- `elem*`} = ELEM_elem(expr_E, x*{x <- `x*`})*{expr_E <- `expr_E*`, `x*` <- `x**`})
    -- if (data*{data <- `data*`} = DATA_data(expr_D, b*{b <- `b*`})*{`b*` <- `b**`, expr_D <- `expr_D*`})
    -- if (start?{start <- `start?`} = START_start(x')?{x' <- `x'?`})
    -- let{n_F : n} n_F = |func*{func <- `func*`}|
    -- if (moduleinst_init = {TYPES functype*{functype <- `functype*`}, FUNCS $funcs(externaddr*{externaddr <- `externaddr*`}) ++ (|s.FUNCS_store| + i_F)^(i_F<n_F){}, GLOBALS $globals(externaddr*{externaddr <- `externaddr*`}), TABLES [], MEMS [], EXPORTS []})
    -- if (f_init = {LOCALS [], MODULE moduleinst_init})
    -- let{z : state} z = `%;%`_state(s, f_init)
    -- (Eval_expr: `%;%~>*%;%`(z, expr_G, z, [val]))*{expr_G <- `expr_G*`, val <- `val*`}
    -- (Eval_expr: `%;%~>*%;%`(z, expr_E, z, [CONST_val(I32_valtype, i_E)]))*{expr_E <- `expr_E*`, i_E <- `i_E*`}
    -- (Eval_expr: `%;%~>*%;%`(z, expr_D, z, [CONST_val(I32_valtype, i_D)]))*{expr_D <- `expr_D*`, i_D <- `i_D*`}
    -- let{s_1 : store, moduleinst : moduleinst} (s_1, moduleinst) = $allocmodule(s, module, externaddr*{externaddr <- `externaddr*`}, val*{val <- `val*`})
    -- let{s_2 : store} s_2 = $initelem(s_1, moduleinst, !($proj_val__0(i_E))*{i_E <- `i_E*`}, moduleinst.FUNCS_moduleinst[x!`%`_uN.0]*{x <- `x*`}*{`x*` <- `x**`})
    -- let{s_3 : store} s_3 = $initdata(s_2, moduleinst, !($proj_val__0(i_D))*{i_D <- `i_D*`}, b*{b <- `b*`}*{`b*` <- `b**`})
    -- if (f = {LOCALS [], MODULE moduleinst})
    -- (wf_val: `%`(val))*{val <- `val*`}
    -- wf_module: `%`(MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`}))
    -- (wf_global: `%`(GLOBAL_global(globaltype, expr_G)))*{expr_G <- `expr_G*`, globaltype <- `globaltype*`}
    -- (wf_elem: `%`(ELEM_elem(expr_E, x*{x <- `x*`})))*{expr_E <- `expr_E*`, `x*` <- `x**`}
    -- (wf_data: `%`(DATA_data(expr_D, b*{b <- `b*`})))*{`b*` <- `b**`, expr_D <- `expr_D*`}
    -- (wf_start: `%`(START_start(x')))?{x' <- `x'?`}
    -- wf_moduleinst: `%`({TYPES functype*{functype <- `functype*`}, FUNCS $funcs(externaddr*{externaddr <- `externaddr*`}) ++ (|s.FUNCS_store| + i_F)^(i_F<n_F){}, GLOBALS $globals(externaddr*{externaddr <- `externaddr*`}), TABLES [], MEMS [], EXPORTS []})
    -- wf_frame: `%`({LOCALS [], MODULE moduleinst_init})
    -- wf_state: `%`(`%;%`_state(s, f_init))
    -- (wf_val: `%`(CONST_val(I32_valtype, i_E)))*{i_E <- `i_E*`}
    -- (wf_val: `%`(CONST_val(I32_valtype, i_D)))*{i_D <- `i_D*`}
    -- wf_frame: `%`({LOCALS [], MODULE moduleinst})

;; test.spectec:1818.6-1818.18
relation instantiate_is_wf: `%%%%`(store : store, module : module, `var_0*` : externaddr*, ret_val : config)
  ;; test.spectec:1818.6-1818.18
  rule instantiate_is_wf_0{store : store, module : module, `var_0*` : externaddr*, ret_val : config}:
    `%%%%`(store, module, `var_0*`, ret_val)
    -- wf_store: `%`(store)
    -- wf_module: `%`(module)
    -- if (ret_val = $instantiate(store, module, `var_0*`))
    -- wf_config: `%`(ret_val)

;; test.spectec:1847.1-1847.44
def $invoke(store : store, funcaddr : funcaddr, val*) : config
  ;; test.spectec:1848.1-1850.51
  def $invoke{s : store, fa : nat, n : nat, `val*` : val*, f : frame, `t_1*` : valtype*, `t_2*` : valtype*}(s, fa, val^n{val <- `val*`}) = `%;%`_config(`%;%`_state(s, f), (val : val <: admininstr)^n{val <- `val*`} ++ [CALL_ADDR_admininstr(fa)])
    -- if (f = {LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], EXPORTS []}})
    -- if ($funcinst(`%;%`_state(s, f))[fa].TYPE_funcinst = `%->%`_functype(t_1^n{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- wf_frame: `%`({LOCALS [], MODULE {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], EXPORTS []}})
    -- wf_state: `%`(`%;%`_state(s, f))

;; test.spectec:1847.6-1847.13
relation invoke_is_wf: `%%%%`(store : store, funcaddr : funcaddr, `var_0*` : val*, ret_val : config)
  ;; test.spectec:1847.6-1847.13
  rule invoke_is_wf_0{store : store, funcaddr : funcaddr, `var_0*` : val*, ret_val : config}:
    `%%%%`(store, funcaddr, `var_0*`, ret_val)
    -- wf_store: `%`(store)
    -- (wf_val: `%`(var_0))*{var_0 <- `var_0*`}
    -- if (ret_val = $invoke(store, funcaddr, `var_0*`))
    -- wf_config: `%`(ret_val)

;; test.spectec:2339.1-2339.43
syntax startopt = start*

;; test.spectec:2356.1-2356.29
syntax code = (local*, expr)

;; test.spectec:2406.1-2406.61
relation Context_ok: `|-%:OK`(context)
  ;; test.spectec:2408.1-2424.34
  rule _{C : context, `ft*` : functype*, `ft_2*` : functype*, `gt*` : globaltype*, `tt*` : tabletype*, `mt*` : memtype*, `lct*` : valtype*, `rt*` : valtype*, `rt'?` : valtype?}:
    `|-%:OK`(C)
    -- if (C = {TYPES ft*{ft <- `ft*`}, FUNCS ft_2*{ft_2 <- `ft_2*`}, GLOBALS gt*{gt <- `gt*`}, TABLES tt*{tt <- `tt*`}, MEMS mt*{mt <- `mt*`}, LOCALS lct*{lct <- `lct*`}, LABELS ?(rt)*{rt <- `rt*`}, RETURN ?(rt'?{rt' <- `rt'?`})})
    -- (Functype_ok: `|-%:OK`(ft))*{ft <- `ft*`}
    -- (Globaltype_ok: `|-%:OK`(gt))*{gt <- `gt*`}
    -- (Memtype_ok: `|-%:OK`(mt))*{mt <- `mt*`}
    -- (Tabletype_ok: `|-%:OK`(tt))*{tt <- `tt*`}
    -- (Functype_ok: `|-%:OK`(ft_2))*{ft_2 <- `ft_2*`}
    -- wf_context: `%`(C)
    -- wf_context: `%`({TYPES ft*{ft <- `ft*`}, FUNCS ft_2*{ft_2 <- `ft_2*`}, GLOBALS gt*{gt <- `gt*`}, TABLES tt*{tt <- `tt*`}, MEMS mt*{mt <- `mt*`}, LOCALS lct*{lct <- `lct*`}, LABELS ?(rt)*{rt <- `rt*`}, RETURN ?(rt'?{rt' <- `rt'?`})})

;; test.spectec:2428.1-2428.34
relation Val_ok: `|-%:%`(val, valtype)
  ;; test.spectec:2430.1-2431.21
  rule _{t : valtype, c_t : val_}:
    `|-%:%`(CONST_val(t, c_t), t)
    -- wf_val: `%`(CONST_val(t, c_t))

;; test.spectec:2436.1-2436.41
relation Result_ok: `|-%:%`(result, valtype*)
  ;; test.spectec:2438.1-2440.25
  rule result{`v*` : val*, `t*` : valtype*}:
    `|-%:%`(_VALS_result(v*{v <- `v*`}), t*{t <- `t*`})
    -- (Val_ok: `|-%:%`(v, t))*{t <- `t*`, v <- `v*`}
    -- wf_result: `%`(_VALS_result(v*{v <- `v*`}))

  ;; test.spectec:2442.1-2443.15
  rule trap{`t*` : valtype*}:
    `|-%:%`(TRAP_result, t*{t <- `t*`})
    -- wf_result: `%`(TRAP_result)

;; test.spectec:2447.1-2447.31
syntax adminexpr = admininstr*

;; test.spectec:2498.1-2498.84
rec {

;; test.spectec:2498.1-2498.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; test.spectec:2500.1-2502.34
  rule global{s : store, a : addr, globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(globalinst.TYPE_globalinst))
    -- if (s.GLOBALS_store[a] = globalinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(GLOBAL_externtype(globalinst.TYPE_globalinst))

  ;; test.spectec:2504.1-2506.28
  rule mem{s : store, a : addr, meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(meminst.TYPE_meminst))
    -- if (s.MEMS_store[a] = meminst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(MEM_externtype(meminst.TYPE_meminst))

  ;; test.spectec:2508.1-2510.32
  rule table{s : store, a : addr, tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(tableinst.TYPE_tableinst))
    -- if (s.TABLES_store[a] = tableinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(TABLE_externtype(tableinst.TYPE_tableinst))

  ;; test.spectec:2512.1-2514.30
  rule func{s : store, a : addr, funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype(funcinst.TYPE_funcinst))
    -- if (s.FUNCS_store[a] = funcinst)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(FUNC_externtype(funcinst.TYPE_funcinst))

  ;; test.spectec:2516.1-2519.34
  rule sub{s : store, externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, externaddr, xt')
    -- Externtype_sub: `|-%<:%`(xt', xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_externtype: `%`(xt')
}

;; test.spectec:2527.1-2527.49
relation Exportinst_ok: `%|-%:OK`(store, exportinst)
  ;; test.spectec:2551.1-2553.33
  rule _{s : store, nm : name, xa : externaddr, xt : externtype}:
    `%|-%:OK`(s, {NAME nm, ADDR xa})
    -- Externaddr_ok: `%|-%:%`(s, xa, xt)
    -- wf_store: `%`(s)
    -- wf_externtype: `%`(xt)
    -- wf_exportinst: `%`({NAME nm, ADDR xa})

;; test.spectec:2558.1-2558.54
relation Moduleinst_ok: `%|-%:%`(store, moduleinst, context)
  ;; test.spectec:2560.1-2581.102
  rule _{s : store, `functype*` : functype*, `funcaddr*` : funcaddr*, `globaladdr*` : globaladdr*, `tableaddr*` : tableaddr*, `memaddr*` : memaddr*, `exportinst*` : exportinst*, `functype_F*` : functype*, `globaltype*` : globaltype*, `tabletype*` : tabletype*, `memtype*` : memtype*}:
    `%|-%:%`(s, {TYPES functype*{functype <- `functype*`}, FUNCS funcaddr*{funcaddr <- `funcaddr*`}, GLOBALS globaladdr*{globaladdr <- `globaladdr*`}, TABLES tableaddr*{tableaddr <- `tableaddr*`}, MEMS memaddr*{memaddr <- `memaddr*`}, EXPORTS exportinst*{exportinst <- `exportinst*`}}, {TYPES functype*{functype <- `functype*`}, FUNCS functype_F*{functype_F <- `functype_F*`}, GLOBALS globaltype*{globaltype <- `globaltype*`}, TABLES tabletype*{tabletype <- `tabletype*`}, MEMS memtype*{memtype <- `memtype*`}, LOCALS [], LABELS [], RETURN ?()})
    -- (Functype_ok: `|-%:OK`(functype))*{functype <- `functype*`}
    -- (Externaddr_ok: `%|-%:%`(s, GLOBAL_externaddr(globaladdr), GLOBAL_externtype(globaltype)))*{globaladdr <- `globaladdr*`, globaltype <- `globaltype*`}
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(funcaddr), FUNC_externtype(functype_F)))*{funcaddr <- `funcaddr*`, functype_F <- `functype_F*`}
    -- (Externaddr_ok: `%|-%:%`(s, MEM_externaddr(memaddr), MEM_externtype(memtype)))*{memaddr <- `memaddr*`, memtype <- `memtype*`}
    -- (Externaddr_ok: `%|-%:%`(s, TABLE_externaddr(tableaddr), TABLE_externtype(tabletype)))*{tableaddr <- `tableaddr*`, tabletype <- `tabletype*`}
    -- (Exportinst_ok: `%|-%:OK`(s, exportinst))*{exportinst <- `exportinst*`}
    -- if $disjoint_(syntax name, exportinst.NAME_exportinst*{exportinst <- `exportinst*`})
    -- (if (exportinst.ADDR_exportinst <- GLOBAL_externaddr(globaladdr)*{globaladdr <- `globaladdr*`} ++ MEM_externaddr(memaddr)*{memaddr <- `memaddr*`} ++ TABLE_externaddr(tableaddr)*{tableaddr <- `tableaddr*`} ++ FUNC_externaddr(funcaddr)*{funcaddr <- `funcaddr*`}))*{exportinst <- `exportinst*`}
    -- wf_store: `%`(s)
    -- wf_moduleinst: `%`({TYPES functype*{functype <- `functype*`}, FUNCS funcaddr*{funcaddr <- `funcaddr*`}, GLOBALS globaladdr*{globaladdr <- `globaladdr*`}, TABLES tableaddr*{tableaddr <- `tableaddr*`}, MEMS memaddr*{memaddr <- `memaddr*`}, EXPORTS exportinst*{exportinst <- `exportinst*`}})
    -- wf_context: `%`({TYPES functype*{functype <- `functype*`}, FUNCS functype_F*{functype_F <- `functype_F*`}, GLOBALS globaltype*{globaltype <- `globaltype*`}, TABLES tabletype*{tabletype <- `tabletype*`}, MEMS memtype*{memtype <- `memtype*`}, LOCALS [], LABELS [], RETURN ?()})
    -- (wf_externtype: `%`(GLOBAL_externtype(globaltype)))*{globaltype <- `globaltype*`}
    -- (wf_externtype: `%`(FUNC_externtype(functype_F)))*{functype_F <- `functype_F*`}
    -- (wf_externtype: `%`(MEM_externtype(memtype)))*{memtype <- `memtype*`}
    -- (wf_externtype: `%`(TABLE_externtype(tabletype)))*{tabletype <- `tabletype*`}

;; test.spectec:2631.1-2631.44
relation Frame_ok: `%|-%:%`(store, frame, context)
  ;; test.spectec:2635.1-2638.27
  rule _{s : store, `val*` : val*, moduleinst : moduleinst, C : context, `t*` : valtype*}:
    `%|-%:%`(s, {LOCALS val*{val <- `val*`}, MODULE moduleinst}, C +++ {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t*{t <- `t*`}, LABELS [], RETURN ?()})
    -- Moduleinst_ok: `%|-%:%`(s, moduleinst, C)
    -- (Val_ok: `|-%:%`(val, t))*{t <- `t*`, val <- `val*`}
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_frame: `%`({LOCALS val*{val <- `val*`}, MODULE moduleinst})
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS t*{t <- `t*`}, LABELS [], RETURN ?()})

;; test.spectec:2449.1-2454.36
rec {

;; test.spectec:2449.1-2450.36
relation Instr_ok2: `%;%|-%:%`(store, context, admininstr, functype)
  ;; test.spectec:2456.1-2458.41
  rule plain{s : store, C : context, instr : instr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, (instr : instr <: admininstr), `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- Instr_ok: `%|-%:%`(C, instr, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_instr: `%`(instr)

  ;; test.spectec:2460.1-2464.67
  rule label{s : store, C : context, n : n, `instr'*` : instr*, `admininstr*` : admininstr*, `t?` : valtype?, `t'?` : valtype?}:
    `%;%|-%:%`(s, C, `LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, admininstr*{admininstr <- `admininstr*`}), `%->%`_functype([], lift(t?{t <- `t?`})))
    -- if (|lift(t'?{t' <- `t'?`})| = n)
    -- Instrs_ok2: `%;%|-%:%`(s, C, (instr' : instr <: admininstr)*{instr' <- `instr'*`}, `%->%`_functype(lift(t'?{t' <- `t'?`}), lift(t?{t <- `t?`})))
    -- Instrs_ok2: `%;%|-%:%`(s, {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t'?{t' <- `t'?`}], RETURN ?()} +++ C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype([], lift(t?{t <- `t?`})))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(`LABEL_%{%}%`_admininstr(n, instr'*{instr' <- `instr'*`}, admininstr*{admininstr <- `admininstr*`}))
    -- wf_context: `%`({TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], LOCALS [], LABELS [t'?{t' <- `t'?`}], RETURN ?()})

  ;; test.spectec:2466.1-2470.41
  rule frame{s : store, C : context, n : n, f : frame, `admininstr*` : admininstr*, `t?` : valtype?, C' : context}:
    `%;%|-%:%`(s, C, `FRAME_%{%}%`_admininstr(n, f, admininstr*{admininstr <- `admininstr*`}), `%->%`_functype([], lift(t?{t <- `t?`})))
    -- if (|lift(t?{t <- `t?`})| = n)
    -- Frame_ok: `%|-%:%`(s, f, C')
    -- Expr_ok2: `%;%|-%:%`(s, C', admininstr*{admininstr <- `admininstr*`}, t?{t <- `t?`})
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_context: `%`(C')
    -- wf_admininstr: `%`(`FRAME_%{%}%`_admininstr(n, f, admininstr*{admininstr <- `admininstr*`}))

  ;; test.spectec:2472.1-2474.60
  rule call_addr{s : store, C : context, funcaddr : funcaddr, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, CALL_ADDR_admininstr(funcaddr), `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(funcaddr), FUNC_externtype(`%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`})))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(CALL_ADDR_admininstr(funcaddr))
    -- wf_externtype: `%`(FUNC_externtype(`%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2476.1-2477.30
  rule trap{s : store, C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, TRAP_admininstr, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(TRAP_admininstr)

;; test.spectec:2451.1-2452.36
relation Instrs_ok2: `%;%|-%:%`(store, context, admininstr*, functype)
  ;; test.spectec:2480.1-2481.27
  rule empty{s : store, C : context}:
    `%;%|-%:%`(s, C, [], `%->%`_functype([], []))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)

  ;; test.spectec:2483.1-2486.54
  rule seq{s : store, C : context, admininstr_1 : admininstr, `admininstr_2*` : admininstr*, `t_1*` : valtype*, `t_3*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, [admininstr_1] ++ admininstr_2*{admininstr_2 <- `admininstr_2*`}, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_3*{t_3 <- `t_3*`}))
    -- Instr_ok2: `%;%|-%:%`(s, C, admininstr_1, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr_2*{admininstr_2 <- `admininstr_2*`}, `%->%`_functype(t_2*{t_2 <- `t_2*`}, t_3*{t_3 <- `t_3*`}))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_admininstr: `%`(admininstr_1)
    -- (wf_admininstr: `%`(admininstr_2))*{admininstr_2 <- `admininstr_2*`}

  ;; test.spectec:2488.1-2490.52
  rule frame{s : store, C : context, `admininstr*` : admininstr*, `t*` : valtype*, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}, t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`}))
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`}))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(admininstr))*{admininstr <- `admininstr*`}

;; test.spectec:2453.1-2454.36
relation Expr_ok2: `%;%|-%:%`(store, context, adminexpr, resulttype)
  ;; test.spectec:2492.1-2494.49
  rule _{s : store, C : context, `admininstr*` : admininstr*, `t?` : valtype?}:
    `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, t?{t <- `t?`})
    -- Instrs_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, `%->%`_functype([], lift(t?{t <- `t?`})))
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- (wf_admininstr: `%`(admininstr))*{admininstr <- `admininstr*`}
}

;; test.spectec:2523.1-2523.57
relation Globalinst_ok: `%|-%:%`(store, globalinst, globaltype)
  ;; test.spectec:2529.1-2532.24
  rule _{s : store, mut : mut, t : valtype, val : val}:
    `%|-%:%`(s, {TYPE `%%`_globaltype(mut, t), VALUE val}, `%%`_globaltype(mut, t))
    -- Globaltype_ok: `|-%:OK`(`%%`_globaltype(mut, t))
    -- Val_ok: `|-%:%`(val, t)
    -- wf_store: `%`(s)
    -- wf_globalinst: `%`({TYPE `%%`_globaltype(mut, t), VALUE val})

;; test.spectec:2524.1-2524.48
relation Meminst_ok: `%|-%:%`(store, meminst, memtype)
  ;; test.spectec:2534.1-2537.37
  rule _{s : store, n : n, `m?` : m?, `b*` : byte*}:
    `%|-%:%`(s, {TYPE `[%..%]`_memtype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), BYTES b*{b <- `b*`}}, `[%..%]`_memtype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))
    -- Memtype_ok: `|-%:OK`(`[%..%]`_memtype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))
    -- if (|b*{b <- `b*`}| = (n * (64 * $Ki)))
    -- wf_store: `%`(s)
    -- wf_meminst: `%`({TYPE `[%..%]`_memtype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), BYTES b*{b <- `b*`}})
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))

;; test.spectec:2525.1-2525.54
relation Tableinst_ok: `%|-%:%`(store, tableinst, tabletype)
  ;; test.spectec:2539.1-2543.21
  rule _{s : store, n : n, `m?` : m?, `fa?*` : funcaddr?*, `ft?*` : functype?*}:
    `%|-%:%`(s, {TYPE `[%..%]`_tabletype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), REFS fa?{fa <- `fa?`}*{`fa?` <- `fa?*`}}, `[%..%]`_tabletype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))
    -- Tabletype_ok: `|-%:OK`(`[%..%]`_tabletype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))
    -- (Externaddr_ok: `%|-%:%`(s, FUNC_externaddr(fa), FUNC_externtype(ft)))?{fa <- `fa?`, ft <- `ft?`}*{`fa?` <- `fa?*`, `ft?` <- `ft?*`}
    -- if (|fa?{fa <- `fa?`}*{`fa?` <- `fa?*`}| = n)
    -- wf_store: `%`(s)
    -- wf_tableinst: `%`({TYPE `[%..%]`_tabletype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), REFS fa?{fa <- `fa?`}*{`fa?` <- `fa?*`}})
    -- wf_limits: `%`(`[%..%]`_limits(`%`_u32(n), `%`_u32(m)?{m <- `m?`}))
    -- (wf_externtype: `%`(FUNC_externtype(ft)))?{ft <- `ft?`}*{`ft?` <- `ft?*`}

;; test.spectec:2526.1-2526.51
relation Funcinst_ok: `%|-%:%`(store, funcinst, functype)
  ;; test.spectec:2545.1-2549.29
  rule _{s : store, ft : functype, moduleinst : moduleinst, func : func, C : context}:
    `%|-%:%`(s, {TYPE ft, MODULE moduleinst, CODE func}, ft)
    -- Functype_ok: `|-%:OK`(ft)
    -- Moduleinst_ok: `%|-%:%`(s, moduleinst, C)
    -- Func_ok: `%|-%:%`(C, func, ft)
    -- wf_store: `%`(s)
    -- wf_context: `%`(C)
    -- wf_funcinst: `%`({TYPE ft, MODULE moduleinst, CODE func})

;; test.spectec:2586.1-2586.33
relation Store_ok: `|-%:OK`(store)
  ;; test.spectec:2588.1-2595.85
  rule _{s : store, `globalinst*` : globalinst*, `globaltype*` : globaltype*, `meminst*` : meminst*, `memtype*` : memtype*, `tableinst*` : tableinst*, `tabletype*` : tabletype*, `funcinst*` : funcinst*, `functype*` : functype*}:
    `|-%:OK`(s)
    -- (Globalinst_ok: `%|-%:%`(s, globalinst, globaltype))*{globalinst <- `globalinst*`, globaltype <- `globaltype*`}
    -- (Meminst_ok: `%|-%:%`(s, meminst, memtype))*{meminst <- `meminst*`, memtype <- `memtype*`}
    -- (Tableinst_ok: `%|-%:%`(s, tableinst, tabletype))*{tableinst <- `tableinst*`, tabletype <- `tabletype*`}
    -- (Funcinst_ok: `%|-%:%`(s, funcinst, functype))*{funcinst <- `funcinst*`, functype <- `functype*`}
    -- if (s = {FUNCS funcinst*{funcinst <- `funcinst*`}, GLOBALS globalinst*{globalinst <- `globalinst*`}, TABLES tableinst*{tableinst <- `tableinst*`}, MEMS meminst*{meminst <- `meminst*`}})
    -- wf_store: `%`(s)
    -- (wf_limits: `%`(memtype))*{memtype <- `memtype*`}
    -- (wf_limits: `%`(tabletype))*{tabletype <- `tabletype*`}
    -- wf_store: `%`({FUNCS funcinst*{funcinst <- `funcinst*`}, GLOBALS globalinst*{globalinst <- `globalinst*`}, TABLES tableinst*{tableinst <- `tableinst*`}, MEMS meminst*{meminst <- `meminst*`}})

;; test.spectec:2599.1-2599.54
relation Extend_globalinst: `%<=%`(globalinst, globalinst)
  ;; test.spectec:2605.1-2607.32
  rule _{mut : mut, t : valtype, val : val, val' : val}:
    `%<=%`({TYPE `%%`_globaltype(mut, t), VALUE val}, {TYPE `%%`_globaltype(mut, t), VALUE val'})
    -- if ((mut = ?(MUT_MUT)) \/ (val = val'))
    -- wf_globalinst: `%`({TYPE `%%`_globaltype(mut, t), VALUE val})
    -- wf_globalinst: `%`({TYPE `%%`_globaltype(mut, t), VALUE val'})

;; test.spectec:2600.1-2600.45
relation Extend_meminst: `%<=%`(meminst, meminst)
  ;; test.spectec:2609.1-2612.22
  rule _{n : n, `m?` : m?, `b*` : byte*, n' : n, `b'*` : byte*}:
    `%<=%`({TYPE `[%..%]`_memtype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), BYTES b*{b <- `b*`}}, {TYPE `[%..%]`_memtype(`%`_u32(n'), `%`_u32(m)?{m <- `m?`}), BYTES b'*{b' <- `b'*`}})
    -- if (n <= n')
    -- if (|b*{b <- `b*`}| <= |b'*{b' <- `b'*`}|)
    -- wf_meminst: `%`({TYPE `[%..%]`_memtype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), BYTES b*{b <- `b*`}})
    -- wf_meminst: `%`({TYPE `[%..%]`_memtype(`%`_u32(n'), `%`_u32(m)?{m <- `m?`}), BYTES b'*{b' <- `b'*`}})

;; test.spectec:2601.1-2601.51
relation Extend_tableinst: `%<=%`(tableinst, tableinst)
  ;; test.spectec:2614.1-2617.26
  rule _{n : n, `m?` : m?, `ref*` : funcaddr*, n' : n, `ref'*` : funcaddr*}:
    `%<=%`({TYPE `[%..%]`_tabletype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), REFS ?(ref)*{ref <- `ref*`}}, {TYPE `[%..%]`_tabletype(`%`_u32(n'), `%`_u32(m)?{m <- `m?`}), REFS ?(ref')*{ref' <- `ref'*`}})
    -- if (n <= n')
    -- if (|ref*{ref <- `ref*`}| <= |ref'*{ref' <- `ref'*`}|)
    -- wf_tableinst: `%`({TYPE `[%..%]`_tabletype(`%`_u32(n), `%`_u32(m)?{m <- `m?`}), REFS ?(ref)*{ref <- `ref*`}})
    -- wf_tableinst: `%`({TYPE `[%..%]`_tabletype(`%`_u32(n'), `%`_u32(m)?{m <- `m?`}), REFS ?(ref')*{ref' <- `ref'*`}})

;; test.spectec:2602.1-2602.48
relation Extend_funcinst: `%<=%`(funcinst, funcinst)
  ;; test.spectec:2619.1-2620.66
  rule _{ft : functype, mm : moduleinst, fc : func}:
    `%<=%`({TYPE ft, MODULE mm, CODE fc}, {TYPE ft, MODULE mm, CODE fc})
    -- wf_funcinst: `%`({TYPE ft, MODULE mm, CODE fc})

;; test.spectec:2603.1-2603.39
relation Extend_store: `%<=%`(store, store)
  ;; test.spectec:2622.1-2627.66
  rule _{s : store, s' : store}:
    `%<=%`(s, s')
    -- (Extend_globalinst: `%<=%`(s.GLOBALS_store[a], s'.GLOBALS_store[a]))^(a<|s.GLOBALS_store|){}
    -- (Extend_meminst: `%<=%`(s.MEMS_store[a], s'.MEMS_store[a]))^(a<|s.MEMS_store|){}
    -- (Extend_tableinst: `%<=%`(s.TABLES_store[a], s'.TABLES_store[a]))^(a<|s.TABLES_store|){}
    -- (Extend_funcinst: `%<=%`(s.FUNCS_store[a], s'.FUNCS_store[a]))^(a<|s.FUNCS_store|){}
    -- wf_store: `%`(s)
    -- wf_store: `%`(s')

;; test.spectec:2632.1-2632.38
relation State_ok: `|-%:%`(state, context)
  ;; test.spectec:2640.1-2643.26
  rule _{s : store, f : frame, C : context}:
    `|-%:%`(`%;%`_state(s, f), C)
    -- Store_ok: `|-%:OK`(s)
    -- Frame_ok: `%|-%:%`(s, f, C)
    -- wf_context: `%`(C)
    -- wf_state: `%`(`%;%`_state(s, f))

;; test.spectec:2633.1-2633.43
relation Config_ok: `|-%:%`(config, resulttype)
  ;; test.spectec:2645.1-2648.40
  rule _{s : store, f : frame, `admininstr*` : admininstr*, `t?` : valtype?, C : context}:
    `|-%:%`(`%;%`_config(`%;%`_state(s, f), admininstr*{admininstr <- `admininstr*`}), t?{t <- `t?`})
    -- State_ok: `|-%:%`(`%;%`_state(s, f), C)
    -- Expr_ok2: `%;%|-%:%`(s, C, admininstr*{admininstr <- `admininstr*`}, t?{t <- `t?`})
    -- wf_context: `%`(C)
    -- wf_config: `%`(`%;%`_config(`%;%`_state(s, f), admininstr*{admininstr <- `admininstr*`}))
    -- wf_state: `%`(`%;%`_state(s, f))

;; test.spectec:1874.1-1874.41
grammar Bbyte : byte
  ;; test.spectec:1874.24-1874.41
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x00 | ... | 0xFF) => `%`_byte(`<implicit-prod-result>`)

;; test.spectec:1876.1-1878.82
rec {

;; test.spectec:1876.1-1878.82
grammar BuN(N : N) : uN
  ;; test.spectec:1877.5-1877.83
  prod{n : n} `%`_byte(n):Bbyte => `%`_uN(n)
    -- if ((n < (2 ^ 7)) /\ (n < (2 ^ N)))
  ;; test.spectec:1878.5-1878.82
  prod{m : m, n : n} {{`%`_byte(n):Bbyte} {`%`_uN(m):BuN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => `%`_uN((((2 ^ 7) * m) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; test.spectec:1893.1-1893.29
grammar Bu32 : u32
  ;; test.spectec:1893.22-1893.29
  prod{`<implicit-prod-result>` : uN} `<implicit-prod-result>`:BuN(32) => `<implicit-prod-result>`

;; test.spectec:1863.1-1864.29
grammar Blist(syntax el, grammar BX : el) : el*
  ;; test.spectec:1864.5-1864.29
  prod{n : n, `el*` : el*} {{`%`_u32(n):Bu32} {el:BX^n{el <- `el*`}}} => el^n{el <- `el*`}

;; test.spectec:1880.1-1883.82
rec {

;; test.spectec:1880.1-1883.82
grammar BsN(N : N) : sN
  ;; test.spectec:1881.5-1881.87
  prod{n : n} `%`_byte(n):Bbyte => `%`_sN((n : nat <:> int))
    -- if ((n < (2 ^ 6)) /\ (n < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat))))
  ;; test.spectec:1882.5-1882.101
  prod{n : n} `%`_byte(n):Bbyte => `%`_sN(((n : nat <:> int) - ((2 ^ 7) : nat <:> int)))
    -- if ((((2 ^ 6) <= n) /\ (n < (2 ^ 7))) /\ ((n : nat <:> int) >= (((2 ^ 7) : nat <:> int) - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int))))
  ;; test.spectec:1883.5-1883.82
  prod{i : sN, n : n} {{`%`_byte(n):Bbyte} {i:BsN((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => `%`_sN(((((2 ^ 7) * (i!`%`_sN.0 : int <:> nat)) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat)) : nat <:> int))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; test.spectec:1885.1-1886.50
grammar BiN(N : N) : iN
  ;; test.spectec:1886.5-1886.50
  prod{i : sN} i:BsN(N) => `%`_iN($inv_signed_(N, i!`%`_sN.0))

;; test.spectec:1889.1-1890.43
grammar BfN(N : N) : fN
  ;; test.spectec:1890.5-1890.43
  prod{`b*` : byte*} b*{b <- `b*`}:Bbyte^(((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat){} => $inv_fbytes_(N, b*{b <- `b*`})

;; test.spectec:1894.1-1894.29
grammar Bu64 : u64
  ;; test.spectec:1894.22-1894.29
  prod{`<implicit-prod-result>` : uN} `<implicit-prod-result>`:BuN(64) => `<implicit-prod-result>`

;; test.spectec:1896.1-1896.29
grammar Bi32 : i32
  ;; test.spectec:1896.22-1896.29
  prod{`<implicit-prod-result>` : iN} `<implicit-prod-result>`:BiN(32) => `<implicit-prod-result>`

;; test.spectec:1897.1-1897.29
grammar Bi64 : i64
  ;; test.spectec:1897.22-1897.29
  prod{`<implicit-prod-result>` : iN} `<implicit-prod-result>`:BiN(64) => `<implicit-prod-result>`

;; test.spectec:1899.1-1899.29
grammar Bf32 : f32
  ;; test.spectec:1899.22-1899.29
  prod{`<implicit-prod-result>` : fN} `<implicit-prod-result>`:BfN(32) => `<implicit-prod-result>`

;; test.spectec:1900.1-1900.29
grammar Bf64 : f64
  ;; test.spectec:1900.22-1900.29
  prod{`<implicit-prod-result>` : fN} `<implicit-prod-result>`:BfN(64) => `<implicit-prod-result>`

;; test.spectec:1914.1-1915.52
grammar Bname : name
  ;; test.spectec:1915.5-1915.52
  prod{name : name, `b*` : byte*} b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte) => name
    -- if ($utf8(name!`%`_name.0) = b*{b <- `b*`})

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
  prod{`t*` : valtype*} t*{t <- `t*`}:Blist(syntax valtype, grammar Bvaltype) => t*{t <- `t*`}

;; test.spectec:1954.1-1955.59
grammar Bfunctype : functype
  ;; test.spectec:1955.5-1955.59
  prod{`t_1*` : valtype*, `t_2*` : valtype*} {{0x60} {t_1*{t_1 <- `t_1*`}:Bresulttype} {t_2*{t_2 <- `t_2*`}:Bresulttype}} => `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`})

;; test.spectec:1960.1-1962.16
grammar Bmut : mut
  ;; test.spectec:1961.5-1961.16
  prod 0x00 => ?()
  ;; test.spectec:1962.5-1962.16
  prod 0x01 => ?(MUT_MUT)

;; test.spectec:1964.1-1966.36
grammar Blimits : limits
  ;; test.spectec:1965.5-1965.31
  prod{n : n} {{0x00} {`%`_u32(n):Bu32}} => `[%..%]`_limits(`%`_u32(n), ?())
  ;; test.spectec:1966.5-1966.36
  prod{n : n, m : m} {{0x01} {`%`_u32(n):Bu32} {`%`_u32(m):Bu32}} => `[%..%]`_limits(`%`_u32(n), ?(`%`_u32(m)))

;; test.spectec:1968.1-1969.33
grammar Bglobaltype : globaltype
  ;; test.spectec:1969.5-1969.33
  prod{mut : mut, t : valtype} {{t:Bvaltype} {mut:Bmut}} => `%%`_globaltype(mut, t)

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
  prod{n : n, m : m} {{`%`_u32(n):Bu32} {`%`_u32(m):Bu32}} => {ALIGN `%`_u32(n), OFFSET `%`_u32(m)}

;; test.spectec:2217.1-2242.38
rec {

;; test.spectec:2217.1-2242.38
grammar Binstr : instr
  ;; test.spectec:1999.5-1999.24
  prod 0x00 => UNREACHABLE_instr
  ;; test.spectec:2000.5-2000.16
  prod 0x01 => NOP_instr
  ;; test.spectec:2001.5-2001.57
  prod{bt : blocktype, `in*` : instr*} {{0x02} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => BLOCK_instr(bt, in*{in <- `in*`})
  ;; test.spectec:2002.5-2002.56
  prod{bt : blocktype, `in*` : instr*} {{0x03} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => LOOP_instr(bt, in*{in <- `in*`})
  ;; test.spectec:2003.5-2003.63
  prod{bt : blocktype, `in*` : instr*} {{0x04} {bt:Bblocktype} {in:Binstr*{in <- `in*`}} {0x0B}} => `IF%%ELSE%`_instr(bt, in*{in <- `in*`}, [])
  ;; test.spectec:2004.5-2004.89
  prod{bt : blocktype, `in_1*` : instr*, `in_2*` : instr*} {{0x04} {bt:Bblocktype} {in_1:Binstr*{in_1 <- `in_1*`}} {0x05} {in_2:Binstr*{in_2 <- `in_2*`}} {0x0B}} => `IF%%ELSE%`_instr(bt, in_1*{in_1 <- `in_1*`}, in_2*{in_2 <- `in_2*`})
  ;; test.spectec:2005.5-2005.29
  prod{l : labelidx} {{0x0C} {l:Blabelidx}} => BR_instr(l)
  ;; test.spectec:2006.5-2006.32
  prod{l : labelidx} {{0x0D} {l:Blabelidx}} => BR_IF_instr(l)
  ;; test.spectec:2007.5-2007.62
  prod{`l*` : labelidx*, l_N : labelidx} {{0x0E} {l*{l <- `l*`}:Blist(syntax labelidx, grammar Blabelidx)} {l_N:Blabelidx}} => BR_TABLE_instr(l*{l <- `l*`}, l_N)
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
  prod{x : idx} {{0x20} {x:Blocalidx}} => `LOCAL.GET`_instr(x)
  ;; test.spectec:2026.5-2026.36
  prod{x : idx} {{0x21} {x:Blocalidx}} => `LOCAL.SET`_instr(x)
  ;; test.spectec:2027.5-2027.36
  prod{x : idx} {{0x22} {x:Blocalidx}} => `LOCAL.TEE`_instr(x)
  ;; test.spectec:2028.5-2028.38
  prod{x : idx} {{0x23} {x:Bglobalidx}} => `GLOBAL.GET`_instr(x)
  ;; test.spectec:2029.5-2029.38
  prod{x : idx} {{0x24} {x:Bglobalidx}} => `GLOBAL.SET`_instr(x)
  ;; test.spectec:2039.5-2039.35
  prod{ao : memarg} {{0x28} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(), ao)
  ;; test.spectec:2040.5-2040.35
  prod{ao : memarg} {{0x29} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(), ao)
  ;; test.spectec:2041.5-2041.35
  prod{ao : memarg} {{0x2A} {ao:Bmemarg}} => LOAD_instr(F32_valtype, ?(), ao)
  ;; test.spectec:2042.5-2042.35
  prod{ao : memarg} {{0x2B} {ao:Bmemarg}} => LOAD_instr(F64_valtype, ?(), ao)
  ;; test.spectec:2043.5-2043.43
  prod{ao : memarg} {{0x2C} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, `%_%`_loadop_Inn(`%`_sz(8), S_sx))), ao)
  ;; test.spectec:2044.5-2044.43
  prod{ao : memarg} {{0x2D} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, `%_%`_loadop_Inn(`%`_sz(8), U_sx))), ao)
  ;; test.spectec:2045.5-2045.44
  prod{ao : memarg} {{0x2E} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, `%_%`_loadop_Inn(`%`_sz(16), S_sx))), ao)
  ;; test.spectec:2046.5-2046.44
  prod{ao : memarg} {{0x2F} {ao:Bmemarg}} => LOAD_instr(I32_valtype, ?(mk_loadop__0_loadop_(I32_Inn, `%_%`_loadop_Inn(`%`_sz(16), U_sx))), ao)
  ;; test.spectec:2047.5-2047.43
  prod{ao : memarg} {{0x30} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, `%_%`_loadop_Inn(`%`_sz(8), S_sx))), ao)
  ;; test.spectec:2048.5-2048.43
  prod{ao : memarg} {{0x31} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, `%_%`_loadop_Inn(`%`_sz(8), U_sx))), ao)
  ;; test.spectec:2049.5-2049.44
  prod{ao : memarg} {{0x32} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, `%_%`_loadop_Inn(`%`_sz(16), S_sx))), ao)
  ;; test.spectec:2050.5-2050.44
  prod{ao : memarg} {{0x33} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, `%_%`_loadop_Inn(`%`_sz(16), U_sx))), ao)
  ;; test.spectec:2051.5-2051.44
  prod{ao : memarg} {{0x34} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, `%_%`_loadop_Inn(`%`_sz(32), S_sx))), ao)
  ;; test.spectec:2052.5-2052.44
  prod{ao : memarg} {{0x35} {ao:Bmemarg}} => LOAD_instr(I64_valtype, ?(mk_loadop__0_loadop_(I64_Inn, `%_%`_loadop_Inn(`%`_sz(32), U_sx))), ao)
  ;; test.spectec:2053.5-2053.36
  prod{ao : memarg} {{0x36} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(), ao)
  ;; test.spectec:2054.5-2054.36
  prod{ao : memarg} {{0x37} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(), ao)
  ;; test.spectec:2055.5-2055.36
  prod{ao : memarg} {{0x38} {ao:Bmemarg}} => STORE_instr(F32_valtype, ?(), ao)
  ;; test.spectec:2056.5-2056.36
  prod{ao : memarg} {{0x39} {ao:Bmemarg}} => STORE_instr(F64_valtype, ?(), ao)
  ;; test.spectec:2057.5-2057.38
  prod{ao : memarg} {{0x3A} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(`%`_sz(8)), ao)
  ;; test.spectec:2058.5-2058.39
  prod{ao : memarg} {{0x3B} {ao:Bmemarg}} => STORE_instr(I32_valtype, ?(`%`_sz(16)), ao)
  ;; test.spectec:2059.5-2059.38
  prod{ao : memarg} {{0x3C} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(`%`_sz(8)), ao)
  ;; test.spectec:2060.5-2060.39
  prod{ao : memarg} {{0x3D} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(`%`_sz(16)), ao)
  ;; test.spectec:2061.5-2061.39
  prod{ao : memarg} {{0x3E} {ao:Bmemarg}} => STORE_instr(I64_valtype, ?(`%`_sz(32)), ao)
  ;; test.spectec:2062.5-2062.29
  prod {{0x3F} {0x00}} => `MEMORY.SIZE`_instr
  ;; test.spectec:2063.5-2063.29
  prod {{0x40} {0x00}} => `MEMORY.GROW`_instr
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
  prod{`in*` : instr*} {{in:Binstr*{in <- `in*`}} {0x0B}} => in*{in <- `in*`}

;; test.spectec:2260.1-2262.15
grammar Bsection_(N : N, syntax en, grammar BX : en*) : en*
  ;; test.spectec:2261.5-2261.55
  prod{`en*` : en*, len : nat} {{`%`_byte(N):Bbyte} {`%`_u32(len):Bu32} {en*{en <- `en*`}:BX}} => en*{en <- `en*`}
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
  prod{`ty*` : type*} ty*{ty <- `ty*`}:Bsection_(1, syntax type, grammar Blist(syntax type, grammar Btype)) => ty*{ty <- `ty*`}

;; test.spectec:2285.1-2286.64
grammar Bimport : import
  ;; test.spectec:2286.5-2286.64
  prod{nm_1 : name, nm_2 : name, xt : externtype} {{nm_1:Bname} {nm_2:Bname} {xt:Bexterntype}} => IMPORT_import(nm_1, nm_2, xt)

;; test.spectec:2288.1-2289.44
grammar Bimportsec : import*
  ;; test.spectec:2289.5-2289.44
  prod{`im*` : import*} im*{im <- `im*`}:Bsection_(2, syntax import, grammar Blist(syntax import, grammar Bimport)) => im*{im <- `im*`}

;; test.spectec:2294.1-2295.43
grammar Bfuncsec : typeidx*
  ;; test.spectec:2295.5-2295.43
  prod{`x*` : idx*} x*{x <- `x*`}:Bsection_(3, syntax typeidx, grammar Blist(syntax typeidx, grammar Btypeidx)) => x*{x <- `x*`}

;; test.spectec:2300.1-2301.30
grammar Btable : table
  ;; test.spectec:2301.5-2301.30
  prod{tt : tabletype} tt:Btabletype => TABLE_table(tt)

;; test.spectec:2303.1-2304.45
grammar Btablesec : table*
  ;; test.spectec:2304.5-2304.45
  prod{`tab*` : table*} tab*{tab <- `tab*`}:Bsection_(4, syntax table, grammar Blist(syntax table, grammar Btable)) => tab*{tab <- `tab*`}

;; test.spectec:2309.1-2310.29
grammar Bmem : mem
  ;; test.spectec:2310.5-2310.29
  prod{mt : memtype} mt:Bmemtype => MEMORY_mem(mt)

;; test.spectec:2312.1-2313.43
grammar Bmemsec : mem*
  ;; test.spectec:2313.5-2313.43
  prod{`mem*` : mem*} mem*{mem <- `mem*`}:Bsection_(5, syntax mem, grammar Blist(syntax mem, grammar Bmem)) => mem*{mem <- `mem*`}

;; test.spectec:2318.1-2319.42
grammar Bglobal : global
  ;; test.spectec:2319.5-2319.42
  prod{gt : globaltype, e : expr} {{gt:Bglobaltype} {e:Bexpr}} => GLOBAL_global(gt, e)

;; test.spectec:2321.1-2322.48
grammar Bglobalsec : global*
  ;; test.spectec:2322.5-2322.48
  prod{`glob*` : global*} glob*{glob <- `glob*`}:Bsection_(6, syntax global, grammar Blist(syntax global, grammar Bglobal)) => glob*{glob <- `glob*`}

;; test.spectec:2327.1-2328.43
grammar Bexport : export
  ;; test.spectec:2328.5-2328.43
  prod{nm : name, xx : externidx} {{nm:Bname} {xx:Bexternidx}} => EXPORT_export(nm, xx)

;; test.spectec:2330.1-2331.44
grammar Bexportsec : export*
  ;; test.spectec:2331.5-2331.44
  prod{`ex*` : export*} ex*{ex <- `ex*`}:Bsection_(7, syntax export, grammar Blist(syntax export, grammar Bexport)) => ex*{ex <- `ex*`}

;; test.spectec:2336.1-2337.28
grammar Bstart : start*
  ;; test.spectec:2337.5-2337.28
  prod{x : idx} x:Bfuncidx => [START_start(x)]

;; test.spectec:2341.1-2342.60
grammar Bstartsec : start?
  ;; test.spectec:2342.5-2342.60
  prod{startopt : startopt} startopt:Bsection_(8, syntax start, grammar Bstart) => !($opt_(syntax start, startopt))

;; test.spectec:2347.1-2348.49
grammar Belem : elem
  ;; test.spectec:2348.5-2348.49
  prod{e : expr, `x*` : idx*} {{0x00} {e:Bexpr} {x*{x <- `x*`}:Blist(syntax funcidx, grammar Bfuncidx)}} => ELEM_elem(e, x*{x <- `x*`})

;; test.spectec:2350.1-2351.46
grammar Belemsec : elem*
  ;; test.spectec:2351.5-2351.46
  prod{`elem*` : elem*} elem*{elem <- `elem*`}:Bsection_(9, syntax elem, grammar Blist(syntax elem, grammar Belem)) => elem*{elem <- `elem*`}

;; test.spectec:2358.1-2359.37
grammar Blocals : local*
  ;; test.spectec:2359.5-2359.37
  prod{t : valtype, n : n} {{`%`_u32(n):Bu32} {t:Bvaltype}} => LOCAL_local(t)^n{}

;; test.spectec:2361.1-2362.74
grammar Bfunc : code
  ;; test.spectec:2362.5-2362.74
  prod{`local**` : local**, expr : expr} {{local*{local <- `local*`}*{`local*` <- `local**`}:Blist(syntax local*, grammar Blocals)} {expr:Bexpr}} => ($concat_(syntax local, local*{local <- `local*`}*{`local*` <- `local**`}), expr)

;; test.spectec:2364.1-2365.55
grammar Bcode : code
  ;; test.spectec:2365.5-2365.55
  prod{code : code, len : nat} {{`%`_u32(len):Bu32} {code:Bfunc}} => code
    -- if (len = 0)

;; test.spectec:2367.1-2368.47
grammar Bcodesec : code*
  ;; test.spectec:2368.5-2368.47
  prod{`code*` : code*} code*{code <- `code*`}:Bsection_(10, syntax code, grammar Blist(syntax code, grammar Bcode)) => code*{code <- `code*`}

;; test.spectec:2373.1-2374.46
grammar Bdata : data
  ;; test.spectec:2374.5-2374.46
  prod{e : expr, `b*` : byte*} {{0x00} {e:Bexpr} {b*{b <- `b*`}:Blist(syntax byte, grammar Bbyte)}} => DATA_data(e, b*{b <- `b*`})

;; test.spectec:2376.1-2377.47
grammar Bdatasec : data*
  ;; test.spectec:2377.5-2377.47
  prod{`data*` : data*} data*{data <- `data*`}:Bsection_(11, syntax data, grammar Blist(syntax data, grammar Bdata)) => data*{data <- `data*`}

;; test.spectec:2382.1-2397.45
grammar Bmodule : module
  ;; test.spectec:2383.5-2397.45
  prod{`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*, `typeidx*` : typeidx*, `expr*` : expr*, `local**` : local**} {{0x00} {0x61} {0x73} {0x6D} {`%`_u32(1):Bu32} {Bcustomsec*{}} {type*{type <- `type*`}:Btypesec} {Bcustomsec*{}} {import*{import <- `import*`}:Bimportsec} {Bcustomsec*{}} {typeidx*{typeidx <- `typeidx*`}:Bfuncsec} {Bcustomsec*{}} {table*{table <- `table*`}:Btablesec} {Bcustomsec*{}} {mem*{mem <- `mem*`}:Bmemsec} {Bcustomsec*{}} {global*{global <- `global*`}:Bglobalsec} {Bcustomsec*{}} {export*{export <- `export*`}:Bexportsec} {Bcustomsec*{}} {start?{start <- `start?`}:Bstartsec} {Bcustomsec*{}} {elem*{elem <- `elem*`}:Belemsec} {Bcustomsec*{}} {(local*{local <- `local*`}, expr)*{expr <- `expr*`, `local*` <- `local**`}:Bcodesec} {Bcustomsec*{}} {data*{data <- `data*`}:Bdatasec} {Bcustomsec*{}}} => MODULE_module(type*{type <- `type*`}, import*{import <- `import*`}, func*{func <- `func*`}, global*{global <- `global*`}, table*{table <- `table*`}, mem*{mem <- `mem*`}, elem*{elem <- `elem*`}, data*{data <- `data*`}, start?{start <- `start?`}, export*{export <- `export*`})
    -- (if (func = FUNC_func(typeidx, local*{local <- `local*`}, expr)))*{expr <- `expr*`, func <- `func*`, `local*` <- `local**`, typeidx <- `typeidx*`}

