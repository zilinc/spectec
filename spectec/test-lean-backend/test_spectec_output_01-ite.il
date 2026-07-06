
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
  def $sum{n : n, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n + $sum(n'*{n' <- `n'*`}))
}

;; test.spectec:32.1-32.58
def $opt_(syntax X, X*) : X?
  ;; test.spectec:33.1-33.31
  def $opt_{syntax X}(syntax X, []) = ?()
  ;; test.spectec:34.1-34.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(w)

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
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:99.1-100.25
syntax uN{N : N}(N) = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:101.1-102.49
syntax sN{N : N}(N) = 
  | `%`(i : int)
    -- if ((((i >= - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; test.spectec:103.1-104.8
syntax iN{N : N}(N) = uN(N)

;; test.spectec:106.1-106.20
syntax u31 = uN(31)

;; test.spectec:107.1-107.20
syntax u32 = uN(32)

;; test.spectec:108.1-108.20
syntax u64 = uN(64)

;; test.spectec:110.1-110.20
syntax i32 = iN(32)

;; test.spectec:111.1-111.20
syntax i64 = iN(64)

;; test.spectec:118.1-118.35
def $signif(N : N) : nat
  ;; test.spectec:119.1-119.21
  def $signif(32) = 23
  ;; test.spectec:120.1-120.21
  def $signif(64) = 52

;; test.spectec:122.1-122.34
def $expon(N : N) : nat
  ;; test.spectec:123.1-123.19
  def $expon(32) = 8
  ;; test.spectec:124.1-124.20
  def $expon(64) = 11

;; test.spectec:126.1-126.30
def $M(N : N) : nat
  ;; test.spectec:127.1-127.23
  def $M{N : N}(N) = $signif(N)

;; test.spectec:129.1-129.30
def $E(N : N) : nat
  ;; test.spectec:130.1-130.22
  def $E{N : N}(N) = $expon(N)

;; test.spectec:136.1-136.30
syntax exp = int

;; test.spectec:137.1-141.84
syntax fNmag{N : N}(N) = 
  | NORM(m : m, exp : exp)
    -- if ((m < (2 ^ $M(N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= exp) /\ (exp <= (((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))
  | SUBNORM(m : m) {exp : exp}
    -- if ((m < (2 ^ $M(N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = exp))
  | INF
  | NAN(m : m)
    -- if ((1 <= m) /\ (m < (2 ^ $M(N))))

;; test.spectec:132.1-134.35
syntax fN{N : N}(N) = 
  | POS(fNmag(N))
  | NEG(fNmag(N))

;; test.spectec:143.1-143.20
syntax f32 = fN(32)

;; test.spectec:144.1-144.20
syntax f64 = fN(64)

;; test.spectec:146.1-146.39
def $fzero(N : N) : fN(N)
  ;; test.spectec:147.1-147.32
  def $fzero{N : N}(N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:149.1-149.39
def $fone(N : N) : fN(N)
  ;; test.spectec:150.1-150.30
  def $fone{N : N}(N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:152.1-152.21
def $canon_(N : N) : nat
  ;; test.spectec:153.1-153.37
  def $canon_{N : N}(N) = (2 ^ ((($signif(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:160.1-160.85
syntax char = 
  | `%`(i : nat)
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:162.1-162.25
def $utf8(char*) : byte*

;; test.spectec:164.1-164.70
syntax name = 
  | `%`(`char*` : char*)
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

;; test.spectec:226.1-226.41
def $size(valtype : valtype) : nat

;; test.spectec:228.1-228.21
syntax val_(valtype : valtype)
  ;; test.spectec:229.1-229.34
  syntax val_{Inn : Inn}((Inn : Inn <: valtype)) = iN($size((Inn : Inn <: valtype)))


  ;; test.spectec:230.1-230.34
  syntax val_{Fnn : Fnn}((Fnn : Fnn <: valtype)) = fN($size((Fnn : Fnn <: valtype)))


;; test.spectec:235.1-235.42
syntax sx = 
  | U
  | S

;; test.spectec:236.1-236.56
syntax sz = 
  | `%`(i : nat)
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; test.spectec:238.1-238.22
syntax unop_(valtype : valtype)
  ;; test.spectec:239.1-239.39
  syntax unop_{Inn : Inn}((Inn : Inn <: valtype)) = 
  | CLZ
  | CTZ
  | POPCNT


  ;; test.spectec:240.1-240.70
  syntax unop_{Fnn : Fnn}((Fnn : Fnn <: valtype)) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; test.spectec:242.1-242.23
syntax binop_(valtype : valtype)
  ;; test.spectec:243.1-245.66
  syntax binop_{Inn : Inn}((Inn : Inn <: valtype)) = 
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


  ;; test.spectec:246.1-247.49
  syntax binop_{Fnn : Fnn}((Fnn : Fnn <: valtype)) = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN


;; test.spectec:249.1-249.24
syntax testop_{Inn : Inn}((Inn : Inn <: valtype)) = 
  | EQZ

;; test.spectec:253.1-253.23
syntax relop_(valtype : valtype)
  ;; test.spectec:254.1-257.52
  syntax relop_{Inn : Inn}((Inn : Inn <: valtype)) = 
  | EQ
  | NE
  | LT(sx : sx)
  | GT(sx : sx)
  | LE(sx : sx)
  | GE(sx : sx)


  ;; test.spectec:258.1-259.32
  syntax relop_{Fnn : Fnn}((Fnn : Fnn <: valtype)) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


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

;; test.spectec:271.1-271.24
syntax loadop_{Inn : Inn}((Inn : Inn <: valtype)) = 
  | `%_%`(sz : sz, sx : sx)
    -- if (sz!`%`_sz.0 < $size((Inn : Inn <: valtype)))

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
  | CONST(valtype : valtype, val_(valtype))
  | UNOP(valtype : valtype, unop_(valtype))
  | BINOP(valtype : valtype, binop_(valtype))
  | TESTOP(valtype : valtype, testop_(valtype))
  | RELOP(valtype : valtype, relop_(valtype))
  | CVTOP(valtype_1 : valtype, valtype_2 : valtype, cvtop : cvtop)
    -- if (valtype_1 =/= valtype_2)
  | `LOCAL.GET`(localidx : localidx)
  | `LOCAL.SET`(localidx : localidx)
  | `LOCAL.TEE`(localidx : localidx)
  | `GLOBAL.GET`(globalidx : globalidx)
  | `GLOBAL.SET`(globalidx : globalidx)
  | LOAD(valtype : valtype, loadop_(valtype)?, memarg : memarg)
  | STORE(valtype : valtype, `sz?` : sz?, memarg : memarg) {`Inn?` : Inn?, `valtype?` : valtype?}
    -- (if ((valtype = (Inn : Inn <: valtype)) /\ (sz!`%`_sz.0 < $size((Inn : Inn <: valtype)))))?{Inn <- `Inn?`, sz <- `sz?`, valtype <- `valtype?`}
  | `MEMORY.SIZE`
  | `MEMORY.GROW`
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

;; test.spectec:351.1-352.25
syntax global = 
  | GLOBAL(globaltype : globaltype, expr : expr)

;; test.spectec:353.1-354.18
syntax table = 
  | TABLE(tabletype : tabletype)

;; test.spectec:355.1-356.17
syntax mem = 
  | MEMORY(memtype : memtype)

;; test.spectec:357.1-358.21
syntax elem = 
  | ELEM(expr : expr, `funcidx*` : funcidx*)

;; test.spectec:359.1-360.18
syntax data = 
  | DATA(expr : expr, `byte*` : byte*)

;; test.spectec:361.1-362.16
syntax start = 
  | START(funcidx : funcidx)

;; test.spectec:364.1-365.66
syntax externidx = 
  | FUNC(funcidx : funcidx)
  | GLOBAL(globalidx : globalidx)
  | TABLE(tableidx : tableidx)
  | MEM(memidx : memidx)

;; test.spectec:366.1-367.24
syntax export = 
  | EXPORT(name : name, externidx : externidx)

;; test.spectec:368.1-369.30
syntax import = 
  | IMPORT(name : name, name : name, externtype : externtype)

;; test.spectec:371.1-372.76
syntax module = 
  | MODULE(`type*` : type*, `import*` : import*, `func*` : func*, `global*` : global*, `table*` : table*, `mem*` : mem*, `elem*` : elem*, `data*` : data*, `start?` : start?, `export*` : export*)

