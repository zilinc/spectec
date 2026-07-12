
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
def $min(nat : nat, nat : nat) : nat
  ;; test.spectec:23.1-23.36
  def $min{i : nat, j : nat}(i, j) = (if (i <= j) then i else j)

;; test.spectec:26.1-26.56
rec {

;; test.spectec:26.1-26.56
def $sum(nat*) : nat
  ;; test.spectec:27.1-27.18
  def $sum([]) = 0
  ;; test.spectec:28.1-28.35
  def $sum{n : n, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n + $sum(n'*{n' <- `n'*`}))
}

;; test.spectec:30.1-30.57
rec {

;; test.spectec:30.1-30.57
def $prod(nat*) : nat
  ;; test.spectec:31.1-31.19
  def $prod([]) = 1
  ;; test.spectec:32.1-32.37
  def $prod{n : n, `n'*` : n*}([n] ++ n'*{n' <- `n'*`}) = (n * $prod(n'*{n' <- `n'*`}))
}

;; test.spectec:47.1-47.58
def $opt_(syntax X, X*) : X?
  ;; test.spectec:48.1-48.31
  def $opt_{syntax X}(syntax X, []) = ?()
  ;; test.spectec:49.1-49.27
  def $opt_{syntax X, w : X}(syntax X, [w]) = ?(w)

;; test.spectec:54.1-54.82
rec {

;; test.spectec:54.1-54.82
def $concat_(syntax X, X**) : X*
  ;; test.spectec:55.1-55.34
  def $concat_{syntax X}(syntax X, []) = []
  ;; test.spectec:56.1-56.64
  def $concat_{syntax X, `w*` : X*, `w'**` : X**}(syntax X, [w*{w <- `w*`}] ++ w'*{w' <- `w'*`}*{`w'*` <- `w'**`}) = w*{w <- `w*`} ++ $concat_(syntax X, w'*{w' <- `w'*`}*{`w'*` <- `w'**`})
}

;; test.spectec:58.1-58.89
rec {

;; test.spectec:58.1-58.89
def $concatn_(syntax X, X**, nat : nat) : X*
  ;; test.spectec:59.1-59.38
  def $concatn_{syntax X, n : n}(syntax X, [], n) = []
  ;; test.spectec:60.1-60.73
  def $concatn_{syntax X, n : n, `w*` : X*, `w'**` : X**}(syntax X, [w^n{w <- `w*`}] ++ w'^n{w' <- `w'*`}*{`w'*` <- `w'**`}, n) = w^n{w <- `w*`} ++ $concatn_(syntax X, w'^n{w' <- `w'*`}*{`w'*` <- `w'**`}, n)
}

;; test.spectec:62.1-62.58
def $concatopt_(syntax X, X?*) : X*
  ;; test.spectec:63.1-63.37
  def $concatopt_{syntax X}(syntax X, []) = []
  ;; test.spectec:64.1-64.67
  def $concatopt_{syntax X, `w?` : X?, `w'?*` : X?*}(syntax X, [w?{w <- `w?`}] ++ w'?{w' <- `w'?`}*{`w'?` <- `w'?*`}) = lift(w?{w <- `w?`}) ++ $concat_(syntax X, lift(w'?{w' <- `w'?`})*{`w'?` <- `w'?*`})

;; test.spectec:66.1-66.39
def $inv_concat_(syntax X, X*) : X**

;; test.spectec:69.1-69.45
def $inv_concatn_(syntax X, nat : nat, X*) : X**

;; test.spectec:75.1-75.78
rec {

;; test.spectec:75.1-75.78
def $disjoint_(syntax X, X*) : bool
  ;; test.spectec:76.1-76.37
  def $disjoint_{syntax X}(syntax X, []) = true
  ;; test.spectec:77.1-77.68
  def $disjoint_{syntax X, w : X, `w'*` : X*}(syntax X, [w] ++ w'*{w' <- `w'*`}) = (~ (w <- w'*{w' <- `w'*`}) /\ $disjoint_(syntax X, w'*{w' <- `w'*`}))
}

;; test.spectec:80.1-80.38
rec {

;; test.spectec:80.1-80.38
def $setminus1_(syntax X, X : X, X*) : X*
  ;; test.spectec:84.1-84.38
  def $setminus1_{syntax X, w : X}(syntax X, w, []) = [w]
  ;; test.spectec:85.1-85.78
  def $setminus1_{syntax X, w : X, w_1 : X, `w'*` : X*}(syntax X, w, [w_1] ++ w'*{w' <- `w'*`}) = (if (w = w_1) then [] else $setminus1_(syntax X, w, w'*{w' <- `w'*`}))
}

;; test.spectec:79.1-79.56
rec {

;; test.spectec:79.1-79.56
def $setminus_(syntax X, X*, X*) : X*
  ;; test.spectec:82.1-82.40
  def $setminus_{syntax X, `w*` : X*}(syntax X, [], w*{w <- `w*`}) = []
  ;; test.spectec:83.1-83.90
  def $setminus_{syntax X, w_1 : X, `w'*` : X*, `w*` : X*}(syntax X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}) = $setminus1_(syntax X, w_1, w*{w <- `w*`}) ++ $setminus_(syntax X, w'*{w' <- `w'*`}, w*{w <- `w*`})
}

;; test.spectec:91.1-91.46
rec {

;; test.spectec:91.1-91.46
def $setproduct2_(syntax X, X : X, X**) : X**
  ;; test.spectec:97.1-97.44
  def $setproduct2_{syntax X, w_1 : X}(syntax X, w_1, []) = []
  ;; test.spectec:98.1-98.90
  def $setproduct2_{syntax X, w_1 : X, `w'*` : X*, `w**` : X**}(syntax X, w_1, [w'*{w' <- `w'*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = [[w_1] ++ w'*{w' <- `w'*`}] ++ $setproduct2_(syntax X, w_1, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; test.spectec:90.1-90.47
rec {

;; test.spectec:90.1-90.47
def $setproduct1_(syntax X, X*, X**) : X**
  ;; test.spectec:95.1-95.46
  def $setproduct1_{syntax X, `w**` : X**}(syntax X, [], w*{w <- `w*`}*{`w*` <- `w**`}) = []
  ;; test.spectec:96.1-96.107
  def $setproduct1_{syntax X, w_1 : X, `w'*` : X*, `w**` : X**}(syntax X, [w_1] ++ w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct2_(syntax X, w_1, w*{w <- `w*`}*{`w*` <- `w**`}) ++ $setproduct1_(syntax X, w'*{w' <- `w'*`}, w*{w <- `w*`}*{`w*` <- `w**`})
}

;; test.spectec:89.1-89.84
rec {

;; test.spectec:89.1-89.84
def $setproduct_(syntax X, X**) : X**
  ;; test.spectec:93.1-93.40
  def $setproduct_{syntax X}(syntax X, []) = [[]]
  ;; test.spectec:94.1-94.90
  def $setproduct_{syntax X, `w_1*` : X*, `w**` : X**}(syntax X, [w_1*{w_1 <- `w_1*`}] ++ w*{w <- `w*`}*{`w*` <- `w**`}) = $setproduct1_(syntax X, w_1*{w_1 <- `w_1*`}, $setproduct_(syntax X, w*{w <- `w*`}*{`w*` <- `w**`}))
}

;; test.spectec:111.1-111.29
def $ND : bool

;; test.spectec:126.1-126.37
syntax bit = 
  | `%`(i : nat)
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:127.1-127.50
syntax byte = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= 255))

;; test.spectec:129.1-130.25
syntax uN{N : N}(N) = 
  | `%`(i : nat)
    -- if ((i >= 0) /\ (i <= ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))

;; test.spectec:131.1-132.50
syntax sN{N : N}(N) = 
  | `%`(i : int)
    -- if ((((i >= - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) /\ (i <= - (1 : nat <:> int))) \/ (i = (0 : nat <:> int))) \/ ((i >= + (1 : nat <:> int)) /\ (i <= (+ ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))

;; test.spectec:133.1-134.8
syntax iN{N : N}(N) = uN(N)

;; test.spectec:136.1-136.20
syntax u8 = uN(8)

;; test.spectec:137.1-137.21
syntax u16 = uN(16)

;; test.spectec:138.1-138.21
syntax u31 = uN(31)

;; test.spectec:139.1-139.21
syntax u32 = uN(32)

;; test.spectec:140.1-140.21
syntax u64 = uN(64)

;; test.spectec:141.1-141.21
syntax s33 = sN(33)

;; test.spectec:142.1-142.21
syntax i32 = iN(32)

;; test.spectec:143.1-143.21
syntax i64 = iN(64)

;; test.spectec:144.1-144.23
syntax i128 = iN(128)

;; test.spectec:151.1-151.35
def $signif(N : N) : nat
  ;; test.spectec:152.1-152.21
  def $signif(32) = 23
  ;; test.spectec:153.1-153.21
  def $signif(64) = 52

;; test.spectec:155.1-155.34
def $expon(N : N) : nat
  ;; test.spectec:156.1-156.19
  def $expon(32) = 8
  ;; test.spectec:157.1-157.20
  def $expon(64) = 11

;; test.spectec:159.1-159.47
def $M(N : N) : nat
  ;; test.spectec:160.1-160.23
  def $M{N : N}(N) = $signif(N)

;; test.spectec:162.1-162.47
def $E(N : N) : nat
  ;; test.spectec:163.1-163.22
  def $E{N : N}(N) = $expon(N)

;; test.spectec:169.1-169.47
syntax exp = int

;; test.spectec:170.1-174.84
syntax fNmag{N : N}(N) = 
  | NORM(m : m, exp : exp)
    -- if ((m < (2 ^ $M(N))) /\ ((((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) <= exp) /\ (exp <= (((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)))))
  | SUBNORM(m : m) {exp : exp}
    -- if ((m < (2 ^ $M(N))) /\ (((2 : nat <:> int) - ((2 ^ ((($E(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) = exp))
  | INF
  | NAN(m : m)
    -- if ((1 <= m) /\ (m < (2 ^ $M(N))))

;; test.spectec:165.1-167.35
syntax fN{N : N}(N) = 
  | POS(fNmag(N))
  | NEG(fNmag(N))

;; test.spectec:176.1-176.21
syntax f32 = fN(32)

;; test.spectec:177.1-177.21
syntax f64 = fN(64)

;; test.spectec:179.1-179.39
def $fzero(N : N) : fN(N)
  ;; test.spectec:180.1-180.32
  def $fzero{N : N}(N) = POS_fN(SUBNORM_fNmag(0))

;; test.spectec:182.1-182.45
def $fnat(N : N, nat : nat) : fN(N)
  ;; test.spectec:183.1-183.33
  def $fnat{N : N, n : n}(N, n) = POS_fN(NORM_fNmag(n, (0 : nat <:> int)))

;; test.spectec:185.1-185.39
def $fone(N : N) : fN(N)
  ;; test.spectec:186.1-186.30
  def $fone{N : N}(N) = POS_fN(NORM_fNmag(1, (0 : nat <:> int)))

;; test.spectec:188.1-188.21
def $canon_(N : N) : nat
  ;; test.spectec:189.1-189.37
  def $canon_{N : N}(N) = (2 ^ ((($signif(N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))

;; test.spectec:194.1-195.8
syntax vN{N : N}(N) = uN(N)

;; test.spectec:197.1-197.23
syntax v128 = vN(128)

;; test.spectec:203.1-203.49
syntax list{syntax X}(syntax X) = 
  | `%`(`X*` : X*)
    -- if (|X*{X <- `X*`}| < (2 ^ 32))

;; test.spectec:208.1-208.85
syntax char = 
  | `%`(i : nat)
    -- if (((i >= 0) /\ (i <= 55295)) \/ ((i >= 57344) /\ (i <= 1114111)))

;; test.spectec:210.1-210.25
def $utf8(char*) : byte*

;; test.spectec:212.1-212.70
syntax name = 
  | `%`(`char*` : char*)
    -- if (|$utf8(char*{char <- `char*`})| < (2 ^ 32))

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
  | FUNC(funcidx : funcidx)
  | GLOBAL(globalidx : globalidx)
  | TABLE(tableidx : tableidx)
  | MEM(memidx : memidx)
  | TAG(tagidx : tagidx)

;; test.spectec:248.1-248.86
rec {

;; test.spectec:248.1-248.86
def $funcsxx(externidx*) : typeidx*
  ;; test.spectec:254.1-254.24
  def $funcsxx([]) = []
  ;; test.spectec:255.1-255.45
  def $funcsxx{x : idx, `xx*` : externidx*}([FUNC_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $funcsxx(xx*{xx <- `xx*`})
  ;; test.spectec:256.1-256.58
  def $funcsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $funcsxx(xx*{xx <- `xx*`})
}

;; test.spectec:249.1-249.88
rec {

;; test.spectec:249.1-249.88
def $globalsxx(externidx*) : globalidx*
  ;; test.spectec:258.1-258.26
  def $globalsxx([]) = []
  ;; test.spectec:259.1-259.51
  def $globalsxx{x : idx, `xx*` : externidx*}([GLOBAL_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $globalsxx(xx*{xx <- `xx*`})
  ;; test.spectec:260.1-260.62
  def $globalsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $globalsxx(xx*{xx <- `xx*`})
}

;; test.spectec:250.1-250.87
rec {

;; test.spectec:250.1-250.87
def $tablesxx(externidx*) : tableidx*
  ;; test.spectec:262.1-262.25
  def $tablesxx([]) = []
  ;; test.spectec:263.1-263.48
  def $tablesxx{x : idx, `xx*` : externidx*}([TABLE_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $tablesxx(xx*{xx <- `xx*`})
  ;; test.spectec:264.1-264.60
  def $tablesxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $tablesxx(xx*{xx <- `xx*`})
}

;; test.spectec:251.1-251.85
rec {

;; test.spectec:251.1-251.85
def $memsxx(externidx*) : memidx*
  ;; test.spectec:266.1-266.23
  def $memsxx([]) = []
  ;; test.spectec:267.1-267.42
  def $memsxx{x : idx, `xx*` : externidx*}([MEM_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $memsxx(xx*{xx <- `xx*`})
  ;; test.spectec:268.1-268.56
  def $memsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $memsxx(xx*{xx <- `xx*`})
}

;; test.spectec:252.1-252.85
rec {

;; test.spectec:252.1-252.85
def $tagsxx(externidx*) : tagidx*
  ;; test.spectec:270.1-270.23
  def $tagsxx([]) = []
  ;; test.spectec:271.1-271.42
  def $tagsxx{x : idx, `xx*` : externidx*}([TAG_externidx(x)] ++ xx*{xx <- `xx*`}) = [x] ++ $tagsxx(xx*{xx <- `xx*`})
  ;; test.spectec:272.1-272.56
  def $tagsxx{externidx : externidx, `xx*` : externidx*}([externidx] ++ xx*{xx <- `xx*`}) = $tagsxx(xx*{xx <- `xx*`})
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

;; test.spectec:291.1-291.28
def $free_opt(free?) : free
  ;; test.spectec:294.1-294.24
  def $free_opt(?()) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:295.1-295.27
  def $free_opt{free : free}(?(free)) = free

;; test.spectec:292.1-292.29
rec {

;; test.spectec:292.1-292.29
def $free_list(free*) : free
  ;; test.spectec:297.1-297.25
  def $free_list([]) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:298.1-298.57
  def $free_list{free : free, `free'*` : free*}([free] ++ free'*{free' <- `free'*`}) = free +++ $free_list(free'*{free' <- `free'*`})
}

;; test.spectec:301.1-301.34
def $free_typeidx(typeidx : typeidx) : free
  ;; test.spectec:313.1-313.45
  def $free_typeidx{typeidx : typeidx}(typeidx) = {TYPES [typeidx], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:302.1-302.34
def $free_funcidx(funcidx : funcidx) : free
  ;; test.spectec:314.1-314.45
  def $free_funcidx{funcidx : funcidx}(funcidx) = {TYPES [], FUNCS [funcidx], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:303.1-303.38
def $free_globalidx(globalidx : globalidx) : free
  ;; test.spectec:315.1-315.53
  def $free_globalidx{globalidx : globalidx}(globalidx) = {TYPES [], FUNCS [], GLOBALS [globalidx], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:304.1-304.36
def $free_tableidx(tableidx : tableidx) : free
  ;; test.spectec:316.1-316.49
  def $free_tableidx{tableidx : tableidx}(tableidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [tableidx], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:305.1-305.32
def $free_memidx(memidx : memidx) : free
  ;; test.spectec:317.1-317.41
  def $free_memidx{memidx : memidx}(memidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [memidx], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:306.1-306.34
def $free_elemidx(elemidx : elemidx) : free
  ;; test.spectec:318.1-318.45
  def $free_elemidx{elemidx : elemidx}(elemidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [elemidx], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:307.1-307.34
def $free_dataidx(dataidx : dataidx) : free
  ;; test.spectec:319.1-319.45
  def $free_dataidx{dataidx : dataidx}(dataidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [dataidx], LOCALS [], LABELS [], TAGS []}

;; test.spectec:308.1-308.36
def $free_localidx(localidx : localidx) : free
  ;; test.spectec:320.1-320.49
  def $free_localidx{localidx : localidx}(localidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [localidx], LABELS [], TAGS []}

;; test.spectec:309.1-309.36
def $free_labelidx(labelidx : labelidx) : free
  ;; test.spectec:321.1-321.49
  def $free_labelidx{labelidx : labelidx}(labelidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [labelidx], TAGS []}

;; test.spectec:311.1-311.32
def $free_tagidx(tagidx : tagidx) : free
  ;; test.spectec:322.1-322.41
  def $free_tagidx{tagidx : tagidx}(tagidx) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS [tagidx]}

;; test.spectec:310.1-310.38
def $free_externidx(externidx : externidx) : free
  ;; test.spectec:324.1-324.59
  def $free_externidx{funcidx : funcidx}(FUNC_externidx(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:325.1-325.67
  def $free_externidx{globalidx : globalidx}(GLOBAL_externidx(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:326.1-326.63
  def $free_externidx{tableidx : tableidx}(TABLE_externidx(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:327.1-327.55
  def $free_externidx{memidx : memidx}(MEM_externidx(memidx)) = $free_memidx(memidx)
  ;; test.spectec:328.1-328.55
  def $free_externidx{tagidx : tagidx}(TAG_externidx(tagidx)) = $free_tagidx(tagidx)

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
  | _IDX(typeidx : typeidx)
  | _DEF(rectype : rectype, n : n)
  | REC(n : n)

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
  | _IDX(typeidx : typeidx)
  | _DEF(rectype : rectype, n : n)
  | REC(n : n)

;; test.spectec:387.1-388.14
syntax valtype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(`null?` : null?, heaptype : heaptype)
  | BOT

;; test.spectec:428.1-428.66
syntax storagetype = 
  | I32
  | I64
  | F32
  | F64
  | V128
  | REF(`null?` : null?, heaptype : heaptype)
  | BOT
  | I8
  | I16

;; test.spectec:438.1-439.16
syntax resulttype = list(syntax valtype)

;; test.spectec:448.1-448.61
syntax fieldtype = 
  | `%%`(`mut?` : mut?, storagetype : storagetype)

;; test.spectec:450.1-453.34
syntax comptype = 
  | STRUCT(list(syntax fieldtype))
  | ARRAY(fieldtype : fieldtype)
  | `FUNC%->%`(resulttype : resulttype, resulttype : resulttype)

;; test.spectec:455.1-456.33
syntax subtype = 
  | SUB(`final?` : final?, `typeuse*` : typeuse*, comptype : comptype)

;; test.spectec:458.1-459.22
syntax rectype = 
  | REC(list(syntax subtype))
}

;; test.spectec:368.1-369.34
syntax deftype = 
  | _DEF(rectype : rectype, n : n)

;; test.spectec:376.1-377.42
syntax typevar = 
  | _IDX(typeidx : typeidx)
  | REC(n : n)

;; test.spectec:382.1-383.23
syntax reftype = 
  | REF(`null?` : null?, heaptype : heaptype)

;; test.spectec:391.1-391.55
syntax Inn = addrtype

;; test.spectec:392.1-392.56
syntax Fnn = 
  | F32
  | F64

;; test.spectec:393.1-393.54
syntax Vnn = vectype

;; test.spectec:394.1-394.42
syntax Cnn = 
  | I32
  | I64
  | F32
  | F64
  | V128

;; test.spectec:397.1-397.43
def $ANYREF : reftype
  ;; test.spectec:410.1-410.32
  def $ANYREF = REF_reftype(?(NULL_null), ANY_heaptype)

;; test.spectec:398.1-398.42
def $EQREF : reftype
  ;; test.spectec:411.1-411.31
  def $EQREF = REF_reftype(?(NULL_null), EQ_heaptype)

;; test.spectec:399.1-399.43
def $I31REF : reftype
  ;; test.spectec:412.1-412.32
  def $I31REF = REF_reftype(?(NULL_null), I31_heaptype)

;; test.spectec:400.1-400.46
def $STRUCTREF : reftype
  ;; test.spectec:413.1-413.35
  def $STRUCTREF = REF_reftype(?(NULL_null), STRUCT_heaptype)

;; test.spectec:401.1-401.45
def $ARRAYREF : reftype
  ;; test.spectec:414.1-414.34
  def $ARRAYREF = REF_reftype(?(NULL_null), ARRAY_heaptype)

;; test.spectec:402.1-402.44
def $FUNCREF : reftype
  ;; test.spectec:415.1-415.33
  def $FUNCREF = REF_reftype(?(NULL_null), FUNC_heaptype)

;; test.spectec:403.1-403.43
def $EXNREF : reftype
  ;; test.spectec:416.1-416.32
  def $EXNREF = REF_reftype(?(NULL_null), EXN_heaptype)

;; test.spectec:404.1-404.46
def $EXTERNREF : reftype
  ;; test.spectec:417.1-417.35
  def $EXTERNREF = REF_reftype(?(NULL_null), EXTERN_heaptype)

;; test.spectec:405.1-405.44
def $NULLREF : reftype
  ;; test.spectec:418.1-418.33
  def $NULLREF = REF_reftype(?(NULL_null), NONE_heaptype)

;; test.spectec:406.1-406.50
def $NULLFUNCREF : reftype
  ;; test.spectec:419.1-419.37
  def $NULLFUNCREF = REF_reftype(?(NULL_null), NOFUNC_heaptype)

;; test.spectec:407.1-407.49
def $NULLEXNREF : reftype
  ;; test.spectec:420.1-420.36
  def $NULLEXNREF = REF_reftype(?(NULL_null), NOEXN_heaptype)

;; test.spectec:408.1-408.54
def $NULLEXTERNREF : reftype
  ;; test.spectec:421.1-421.41
  def $NULLEXTERNREF = REF_reftype(?(NULL_null), NOEXTERN_heaptype)

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
syntax Pnn = packtype

;; test.spectec:432.1-432.56
syntax Jnn = 
  | I32
  | I64
  | I8
  | I16

;; test.spectec:433.1-433.55
syntax Lnn = lanetype

;; test.spectec:464.1-464.74
syntax limits = 
  | `[%..%]`(u64 : u64, `u64?` : u64?)

;; test.spectec:466.1-466.47
syntax tagtype = typeuse

;; test.spectec:467.1-467.58
syntax globaltype = 
  | `%%`(`mut?` : mut?, valtype : valtype)

;; test.spectec:468.1-468.63
syntax memtype = 
  | `%%PAGE`(addrtype : addrtype, limits : limits)

;; test.spectec:469.1-469.67
syntax tabletype = 
  | `%%%`(addrtype : addrtype, limits : limits, reftype : reftype)

;; test.spectec:470.1-470.64
syntax datatype = 
  | OK

;; test.spectec:471.1-471.52
syntax elemtype = reftype

;; test.spectec:473.1-474.83
syntax externtype = 
  | TAG(tagtype : tagtype)
  | GLOBAL(globaltype : globaltype)
  | MEM(memtype : memtype)
  | TABLE(tabletype : tabletype)
  | FUNC(typeuse : typeuse)

;; test.spectec:476.1-477.47
syntax moduletype = 
  | `%->%`(`externtype*` : externtype*, `externtype*` : externtype*)

;; test.spectec:515.1-515.65
def $IN(N : N) : Inn
  ;; test.spectec:516.1-516.18
  def $IN(32) = I32_Inn
  ;; test.spectec:517.1-517.18
  def $IN(64) = I64_Inn

;; test.spectec:519.1-519.65
def $FN(N : N) : Fnn
  ;; test.spectec:520.1-520.18
  def $FN(32) = F32_Fnn
  ;; test.spectec:521.1-521.18
  def $FN(64) = F64_Fnn

;; test.spectec:523.1-523.65
def $JN(N : N) : Jnn
  ;; test.spectec:524.1-524.16
  def $JN(8) = I8_Jnn
  ;; test.spectec:525.1-525.18
  def $JN(16) = I16_Jnn
  ;; test.spectec:526.1-526.18
  def $JN(32) = I32_Jnn
  ;; test.spectec:527.1-527.18
  def $JN(64) = I64_Jnn

;; test.spectec:532.1-532.46
def $size(numtype : numtype) : nat
  ;; test.spectec:541.1-541.20
  def $size(I32_numtype) = 32
  ;; test.spectec:542.1-542.20
  def $size(I64_numtype) = 64
  ;; test.spectec:543.1-543.20
  def $size(F32_numtype) = 32
  ;; test.spectec:544.1-544.20
  def $size(F64_numtype) = 64

;; test.spectec:533.1-533.46
def $vsize(vectype : vectype) : nat
  ;; test.spectec:546.1-546.23
  def $vsize(V128_vectype) = 128

;; test.spectec:534.1-534.46
def $psize(packtype : packtype) : nat
  ;; test.spectec:548.1-548.19
  def $psize(I8_packtype) = 8
  ;; test.spectec:549.1-549.21
  def $psize(I16_packtype) = 16

;; test.spectec:535.1-535.46
def $lsize(lanetype : lanetype) : nat
  ;; test.spectec:551.1-551.37
  def $lsize{numtype : numtype}((numtype : numtype <: lanetype)) = $size(numtype)
  ;; test.spectec:552.1-552.40
  def $lsize{packtype : packtype}((packtype : packtype <: lanetype)) = $psize(packtype)

;; test.spectec:536.1-536.60
def $zsize(storagetype : storagetype) : nat
  ;; test.spectec:554.1-554.37
  def $zsize{numtype : numtype}((numtype : numtype <: storagetype)) = $size(numtype)
  ;; test.spectec:555.1-555.38
  def $zsize{vectype : vectype}((vectype : vectype <: storagetype)) = $vsize(vectype)
  ;; test.spectec:556.1-556.40
  def $zsize{packtype : packtype}((packtype : packtype <: storagetype)) = $psize(packtype)

;; test.spectec:537.1-537.71
def $isize(Inn : Inn) : nat
  ;; test.spectec:558.1-558.29
  def $isize{Inn : Inn}(Inn) = $size((Inn : addrtype <: numtype))

;; test.spectec:538.1-538.71
def $jsize(Jnn : Jnn) : nat
  ;; test.spectec:560.1-560.30
  def $jsize{Jnn : Jnn}(Jnn) = $lsize((Jnn : Jnn <: lanetype))

;; test.spectec:539.1-539.71
def $fsize(Fnn : Fnn) : nat
  ;; test.spectec:559.1-559.29
  def $fsize{Fnn : Fnn}(Fnn) = $size((Fnn : Fnn <: numtype))

;; test.spectec:562.1-562.40
def $inv_isize(nat : nat) : Inn
  ;; test.spectec:566.1-566.25
  def $inv_isize(32) = I32_Inn
  ;; test.spectec:567.1-567.25
  def $inv_isize(64) = I64_Inn

;; test.spectec:563.1-563.40
def $inv_jsize(nat : nat) : Jnn
  ;; test.spectec:570.1-570.24
  def $inv_jsize(8) = I8_Jnn
  ;; test.spectec:571.1-571.25
  def $inv_jsize(16) = I16_Jnn
  ;; test.spectec:572.1-572.34
  def $inv_jsize{n : n}(n) = ($inv_isize(n) : addrtype <: Jnn)

;; test.spectec:564.1-564.40
def $inv_fsize(nat : nat) : Fnn
  ;; test.spectec:568.1-568.25
  def $inv_fsize(32) = F32_Fnn
  ;; test.spectec:569.1-569.25
  def $inv_fsize(64) = F64_Fnn

;; test.spectec:575.1-575.63
def $sizenn(numtype : numtype) : nat
  ;; test.spectec:578.1-578.28
  def $sizenn{nt : numtype}(nt) = $size(nt)

;; test.spectec:576.1-576.63
def $sizenn1(numtype : numtype) : nat
  ;; test.spectec:579.1-579.29
  def $sizenn1{nt : numtype}(nt) = $size(nt)

;; test.spectec:577.1-577.63
def $sizenn2(numtype : numtype) : nat
  ;; test.spectec:580.1-580.29
  def $sizenn2{nt : numtype}(nt) = $size(nt)

;; test.spectec:582.1-582.63
def $vsizenn(vectype : vectype) : nat
  ;; test.spectec:583.1-583.30
  def $vsizenn{vt : vectype}(vt) = $vsize(vt)

;; test.spectec:585.1-585.63
def $psizenn(packtype : packtype) : nat
  ;; test.spectec:586.1-586.30
  def $psizenn{pt : packtype}(pt) = $psize(pt)

;; test.spectec:588.1-588.63
def $lsizenn(lanetype : lanetype) : nat
  ;; test.spectec:591.1-591.30
  def $lsizenn{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:589.1-589.63
def $lsizenn1(lanetype : lanetype) : nat
  ;; test.spectec:592.1-592.31
  def $lsizenn1{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:590.1-590.63
def $lsizenn2(lanetype : lanetype) : nat
  ;; test.spectec:593.1-593.31
  def $lsizenn2{lt : lanetype}(lt) = $lsize(lt)

;; test.spectec:595.1-595.83
def $jsizenn(Jnn : Jnn) : nat
  ;; test.spectec:596.1-596.32
  def $jsizenn{Jnn : Jnn}(Jnn) = $lsize((Jnn : Jnn <: lanetype))

;; test.spectec:598.1-598.42
def $inv_jsizenn(nat : nat) : Jnn
  ;; test.spectec:599.1-599.36
  def $inv_jsizenn{n : n}(n) = $inv_jsize(n)

;; test.spectec:604.1-604.56
def $lunpack(lanetype : lanetype) : numtype
  ;; test.spectec:605.1-605.32
  def $lunpack{numtype : numtype}((numtype : numtype <: lanetype)) = numtype
  ;; test.spectec:606.1-606.29
  def $lunpack{packtype : packtype}((packtype : packtype <: lanetype)) = I32_numtype

;; test.spectec:608.1-608.35
def $unpack(storagetype : storagetype) : valtype
  ;; test.spectec:609.1-609.31
  def $unpack{valtype : valtype}((valtype : valtype <: storagetype)) = valtype
  ;; test.spectec:610.1-610.28
  def $unpack{packtype : packtype}((packtype : packtype <: storagetype)) = I32_valtype

;; test.spectec:612.1-612.73
def $nunpack(storagetype : storagetype) : numtype
  ;; test.spectec:613.1-613.32
  def $nunpack{numtype : numtype}((numtype : numtype <: storagetype)) = numtype
  ;; test.spectec:614.1-614.29
  def $nunpack{packtype : packtype}((packtype : packtype <: storagetype)) = I32_numtype

;; test.spectec:616.1-616.73
def $vunpack(storagetype : storagetype) : vectype
  ;; test.spectec:617.1-617.32
  def $vunpack{vectype : vectype}((vectype : vectype <: storagetype)) = vectype

;; test.spectec:619.1-619.74
def $cunpack(storagetype : storagetype) : consttype
  ;; test.spectec:620.1-620.36
  def $cunpack{consttype : consttype}((consttype : consttype <: storagetype)) = consttype
  ;; test.spectec:621.1-621.29
  def $cunpack{packtype : packtype}((packtype : packtype <: storagetype)) = I32_consttype
  ;; test.spectec:622.1-622.44
  def $cunpack{lanetype : lanetype}((lanetype : lanetype <: storagetype)) = ($lunpack(lanetype) : numtype <: consttype)

;; test.spectec:627.1-627.90
def $minat(addrtype : addrtype, addrtype : addrtype) : addrtype
  ;; test.spectec:628.1-628.64
  def $minat{at_1 : addrtype, at_2 : addrtype}(at_1, at_2) = (if ($size((at_1 : addrtype <: numtype)) <= $size((at_2 : addrtype <: numtype))) then at_1 else at_2)

;; test.spectec:631.1-631.82
def $diffrt(reftype : reftype, reftype : reftype) : reftype
  ;; test.spectec:632.1-632.62
  def $diffrt{`null_1?` : null?, ht_1 : heaptype, ht_2 : heaptype}(REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(?(NULL_null), ht_2)) = REF_reftype(?(), ht_1)
  ;; test.spectec:633.1-633.65
  def $diffrt{`null_1?` : null?, ht_1 : heaptype, ht_2 : heaptype}(REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1), REF_reftype(?(), ht_2)) = REF_reftype(null_1?{null_1 <- `null_1?`}, ht_1)

;; test.spectec:636.1-636.63
def $as_deftype(typeuse : typeuse) : deftype
  ;; test.spectec:637.1-637.25
  def $as_deftype{dt : deftype}((dt : deftype <: typeuse)) = dt

;; test.spectec:644.1-644.87
rec {

;; test.spectec:644.1-644.87
def $tagsxt(externtype*) : tagtype*
  ;; test.spectec:650.1-650.23
  def $tagsxt([]) = []
  ;; test.spectec:651.1-651.44
  def $tagsxt{jt : tagtype, `xt*` : externtype*}([TAG_externtype(jt)] ++ xt*{xt <- `xt*`}) = [jt] ++ $tagsxt(xt*{xt <- `xt*`})
  ;; test.spectec:652.1-652.57
  def $tagsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tagsxt(xt*{xt <- `xt*`})
}

;; test.spectec:645.1-645.90
rec {

;; test.spectec:645.1-645.90
def $globalsxt(externtype*) : globaltype*
  ;; test.spectec:654.1-654.26
  def $globalsxt([]) = []
  ;; test.spectec:655.1-655.53
  def $globalsxt{gt : globaltype, `xt*` : externtype*}([GLOBAL_externtype(gt)] ++ xt*{xt <- `xt*`}) = [gt] ++ $globalsxt(xt*{xt <- `xt*`})
  ;; test.spectec:656.1-656.63
  def $globalsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $globalsxt(xt*{xt <- `xt*`})
}

;; test.spectec:646.1-646.87
rec {

;; test.spectec:646.1-646.87
def $memsxt(externtype*) : memtype*
  ;; test.spectec:658.1-658.23
  def $memsxt([]) = []
  ;; test.spectec:659.1-659.44
  def $memsxt{mt : memtype, `xt*` : externtype*}([MEM_externtype(mt)] ++ xt*{xt <- `xt*`}) = [mt] ++ $memsxt(xt*{xt <- `xt*`})
  ;; test.spectec:660.1-660.57
  def $memsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $memsxt(xt*{xt <- `xt*`})
}

;; test.spectec:647.1-647.89
rec {

;; test.spectec:647.1-647.89
def $tablesxt(externtype*) : tabletype*
  ;; test.spectec:662.1-662.25
  def $tablesxt([]) = []
  ;; test.spectec:663.1-663.50
  def $tablesxt{tt : tabletype, `xt*` : externtype*}([TABLE_externtype(tt)] ++ xt*{xt <- `xt*`}) = [tt] ++ $tablesxt(xt*{xt <- `xt*`})
  ;; test.spectec:664.1-664.61
  def $tablesxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $tablesxt(xt*{xt <- `xt*`})
}

;; test.spectec:648.1-648.88
rec {

;; test.spectec:648.1-648.88
def $funcsxt(externtype*) : deftype*
  ;; test.spectec:666.1-666.24
  def $funcsxt([]) = []
  ;; test.spectec:667.1-667.47
  def $funcsxt{dt : deftype, `xt*` : externtype*}([FUNC_externtype((dt : deftype <: typeuse))] ++ xt*{xt <- `xt*`}) = [dt] ++ $funcsxt(xt*{xt <- `xt*`})
  ;; test.spectec:668.1-668.59
  def $funcsxt{externtype : externtype, `xt*` : externtype*}([externtype] ++ xt*{xt <- `xt*`}) = $funcsxt(xt*{xt <- `xt*`})
}

;; test.spectec:673.1-673.126
rec {

;; test.spectec:673.1-673.126
def $subst_typevar(typevar : typevar, typevar*, typeuse*) : typeuse
  ;; test.spectec:701.1-701.38
  def $subst_typevar{tv : typevar}(tv, [], []) = (tv : typevar <: typeuse)
  ;; test.spectec:702.1-702.95
  def $subst_typevar{tv : typevar, tv_1 : typevar, `tv'*` : typevar*, tu_1 : typeuse, `tu'*` : typeuse*}(tv, [tv_1] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`}) = (if (tv = tv_1) then tu_1 else $subst_typevar(tv, tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}))
}

;; test.spectec:737.1-737.87
rec {

;; test.spectec:737.1-737.87
def $minus_recs(typevar*, typeuse*) : (typevar*, typeuse*)
  ;; test.spectec:738.1-738.39
  def $minus_recs([], []) = ([], [])
  ;; test.spectec:739.1-739.63
  def $minus_recs{n : n, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*}([REC_typevar(n)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  ;; test.spectec:740.1-741.45
  def $minus_recs{x : idx, `tv*` : typevar*, tu_1 : typeuse, `tu*` : typeuse*}([_IDX_typevar(x)] ++ tv*{tv <- `tv*`}, [tu_1] ++ tu*{tu <- `tu*`}) = ([_IDX_typevar(x)] ++ tv'*{tv' <- `tv'*`}, [tu_1] ++ tu'*{tu' <- `tu'*`})
    -- let{`tv'*` : typevar*, `tu'*` : typeuse*} (tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
}

;; test.spectec:683.1-683.112
def $subst_packtype(packtype : packtype, typevar*, typeuse*) : packtype
  ;; test.spectec:723.1-723.39
  def $subst_packtype{pt : packtype, `tv*` : typevar*, `tu*` : typeuse*}(pt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = pt

;; test.spectec:677.1-677.112
def $subst_numtype(numtype : numtype, typevar*, typeuse*) : numtype
  ;; test.spectec:709.1-709.38
  def $subst_numtype{nt : numtype, `tv*` : typevar*, `tu*` : typeuse*}(nt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = nt

;; test.spectec:678.1-678.112
def $subst_vectype(vectype : vectype, typevar*, typeuse*) : vectype
  ;; test.spectec:710.1-710.38
  def $subst_vectype{vt : vectype, `tv*` : typevar*, `tu*` : typeuse*}(vt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = vt

;; test.spectec:674.1-690.112
rec {

;; test.spectec:674.1-674.112
def $subst_typeuse(typeuse : typeuse, typevar*, typeuse*) : typeuse
  ;; test.spectec:705.1-705.66
  def $subst_typeuse{tv' : typevar, `tv*` : typevar*, `tu*` : typeuse*}((tv' : typevar <: typeuse), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = $subst_typevar(tv', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})
  ;; test.spectec:706.1-706.64
  def $subst_typeuse{dt : deftype, `tv*` : typevar*, `tu*` : typeuse*}((dt : deftype <: typeuse), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_deftype(dt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : deftype <: typeuse)

;; test.spectec:679.1-679.112
def $subst_heaptype(heaptype : heaptype, typevar*, typeuse*) : heaptype
  ;; test.spectec:712.1-712.67
  def $subst_heaptype{tv' : typevar, `tv*` : typevar*, `tu*` : typeuse*}((tv' : typevar <: heaptype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_typevar(tv', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : typeuse <: heaptype)
  ;; test.spectec:713.1-713.65
  def $subst_heaptype{dt : deftype, `tv*` : typevar*, `tu*` : typeuse*}((dt : deftype <: heaptype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_deftype(dt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : deftype <: heaptype)
  ;; test.spectec:714.1-714.53
  def $subst_heaptype{ht : heaptype, `tv*` : typevar*, `tu*` : typeuse*}(ht, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ht

;; test.spectec:680.1-680.112
def $subst_reftype(reftype : reftype, typevar*, typeuse*) : reftype
  ;; test.spectec:716.1-716.87
  def $subst_reftype{`null?` : null?, ht : heaptype, `tv*` : typevar*, `tu*` : typeuse*}(REF_reftype(null?{null <- `null?`}, ht), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = REF_reftype(null?{null <- `null?`}, $subst_heaptype(ht, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:681.1-681.112
def $subst_valtype(valtype : valtype, typevar*, typeuse*) : valtype
  ;; test.spectec:718.1-718.64
  def $subst_valtype{nt : numtype, `tv*` : typevar*, `tu*` : typeuse*}((nt : numtype <: valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_numtype(nt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : numtype <: valtype)
  ;; test.spectec:719.1-719.64
  def $subst_valtype{vt : vectype, `tv*` : typevar*, `tu*` : typeuse*}((vt : vectype <: valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_vectype(vt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : vectype <: valtype)
  ;; test.spectec:720.1-720.64
  def $subst_valtype{rt : reftype, `tv*` : typevar*, `tu*` : typeuse*}((rt : reftype <: valtype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_reftype(rt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : reftype <: valtype)
  ;; test.spectec:721.1-721.40
  def $subst_valtype{`tv*` : typevar*, `tu*` : typeuse*}(BOT_valtype, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = BOT_valtype

;; test.spectec:684.1-684.112
def $subst_storagetype(storagetype : storagetype, typevar*, typeuse*) : storagetype
  ;; test.spectec:725.1-725.66
  def $subst_storagetype{t : valtype, `tv*` : typevar*, `tu*` : typeuse*}((t : valtype <: storagetype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_valtype(t, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : valtype <: storagetype)
  ;; test.spectec:726.1-726.69
  def $subst_storagetype{pt : packtype, `tv*` : typevar*, `tu*` : typeuse*}((pt : packtype <: storagetype), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ($subst_packtype(pt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) : packtype <: storagetype)

;; test.spectec:685.1-685.112
def $subst_fieldtype(fieldtype : fieldtype, typevar*, typeuse*) : fieldtype
  ;; test.spectec:728.1-728.82
  def $subst_fieldtype{`mut?` : mut?, zt : storagetype, `tv*` : typevar*, `tu*` : typeuse*}(`%%`_fieldtype(mut?{mut <- `mut?`}, zt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%`_fieldtype(mut?{mut <- `mut?`}, $subst_storagetype(zt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:687.1-687.112
def $subst_comptype(comptype : comptype, typevar*, typeuse*) : comptype
  ;; test.spectec:730.1-730.85
  def $subst_comptype{`ft*` : fieldtype*, `tv*` : typevar*, `tu*` : typeuse*}(STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = STRUCT_comptype(`%`_list($subst_fieldtype(ft, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{ft <- `ft*`}))
  ;; test.spectec:731.1-731.81
  def $subst_comptype{ft : fieldtype, `tv*` : typevar*, `tu*` : typeuse*}(ARRAY_comptype(ft), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = ARRAY_comptype($subst_fieldtype(ft, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:732.1-732.123
  def $subst_comptype{`t_1*` : valtype*, `t_2*` : valtype*, `tv*` : typevar*, `tu*` : typeuse*}(`FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `FUNC%->%`_comptype(`%`_resulttype($subst_valtype(t_1, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{t_1 <- `t_1*`}), `%`_resulttype($subst_valtype(t_2, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{t_2 <- `t_2*`}))

;; test.spectec:688.1-688.112
def $subst_subtype(subtype : subtype, typevar*, typeuse*) : subtype
  ;; test.spectec:734.1-735.74
  def $subst_subtype{`final?` : final?, `tu'*` : typeuse*, ct : comptype, `tv*` : typevar*, `tu*` : typeuse*}(SUB_subtype(final?{final <- `final?`}, tu'*{tu' <- `tu'*`}, ct), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = SUB_subtype(final?{final <- `final?`}, $subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{tu' <- `tu'*`}, $subst_comptype(ct, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:689.1-689.112
def $subst_rectype(rectype : rectype, typevar*, typeuse*) : rectype
  ;; test.spectec:743.1-744.45
  def $subst_rectype{`st*` : subtype*, `tv*` : typevar*, `tu*` : typeuse*}(REC_rectype(`%`_list(st*{st <- `st*`})), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = REC_rectype(`%`_list($subst_subtype(st, tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`})*{st <- `st*`}))
    -- let{`tv'*` : typevar*, `tu'*` : typeuse*} (tv'*{tv' <- `tv'*`}, tu'*{tu' <- `tu'*`}) = $minus_recs(tv*{tv <- `tv*`}, tu*{tu <- `tu*`})

;; test.spectec:690.1-690.112
def $subst_deftype(deftype : deftype, typevar*, typeuse*) : deftype
  ;; test.spectec:749.1-749.80
  def $subst_deftype{qt : rectype, i : n, `tv*` : typevar*, `tu*` : typeuse*}(_DEF_deftype(qt, i), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = _DEF_deftype($subst_rectype(qt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}), i)
}

;; test.spectec:676.1-676.112
def $subst_addrtype(addrtype : addrtype, typevar*, typeuse*) : addrtype
  ;; test.spectec:708.1-708.39
  def $subst_addrtype{at : addrtype, `tv*` : typevar*, `tu*` : typeuse*}(at, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = at

;; test.spectec:692.1-692.112
def $subst_tagtype(tagtype : tagtype, typevar*, typeuse*) : tagtype
  ;; test.spectec:751.1-751.66
  def $subst_tagtype{tu' : typeuse, `tv*` : typevar*, `tu*` : typeuse*}(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = $subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`})

;; test.spectec:693.1-693.112
def $subst_globaltype(globaltype : globaltype, typevar*, typeuse*) : globaltype
  ;; test.spectec:752.1-752.77
  def $subst_globaltype{`mut?` : mut?, t : valtype, `tv*` : typevar*, `tu*` : typeuse*}(`%%`_globaltype(mut?{mut <- `mut?`}, t), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%`_globaltype(mut?{mut <- `mut?`}, $subst_valtype(t, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:694.1-694.112
def $subst_memtype(memtype : memtype, typevar*, typeuse*) : memtype
  ;; test.spectec:753.1-753.58
  def $subst_memtype{at : addrtype, lim : limits, `tv*` : typevar*, `tu*` : typeuse*}(`%%PAGE`_memtype(at, lim), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%PAGE`_memtype(at, lim)

;; test.spectec:695.1-695.112
def $subst_tabletype(tabletype : tabletype, typevar*, typeuse*) : tabletype
  ;; test.spectec:754.1-754.82
  def $subst_tabletype{at : addrtype, lim : limits, rt : reftype, `tv*` : typevar*, `tu*` : typeuse*}(`%%%`_tabletype(at, lim, rt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%%%`_tabletype(at, lim, $subst_reftype(rt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:697.1-697.112
def $subst_externtype(externtype : externtype, typevar*, typeuse*) : externtype
  ;; test.spectec:756.1-756.77
  def $subst_externtype{jt : tagtype, `tv*` : typevar*, `tu*` : typeuse*}(TAG_externtype(jt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = TAG_externtype($subst_tagtype(jt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:757.1-757.86
  def $subst_externtype{gt : globaltype, `tv*` : typevar*, `tu*` : typeuse*}(GLOBAL_externtype(gt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = GLOBAL_externtype($subst_globaltype(gt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:758.1-758.83
  def $subst_externtype{tt : tabletype, `tv*` : typevar*, `tu*` : typeuse*}(TABLE_externtype(tt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = TABLE_externtype($subst_tabletype(tt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:759.1-759.77
  def $subst_externtype{mt : memtype, `tv*` : typevar*, `tu*` : typeuse*}(MEM_externtype(mt), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = MEM_externtype($subst_memtype(mt, tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))
  ;; test.spectec:760.1-760.81
  def $subst_externtype{tu' : typeuse, `tv*` : typevar*, `tu*` : typeuse*}(FUNC_externtype(tu'), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = FUNC_externtype($subst_typeuse(tu', tv*{tv <- `tv*`}, tu*{tu <- `tu*`}))

;; test.spectec:698.1-698.112
def $subst_moduletype(moduletype : moduletype, typevar*, typeuse*) : moduletype
  ;; test.spectec:762.1-762.123
  def $subst_moduletype{`xt_1*` : externtype*, `xt_2*` : externtype*, `tv*` : typevar*, `tu*` : typeuse*}(`%->%`_moduletype(xt_1*{xt_1 <- `xt_1*`}, xt_2*{xt_2 <- `xt_2*`}), tv*{tv <- `tv*`}, tu*{tu <- `tu*`}) = `%->%`_moduletype($subst_externtype(xt_1, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{xt_1 <- `xt_1*`}, $subst_externtype(xt_2, tv*{tv <- `tv*`}, tu*{tu <- `tu*`})*{xt_2 <- `xt_2*`})

;; test.spectec:767.1-767.94
def $subst_all_valtype(valtype : valtype, typeuse*) : valtype
  ;; test.spectec:777.1-777.74
  def $subst_all_valtype{t : valtype, n : n, `tu*` : typeuse*, i : nat}(t, tu^n{tu <- `tu*`}) = $subst_valtype(t, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:768.1-768.94
def $subst_all_reftype(reftype : reftype, typeuse*) : reftype
  ;; test.spectec:778.1-778.76
  def $subst_all_reftype{rt : reftype, n : n, `tu*` : typeuse*, i : nat}(rt, tu^n{tu <- `tu*`}) = $subst_reftype(rt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:769.1-769.94
def $subst_all_deftype(deftype : deftype, typeuse*) : deftype
  ;; test.spectec:779.1-779.76
  def $subst_all_deftype{dt : deftype, n : n, `tu*` : typeuse*, i : nat}(dt, tu^n{tu <- `tu*`}) = $subst_deftype(dt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:770.1-770.94
def $subst_all_tagtype(tagtype : tagtype, typeuse*) : tagtype
  ;; test.spectec:780.1-780.76
  def $subst_all_tagtype{jt : tagtype, n : n, `tu*` : typeuse*, i : nat}(jt, tu^n{tu <- `tu*`}) = $subst_tagtype(jt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:771.1-771.103
def $subst_all_globaltype(globaltype : globaltype, typeuse*) : globaltype
  ;; test.spectec:781.1-781.82
  def $subst_all_globaltype{gt : globaltype, n : n, `tu*` : typeuse*, i : nat}(gt, tu^n{tu <- `tu*`}) = $subst_globaltype(gt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:772.1-772.94
def $subst_all_memtype(memtype : memtype, typeuse*) : memtype
  ;; test.spectec:782.1-782.76
  def $subst_all_memtype{mt : memtype, n : n, `tu*` : typeuse*, i : nat}(mt, tu^n{tu <- `tu*`}) = $subst_memtype(mt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:773.1-773.100
def $subst_all_tabletype(tabletype : tabletype, typeuse*) : tabletype
  ;; test.spectec:783.1-783.80
  def $subst_all_tabletype{tt : tabletype, n : n, `tu*` : typeuse*, i : nat}(tt, tu^n{tu <- `tu*`}) = $subst_tabletype(tt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:774.1-774.103
def $subst_all_externtype(externtype : externtype, typeuse*) : externtype
  ;; test.spectec:784.1-784.82
  def $subst_all_externtype{xt : externtype, n : n, `tu*` : typeuse*, i : nat}(xt, tu^n{tu <- `tu*`}) = $subst_externtype(xt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:775.1-775.103
def $subst_all_moduletype(moduletype : moduletype, typeuse*) : moduletype
  ;; test.spectec:785.1-785.84
  def $subst_all_moduletype{mmt : moduletype, n : n, `tu*` : typeuse*, i : nat}(mmt, tu^n{tu <- `tu*`}) = $subst_moduletype(mmt, _IDX_typevar(`%`_typeidx(i))^(i<n){}, tu^n{tu <- `tu*`})

;; test.spectec:787.1-787.97
rec {

;; test.spectec:787.1-787.97
def $subst_all_deftypes(deftype*, typeuse*) : deftype*
  ;; test.spectec:788.1-788.40
  def $subst_all_deftypes{`tu*` : typeuse*}([], tu*{tu <- `tu*`}) = []
  ;; test.spectec:789.1-789.101
  def $subst_all_deftypes{dt_1 : deftype, `dt*` : deftype*, `tu*` : typeuse*}([dt_1] ++ dt*{dt <- `dt*`}, tu*{tu <- `tu*`}) = [$subst_all_deftype(dt_1, tu*{tu <- `tu*`})] ++ $subst_all_deftypes(dt*{dt <- `dt*`}, tu*{tu <- `tu*`})
}

;; test.spectec:794.1-794.88
def $rollrt(typeidx : typeidx, rectype : rectype) : rectype
  ;; test.spectec:799.1-800.32
  def $rollrt{x : idx, rectype : rectype, i : nat, n : n, `subtype*` : subtype*}(x, rectype) = REC_rectype(`%`_list($subst_subtype(subtype, _IDX_typevar(`%`_typeidx((x!`%`_idx.0 + i)))^(i<n){}, REC_typeuse(i)^(i<n){})^n{subtype <- `subtype*`}))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:795.1-795.90
def $unrollrt(rectype : rectype) : rectype
  ;; test.spectec:801.1-802.32
  def $unrollrt{rectype : rectype, i : nat, n : n, `subtype*` : subtype*}(rectype) = REC_rectype(`%`_list($subst_subtype(subtype, REC_typevar(i)^(i<n){}, _DEF_typeuse(rectype, i)^(i<n){})^n{subtype <- `subtype*`}))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:796.1-796.90
def $rolldt(typeidx : typeidx, rectype : rectype) : deftype*
  ;; test.spectec:804.1-804.100
  def $rolldt{x : idx, rectype : rectype, n : n, `subtype*` : subtype*}(x, rectype) = _DEF_deftype(REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})), i)^(i<n){}
    -- if ($rollrt(x, rectype) = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))

;; test.spectec:797.1-797.90
def $unrolldt(deftype : deftype) : subtype
  ;; test.spectec:805.1-805.98
  def $unrolldt{rectype : rectype, i : n}(_DEF_deftype(rectype, i)) = subtype*{subtype <- `subtype*`}[i]
    -- let{`subtype*` : subtype*} REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})) = $unrollrt(rectype)

;; test.spectec:810.1-810.36
def $free_addrtype(addrtype : addrtype) : free
  ;; test.spectec:840.1-840.34
  def $free_addrtype{addrtype : addrtype}(addrtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:811.1-811.34
def $free_numtype(numtype : numtype) : free
  ;; test.spectec:842.1-842.32
  def $free_numtype{numtype : numtype}(numtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:812.1-812.36
def $free_packtype(packtype : packtype) : free
  ;; test.spectec:844.1-844.34
  def $free_packtype{packtype : packtype}(packtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:813.1-813.36
def $free_lanetype(lanetype : lanetype) : free
  ;; test.spectec:846.1-846.53
  def $free_lanetype{numtype : numtype}((numtype : numtype <: lanetype)) = $free_numtype(numtype)
  ;; test.spectec:847.1-847.56
  def $free_lanetype{packtype : packtype}((packtype : packtype <: lanetype)) = $free_packtype(packtype)

;; test.spectec:814.1-814.34
def $free_vectype(vectype : vectype) : free
  ;; test.spectec:849.1-849.32
  def $free_vectype{vectype : vectype}(vectype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:815.1-815.38
def $free_consttype(consttype : consttype) : free
  ;; test.spectec:851.1-851.54
  def $free_consttype{numtype : numtype}((numtype : numtype <: consttype)) = $free_numtype(numtype)
  ;; test.spectec:852.1-852.54
  def $free_consttype{vectype : vectype}((vectype : vectype <: consttype)) = $free_vectype(vectype)

;; test.spectec:816.1-816.42
def $free_absheaptype(absheaptype : absheaptype) : free
  ;; test.spectec:854.1-854.40
  def $free_absheaptype{absheaptype : absheaptype}(absheaptype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:819.1-819.34
def $free_typevar(typevar : typevar) : free
  ;; test.spectec:859.1-859.57
  def $free_typevar{typeidx : typeidx}(_IDX_typevar(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:860.1-860.30
  def $free_typevar{n : n}(REC_typevar(n)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:817.1-856.34
rec {

;; test.spectec:817.1-817.36
def $free_heaptype(heaptype : heaptype) : free
  ;; test.spectec:865.1-865.65
  def $free_heaptype{absheaptype : absheaptype}((absheaptype : absheaptype <: heaptype)) = $free_absheaptype(absheaptype)
  ;; test.spectec:866.1-866.53
  def $free_heaptype{typeuse : typeuse}((typeuse : typeuse <: heaptype)) = $free_typeuse(typeuse)

;; test.spectec:818.1-818.34
def $free_reftype(reftype : reftype) : free
  ;; test.spectec:868.1-868.65
  def $free_reftype{`null?` : null?, heaptype : heaptype}(REF_reftype(null?{null <- `null?`}, heaptype)) = $free_heaptype(heaptype)

;; test.spectec:820.1-820.34
def $free_typeuse(typeuse : typeuse) : free
  ;; test.spectec:862.1-862.52
  def $free_typeuse{typevar : typevar}((typevar : typevar <: typeuse)) = $free_typevar(typevar)
  ;; test.spectec:863.1-863.52
  def $free_typeuse{deftype : deftype}((deftype : deftype <: typeuse)) = $free_deftype(deftype)

;; test.spectec:821.1-821.34
def $free_valtype(valtype : valtype) : free
  ;; test.spectec:870.1-870.52
  def $free_valtype{numtype : numtype}((numtype : numtype <: valtype)) = $free_numtype(numtype)
  ;; test.spectec:871.1-871.52
  def $free_valtype{vectype : vectype}((vectype : vectype <: valtype)) = $free_vectype(vectype)
  ;; test.spectec:872.1-872.52
  def $free_valtype{reftype : reftype}((reftype : reftype <: valtype)) = $free_reftype(reftype)
  ;; test.spectec:873.1-873.28
  def $free_valtype(BOT_valtype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:823.1-823.40
def $free_resulttype(resulttype : resulttype) : free
  ;; test.spectec:875.1-875.69
  def $free_resulttype{`valtype*` : valtype*}(`%`_resulttype(valtype*{valtype <- `valtype*`})) = $free_list($free_valtype(valtype)*{valtype <- `valtype*`})

;; test.spectec:824.1-824.42
def $free_storagetype(storagetype : storagetype) : free
  ;; test.spectec:877.1-877.56
  def $free_storagetype{valtype : valtype}((valtype : valtype <: storagetype)) = $free_valtype(valtype)
  ;; test.spectec:878.1-878.59
  def $free_storagetype{packtype : packtype}((packtype : packtype <: storagetype)) = $free_packtype(packtype)

;; test.spectec:825.1-825.38
def $free_fieldtype(fieldtype : fieldtype) : free
  ;; test.spectec:880.1-880.71
  def $free_fieldtype{`mut?` : mut?, storagetype : storagetype}(`%%`_fieldtype(mut?{mut <- `mut?`}, storagetype)) = $free_storagetype(storagetype)

;; test.spectec:826.1-826.36
def $free_comptype(comptype : comptype) : free
  ;; test.spectec:882.1-882.80
  def $free_comptype{`fieldtype*` : fieldtype*}(STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))) = $free_list($free_fieldtype(fieldtype)*{fieldtype <- `fieldtype*`})
  ;; test.spectec:883.1-883.65
  def $free_comptype{fieldtype : fieldtype}(ARRAY_comptype(fieldtype)) = $free_fieldtype(fieldtype)
  ;; test.spectec:884.1-884.121
  def $free_comptype{resulttype_1 : resulttype, resulttype_2 : resulttype}(`FUNC%->%`_comptype(resulttype_1, resulttype_2)) = $free_resulttype(resulttype_1) +++ $free_resulttype(resulttype_2)

;; test.spectec:827.1-827.34
def $free_subtype(subtype : subtype) : free
  ;; test.spectec:886.1-887.66
  def $free_subtype{`final?` : final?, `typeuse*` : typeuse*, comptype : comptype}(SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype)) = $free_list($free_typeuse(typeuse)*{typeuse <- `typeuse*`}) +++ $free_comptype(comptype)

;; test.spectec:828.1-828.34
def $free_rectype(rectype : rectype) : free
  ;; test.spectec:889.1-889.70
  def $free_rectype{`subtype*` : subtype*}(REC_rectype(`%`_list(subtype*{subtype <- `subtype*`}))) = $free_list($free_subtype(subtype)*{subtype <- `subtype*`})

;; test.spectec:856.1-856.34
def $free_deftype(deftype : deftype) : free
  ;; test.spectec:857.1-857.59
  def $free_deftype{rectype : rectype, n : n}(_DEF_deftype(rectype, n)) = $free_rectype(rectype)
}

;; test.spectec:830.1-830.34
def $free_tagtype(tagtype : tagtype) : free
  ;; test.spectec:891.1-891.52
  def $free_tagtype{deftype : deftype}((deftype : deftype <: typeuse)) = $free_deftype(deftype)

;; test.spectec:831.1-831.40
def $free_globaltype(globaltype : globaltype) : free
  ;; test.spectec:893.1-893.60
  def $free_globaltype{`mut?` : mut?, valtype : valtype}(`%%`_globaltype(mut?{mut <- `mut?`}, valtype)) = $free_valtype(valtype)

;; test.spectec:832.1-832.34
def $free_memtype(memtype : memtype) : free
  ;; test.spectec:895.1-895.67
  def $free_memtype{addrtype : addrtype, limits : limits}(`%%PAGE`_memtype(addrtype, limits)) = $free_addrtype(addrtype)

;; test.spectec:833.1-833.38
def $free_tabletype(tabletype : tabletype) : free
  ;; test.spectec:897.1-898.53
  def $free_tabletype{addrtype : addrtype, limits : limits, reftype : reftype}(`%%%`_tabletype(addrtype, limits, reftype)) = $free_addrtype(addrtype) +++ $free_reftype(reftype)

;; test.spectec:834.1-834.36
def $free_datatype(datatype : datatype) : free
  ;; test.spectec:900.1-900.28
  def $free_datatype(OK_datatype) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:835.1-835.36
def $free_elemtype(elemtype : elemtype) : free
  ;; test.spectec:902.1-902.53
  def $free_elemtype{reftype : reftype}(reftype) = $free_reftype(reftype)

;; test.spectec:836.1-836.40
def $free_externtype(externtype : externtype) : free
  ;; test.spectec:904.1-904.59
  def $free_externtype{tagtype : tagtype}(TAG_externtype(tagtype)) = $free_tagtype(tagtype)
  ;; test.spectec:905.1-905.71
  def $free_externtype{globaltype : globaltype}(GLOBAL_externtype(globaltype)) = $free_globaltype(globaltype)
  ;; test.spectec:906.1-906.59
  def $free_externtype{memtype : memtype}(MEM_externtype(memtype)) = $free_memtype(memtype)
  ;; test.spectec:907.1-907.67
  def $free_externtype{tabletype : tabletype}(TABLE_externtype(tabletype)) = $free_tabletype(tabletype)
  ;; test.spectec:908.1-908.60
  def $free_externtype{typeuse : typeuse}(FUNC_externtype(typeuse)) = $free_typeuse(typeuse)

;; test.spectec:837.1-837.40
def $free_moduletype(moduletype : moduletype) : free
  ;; test.spectec:910.1-912.46
  def $free_moduletype{`externtype_1*` : externtype*, `externtype_2*` : externtype*}(`%->%`_moduletype(externtype_1*{externtype_1 <- `externtype_1*`}, externtype_2*{externtype_2 <- `externtype_2*`})) = $free_list($free_externtype(externtype_1)*{externtype_1 <- `externtype_1*`}) +++ $free_list($free_externtype(externtype_2)*{externtype_2 <- `externtype_2*`})

;; test.spectec:927.1-927.21
syntax num_(numtype : numtype)
  ;; test.spectec:928.1-928.36
  syntax num_{Inn : Inn}((Inn : addrtype <: numtype)) = iN($sizenn((Inn : addrtype <: numtype)))


  ;; test.spectec:929.1-929.36
  syntax num_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = fN($sizenn((Fnn : Fnn <: numtype)))


;; test.spectec:931.1-931.38
syntax pack_{Pnn : Pnn}(Pnn) = iN($psizenn(Pnn))

;; test.spectec:933.1-933.23
syntax lane_(lanetype : lanetype)
  ;; test.spectec:934.1-934.38
  syntax lane_{numtype : numtype}((numtype : numtype <: lanetype)) = num_(numtype)


  ;; test.spectec:935.1-935.41
  syntax lane_{packtype : packtype}((packtype : packtype <: lanetype)) = pack_(packtype)


  ;; test.spectec:936.1-936.36
  syntax lane_{Jnn : Jnn}((Jnn : Jnn <: lanetype)) = iN($lsize((Jnn : Jnn <: lanetype)))


;; test.spectec:938.1-938.35
syntax vec_{Vnn : Vnn}(Vnn) = vN($vsize(Vnn))

;; test.spectec:940.1-940.25
syntax lit_(storagetype : storagetype)
  ;; test.spectec:941.1-941.37
  syntax lit_{numtype : numtype}((numtype : numtype <: storagetype)) = num_(numtype)


  ;; test.spectec:942.1-942.37
  syntax lit_{vectype : vectype}((vectype : vectype <: storagetype)) = vec_(vectype)


  ;; test.spectec:943.1-943.40
  syntax lit_{packtype : packtype}((packtype : packtype <: storagetype)) = pack_(packtype)


;; test.spectec:948.1-948.56
syntax sz = 
  | `%`(i : nat)
    -- if ((((i = 8) \/ (i = 16)) \/ (i = 32)) \/ (i = 64))

;; test.spectec:949.1-949.42
syntax sx = 
  | U
  | S

;; test.spectec:951.1-951.22
syntax unop_(numtype : numtype)
  ;; test.spectec:952.1-952.102
  syntax unop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | CLZ
  | CTZ
  | POPCNT
  | EXTEND(sz : sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : addrtype <: numtype)))


  ;; test.spectec:953.1-953.70
  syntax unop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; test.spectec:955.1-955.23
syntax binop_(numtype : numtype)
  ;; test.spectec:956.1-958.67
  syntax binop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
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


  ;; test.spectec:959.1-960.87
  syntax binop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | ADD
  | SUB
  | MUL
  | DIV
  | MIN
  | MAX
  | COPYSIGN


;; test.spectec:962.1-962.24
syntax testop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | EQZ

;; test.spectec:966.1-966.23
syntax relop_(numtype : numtype)
  ;; test.spectec:967.1-970.54
  syntax relop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | EQ
  | NE
  | LT(sx : sx)
  | GT(sx : sx)
  | LE(sx : sx)
  | GE(sx : sx)


  ;; test.spectec:971.1-972.32
  syntax relop_{Fnn : Fnn}((Fnn : Fnn <: numtype)) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


;; test.spectec:975.1-975.37
syntax cvtop__(numtype_1 : numtype, numtype_2 : numtype)
  ;; test.spectec:976.1-978.57
  syntax cvtop__{Inn_1 : Inn, Inn_2 : Inn}((Inn_1 : addrtype <: numtype), (Inn_2 : addrtype <: numtype)) = 
  | EXTEND(sx : sx)
    -- if ($sizenn1((Inn_1 : addrtype <: numtype)) < $sizenn2((Inn_2 : addrtype <: numtype)))
  | WRAP
    -- if ($sizenn1((Inn_1 : addrtype <: numtype)) > $sizenn2((Inn_2 : addrtype <: numtype)))


  ;; test.spectec:979.1-981.57
  syntax cvtop__{Inn_1 : Inn, Fnn_2 : Fnn}((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype)) = 
  | CONVERT(sx : sx)
  | REINTERPRET
    -- if ($sizenn1((Inn_1 : addrtype <: numtype)) = $sizenn2((Fnn_2 : Fnn <: numtype)))


  ;; test.spectec:982.1-985.57
  syntax cvtop__{Fnn_1 : Fnn, Inn_2 : Inn}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype)) = 
  | TRUNC(sx : sx)
  | TRUNC_SAT(sx : sx)
  | REINTERPRET
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) = $sizenn2((Inn_2 : addrtype <: numtype)))


  ;; test.spectec:986.1-988.57
  syntax cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype)) = 
  | PROMOTE
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) < $sizenn2((Fnn_2 : Fnn <: numtype)))
  | DEMOTE
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) > $sizenn2((Fnn_2 : Fnn <: numtype)))


;; test.spectec:993.1-993.60
syntax dim = 
  | `%`(i : nat)
    -- if (((((i = 1) \/ (i = 2)) \/ (i = 4)) \/ (i = 8)) \/ (i = 16))

;; test.spectec:994.1-995.40
syntax shape = 
  | `%X%`(lanetype : lanetype, dim : dim)
    -- if (($lsize(lanetype) * dim!`%`_dim.0) = 128)

;; test.spectec:998.1-998.43
def $dim(shape : shape) : dim
  ;; test.spectec:999.1-999.22
  def $dim{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = `%`_dim(N)

;; test.spectec:1001.1-1001.58
def $lanetype(shape : shape) : lanetype
  ;; test.spectec:1002.1-1002.29
  def $lanetype{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = Lnn

;; test.spectec:1004.1-1004.57
def $unpackshape(shape : shape) : numtype
  ;; test.spectec:1005.1-1005.42
  def $unpackshape{Lnn : Lnn, N : N}(`%X%`_shape(Lnn, `%`_dim(N))) = $lunpack(Lnn)

;; test.spectec:1008.1-1008.78
syntax ishape = 
  | `%`(shape : shape) {Jnn : Jnn}
    -- if ($lanetype(shape) = (Jnn : Jnn <: lanetype))

;; test.spectec:1009.1-1009.77
syntax bshape = 
  | `%`(shape : shape)
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
syntax vunop_(shape : shape)
  ;; test.spectec:1023.1-1024.36
  syntax vunop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | ABS
  | NEG
  | POPCNT
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) = 8)


  ;; test.spectec:1025.1-1026.35
  syntax vunop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | ABS
  | NEG
  | SQRT
  | CEIL
  | FLOOR
  | TRUNC
  | NEAREST


;; test.spectec:1028.1-1028.43
syntax vbinop_(shape : shape)
  ;; test.spectec:1029.1-1039.72
  syntax vbinop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | ADD
  | SUB
  | ADD_SAT(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 16)
  | SUB_SAT(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 16)
  | MUL
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) >= 16)
  | AVGRU
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 16)
  | Q15MULR_SATS
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) = 16)
  | RELAXED_Q15MULRS
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) = 16)
  | MIN(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 32)
  | MAX(sx : sx)
    -- if ($lsizenn((Jnn : Jnn <: lanetype)) <= 32)


  ;; test.spectec:1040.1-1042.30
  syntax vbinop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
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


;; test.spectec:1044.1-1044.44
syntax vternop_(shape : shape)
  ;; test.spectec:1045.1-1045.46
  syntax vternop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | RELAXED_LANESELECT


  ;; test.spectec:1046.1-1046.56
  syntax vternop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | RELAXED_MADD
  | RELAXED_NMADD


;; test.spectec:1048.1-1048.44
syntax vtestop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | ALL_TRUE

;; test.spectec:1052.1-1052.43
syntax vrelop_(shape : shape)
  ;; test.spectec:1053.1-1057.67
  syntax vrelop_{Jnn : Jnn, M : M}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))) = 
  | EQ
  | NE
  | LT(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))
  | GT(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))
  | LE(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))
  | GE(sx : sx)
    -- if (($lsizenn((Jnn : Jnn <: lanetype)) =/= 64) \/ (sx = S_sx))


  ;; test.spectec:1058.1-1058.54
  syntax vrelop_{Fnn : Fnn, M : M}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))) = 
  | EQ
  | NE
  | LT
  | GT
  | LE
  | GE


;; test.spectec:1060.1-1060.46
syntax vshiftop_{Jnn : Jnn, M : M}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)))) = 
  | SHL
  | SHR(sx : sx)

;; test.spectec:1063.1-1063.47
syntax vswizzlop_{M : M}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M)))) = 
  | SWIZZLE
  | RELAXED_SWIZZLE

;; test.spectec:1066.1-1066.59
syntax vextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | EXTADD_PAIRWISE(sx : sx)
    -- if ((16 <= (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype)))) /\ (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) <= 32)))

;; test.spectec:1071.1-1071.60
syntax vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | EXTMUL(half : half, sx : sx)
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) >= 16))
  | DOTS
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32))
  | RELAXED_DOTS
    -- if (((2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 16))

;; test.spectec:1080.1-1080.61
syntax vextternop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)))) = 
  | RELAXED_DOT_ADDS
    -- if (((4 * $lsizenn1((Jnn_1 : Jnn <: lanetype))) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32))

;; test.spectec:1085.1-1085.55
syntax vcvtop__(shape_1 : shape, shape_2 : shape)
  ;; test.spectec:1086.1-1088.53
  syntax vcvtop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))) = 
  | EXTEND(half : half, sx : sx)
    -- if ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))))


  ;; test.spectec:1089.1-1092.67
  syntax vcvtop__{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2))) = 
  | CONVERT(`half?` : half?, sx : sx)
    -- if (((($sizenn2((Fnn_2 : Fnn <: numtype)) = $lsizenn1((Jnn_1 : Jnn <: lanetype))) /\ ($lsizenn1((Jnn_1 : Jnn <: lanetype)) = 32)) /\ (half?{half <- `half?`} = ?())) \/ (($sizenn2((Fnn_2 : Fnn <: numtype)) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype)))) /\ (half?{half <- `half?`} = ?(LOW_half))))


  ;; test.spectec:1093.1-1099.68
  syntax vcvtop__{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))) = 
  | TRUNC_SAT(sx : sx, `zero?` : zero?)
    -- if (((($sizenn1((Fnn_1 : Fnn <: numtype)) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $lsizenn2((Jnn_2 : Jnn <: lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))
  | RELAXED_TRUNC(sx : sx, `zero?` : zero?)
    -- if (((($sizenn1((Fnn_1 : Fnn <: numtype)) = $lsizenn2((Jnn_2 : Jnn <: lanetype))) /\ ($lsizenn2((Jnn_2 : Jnn <: lanetype)) = 32)) /\ (zero?{zero <- `zero?`} = ?())) \/ (($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $lsizenn2((Jnn_2 : Jnn <: lanetype)))) /\ (zero?{zero <- `zero?`} = ?(ZERO_zero))))


  ;; test.spectec:1100.1-1104.51
  syntax vcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2))) = 
  | DEMOTE(zero : zero)
    -- if ($sizenn1((Fnn_1 : Fnn <: numtype)) = (2 * $sizenn2((Fnn_2 : Fnn <: numtype))))
  | PROMOTELOW
    -- if ((2 * $sizenn1((Fnn_1 : Fnn <: numtype))) = $sizenn2((Fnn_2 : Fnn <: numtype)))


;; test.spectec:1109.1-1109.69
syntax memarg = 
{
  ALIGN u32,
  OFFSET u64
}

;; test.spectec:1113.1-1113.24
syntax loadop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | `%_%`(sz : sz, sx : sx)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : addrtype <: numtype)))

;; test.spectec:1116.1-1116.25
syntax storeop_{Inn : Inn}((Inn : addrtype <: numtype)) = 
  | `%`(sz : sz)
    -- if (sz!`%`_sz.0 < $sizenn((Inn : addrtype <: numtype)))

;; test.spectec:1119.1-1122.59
syntax vloadop_{vectype : vectype}(vectype) = 
  | `SHAPE%X%_%`(sz : sz, M : M, sx : sx)
    -- if (((sz!`%`_sz.0 * M) : nat <:> rat) = (($vsize(vectype) : nat <:> rat) / (2 : nat <:> rat)))
  | SPLAT(sz : sz)
  | ZERO(sz : sz)
    -- if (sz!`%`_sz.0 >= 32)

;; test.spectec:1127.1-1129.17
syntax blocktype = 
  | _RESULT(`valtype?` : valtype?)
  | _IDX(typeidx : typeidx)

;; test.spectec:4102.1-4102.39
syntax addr = nat

;; test.spectec:4111.1-4111.51
syntax arrayaddr = addr

;; test.spectec:1177.1-1181.27
syntax catch = 
  | CATCH(tagidx : tagidx, labelidx : labelidx)
  | CATCH_REF(tagidx : tagidx, labelidx : labelidx)
  | CATCH_ALL(labelidx : labelidx)
  | CATCH_ALL_REF(labelidx : labelidx)

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
  | TAG(tagaddr : tagaddr)
  | GLOBAL(globaladdr : globaladdr)
  | MEM(memaddr : memaddr)
  | TABLE(tableaddr : tableaddr)
  | FUNC(funcaddr : funcaddr)

;; test.spectec:4176.1-4177.33
syntax exportinst = 
{
  NAME name,
  ADDR externaddr
}

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

;; test.spectec:4113.1-4113.49
syntax hostaddr = addr

;; test.spectec:4110.1-4110.56
syntax structaddr = addr

;; test.spectec:4130.1-4138.19
rec {

;; test.spectec:4130.1-4138.19
syntax ref = 
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)
}

;; test.spectec:4140.1-4141.20
syntax val = 
  | CONST(numtype : numtype, num_(numtype))
  | VCONST(vectype : vectype, vec_(vectype))
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)

;; test.spectec:4222.1-4223.40
syntax frame = 
{
  LOCALS val?*,
  MODULE moduleinst
}

;; test.spectec:4228.1-4234.9
rec {

;; test.spectec:4228.1-4234.9
syntax instr = 
  | NOP
  | UNREACHABLE
  | DROP
  | SELECT(`valtype*?` : valtype*?)
  | BLOCK(blocktype : blocktype, `instr*` : instr*)
  | LOOP(blocktype : blocktype, `instr*` : instr*)
  | `IF%%ELSE%`(blocktype : blocktype, `instr*` : instr*, `instr*` : instr*)
  | BR(labelidx : labelidx)
  | BR_IF(labelidx : labelidx)
  | BR_TABLE(`labelidx*` : labelidx*, labelidx : labelidx)
  | BR_ON_NULL(labelidx : labelidx)
  | BR_ON_NON_NULL(labelidx : labelidx)
  | BR_ON_CAST(labelidx : labelidx, reftype : reftype, reftype : reftype)
  | BR_ON_CAST_FAIL(labelidx : labelidx, reftype : reftype, reftype : reftype)
  | CALL(funcidx : funcidx)
  | CALL_REF(typeuse : typeuse)
  | CALL_INDIRECT(tableidx : tableidx, typeuse : typeuse)
  | RETURN
  | RETURN_CALL(funcidx : funcidx)
  | RETURN_CALL_REF(typeuse : typeuse)
  | RETURN_CALL_INDIRECT(tableidx : tableidx, typeuse : typeuse)
  | THROW(tagidx : tagidx)
  | THROW_REF
  | TRY_TABLE(blocktype : blocktype, list(syntax catch), `instr*` : instr*)
  | `LOCAL.GET`(localidx : localidx)
  | `LOCAL.SET`(localidx : localidx)
  | `LOCAL.TEE`(localidx : localidx)
  | `GLOBAL.GET`(globalidx : globalidx)
  | `GLOBAL.SET`(globalidx : globalidx)
  | `TABLE.GET`(tableidx : tableidx)
  | `TABLE.SET`(tableidx : tableidx)
  | `TABLE.SIZE`(tableidx : tableidx)
  | `TABLE.GROW`(tableidx : tableidx)
  | `TABLE.FILL`(tableidx : tableidx)
  | `TABLE.COPY`(tableidx : tableidx, tableidx : tableidx)
  | `TABLE.INIT`(tableidx : tableidx, elemidx : elemidx)
  | `ELEM.DROP`(elemidx : elemidx)
  | LOAD(numtype : numtype, loadop_(numtype)?, memidx : memidx, memarg : memarg)
  | STORE(numtype : numtype, storeop_(numtype)?, memidx : memidx, memarg : memarg)
  | VLOAD(vectype : vectype, vloadop_(vectype)?, memidx : memidx, memarg : memarg)
  | VLOAD_LANE(vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx)
  | VSTORE(vectype : vectype, memidx : memidx, memarg : memarg)
  | VSTORE_LANE(vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx)
  | `MEMORY.SIZE`(memidx : memidx)
  | `MEMORY.GROW`(memidx : memidx)
  | `MEMORY.FILL`(memidx : memidx)
  | `MEMORY.COPY`(memidx : memidx, memidx : memidx)
  | `MEMORY.INIT`(memidx : memidx, dataidx : dataidx)
  | `DATA.DROP`(dataidx : dataidx)
  | `REF.NULL`(heaptype : heaptype)
  | `REF.IS_NULL`
  | `REF.AS_NON_NULL`
  | `REF.EQ`
  | `REF.TEST`(reftype : reftype)
  | `REF.CAST`(reftype : reftype)
  | `REF.FUNC`(funcidx : funcidx)
  | `REF.I31`
  | `I31.GET`(sx : sx)
  | `STRUCT.NEW`(typeidx : typeidx)
  | `STRUCT.NEW_DEFAULT`(typeidx : typeidx)
  | `STRUCT.GET`(`sx?` : sx?, typeidx : typeidx, fieldidx : fieldidx)
  | `STRUCT.SET`(typeidx : typeidx, fieldidx : fieldidx)
  | `ARRAY.NEW`(typeidx : typeidx)
  | `ARRAY.NEW_DEFAULT`(typeidx : typeidx)
  | `ARRAY.NEW_FIXED`(typeidx : typeidx, u32 : u32)
  | `ARRAY.NEW_DATA`(typeidx : typeidx, dataidx : dataidx)
  | `ARRAY.NEW_ELEM`(typeidx : typeidx, elemidx : elemidx)
  | `ARRAY.GET`(`sx?` : sx?, typeidx : typeidx)
  | `ARRAY.SET`(typeidx : typeidx)
  | `ARRAY.LEN`
  | `ARRAY.FILL`(typeidx : typeidx)
  | `ARRAY.COPY`(typeidx : typeidx, typeidx : typeidx)
  | `ARRAY.INIT_DATA`(typeidx : typeidx, dataidx : dataidx)
  | `ARRAY.INIT_ELEM`(typeidx : typeidx, elemidx : elemidx)
  | `EXTERN.CONVERT_ANY`
  | `ANY.CONVERT_EXTERN`
  | CONST(numtype : numtype, num_(numtype))
  | UNOP(numtype : numtype, unop_(numtype))
  | BINOP(numtype : numtype, binop_(numtype))
  | TESTOP(numtype : numtype, testop_(numtype))
  | RELOP(numtype : numtype, relop_(numtype))
  | CVTOP(numtype_1 : numtype, numtype_2 : numtype, cvtop__(numtype_2, numtype_1))
  | VCONST(vectype : vectype, vec_(vectype))
  | VVUNOP(vectype : vectype, vvunop : vvunop)
  | VVBINOP(vectype : vectype, vvbinop : vvbinop)
  | VVTERNOP(vectype : vectype, vvternop : vvternop)
  | VVTESTOP(vectype : vectype, vvtestop : vvtestop)
  | VUNOP(shape : shape, vunop_(shape))
  | VBINOP(shape : shape, vbinop_(shape))
  | VTERNOP(shape : shape, vternop_(shape))
  | VTESTOP(shape : shape, vtestop_(shape))
  | VRELOP(shape : shape, vrelop_(shape))
  | VSHIFTOP(ishape : ishape, vshiftop_(ishape))
  | VBITMASK(ishape : ishape)
  | VSWIZZLOP(bshape : bshape, vswizzlop_(bshape))
  | VSHUFFLE(bshape : bshape, `laneidx*` : laneidx*)
    -- if (`%`_dim(|laneidx*{laneidx <- `laneidx*`}|) = $dim(bshape!`%`_bshape.0))
  | VEXTUNOP(ishape_1 : ishape, ishape_2 : ishape, vextunop__(ishape_2, ishape_1))
  | VEXTBINOP(ishape_1 : ishape, ishape_2 : ishape, vextbinop__(ishape_2, ishape_1))
  | VEXTTERNOP(ishape_1 : ishape, ishape_2 : ishape, vextternop__(ishape_2, ishape_1))
  | VNARROW(ishape_1 : ishape, ishape_2 : ishape, sx : sx)
    -- if (($lsize($lanetype(ishape_2!`%`_ishape.0)) = (2 * $lsize($lanetype(ishape_1!`%`_ishape.0)))) /\ ((2 * $lsize($lanetype(ishape_1!`%`_ishape.0))) <= 32))
  | VCVTOP(shape_1 : shape, shape_2 : shape, vcvtop__(shape_2, shape_1))
  | VSPLAT(shape : shape)
  | VEXTRACT_LANE(shape : shape, `sx?` : sx?, laneidx : laneidx)
    -- if ((sx?{sx <- `sx?`} = ?()) <=> ($lanetype(shape) <- [I32_lanetype I64_lanetype F32_lanetype F64_lanetype]))
  | VREPLACE_LANE(shape : shape, laneidx : laneidx)
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)
  | `LABEL_%{%}%`(n : n, `instr*` : instr*, `instr*` : instr*)
  | `FRAME_%{%}%`(n : n, frame : frame, `instr*` : instr*)
  | `HANDLER_%{%}%`(n : n, `catch*` : catch*, `instr*` : instr*)
  | TRAP
}

;; test.spectec:1314.1-1315.9
syntax expr = instr*

;; test.spectec:1326.1-1326.35
def $memarg0 : memarg
  ;; test.spectec:1327.1-1327.35
  def $memarg0 = {ALIGN `%`_u32(0), OFFSET `%`_u64(0)}

;; test.spectec:1329.1-1329.69
def $const(consttype : consttype, lit_ : lit_((consttype : consttype <: storagetype))) : instr
  ;; test.spectec:1330.1-1330.43
  def $const{numtype : numtype, c : lit_(((numtype : numtype <: consttype) : consttype <: storagetype))}((numtype : numtype <: consttype), c) = CONST_instr(numtype, c)
  ;; test.spectec:1331.1-1331.44
  def $const{vectype : vectype, c : lit_(((vectype : vectype <: consttype) : consttype <: storagetype))}((vectype : vectype <: consttype), c) = VCONST_instr(vectype, c)

;; test.spectec:1336.1-1336.30
def $free_shape(shape : shape) : free
  ;; test.spectec:1345.1-1345.59
  def $free_shape{lanetype : lanetype, dim : dim}(`%X%`_shape(lanetype, dim)) = $free_lanetype(lanetype)

;; test.spectec:1337.1-1337.38
def $free_blocktype(blocktype : blocktype) : free
  ;; test.spectec:1347.1-1347.75
  def $free_blocktype{`valtype?` : valtype?}(_RESULT_blocktype(valtype?{valtype <- `valtype?`})) = $free_opt($free_valtype(valtype)?{valtype <- `valtype?`})
  ;; test.spectec:1348.1-1348.59
  def $free_blocktype{typeidx : typeidx}(_IDX_blocktype(typeidx)) = $free_typeidx(typeidx)

;; test.spectec:1338.1-1338.30
def $free_catch(catch : catch) : free
  ;; test.spectec:1350.1-1350.90
  def $free_catch{tagidx : tagidx, labelidx : labelidx}(CATCH_catch(tagidx, labelidx)) = $free_tagidx(tagidx) +++ $free_labelidx(labelidx)
  ;; test.spectec:1351.1-1351.94
  def $free_catch{tagidx : tagidx, labelidx : labelidx}(CATCH_REF_catch(tagidx, labelidx)) = $free_tagidx(tagidx) +++ $free_labelidx(labelidx)
  ;; test.spectec:1352.1-1352.63
  def $free_catch{labelidx : labelidx}(CATCH_ALL_catch(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1353.1-1353.67
  def $free_catch{labelidx : labelidx}(CATCH_ALL_REF_catch(labelidx)) = $free_labelidx(labelidx)

;; test.spectec:1504.1-1504.44
rec {

;; test.spectec:1504.1-1504.44
def $shift_labelidxs(labelidx*) : labelidx*
  ;; test.spectec:1505.1-1505.32
  def $shift_labelidxs([]) = []
  ;; test.spectec:1506.1-1506.66
  def $shift_labelidxs{`labelidx'*` : labelidx*}([`%`_labelidx(0)] ++ labelidx'*{labelidx' <- `labelidx'*`}) = $shift_labelidxs(labelidx'*{labelidx' <- `labelidx'*`})
  ;; test.spectec:1507.1-1507.91
  def $shift_labelidxs{labelidx : labelidx, `labelidx'*` : labelidx*}([labelidx] ++ labelidx'*{labelidx' <- `labelidx'*`}) = [`%`_labelidx((((labelidx!`%`_labelidx.0 : nat <:> int) - (1 : nat <:> int)) : int <:> nat))] ++ $shift_labelidxs(labelidx'*{labelidx' <- `labelidx'*`})
}

;; test.spectec:1340.1-1341.31
rec {

;; test.spectec:1340.1-1340.30
def $free_instr(instr : instr) : free
  ;; test.spectec:1355.1-1355.26
  def $free_instr(NOP_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1356.1-1356.34
  def $free_instr(UNREACHABLE_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1357.1-1357.27
  def $free_instr(DROP_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1358.1-1358.86
  def $free_instr{`valtype*?` : valtype*?}(SELECT_instr(valtype*{valtype <- `valtype*`}?{`valtype*` <- `valtype*?`})) = $free_opt($free_list($free_valtype(valtype)*{valtype <- `valtype*`})?{`valtype*` <- `valtype*?`})
  ;; test.spectec:1360.1-1360.92
  def $free_instr{blocktype : blocktype, `instr*` : instr*}(BLOCK_instr(blocktype, instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_block(instr*{instr <- `instr*`})
  ;; test.spectec:1361.1-1361.91
  def $free_instr{blocktype : blocktype, `instr*` : instr*}(LOOP_instr(blocktype, instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_block(instr*{instr <- `instr*`})
  ;; test.spectec:1362.1-1363.79
  def $free_instr{blocktype : blocktype, `instr_1*` : instr*, `instr_2*` : instr*}(`IF%%ELSE%`_instr(blocktype, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`})) = $free_blocktype(blocktype) +++ $free_block(instr_1*{instr_1 <- `instr_1*`}) +++ $free_block(instr_2*{instr_2 <- `instr_2*`})
  ;; test.spectec:1365.1-1365.56
  def $free_instr{labelidx : labelidx}(BR_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1366.1-1366.59
  def $free_instr{labelidx : labelidx}(BR_IF_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1367.1-1368.69
  def $free_instr{`labelidx*` : labelidx*, labelidx' : labelidx}(BR_TABLE_instr(labelidx*{labelidx <- `labelidx*`}, labelidx')) = $free_list($free_labelidx(labelidx)*{labelidx <- `labelidx*`}) +++ $free_labelidx(labelidx')
  ;; test.spectec:1369.1-1369.64
  def $free_instr{labelidx : labelidx}(BR_ON_NULL_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1370.1-1370.68
  def $free_instr{labelidx : labelidx}(BR_ON_NON_NULL_instr(labelidx)) = $free_labelidx(labelidx)
  ;; test.spectec:1371.1-1372.83
  def $free_instr{labelidx : labelidx, reftype_1 : reftype, reftype_2 : reftype}(BR_ON_CAST_instr(labelidx, reftype_1, reftype_2)) = $free_labelidx(labelidx) +++ $free_reftype(reftype_1) +++ $free_reftype(reftype_2)
  ;; test.spectec:1373.1-1374.83
  def $free_instr{labelidx : labelidx, reftype_1 : reftype, reftype_2 : reftype}(BR_ON_CAST_FAIL_instr(labelidx, reftype_1, reftype_2)) = $free_labelidx(labelidx) +++ $free_reftype(reftype_1) +++ $free_reftype(reftype_2)
  ;; test.spectec:1376.1-1376.55
  def $free_instr{funcidx : funcidx}(CALL_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1377.1-1377.59
  def $free_instr{typeuse : typeuse}(CALL_REF_instr(typeuse)) = $free_typeuse(typeuse)
  ;; test.spectec:1378.1-1379.53
  def $free_instr{tableidx : tableidx, typeuse : typeuse}(CALL_INDIRECT_instr(tableidx, typeuse)) = $free_tableidx(tableidx) +++ $free_typeuse(typeuse)
  ;; test.spectec:1380.1-1380.29
  def $free_instr(RETURN_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1381.1-1381.62
  def $free_instr{funcidx : funcidx}(RETURN_CALL_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1382.1-1382.66
  def $free_instr{typeuse : typeuse}(RETURN_CALL_REF_instr(typeuse)) = $free_typeuse(typeuse)
  ;; test.spectec:1383.1-1384.53
  def $free_instr{tableidx : tableidx, typeuse : typeuse}(RETURN_CALL_INDIRECT_instr(tableidx, typeuse)) = $free_tableidx(tableidx) +++ $free_typeuse(typeuse)
  ;; test.spectec:1386.1-1386.53
  def $free_instr{tagidx : tagidx}(THROW_instr(tagidx)) = $free_tagidx(tagidx)
  ;; test.spectec:1387.1-1387.32
  def $free_instr(THROW_REF_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1388.1-1389.99
  def $free_instr{blocktype : blocktype, `catch*` : catch*, `instr*` : instr*}(TRY_TABLE_instr(blocktype, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`})) = $free_blocktype(blocktype) +++ $free_list($free_catch(catch)*{catch <- `catch*`}) +++ $free_list($free_instr(instr)*{instr <- `instr*`})
  ;; test.spectec:1391.1-1391.63
  def $free_instr{numtype : numtype, numlit : num_(numtype)}(CONST_instr(numtype, numlit)) = $free_numtype(numtype)
  ;; test.spectec:1392.1-1392.60
  def $free_instr{numtype : numtype, unop : unop_(numtype)}(UNOP_instr(numtype, unop)) = $free_numtype(numtype)
  ;; test.spectec:1393.1-1393.62
  def $free_instr{numtype : numtype, binop : binop_(numtype)}(BINOP_instr(numtype, binop)) = $free_numtype(numtype)
  ;; test.spectec:1394.1-1394.64
  def $free_instr{numtype : numtype, testop : testop_(numtype)}(TESTOP_instr(numtype, testop)) = $free_numtype(numtype)
  ;; test.spectec:1395.1-1395.62
  def $free_instr{numtype : numtype, relop : relop_(numtype)}(RELOP_instr(numtype, relop)) = $free_numtype(numtype)
  ;; test.spectec:1396.1-1397.55
  def $free_instr{numtype_1 : numtype, numtype_2 : numtype, cvtop : cvtop__(numtype_2, numtype_1)}(CVTOP_instr(numtype_1, numtype_2, cvtop)) = $free_numtype(numtype_1) +++ $free_numtype(numtype_2)
  ;; test.spectec:1399.1-1399.64
  def $free_instr{vectype : vectype, veclit : vec_(vectype)}(VCONST_instr(vectype, veclit)) = $free_vectype(vectype)
  ;; test.spectec:1400.1-1400.64
  def $free_instr{vectype : vectype, vvunop : vvunop}(VVUNOP_instr(vectype, vvunop)) = $free_vectype(vectype)
  ;; test.spectec:1401.1-1401.66
  def $free_instr{vectype : vectype, vvbinop : vvbinop}(VVBINOP_instr(vectype, vvbinop)) = $free_vectype(vectype)
  ;; test.spectec:1402.1-1402.68
  def $free_instr{vectype : vectype, vvternop : vvternop}(VVTERNOP_instr(vectype, vvternop)) = $free_vectype(vectype)
  ;; test.spectec:1403.1-1403.68
  def $free_instr{vectype : vectype, vvtestop : vvtestop}(VVTESTOP_instr(vectype, vvtestop)) = $free_vectype(vectype)
  ;; test.spectec:1404.1-1404.56
  def $free_instr{shape : shape, vunop : vunop_(shape)}(VUNOP_instr(shape, vunop)) = $free_shape(shape)
  ;; test.spectec:1405.1-1405.58
  def $free_instr{shape : shape, vbinop : vbinop_(shape)}(VBINOP_instr(shape, vbinop)) = $free_shape(shape)
  ;; test.spectec:1406.1-1406.60
  def $free_instr{shape : shape, vternop : vternop_(shape)}(VTERNOP_instr(shape, vternop)) = $free_shape(shape)
  ;; test.spectec:1407.1-1407.60
  def $free_instr{shape : shape, vtestop : vtestop_(shape)}(VTESTOP_instr(shape, vtestop)) = $free_shape(shape)
  ;; test.spectec:1408.1-1408.58
  def $free_instr{shape : shape, vrelop : vrelop_(shape)}(VRELOP_instr(shape, vrelop)) = $free_shape(shape)
  ;; test.spectec:1409.1-1409.64
  def $free_instr{ishape : ishape, vshiftop : vshiftop_(ishape)}(VSHIFTOP_instr(ishape, vshiftop)) = $free_shape(ishape!`%`_ishape.0)
  ;; test.spectec:1410.1-1410.55
  def $free_instr{ishape : ishape}(VBITMASK_instr(ishape)) = $free_shape(ishape!`%`_ishape.0)
  ;; test.spectec:1411.1-1411.66
  def $free_instr{bshape : bshape, vswizzlop : vswizzlop_(bshape)}(VSWIZZLOP_instr(bshape, vswizzlop)) = $free_shape(bshape!`%`_bshape.0)
  ;; test.spectec:1412.1-1412.64
  def $free_instr{bshape : bshape, `laneidx*` : laneidx*}(VSHUFFLE_instr(bshape, laneidx*{laneidx <- `laneidx*`})) = $free_shape(bshape!`%`_bshape.0)
  ;; test.spectec:1413.1-1414.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, vextunop : vextunop__(ishape_2, ishape_1)}(VEXTUNOP_instr(ishape_1, ishape_2, vextunop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1415.1-1416.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, vextbinop : vextbinop__(ishape_2, ishape_1)}(VEXTBINOP_instr(ishape_1, ishape_2, vextbinop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1417.1-1418.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, vextternop : vextternop__(ishape_2, ishape_1)}(VEXTTERNOP_instr(ishape_1, ishape_2, vextternop)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1419.1-1420.49
  def $free_instr{ishape_1 : ishape, ishape_2 : ishape, sx : sx}(VNARROW_instr(ishape_1, ishape_2, sx)) = $free_shape(ishape_1!`%`_ishape.0) +++ $free_shape(ishape_2!`%`_ishape.0)
  ;; test.spectec:1421.1-1422.47
  def $free_instr{shape_1 : shape, shape_2 : shape, vcvtop : vcvtop__(shape_2, shape_1)}(VCVTOP_instr(shape_1, shape_2, vcvtop)) = $free_shape(shape_1) +++ $free_shape(shape_2)
  ;; test.spectec:1423.1-1423.51
  def $free_instr{shape : shape}(VSPLAT_instr(shape)) = $free_shape(shape)
  ;; test.spectec:1424.1-1424.70
  def $free_instr{shape : shape, `sx?` : sx?, laneidx : laneidx}(VEXTRACT_LANE_instr(shape, sx?{sx <- `sx?`}, laneidx)) = $free_shape(shape)
  ;; test.spectec:1425.1-1425.66
  def $free_instr{shape : shape, laneidx : laneidx}(VREPLACE_LANE_instr(shape, laneidx)) = $free_shape(shape)
  ;; test.spectec:1427.1-1427.62
  def $free_instr{heaptype : heaptype}(`REF.NULL`_instr(heaptype)) = $free_heaptype(heaptype)
  ;; test.spectec:1428.1-1428.34
  def $free_instr(`REF.IS_NULL`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1429.1-1429.38
  def $free_instr(`REF.AS_NON_NULL`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1430.1-1430.29
  def $free_instr(`REF.EQ`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1431.1-1431.59
  def $free_instr{reftype : reftype}(`REF.TEST`_instr(reftype)) = $free_reftype(reftype)
  ;; test.spectec:1432.1-1432.59
  def $free_instr{reftype : reftype}(`REF.CAST`_instr(reftype)) = $free_reftype(reftype)
  ;; test.spectec:1433.1-1433.59
  def $free_instr{funcidx : funcidx}(`REF.FUNC`_instr(funcidx)) = $free_funcidx(funcidx)
  ;; test.spectec:1434.1-1434.30
  def $free_instr(`REF.I31`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1436.1-1436.33
  def $free_instr{sx : sx}(`I31.GET`_instr(sx)) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1438.1-1438.61
  def $free_instr{typeidx : typeidx}(`STRUCT.NEW`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1439.1-1439.69
  def $free_instr{typeidx : typeidx}(`STRUCT.NEW_DEFAULT`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1440.1-1440.69
  def $free_instr{`sx?` : sx?, typeidx : typeidx, u32 : u32}(`STRUCT.GET`_instr(sx?{sx <- `sx?`}, typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1441.1-1441.65
  def $free_instr{typeidx : typeidx, u32 : u32}(`STRUCT.SET`_instr(typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1443.1-1443.60
  def $free_instr{typeidx : typeidx}(`ARRAY.NEW`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1444.1-1444.68
  def $free_instr{typeidx : typeidx}(`ARRAY.NEW_DEFAULT`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1445.1-1445.70
  def $free_instr{typeidx : typeidx, u32 : u32}(`ARRAY.NEW_FIXED`_instr(typeidx, u32)) = $free_typeidx(typeidx)
  ;; test.spectec:1446.1-1447.51
  def $free_instr{typeidx : typeidx, dataidx : dataidx}(`ARRAY.NEW_DATA`_instr(typeidx, dataidx)) = $free_typeidx(typeidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1448.1-1449.51
  def $free_instr{typeidx : typeidx, elemidx : elemidx}(`ARRAY.NEW_ELEM`_instr(typeidx, elemidx)) = $free_typeidx(typeidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1450.1-1450.64
  def $free_instr{`sx?` : sx?, typeidx : typeidx}(`ARRAY.GET`_instr(sx?{sx <- `sx?`}, typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1451.1-1451.60
  def $free_instr{typeidx : typeidx}(`ARRAY.SET`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1452.1-1452.32
  def $free_instr(`ARRAY.LEN`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1453.1-1453.61
  def $free_instr{typeidx : typeidx}(`ARRAY.FILL`_instr(typeidx)) = $free_typeidx(typeidx)
  ;; test.spectec:1454.1-1455.55
  def $free_instr{typeidx_1 : typeidx, typeidx_2 : typeidx}(`ARRAY.COPY`_instr(typeidx_1, typeidx_2)) = $free_typeidx(typeidx_1) +++ $free_typeidx(typeidx_2)
  ;; test.spectec:1456.1-1457.51
  def $free_instr{typeidx : typeidx, dataidx : dataidx}(`ARRAY.INIT_DATA`_instr(typeidx, dataidx)) = $free_typeidx(typeidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1458.1-1459.51
  def $free_instr{typeidx : typeidx, elemidx : elemidx}(`ARRAY.INIT_ELEM`_instr(typeidx, elemidx)) = $free_typeidx(typeidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1461.1-1461.41
  def $free_instr(`EXTERN.CONVERT_ANY`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1462.1-1462.41
  def $free_instr(`ANY.CONVERT_EXTERN`_instr) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1464.1-1464.63
  def $free_instr{localidx : localidx}(`LOCAL.GET`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1465.1-1465.63
  def $free_instr{localidx : localidx}(`LOCAL.SET`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1466.1-1466.63
  def $free_instr{localidx : localidx}(`LOCAL.TEE`_instr(localidx)) = $free_localidx(localidx)
  ;; test.spectec:1468.1-1468.67
  def $free_instr{globalidx : globalidx}(`GLOBAL.GET`_instr(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:1469.1-1469.67
  def $free_instr{globalidx : globalidx}(`GLOBAL.SET`_instr(globalidx)) = $free_globalidx(globalidx)
  ;; test.spectec:1471.1-1471.63
  def $free_instr{tableidx : tableidx}(`TABLE.GET`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1472.1-1472.63
  def $free_instr{tableidx : tableidx}(`TABLE.SET`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1473.1-1473.64
  def $free_instr{tableidx : tableidx}(`TABLE.SIZE`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1474.1-1474.64
  def $free_instr{tableidx : tableidx}(`TABLE.GROW`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1475.1-1475.64
  def $free_instr{tableidx : tableidx}(`TABLE.FILL`_instr(tableidx)) = $free_tableidx(tableidx)
  ;; test.spectec:1476.1-1477.59
  def $free_instr{tableidx_1 : tableidx, tableidx_2 : tableidx}(`TABLE.COPY`_instr(tableidx_1, tableidx_2)) = $free_tableidx(tableidx_1) +++ $free_tableidx(tableidx_2)
  ;; test.spectec:1478.1-1479.53
  def $free_instr{tableidx : tableidx, elemidx : elemidx}(`TABLE.INIT`_instr(tableidx, elemidx)) = $free_tableidx(tableidx) +++ $free_elemidx(elemidx)
  ;; test.spectec:1480.1-1480.60
  def $free_instr{elemidx : elemidx}(`ELEM.DROP`_instr(elemidx)) = $free_elemidx(elemidx)
  ;; test.spectec:1482.1-1483.49
  def $free_instr{numtype : numtype, `loadop?` : loadop_(numtype)?, memidx : memidx, memarg : memarg}(LOAD_instr(numtype, loadop?{loadop <- `loadop?`}, memidx, memarg)) = $free_numtype(numtype) +++ $free_memidx(memidx)
  ;; test.spectec:1484.1-1485.49
  def $free_instr{numtype : numtype, `storeop?` : storeop_(numtype)?, memidx : memidx, memarg : memarg}(STORE_instr(numtype, storeop?{storeop <- `storeop?`}, memidx, memarg)) = $free_numtype(numtype) +++ $free_memidx(memidx)
  ;; test.spectec:1486.1-1487.49
  def $free_instr{vectype : vectype, `vloadop?` : vloadop_(vectype)?, memidx : memidx, memarg : memarg}(VLOAD_instr(vectype, vloadop?{vloadop <- `vloadop?`}, memidx, memarg)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1488.1-1489.49
  def $free_instr{vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx}(VLOAD_LANE_instr(vectype, sz, memidx, memarg, laneidx)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1490.1-1491.49
  def $free_instr{vectype : vectype, memidx : memidx, memarg : memarg}(VSTORE_instr(vectype, memidx, memarg)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1492.1-1493.49
  def $free_instr{vectype : vectype, sz : sz, memidx : memidx, memarg : memarg, laneidx : laneidx}(VSTORE_LANE_instr(vectype, sz, memidx, memarg, laneidx)) = $free_vectype(vectype) +++ $free_memidx(memidx)
  ;; test.spectec:1494.1-1494.59
  def $free_instr{memidx : memidx}(`MEMORY.SIZE`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1495.1-1495.59
  def $free_instr{memidx : memidx}(`MEMORY.GROW`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1496.1-1496.59
  def $free_instr{memidx : memidx}(`MEMORY.FILL`_instr(memidx)) = $free_memidx(memidx)
  ;; test.spectec:1497.1-1498.51
  def $free_instr{memidx_1 : memidx, memidx_2 : memidx}(`MEMORY.COPY`_instr(memidx_1, memidx_2)) = $free_memidx(memidx_1) +++ $free_memidx(memidx_2)
  ;; test.spectec:1499.1-1500.49
  def $free_instr{memidx : memidx, dataidx : dataidx}(`MEMORY.INIT`_instr(memidx, dataidx)) = $free_memidx(memidx) +++ $free_dataidx(dataidx)
  ;; test.spectec:1501.1-1501.60
  def $free_instr{dataidx : dataidx}(`DATA.DROP`_instr(dataidx)) = $free_dataidx(dataidx)

;; test.spectec:1341.1-1341.31
def $free_block(instr*) : free
  ;; test.spectec:1509.1-1510.47
  def $free_block{`instr*` : instr*}(instr*{instr <- `instr*`}) = free[LABELS_free = $shift_labelidxs(free.LABELS_free)]
    -- let{free : free} free = $free_list($free_instr(instr)*{instr <- `instr*`})
}

;; test.spectec:1342.1-1342.28
def $free_expr(expr : expr) : free
  ;; test.spectec:1513.1-1513.57
  def $free_expr{`instr*` : instr*}(instr*{instr <- `instr*`}) = $free_list($free_instr(instr)*{instr <- `instr*`})

;; test.spectec:1526.1-1527.43
syntax elemmode = 
  | ACTIVE(tableidx : tableidx, expr : expr)
  | PASSIVE
  | DECLARE

;; test.spectec:1528.1-1529.31
syntax datamode = 
  | ACTIVE(memidx : memidx, expr : expr)
  | PASSIVE

;; test.spectec:1531.1-1532.15
syntax type = 
  | TYPE(rectype : rectype)

;; test.spectec:1534.1-1535.14
syntax tag = 
  | TAG(tagtype : tagtype)

;; test.spectec:1537.1-1538.25
syntax global = 
  | GLOBAL(globaltype : globaltype, expr : expr)

;; test.spectec:1540.1-1541.17
syntax mem = 
  | MEMORY(memtype : memtype)

;; test.spectec:1543.1-1544.23
syntax table = 
  | TABLE(tabletype : tabletype, expr : expr)

;; test.spectec:1546.1-1547.22
syntax data = 
  | DATA(`byte*` : byte*, datamode : datamode)

;; test.spectec:1549.1-1550.16
syntax local = 
  | LOCAL(valtype : valtype)

;; test.spectec:1552.1-1553.27
syntax func = 
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)

;; test.spectec:1555.1-1556.30
syntax elem = 
  | ELEM(reftype : reftype, `expr*` : expr*, elemmode : elemmode)

;; test.spectec:1558.1-1559.16
syntax start = 
  | START(funcidx : funcidx)

;; test.spectec:1561.1-1562.30
syntax import = 
  | IMPORT(name : name, name : name, externtype : externtype)

;; test.spectec:1564.1-1565.24
syntax export = 
  | EXPORT(name : name, externidx : externidx)

;; test.spectec:1567.1-1579.17
syntax module = 
  | MODULE(list(syntax type), list(syntax import), list(syntax tag), list(syntax global), list(syntax mem), list(syntax table), list(syntax func), list(syntax data), list(syntax elem), `start?` : start?, list(syntax export))

;; test.spectec:1594.1-1594.28
def $free_type(type : type) : free
  ;; test.spectec:1611.1-1611.54
  def $free_type{rectype : rectype}(TYPE_type(rectype)) = $free_rectype(rectype)

;; test.spectec:1595.1-1595.26
def $free_tag(tag : tag) : free
  ;; test.spectec:1613.1-1613.52
  def $free_tag{tagtype : tagtype}(TAG_tag(tagtype)) = $free_tagtype(tagtype)

;; test.spectec:1596.1-1596.32
def $free_global(global : global) : free
  ;; test.spectec:1615.1-1616.51
  def $free_global{globaltype : globaltype, expr : expr}(GLOBAL_global(globaltype, expr)) = $free_globaltype(globaltype) +++ $free_expr(expr)

;; test.spectec:1597.1-1597.26
def $free_mem(mem : mem) : free
  ;; test.spectec:1618.1-1618.55
  def $free_mem{memtype : memtype}(MEMORY_mem(memtype)) = $free_memtype(memtype)

;; test.spectec:1598.1-1598.30
def $free_table(table : table) : free
  ;; test.spectec:1620.1-1621.49
  def $free_table{tabletype : tabletype, expr : expr}(TABLE_table(tabletype, expr)) = $free_tabletype(tabletype) +++ $free_expr(expr)

;; test.spectec:1599.1-1599.30
def $free_local(local : local) : free
  ;; test.spectec:1623.1-1623.44
  def $free_local{t : valtype}(LOCAL_local(t)) = $free_valtype(t)

;; test.spectec:1600.1-1600.28
def $free_func(func : func) : free
  ;; test.spectec:1625.1-1627.35
  def $free_func{typeidx : typeidx, `local*` : local*, expr : expr}(FUNC_func(typeidx, local*{local <- `local*`}, expr)) = $free_typeidx(typeidx) +++ $free_list($free_local(local)*{local <- `local*`}) +++ $free_block(expr)[LOCALS_free = []]

;; test.spectec:1603.1-1603.36
def $free_datamode(datamode : datamode) : free
  ;; test.spectec:1639.1-1639.82
  def $free_datamode{memidx : memidx, expr : expr}(ACTIVE_datamode(memidx, expr)) = $free_memidx(memidx) +++ $free_expr(expr)
  ;; test.spectec:1640.1-1640.33
  def $free_datamode(PASSIVE_datamode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:1601.1-1601.28
def $free_data(data : data) : free
  ;; test.spectec:1629.1-1629.63
  def $free_data{`byte*` : byte*, datamode : datamode}(DATA_data(byte*{byte <- `byte*`}, datamode)) = $free_datamode(datamode)

;; test.spectec:1604.1-1604.36
def $free_elemmode(elemmode : elemmode) : free
  ;; test.spectec:1635.1-1635.88
  def $free_elemmode{tableidx : tableidx, expr : expr}(ACTIVE_elemmode(tableidx, expr)) = $free_tableidx(tableidx) +++ $free_expr(expr)
  ;; test.spectec:1636.1-1636.33
  def $free_elemmode(PASSIVE_elemmode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}
  ;; test.spectec:1637.1-1637.33
  def $free_elemmode(DECLARE_elemmode) = {TYPES [], FUNCS [], GLOBALS [], TABLES [], MEMS [], ELEMS [], DATAS [], LOCALS [], LABELS [], TAGS []}

;; test.spectec:1602.1-1602.28
def $free_elem(elem : elem) : free
  ;; test.spectec:1631.1-1633.27
  def $free_elem{reftype : reftype, `expr*` : expr*, elemmode : elemmode}(ELEM_elem(reftype, expr*{expr <- `expr*`}, elemmode)) = $free_reftype(reftype) +++ $free_list($free_expr(expr)*{expr <- `expr*`}) +++ $free_elemmode(elemmode)

;; test.spectec:1605.1-1605.30
def $free_start(start : start) : free
  ;; test.spectec:1642.1-1642.56
  def $free_start{funcidx : funcidx}(START_start(funcidx)) = $free_funcidx(funcidx)

;; test.spectec:1606.1-1606.32
def $free_import(import : import) : free
  ;; test.spectec:1644.1-1644.81
  def $free_import{name_1 : name, name_2 : name, externtype : externtype}(IMPORT_import(name_1, name_2, externtype)) = $free_externtype(externtype)

;; test.spectec:1607.1-1607.32
def $free_export(export : export) : free
  ;; test.spectec:1646.1-1646.69
  def $free_export{name : name, externidx : externidx}(EXPORT_export(name, externidx)) = $free_externidx(externidx)

;; test.spectec:1608.1-1608.32
def $free_module(module : module) : free
  ;; test.spectec:1648.1-1659.36
  def $free_module{`type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*}(MODULE_module(`%`_list(type*{type <- `type*`}), `%`_list(import*{import <- `import*`}), `%`_list(tag*{tag <- `tag*`}), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list(func*{func <- `func*`}), `%`_list(data*{data <- `data*`}), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`}))) = $free_list($free_type(type)*{type <- `type*`}) +++ $free_list($free_tag(tag)*{tag <- `tag*`}) +++ $free_list($free_global(global)*{global <- `global*`}) +++ $free_list($free_mem(mem)*{mem <- `mem*`}) +++ $free_list($free_table(table)*{table <- `table*`}) +++ $free_list($free_func(func)*{func <- `func*`}) +++ $free_list($free_data(data)*{data <- `data*`}) +++ $free_list($free_elem(elem)*{elem <- `elem*`}) +++ $free_opt($free_start(start)?{start <- `start?`}) +++ $free_list($free_import(import)*{import <- `import*`}) +++ $free_list($free_export(export)*{export <- `export*`})

;; test.spectec:1662.1-1662.89
def $funcidx_module(module : module) : funcidx*
  ;; test.spectec:1663.1-1663.57
  def $funcidx_module{module : module}(module) = $free_module(module).FUNCS_free

;; test.spectec:1665.1-1665.87
def $dataidx_funcs(func*) : dataidx*
  ;; test.spectec:1666.1-1666.64
  def $dataidx_funcs{`func*` : func*}(func*{func <- `func*`}) = $free_list($free_func(func)*{func <- `func*`}).DATAS_free

;; test.spectec:1682.1-1683.16
syntax init = 
  | SET
  | UNSET

;; test.spectec:1685.1-1686.15
syntax localtype = 
  | `%%`(init : init, valtype : valtype)

;; test.spectec:1688.1-1689.57
syntax instrtype = 
  | `%->_%%`(resulttype : resulttype, `localidx*` : localidx*, resulttype : resulttype)

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

;; test.spectec:1723.1-1723.158
rec {

;; test.spectec:1723.1-1723.158
def $with_locals(context : context, localidx*, localtype*) : context
  ;; test.spectec:1725.1-1725.34
  def $with_locals{C : context}(C, [], []) = C
  ;; test.spectec:1726.1-1726.90
  def $with_locals{C : context, x_1 : idx, `x*` : idx*, lct_1 : localtype, `lct*` : localtype*}(C, [x_1] ++ x*{x <- `x*`}, [lct_1] ++ lct*{lct <- `lct*`}) = $with_locals(C[LOCALS_context[x_1!`%`_idx.0] = lct_1], x*{x <- `x*`}, lct*{lct <- `lct*`})
}

;; test.spectec:1736.1-1736.94
rec {

;; test.spectec:1736.1-1736.94
def $clos_deftypes(deftype*) : deftype*
  ;; test.spectec:1745.1-1745.30
  def $clos_deftypes([]) = []
  ;; test.spectec:1746.1-1746.101
  def $clos_deftypes{`dt*` : deftype*, dt_n : deftype}(dt*{dt <- `dt*`} ++ [dt_n]) = dt'*{dt' <- `dt'*`} ++ [$subst_all_deftype(dt_n, (dt' : deftype <: typeuse)*{dt' <- `dt'*`})]
    -- let{`dt'*` : deftype*} dt'*{dt' <- `dt'*`} = $clos_deftypes(dt*{dt <- `dt*`})
}

;; test.spectec:1731.1-1731.93
def $clos_valtype(context : context, valtype : valtype) : valtype
  ;; test.spectec:1739.1-1739.89
  def $clos_valtype{C : context, t : valtype}(C, t) = $subst_all_valtype(t, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- let{`dt*` : deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1732.1-1732.93
def $clos_deftype(context : context, deftype : deftype) : deftype
  ;; test.spectec:1740.1-1740.93
  def $clos_deftype{C : context, dt : deftype}(C, dt) = $subst_all_deftype(dt, (dt' : deftype <: typeuse)*{dt' <- `dt'*`})
    -- let{`dt'*` : deftype*} dt'*{dt' <- `dt'*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1733.1-1733.93
def $clos_tagtype(context : context, tagtype : tagtype) : tagtype
  ;; test.spectec:1741.1-1741.91
  def $clos_tagtype{C : context, jt : tagtype}(C, jt) = $subst_all_tagtype(jt, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- let{`dt*` : deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1734.1-1734.102
def $clos_externtype(context : context, externtype : externtype) : externtype
  ;; test.spectec:1742.1-1742.97
  def $clos_externtype{C : context, xt : externtype}(C, xt) = $subst_all_externtype(xt, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- let{`dt*` : deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1735.1-1735.102
def $clos_moduletype(context : context, moduletype : moduletype) : moduletype
  ;; test.spectec:1743.1-1743.99
  def $clos_moduletype{C : context, mmt : moduletype}(C, mmt) = $subst_all_moduletype(mmt, (dt : deftype <: typeuse)*{dt <- `dt*`})
    -- let{`dt*` : deftype*} dt*{dt <- `dt*`} = $clos_deftypes(C.TYPES_context)

;; test.spectec:1761.1-1761.91
relation Numtype_ok: `%|-%:OK`(context, numtype)
  ;; test.spectec:1768.1-1769.20
  rule _{C : context, numtype : numtype}:
    `%|-%:OK`(C, numtype)

;; test.spectec:1762.1-1762.91
relation Vectype_ok: `%|-%:OK`(context, vectype)
  ;; test.spectec:1771.1-1772.20
  rule _{C : context, vectype : vectype}:
    `%|-%:OK`(C, vectype)

;; test.spectec:1842.1-1843.79
syntax oktypenat = 
  | OK(nat)

;; test.spectec:1845.1-1845.103
relation Packtype_ok: `%|-%:OK`(context, packtype)
  ;; test.spectec:1873.1-1874.21
  rule _{C : context, packtype : packtype}:
    `%|-%:OK`(C, packtype)

;; test.spectec:2168.1-2168.116
relation Packtype_sub: `%|-%<:%`(context, packtype, packtype)
  ;; test.spectec:2177.1-2178.28
  rule _{C : context, packtype : packtype}:
    `%|-%<:%`(C, packtype, packtype)

;; test.spectec:2026.1-2026.103
relation Numtype_sub: `%|-%<:%`(context, numtype, numtype)
  ;; test.spectec:2032.1-2033.26
  rule _{C : context, numtype : numtype}:
    `%|-%<:%`(C, numtype, numtype)

;; test.spectec:1827.1-1828.70
relation Expand: `%~~%`(deftype, comptype)
  ;; test.spectec:1832.1-1832.91
  rule _{deftype : deftype, comptype : comptype, `final?` : final?, `typeuse*` : typeuse*}:
    `%~~%`(deftype, comptype)
    -- if ($unrolldt(deftype) = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, comptype))

;; test.spectec:2027.1-2027.103
relation Vectype_sub: `%|-%<:%`(context, vectype, vectype)
  ;; test.spectec:2035.1-2036.26
  rule _{C : context, vectype : vectype}:
    `%|-%<:%`(C, vectype, vectype)

;; test.spectec:1912.1-1912.70
def $before(typeuse : typeuse, nat : nat) : bool
  ;; test.spectec:1913.1-1913.30
  def $before{j : n, i : nat}(REC_typeuse(j), i) = (j < i)
  ;; test.spectec:1914.1-1914.45
  def $before{typeuse : typeuse, i : nat}(typeuse, i) = true

;; test.spectec:1916.1-1916.44
def $unrollht_(context : context, heaptype : heaptype) : subtype
  ;; test.spectec:1917.1-1917.48
  def $unrollht_{C : context, deftype : deftype}(C, (deftype : deftype <: heaptype)) = $unrolldt(deftype)
  ;; test.spectec:1918.1-1918.62
  def $unrollht_{C : context, typeidx : typeidx}(C, _IDX_heaptype(typeidx)) = $unrolldt(C.TYPES_context[typeidx!`%`_typeidx.0])
  ;; test.spectec:1919.1-1919.37
  def $unrollht_{C : context, i : n}(C, REC_heaptype(i)) = C.RECS_context[i]

;; test.spectec:1763.1-2170.117
rec {

;; test.spectec:1763.1-1763.92
relation Heaptype_ok: `%|-%:OK`(context, heaptype)
  ;; test.spectec:1774.1-1775.24
  rule abs{C : context, absheaptype : absheaptype}:
    `%|-%:OK`(C, (absheaptype : absheaptype <: heaptype))

  ;; test.spectec:1777.1-1779.35
  rule typeuse{C : context, typeuse : typeuse}:
    `%|-%:OK`(C, (typeuse : typeuse <: heaptype))
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)

  ;; test.spectec:1781.1-1782.16
  rule bot{C : context}:
    `%|-%:OK`(C, BOT_heaptype)

;; test.spectec:1764.1-1764.91
relation Reftype_ok: `%|-%:OK`(context, reftype)
  ;; test.spectec:1784.1-1786.37
  rule _{C : context, heaptype : heaptype}:
    `%|-%:OK`(C, REF_reftype(NULL_null?{}, heaptype))
    -- Heaptype_ok: `%|-%:OK`(C, heaptype)

;; test.spectec:1765.1-1765.91
relation Valtype_ok: `%|-%:OK`(context, valtype)
  ;; test.spectec:1788.1-1790.35
  rule num{C : context, numtype : numtype}:
    `%|-%:OK`(C, (numtype : numtype <: valtype))
    -- Numtype_ok: `%|-%:OK`(C, numtype)

  ;; test.spectec:1792.1-1794.35
  rule vec{C : context, vectype : vectype}:
    `%|-%:OK`(C, (vectype : vectype <: valtype))
    -- Vectype_ok: `%|-%:OK`(C, vectype)

  ;; test.spectec:1796.1-1798.35
  rule ref{C : context, reftype : reftype}:
    `%|-%:OK`(C, (reftype : reftype <: valtype))
    -- Reftype_ok: `%|-%:OK`(C, reftype)

  ;; test.spectec:1800.1-1801.16
  rule bot{C : context}:
    `%|-%:OK`(C, BOT_valtype)

;; test.spectec:1766.1-1766.94
relation Typeuse_ok: `%|-%:OK`(context, typeuse)
  ;; test.spectec:1860.1-1862.30
  rule typeidx{C : context, typeidx : typeidx, dt : deftype}:
    `%|-%:OK`(C, _IDX_typeuse(typeidx))
    -- if (C.TYPES_context[typeidx!`%`_typeidx.0] = dt)

  ;; test.spectec:1864.1-1866.23
  rule rec{C : context, i : n, st : subtype}:
    `%|-%:OK`(C, REC_typeuse(i))
    -- if (C.RECS_context[i] = st)

  ;; test.spectec:1868.1-1870.35
  rule deftype{C : context, deftype : deftype}:
    `%|-%:OK`(C, (deftype : deftype <: typeuse))
    -- Deftype_ok: `%|-%:OK`(C, deftype)

;; test.spectec:1807.1-1807.100
relation Resulttype_ok: `%|-%:OK`(context, resulttype)
  ;; test.spectec:1814.1-1816.32
  rule _{C : context, `t*` : valtype*}:
    `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))
    -- (Valtype_ok: `%|-%:OK`(C, t))*{t <- `t*`}

;; test.spectec:1846.1-1846.104
relation Fieldtype_ok: `%|-%:OK`(context, fieldtype)
  ;; test.spectec:1884.1-1886.43
  rule _{C : context, storagetype : storagetype}:
    `%|-%:OK`(C, `%%`_fieldtype(MUT_mut?{}, storagetype))
    -- Storagetype_ok: `%|-%:OK`(C, storagetype)

;; test.spectec:1847.1-1847.106
relation Storagetype_ok: `%|-%:OK`(context, storagetype)
  ;; test.spectec:1876.1-1878.35
  rule val{C : context, valtype : valtype}:
    `%|-%:OK`(C, (valtype : valtype <: storagetype))
    -- Valtype_ok: `%|-%:OK`(C, valtype)

  ;; test.spectec:1880.1-1882.37
  rule pack{C : context, packtype : packtype}:
    `%|-%:OK`(C, (packtype : packtype <: storagetype))
    -- Packtype_ok: `%|-%:OK`(C, packtype)

;; test.spectec:1848.1-1848.103
relation Comptype_ok: `%|-%:OK`(context, comptype)
  ;; test.spectec:1889.1-1891.42
  rule struct{C : context, `fieldtype*` : fieldtype*}:
    `%|-%:OK`(C, STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))
    -- (Fieldtype_ok: `%|-%:OK`(C, fieldtype))*{fieldtype <- `fieldtype*`}

  ;; test.spectec:1893.1-1895.39
  rule array{C : context, fieldtype : fieldtype}:
    `%|-%:OK`(C, ARRAY_comptype(fieldtype))
    -- Fieldtype_ok: `%|-%:OK`(C, fieldtype)

  ;; test.spectec:1897.1-1900.35
  rule func{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:OK`(C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; test.spectec:1851.1-1851.126
relation Subtype_ok2: `%|-%:%`(context, subtype, oktypenat)
  ;; test.spectec:1921.1-1930.49
  rule _{C : context, `typeuse*` : typeuse*, comptype : comptype, i : nat, `comptype'*` : comptype*, `typeuse'**` : typeuse**}:
    `%|-%:%`(C, SUB_subtype(FINAL_final?{}, typeuse*{typeuse <- `typeuse*`}, comptype), OK_oktypenat(i))
    -- if (|typeuse*{typeuse <- `typeuse*`}| <= 1)
    -- (Typeuse_ok: `%|-%:OK`(C, typeuse))*{typeuse <- `typeuse*`}
    -- (if $before(typeuse, i))*{typeuse <- `typeuse*`}
    -- (if ($unrollht_(C, (typeuse : typeuse <: heaptype)) = SUB_subtype(?(), typeuse'*{typeuse' <- `typeuse'*`}, comptype')))*{comptype' <- `comptype'*`, typeuse <- `typeuse*`, `typeuse'*` <- `typeuse'**`}
    -- Comptype_ok: `%|-%:OK`(C, comptype)
    -- (Comptype_sub: `%|-%<:%`(C, comptype, comptype'))*{comptype' <- `comptype'*`}

;; test.spectec:1852.1-1852.126
relation Rectype_ok2: `%|-%:%`(context, rectype, oktypenat)
  ;; test.spectec:1942.1-1943.23
  rule empty{C : context, i : nat}:
    `%|-%:%`(C, REC_rectype(`%`_list([])), OK_oktypenat(i))

  ;; test.spectec:1945.1-1948.49
  rule cons{C : context, subtype_1 : subtype, `subtype*` : subtype*, i : nat}:
    `%|-%:%`(C, REC_rectype(`%`_list([subtype_1] ++ subtype*{subtype <- `subtype*`})), OK_oktypenat(i))
    -- Subtype_ok2: `%|-%:%`(C, subtype_1, OK_oktypenat(i))
    -- Rectype_ok2: `%|-%:%`(C, REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})), OK_oktypenat((i + 1)))

;; test.spectec:1853.1-1853.102
relation Deftype_ok: `%|-%:OK`(context, deftype)
  ;; test.spectec:1951.1-1955.14
  rule _{C : context, rectype : rectype, i : n, n : n, `subtype*` : subtype*}:
    `%|-%:OK`(C, _DEF_deftype(rectype, i))
    -- Rectype_ok2: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS subtype^n{subtype <- `subtype*`}} +++ C, rectype, OK_oktypenat(0))
    -- if (rectype = REC_rectype(`%`_list(subtype^n{subtype <- `subtype*`})))
    -- if (i < n)

;; test.spectec:1856.1-1856.108
relation Comptype_sub: `%|-%<:%`(context, comptype, comptype)
  ;; test.spectec:2200.1-2202.41
  rule struct{C : context, `ft_1*` : fieldtype*, `ft'_1*` : fieldtype*, `ft_2*` : fieldtype*}:
    `%|-%<:%`(C, STRUCT_comptype(`%`_list(ft_1*{ft_1 <- `ft_1*`} ++ ft'_1*{ft'_1 <- `ft'_1*`})), STRUCT_comptype(`%`_list(ft_2*{ft_2 <- `ft_2*`})))
    -- (Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2))*{ft_1 <- `ft_1*`, ft_2 <- `ft_2*`}

  ;; test.spectec:2204.1-2206.38
  rule array{C : context, ft_1 : fieldtype, ft_2 : fieldtype}:
    `%|-%<:%`(C, ARRAY_comptype(ft_1), ARRAY_comptype(ft_2))
    -- Fieldtype_sub: `%|-%<:%`(C, ft_1, ft_2)

  ;; test.spectec:2208.1-2211.41
  rule func{C : context, `t_11*` : valtype*, `t_12*` : valtype*, `t_21*` : valtype*, `t_22*` : valtype*}:
    `%|-%<:%`(C, `FUNC%->%`_comptype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), `%`_resulttype(t_12*{t_12 <- `t_12*`})), `FUNC%->%`_comptype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_11*{t_11 <- `t_11*`}))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_12*{t_12 <- `t_12*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`}))

;; test.spectec:1857.1-1857.107
relation Deftype_sub: `%|-%<:%`(context, deftype, deftype)
  ;; test.spectec:2214.1-2216.66
  rule refl{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($clos_deftype(C, deftype_1) = $clos_deftype(C, deftype_2))

  ;; test.spectec:2218.1-2221.49
  rule super{C : context, deftype_1 : deftype, deftype_2 : deftype, `final?` : final?, `typeuse*` : typeuse*, ct : comptype, i : nat}:
    `%|-%<:%`(C, deftype_1, deftype_2)
    -- if ($unrolldt(deftype_1) = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))
    -- Heaptype_sub: `%|-%<:%`(C, (typeuse*{typeuse <- `typeuse*`}[i] : typeuse <: heaptype), (deftype_2 : deftype <: heaptype))

;; test.spectec:2028.1-2028.104
relation Heaptype_sub: `%|-%<:%`(context, heaptype, heaptype)
  ;; test.spectec:2039.1-2040.28
  rule refl{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, heaptype, heaptype)

  ;; test.spectec:2042.1-2046.48
  rule trans{C : context, heaptype_1 : heaptype, heaptype_2 : heaptype, heaptype' : heaptype}:
    `%|-%<:%`(C, heaptype_1, heaptype_2)
    -- Heaptype_ok: `%|-%:OK`(C, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype_1, heaptype')
    -- Heaptype_sub: `%|-%<:%`(C, heaptype', heaptype_2)

  ;; test.spectec:2048.1-2049.17
  rule `eq-any`{C : context}:
    `%|-%<:%`(C, EQ_heaptype, ANY_heaptype)

  ;; test.spectec:2051.1-2052.17
  rule `i31-eq`{C : context}:
    `%|-%<:%`(C, I31_heaptype, EQ_heaptype)

  ;; test.spectec:2054.1-2055.20
  rule `struct-eq`{C : context}:
    `%|-%<:%`(C, STRUCT_heaptype, EQ_heaptype)

  ;; test.spectec:2057.1-2058.19
  rule `array-eq`{C : context}:
    `%|-%<:%`(C, ARRAY_heaptype, EQ_heaptype)

  ;; test.spectec:2060.1-2062.42
  rule struct{C : context, deftype : deftype, `fieldtype*` : fieldtype*}:
    `%|-%<:%`(C, (deftype : deftype <: heaptype), STRUCT_heaptype)
    -- Expand: `%~~%`(deftype, STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`})))

  ;; test.spectec:2064.1-2066.40
  rule array{C : context, deftype : deftype, fieldtype : fieldtype}:
    `%|-%<:%`(C, (deftype : deftype <: heaptype), ARRAY_heaptype)
    -- Expand: `%~~%`(deftype, ARRAY_comptype(fieldtype))

  ;; test.spectec:2068.1-2070.42
  rule func{C : context, deftype : deftype, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%<:%`(C, (deftype : deftype <: heaptype), FUNC_heaptype)
    -- Expand: `%~~%`(deftype, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2072.1-2074.46
  rule def{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, (deftype_1 : deftype <: heaptype), (deftype_2 : deftype <: heaptype))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)

  ;; test.spectec:2076.1-2078.53
  rule `typeidx-l`{C : context, typeidx : typeidx, heaptype : heaptype}:
    `%|-%<:%`(C, _IDX_heaptype(typeidx), heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, (C.TYPES_context[typeidx!`%`_typeidx.0] : deftype <: heaptype), heaptype)

  ;; test.spectec:2080.1-2082.53
  rule `typeidx-r`{C : context, heaptype : heaptype, typeidx : typeidx}:
    `%|-%<:%`(C, heaptype, _IDX_heaptype(typeidx))
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, (C.TYPES_context[typeidx!`%`_typeidx.0] : deftype <: heaptype))

  ;; test.spectec:2084.1-2086.51
  rule `rec-struct`{C : context, i : n, `final?` : final?, `fieldtype*` : fieldtype*}:
    `%|-%<:%`(C, REC_heaptype(i), STRUCT_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], STRUCT_comptype(`%`_list(fieldtype*{fieldtype <- `fieldtype*`}))))

  ;; test.spectec:2088.1-2090.49
  rule `rec-array`{C : context, i : n, `final?` : final?, fieldtype : fieldtype}:
    `%|-%<:%`(C, REC_heaptype(i), ARRAY_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], ARRAY_comptype(fieldtype)))

  ;; test.spectec:2092.1-2094.51
  rule `rec-func`{C : context, i : n, `final?` : final?, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%<:%`(C, REC_heaptype(i), FUNC_heaptype)
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, [], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))))

  ;; test.spectec:2096.1-2098.43
  rule `rec-sub`{C : context, i : n, `typeuse*` : typeuse*, j : nat, `final?` : final?, ct : comptype}:
    `%|-%<:%`(C, REC_heaptype(i), (typeuse*{typeuse <- `typeuse*`}[j] : typeuse <: heaptype))
    -- if (C.RECS_context[i] = SUB_subtype(final?{final <- `final?`}, typeuse*{typeuse <- `typeuse*`}, ct))

  ;; test.spectec:2100.1-2103.25
  rule none{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NONE_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, ANY_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2105.1-2108.25
  rule nofunc{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOFUNC_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, FUNC_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2110.1-2113.25
  rule noexn{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOEXN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXN_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2115.1-2118.25
  rule noextern{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, NOEXTERN_heaptype, heaptype)
    -- Heaptype_sub: `%|-%<:%`(C, heaptype, EXTERN_heaptype)
    -- if (heaptype =/= BOT_heaptype)

  ;; test.spectec:2120.1-2121.23
  rule bot{C : context, heaptype : heaptype}:
    `%|-%<:%`(C, BOT_heaptype, heaptype)

;; test.spectec:2029.1-2029.103
relation Reftype_sub: `%|-%<:%`(context, reftype, reftype)
  ;; test.spectec:2124.1-2126.37
  rule nonnull{C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(?(), ht_1), REF_reftype(?(), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)

  ;; test.spectec:2128.1-2130.37
  rule null{C : context, ht_1 : heaptype, ht_2 : heaptype}:
    `%|-%<:%`(C, REF_reftype(NULL_null?{}, ht_1), REF_reftype(?(NULL_null), ht_2))
    -- Heaptype_sub: `%|-%<:%`(C, ht_1, ht_2)

;; test.spectec:2030.1-2030.103
relation Valtype_sub: `%|-%<:%`(context, valtype, valtype)
  ;; test.spectec:2133.1-2135.46
  rule num{C : context, numtype_1 : numtype, numtype_2 : numtype}:
    `%|-%<:%`(C, (numtype_1 : numtype <: valtype), (numtype_2 : numtype <: valtype))
    -- Numtype_sub: `%|-%<:%`(C, numtype_1, numtype_2)

  ;; test.spectec:2137.1-2139.46
  rule vec{C : context, vectype_1 : vectype, vectype_2 : vectype}:
    `%|-%<:%`(C, (vectype_1 : vectype <: valtype), (vectype_2 : vectype <: valtype))
    -- Vectype_sub: `%|-%<:%`(C, vectype_1, vectype_2)

  ;; test.spectec:2141.1-2143.46
  rule ref{C : context, reftype_1 : reftype, reftype_2 : reftype}:
    `%|-%<:%`(C, (reftype_1 : reftype <: valtype), (reftype_2 : reftype <: valtype))
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)

  ;; test.spectec:2145.1-2146.22
  rule bot{C : context, valtype : valtype}:
    `%|-%<:%`(C, BOT_valtype, valtype)

;; test.spectec:2151.1-2151.115
relation Resulttype_sub: `%|-%<:%`(context, resulttype, resulttype)
  ;; test.spectec:2154.1-2156.37
  rule _{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%<:%`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (Valtype_sub: `%|-%<:%`(C, t_1, t_2))*{t_1 <- `t_1*`, t_2 <- `t_2*`}

;; test.spectec:2169.1-2169.119
relation Storagetype_sub: `%|-%<:%`(context, storagetype, storagetype)
  ;; test.spectec:2181.1-2183.46
  rule val{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, (valtype_1 : valtype <: storagetype), (valtype_2 : valtype <: storagetype))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)

  ;; test.spectec:2185.1-2187.49
  rule pack{C : context, packtype_1 : packtype, packtype_2 : packtype}:
    `%|-%<:%`(C, (packtype_1 : packtype <: storagetype), (packtype_2 : packtype <: storagetype))
    -- Packtype_sub: `%|-%<:%`(C, packtype_1, packtype_2)

;; test.spectec:2170.1-2170.117
relation Fieldtype_sub: `%|-%<:%`(context, fieldtype, fieldtype)
  ;; test.spectec:2190.1-2192.40
  rule const{C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, `%%`_fieldtype(?(), zt_1), `%%`_fieldtype(?(), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)

  ;; test.spectec:2194.1-2197.40
  rule var{C : context, zt_1 : storagetype, zt_2 : storagetype}:
    `%|-%<:%`(C, `%%`_fieldtype(?(MUT_mut), zt_1), `%%`_fieldtype(?(MUT_mut), zt_2))
    -- Storagetype_sub: `%|-%<:%`(C, zt_1, zt_2)
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)
}

;; test.spectec:1806.1-1806.96
relation Localtype_ok: `%|-%:OK`(context, localtype)
  ;; test.spectec:1810.1-1812.29
  rule _{C : context, init : init, t : valtype}:
    `%|-%:OK`(C, `%%`_localtype(init, t))
    -- Valtype_ok: `%|-%:OK`(C, t)

;; test.spectec:1808.1-1808.99
relation Instrtype_ok: `%|-%:OK`(context, instrtype)
  ;; test.spectec:1818.1-1822.29
  rule _{C : context, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*, `lct*` : localtype*}:
    `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_1*{t_1 <- `t_1*`}))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}))
    -- (if (C.LOCALS_context[x!`%`_idx.0] = lct))*{lct <- `lct*`, x <- `x*`}

;; test.spectec:1829.1-1830.70
relation Expand_use: `%~~_%%`(typeuse, context, comptype)
  ;; test.spectec:1834.1-1834.84
  rule deftype{deftype : deftype, C : context, comptype : comptype}:
    `%~~_%%`((deftype : deftype <: typeuse), C, comptype)
    -- Expand: `%~~%`(deftype, comptype)

  ;; test.spectec:1835.1-1835.93
  rule typeidx{typeidx : typeidx, C : context, comptype : comptype}:
    `%~~_%%`(_IDX_typeuse(typeidx), C, comptype)
    -- Expand: `%~~%`(C.TYPES_context[typeidx!`%`_typeidx.0], comptype)

;; test.spectec:1840.1-1841.76
syntax oktypeidx = 
  | OK(typeidx : typeidx)

;; test.spectec:1849.1-1849.126
relation Subtype_ok: `%|-%:%`(context, subtype, oktypeidx)
  ;; test.spectec:1903.1-1910.49
  rule _{C : context, `x*` : idx*, comptype : comptype, x_0 : idx, `comptype'*` : comptype*, `yy**` : typeuse**}:
    `%|-%:%`(C, SUB_subtype(FINAL_final?{}, _IDX_typeuse(x)*{x <- `x*`}, comptype), OK_oktypeidx(x_0))
    -- if (|x*{x <- `x*`}| <= 1)
    -- (if (x!`%`_idx.0 < x_0!`%`_idx.0))*{x <- `x*`}
    -- (if ($unrolldt(C.TYPES_context[x!`%`_idx.0]) = SUB_subtype(?(), yy*{yy <- `yy*`}, comptype')))*{comptype' <- `comptype'*`, x <- `x*`, `yy*` <- `yy**`}
    -- Comptype_ok: `%|-%:OK`(C, comptype)
    -- (Comptype_sub: `%|-%<:%`(C, comptype, comptype'))*{comptype' <- `comptype'*`}

;; test.spectec:1850.1-1850.126
rec {

;; test.spectec:1850.1-1850.126
relation Rectype_ok: `%|-%:%`(context, rectype, oktypeidx)
  ;; test.spectec:1933.1-1934.23
  rule empty{C : context, x : idx}:
    `%|-%:%`(C, REC_rectype(`%`_list([])), OK_oktypeidx(x))

  ;; test.spectec:1936.1-1939.48
  rule cons{C : context, subtype_1 : subtype, `subtype*` : subtype*, x : idx}:
    `%|-%:%`(C, REC_rectype(`%`_list([subtype_1] ++ subtype*{subtype <- `subtype*`})), OK_oktypeidx(x))
    -- Subtype_ok: `%|-%:%`(C, subtype_1, OK_oktypeidx(x))
    -- Rectype_ok: `%|-%:%`(C, REC_rectype(`%`_list(subtype*{subtype <- `subtype*`})), OK_oktypeidx(`%`_typeidx((x!`%`_idx.0 + 1))))
}

;; test.spectec:1960.1-1960.120
relation Limits_ok: `%|-%:%`(context, limits, nat)
  ;; test.spectec:1968.1-1971.23
  rule _{C : context, n : n, `m?` : m?, k : nat}:
    `%|-%:%`(C, `[%..%]`_limits(`%`_u64(n), `%`_u64(m)?{m <- `m?`}), k)
    -- if (n <= k)
    -- (if ((n <= m) /\ (m <= k)))?{m <- `m?`}

;; test.spectec:1961.1-1961.97
relation Tagtype_ok: `%|-%:OK`(context, tagtype)
  ;; test.spectec:1973.1-1976.54
  rule _{C : context, typeuse : typeuse, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:OK`(C, typeuse)
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- Expand_use: `%~~_%%`(typeuse, C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:1962.1-1962.100
relation Globaltype_ok: `%|-%:OK`(context, globaltype)
  ;; test.spectec:1978.1-1980.29
  rule _{C : context, t : valtype}:
    `%|-%:OK`(C, `%%`_globaltype(MUT_mut?{}, t))
    -- Valtype_ok: `%|-%:OK`(C, t)

;; test.spectec:1963.1-1963.97
relation Memtype_ok: `%|-%:OK`(context, memtype)
  ;; test.spectec:1982.1-1984.58
  rule _{C : context, addrtype : addrtype, limits : limits}:
    `%|-%:OK`(C, `%%PAGE`_memtype(addrtype, limits))
    -- Limits_ok: `%|-%:%`(C, limits, (2 ^ ((($size((addrtype : addrtype <: numtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))

;; test.spectec:1964.1-1964.99
relation Tabletype_ok: `%|-%:OK`(context, tabletype)
  ;; test.spectec:1986.1-1989.35
  rule _{C : context, addrtype : addrtype, limits : limits, reftype : reftype}:
    `%|-%:OK`(C, `%%%`_tabletype(addrtype, limits, reftype))
    -- Limits_ok: `%|-%:%`(C, limits, ((((2 ^ $size((addrtype : addrtype <: numtype))) : nat <:> int) - (1 : nat <:> int)) : int <:> nat))
    -- Reftype_ok: `%|-%:OK`(C, reftype)

;; test.spectec:1965.1-1965.100
relation Externtype_ok: `%|-%:OK`(context, externtype)
  ;; test.spectec:1992.1-1994.35
  rule tag{C : context, tagtype : tagtype}:
    `%|-%:OK`(C, TAG_externtype(tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, tagtype)

  ;; test.spectec:1996.1-1998.41
  rule global{C : context, globaltype : globaltype}:
    `%|-%:OK`(C, GLOBAL_externtype(globaltype))
    -- Globaltype_ok: `%|-%:OK`(C, globaltype)

  ;; test.spectec:2000.1-2002.35
  rule mem{C : context, memtype : memtype}:
    `%|-%:OK`(C, MEM_externtype(memtype))
    -- Memtype_ok: `%|-%:OK`(C, memtype)

  ;; test.spectec:2004.1-2006.39
  rule table{C : context, tabletype : tabletype}:
    `%|-%:OK`(C, TABLE_externtype(tabletype))
    -- Tabletype_ok: `%|-%:OK`(C, tabletype)

  ;; test.spectec:2008.1-2011.54
  rule func{C : context, typeuse : typeuse, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:OK`(C, FUNC_externtype(typeuse))
    -- Typeuse_ok: `%|-%:OK`(C, typeuse)
    -- Expand_use: `%~~_%%`(typeuse, C, `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:2152.1-2152.114
relation Instrtype_sub: `%|-%<:%`(context, instrtype, instrtype)
  ;; test.spectec:2158.1-2163.31
  rule _{C : context, `t_11*` : valtype*, `x_1*` : idx*, `t_12*` : valtype*, `t_21*` : valtype*, `x_2*` : idx*, `t_22*` : valtype*, `x*` : idx*, `t*` : valtype*}:
    `%|-%<:%`(C, `%->_%%`_instrtype(`%`_resulttype(t_11*{t_11 <- `t_11*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_12*{t_12 <- `t_12*`})), `%->_%%`_instrtype(`%`_resulttype(t_21*{t_21 <- `t_21*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_22*{t_22 <- `t_22*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_21*{t_21 <- `t_21*`}), `%`_resulttype(t_11*{t_11 <- `t_11*`}))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_12*{t_12 <- `t_12*`}), `%`_resulttype(t_22*{t_22 <- `t_22*`}))
    -- if (x*{x <- `x*`} = $setminus_(syntax localidx, x_2*{x_2 <- `x_2*`}, x_1*{x_1 <- `x_1*`}))
    -- (if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(SET_init, t)))*{t <- `t*`, x <- `x*`}

;; test.spectec:2226.1-2226.110
relation Limits_sub: `%|-%<:%`(context, limits, limits)
  ;; test.spectec:2234.1-2237.22
  rule max{C : context, n_1 : n, m_1 : m, n_2 : n, `m_2?` : m?}:
    `%|-%<:%`(C, `[%..%]`_limits(`%`_u64(n_1), ?(`%`_u64(m_1))), `[%..%]`_limits(`%`_u64(n_2), `%`_u64(m_2)?{m_2 <- `m_2?`}))
    -- if (n_1 >= n_2)
    -- (if (m_1 <= m_2))?{m_2 <- `m_2?`}

  ;; test.spectec:2239.1-2241.19
  rule eps{C : context, n_1 : n, n_2 : n}:
    `%|-%<:%`(C, `[%..%]`_limits(`%`_u64(n_1), ?()), `[%..%]`_limits(`%`_u64(n_2), ?()))
    -- if (n_1 >= n_2)

;; test.spectec:2227.1-2227.111
relation Tagtype_sub: `%|-%<:%`(context, tagtype, tagtype)
  ;; test.spectec:2244.1-2247.46
  rule _{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, (deftype_1 : deftype <: typeuse), (deftype_2 : deftype <: typeuse))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)
    -- Deftype_sub: `%|-%<:%`(C, deftype_2, deftype_1)

;; test.spectec:2228.1-2228.114
relation Globaltype_sub: `%|-%<:%`(context, globaltype, globaltype)
  ;; test.spectec:2249.1-2251.46
  rule const{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, `%%`_globaltype(?(), valtype_1), `%%`_globaltype(?(), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)

  ;; test.spectec:2253.1-2256.46
  rule var{C : context, valtype_1 : valtype, valtype_2 : valtype}:
    `%|-%<:%`(C, `%%`_globaltype(?(MUT_mut), valtype_1), `%%`_globaltype(?(MUT_mut), valtype_2))
    -- Valtype_sub: `%|-%<:%`(C, valtype_1, valtype_2)
    -- Valtype_sub: `%|-%<:%`(C, valtype_2, valtype_1)

;; test.spectec:2229.1-2229.111
relation Memtype_sub: `%|-%<:%`(context, memtype, memtype)
  ;; test.spectec:2258.1-2260.43
  rule _{C : context, addrtype : addrtype, limits_1 : limits, limits_2 : limits}:
    `%|-%<:%`(C, `%%PAGE`_memtype(addrtype, limits_1), `%%PAGE`_memtype(addrtype, limits_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)

;; test.spectec:2230.1-2230.113
relation Tabletype_sub: `%|-%<:%`(context, tabletype, tabletype)
  ;; test.spectec:2262.1-2266.46
  rule _{C : context, addrtype : addrtype, limits_1 : limits, reftype_1 : reftype, limits_2 : limits, reftype_2 : reftype}:
    `%|-%<:%`(C, `%%%`_tabletype(addrtype, limits_1, reftype_1), `%%%`_tabletype(addrtype, limits_2, reftype_2))
    -- Limits_sub: `%|-%<:%`(C, limits_1, limits_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_1, reftype_2)
    -- Reftype_sub: `%|-%<:%`(C, reftype_2, reftype_1)

;; test.spectec:2231.1-2231.114
relation Externtype_sub: `%|-%<:%`(context, externtype, externtype)
  ;; test.spectec:2269.1-2271.46
  rule tag{C : context, tagtype_1 : tagtype, tagtype_2 : tagtype}:
    `%|-%<:%`(C, TAG_externtype(tagtype_1), TAG_externtype(tagtype_2))
    -- Tagtype_sub: `%|-%<:%`(C, tagtype_1, tagtype_2)

  ;; test.spectec:2273.1-2275.55
  rule global{C : context, globaltype_1 : globaltype, globaltype_2 : globaltype}:
    `%|-%<:%`(C, GLOBAL_externtype(globaltype_1), GLOBAL_externtype(globaltype_2))
    -- Globaltype_sub: `%|-%<:%`(C, globaltype_1, globaltype_2)

  ;; test.spectec:2277.1-2279.46
  rule mem{C : context, memtype_1 : memtype, memtype_2 : memtype}:
    `%|-%<:%`(C, MEM_externtype(memtype_1), MEM_externtype(memtype_2))
    -- Memtype_sub: `%|-%<:%`(C, memtype_1, memtype_2)

  ;; test.spectec:2281.1-2283.52
  rule table{C : context, tabletype_1 : tabletype, tabletype_2 : tabletype}:
    `%|-%<:%`(C, TABLE_externtype(tabletype_1), TABLE_externtype(tabletype_2))
    -- Tabletype_sub: `%|-%<:%`(C, tabletype_1, tabletype_2)

  ;; test.spectec:2285.1-2287.46
  rule func{C : context, deftype_1 : deftype, deftype_2 : deftype}:
    `%|-%<:%`(C, FUNC_externtype((deftype_1 : deftype <: typeuse)), FUNC_externtype((deftype_2 : deftype <: typeuse)))
    -- Deftype_sub: `%|-%<:%`(C, deftype_1, deftype_2)

;; test.spectec:2337.1-2337.121
relation Blocktype_ok: `%|-%:%`(context, blocktype, instrtype)
  ;; test.spectec:2339.1-2341.38
  rule valtype{C : context, `valtype?` : valtype?}:
    `%|-%:%`(C, _RESULT_blocktype(valtype?{valtype <- `valtype?`}), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(lift(valtype?{valtype <- `valtype?`}))))
    -- (Valtype_ok: `%|-%:OK`(C, valtype))?{valtype <- `valtype?`}

  ;; test.spectec:2343.1-2345.51
  rule typeidx{C : context, typeidx : typeidx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, _IDX_blocktype(typeidx), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.TYPES_context[typeidx!`%`_typeidx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

;; test.spectec:2459.1-2459.77
relation Catch_ok: `%|-%:OK`(context, catch)
  ;; test.spectec:2476.1-2479.44
  rule catch{C : context, x : idx, l : labelidx, `t*` : valtype*}:
    `%|-%:OK`(C, CATCH_catch(x, l))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_idx.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_labelidx.0])

  ;; test.spectec:2481.1-2484.54
  rule catch_ref{C : context, x : idx, l : labelidx, `t*` : valtype*}:
    `%|-%:OK`(C, CATCH_REF_catch(x, l))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_idx.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[l!`%`_labelidx.0])

  ;; test.spectec:2486.1-2488.45
  rule catch_all{C : context, l : labelidx}:
    `%|-%:OK`(C, CATCH_ALL_catch(l))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype([]), C.LABELS_context[l!`%`_labelidx.0])

  ;; test.spectec:2490.1-2492.51
  rule catch_all_ref{C : context, l : labelidx}:
    `%|-%:OK`(C, CATCH_ALL_REF_catch(l))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype([REF_valtype(?(), EXN_heaptype)]), C.LABELS_context[l!`%`_labelidx.0])

;; test.spectec:4441.1-4441.44
def $default_(valtype : valtype) : val?
  ;; test.spectec:4442.1-4442.35
  def $default_{Inn : Inn}((Inn : addrtype <: valtype)) = ?(CONST_val((Inn : addrtype <: numtype), `%`_num_(0)))
  ;; test.spectec:4443.1-4443.52
  def $default_{Fnn : Fnn}((Fnn : Fnn <: valtype)) = ?(CONST_val((Fnn : Fnn <: numtype), $fzero($size((Fnn : Fnn <: numtype)))))
  ;; test.spectec:4444.1-4444.36
  def $default_{Vnn : Vnn}((Vnn : vectype <: valtype)) = ?(VCONST_val(Vnn, `%`_vec_(0)))
  ;; test.spectec:4445.1-4445.43
  def $default_{ht : heaptype}(REF_valtype(?(NULL_null), ht)) = ?(`REF.NULL_ADDR`_val)
  ;; test.spectec:4446.1-4446.28
  def $default_{ht : heaptype}(REF_valtype(?(), ht)) = ?()

;; test.spectec:2304.1-2305.71
relation Defaultable: `|-%DEFAULTABLE`(valtype)
  ;; test.spectec:4449.1-4449.62
  rule _{t : valtype}:
    `|-%DEFAULTABLE`(t)
    -- if ($default_(t) =/= ?())

;; test.spectec:2703.1-2703.131
relation Memarg_ok: `|-%:%->%`(memarg, addrtype, N)
  ;; test.spectec:2705.1-2708.27
  rule _{n : n, m : m, at : addrtype, N : N}:
    `|-%:%->%`({ALIGN `%`_u32(n), OFFSET `%`_u64(m)}, at, N)
    -- if (((2 ^ n) : nat <:> rat) <= ((N : nat <:> rat) / (8 : nat <:> rat)))
    -- if (m < (2 ^ $size((at : addrtype <: numtype))))

;; test.spectec:2550.1-2550.111
def $is_packtype(storagetype : storagetype) : bool
  ;; test.spectec:2551.1-2551.42
  def $is_packtype{zt : storagetype}(zt) = (zt =/= ($unpack(zt) : valtype <: storagetype))

;; test.spectec:2300.1-2301.96
rec {

;; test.spectec:2300.1-2300.95
relation Instr_ok: `%|-%:%`(context, instr, instrtype)
  ;; test.spectec:2313.1-2314.24
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2316.1-2318.42
  rule unreachable{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, UNREACHABLE_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2320.1-2322.29
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- Valtype_ok: `%|-%:OK`(C, t)

  ;; test.spectec:2324.1-2326.29
  rule `select-expl`{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr(?([t])), `%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)

  ;; test.spectec:2328.1-2332.37
  rule `select-impl`{C : context, t : valtype, t' : valtype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, SELECT_instr(?()), `%->_%%`_instrtype(`%`_resulttype([t t I32_valtype]), [], `%`_resulttype([t])))
    -- Valtype_ok: `%|-%:OK`(C, t)
    -- Valtype_sub: `%|-%<:%`(C, t, t')
    -- if ((t' = (numtype : numtype <: valtype)) \/ (t' = (vectype : vectype <: valtype)))

  ;; test.spectec:2348.1-2351.67
  rule block{C : context, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%|-%:%`(C, BLOCK_instr(bt, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2353.1-2356.67
  rule loop{C : context, bt : blocktype, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%|-%:%`(C, LOOP_instr(bt, instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_1*{t_1 <- `t_1*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2358.1-2362.71
  rule if{C : context, bt : blocktype, `instr_1*` : instr*, `instr_2*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x_1*` : idx*, `x_2*` : idx*}:
    `%|-%:%`(C, `IF%%ELSE%`_instr(bt, instr_1*{instr_1 <- `instr_1*`}, instr_2*{instr_2 <- `instr_2*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr_1*{instr_1 <- `instr_1*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2367.1-2370.42
  rule br{C : context, l : labelidx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_instr(l), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2372.1-2374.25
  rule br_if{C : context, l : labelidx, `t*` : valtype*}:
    `%|-%:%`(C, BR_IF_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})

  ;; test.spectec:2376.1-2380.49
  rule br_table{C : context, `l*` : labelidx*, l' : labelidx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, BR_TABLE_instr(l*{l <- `l*`}, l'), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l!`%`_labelidx.0]))*{l <- `l*`}
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t*{t <- `t*`}), C.LABELS_context[l'!`%`_labelidx.0])
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`} ++ [I32_valtype]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2382.1-2385.31
  rule br_on_null{C : context, l : labelidx, `t*` : valtype*, ht : heaptype}:
    `%|-%:%`(C, BR_ON_NULL_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(), ht)])))
    -- if (C.LABELS_context[l!`%`_labelidx.0]!`%`_resulttype.0 = t*{t <- `t*`})
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2387.1-2389.40
  rule br_on_non_null{C : context, l : labelidx, `t*` : valtype*, ht : heaptype}:
    `%|-%:%`(C, BR_ON_NON_NULL_instr(l), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype(t*{t <- `t*`})))
    -- if (C.LABELS_context[l!`%`_labelidx.0] = `%`_resulttype(t*{t <- `t*`} ++ [REF_valtype(NULL_null?{}, ht)]))

  ;; test.spectec:2391.1-2397.34
  rule br_on_cast{C : context, l : labelidx, rt_1 : reftype, rt_2 : reftype, `t*` : valtype*, rt : reftype}:
    `%|-%:%`(C, BR_ON_CAST_instr(l, rt_1, rt_2), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : reftype <: valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [($diffrt(rt_1, rt_2) : reftype <: valtype)])))
    -- if (C.LABELS_context[l!`%`_labelidx.0] = `%`_resulttype(t*{t <- `t*`} ++ [(rt : reftype <: valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt)

  ;; test.spectec:2399.1-2405.49
  rule br_on_cast_fail{C : context, l : labelidx, rt_1 : reftype, rt_2 : reftype, `t*` : valtype*, rt : reftype}:
    `%|-%:%`(C, BR_ON_CAST_FAIL_instr(l, rt_1, rt_2), `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ [(rt_1 : reftype <: valtype)]), [], `%`_resulttype(t*{t <- `t*`} ++ [(rt_2 : reftype <: valtype)])))
    -- if (C.LABELS_context[l!`%`_labelidx.0] = `%`_resulttype(t*{t <- `t*`} ++ [(rt : reftype <: valtype)]))
    -- Reftype_ok: `%|-%:OK`(C, rt_1)
    -- Reftype_ok: `%|-%:OK`(C, rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)
    -- Reftype_sub: `%|-%<:%`(C, $diffrt(rt_1, rt_2), rt)

  ;; test.spectec:2410.1-2412.45
  rule call{C : context, x : idx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, CALL_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2414.1-2416.45
  rule call_ref{C : context, x : idx, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, CALL_REF_instr(_IDX_typeuse(x)), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2418.1-2422.45
  rule call_indirect{C : context, x : idx, y : idx, `t_1*` : valtype*, at : addrtype, `t_2*` : valtype*, lim : limits, rt : reftype}:
    `%|-%:%`(C, CALL_INDIRECT_instr(x, _IDX_typeuse(y)), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [(at : addrtype <: valtype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPES_context[y!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2424.1-2427.42
  rule return{C : context, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, RETURN_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t*{t <- `t*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2430.1-2435.42
  rule return_call{C : context, x : idx, `t_3*` : valtype*, `t_1*` : valtype*, `t_4*` : valtype*, `t_2*` : valtype*, `t'_2*` : valtype*}:
    `%|-%:%`(C, RETURN_CALL_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2438.1-2443.42
  rule return_call_ref{C : context, x : idx, `t_3*` : valtype*, `t_1*` : valtype*, `t_4*` : valtype*, `t_2*` : valtype*, `t'_2*` : valtype*}:
    `%|-%:%`(C, RETURN_CALL_REF_instr(_IDX_typeuse(x)), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2446.1-2454.42
  rule return_call_indirect{C : context, x : idx, y : idx, `t_3*` : valtype*, `t_1*` : valtype*, at : addrtype, `t_4*` : valtype*, lim : limits, rt : reftype, `t_2*` : valtype*, `t'_2*` : valtype*}:
    `%|-%:%`(C, RETURN_CALL_INDIRECT_instr(x, _IDX_typeuse(y)), `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`} ++ t_1*{t_1 <- `t_1*`} ++ [(at : addrtype <: valtype)]), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))
    -- Reftype_sub: `%|-%<:%`(C, rt, REF_reftype(?(NULL_null), FUNC_heaptype))
    -- Expand: `%~~%`(C.TYPES_context[y!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- if (C.RETURN_context = ?(`%`_resulttype(t'_2*{t'_2 <- `t'_2*`})))
    -- Resulttype_sub: `%|-%<:%`(C, `%`_resulttype(t_2*{t_2 <- `t_2*`}), `%`_resulttype(t'_2*{t'_2 <- `t'_2*`}))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_3*{t_3 <- `t_3*`}), [], `%`_resulttype(t_4*{t_4 <- `t_4*`})))

  ;; test.spectec:2461.1-2464.42
  rule throw{C : context, x : idx, `t_1*` : valtype*, `t*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, THROW_instr(x), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ t*{t <- `t*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Expand: `%~~%`($as_deftype(C.TAGS_context[x!`%`_idx.0]), `FUNC%->%`_comptype(`%`_resulttype(t*{t <- `t*`}), `%`_resulttype([])))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2466.1-2468.42
  rule throw_ref{C : context, `t_1*` : valtype*, `t_2*` : valtype*}:
    `%|-%:%`(C, THROW_REF_instr, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`} ++ [REF_valtype(?(NULL_null), EXN_heaptype)]), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrtype_ok: `%|-%:OK`(C, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))

  ;; test.spectec:2470.1-2474.34
  rule try_table{C : context, bt : blocktype, `catch*` : catch*, `instr*` : instr*, `t_1*` : valtype*, `t_2*` : valtype*, `x*` : idx*}:
    `%|-%:%`(C, TRY_TABLE_instr(bt, `%`_list(catch*{catch <- `catch*`}), instr*{instr <- `instr*`}), `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), [], `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(), REFS [], RECS []} +++ C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Catch_ok: `%|-%:OK`(C, catch))*{catch <- `catch*`}

  ;; test.spectec:2497.1-2499.31
  rule `ref.null`{C : context, ht : heaptype}:
    `%|-%:%`(C, `REF.NULL`_instr(ht), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(NULL_null), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2501.1-2504.20
  rule `ref.func`{C : context, x : idx, dt : deftype}:
    `%|-%:%`(C, `REF.FUNC`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), (dt : deftype <: heaptype))])))
    -- if (C.FUNCS_context[x!`%`_idx.0] = dt)
    -- if (x <- C.REFS_context)

  ;; test.spectec:2506.1-2507.34
  rule `ref.i31`{C : context}:
    `%|-%:%`(C, `REF.I31`_instr, `%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), I31_heaptype)])))

  ;; test.spectec:2509.1-2511.31
  rule `ref.is_null`{C : context, ht : heaptype}:
    `%|-%:%`(C, `REF.IS_NULL`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([I32_valtype])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2513.1-2515.31
  rule `ref.as_non_null`{C : context, ht : heaptype}:
    `%|-%:%`(C, `REF.AS_NON_NULL`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ht)]), [], `%`_resulttype([REF_valtype(?(), ht)])))
    -- Heaptype_ok: `%|-%:OK`(C, ht)

  ;; test.spectec:2517.1-2518.51
  rule `ref.eq`{C : context}:
    `%|-%:%`(C, `REF.EQ`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), EQ_heaptype) REF_valtype(?(NULL_null), EQ_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2520.1-2524.33
  rule `ref.test`{C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, `REF.TEST`_instr(rt), `%->_%%`_instrtype(`%`_resulttype([(rt' : reftype <: valtype)]), [], `%`_resulttype([I32_valtype])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')

  ;; test.spectec:2526.1-2530.33
  rule `ref.cast`{C : context, rt : reftype, rt' : reftype}:
    `%|-%:%`(C, `REF.CAST`_instr(rt), `%->_%%`_instrtype(`%`_resulttype([(rt' : reftype <: valtype)]), [], `%`_resulttype([(rt : reftype <: valtype)])))
    -- Reftype_ok: `%|-%:OK`(C, rt)
    -- Reftype_ok: `%|-%:OK`(C, rt')
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')

  ;; test.spectec:2535.1-2536.42
  rule `i31.get`{C : context, sx : sx}:
    `%|-%:%`(C, `I31.GET`_instr(sx), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), I31_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2541.1-2543.45
  rule `struct.new`{C : context, x : idx, `zt*` : storagetype*, `mut?*` : mut?*}:
    `%|-%:%`(C, `STRUCT.NEW`_instr(x), `%->_%%`_instrtype(`%`_resulttype($unpack(zt)*{zt <- `zt*`}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))

  ;; test.spectec:2545.1-2548.48
  rule `struct.new_default`{C : context, x : idx, `mut?*` : mut?*, `zt*` : storagetype*}:
    `%|-%:%`(C, `STRUCT.NEW_DEFAULT`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)*{`mut?` <- `mut?*`, zt <- `zt*`})))
    -- (Defaultable: `|-%DEFAULTABLE`($unpack(zt)))*{zt <- `zt*`}

  ;; test.spectec:2553.1-2557.41
  rule `struct.get`{C : context, `sx?` : sx?, x : idx, i : fieldidx, zt : storagetype, `ft*` : fieldtype*, `mut?` : mut?}:
    `%|-%:%`(C, `STRUCT.GET`_instr(sx?{sx <- `sx?`}, x, i), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x))]), [], `%`_resulttype([$unpack(zt)])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i!`%`_fieldidx.0] = `%%`_fieldtype(mut?{mut <- `mut?`}, zt))
    -- if ((sx?{sx <- `sx?`} =/= ?()) <=> $is_packtype(zt))

  ;; test.spectec:2559.1-2562.24
  rule `struct.set`{C : context, x : idx, i : fieldidx, zt : storagetype, `ft*` : fieldtype*}:
    `%|-%:%`(C, `STRUCT.SET`_instr(x, i), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) $unpack(zt)]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], STRUCT_comptype(`%`_list(ft*{ft <- `ft*`})))
    -- if (ft*{ft <- `ft*`}[i!`%`_fieldidx.0] = `%%`_fieldtype(?(MUT_mut), zt))

  ;; test.spectec:2567.1-2569.43
  rule `array.new`{C : context, x : idx, zt : storagetype, `mut?` : mut?}:
    `%|-%:%`(C, `ARRAY.NEW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([$unpack(zt) I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2571.1-2574.45
  rule `array.new_default`{C : context, x : idx, `mut?` : mut?, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.NEW_DEFAULT`_instr(x), `%->_%%`_instrtype(`%`_resulttype([I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- Defaultable: `|-%DEFAULTABLE`($unpack(zt))

  ;; test.spectec:2576.1-2578.43
  rule `array.new_fixed`{C : context, x : idx, n : n, zt : storagetype, `mut?` : mut?}:
    `%|-%:%`(C, `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)), `%->_%%`_instrtype(`%`_resulttype($unpack(zt)^n{}), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))

  ;; test.spectec:2580.1-2583.40
  rule `array.new_elem`{C : context, x : idx, y : idx, `mut?` : mut?, rt : reftype}:
    `%|-%:%`(C, `ARRAY.NEW_ELEM`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, (rt : reftype <: storagetype))))
    -- Reftype_sub: `%|-%<:%`(C, C.ELEMS_context[y!`%`_idx.0], rt)

  ;; test.spectec:2585.1-2589.24
  rule `array.new_data`{C : context, x : idx, y : idx, `mut?` : mut?, zt : storagetype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, `ARRAY.NEW_DATA`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([I32_valtype I32_valtype]), [], `%`_resulttype([REF_valtype(?(), _IDX_heaptype(x))])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if (($unpack(zt) = (numtype : numtype <: valtype)) \/ ($unpack(zt) = (vectype : vectype <: valtype)))
    -- if (C.DATAS_context[y!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2591.1-2594.41
  rule `array.get`{C : context, `sx?` : sx?, x : idx, zt : storagetype, `mut?` : mut?}:
    `%|-%:%`(C, `ARRAY.GET`_instr(sx?{sx <- `sx?`}, x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype]), [], `%`_resulttype([$unpack(zt)])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt)))
    -- if ((sx?{sx <- `sx?`} =/= ?()) <=> $is_packtype(zt))

  ;; test.spectec:2596.1-2598.42
  rule `array.set`{C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt)]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2600.1-2601.43
  rule `array.len`{C : context}:
    `%|-%:%`(C, `ARRAY.LEN`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), ARRAY_heaptype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2603.1-2605.42
  rule `array.fill`{C : context, x : idx, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype $unpack(zt) I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))

  ;; test.spectec:2607.1-2611.40
  rule `array.copy`{C : context, x_1 : idx, x_2 : idx, zt_1 : storagetype, `mut?` : mut?, zt_2 : storagetype}:
    `%|-%:%`(C, `ARRAY.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x_1)) I32_valtype REF_valtype(?(NULL_null), _IDX_heaptype(x_2)) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x_1!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt_1)))
    -- Expand: `%~~%`(C.TYPES_context[x_2!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(mut?{mut <- `mut?`}, zt_2)))
    -- Storagetype_sub: `%|-%<:%`(C, zt_2, zt_1)

  ;; test.spectec:2613.1-2616.44
  rule `array.init_elem`{C : context, x : idx, y : idx, zt : storagetype}:
    `%|-%:%`(C, `ARRAY.INIT_ELEM`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- Storagetype_sub: `%|-%<:%`(C, (C.ELEMS_context[y!`%`_idx.0] : reftype <: storagetype), zt)

  ;; test.spectec:2618.1-2622.24
  rule `array.init_data`{C : context, x : idx, y : idx, zt : storagetype, numtype : numtype, vectype : vectype}:
    `%|-%:%`(C, `ARRAY.INIT_DATA`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([REF_valtype(?(NULL_null), _IDX_heaptype(x)) I32_valtype I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], ARRAY_comptype(`%%`_fieldtype(?(MUT_mut), zt)))
    -- if (($unpack(zt) = (numtype : numtype <: valtype)) \/ ($unpack(zt) = (vectype : vectype <: valtype)))
    -- if (C.DATAS_context[y!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2627.1-2629.26
  rule `extern.convert_any`{C : context, `null_1?` : null?, `null_2?` : null?}:
    `%|-%:%`(C, `EXTERN.CONVERT_ANY`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, ANY_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, EXTERN_heaptype)])))
    -- if (null_1?{null_1 <- `null_1?`} = null_2?{null_2 <- `null_2?`})

  ;; test.spectec:2631.1-2633.26
  rule `any.convert_extern`{C : context, `null_1?` : null?, `null_2?` : null?}:
    `%|-%:%`(C, `ANY.CONVERT_EXTERN`_instr, `%->_%%`_instrtype(`%`_resulttype([REF_valtype(null_1?{null_1 <- `null_1?`}, EXTERN_heaptype)]), [], `%`_resulttype([REF_valtype(null_2?{null_2 <- `null_2?`}, ANY_heaptype)])))
    -- if (null_1?{null_1 <- `null_1?`} = null_2?{null_2 <- `null_2?`})

  ;; test.spectec:2638.1-2640.28
  rule `local.get`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `LOCAL.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(SET_init, t))

  ;; test.spectec:2642.1-2644.29
  rule `local.set`{C : context, x : idx, t : valtype, init : init}:
    `%|-%:%`(C, `LOCAL.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(init, t))

  ;; test.spectec:2646.1-2648.29
  rule `local.tee`{C : context, x : idx, t : valtype, init : init}:
    `%|-%:%`(C, `LOCAL.TEE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [x], `%`_resulttype([t])))
    -- if (C.LOCALS_context[x!`%`_idx.0] = `%%`_localtype(init, t))

  ;; test.spectec:2653.1-2655.30
  rule `global.get`{C : context, x : idx, t : valtype, `mut?` : mut?}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([t])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(mut?{mut <- `mut?`}, t))

  ;; test.spectec:2657.1-2659.29
  rule `global.set`{C : context, x : idx, t : valtype}:
    `%|-%:%`(C, `GLOBAL.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([t]), [], `%`_resulttype([])))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(MUT_mut), t))

  ;; test.spectec:2664.1-2666.32
  rule `table.get`{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.GET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(rt : reftype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2668.1-2670.32
  rule `table.set`{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.SET`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (rt : reftype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2672.1-2674.32
  rule `table.size`{C : context, x : idx, at : addrtype, lim : limits, rt : reftype}:
    `%|-%:%`(C, `TABLE.SIZE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2676.1-2678.32
  rule `table.grow`{C : context, x : idx, rt : reftype, at : addrtype, lim : limits}:
    `%|-%:%`(C, `TABLE.GROW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(rt : reftype <: valtype) (at : addrtype <: valtype)]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2680.1-2682.32
  rule `table.fill`{C : context, x : idx, at : addrtype, rt : reftype, lim : limits}:
    `%|-%:%`(C, `TABLE.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (rt : reftype <: valtype) (at : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt))

  ;; test.spectec:2684.1-2688.36
  rule `table.copy`{C : context, x_1 : idx, x_2 : idx, at_1 : addrtype, at_2 : addrtype, lim_1 : limits, rt_1 : reftype, lim_2 : limits, rt_2 : reftype}:
    `%|-%:%`(C, `TABLE.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([(at_1 : addrtype <: valtype) (at_2 : addrtype <: valtype) ($minat(at_1, at_2) : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x_1!`%`_idx.0] = `%%%`_tabletype(at_1, lim_1, rt_1))
    -- if (C.TABLES_context[x_2!`%`_idx.0] = `%%%`_tabletype(at_2, lim_2, rt_2))
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

  ;; test.spectec:2690.1-2694.36
  rule `table.init`{C : context, x : idx, y : idx, at : addrtype, lim : limits, rt_1 : reftype, rt_2 : reftype}:
    `%|-%:%`(C, `TABLE.INIT`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt_1))
    -- if (C.ELEMS_context[y!`%`_idx.0] = rt_2)
    -- Reftype_sub: `%|-%<:%`(C, rt_2, rt_1)

  ;; test.spectec:2696.1-2698.24
  rule `elem.drop`{C : context, x : idx, rt : reftype}:
    `%|-%:%`(C, `ELEM.DROP`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- if (C.ELEMS_context[x!`%`_idx.0] = rt)

  ;; test.spectec:2711.1-2713.32
  rule `memory.size`{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.SIZE`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:2715.1-2717.32
  rule `memory.grow`{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.GROW`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(at : addrtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:2719.1-2721.32
  rule `memory.fill`{C : context, x : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.FILL`_instr(x), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) I32_valtype (at : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))

  ;; test.spectec:2723.1-2726.38
  rule `memory.copy`{C : context, x_1 : idx, x_2 : idx, at_1 : addrtype, at_2 : addrtype, lim_1 : limits, lim_2 : limits}:
    `%|-%:%`(C, `MEMORY.COPY`_instr(x_1, x_2), `%->_%%`_instrtype(`%`_resulttype([(at_1 : addrtype <: valtype) (at_2 : addrtype <: valtype) ($minat(at_1, at_2) : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x_1!`%`_idx.0] = `%%PAGE`_memtype(at_1, lim_1))
    -- if (C.MEMS_context[x_2!`%`_idx.0] = `%%PAGE`_memtype(at_2, lim_2))

  ;; test.spectec:2728.1-2731.24
  rule `memory.init`{C : context, x : idx, y : idx, at : addrtype, lim : limits}:
    `%|-%:%`(C, `MEMORY.INIT`_instr(x, y), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) I32_valtype I32_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- if (C.DATAS_context[y!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2733.1-2735.24
  rule `data.drop`{C : context, x : idx}:
    `%|-%:%`(C, `DATA.DROP`_instr(x), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))
    -- if (C.DATAS_context[x!`%`_idx.0] = OK_datatype)

  ;; test.spectec:2746.1-2749.44
  rule `load-val`{C : context, nt : numtype, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, LOAD_instr(nt, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(nt : numtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $size(nt))

  ;; test.spectec:2751.1-2754.36
  rule `load-pack`{C : context, Inn : Inn, M : M, sx : sx, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, LOAD_instr((Inn : addrtype <: numtype), ?(`%_%`_loadop_(`%`_sz(M), sx)), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([(Inn : addrtype <: valtype)])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, M)

  ;; test.spectec:2765.1-2768.44
  rule `store-val`{C : context, nt : numtype, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, STORE_instr(nt, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (nt : numtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $size(nt))

  ;; test.spectec:2770.1-2773.36
  rule `store-pack`{C : context, Inn : Inn, M : M, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, STORE_instr((Inn : addrtype <: numtype), ?(`%`_storeop_(`%`_sz(M))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) (Inn : addrtype <: valtype)]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, M)

  ;; test.spectec:2775.1-2778.47
  rule `vload-val`{C : context, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $vsize(V128_vectype))

  ;; test.spectec:2780.1-2783.41
  rule `vload-pack`{C : context, M : M, N : N, sx : sx, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(`SHAPE%X%_%`_vloadop_(`%`_sz(M), N, sx)), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, (M * N))

  ;; test.spectec:2785.1-2788.36
  rule `vload-splat`{C : context, N : N, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(SPLAT_vloadop_(`%`_sz(N))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)

  ;; test.spectec:2790.1-2793.36
  rule `vload-zero`{C : context, N : N, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_instr(V128_vectype, ?(ZERO_vloadop_(`%`_sz(N))), x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)

  ;; test.spectec:2795.1-2799.21
  rule vload_lane{C : context, N : N, x : idx, memarg : memarg, i : laneidx, at : addrtype, lim : limits}:
    `%|-%:%`(C, VLOAD_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- if ((i!`%`_laneidx.0 : nat <:> rat) < ((128 : nat <:> rat) / (N : nat <:> rat)))

  ;; test.spectec:2801.1-2804.47
  rule vstore{C : context, x : idx, memarg : memarg, at : addrtype, lim : limits}:
    `%|-%:%`(C, VSTORE_instr(V128_vectype, x, memarg), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) V128_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, $vsize(V128_vectype))

  ;; test.spectec:2806.1-2810.21
  rule vstore_lane{C : context, N : N, x : idx, memarg : memarg, i : laneidx, at : addrtype, lim : limits}:
    `%|-%:%`(C, VSTORE_LANE_instr(V128_vectype, `%`_sz(N), x, memarg, i), `%->_%%`_instrtype(`%`_resulttype([(at : addrtype <: valtype) V128_valtype]), [], `%`_resulttype([])))
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Memarg_ok: `|-%:%->%`(memarg, at, N)
    -- if ((i!`%`_laneidx.0 : nat <:> rat) < ((128 : nat <:> rat) / (N : nat <:> rat)))

  ;; test.spectec:2815.1-2816.33
  rule const{C : context, nt : numtype, c_nt : num_(nt)}:
    `%|-%:%`(C, CONST_instr(nt, c_nt), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([(nt : numtype <: valtype)])))

  ;; test.spectec:2818.1-2819.34
  rule unop{C : context, nt : numtype, unop_nt : unop_(nt)}:
    `%|-%:%`(C, UNOP_instr(nt, unop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype)]), [], `%`_resulttype([(nt : numtype <: valtype)])))

  ;; test.spectec:2821.1-2822.39
  rule binop{C : context, nt : numtype, binop_nt : binop_(nt)}:
    `%|-%:%`(C, BINOP_instr(nt, binop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype) (nt : numtype <: valtype)]), [], `%`_resulttype([(nt : numtype <: valtype)])))

  ;; test.spectec:2824.1-2825.39
  rule testop{C : context, nt : numtype, testop_nt : testop_(nt)}:
    `%|-%:%`(C, TESTOP_instr(nt, testop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2827.1-2828.40
  rule relop{C : context, nt : numtype, relop_nt : relop_(nt)}:
    `%|-%:%`(C, RELOP_instr(nt, relop_nt), `%->_%%`_instrtype(`%`_resulttype([(nt : numtype <: valtype) (nt : numtype <: valtype)]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2830.1-2831.44
  rule cvtop{C : context, nt_1 : numtype, nt_2 : numtype, cvtop : cvtop__(nt_2, nt_1)}:
    `%|-%:%`(C, CVTOP_instr(nt_1, nt_2, cvtop), `%->_%%`_instrtype(`%`_resulttype([(nt_2 : numtype <: valtype)]), [], `%`_resulttype([(nt_1 : numtype <: valtype)])))

  ;; test.spectec:2836.1-2837.35
  rule vconst{C : context, c : vec_(V128_Vnn)}:
    `%|-%:%`(C, VCONST_instr(V128_vectype, c), `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2839.1-2840.41
  rule vvunop{C : context, vvunop : vvunop}:
    `%|-%:%`(C, VVUNOP_instr(V128_vectype, vvunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2842.1-2843.48
  rule vvbinop{C : context, vvbinop : vvbinop}:
    `%|-%:%`(C, VVBINOP_instr(V128_vectype, vvbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2845.1-2846.55
  rule vvternop{C : context, vvternop : vvternop}:
    `%|-%:%`(C, VVTERNOP_instr(V128_vectype, vvternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2848.1-2849.44
  rule vvtestop{C : context, vvtestop : vvtestop}:
    `%|-%:%`(C, VVTESTOP_instr(V128_vectype, vvtestop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2851.1-2852.37
  rule vunop{C : context, sh : shape, vunop : vunop_(sh)}:
    `%|-%:%`(C, VUNOP_instr(sh, vunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2854.1-2855.44
  rule vbinop{C : context, sh : shape, vbinop : vbinop_(sh)}:
    `%|-%:%`(C, VBINOP_instr(sh, vbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2857.1-2858.51
  rule vternop{C : context, sh : shape, vternop : vternop_(sh)}:
    `%|-%:%`(C, VTERNOP_instr(sh, vternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2860.1-2861.40
  rule vtestop{C : context, sh : shape, vtestop : vtestop_(sh)}:
    `%|-%:%`(C, VTESTOP_instr(sh, vtestop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2863.1-2864.44
  rule vrelop{C : context, sh : shape, vrelop : vrelop_(sh)}:
    `%|-%:%`(C, VRELOP_instr(sh, vrelop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2866.1-2867.47
  rule vshiftop{C : context, sh : ishape, vshiftop : vshiftop_(sh)}:
    `%|-%:%`(C, VSHIFTOP_instr(sh, vshiftop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype I32_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2869.1-2870.33
  rule vbitmask{C : context, sh : ishape}:
    `%|-%:%`(C, VBITMASK_instr(sh), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([I32_valtype])))

  ;; test.spectec:2872.1-2873.50
  rule vswizzlop{C : context, sh : bshape, vswizzlop : vswizzlop_(sh)}:
    `%|-%:%`(C, VSWIZZLOP_instr(sh, vswizzlop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2875.1-2877.29
  rule vshuffle{C : context, sh : bshape, `i*` : laneidx*}:
    `%|-%:%`(C, VSHUFFLE_instr(sh, i*{i <- `i*`}), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))
    -- (if (i!`%`_laneidx.0 < (2 * $dim(sh!`%`_bshape.0)!`%`_dim.0)))*{i <- `i*`}

  ;; test.spectec:2879.1-2880.44
  rule vsplat{C : context, sh : shape}:
    `%|-%:%`(C, VSPLAT_instr(sh), `%->_%%`_instrtype(`%`_resulttype([($unpackshape(sh) : numtype <: valtype)]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2882.1-2884.21
  rule vextract_lane{C : context, sh : shape, `sx?` : sx?, i : laneidx}:
    `%|-%:%`(C, VEXTRACT_LANE_instr(sh, sx?{sx <- `sx?`}, i), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([($unpackshape(sh) : numtype <: valtype)])))
    -- if (i!`%`_laneidx.0 < $dim(sh)!`%`_dim.0)

  ;; test.spectec:2886.1-2888.21
  rule vreplace_lane{C : context, sh : shape, i : laneidx}:
    `%|-%:%`(C, VREPLACE_LANE_instr(sh, i), `%->_%%`_instrtype(`%`_resulttype([V128_valtype ($unpackshape(sh) : numtype <: valtype)]), [], `%`_resulttype([V128_valtype])))
    -- if (i!`%`_laneidx.0 < $dim(sh)!`%`_dim.0)

  ;; test.spectec:2890.1-2891.50
  rule vextunop{C : context, sh_1 : ishape, sh_2 : ishape, vextunop : vextunop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTUNOP_instr(sh_1, sh_2, vextunop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2893.1-2894.57
  rule vextbinop{C : context, sh_1 : ishape, sh_2 : ishape, vextbinop : vextbinop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTBINOP_instr(sh_1, sh_2, vextbinop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2896.1-2897.64
  rule vextternop{C : context, sh_1 : ishape, sh_2 : ishape, vextternop : vextternop__(sh_2, sh_1)}:
    `%|-%:%`(C, VEXTTERNOP_instr(sh_1, sh_2, vextternop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2899.1-2900.48
  rule vnarrow{C : context, sh_1 : ishape, sh_2 : ishape, sx : sx}:
    `%|-%:%`(C, VNARROW_instr(sh_1, sh_2, sx), `%->_%%`_instrtype(`%`_resulttype([V128_valtype V128_valtype]), [], `%`_resulttype([V128_valtype])))

  ;; test.spectec:2902.1-2903.46
  rule vcvtop{C : context, sh_1 : shape, sh_2 : shape, vcvtop : vcvtop__(sh_2, sh_1)}:
    `%|-%:%`(C, VCVTOP_instr(sh_1, sh_2, vcvtop), `%->_%%`_instrtype(`%`_resulttype([V128_valtype]), [], `%`_resulttype([V128_valtype])))

;; test.spectec:2301.1-2301.96
relation Instrs_ok: `%|-%:%`(context, instr*, instrtype)
  ;; test.spectec:2908.1-2909.24
  rule empty{C : context}:
    `%|-%:%`(C, [], `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype([])))

  ;; test.spectec:2912.1-2916.82
  rule seq{C : context, instr_1 : instr, `instr_2*` : instr*, `t_1*` : valtype*, `x_1*` : idx*, `x_2*` : idx*, `t_3*` : valtype*, `t_2*` : valtype*, `init*` : init*, `t*` : valtype*}:
    `%|-%:%`(C, [instr_1] ++ instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`} ++ x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x_1*{x_1 <- `x_1*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (if (C.LOCALS_context[x_1!`%`_idx.0] = `%%`_localtype(init, t)))*{init <- `init*`, t <- `t*`, x_1 <- `x_1*`}
    -- Instrs_ok: `%|-%:%`($with_locals(C, x_1*{x_1 <- `x_1*`}, `%%`_localtype(SET_init, t)*{t <- `t*`}), instr_2*{instr_2 <- `instr_2*`}, `%->_%%`_instrtype(`%`_resulttype(t_2*{t_2 <- `t_2*`}), x_2*{x_2 <- `x_2*`}, `%`_resulttype(t_3*{t_3 <- `t_3*`})))

  ;; test.spectec:2918.1-2922.33
  rule sub{C : context, `instr*` : instr*, it' : instrtype, it : instrtype}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, it')
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, it)
    -- Instrtype_sub: `%|-%<:%`(C, it, it')
    -- Instrtype_ok: `%|-%:OK`(C, it')

  ;; test.spectec:2925.1-2928.33
  rule frame{C : context, `instr*` : instr*, `t*` : valtype*, `t_1*` : valtype*, `x*` : idx*, `t_2*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t*{t <- `t*`} ++ t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t*{t <- `t*`} ++ t_2*{t_2 <- `t_2*`})))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), x*{x <- `x*`}, `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- Resulttype_ok: `%|-%:OK`(C, `%`_resulttype(t*{t <- `t*`}))
}

;; test.spectec:2302.1-2302.94
relation Expr_ok: `%|-%:%`(context, expr, resulttype)
  ;; test.spectec:2933.1-2935.40
  rule _{C : context, `instr*` : instr*, `t*` : valtype*}:
    `%|-%:%`(C, instr*{instr <- `instr*`}, `%`_resulttype(t*{t <- `t*`}))
    -- Instrs_ok: `%|-%:%`(C, instr*{instr <- `instr*`}, `%->_%%`_instrtype(`%`_resulttype([]), [], `%`_resulttype(t*{t <- `t*`})))

;; test.spectec:2307.1-2308.75
relation Nondefaultable: `|-%NONDEFAULTABLE`(valtype)
  ;; test.spectec:4452.1-4452.66
  rule _{t : valtype}:
    `|-%NONDEFAULTABLE`(t)
    -- if ($default_(t) = ?())

;; test.spectec:2940.1-2940.104
relation Instr_const: `%|-%CONST`(context, instr)
  ;; test.spectec:2944.1-2945.29
  rule const{C : context, nt : numtype, c_nt : num_(nt)}:
    `%|-%CONST`(C, CONST_instr(nt, c_nt))

  ;; test.spectec:2947.1-2948.30
  rule vconst{C : context, vt : vectype, c_vt : vec_(vt)}:
    `%|-%CONST`(C, VCONST_instr(vt, c_vt))

  ;; test.spectec:2950.1-2951.27
  rule `ref.null`{C : context, ht : heaptype}:
    `%|-%CONST`(C, `REF.NULL`_instr(ht))

  ;; test.spectec:2953.1-2954.23
  rule `ref.i31`{C : context}:
    `%|-%CONST`(C, `REF.I31`_instr)

  ;; test.spectec:2956.1-2957.26
  rule `ref.func`{C : context, x : idx}:
    `%|-%CONST`(C, `REF.FUNC`_instr(x))

  ;; test.spectec:2959.1-2960.28
  rule `struct.new`{C : context, x : idx}:
    `%|-%CONST`(C, `STRUCT.NEW`_instr(x))

  ;; test.spectec:2962.1-2963.36
  rule `struct.new_default`{C : context, x : idx}:
    `%|-%CONST`(C, `STRUCT.NEW_DEFAULT`_instr(x))

  ;; test.spectec:2965.1-2966.27
  rule `array.new`{C : context, x : idx}:
    `%|-%CONST`(C, `ARRAY.NEW`_instr(x))

  ;; test.spectec:2968.1-2969.35
  rule `array.new_default`{C : context, x : idx}:
    `%|-%CONST`(C, `ARRAY.NEW_DEFAULT`_instr(x))

  ;; test.spectec:2971.1-2972.35
  rule `array.new_fixed`{C : context, x : idx, n : n}:
    `%|-%CONST`(C, `ARRAY.NEW_FIXED`_instr(x, `%`_u32(n)))

  ;; test.spectec:2974.1-2975.34
  rule `any.convert_extern`{C : context}:
    `%|-%CONST`(C, `ANY.CONVERT_EXTERN`_instr)

  ;; test.spectec:2977.1-2978.34
  rule `extern.convert_any`{C : context}:
    `%|-%CONST`(C, `EXTERN.CONVERT_ANY`_instr)

  ;; test.spectec:2980.1-2982.25
  rule `global.get`{C : context, x : idx, t : valtype}:
    `%|-%CONST`(C, `GLOBAL.GET`_instr(x))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = `%%`_globaltype(?(), t))

  ;; test.spectec:2984.1-2987.29
  rule binop{C : context, Inn : Inn, binop : binop_((Inn : addrtype <: numtype))}:
    `%|-%CONST`(C, BINOP_instr((Inn : addrtype <: numtype), binop))
    -- if (Inn <- [I32_Inn I64_Inn])
    -- if (binop <- [ADD_binop_ SUB_binop_ MUL_binop_])

;; test.spectec:2941.1-2941.103
relation Expr_const: `%|-%CONST`(context, expr)
  ;; test.spectec:2990.1-2991.38
  rule _{C : context, `instr*` : instr*}:
    `%|-%CONST`(C, instr*{instr <- `instr*`})
    -- (Instr_const: `%|-%CONST`(C, instr))*{instr <- `instr*`}

;; test.spectec:2942.1-2942.105
relation Expr_ok_const: `%|-%:%CONST`(context, expr, valtype)
  ;; test.spectec:2994.1-2997.33
  rule _{C : context, expr : expr, t : valtype}:
    `%|-%:%CONST`(C, expr, t)
    -- Expr_ok: `%|-%:%`(C, expr, `%`_resulttype([t]))
    -- Expr_const: `%|-%CONST`(C, expr)

;; test.spectec:3012.1-3012.97
relation Type_ok: `%|-%:%`(context, type, deftype*)
  ;; test.spectec:3025.1-3029.53
  rule _{C : context, rectype : rectype, `dt*` : deftype*, x : idx}:
    `%|-%:%`(C, TYPE_type(rectype), dt*{dt <- `dt*`})
    -- if (x!`%`_idx.0 = |C.TYPES_context|)
    -- if (dt*{dt <- `dt*`} = $rolldt(x, rectype))
    -- Rectype_ok: `%|-%:%`(C +++ {TYPES dt*{dt <- `dt*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rectype, OK_oktypeidx(x))

;; test.spectec:3013.1-3013.96
relation Tag_ok: `%|-%:%`(context, tag, tagtype)
  ;; test.spectec:3031.1-3033.35
  rule _{C : context, tagtype : tagtype}:
    `%|-%:%`(C, TAG_tag(tagtype), $clos_tagtype(C, tagtype))
    -- Tagtype_ok: `%|-%:OK`(C, tagtype)

;; test.spectec:3014.1-3014.99
relation Global_ok: `%|-%:%`(context, global, globaltype)
  ;; test.spectec:3035.1-3039.40
  rule _{C : context, globaltype : globaltype, expr : expr, t : valtype}:
    `%|-%:%`(C, GLOBAL_global(globaltype, expr), globaltype)
    -- Globaltype_ok: `%|-%:OK`(C, globaltype)
    -- if (globaltype = `%%`_globaltype(MUT_mut?{}, t))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, t)

;; test.spectec:3015.1-3015.96
relation Mem_ok: `%|-%:%`(context, mem, memtype)
  ;; test.spectec:3041.1-3043.35
  rule _{C : context, memtype : memtype}:
    `%|-%:%`(C, MEMORY_mem(memtype), memtype)
    -- Memtype_ok: `%|-%:OK`(C, memtype)

;; test.spectec:3016.1-3016.98
relation Table_ok: `%|-%:%`(context, table, tabletype)
  ;; test.spectec:3045.1-3049.41
  rule _{C : context, tabletype : tabletype, expr : expr, at : addrtype, lim : limits, rt : reftype}:
    `%|-%:%`(C, TABLE_table(tabletype, expr), tabletype)
    -- Tabletype_ok: `%|-%:OK`(C, tabletype)
    -- if (tabletype = `%%%`_tabletype(at, lim, rt))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (rt : reftype <: valtype))

;; test.spectec:3023.1-3023.98
relation Local_ok: `%|-%:%`(context, local, localtype)
  ;; test.spectec:3051.1-3053.35
  rule set{C : context, t : valtype}:
    `%|-%:%`(C, LOCAL_local(t), `%%`_localtype(SET_init, t))
    -- Defaultable: `|-%DEFAULTABLE`(t)

  ;; test.spectec:3055.1-3057.41
  rule unset{C : context, t : valtype}:
    `%|-%:%`(C, LOCAL_local(t), `%%`_localtype(UNSET_init, t))
    -- Nondefaultable: `|-%NONDEFAULTABLE`(t)

;; test.spectec:3017.1-3017.97
relation Func_ok: `%|-%:%`(context, func, deftype)
  ;; test.spectec:3059.1-3064.89
  rule _{C : context, x : idx, `local*` : local*, expr : expr, `t_1*` : valtype*, `t_2*` : valtype*, `lct*` : localtype*}:
    `%|-%:%`(C, FUNC_func(x, local*{local <- `local*`}, expr), C.TYPES_context[x!`%`_idx.0])
    -- Expand: `%~~%`(C.TYPES_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype(t_1*{t_1 <- `t_1*`}), `%`_resulttype(t_2*{t_2 <- `t_2*`})))
    -- (Local_ok: `%|-%:%`(C, local, lct))*{lct <- `lct*`, local <- `local*`}
    -- Expr_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS `%%`_localtype(SET_init, t_1)*{t_1 <- `t_1*`} ++ lct*{lct <- `lct*`}, LABELS [`%`_resulttype(t_2*{t_2 <- `t_2*`})], RETURN ?(`%`_resulttype(t_2*{t_2 <- `t_2*`})), REFS [], RECS []}, expr, `%`_resulttype(t_2*{t_2 <- `t_2*`}))

;; test.spectec:3020.1-3020.118
relation Datamode_ok: `%|-%:%`(context, datamode, datatype)
  ;; test.spectec:3076.1-3077.20
  rule passive{C : context}:
    `%|-%:%`(C, PASSIVE_datamode, OK_datatype)

  ;; test.spectec:3079.1-3082.41
  rule active{C : context, x : idx, expr : expr, at : addrtype, lim : limits}:
    `%|-%:%`(C, ACTIVE_datamode(x, expr), OK_datatype)
    -- if (C.MEMS_context[x!`%`_idx.0] = `%%PAGE`_memtype(at, lim))
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (at : addrtype <: valtype))

;; test.spectec:3018.1-3018.115
relation Data_ok: `%|-%:%`(context, data, datatype)
  ;; test.spectec:3066.1-3068.37
  rule _{C : context, `b*` : byte*, datamode : datamode}:
    `%|-%:%`(C, DATA_data(b*{b <- `b*`}, datamode), OK_datatype)
    -- Datamode_ok: `%|-%:%`(C, datamode, OK_datatype)

;; test.spectec:3021.1-3021.101
relation Elemmode_ok: `%|-%:%`(context, elemmode, elemtype)
  ;; test.spectec:3084.1-3085.20
  rule passive{C : context, rt : reftype}:
    `%|-%:%`(C, PASSIVE_elemmode, rt)

  ;; test.spectec:3087.1-3088.20
  rule declare{C : context, rt : reftype}:
    `%|-%:%`(C, DECLARE_elemmode, rt)

  ;; test.spectec:3090.1-3094.41
  rule active{C : context, x : idx, expr : expr, rt : reftype, at : addrtype, lim : limits, rt' : reftype}:
    `%|-%:%`(C, ACTIVE_elemmode(x, expr), rt)
    -- if (C.TABLES_context[x!`%`_idx.0] = `%%%`_tabletype(at, lim, rt'))
    -- Reftype_sub: `%|-%<:%`(C, rt, rt')
    -- Expr_ok_const: `%|-%:%CONST`(C, expr, (at : addrtype <: valtype))

;; test.spectec:3019.1-3019.97
relation Elem_ok: `%|-%:%`(context, elem, elemtype)
  ;; test.spectec:3070.1-3074.43
  rule _{C : context, elemtype : elemtype, `expr*` : expr*, elemmode : elemmode}:
    `%|-%:%`(C, ELEM_elem(elemtype, expr*{expr <- `expr*`}, elemmode), elemtype)
    -- Reftype_ok: `%|-%:OK`(C, elemtype)
    -- (Expr_ok_const: `%|-%:%CONST`(C, expr, (elemtype : reftype <: valtype)))*{expr <- `expr*`}
    -- Elemmode_ok: `%|-%:%`(C, elemmode, elemtype)

;; test.spectec:3022.1-3022.98
relation Start_ok: `%|-%:OK`(context, start)
  ;; test.spectec:3096.1-3098.43
  rule _{C : context, x : idx}:
    `%|-%:OK`(C, START_start(x))
    -- Expand: `%~~%`(C.FUNCS_context[x!`%`_idx.0], `FUNC%->%`_comptype(`%`_resulttype([]), `%`_resulttype([])))

;; test.spectec:3103.1-3103.105
relation Import_ok: `%|-%:%`(context, import, externtype)
  ;; test.spectec:3107.1-3109.33
  rule _{C : context, name_1 : name, name_2 : name, xt : externtype}:
    `%|-%:%`(C, IMPORT_import(name_1, name_2, xt), $clos_externtype(C, xt))
    -- Externtype_ok: `%|-%:OK`(C, xt)

;; test.spectec:3105.1-3105.108
relation Externidx_ok: `%|-%:%`(context, externidx, externtype)
  ;; test.spectec:3116.1-3118.23
  rule tag{C : context, x : idx, jt : tagtype}:
    `%|-%:%`(C, TAG_externidx(x), TAG_externtype(jt))
    -- if (C.TAGS_context[x!`%`_idx.0] = jt)

  ;; test.spectec:3120.1-3122.26
  rule global{C : context, x : idx, gt : globaltype}:
    `%|-%:%`(C, GLOBAL_externidx(x), GLOBAL_externtype(gt))
    -- if (C.GLOBALS_context[x!`%`_idx.0] = gt)

  ;; test.spectec:3124.1-3126.23
  rule mem{C : context, x : idx, mt : memtype}:
    `%|-%:%`(C, MEM_externidx(x), MEM_externtype(mt))
    -- if (C.MEMS_context[x!`%`_idx.0] = mt)

  ;; test.spectec:3128.1-3130.25
  rule table{C : context, x : idx, tt : tabletype}:
    `%|-%:%`(C, TABLE_externidx(x), TABLE_externtype(tt))
    -- if (C.TABLES_context[x!`%`_idx.0] = tt)

  ;; test.spectec:3132.1-3134.24
  rule func{C : context, x : idx, dt : deftype}:
    `%|-%:%`(C, FUNC_externidx(x), FUNC_externtype((dt : deftype <: typeuse)))
    -- if (C.FUNCS_context[x!`%`_idx.0] = dt)

;; test.spectec:3104.1-3104.105
relation Export_ok: `%|-%:%%`(context, export, name, externtype)
  ;; test.spectec:3111.1-3113.39
  rule _{C : context, name : name, externidx : externidx, xt : externtype}:
    `%|-%:%%`(C, EXPORT_export(name, externidx), name, xt)
    -- Externidx_ok: `%|-%:%`(C, externidx, xt)

;; test.spectec:3141.1-3141.100
rec {

;; test.spectec:3141.1-3141.100
relation Globals_ok: `%|-%:%`(context, global*, globaltype*)
  ;; test.spectec:3186.1-3187.17
  rule empty{C : context}:
    `%|-%:%`(C, [], [])

  ;; test.spectec:3189.1-3192.54
  rule cons{C : context, global_1 : global, `global*` : global*, gt_1 : globaltype, `gt*` : globaltype*}:
    `%|-%:%`(C, [global_1] ++ global*{global <- `global*`}, [gt_1] ++ gt*{gt <- `gt*`})
    -- Global_ok: `%|-%:%`(C, global_1, gt_1)
    -- Globals_ok: `%|-%:%`(C +++ {TYPES [], TAGS [], GLOBALS [gt_1], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, global*{global <- `global*`}, gt*{gt <- `gt*`})
}

;; test.spectec:3140.1-3140.98
rec {

;; test.spectec:3140.1-3140.98
relation Types_ok: `%|-%:%`(context, type*, deftype*)
  ;; test.spectec:3178.1-3179.17
  rule empty{C : context}:
    `%|-%:%`(C, [], [])

  ;; test.spectec:3181.1-3184.49
  rule cons{C : context, type_1 : type, `type*` : type*, `dt_1*` : deftype*, `dt*` : deftype*}:
    `%|-%:%`(C, [type_1] ++ type*{type <- `type*`}, dt_1*{dt_1 <- `dt_1*`} ++ dt*{dt <- `dt*`})
    -- Type_ok: `%|-%:%`(C, type_1, dt_1*{dt_1 <- `dt_1*`})
    -- Types_ok: `%|-%:%`(C +++ {TYPES dt_1*{dt_1 <- `dt_1*`}, TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, type*{type <- `type*`}, dt*{dt <- `dt*`})
}

;; test.spectec:3144.1-3144.59
syntax nonfuncs = 
  | `%%%%%%`(`global*` : global*, `mem*` : mem*, `table*` : table*, `elem*` : elem*, `start?` : start?, `export*` : export*)

;; test.spectec:3145.1-3145.93
def $funcidx_nonfuncs(nonfuncs : nonfuncs) : funcidx*
  ;; test.spectec:3146.1-3147.87
  def $funcidx_nonfuncs{`global*` : global*, `mem*` : mem*, `table*` : table*, `elem*` : elem*, `start?` : start?, `export*` : export*}(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`})) = $funcidx_module(MODULE_module(`%`_list([]), `%`_list([]), `%`_list([]), `%`_list(global*{global <- `global*`}), `%`_list(mem*{mem <- `mem*`}), `%`_list(table*{table <- `table*`}), `%`_list([]), `%`_list([]), `%`_list(elem*{elem <- `elem*`}), start?{start <- `start?`}, `%`_list(export*{export <- `export*`})))

;; test.spectec:3139.1-3139.99
relation Module_ok: `|-%:%`(module, moduletype)
  ;; test.spectec:3149.1-3175.32
  rule _{`type*` : type*, `import*` : import*, `tag*` : tag*, `global*` : global*, `mem*` : mem*, `table*` : table*, `func*` : func*, `data*` : data*, `elem*` : elem*, `start?` : start?, `export*` : export*, C : context, `xt_I*` : externtype*, `xt_E*` : externtype*, `dt'*` : deftype*, C' : context, `jt*` : tagtype*, `gt*` : globaltype*, `mt*` : memtype*, `tt*` : tabletype*, `dt*` : deftype*, `ok*` : datatype*, `rt*` : reftype*, `nm*` : name*, `jt_I*` : tagtype*, `mt_I*` : memtype*, `tt_I*` : tabletype*, `gt_I*` : globaltype*, `dt_I*` : deftype*, `x*` : idx*}:
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
    -- if $disjoint_(syntax name, nm*{nm <- `nm*`})
    -- if (C = C' +++ {TYPES [], TAGS jt_I*{jt_I <- `jt_I*`} ++ jt*{jt <- `jt*`}, GLOBALS gt*{gt <- `gt*`}, MEMS mt_I*{mt_I <- `mt_I*`} ++ mt*{mt <- `mt*`}, TABLES tt_I*{tt_I <- `tt_I*`} ++ tt*{tt <- `tt*`}, FUNCS [], DATAS ok*{ok <- `ok*`}, ELEMS rt*{rt <- `rt*`}, LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []})
    -- if (C' = {TYPES dt'*{dt' <- `dt'*`}, TAGS [], GLOBALS gt_I*{gt_I <- `gt_I*`}, MEMS [], TABLES [], FUNCS dt_I*{dt_I <- `dt_I*`} ++ dt*{dt <- `dt*`}, DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS x*{x <- `x*`}, RECS []})
    -- if (x*{x <- `x*`} = $funcidx_nonfuncs(`%%%%%%`_nonfuncs(global*{global <- `global*`}, mem*{mem <- `mem*`}, table*{table <- `table*`}, elem*{elem <- `elem*`}, start?{start <- `start?`}, export*{export <- `export*`})))
    -- if (jt_I*{jt_I <- `jt_I*`} = $tagsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (gt_I*{gt_I <- `gt_I*`} = $globalsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (mt_I*{mt_I <- `mt_I*`} = $memsxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (tt_I*{tt_I <- `tt_I*`} = $tablesxt(xt_I*{xt_I <- `xt_I*`}))
    -- if (dt_I*{dt_I <- `dt_I*`} = $funcsxt(xt_I*{xt_I <- `xt_I*`}))

;; test.spectec:3205.1-3205.24
syntax relaxed2 = 
  | `%`(i : nat)
    -- if ((i = 0) \/ (i = 1))

;; test.spectec:3206.1-3206.32
syntax relaxed4 = 
  | `%`(i : nat)
    -- if ((((i = 0) \/ (i = 1)) \/ (i = 2)) \/ (i = 3))

;; test.spectec:3208.1-3208.83
def $relaxed2(relaxed2 : relaxed2, syntax X, X : X, X : X) : X
  ;; test.spectec:3211.1-3211.63
  def $relaxed2{i : relaxed2, syntax X, X_1 : X, X_2 : X}(i, syntax X, X_1, X_2) = (if $ND then [X_1 X_2][i!`%`_relaxed2.0] else [X_1 X_2][0])

;; test.spectec:3209.1-3209.89
def $relaxed4(relaxed4 : relaxed4, syntax X, X : X, X : X, X : X, X : X) : X
  ;; test.spectec:3214.1-3214.81
  def $relaxed4{i : relaxed4, syntax X, X_1 : X, X_2 : X, X_3 : X, X_4 : X}(i, syntax X, X_1, X_2, X_3, X_4) = (if $ND then [X_1 X_2 X_3 X_4][i!`%`_relaxed4.0] else [X_1 X_2 X_3 X_4][0])

;; test.spectec:3218.1-3218.43
def $R_fmadd : relaxed2

;; test.spectec:3219.1-3219.43
def $R_fmin : relaxed4

;; test.spectec:3220.1-3220.43
def $R_fmax : relaxed4

;; test.spectec:3221.1-3221.43
def $R_idot : relaxed2

;; test.spectec:3222.1-3222.43
def $R_iq15mulr : relaxed2

;; test.spectec:3223.1-3223.43
def $R_trunc_u : relaxed4

;; test.spectec:3224.1-3224.43
def $R_trunc_s : relaxed2

;; test.spectec:3225.1-3225.43
def $R_swizzle : relaxed2

;; test.spectec:3226.1-3226.43
def $R_laneselect : relaxed2

;; test.spectec:3241.1-3241.41
def $s33_to_u32(s33 : s33) : u32

;; test.spectec:3246.1-3246.107
def $ibits_(N : N, iN : iN(N)) : bit*

;; test.spectec:3247.1-3247.107
def $fbits_(N : N, fN : fN(N)) : bit*

;; test.spectec:3248.1-3248.109
def $ibytes_(N : N, iN : iN(N)) : byte*

;; test.spectec:3249.1-3249.109
def $fbytes_(N : N, fN : fN(N)) : byte*

;; test.spectec:3250.1-3250.104
def $nbytes_(numtype : numtype, num_ : num_(numtype)) : byte*

;; test.spectec:3251.1-3251.104
def $vbytes_(vectype : vectype, vec_ : vec_(vectype)) : byte*

;; test.spectec:3252.1-3252.104
def $zbytes_(storagetype : storagetype, lit_ : lit_(storagetype)) : byte*

;; test.spectec:3253.1-3253.104
def $cbytes_(Cnn : Cnn, lit_ : lit_((Cnn : Cnn <: storagetype))) : byte*

;; test.spectec:3255.1-3255.91
def $inv_ibits_(N : N, bit*) : iN(N)

;; test.spectec:3256.1-3256.91
def $inv_fbits_(N : N, bit*) : fN(N)

;; test.spectec:3257.1-3257.92
def $inv_ibytes_(N : N, byte*) : iN(N)

;; test.spectec:3258.1-3258.92
def $inv_fbytes_(N : N, byte*) : fN(N)

;; test.spectec:3259.1-3259.87
def $inv_nbytes_(numtype : numtype, byte*) : num_(numtype)

;; test.spectec:3260.1-3260.87
def $inv_vbytes_(vectype : vectype, byte*) : vec_(vectype)

;; test.spectec:3261.1-3261.92
def $inv_zbytes_(storagetype : storagetype, byte*) : lit_(storagetype)

;; test.spectec:3262.1-3262.87
def $inv_cbytes_(Cnn : Cnn, byte*) : lit_((Cnn : Cnn <: storagetype))

;; test.spectec:3286.1-3286.54
def $signed_(N : N, nat : nat) : int
  ;; test.spectec:3287.1-3287.54
  def $signed_{N : N, i : nat}(N, i) = (i : nat <:> int)
    -- if (i < (2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)))
  ;; test.spectec:3288.1-3288.61
  def $signed_{N : N, i : nat}(N, i) = ((i : nat <:> int) - ((2 ^ N) : nat <:> int))
    -- if (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) <= i) /\ (i < (2 ^ N)))

;; test.spectec:3290.1-3290.68
def $inv_signed_(N : N, int : int) : nat
  ;; test.spectec:3291.1-3291.62
  def $inv_signed_{N : N, i : int}(N, i) = (i : int <:> nat)
    -- if (((0 : nat <:> int) <= i) /\ (i < ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)))
  ;; test.spectec:3292.1-3292.63
  def $inv_signed_{N : N, i : int}(N, i) = ((i + ((2 ^ N) : nat <:> int)) : int <:> nat)
    -- if ((- ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) <= i) /\ (i < (0 : nat <:> int)))

;; test.spectec:3295.1-3295.60
def $sx(storagetype : storagetype) : sx?
  ;; test.spectec:3296.1-3296.25
  def $sx{consttype : consttype}((consttype : consttype <: storagetype)) = ?()
  ;; test.spectec:3297.1-3297.22
  def $sx{packtype : packtype}((packtype : packtype <: storagetype)) = ?(S_sx)

;; test.spectec:3302.1-3302.51
def $zero(lanetype : lanetype) : lane_(lanetype)
  ;; test.spectec:3303.1-3303.19
  def $zero{Jnn : Jnn}((Jnn : Jnn <: lanetype)) = `%`_lane_(0)
  ;; test.spectec:3304.1-3304.36
  def $zero{Fnn : Fnn}((Fnn : Fnn <: lanetype)) = $fzero($size((Fnn : Fnn <: numtype)))

;; test.spectec:3306.1-3306.22
def $bool(bool : bool) : nat
  ;; test.spectec:3307.1-3307.21
  def $bool(false) = 0
  ;; test.spectec:3308.1-3308.20
  def $bool(true) = 1

;; test.spectec:3310.1-3310.23
def $truncz(rat : rat) : int

;; test.spectec:3314.1-3314.59
def $ceilz(rat : rat) : int

;; test.spectec:3321.1-3321.61
def $sat_u_(N : N, int : int) : nat
  ;; test.spectec:3322.1-3322.48
  def $sat_u_{N : N, i : int}(N, i) = (if (i < (0 : nat <:> int)) then 0 else (if (i > (((2 ^ N) : nat <:> int) - (1 : nat <:> int))) then ((((2 ^ N) : nat <:> int) - (1 : nat <:> int)) : int <:> nat) else (i : int <:> nat)))

;; test.spectec:3326.1-3326.61
def $sat_s_(N : N, int : int) : int
  ;; test.spectec:3327.1-3327.58
  def $sat_s_{N : N, i : int}(N, i) = (if (i < - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int)) then - ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) else (if (i > (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int))) then (((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> int) - (1 : nat <:> int)) else i))

;; test.spectec:3334.1-3334.29
def $ineg_(N : N, iN : iN(N)) : iN(N)
  ;; test.spectec:3381.1-3381.42
  def $ineg_{N : N, i_1 : iN(N)}(N, i_1) = `%`_iN((((((2 ^ N) : nat <:> int) - (i_1!`%`_iN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:3335.1-3335.29
def $iabs_(N : N, iN : iN(N)) : iN(N)
  ;; test.spectec:3383.1-3383.65
  def $iabs_{N : N, i_1 : iN(N)}(N, i_1) = (if ($signed_(N, i_1!`%`_iN.0) >= (0 : nat <:> int)) then i_1 else $ineg_(N, i_1))

;; test.spectec:3336.1-3336.29
def $iclz_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3337.1-3337.29
def $ictz_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3338.1-3338.32
def $ipopcnt_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3339.1-3339.86
def $iextend_(N : N, M : M, sx : sx, iN : iN(N)) : iN(N)
  ;; test.spectec:3395.1-3395.39
  def $iextend_{N : N, M : M, i : iN(N)}(N, M, U_sx, i) = `%`_iN((i!`%`_iN.0 \ (2 ^ M)))
  ;; test.spectec:3396.1-3396.69
  def $iextend_{N : N, M : M, i : iN(N)}(N, M, S_sx, i) = `%`_iN($inv_signed_(N, $signed_(M, (i!`%`_iN.0 \ (2 ^ M)))))

;; test.spectec:3341.1-3341.36
def $iadd_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3399.1-3399.47
  def $iadd_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((i_1!`%`_iN.0 + i_2!`%`_iN.0) \ (2 ^ N)))

;; test.spectec:3342.1-3342.36
def $isub_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3401.1-3401.53
  def $isub_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((((((2 ^ N) + i_1!`%`_iN.0) : nat <:> int) - (i_2!`%`_iN.0 : nat <:> int)) \ ((2 ^ N) : nat <:> int)) : int <:> nat))

;; test.spectec:3343.1-3343.36
def $imul_(N : N, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3403.1-3403.47
  def $imul_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_iN(((i_1!`%`_iN.0 * i_2!`%`_iN.0) \ (2 ^ N)))

;; test.spectec:3344.1-3344.83
def $idiv_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)?
  ;; test.spectec:3405.1-3405.33
  def $idiv_{N : N, i_1 : iN(N)}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3406.1-3406.51
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = ?(`%`_iN(($truncz(((i_1!`%`_iN.0 : nat <:> rat) / (i_2!`%`_iN.0 : nat <:> rat))) : int <:> nat)))
  ;; test.spectec:3407.1-3407.33
  def $idiv_{N : N, i_1 : iN(N)}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3408.1-3408.96
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = ?()
    -- if ((($signed_(N, i_1!`%`_iN.0) : int <:> rat) / ($signed_(N, i_2!`%`_iN.0) : int <:> rat)) = ((2 ^ (((N : nat <:> int) - (1 : nat <:> int)) : int <:> nat)) : nat <:> rat))
  ;; test.spectec:3409.1-3409.94
  def $idiv_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, $truncz((($signed_(N, i_1!`%`_iN.0) : int <:> rat) / ($signed_(N, i_2!`%`_iN.0) : int <:> rat))))))

;; test.spectec:3345.1-3345.83
def $irem_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)?
  ;; test.spectec:3411.1-3411.33
  def $irem_{N : N, i_1 : iN(N)}(N, U_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3412.1-3412.66
  def $irem_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = ?(`%`_iN((((i_1!`%`_iN.0 : nat <:> int) - ((i_2!`%`_iN.0 * ($truncz(((i_1!`%`_iN.0 : nat <:> rat) / (i_2!`%`_iN.0 : nat <:> rat))) : int <:> nat)) : nat <:> int)) : int <:> nat)))
  ;; test.spectec:3413.1-3413.33
  def $irem_{N : N, i_1 : iN(N)}(N, S_sx, i_1, `%`_iN(0)) = ?()
  ;; test.spectec:3414.1-3415.84
  def $irem_{N : N, i_1 : iN(N), i_2 : iN(N), j_1 : int, j_2 : int}(N, S_sx, i_1, i_2) = ?(`%`_iN($inv_signed_(N, (j_1 - (j_2 * $truncz(((j_1 : int <:> rat) / (j_2 : int <:> rat))))))))
    -- if ((j_1 = $signed_(N, i_1!`%`_iN.0)) /\ (j_2 = $signed_(N, i_2!`%`_iN.0)))

;; test.spectec:3346.1-3346.83
def $imin_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3417.1-3417.51
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_iN.0 <= i_2!`%`_iN.0)
  ;; test.spectec:3418.1-3418.50
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_iN.0 > i_2!`%`_iN.0)
  ;; test.spectec:3419.1-3419.77
  def $imin_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = (if ($signed_(N, i_1!`%`_iN.0) <= $signed_(N, i_2!`%`_iN.0)) then i_1 else i_2)

;; test.spectec:3347.1-3347.83
def $imax_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3422.1-3422.51
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_1
    -- if (i_1!`%`_iN.0 >= i_2!`%`_iN.0)
  ;; test.spectec:3423.1-3423.50
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = i_2
    -- if (i_1!`%`_iN.0 < i_2!`%`_iN.0)
  ;; test.spectec:3424.1-3424.77
  def $imax_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = (if ($signed_(N, i_1!`%`_iN.0) >= $signed_(N, i_2!`%`_iN.0)) then i_1 else i_2)

;; test.spectec:3348.1-3348.88
def $iadd_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3427.1-3427.58
  def $iadd_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_iN.0 + i_2!`%`_iN.0) : nat <:> int)))
  ;; test.spectec:3428.1-3428.101
  def $iadd_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_iN.0) + $signed_(N, i_2!`%`_iN.0)))))

;; test.spectec:3349.1-3349.88
def $isub_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)
  ;; test.spectec:3430.1-3430.58
  def $isub_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_iN($sat_u_(N, ((i_1!`%`_iN.0 : nat <:> int) - (i_2!`%`_iN.0 : nat <:> int))))
  ;; test.spectec:3431.1-3431.101
  def $isub_sat_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_iN($inv_signed_(N, $sat_s_(N, ($signed_(N, i_1!`%`_iN.0) - $signed_(N, i_2!`%`_iN.0)))))

;; test.spectec:3350.1-3350.92
def $iq15mulr_sat_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3351.1-3351.101
def $irelaxed_q15mulr_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)*

;; test.spectec:3352.1-3352.84
def $iavgr_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3354.1-3354.29
def $inot_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3355.1-3355.29
def $irev_(N : N, iN : iN(N)) : iN(N)

;; test.spectec:3356.1-3356.36
def $iand_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3357.1-3357.39
def $iandnot_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3358.1-3358.35
def $ior_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3359.1-3359.36
def $ixor_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3360.1-3360.34
def $ishl_(N : N, iN : iN(N), u32 : u32) : iN(N)

;; test.spectec:3361.1-3361.76
def $ishr_(N : N, sx : sx, iN : iN(N), u32 : u32) : iN(N)

;; test.spectec:3362.1-3362.37
def $irotl_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3363.1-3363.37
def $irotr_(N : N, iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3365.1-3365.49
def $ibitselect_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)

;; test.spectec:3366.1-3366.59
def $irelaxed_laneselect_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)*

;; test.spectec:3368.1-3368.27
def $ieqz_(N : N, iN : iN(N)) : u32
  ;; test.spectec:3452.1-3452.36
  def $ieqz_{N : N, i_1 : iN(N)}(N, i_1) = `%`_u32($bool((i_1!`%`_iN.0 = 0)))

;; test.spectec:3369.1-3369.27
def $inez_(N : N, iN : iN(N)) : u32
  ;; test.spectec:3454.1-3454.38
  def $inez_{N : N, i_1 : iN(N)}(N, i_1) = `%`_u32($bool((i_1!`%`_iN.0 =/= 0)))

;; test.spectec:3371.1-3371.33
def $ieq_(N : N, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3457.1-3457.42
  def $ieq_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_u32($bool((i_1 = i_2)))

;; test.spectec:3372.1-3372.33
def $ine_(N : N, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3459.1-3459.44
  def $ine_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, i_1, i_2) = `%`_u32($bool((i_1 =/= i_2)))

;; test.spectec:3373.1-3373.75
def $ilt_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3461.1-3461.45
  def $ilt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 < i_2!`%`_iN.0)))
  ;; test.spectec:3462.1-3462.71
  def $ilt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) < $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3374.1-3374.75
def $igt_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3464.1-3464.45
  def $igt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 > i_2!`%`_iN.0)))
  ;; test.spectec:3465.1-3465.71
  def $igt_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) > $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3375.1-3375.75
def $ile_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3467.1-3467.46
  def $ile_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 <= i_2!`%`_iN.0)))
  ;; test.spectec:3468.1-3468.72
  def $ile_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) <= $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3376.1-3376.75
def $ige_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32
  ;; test.spectec:3470.1-3470.46
  def $ige_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, U_sx, i_1, i_2) = `%`_u32($bool((i_1!`%`_iN.0 >= i_2!`%`_iN.0)))
  ;; test.spectec:3471.1-3471.72
  def $ige_{N : N, i_1 : iN(N), i_2 : iN(N)}(N, S_sx, i_1, i_2) = `%`_u32($bool(($signed_(N, i_1!`%`_iN.0) >= $signed_(N, i_2!`%`_iN.0))))

;; test.spectec:3476.1-3476.30
def $fabs_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3477.1-3477.30
def $fneg_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3478.1-3478.31
def $fsqrt_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3479.1-3479.31
def $fceil_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3480.1-3480.32
def $ffloor_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3481.1-3481.32
def $ftrunc_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3482.1-3482.34
def $fnearest_(N : N, fN : fN(N)) : fN(N)*

;; test.spectec:3484.1-3484.37
def $fadd_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3485.1-3485.37
def $fsub_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3486.1-3486.37
def $fmul_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3487.1-3487.37
def $fdiv_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3488.1-3488.37
def $fmin_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3489.1-3489.37
def $fmax_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3490.1-3490.38
def $fpmin_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3491.1-3491.38
def $fpmax_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3492.1-3492.82
def $frelaxed_min_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3493.1-3493.82
def $frelaxed_max_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3494.1-3494.42
def $fcopysign_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3496.1-3496.33
def $feq_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3497.1-3497.33
def $fne_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3498.1-3498.33
def $flt_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3499.1-3499.33
def $fgt_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3500.1-3500.33
def $fle_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3501.1-3501.33
def $fge_(N : N, fN : fN(N), fN : fN(N)) : u32

;; test.spectec:3503.1-3503.91
def $frelaxed_madd_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3504.1-3504.92
def $frelaxed_nmadd_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*

;; test.spectec:3542.1-3542.33
def $wrap__(M : M, N : N, iN : iN(M)) : iN(N)

;; test.spectec:3543.1-3543.90
def $extend__(M : M, N : N, sx : sx, iN : iN(M)) : iN(N)

;; test.spectec:3544.1-3544.89
def $trunc__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; test.spectec:3545.1-3545.94
def $trunc_sat__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; test.spectec:3546.1-3546.98
def $relaxed_trunc__(M : M, N : N, sx : sx, fN : fN(M)) : iN(N)?

;; test.spectec:3547.1-3547.36
def $demote__(M : M, N : N, fN : fN(M)) : fN(N)*

;; test.spectec:3548.1-3548.37
def $promote__(M : M, N : N, fN : fN(M)) : fN(N)*

;; test.spectec:3549.1-3549.91
def $convert__(M : M, N : N, sx : sx, iN : iN(M)) : fN(N)

;; test.spectec:3550.1-3550.88
def $narrow__(M : M, N : N, sx : sx, iN : iN(M)) : iN(N)

;; test.spectec:3552.1-3552.76
def $reinterpret__(numtype_1 : numtype, numtype_2 : numtype, num_ : num_(numtype_1)) : num_(numtype_2)

;; test.spectec:3572.1-3573.49
def $lpacknum_(lanetype : lanetype, num_ : num_($lunpack(lanetype))) : lane_(lanetype)
  ;; test.spectec:3577.1-3577.31
  def $lpacknum_{numtype : numtype, c : num_($lunpack((numtype : numtype <: lanetype)))}((numtype : numtype <: lanetype), c) = c
  ;; test.spectec:3578.1-3578.86
  def $lpacknum_{packtype : packtype, c : num_($lunpack((packtype : packtype <: lanetype)))}((packtype : packtype <: lanetype), c) = $wrap__($size($lunpack((packtype : packtype <: lanetype))), $psize(packtype), c)

;; test.spectec:3574.1-3575.49
def $cpacknum_(storagetype : storagetype, lit_ : lit_(($cunpack(storagetype) : consttype <: storagetype))) : lit_(storagetype)
  ;; test.spectec:3580.1-3580.33
  def $cpacknum_{consttype : consttype, c : lit_(($cunpack((consttype : consttype <: storagetype)) : consttype <: storagetype))}((consttype : consttype <: storagetype), c) = c
  ;; test.spectec:3581.1-3581.86
  def $cpacknum_{packtype : packtype, c : lit_(($cunpack((packtype : packtype <: storagetype)) : consttype <: storagetype))}((packtype : packtype <: storagetype), c) = $wrap__($size($lunpack((packtype : packtype <: lanetype))), $psize(packtype), c)

;; test.spectec:3584.1-3585.53
def $lunpacknum_(lanetype : lanetype, lane_ : lane_(lanetype)) : num_($lunpack(lanetype))
  ;; test.spectec:3589.1-3589.33
  def $lunpacknum_{numtype : numtype, c : lane_((numtype : numtype <: lanetype))}((numtype : numtype <: lanetype), c) = c
  ;; test.spectec:3590.1-3590.93
  def $lunpacknum_{packtype : packtype, c : lane_((packtype : packtype <: lanetype))}((packtype : packtype <: lanetype), c) = $extend__($psize(packtype), $size($lunpack((packtype : packtype <: lanetype))), U_sx, c)

;; test.spectec:3586.1-3587.53
def $cunpacknum_(storagetype : storagetype, lit_ : lit_(storagetype)) : lit_(($cunpack(storagetype) : consttype <: storagetype))
  ;; test.spectec:3592.1-3592.35
  def $cunpacknum_{consttype : consttype, c : lit_((consttype : consttype <: storagetype))}((consttype : consttype <: storagetype), c) = c
  ;; test.spectec:3593.1-3593.93
  def $cunpacknum_{packtype : packtype, c : lit_((packtype : packtype <: storagetype))}((packtype : packtype <: storagetype), c) = $extend__($psize(packtype), $size($lunpack((packtype : packtype <: lanetype))), U_sx, c)

;; test.spectec:3598.1-3599.28
def $unop_(numtype : numtype, unop_ : unop_(numtype), num_ : num_(numtype)) : num_(numtype)*
  ;; test.spectec:3609.1-3609.50
  def $unop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), CLZ_unop_, i) = [$iclz_($sizenn((Inn : addrtype <: numtype)), i)]
  ;; test.spectec:3610.1-3610.50
  def $unop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), CTZ_unop_, i) = [$ictz_($sizenn((Inn : addrtype <: numtype)), i)]
  ;; test.spectec:3611.1-3611.56
  def $unop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), POPCNT_unop_, i) = [$ipopcnt_($sizenn((Inn : addrtype <: numtype)), i)]
  ;; test.spectec:3612.1-3612.64
  def $unop_{Inn : Inn, M : M, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), EXTEND_unop_(`%`_sz(M)), i) = [$iextend_($sizenn((Inn : addrtype <: numtype)), M, S_sx, i)]
  ;; test.spectec:3614.1-3614.50
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), ABS_unop_, f) = $fabs_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3615.1-3615.50
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NEG_unop_, f) = $fneg_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3616.1-3616.52
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), SQRT_unop_, f) = $fsqrt_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3617.1-3617.52
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), CEIL_unop_, f) = $fceil_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3618.1-3618.54
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), FLOOR_unop_, f) = $ffloor_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3619.1-3619.54
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), TRUNC_unop_, f) = $ftrunc_($sizenn((Fnn : Fnn <: numtype)), f)
  ;; test.spectec:3620.1-3620.58
  def $unop_{Fnn : Fnn, f : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NEAREST_unop_, f) = $fnearest_($sizenn((Fnn : Fnn <: numtype)), f)

;; test.spectec:3600.1-3601.32
def $binop_(numtype : numtype, binop_ : binop_(numtype), num_ : num_(numtype), num_ : num_(numtype)) : num_(numtype)*
  ;; test.spectec:3622.1-3622.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), ADD_binop_, i_1, i_2) = [$iadd_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3623.1-3623.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), SUB_binop_, i_1, i_2) = [$isub_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3624.1-3624.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), MUL_binop_, i_1, i_2) = [$imul_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3625.1-3625.72
  def $binop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), DIV_binop_(sx), i_1, i_2) = lift($idiv_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2))
  ;; test.spectec:3626.1-3626.72
  def $binop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), REM_binop_(sx), i_1, i_2) = lift($irem_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2))
  ;; test.spectec:3627.1-3627.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), AND_binop_, i_1, i_2) = [$iand_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3628.1-3628.63
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), OR_binop_, i_1, i_2) = [$ior_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3629.1-3629.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), XOR_binop_, i_1, i_2) = [$ixor_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3630.1-3630.65
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), SHL_binop_, i_1, i_2) = [$ishl_($sizenn((Inn : addrtype <: numtype)), i_1, `%`_u32(i_2!`%`_num_.0))]
  ;; test.spectec:3631.1-3631.72
  def $binop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), SHR_binop_(sx), i_1, i_2) = [$ishr_($sizenn((Inn : addrtype <: numtype)), sx, i_1, `%`_u32(i_2!`%`_num_.0))]
  ;; test.spectec:3632.1-3632.67
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), ROTL_binop_, i_1, i_2) = [$irotl_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3633.1-3633.67
  def $binop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), ROTR_binop_, i_1, i_2) = [$irotr_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)]
  ;; test.spectec:3635.1-3635.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), ADD_binop_, f_1, f_2) = $fadd_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3636.1-3636.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), SUB_binop_, f_1, f_2) = $fsub_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3637.1-3637.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MUL_binop_, f_1, f_2) = $fmul_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3638.1-3638.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), DIV_binop_, f_1, f_2) = $fdiv_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3639.1-3639.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MIN_binop_, f_1, f_2) = $fmin_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3640.1-3640.65
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), MAX_binop_, f_1, f_2) = $fmax_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3641.1-3641.75
  def $binop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), COPYSIGN_binop_, f_1, f_2) = $fcopysign_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)

;; test.spectec:3602.1-3603.28
def $testop_(numtype : numtype, testop_ : testop_(numtype), num_ : num_(numtype)) : u32
  ;; test.spectec:3643.1-3643.52
  def $testop_{Inn : Inn, i : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), EQZ_testop_, i) = $ieqz_($sizenn((Inn : addrtype <: numtype)), i)

;; test.spectec:3604.1-3605.32
def $relop_(numtype : numtype, relop_ : relop_(numtype), num_ : num_(numtype), num_ : num_(numtype)) : u32
  ;; test.spectec:3645.1-3645.63
  def $relop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), EQ_relop_, i_1, i_2) = $ieq_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)
  ;; test.spectec:3646.1-3646.63
  def $relop_{Inn : Inn, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), NE_relop_, i_1, i_2) = $ine_($sizenn((Inn : addrtype <: numtype)), i_1, i_2)
  ;; test.spectec:3647.1-3647.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), LT_relop_(sx), i_1, i_2) = $ilt_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3648.1-3648.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), GT_relop_(sx), i_1, i_2) = $igt_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3649.1-3649.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), LE_relop_(sx), i_1, i_2) = $ile_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3650.1-3650.70
  def $relop_{Inn : Inn, sx : sx, i_1 : num_((Inn : addrtype <: numtype)), i_2 : num_((Inn : addrtype <: numtype))}((Inn : addrtype <: numtype), GE_relop_(sx), i_1, i_2) = $ige_($sizenn((Inn : addrtype <: numtype)), sx, i_1, i_2)
  ;; test.spectec:3652.1-3652.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), EQ_relop_, f_1, f_2) = $feq_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3653.1-3653.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), NE_relop_, f_1, f_2) = $fne_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3654.1-3654.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), LT_relop_, f_1, f_2) = $flt_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3655.1-3655.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), GT_relop_, f_1, f_2) = $fgt_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3656.1-3656.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), LE_relop_, f_1, f_2) = $fle_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)
  ;; test.spectec:3657.1-3657.63
  def $relop_{Fnn : Fnn, f_1 : num_((Fnn : Fnn <: numtype)), f_2 : num_((Fnn : Fnn <: numtype))}((Fnn : Fnn <: numtype), GE_relop_, f_1, f_2) = $fge_($sizenn((Fnn : Fnn <: numtype)), f_1, f_2)

;; test.spectec:3606.1-3607.32
def $cvtop__(numtype_1 : numtype, numtype_2 : numtype, cvtop__ : cvtop__(numtype_1, numtype_2), num_ : num_(numtype_1)) : num_(numtype_2)*
  ;; test.spectec:3659.1-3660.55
  def $cvtop__{Inn_1 : Inn, Inn_2 : Inn, sx : sx, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Inn_2 : addrtype <: numtype), EXTEND_cvtop__(sx), i_1) = [$extend__($sizenn1((Inn_1 : addrtype <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), sx, i_1)]
  ;; test.spectec:3661.1-3662.49
  def $cvtop__{Inn_1 : Inn, Inn_2 : Inn, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Inn_2 : addrtype <: numtype), WRAP_cvtop__, i_1) = [$wrap__($sizenn1((Inn_1 : addrtype <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), i_1)]
  ;; test.spectec:3663.1-3664.54
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, sx : sx, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), TRUNC_cvtop__(sx), f_1) = lift($trunc__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), sx, f_1))
  ;; test.spectec:3665.1-3666.58
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, sx : sx, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), TRUNC_SAT_cvtop__(sx), f_1) = lift($trunc_sat__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Inn_2 : addrtype <: numtype)), sx, f_1))
  ;; test.spectec:3667.1-3668.56
  def $cvtop__{Inn_1 : Inn, Fnn_2 : Fnn, sx : sx, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype), CONVERT_cvtop__(sx), i_1) = [$convert__($sizenn1((Inn_1 : addrtype <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), sx, i_1)]
  ;; test.spectec:3669.1-3670.52
  def $cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype), PROMOTE_cvtop__, f_1) = $promote__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), f_1)
  ;; test.spectec:3671.1-3672.51
  def $cvtop__{Fnn_1 : Fnn, Fnn_2 : Fnn, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Fnn_2 : Fnn <: numtype), DEMOTE_cvtop__, f_1) = $demote__($sizenn1((Fnn_1 : Fnn <: numtype)), $sizenn2((Fnn_2 : Fnn <: numtype)), f_1)
  ;; test.spectec:3673.1-3674.70
  def $cvtop__{Inn_1 : Inn, Fnn_2 : Fnn, i_1 : num_((Inn_1 : addrtype <: numtype))}((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype), REINTERPRET_cvtop__, i_1) = [$reinterpret__((Inn_1 : addrtype <: numtype), (Fnn_2 : Fnn <: numtype), i_1)]
    -- if ($size((Inn_1 : addrtype <: numtype)) = $size((Fnn_2 : Fnn <: numtype)))
  ;; test.spectec:3675.1-3676.70
  def $cvtop__{Fnn_1 : Fnn, Inn_2 : Inn, f_1 : num_((Fnn_1 : Fnn <: numtype))}((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), REINTERPRET_cvtop__, f_1) = [$reinterpret__((Fnn_1 : Fnn <: numtype), (Inn_2 : addrtype <: numtype), f_1)]
    -- if ($size((Fnn_1 : Fnn <: numtype)) = $size((Inn_2 : addrtype <: numtype)))

;; test.spectec:3694.1-3694.84
def $lanes_(shape : shape, vec_ : vec_(V128_Vnn)) : lane_($lanetype(shape))*

;; test.spectec:3696.1-3697.37
def $inv_lanes_(shape : shape, lane_($lanetype(shape))*) : vec_(V128_Vnn)

;; test.spectec:3703.1-3703.66
def $zeroop(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2)) : zero?
  ;; test.spectec:3704.1-3704.60
  def $zeroop{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx)) = ?()
  ;; test.spectec:3705.1-3705.62
  def $zeroop{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx)) = ?()
  ;; test.spectec:3706.1-3706.66
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`})) = zero?{zero <- `zero?`}
  ;; test.spectec:3707.1-3707.70
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), RELAXED_TRUNC_vcvtop__(sx, zero?{zero <- `zero?`})) = zero?{zero <- `zero?`}
  ;; test.spectec:3708.1-3708.58
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, zero : zero}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(zero)) = ?(zero)
  ;; test.spectec:3709.1-3709.57
  def $zeroop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__) = ?()

;; test.spectec:3711.1-3711.66
def $halfop(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2)) : half?
  ;; test.spectec:3712.1-3712.61
  def $halfop{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx)) = ?(half)
  ;; test.spectec:3713.1-3713.64
  def $halfop{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx)) = half?{half <- `half?`}
  ;; test.spectec:3714.1-3714.64
  def $halfop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`})) = ?()
  ;; test.spectec:3715.1-3715.68
  def $halfop{Fnn_1 : Fnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, `zero?` : zero?}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), RELAXED_TRUNC_vcvtop__(sx, zero?{zero <- `zero?`})) = ?()
  ;; test.spectec:3716.1-3716.57
  def $halfop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, zero : zero}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(zero)) = ?()
  ;; test.spectec:3717.1-3717.57
  def $halfop{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__) = ?(LOW_half)

;; test.spectec:3719.1-3719.32
def $half(half : half, nat : nat, nat : nat) : nat
  ;; test.spectec:3720.1-3720.25
  def $half{i : nat, j : nat}(LOW_half, i, j) = i
  ;; test.spectec:3721.1-3721.26
  def $half{i : nat, j : nat}(HIGH_half, i, j) = j

;; test.spectec:3724.1-3724.46
def $iswizzle_lane_(N : N, iN(N)*, iN : iN(N)) : iN(N)
  ;; test.spectec:3727.1-3727.62
  def $iswizzle_lane_{N : N, `c*` : iN(N)*, i : iN(N)}(N, c*{c <- `c*`}, i) = (if (i!`%`_iN.0 < |c*{c <- `c*`}|) then c*{c <- `c*`}[i!`%`_iN.0] else `%`_iN(0))

;; test.spectec:3725.1-3725.54
def $irelaxed_swizzle_lane_(N : N, iN(N)*, iN : iN(N)) : iN(N)
  ;; test.spectec:3730.1-3730.62
  def $irelaxed_swizzle_lane_{N : N, `c*` : iN(N)*, i : iN(N)}(N, c*{c <- `c*`}, i) = (if (i!`%`_iN.0 < |c*{c <- `c*`}|) then c*{c <- `c*`}[i!`%`_iN.0] else (if ($signed_(N, i!`%`_iN.0) < (0 : nat <:> int)) then `%`_iN(0) else $relaxed2($R_swizzle, syntax iN(N), `%`_iN(0), c*{c <- `c*`}[(i!`%`_iN.0 \ |c*{c <- `c*`}|)])))

;; test.spectec:3738.1-3738.87
def $ivunop_(shape : shape, def $f_(N : N, iN : iN(N)) : iN(N), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3761.1-3763.40
  def $ivunop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N)) : iN(N), v_1 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1) = [$inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})]
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1)*{c_1 <- `c_1*`}

;; test.spectec:3739.1-3739.74
def $fvunop_(shape : shape, def $f_(N : N, fN : fN(N)) : fN(N)*, vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3765.1-3767.66
  def $fvunop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N)) : fN(N)*, v_1 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1) = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c**` : lane_((Fnn : Fnn <: lanetype))**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $f_($sizenn((Fnn : Fnn <: numtype)), c_1)*{c_1 <- `c_1*`})

;; test.spectec:3741.1-3741.107
def $ivbinop_(shape : shape, def $f_(N : N, iN : iN(N), iN : iN(N)) : iN(N), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3770.1-3773.45
  def $ivbinop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), iN : iN(N)) : iN(N), v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = [$inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})]
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3742.1-3742.117
def $ivbinopsx_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N), sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3775.1-3778.49
  def $ivbinopsx_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N), sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = [$inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})]
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3743.1-3743.106
def $ivbinopsxnd_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)*, sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3780.1-3783.76
  def $ivbinopsxnd_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : iN(N)*, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c**` : lane_((Jnn : Jnn <: lanetype))**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Jnn : Jnn <: lanetype)), $f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`})

;; test.spectec:3744.1-3744.94
def $fvbinop_(shape : shape, def $f_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3785.1-3788.71
  def $fvbinop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N), fN : fN(N)) : fN(N)*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c**` : lane_((Fnn : Fnn <: lanetype))**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $f_($sizenn((Fnn : Fnn <: numtype)), c_1, c_2)*{c_1 <- `c_1*`, c_2 <- `c_2*`})

;; test.spectec:3746.1-3746.116
def $ivternopnd_(shape : shape, def $f_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3791.1-3795.77
  def $ivternopnd_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), iN : iN(N), iN : iN(N)) : iN(N)*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c_3*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_3*{c_3 <- `c_3*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_3)
    -- let{`c**` : lane_((Jnn : Jnn <: lanetype))**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Jnn : Jnn <: lanetype)), $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, c_2, c_3)*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`})

;; test.spectec:3747.1-3747.114
def $fvternop_(shape : shape, def $f_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3797.1-3801.76
  def $fvternop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N), fN : fN(N), fN : fN(N)) : fN(N)*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2, v_3) = $inv_lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`}
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c_3*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_3*{c_3 <- `c_3*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_3)
    -- let{`c**` : lane_((Fnn : Fnn <: lanetype))**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_((Fnn : Fnn <: lanetype)), $f_($sizenn((Fnn : Fnn <: numtype)), c_1, c_2, c_3)*{c_1 <- `c_1*`, c_2 <- `c_2*`, c_3 <- `c_3*`})

;; test.spectec:3749.1-3749.90
def $ivrelop_(shape : shape, def $f_(N : N, iN : iN(N), iN : iN(N)) : u32, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3804.1-3807.77
  def $ivrelop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), iN : iN(N)) : u32, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, c_2)!`%`_u32.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3750.1-3750.100
def $ivrelopsx_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32, sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3809.1-3812.81
  def $ivrelopsx_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), iN : iN(N)) : u32, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $extend__(1, $lsizenn((Jnn : Jnn <: lanetype)), S_sx, `%`_iN($f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, c_2)!`%`_u32.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`}

;; test.spectec:3751.1-3751.90
def $fvrelop_(shape : shape, def $f_(N : N, fN : fN(N), fN : fN(N)) : u32, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3814.1-3818.36
  def $fvrelop_{Fnn : Fnn, M : M, def $f_(N : N, fN : fN(N), fN : fN(N)) : u32, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), Inn : Inn}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Inn : addrtype <: lanetype), `%`_dim(M)), `%`_lane_(c!`%`_iN.0)*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : iN($sizenn((Fnn : Fnn <: numtype)))*} c*{c <- `c*`} = $extend__(1, $sizenn((Fnn : Fnn <: numtype)), S_sx, `%`_iN($f_($sizenn((Fnn : Fnn <: numtype)), c_1, c_2)!`%`_u32.0))*{c_1 <- `c_1*`, c_2 <- `c_2*`}
    -- if ($isize(Inn) = $fsize(Fnn))

;; test.spectec:3753.1-3753.99
def $ivshiftop_(shape : shape, def $f_(N : N, iN : iN(N), u32 : u32) : iN(N), vec_ : vec_(V128_Vnn), u32 : u32) : vec_(V128_Vnn)
  ;; test.spectec:3821.1-3823.41
  def $ivshiftop_{Jnn : Jnn, M : M, def $f_(N : N, iN : iN(N), u32 : u32) : iN(N), v_1 : vec_(V128_Vnn), i : u32}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, i) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1, i)*{c_1 <- `c_1*`}

;; test.spectec:3754.1-3754.109
def $ivshiftopsx_(shape : shape, def $f_(N : N, sx : sx, iN : iN(N), u32 : u32) : iN(N), sx : sx, vec_ : vec_(V128_Vnn), u32 : u32) : vec_(V128_Vnn)
  ;; test.spectec:3825.1-3827.45
  def $ivshiftopsx_{Jnn : Jnn, M : M, def $f_(N : N, sx : sx, iN : iN(N), u32 : u32) : iN(N), sx : sx, v_1 : vec_(V128_Vnn), i : u32}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, sx, v_1, i) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), sx, c_1, i)*{c_1 <- `c_1*`}

;; test.spectec:3756.1-3756.43
def $ivbitmaskop_(shape : shape, vec_ : vec_(V128_Vnn)) : u32
  ;; test.spectec:3830.1-3832.72
  def $ivbitmaskop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), c : iN(32)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1) = $irev_(32, c)
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- if ($ibits_(32, c) = `%`_bit($ilt_($lsizenn((Jnn : Jnn <: lanetype)), S_sx, c_1, `%`_iN(0))!`%`_u32.0)*{c_1 <- `c_1*`} ++ `%`_bit(0)^(((32 : nat <:> int) - (M : nat <:> int)) : int <:> nat){})

;; test.spectec:3757.1-3757.110
def $ivswizzlop_(shape : shape, def $f_(N : N, iN(N)*, iN : iN(N)) : iN(N), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3835.1-3838.44
  def $ivswizzlop_{Jnn : Jnn, M : M, def $f_(N : N, iN(N)*, iN : iN(N)) : iN(N), v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $f_, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : iN($lsizenn((Jnn : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn((Jnn : Jnn <: lanetype)), c_1*{c_1 <- `c_1*`}, c_2)*{c_2 <- `c_2*`}

;; test.spectec:3758.1-3758.85
def $ivshufflop_(shape : shape, laneidx*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3841.1-3844.34
  def $ivshufflop_{Jnn : Jnn, M : M, `i*` : laneidx*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), i*{i <- `i*`}, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v_2)
    -- let{`c*` : lane_($lanetype(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))))*} c*{c <- `c*`} = c_1*{c_1 <- `c_1*`} ++ c_2*{c_2 <- `c_2*`}[i!`%`_laneidx.0]*{i <- `i*`}

;; test.spectec:3849.1-3850.28
def $vvunop_(vectype : vectype, vvunop : vvunop, vec_ : vec_(vectype)) : vec_(vectype)*
  ;; test.spectec:3890.1-3890.53
  def $vvunop_{Vnn : Vnn, v : vec_(Vnn)}(Vnn, NOT_vvunop, v) = [$inot_($vsizenn(Vnn), v)]

;; test.spectec:3851.1-3852.31
def $vvbinop_(vectype : vectype, vvbinop : vvbinop, vec_ : vec_(vectype), vec_ : vec_(vectype)) : vec_(vectype)*
  ;; test.spectec:3892.1-3892.68
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, AND_vvbinop, v_1, v_2) = [$iand_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3893.1-3893.74
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, ANDNOT_vvbinop, v_1, v_2) = [$iandnot_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3894.1-3894.66
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, OR_vvbinop, v_1, v_2) = [$ior_($vsizenn(Vnn), v_1, v_2)]
  ;; test.spectec:3895.1-3895.68
  def $vvbinop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn)}(Vnn, XOR_vvbinop, v_1, v_2) = [$ixor_($vsizenn(Vnn), v_1, v_2)]

;; test.spectec:3853.1-3854.34
def $vvternop_(vectype : vectype, vvternop : vvternop, vec_ : vec_(vectype), vec_ : vec_(vectype), vec_ : vec_(vectype)) : vec_(vectype)*
  ;; test.spectec:3897.1-3897.91
  def $vvternop_{Vnn : Vnn, v_1 : vec_(Vnn), v_2 : vec_(Vnn), v_3 : vec_(Vnn)}(Vnn, BITSELECT_vvternop, v_1, v_2, v_3) = [$ibitselect_($vsizenn(Vnn), v_1, v_2, v_3)]

;; test.spectec:3856.1-3857.28
def $vunop_(shape : shape, vunop_ : vunop_(shape), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3899.1-3899.60
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), ABS_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fabs_, v)
  ;; test.spectec:3900.1-3900.60
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NEG_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fneg_, v)
  ;; test.spectec:3901.1-3901.62
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), SQRT_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fsqrt_, v)
  ;; test.spectec:3902.1-3902.62
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), CEIL_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fceil_, v)
  ;; test.spectec:3903.1-3903.64
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), FLOOR_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $ffloor_, v)
  ;; test.spectec:3904.1-3904.64
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), TRUNC_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $ftrunc_, v)
  ;; test.spectec:3905.1-3905.68
  def $vunop_{Fnn : Fnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NEAREST_vunop_, v) = $fvunop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fnearest_, v)
  ;; test.spectec:3907.1-3907.60
  def $vunop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ABS_vunop_, v) = $ivunop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iabs_, v)
  ;; test.spectec:3908.1-3908.60
  def $vunop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), NEG_vunop_, v) = $ivunop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ineg_, v)
  ;; test.spectec:3909.1-3909.66
  def $vunop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), POPCNT_vunop_, v) = $ivunop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ipopcnt_, v)

;; test.spectec:3858.1-3859.31
def $vbinop_(shape : shape, vbinop_ : vbinop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3911.1-3911.76
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ADD_vbinop_, v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iadd_, v_1, v_2)
  ;; test.spectec:3912.1-3912.76
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), SUB_vbinop_, v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $isub_, v_1, v_2)
  ;; test.spectec:3913.1-3913.76
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MUL_vbinop_, v_1, v_2) = $ivbinop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $imul_, v_1, v_2)
  ;; test.spectec:3914.1-3914.93
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), ADD_SAT_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iadd_sat_, sx, v_1, v_2)
  ;; test.spectec:3915.1-3915.93
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), SUB_SAT_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $isub_sat_, sx, v_1, v_2)
  ;; test.spectec:3916.1-3916.85
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MIN_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $imin_, sx, v_1, v_2)
  ;; test.spectec:3917.1-3917.85
  def $vbinop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), MAX_vbinop_(sx), v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $imax_, sx, v_1, v_2)
  ;; test.spectec:3918.1-3918.85
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), AVGRU_vbinop_, v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iavgr_, U_sx, v_1, v_2)
  ;; test.spectec:3919.1-3919.99
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), Q15MULR_SATS_vbinop_, v_1, v_2) = $ivbinopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $iq15mulr_sat_, S_sx, v_1, v_2)
  ;; test.spectec:3920.1-3920.109
  def $vbinop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), RELAXED_Q15MULRS_vbinop_, v_1, v_2) = $ivbinopsxnd_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $irelaxed_q15mulr_, S_sx, v_1, v_2)
  ;; test.spectec:3922.1-3922.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), ADD_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fadd_, v_1, v_2)
  ;; test.spectec:3923.1-3923.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), SUB_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fsub_, v_1, v_2)
  ;; test.spectec:3924.1-3924.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MUL_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fmul_, v_1, v_2)
  ;; test.spectec:3925.1-3925.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), DIV_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fdiv_, v_1, v_2)
  ;; test.spectec:3926.1-3926.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MIN_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fmin_, v_1, v_2)
  ;; test.spectec:3927.1-3927.76
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), MAX_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fmax_, v_1, v_2)
  ;; test.spectec:3928.1-3928.78
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), PMIN_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fpmin_, v_1, v_2)
  ;; test.spectec:3929.1-3929.78
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), PMAX_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fpmax_, v_1, v_2)
  ;; test.spectec:3930.1-3930.92
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_MIN_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_min_, v_1, v_2)
  ;; test.spectec:3931.1-3931.92
  def $vbinop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_MAX_vbinop_, v_1, v_2) = $fvbinop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_max_, v_1, v_2)

;; test.spectec:3860.1-3861.34
def $vternop_(shape : shape, vternop_ : vternop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)*
  ;; test.spectec:3933.1-3933.120
  def $vternop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), RELAXED_LANESELECT_vternop_, v_1, v_2, v_3) = $ivternopnd_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $irelaxed_laneselect_, v_1, v_2, v_3)
  ;; test.spectec:3935.1-3935.106
  def $vternop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_MADD_vternop_, v_1, v_2, v_3) = $fvternop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_madd_, v_1, v_2, v_3)
  ;; test.spectec:3936.1-3936.108
  def $vternop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn), v_3 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), RELAXED_NMADD_vternop_, v_1, v_2, v_3) = $fvternop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $frelaxed_nmadd_, v_1, v_2, v_3)

;; test.spectec:3862.1-3863.31
def $vrelop_(shape : shape, vrelop_ : vrelop_(shape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3938.1-3938.74
  def $vrelop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), EQ_vrelop_, v_1, v_2) = $ivrelop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ieq_, v_1, v_2)
  ;; test.spectec:3939.1-3939.74
  def $vrelop_{Jnn : Jnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), NE_vrelop_, v_1, v_2) = $ivrelop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ine_, v_1, v_2)
  ;; test.spectec:3940.1-3940.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), LT_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ilt_, sx, v_1, v_2)
  ;; test.spectec:3941.1-3941.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), GT_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $igt_, sx, v_1, v_2)
  ;; test.spectec:3942.1-3942.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), LE_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ile_, sx, v_1, v_2)
  ;; test.spectec:3943.1-3943.83
  def $vrelop_{Jnn : Jnn, M : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), GE_vrelop_(sx), v_1, v_2) = $ivrelopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ige_, sx, v_1, v_2)
  ;; test.spectec:3945.1-3945.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), EQ_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $feq_, v_1, v_2)
  ;; test.spectec:3946.1-3946.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), NE_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fne_, v_1, v_2)
  ;; test.spectec:3947.1-3947.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), LT_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $flt_, v_1, v_2)
  ;; test.spectec:3948.1-3948.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), GT_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fgt_, v_1, v_2)
  ;; test.spectec:3949.1-3949.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), LE_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fle_, v_1, v_2)
  ;; test.spectec:3950.1-3950.74
  def $vrelop_{Fnn : Fnn, M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), GE_vrelop_, v_1, v_2) = $fvrelop_(`%X%`_shape((Fnn : Fnn <: lanetype), `%`_dim(M)), def $fge_, v_1, v_2)

;; test.spectec:3865.1-3866.41
def $lcvtop__(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2), lane_ : lane_($lanetype(shape_1))) : lane_($lanetype(shape_2))*
  ;; test.spectec:3962.1-3963.69
  def $lcvtop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx, c_1 : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), EXTEND_vcvtop__(half, sx), c_1) = [c]
    -- let{c : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))} c = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, c_1)
  ;; test.spectec:3964.1-3965.70
  def $lcvtop__{Jnn_1 : Jnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, `half?` : half?, sx : sx, c_1 : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), CONVERT_vcvtop__(half?{half <- `half?`}, sx), c_1) = [c]
    -- let{c : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))} c = $convert__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), sx, c_1)
  ;; test.spectec:3966.1-3967.73
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1))))}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : addrtype <: lanetype), `%`_dim(M_2)), TRUNC_SAT_vcvtop__(sx, zero?{zero <- `zero?`}), c_1) = lift(c?{c <- `c?`})
    -- let{`c?` : iN($lsizenn2((Inn_2 : addrtype <: lanetype)))?} c?{c <- `c?`} = $trunc_sat__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Inn_2 : addrtype <: lanetype)), sx, c_1)
  ;; test.spectec:3968.1-3969.77
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Inn_2 : Inn, M_2 : M, sx : sx, `zero?` : zero?, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1))))}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Inn_2 : addrtype <: lanetype), `%`_dim(M_2)), RELAXED_TRUNC_vcvtop__(sx, zero?{zero <- `zero?`}), c_1) = lift(c?{c <- `c?`})
    -- let{`c?` : iN($lsizenn2((Inn_2 : addrtype <: lanetype)))?} c?{c <- `c?`} = $relaxed_trunc__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Inn_2 : addrtype <: lanetype)), sx, c_1)
  ;; test.spectec:3970.1-3971.66
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1))))}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), DEMOTE_vcvtop__(ZERO_zero), c_1) = c*{c <- `c*`}
    -- let{`c*` : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))*} c*{c <- `c*`} = $demote__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), c_1)
  ;; test.spectec:3972.1-3973.67
  def $lcvtop__{Fnn_1 : Fnn, M_1 : M, Fnn_2 : Fnn, M_2 : M, c_1 : lane_($lanetype(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1))))}(`%X%`_shape((Fnn_1 : Fnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Fnn_2 : Fnn <: lanetype), `%`_dim(M_2)), PROMOTELOW_vcvtop__, c_1) = c*{c <- `c*`}
    -- let{`c*` : fN($lsizenn2((Fnn_2 : Fnn <: lanetype)))*} c*{c <- `c*`} = $promote__($lsizenn1((Fnn_1 : Fnn <: lanetype)), $lsizenn2((Fnn_2 : Fnn <: lanetype)), c_1)

;; test.spectec:3867.1-3868.41
def $vcvtop__(shape_1 : shape, shape_2 : shape, vcvtop__ : vcvtop__(shape_1, shape_2), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3975.1-3979.41
  def $vcvtop__{Lnn_1 : Lnn, M : M, Lnn_2 : Lnn, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M))), v_1 : vec_(V128_Vnn), v : vec_(V128_Vnn)}(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, v_1) = v
    -- if (($halfop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()) /\ ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop) = ?()))
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M)), v_1)
    -- let{`c**` : lane_(Lnn_2)**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M)), `%X%`_shape(Lnn_2, `%`_dim(M)), vcvtop, c_1)*{c_1 <- `c_1*`})
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M)), c*{c <- `c*`})*{`c*` <- `c**`})
  ;; test.spectec:3980.1-3984.43
  def $vcvtop__{Lnn_1 : Lnn, M_1 : M, Lnn_2 : Lnn, M_2 : M, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2))), v_1 : vec_(V128_Vnn), v : vec_(V128_Vnn), half : half}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v_1) = v
    -- if ($halfop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(half))
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M_1))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v_1)[$half(half, 0, M_2) : M_2]
    -- let{`c**` : lane_(Lnn_2)**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`})
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})
  ;; test.spectec:3985.1-3989.43
  def $vcvtop__{Lnn_1 : Lnn, M_1 : M, Lnn_2 : Lnn, M_2 : M, vcvtop : vcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2))), v_1 : vec_(V128_Vnn), v : vec_(V128_Vnn)}(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, v_1) = v
    -- if ($zeroop(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop) = ?(ZERO_zero))
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape(Lnn_1, `%`_dim(M_1))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape(Lnn_1, `%`_dim(M_1)), v_1)
    -- let{`c**` : lane_(Lnn_2)**} c*{c <- `c*`}*{`c*` <- `c**`} = $setproduct_(syntax lane_(Lnn_2), $lcvtop__(`%X%`_shape(Lnn_1, `%`_dim(M_1)), `%X%`_shape(Lnn_2, `%`_dim(M_2)), vcvtop, c_1)*{c_1 <- `c_1*`} ++ [$zero(Lnn_2)]^M_1{})
    -- if (v <- $inv_lanes_(`%X%`_shape(Lnn_2, `%`_dim(M_2)), c*{c <- `c*`})*{`c*` <- `c**`})

;; test.spectec:3870.1-3871.34
def $vshiftop_(ishape : ishape, vshiftop_ : vshiftop_(ishape), vec_ : vec_(V128_Vnn), u32 : u32) : vec_(V128_Vnn)
  ;; test.spectec:3952.1-3952.72
  def $vshiftop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn), i : u32}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), SHL_vshiftop_, v, i) = $ivshiftop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ishl_, v, i)
  ;; test.spectec:3953.1-3953.81
  def $vshiftop_{Jnn : Jnn, M : M, sx : sx, v : vec_(V128_Vnn), i : u32}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), SHR_vshiftop_(sx), v, i) = $ivshiftopsx_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), def $ishr_, sx, v, i)

;; test.spectec:3872.1-3873.34
def $vbitmaskop_(ishape : ishape, vec_ : vec_(V128_Vnn)) : u32
  ;; test.spectec:3955.1-3955.57
  def $vbitmaskop_{Jnn : Jnn, M : M, v : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), v) = $ivbitmaskop_(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M)), v)

;; test.spectec:3874.1-3875.31
def $vswizzlop_(bshape : bshape, vswizzlop_ : vswizzlop_(bshape), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3957.1-3957.93
  def $vswizzlop_{M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), SWIZZLE_vswizzlop_, v_1, v_2) = $ivswizzlop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), def $iswizzle_lane_, v_1, v_2)
  ;; test.spectec:3958.1-3958.109
  def $vswizzlop_{M : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), RELAXED_SWIZZLE_vswizzlop_, v_1, v_2) = $ivswizzlop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), def $irelaxed_swizzle_lane_, v_1, v_2)

;; test.spectec:3876.1-3877.40
def $vshufflop_(bshape : bshape, laneidx*, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3960.1-3960.75
  def $vshufflop_{M : M, `i*` : laneidx*, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_bshape(`%X%`_shape(I8_lanetype, `%`_dim(M))), i*{i <- `i*`}, v_1, v_2) = $ivshufflop_(`%X%`_shape(I8_lanetype, `%`_dim(M)), i*{i <- `i*`}, v_1, v_2)

;; test.spectec:3879.1-3880.49
def $vnarrowop__(shape_1 : shape, shape_2 : shape, sx : sx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:3991.1-3996.53
  def $vnarrowop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), sx, v_1, v_2) = v
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_1)
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_2)
    -- let{`c'_1*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*} c'_1*{c'_1 <- `c'_1*`} = $narrow__($lsize((Jnn_1 : Jnn <: lanetype)), $lsize((Jnn_2 : Jnn <: lanetype)), sx, c_1)*{c_1 <- `c_1*`}
    -- let{`c'_2*` : iN($lsize((Jnn_2 : Jnn <: lanetype)))*} c'_2*{c'_2 <- `c'_2*`} = $narrow__($lsize((Jnn_1 : Jnn <: lanetype)), $lsize((Jnn_2 : Jnn <: lanetype)), sx, c_2)*{c_2 <- `c_2*`}
    -- let{v : vec_(V128_Vnn)} v = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), c'_1*{c'_1 <- `c'_1*`} ++ c'_2*{c'_2 <- `c'_2*`})

;; test.spectec:4040.1-4040.76
def $ivadd_pairwise_(N : N, iN(N)*) : iN(N)*
  ;; test.spectec:4041.1-4042.37
  def $ivadd_pairwise_{N : N, `i*` : iN(N)*, `j_1*` : N*, `j_2*` : N*}(N, i*{i <- `i*`}) = $iadd_(N, `%`_iN(j_1), `%`_iN(j_2))*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax N, [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = i!`%`_iN.0*{i <- `i*`})

;; test.spectec:4026.1-4026.93
def $ivextunop__(shape_1 : shape, shape_2 : shape, def $f_(N : N, iN(N)*) : iN(N)*, sx : sx, vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4027.1-4030.42
  def $ivextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, def $f_(N : N, iN(N)*) : iN(N)*, sx : sx, v_1 : vec_(V128_Vnn)}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $f_, sx, v_1) = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_1)
    -- let{`c'_1*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*} c'_1*{c'_1 <- `c'_1*`} = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx, c_1)*{c_1 <- `c_1*`}
    -- let{`c*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn2((Jnn_2 : Jnn <: lanetype)), c'_1*{c'_1 <- `c'_1*`})

;; test.spectec:3882.1-3883.32
def $vextunop__(ishape_1 : ishape, ishape_2 : ishape, vextunop__ : vextunop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4055.1-4056.70
  def $vextunop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, sx : sx, v_1 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTADD_PAIRWISE_vextunop__(sx), v_1) = $ivextunop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivadd_pairwise_, sx, v_1)

;; test.spectec:4047.1-4047.40
def $ivdot_(N : N, iN(N)*, iN(N)*) : iN(N)*
  ;; test.spectec:4048.1-4049.59
  def $ivdot_{N : N, `i_1*` : iN(N)*, `i_2*` : iN(N)*, `j_1*` : iN(N)*, `j_2*` : iN(N)*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $iadd_(N, j_1, j_2)*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax iN(N), [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`})

;; test.spectec:4051.1-4051.76
def $ivdot_sat_(N : N, iN(N)*, iN(N)*) : iN(N)*
  ;; test.spectec:4052.1-4053.59
  def $ivdot_sat_{N : N, `i_1*` : iN(N)*, `i_2*` : iN(N)*, `j_1*` : iN(N)*, `j_2*` : iN(N)*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $iadd_sat_(N, S_sx, j_1, j_2)*{j_1 <- `j_1*`, j_2 <- `j_2*`}
    -- if ($concat_(syntax iN(N), [j_1 j_2]*{j_1 <- `j_1*`, j_2 <- `j_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`})

;; test.spectec:4032.1-4032.136
def $ivextbinop__(shape_1 : shape, shape_2 : shape, def $f_(N : N, iN(N)*, iN(N)*) : iN(N)*, sx : sx, sx : sx, laneidx : laneidx, laneidx : laneidx, vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4033.1-4038.49
  def $ivextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, def $f_(N : N, iN(N)*, iN(N)*) : iN(N)*, sx_1 : sx, sx_2 : sx, i : laneidx, k : laneidx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $f_, sx_1, sx_2, i, k, v_1, v_2) = $inv_lanes_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), c*{c <- `c*`})
    -- let{`c_1*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*} c_1*{c_1 <- `c_1*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_1)[i!`%`_laneidx.0 : k!`%`_laneidx.0]
    -- let{`c_2*` : lane_($lanetype(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))))*} c_2*{c_2 <- `c_2*`} = $lanes_(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), v_2)[i!`%`_laneidx.0 : k!`%`_laneidx.0]
    -- let{`c'_1*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*} c'_1*{c'_1 <- `c'_1*`} = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx_1, c_1)*{c_1 <- `c_1*`}
    -- let{`c'_2*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*} c'_2*{c'_2 <- `c'_2*`} = $extend__($lsizenn1((Jnn_1 : Jnn <: lanetype)), $lsizenn2((Jnn_2 : Jnn <: lanetype)), sx_2, c_2)*{c_2 <- `c_2*`}
    -- let{`c*` : iN($lsizenn2((Jnn_2 : Jnn <: lanetype)))*} c*{c <- `c*`} = $f_($lsizenn2((Jnn_2 : Jnn <: lanetype)), c'_1*{c'_1 <- `c'_1*`}, c'_2*{c'_2 <- `c'_2*`})

;; test.spectec:4044.1-4044.40
def $ivmul_(N : N, iN(N)*, iN(N)*) : iN(N)*
  ;; test.spectec:4045.1-4045.50
  def $ivmul_{N : N, `i_1*` : iN(N)*, `i_2*` : iN(N)*}(N, i_1*{i_1 <- `i_1*`}, i_2*{i_2 <- `i_2*`}) = $imul_(N, i_1, i_2)*{i_1 <- `i_1*`, i_2 <- `i_2*`}

;; test.spectec:3884.1-3885.35
def $vextbinop__(ishape_1 : ishape, ishape_2 : ishape, vextbinop__ : vextbinop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4058.1-4059.97
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, half : half, sx : sx, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTMUL_vextbinop__(half, sx), v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivmul_, sx, sx, `%`_laneidx($half(half, 0, M_2)), `%`_laneidx(M_2), v_1, v_2)
  ;; test.spectec:4060.1-4061.77
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), DOTS_vextbinop__, v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivdot_, S_sx, S_sx, `%`_laneidx(0), `%`_laneidx(M_1), v_1, v_2)
  ;; test.spectec:4062.1-4063.108
  def $vextbinop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, v_1 : vec_(V128_Vnn), v_2 : vec_(V128_Vnn)}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), RELAXED_DOTS_vextbinop__, v_1, v_2) = $ivextbinop__(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1)), `%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), def $ivdot_sat_, S_sx, $relaxed2($R_idot, syntax sx, S_sx, U_sx), `%`_laneidx(0), `%`_laneidx(M_1), v_1, v_2)

;; test.spectec:3886.1-3887.38
def $vextternop__(ishape_1 : ishape, ishape_2 : ishape, vextternop__ : vextternop__(ishape_1, ishape_2), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn), vec_ : vec_(V128_Vnn)) : vec_(V128_Vnn)
  ;; test.spectec:4082.1-4087.50
  def $vextternop__{Jnn_1 : Jnn, M_1 : M, Jnn_2 : Jnn, M_2 : M, c_1 : vec_(V128_Vnn), c_2 : vec_(V128_Vnn), c_3 : vec_(V128_Vnn), c : vec_(V128_Vnn), Jnn : Jnn}(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), RELAXED_DOT_ADDS_vextternop__, c_1, c_2, c_3) = c
    -- if ($jsizenn(Jnn) = (2 * $lsizenn1((Jnn_1 : Jnn <: lanetype))))
    -- let{M : M} M = (2 * M_2)
    -- let{c' : vec_(V128_Vnn)} c' = $vextbinop__(`%`_ishape(`%X%`_shape((Jnn_1 : Jnn <: lanetype), `%`_dim(M_1))), `%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), RELAXED_DOTS_vextbinop__, c_1, c_2)
    -- let{c'' : vec_(V128_Vnn)} c'' = $vextunop__(`%`_ishape(`%X%`_shape((Jnn : Jnn <: lanetype), `%`_dim(M))), `%`_ishape(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2))), EXTADD_PAIRWISE_vextunop__(S_sx), c')
    -- if (c <- $vbinop_(`%X%`_shape((Jnn_2 : Jnn <: lanetype), `%`_dim(M_2)), ADD_vbinop_, c'', c_3))

;; test.spectec:4124.1-4125.63
syntax num = 
  | CONST(numtype : numtype, num_(numtype))

;; test.spectec:4127.1-4128.87
syntax vec = 
  | VCONST(vectype : vectype, vec_(vectype))

;; test.spectec:4143.1-4144.58
syntax result = 
  | _VALS(`val*` : val*)
  | `(REF.EXN_ADDR%)THROW_REF`(exnaddr : exnaddr)
  | TRAP

;; test.spectec:4152.1-4152.72
syntax hostfunc = 
  | `...`

;; test.spectec:4153.1-4153.73
syntax funccode = 
  | FUNC(typeidx : typeidx, `local*` : local*, expr : expr)
  | `...`

;; test.spectec:4155.1-4156.19
syntax taginst = 
{
  TYPE tagtype
}

;; test.spectec:4158.1-4159.33
syntax globalinst = 
{
  TYPE globaltype,
  VALUE val
}

;; test.spectec:4161.1-4162.32
syntax meminst = 
{
  TYPE memtype,
  BYTES byte*
}

;; test.spectec:4164.1-4165.32
syntax tableinst = 
{
  TYPE tabletype,
  REFS ref*
}

;; test.spectec:4167.1-4168.53
syntax funcinst = 
{
  TYPE deftype,
  MODULE moduleinst,
  CODE funccode
}

;; test.spectec:4170.1-4171.18
syntax datainst = 
{
  BYTES byte*
}

;; test.spectec:4173.1-4174.31
syntax eleminst = 
{
  TYPE elemtype,
  REFS ref*
}

;; test.spectec:4180.1-4181.64
syntax packval = 
  | PACK(packtype : packtype, iN($psizenn(packtype)))

;; test.spectec:4183.1-4184.18
syntax fieldval = 
  | CONST(numtype : numtype, num_(numtype))
  | VCONST(vectype : vectype, vec_(vectype))
  | `REF.I31_NUM`(u31 : u31)
  | `REF.NULL_ADDR`
  | `REF.STRUCT_ADDR`(structaddr : structaddr)
  | `REF.ARRAY_ADDR`(arrayaddr : arrayaddr)
  | `REF.FUNC_ADDR`(funcaddr : funcaddr)
  | `REF.EXN_ADDR`(exnaddr : exnaddr)
  | `REF.HOST_ADDR`(hostaddr : hostaddr)
  | `REF.EXTERN`(ref : ref)
  | PACK(packtype : packtype, iN($psizenn(packtype)))

;; test.spectec:4186.1-4187.37
syntax structinst = 
{
  TYPE deftype,
  FIELDS fieldval*
}

;; test.spectec:4189.1-4190.37
syntax arrayinst = 
{
  TYPE deftype,
  FIELDS fieldval*
}

;; test.spectec:4192.1-4193.31
syntax exninst = 
{
  TAG tagaddr,
  FIELDS val*
}

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

;; test.spectec:4239.1-4239.47
syntax state = 
  | `%;%`(store : store, frame : frame)

;; test.spectec:4240.1-4240.57
syntax config = 
  | `%;%`(state : state, `instr*` : instr*)

;; test.spectec:4267.1-4267.31
def $Ki : nat
  ;; test.spectec:4268.1-4268.15
  def $Ki = 1024

;; test.spectec:4273.1-4273.114
def $packfield_(storagetype : storagetype, val : val) : fieldval
  ;; test.spectec:4276.1-4276.36
  def $packfield_{valtype : valtype, val : val}((valtype : valtype <: storagetype), val) = (val : val <: fieldval)
  ;; test.spectec:4277.1-4277.88
  def $packfield_{packtype : packtype, i : num_(I32_numtype)}((packtype : packtype <: storagetype), CONST_val(I32_numtype, i)) = PACK_fieldval(packtype, $wrap__(32, $psize(packtype), i))

;; test.spectec:4274.1-4274.126
def $unpackfield_(storagetype : storagetype, sx?, fieldval : fieldval) : val
  ;; test.spectec:4279.1-4279.43
  def $unpackfield_{valtype : valtype, val : val}((valtype : valtype <: storagetype), ?(), (val : val <: fieldval)) = val
  ;; test.spectec:4280.1-4280.100
  def $unpackfield_{packtype : packtype, sx : sx, i : iN($psizenn(packtype))}((packtype : packtype <: storagetype), ?(sx), PACK_fieldval(packtype, i)) = CONST_val(I32_numtype, $extend__($psize(packtype), 32, sx, i))

;; test.spectec:4285.1-4285.86
rec {

;; test.spectec:4285.1-4285.86
def $tagsxa(externaddr*) : tagaddr*
  ;; test.spectec:4291.1-4291.23
  def $tagsxa([]) = []
  ;; test.spectec:4292.1-4292.42
  def $tagsxa{a : addr, `xa*` : externaddr*}([TAG_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $tagsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4293.1-4293.57
  def $tagsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $tagsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4286.1-4286.89
rec {

;; test.spectec:4286.1-4286.89
def $globalsxa(externaddr*) : globaladdr*
  ;; test.spectec:4295.1-4295.26
  def $globalsxa([]) = []
  ;; test.spectec:4296.1-4296.51
  def $globalsxa{a : addr, `xa*` : externaddr*}([GLOBAL_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $globalsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4297.1-4297.63
  def $globalsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $globalsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4287.1-4287.86
rec {

;; test.spectec:4287.1-4287.86
def $memsxa(externaddr*) : memaddr*
  ;; test.spectec:4299.1-4299.23
  def $memsxa([]) = []
  ;; test.spectec:4300.1-4300.42
  def $memsxa{a : addr, `xa*` : externaddr*}([MEM_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $memsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4301.1-4301.57
  def $memsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $memsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4288.1-4288.88
rec {

;; test.spectec:4288.1-4288.88
def $tablesxa(externaddr*) : tableaddr*
  ;; test.spectec:4303.1-4303.25
  def $tablesxa([]) = []
  ;; test.spectec:4304.1-4304.48
  def $tablesxa{a : addr, `xa*` : externaddr*}([TABLE_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $tablesxa(xa*{xa <- `xa*`})
  ;; test.spectec:4305.1-4305.61
  def $tablesxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $tablesxa(xa*{xa <- `xa*`})
}

;; test.spectec:4289.1-4289.87
rec {

;; test.spectec:4289.1-4289.87
def $funcsxa(externaddr*) : funcaddr*
  ;; test.spectec:4307.1-4307.24
  def $funcsxa([]) = []
  ;; test.spectec:4308.1-4308.45
  def $funcsxa{a : addr, `xa*` : externaddr*}([FUNC_externaddr(a)] ++ xa*{xa <- `xa*`}) = [a] ++ $funcsxa(xa*{xa <- `xa*`})
  ;; test.spectec:4309.1-4309.59
  def $funcsxa{externaddr : externaddr, `xa*` : externaddr*}([externaddr] ++ xa*{xa <- `xa*`}) = $funcsxa(xa*{xa <- `xa*`})
}

;; test.spectec:4314.1-4314.74
def $store(state : state) : store
  ;; test.spectec:4317.1-4317.23
  def $store{s : store, f : frame}(`%;%`_state(s, f)) = s

;; test.spectec:4315.1-4315.74
def $frame(state : state) : frame
  ;; test.spectec:4318.1-4318.23
  def $frame{s : store, f : frame}(`%;%`_state(s, f)) = f

;; test.spectec:4320.1-4320.80
def $tagaddr(state : state) : tagaddr*
  ;; test.spectec:4321.1-4321.37
  def $tagaddr{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame.TAGS_moduleinst

;; test.spectec:4323.1-4323.76
def $moduleinst(state : state) : moduleinst
  ;; test.spectec:4335.1-4335.35
  def $moduleinst{s : store, f : frame}(`%;%`_state(s, f)) = f.MODULE_frame

;; test.spectec:4324.1-4324.76
def $taginst(state : state) : taginst*
  ;; test.spectec:4336.1-4336.30
  def $taginst{s : store, f : frame}(`%;%`_state(s, f)) = s.TAGS_store

;; test.spectec:4325.1-4325.76
def $globalinst(state : state) : globalinst*
  ;; test.spectec:4337.1-4337.36
  def $globalinst{s : store, f : frame}(`%;%`_state(s, f)) = s.GLOBALS_store

;; test.spectec:4326.1-4326.76
def $meminst(state : state) : meminst*
  ;; test.spectec:4338.1-4338.30
  def $meminst{s : store, f : frame}(`%;%`_state(s, f)) = s.MEMS_store

;; test.spectec:4327.1-4327.76
def $tableinst(state : state) : tableinst*
  ;; test.spectec:4339.1-4339.34
  def $tableinst{s : store, f : frame}(`%;%`_state(s, f)) = s.TABLES_store

;; test.spectec:4328.1-4328.76
def $funcinst(state : state) : funcinst*
  ;; test.spectec:4340.1-4340.32
  def $funcinst{s : store, f : frame}(`%;%`_state(s, f)) = s.FUNCS_store

;; test.spectec:4329.1-4329.76
def $datainst(state : state) : datainst*
  ;; test.spectec:4341.1-4341.32
  def $datainst{s : store, f : frame}(`%;%`_state(s, f)) = s.DATAS_store

;; test.spectec:4330.1-4330.76
def $eleminst(state : state) : eleminst*
  ;; test.spectec:4342.1-4342.32
  def $eleminst{s : store, f : frame}(`%;%`_state(s, f)) = s.ELEMS_store

;; test.spectec:4331.1-4331.76
def $structinst(state : state) : structinst*
  ;; test.spectec:4343.1-4343.36
  def $structinst{s : store, f : frame}(`%;%`_state(s, f)) = s.STRUCTS_store

;; test.spectec:4332.1-4332.76
def $arrayinst(state : state) : arrayinst*
  ;; test.spectec:4344.1-4344.34
  def $arrayinst{s : store, f : frame}(`%;%`_state(s, f)) = s.ARRAYS_store

;; test.spectec:4333.1-4333.76
def $exninst(state : state) : exninst*
  ;; test.spectec:4345.1-4345.30
  def $exninst{s : store, f : frame}(`%;%`_state(s, f)) = s.EXNS_store

;; test.spectec:4359.1-4359.38
def $fof(state : state) : frame
  ;; test.spectec:4362.1-4362.24
  def $fof{z : state}(z) = $frame(z)

;; test.spectec:4348.1-4348.85
def $type(state : state, typeidx : typeidx) : deftype
  ;; test.spectec:4364.1-4364.42
  def $type{z : state, x : idx}(z, x) = $fof(z).MODULE_frame.TYPES_moduleinst[x!`%`_idx.0]

;; test.spectec:4358.1-4358.38
def $sof(state : state) : store
  ;; test.spectec:4361.1-4361.24
  def $sof{z : state}(z) = $store(z)

;; test.spectec:4349.1-4349.85
def $tag(state : state, tagidx : tagidx) : taginst
  ;; test.spectec:4365.1-4365.54
  def $tag{z : state, x : idx}(z, x) = $sof(z).TAGS_store[$fof(z).MODULE_frame.TAGS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4350.1-4350.85
def $global(state : state, globalidx : globalidx) : globalinst
  ;; test.spectec:4366.1-4366.63
  def $global{z : state, x : idx}(z, x) = $sof(z).GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4351.1-4351.85
def $mem(state : state, memidx : memidx) : meminst
  ;; test.spectec:4367.1-4367.54
  def $mem{z : state, x : idx}(z, x) = $sof(z).MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4352.1-4352.85
def $table(state : state, tableidx : tableidx) : tableinst
  ;; test.spectec:4368.1-4368.60
  def $table{z : state, x : idx}(z, x) = $sof(z).TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]]

;; test.spectec:4353.1-4353.85
def $func(state : state, funcidx : funcidx) : funcinst
  ;; test.spectec:4369.1-4369.57
  def $func{z : state, x : idx}(z, x) = $sof(z).FUNCS_store[$fof(z).MODULE_frame.FUNCS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4354.1-4354.85
def $data(state : state, dataidx : dataidx) : datainst
  ;; test.spectec:4370.1-4370.57
  def $data{z : state, x : idx}(z, x) = $sof(z).DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4355.1-4355.85
def $elem(state : state, tableidx : tableidx) : eleminst
  ;; test.spectec:4371.1-4371.57
  def $elem{z : state, x : idx}(z, x) = $sof(z).ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[x!`%`_idx.0]]

;; test.spectec:4356.1-4356.85
def $local(state : state, localidx : localidx) : val?
  ;; test.spectec:4372.1-4372.37
  def $local{z : state, x : idx}(z, x) = $fof(z).LOCALS_frame[x!`%`_idx.0]

;; test.spectec:4377.1-4377.165
def $with_local(state : state, localidx : localidx, val : val) : state
  ;; test.spectec:4388.1-4388.60
  def $with_local{z : state, x : idx, v : val}(z, x, v) = `%;%`_state($sof(z), $fof(z)[LOCALS_frame[x!`%`_idx.0] = ?(v)])

;; test.spectec:4378.1-4378.172
def $with_global(state : state, globalidx : globalidx, val : val) : state
  ;; test.spectec:4389.1-4389.92
  def $with_global{z : state, x : idx, v : val}(z, x, v) = `%;%`_state($sof(z)[GLOBALS_store[$fof(z).MODULE_frame.GLOBALS_moduleinst[x!`%`_idx.0]].VALUE_globalinst = v], $fof(z))

;; test.spectec:4379.1-4379.174
def $with_table(state : state, tableidx : tableidx, nat : nat, ref : ref) : state
  ;; test.spectec:4390.1-4390.94
  def $with_table{z : state, x : idx, i : nat, r : ref}(z, x, i, r) = `%;%`_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]].REFS_tableinst[i] = r], $fof(z))

;; test.spectec:4380.1-4380.165
def $with_tableinst(state : state, tableidx : tableidx, tableinst : tableinst) : state
  ;; test.spectec:4391.1-4391.89
  def $with_tableinst{z : state, x : idx, ti : tableinst}(z, x, ti) = `%;%`_state($sof(z)[TABLES_store[$fof(z).MODULE_frame.TABLES_moduleinst[x!`%`_idx.0]] = ti], $fof(z))

;; test.spectec:4381.1-4381.176
def $with_mem(state : state, memidx : memidx, nat : nat, nat : nat, byte*) : state
  ;; test.spectec:4392.1-4392.98
  def $with_mem{z : state, x : idx, i : nat, j : nat, `b*` : byte*}(z, x, i, j, b*{b <- `b*`}) = `%;%`_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]].BYTES_meminst[i : j] = b*{b <- `b*`}], $fof(z))

;; test.spectec:4382.1-4382.167
def $with_meminst(state : state, memidx : memidx, meminst : meminst) : state
  ;; test.spectec:4393.1-4393.83
  def $with_meminst{z : state, x : idx, mi : meminst}(z, x, mi) = `%;%`_state($sof(z)[MEMS_store[$fof(z).MODULE_frame.MEMS_moduleinst[x!`%`_idx.0]] = mi], $fof(z))

;; test.spectec:4383.1-4383.169
def $with_elem(state : state, elemidx : elemidx, ref*) : state
  ;; test.spectec:4394.1-4394.87
  def $with_elem{z : state, x : idx, `r*` : ref*}(z, x, r*{r <- `r*`}) = `%;%`_state($sof(z)[ELEMS_store[$fof(z).MODULE_frame.ELEMS_moduleinst[x!`%`_idx.0]].REFS_eleminst = r*{r <- `r*`}], $fof(z))

;; test.spectec:4384.1-4384.170
def $with_data(state : state, dataidx : dataidx, byte*) : state
  ;; test.spectec:4395.1-4395.88
  def $with_data{z : state, x : idx, `b*` : byte*}(z, x, b*{b <- `b*`}) = `%;%`_state($sof(z)[DATAS_store[$fof(z).MODULE_frame.DATAS_moduleinst[x!`%`_idx.0]].BYTES_datainst = b*{b <- `b*`}], $fof(z))

;; test.spectec:4385.1-4385.181
def $with_struct(state : state, structaddr : structaddr, nat : nat, fieldval : fieldval) : state
  ;; test.spectec:4396.1-4396.77
  def $with_struct{z : state, a : addr, i : nat, fv : fieldval}(z, a, i, fv) = `%;%`_state($sof(z)[STRUCTS_store[a].FIELDS_structinst[i] = fv], $fof(z))

;; test.spectec:4386.1-4386.180
def $with_array(state : state, arrayaddr : arrayaddr, nat : nat, fieldval : fieldval) : state
  ;; test.spectec:4397.1-4397.75
  def $with_array{z : state, a : addr, i : nat, fv : fieldval}(z, a, i, fv) = `%;%`_state($sof(z)[ARRAYS_store[a].FIELDS_arrayinst[i] = fv], $fof(z))

;; test.spectec:4400.1-4400.140
def $add_structinst(state : state, structinst*) : state
  ;; test.spectec:4404.1-4404.65
  def $add_structinst{z : state, `si*` : structinst*}(z, si*{si <- `si*`}) = `%;%`_state($sof(z)[STRUCTS_store =++ si*{si <- `si*`}], $fof(z))

;; test.spectec:4401.1-4401.139
def $add_arrayinst(state : state, arrayinst*) : state
  ;; test.spectec:4405.1-4405.63
  def $add_arrayinst{z : state, `ai*` : arrayinst*}(z, ai*{ai <- `ai*`}) = `%;%`_state($sof(z)[ARRAYS_store =++ ai*{ai <- `ai*`}], $fof(z))

;; test.spectec:4402.1-4402.137
def $add_exninst(state : state, exninst*) : state
  ;; test.spectec:4406.1-4406.61
  def $add_exninst{z : state, `exn*` : exninst*}(z, exn*{exn <- `exn*`}) = `%;%`_state($sof(z)[EXNS_store =++ exn*{exn <- `exn*`}], $fof(z))

;; test.spectec:4411.1-4411.62
def $growtable(tableinst : tableinst, nat : nat, ref : ref) : tableinst
  ;; test.spectec:4414.1-4419.33
  def $growtable{tableinst : tableinst, n : n, r : ref, tableinst' : tableinst, i' : u64}(tableinst, n, r) = tableinst'
    -- let{at : addrtype, i : u64, `j?` : u64?, rt : reftype, `r'*` : ref*} {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i, j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`}} = tableinst
    -- if (tableinst' = {TYPE `%%%`_tabletype(at, `[%..%]`_limits(i', j?{j <- `j?`}), rt), REFS r'*{r' <- `r'*`} ++ r^n{}})
    -- if (i'!`%`_u64.0 = (|r'*{r' <- `r'*`}| + n))
    -- (if (i'!`%`_u64.0 <= j!`%`_u64.0))?{j <- `j?`}
    -- if ((i'!`%`_u64.0 : nat <:> int) <= (((2 ^ $size((at : addrtype <: numtype))) : nat <:> int) - (1 : nat <:> int)))

;; test.spectec:4412.1-4412.62
def $growmem(meminst : meminst, nat : nat) : meminst
  ;; test.spectec:4421.1-4426.36
  def $growmem{meminst : meminst, n : n, meminst' : meminst, i' : u64}(meminst, n) = meminst'
    -- let{at : addrtype, i : u64, `j?` : u64?, `b*` : byte*} {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i, j?{j <- `j?`})), BYTES b*{b <- `b*`}} = meminst
    -- if (meminst' = {TYPE `%%PAGE`_memtype(at, `[%..%]`_limits(i', j?{j <- `j?`})), BYTES b*{b <- `b*`} ++ `%`_byte(0)^(n * (64 * $Ki)){}})
    -- if ((i'!`%`_u64.0 : nat <:> rat) = (((|b*{b <- `b*`}| : nat <:> rat) / ((64 * $Ki) : nat <:> rat)) + (n : nat <:> rat)))
    -- (if (i'!`%`_u64.0 <= j!`%`_u64.0))?{j <- `j?`}
    -- if (i'!`%`_u64.0 <= (2 ^ ((($size((at : addrtype <: numtype)) : nat <:> int) - (16 : nat <:> int)) : int <:> nat)))

;; test.spectec:4457.1-4457.60
relation Num_ok: `%|-%:%`(store, num, numtype)
  ;; test.spectec:4462.1-4463.23
  rule _{s : store, nt : numtype, c : num_(nt)}:
    `%|-%:%`(s, CONST_num(nt, c), nt)

;; test.spectec:4458.1-4458.60
relation Vec_ok: `%|-%:%`(store, vec, vectype)
  ;; test.spectec:4465.1-4466.24
  rule _{s : store, vt : vectype, c : vec_(vt)}:
    `%|-%:%`(s, VCONST_vec(vt, c), vt)

;; test.spectec:4459.1-4459.60
rec {

;; test.spectec:4459.1-4459.60
relation Ref_ok: `%|-%:%`(store, ref, reftype)
  ;; test.spectec:4469.1-4470.36
  rule null{s : store}:
    `%|-%:%`(s, `REF.NULL_ADDR`_ref, REF_reftype(?(NULL_null), BOT_heaptype))

  ;; test.spectec:4472.1-4473.31
  rule i31{s : store, i : u31}:
    `%|-%:%`(s, `REF.I31_NUM`_ref(i), REF_reftype(?(), I31_heaptype))

  ;; test.spectec:4475.1-4477.31
  rule struct{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, `REF.STRUCT_ADDR`_ref(a), REF_reftype(?(), (dt : deftype <: heaptype)))
    -- if (s.STRUCTS_store[a].TYPE_structinst = dt)

  ;; test.spectec:4479.1-4481.30
  rule array{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, `REF.ARRAY_ADDR`_ref(a), REF_reftype(?(), (dt : deftype <: heaptype)))
    -- if (s.ARRAYS_store[a].TYPE_arrayinst = dt)

  ;; test.spectec:4483.1-4485.29
  rule func{s : store, a : addr, dt : deftype}:
    `%|-%:%`(s, `REF.FUNC_ADDR`_ref(a), REF_reftype(?(), (dt : deftype <: heaptype)))
    -- if (s.FUNCS_store[a].TYPE_funcinst = dt)

  ;; test.spectec:4487.1-4489.24
  rule exn{s : store, a : addr, exn : exninst}:
    `%|-%:%`(s, `REF.EXN_ADDR`_ref(a), REF_reftype(?(), EXN_heaptype))
    -- if (s.EXNS_store[a] = exn)

  ;; test.spectec:4491.1-4492.33
  rule host{s : store, a : addr}:
    `%|-%:%`(s, `REF.HOST_ADDR`_ref(a), REF_reftype(?(), ANY_heaptype))

  ;; test.spectec:4494.1-4497.30
  rule extern{s : store, ref : ref}:
    `%|-%:%`(s, `REF.EXTERN`_ref(ref), REF_reftype(?(), EXTERN_heaptype))
    -- Ref_ok: `%|-%:%`(s, ref, REF_reftype(?(), ANY_heaptype))
    -- if (ref =/= `REF.NULL_ADDR`_ref)

  ;; test.spectec:4499.1-4503.34
  rule sub{s : store, ref : ref, rt : reftype, rt' : reftype}:
    `%|-%:%`(s, ref, rt)
    -- Ref_ok: `%|-%:%`(s, ref, rt')
    -- Reftype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt)
    -- Reftype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, rt', rt)
}

;; test.spectec:4460.1-4460.60
relation Val_ok: `%|-%:%`(store, val, valtype)
  ;; test.spectec:4506.1-4508.27
  rule num{s : store, num : num, nt : numtype}:
    `%|-%:%`(s, (num : num <: val), (nt : numtype <: valtype))
    -- Num_ok: `%|-%:%`(s, num, nt)

  ;; test.spectec:4510.1-4512.27
  rule vec{s : store, vec : vec, vt : vectype}:
    `%|-%:%`(s, (vec : vec <: val), (vt : vectype <: valtype))
    -- Vec_ok: `%|-%:%`(s, vec, vt)

  ;; test.spectec:4514.1-4516.27
  rule ref{s : store, ref : ref, rt : reftype}:
    `%|-%:%`(s, (ref : ref <: val), (rt : reftype <: valtype))
    -- Ref_ok: `%|-%:%`(s, ref, rt)

;; test.spectec:4521.1-4521.49
relation Packval_ok: `%|-%:%`(store, packval, packtype)
  ;; test.spectec:4524.1-4525.22
  rule _{s : store, pt : packtype, c : iN($psizenn(pt))}:
    `%|-%:%`(s, PACK_packval(pt, c), pt)

;; test.spectec:4522.1-4522.54
relation Fieldval_ok: `%|-%:%`(store, fieldval, storagetype)
  ;; test.spectec:4527.1-4529.26
  rule val{s : store, val : val, t : valtype}:
    `%|-%:%`(s, (val : val <: fieldval), (t : valtype <: storagetype))
    -- Val_ok: `%|-%:%`(s, val, t)

  ;; test.spectec:4531.1-4533.35
  rule packval{s : store, packval : packval, pt : packtype}:
    `%|-%:%`(s, (packval : packval <: fieldval), (pt : packtype <: storagetype))
    -- Packval_ok: `%|-%:%`(s, packval, pt)

;; test.spectec:4538.1-4538.84
rec {

;; test.spectec:4538.1-4538.84
relation Externaddr_ok: `%|-%:%`(store, externaddr, externtype)
  ;; test.spectec:4540.1-4542.28
  rule tag{s : store, a : addr, taginst : taginst}:
    `%|-%:%`(s, TAG_externaddr(a), TAG_externtype(taginst.TYPE_taginst))
    -- if (s.TAGS_store[a] = taginst)

  ;; test.spectec:4544.1-4546.34
  rule global{s : store, a : addr, globalinst : globalinst}:
    `%|-%:%`(s, GLOBAL_externaddr(a), GLOBAL_externtype(globalinst.TYPE_globalinst))
    -- if (s.GLOBALS_store[a] = globalinst)

  ;; test.spectec:4548.1-4550.28
  rule mem{s : store, a : addr, meminst : meminst}:
    `%|-%:%`(s, MEM_externaddr(a), MEM_externtype(meminst.TYPE_meminst))
    -- if (s.MEMS_store[a] = meminst)

  ;; test.spectec:4552.1-4554.32
  rule table{s : store, a : addr, tableinst : tableinst}:
    `%|-%:%`(s, TABLE_externaddr(a), TABLE_externtype(tableinst.TYPE_tableinst))
    -- if (s.TABLES_store[a] = tableinst)

  ;; test.spectec:4556.1-4558.30
  rule func{s : store, a : addr, funcinst : funcinst}:
    `%|-%:%`(s, FUNC_externaddr(a), FUNC_externtype((funcinst.TYPE_funcinst : deftype <: typeuse)))
    -- if (s.FUNCS_store[a] = funcinst)

  ;; test.spectec:4560.1-4564.37
  rule sub{s : store, externaddr : externaddr, xt : externtype, xt' : externtype}:
    `%|-%:%`(s, externaddr, xt)
    -- Externaddr_ok: `%|-%:%`(s, externaddr, xt')
    -- Externtype_ok: `%|-%:OK`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt)
    -- Externtype_sub: `%|-%<:%`({TYPES [], TAGS [], GLOBALS [], MEMS [], TABLES [], FUNCS [], DATAS [], ELEMS [], LOCALS [], LABELS [], RETURN ?(), REFS [], RECS []}, xt', xt)
}

;; test.spectec:4577.1-4577.96
def $inst_valtype(moduleinst : moduleinst, valtype : valtype) : valtype
  ;; test.spectec:4583.1-4583.75
  def $inst_valtype{moduleinst : moduleinst, t : valtype}(moduleinst, t) = $subst_all_valtype(t, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4578.1-4578.96
def $inst_reftype(moduleinst : moduleinst, reftype : reftype) : reftype
  ;; test.spectec:4584.1-4584.77
  def $inst_reftype{moduleinst : moduleinst, rt : reftype}(moduleinst, rt) = $subst_all_reftype(rt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4579.1-4579.105
def $inst_globaltype(moduleinst : moduleinst, globaltype : globaltype) : globaltype
  ;; test.spectec:4585.1-4585.83
  def $inst_globaltype{moduleinst : moduleinst, gt : globaltype}(moduleinst, gt) = $subst_all_globaltype(gt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4580.1-4580.96
def $inst_memtype(moduleinst : moduleinst, memtype : memtype) : memtype
  ;; test.spectec:4586.1-4586.77
  def $inst_memtype{moduleinst : moduleinst, mt : memtype}(moduleinst, mt) = $subst_all_memtype(mt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

;; test.spectec:4581.1-4581.102
def $inst_tabletype(moduleinst : moduleinst, tabletype : tabletype) : tabletype
  ;; test.spectec:4587.1-4587.81
  def $inst_tabletype{moduleinst : moduleinst, tt : tabletype}(moduleinst, tt) = $subst_all_tabletype(tt, (moduleinst.TYPES_moduleinst : deftype* <: typeuse*))

