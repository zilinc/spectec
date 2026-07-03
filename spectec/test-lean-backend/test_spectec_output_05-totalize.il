
;; test.spectec:7.1-7.22
syntax localidx = nat

;; test.spectec:8.1-8.23
syntax globalidx = nat

;; test.spectec:10.1-10.17
syntax mut = 
  | MUT

;; test.spectec:11.1-11.39
syntax valtype = 
  | I32
  | I64
  | F32
  | F64

;; test.spectec:12.1-12.39
syntax functype = 
  | `%->%`(`valtype*` : valtype*, `valtype*` : valtype*)

;; test.spectec:13.1-13.33
syntax globaltype = 
  | `%%`(`mut?` : mut?, valtype : valtype)

;; test.spectec:15.1-15.19
syntax const = nat

;; test.spectec:17.1-25.27
syntax instr = 
  | NOP
  | DROP
  | SELECT
  | CONST(valtype : valtype, const : const)
  | `LOCAL.GET`(localidx : localidx)
  | `LOCAL.SET`(localidx : localidx)
  | `GLOBAL.GET`(globalidx : globalidx)
  | `GLOBAL.SET`(globalidx : globalidx)

;; test.spectec:30.1-30.58
syntax context = 
{
  GLOBALS globaltype*,
  LOCALS valtype*
}

;; test.spectec:35.1-35.47
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; test.spectec:37.1-38.26
  rule nop{C : context}:
    `%|-%:%`(C, NOP_instr, `%->%`_functype([], []))

  ;; test.spectec:40.1-41.25
  rule drop{C : context, t : valtype}:
    `%|-%:%`(C, DROP_instr, `%->%`_functype([t], []))

  ;; test.spectec:43.1-44.31
  rule select{C : context, t : valtype}:
    `%|-%:%`(C, SELECT_instr, `%->%`_functype([t t I32_valtype], [t]))

  ;; test.spectec:46.1-47.30
  rule const{C : context, t : valtype, c : const}:
    `%|-%:%`(C, CONST_instr(t, c), `%->%`_functype([], [t]))

  ;; test.spectec:49.1-51.26
  rule `local.get`{C : context, x : localidx, t : valtype}:
    `%|-%:%`(C, `LOCAL.GET`_instr(x), `%->%`_functype([], [t]))
    -- if (C.LOCALS_context[x] = t)

  ;; test.spectec:53.1-55.26
  rule `local.set`{C : context, x : localidx, t : valtype}:
    `%|-%:%`(C, `LOCAL.SET`_instr(x), `%->%`_functype([t], []))
    -- if (C.LOCALS_context[x] = t)

  ;; test.spectec:57.1-59.32
  rule `global.get`{C : context, x : globalidx, t : valtype}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->%`_functype([], [t]))
    -- if (C.GLOBALS_context[x] = `%%`_globaltype(?(MUT_mut), t))

  ;; test.spectec:61.1-63.31
  rule `global.set`{C : context, x : globalidx, t : valtype}:
    `%|-%:%`(C, `GLOBAL.GET`_instr(x), `%->%`_functype([t], []))
    -- if (C.GLOBALS_context[x] = `%%`_globaltype(?(MUT_mut), t))

;; test.spectec:68.1-68.18
syntax addr = nat

;; test.spectec:69.1-69.38
syntax moduleinst = 
{
  GLOBALS addr*
}

;; test.spectec:71.1-71.33
syntax val = 
  | CONST(valtype : valtype, const : const)

;; test.spectec:73.1-73.32
syntax store = 
{
  GLOBALS val*
}

;; test.spectec:74.1-74.50
syntax frame = 
{
  LOCALS val*,
  MODULE moduleinst
}

;; test.spectec:75.1-75.28
syntax state = 
  | `%;%`(store : store, frame : frame)

;; test.spectec:76.1-76.30
syntax config = 
  | `%;%`(state : state, `instr*` : instr*)

;; test.spectec:82.1-82.34
def $local(state : state, localidx : localidx) : val
  ;; test.spectec:83.1-83.36
  def $local{s : store, f : frame, x : nat}(`%;%`_state(s, f), x) = f.LOCALS_frame[x]

;; test.spectec:85.1-85.36
def $global(state : state, globalidx : globalidx) : val
  ;; test.spectec:86.1-86.56
  def $global{s : store, f : frame, x : nat}(`%;%`_state(s, f), x) = s.GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[x]]

;; test.spectec:88.1-88.48
def $update_local(state : state, localidx : localidx, val : val) : state
  ;; test.spectec:89.1-89.55
  def $update_local{s : store, f : frame, x : nat, v : val}(`%;%`_state(s, f), x, v) = `%;%`_state(s, f[LOCALS_frame[x] = v])

;; test.spectec:91.1-91.50
def $update_global(state : state, globalidx : globalidx, val : val) : state
  ;; test.spectec:92.1-92.75
  def $update_global{s : store, f : frame, x : nat, v : val}(`%;%`_state(s, f), x, v) = `%;%`_state(s[GLOBALS_store[f.MODULE_frame.GLOBALS_moduleinst[x]] = v], f)

;; test.spectec:96.1-96.37
relation Step_pure: `%~>%`(instr*, instr*)
  ;; test.spectec:105.1-106.17
  rule nop:
    `%~>%`([NOP_instr], [])

  ;; test.spectec:108.1-109.22
  rule drop{val : val}:
    `%~>%`([(val : val <: instr) DROP_instr], [])

  ;; test.spectec:111.1-112.63
  rule `select-true`{val_1 : val, val_2 : val, c : const}:
    `%~>%`([(val_1 : val <: instr) (val_2 : val <: instr) CONST_instr(I32_valtype, c) SELECT_instr], [(val_1 : val <: instr)])
    -- if (c =/= 0)

  ;; test.spectec:114.1-115.62
  rule `select-false`{val_1 : val, val_2 : val, c : const}:
    `%~>%`([(val_1 : val <: instr) (val_2 : val <: instr) CONST_instr(I32_valtype, c) SELECT_instr], [(val_2 : val <: instr)])
    -- otherwise

;; test.spectec:95.1-95.32
relation Step: `%~>%`(config, config)
  ;; test.spectec:101.1-103.36
  rule pure{z : state, `instr*` : instr*, `instr'*` : instr*}:
    `%~>%`(`%;%`_config(z, instr*{instr <- `instr*`}), `%;%`_config(z, instr'*{instr' <- `instr'*`}))
    -- Step_pure: `%~>%`(instr*{instr <- `instr*`}, instr'*{instr' <- `instr'*`})

  ;; test.spectec:117.1-119.29
  rule `local.get`{z : state, x : localidx, val : val}:
    `%~>%`(`%;%`_config(z, [`LOCAL.GET`_instr(x)]), `%;%`_config(z, [(val : val <: instr)]))
    -- if (val = $local(z, x))

  ;; test.spectec:121.1-123.40
  rule `local.set`{z : state, val : val, x : localidx, z' : state}:
    `%~>%`(`%;%`_config(z, [(val : val <: instr) `LOCAL.SET`_instr(x)]), `%;%`_config(z', []))
    -- if (z' = $update_local(z, x, val))

  ;; test.spectec:125.1-127.30
  rule `global.get`{z : state, x : globalidx, val : val}:
    `%~>%`(`%;%`_config(z, [`GLOBAL.GET`_instr(x)]), `%;%`_config(z, [(val : val <: instr)]))
    -- if (val = $global(z, x))

  ;; test.spectec:129.1-131.41
  rule `global.set`{z : state, val : val, x : globalidx, z' : state}:
    `%~>%`(`%;%`_config(z, [(val : val <: instr) `GLOBAL.SET`_instr(x)]), `%;%`_config(z', []))
    -- if (z' = $update_global(z, x, val))

;; test.spectec:136.1-136.30
def $float(nat : nat, nat*) : const

;; test.spectec:138.1-138.40
grammar Bbyte : nat
  ;; test.spectec:138.23-138.40
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:(0x00 | ... | 0xFF) => `<implicit-prod-result>`

;; test.spectec:140.1-142.79
rec {

;; test.spectec:140.1-142.79
grammar Bu(N : nat) : nat
  ;; test.spectec:141.5-141.80
  prod{n : nat} n:Bbyte => n
    -- if ((n < (2 ^ 7)) /\ (n < (2 ^ N)))
  ;; test.spectec:142.5-142.79
  prod{m : nat, n : nat} {{n:Bbyte} {m:Bu((((N : nat <:> int) - (7 : nat <:> int)) : int <:> nat))}} => (((2 ^ 7) * m) + (((n : nat <:> int) - ((2 ^ 7) : nat <:> int)) : int <:> nat))
    -- if ((n >= (2 ^ 7)) /\ (N > 7))
}

;; test.spectec:144.1-144.30
grammar Bu32 : const
  ;; test.spectec:144.24-144.30
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:Bu(32) => `<implicit-prod-result>`

;; test.spectec:145.1-145.30
grammar Bu64 : const
  ;; test.spectec:145.24-145.30
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:Bu(64) => `<implicit-prod-result>`

;; test.spectec:147.1-148.36
grammar Bf(N : nat) : nat
  ;; test.spectec:148.5-148.36
  prod{`b*` : nat*} b*{b <- `b*`}:Bbyte^(((N : nat <:> rat) / (8 : nat <:> rat)) : rat <:> nat){} => $float(N, b*{b <- `b*`})

;; test.spectec:150.1-150.30
grammar Bf32 : const
  ;; test.spectec:150.24-150.30
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:Bf(32) => `<implicit-prod-result>`

;; test.spectec:151.1-151.30
grammar Bf64 : const
  ;; test.spectec:151.24-151.30
  prod{`<implicit-prod-result>` : nat} `<implicit-prod-result>`:Bf(64) => `<implicit-prod-result>`

;; test.spectec:154.1-158.18
grammar Bvaltype : valtype
  ;; test.spectec:155.7-155.18
  prod 0x7F => I32_valtype
  ;; test.spectec:156.7-156.18
  prod 0x7E => I64_valtype
  ;; test.spectec:157.7-157.18
  prod 0x7D => F32_valtype
  ;; test.spectec:158.7-158.18
  prod 0x7C => F64_valtype

;; test.spectec:160.1-162.18
grammar Bmut : mut?
  ;; test.spectec:161.7-161.18
  prod 0x00 => ?()
  ;; test.spectec:162.7-162.18
  prod 0x01 => ?(MUT_mut)

;; test.spectec:164.1-165.35
grammar Bglobaltype : globaltype
  ;; test.spectec:165.7-165.35
  prod{mut : mut, t : valtype} {{t:Bvaltype} {?(mut):Bmut}} => `%%`_globaltype(?(mut), t)

;; test.spectec:167.1-168.35
grammar Bresulttype : valtype*
  ;; test.spectec:168.7-168.35
  prod{n : nat, `t*` : valtype*} {{n:Bu32} {t:Bvaltype^n{t <- `t*`}}} => t^n{t <- `t*`}

;; test.spectec:170.1-171.61
grammar Bfunctype : functype
  ;; test.spectec:171.7-171.61
  prod{`t_1*` : valtype*, `t_2*` : valtype*} {{0x60} {t_1*{t_1 <- `t_1*`}:Bresulttype} {t_2*{t_2 <- `t_2*`}:Bresulttype}} => `%->%`_functype(t_1*{t_1 <- `t_1*`}, t_2*{t_2 <- `t_2*`})

;; test.spectec:174.1-174.45
grammar Bglobalidx : globalidx
  ;; test.spectec:174.34-174.45
  prod{x : nat} x:Bu32 => x

;; test.spectec:175.1-175.43
grammar Blocalidx : localidx
  ;; test.spectec:175.32-175.43
  prod{x : nat} x:Bu32 => x

;; test.spectec:177.1-188.31
grammar Binstr : instr
  ;; test.spectec:178.5-178.16
  prod 0x01 => NOP_instr
  ;; test.spectec:179.5-179.17
  prod 0x1A => DROP_instr
  ;; test.spectec:180.5-180.19
  prod 0x1B => SELECT_instr
  ;; test.spectec:181.5-181.36
  prod{x : nat} {{0x20} {x:Blocalidx}} => `LOCAL.GET`_instr(x)
  ;; test.spectec:182.5-182.36
  prod{x : nat} {{0x21} {x:Blocalidx}} => `LOCAL.SET`_instr(x)
  ;; test.spectec:183.5-183.38
  prod{x : nat} {{0x23} {x:Bglobalidx}} => `GLOBAL.GET`_instr(x)
  ;; test.spectec:184.5-184.38
  prod{x : nat} {{0x24} {x:Bglobalidx}} => `GLOBAL.SET`_instr(x)
  ;; test.spectec:185.5-185.31
  prod{n : nat} {{0x41} {n:Bu32}} => CONST_instr(I32_valtype, n)
  ;; test.spectec:186.5-186.31
  prod{n : nat} {{0x42} {n:Bu64}} => CONST_instr(I64_valtype, n)
  ;; test.spectec:187.5-187.31
  prod{p : nat} {{0x43} {p:Bf32}} => CONST_instr(F32_valtype, p)
  ;; test.spectec:188.5-188.31
  prod{p : nat} {{0x44} {p:Bf64}} => CONST_instr(F64_valtype, p)

