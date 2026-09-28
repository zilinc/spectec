(module
  (type $t (func (param i32) (result i32)))  ;; TYPES[0]
  (memory 1)                                  ;; MEMS[0]
  (global $count (mut i32) (i32.const 0))  ;; GLOBALS[0]
  (table 1 funcref)                        ;; TABLES[0]
  (elem (i32.const 0) $sq)              ;; table[0] = $sq, at instantiation

  (func $sq (param i32) (result i32)   ;; FUNCS[0]
    local.get 0  local.get 0  i32.mul)

  (func $run (export "run")          ;; FUNCS[1]
      (param $x i32) (result i32) (local $y i32)
    i32.const 0  local.get $x  i32.store       ;; A: write x to mem
    local.get $x  i32.const 0
    call_indirect (type $t)                    ;; B: call table[0]
    local.set $y
    global.get $count  i32.const 1  i32.add
    global.set $count                           ;; C: bump global
    i32.const 0  i32.load                       ;; D: read mem back
    local.get $y  i32.add))