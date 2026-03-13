;; memory.fill
(module
  (memory i64 1)

  (func (export "fill") (param i64 i32 i64)
    (memory.fill
      (local.get 0)
      (local.get 1)
      (local.get 2)))

  (func (export "load8_u") (param i64) (result i32)
    (i32.load8_u (local.get 0)))
)

;; Fill all of memory
(invoke "fill" (i64.const 0) (i32.const 0) (i64.const 0x10000))
