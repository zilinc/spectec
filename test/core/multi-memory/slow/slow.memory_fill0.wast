;; memory.fill
(module
  (memory $mem0 0)
  (memory $mem1 0)
  (memory $mem2 1)

  (func (export "fill") (param i32 i32 i32)
    (memory.fill $mem2
      (local.get 0)
      (local.get 1)
      (local.get 2)))

  (func (export "load8_u") (param i32) (result i32)
    (i32.load8_u $mem2 (local.get 0)))
)

;; Fill all of memory
(invoke "fill" (i32.const 0) (i32.const 0) (i32.const 0x10000))
