;; memory.fill
(module
  (memory 1)

  (func (export "fill") (param i32 i32 i32)
    (memory.fill
      (local.get 0)
      (local.get 1)
      (local.get 2)))

  (func (export "load8_u") (param i32) (result i32)
    (i32.load8_u (local.get 0)))
)

;; Fill all of memory
(invoke "fill" (i32.const 0) (i32.const 0) (i32.const 0x10000))
