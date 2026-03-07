;; Test that newly allocated memory (program start and memory.grow) is zeroed

(module
  (memory 1)
  (func (export "grow") (param i32) (result i32)
    (memory.grow (local.get 0))
  )
  (func (export "check-memory-zero") (param i32 i32) (result i32)
    (local i32)
    (local.set 2 (i32.const 1))
    (block
      (loop
        (local.set 2 (i32.load8_u (local.get 0)))
        (br_if 1 (i32.ne (local.get 2) (i32.const 0)))
        (br_if 1 (i32.ge_u (local.get 0) (local.get 1)))
        (local.set 0 (i32.add (local.get 0) (i32.const 1)))
        (br_if 0 (i32.le_u (local.get 0) (local.get 1)))
      )
    )
    (local.get 2)
  )
)

(assert_return (invoke "check-memory-zero" (i32.const 0) (i32.const 0xffff)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 1))
(assert_return (invoke "check-memory-zero" (i32.const 0x10000) (i32.const 0x1_ffff)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 2))
(assert_return (invoke "check-memory-zero" (i32.const 0x20000) (i32.const 0x2_ffff)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 3))
(assert_return (invoke "check-memory-zero" (i32.const 0x30000) (i32.const 0x3_ffff)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 4))
(assert_return (invoke "check-memory-zero" (i32.const 0x40000) (i32.const 0x4_ffff)) (i32.const 0))
(assert_return (invoke "grow" (i32.const 1)) (i32.const 5))
(assert_return (invoke "check-memory-zero" (i32.const 0x50000) (i32.const 0x5_ffff)) (i32.const 0))
