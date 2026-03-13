;; Test `return_call` operator

(module
  (import "spectest" "print_i32_f32" (func $print_i32_f32 (param i32 f32)))

  ;; Auxiliary definitions
  (func $const-i32 (result i32) (i32.const 0x132))
  (func $const-i64 (result i64) (i64.const 0x164))
  (func $const-f32 (result f32) (f32.const 0xf32))
  (func $const-f64 (result f64) (f64.const 0xf64))

  (func $id-i32 (param i32) (result i32) (local.get 0))
  (func $id-i64 (param i64) (result i64) (local.get 0))
  (func $id-f32 (param f32) (result f32) (local.get 0))
  (func $id-f64 (param f64) (result f64) (local.get 0))

  (func $f32-i32 (param f32 i32) (result i32) (local.get 1))
  (func $i32-i64 (param i32 i64) (result i64) (local.get 1))
  (func $f64-f32 (param f64 f32) (result f32) (local.get 1))
  (func $i64-f64 (param i64 f64) (result f64) (local.get 1))

  ;; Typing

  (func (export "type-i32") (result i32) (return_call $const-i32))
  (func (export "type-i64") (result i64) (return_call $const-i64))
  (func (export "type-f32") (result f32) (return_call $const-f32))
  (func (export "type-f64") (result f64) (return_call $const-f64))

  (func (export "type-first-i32") (result i32) (return_call $id-i32 (i32.const 32)))
  (func (export "type-first-i64") (result i64) (return_call $id-i64 (i64.const 64)))
  (func (export "type-first-f32") (result f32) (return_call $id-f32 (f32.const 1.32)))
  (func (export "type-first-f64") (result f64) (return_call $id-f64 (f64.const 1.64)))

  (func (export "type-second-i32") (result i32)
    (return_call $f32-i32 (f32.const 32.1) (i32.const 32))
  )
  (func (export "type-second-i64") (result i64)
    (return_call $i32-i64 (i32.const 32) (i64.const 64))
  )
  (func (export "type-second-f32") (result f32)
    (return_call $f64-f32 (f64.const 64) (f32.const 32))
  )
  (func (export "type-second-f64") (result f64)
    (return_call $i64-f64 (i64.const 64) (f64.const 64.1))
  )

  ;; Recursion

  (func $fac-acc (export "fac-acc") (param i64 i64) (result i64)
    (if (result i64) (i64.eqz (local.get 0))
      (then (local.get 1))
      (else
        (return_call $fac-acc
          (i64.sub (local.get 0) (i64.const 1))
          (i64.mul (local.get 0) (local.get 1))
        )
      )
    )
  )

  (func $count (export "count") (param i64) (result i64)
    (if (result i64) (i64.eqz (local.get 0))
      (then (local.get 0))
      (else (return_call $count (i64.sub (local.get 0) (i64.const 1))))
    )
  )

  (func $even (export "even") (param i64) (result i32)
    (if (result i32) (i64.eqz (local.get 0))
      (then (i32.const 44))
      (else (return_call $odd (i64.sub (local.get 0) (i64.const 1))))
    )
  )
  (func $odd (export "odd") (param i64) (result i32)
    (if (result i32) (i64.eqz (local.get 0))
      (then (i32.const 99))
      (else (return_call $even (i64.sub (local.get 0) (i64.const 1))))
    )
  )

  ;; Functions with multiple parameters / multiple results
  (func (export "tailprint_i32_f32") (param i32 f32)
    (return_call $print_i32_f32 (local.get 0) (local.get 1))
  )

  (func $swizzle (param f64 i64) (result i32 f32)
    (i32.wrap_i64 (local.get 1))
    (f32.demote_f64 (local.get 0))
  )

  (func (export "type-f64-i64-to-i32-f32") (param f64 i64) (result i32 f32)
    (return_call $swizzle (local.get 0) (local.get 1))
  )
)


(assert_return (invoke "count" (i64.const 1_000_000)) (i64.const 0))

(assert_return (invoke "even" (i64.const 1_000_000)) (i32.const 44))
(assert_return (invoke "even" (i64.const 1_000_001)) (i32.const 99))
(assert_return (invoke "odd" (i64.const 1_000_000)) (i32.const 99))
(assert_return (invoke "odd" (i64.const 999_999)) (i32.const 44))
