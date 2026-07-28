(module
  (func $factorial (param i32) (result i32)
    local.get 0
    if (result i32)
      local.get 0
      local.get 0
      i32.const 1
      i32.sub
      call $factorial
      i32.mul
    else
      i32.const 1
    end)
    
  (func (export "call_factorial") (result i32)
    i32.const 5
    call $factorial
  ))
(assert_return (invoke "call_factorial") (i32.const 120))