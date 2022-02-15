(module
  (import "env" "f0" (func (result i32)))
  (import "env" "f1" (func (result i64)))
  (import "env" "f2" (func (result i32)))
  (table 5 5 funcref)
  (elem (i32.const 1) 1 2 3 4)
  (func (result i32) i32.const 3)
  (func (result i64) i64.const 4)
  (func (result i32)
    i32.const 2
    call_indirect (result i32)
  )
)
