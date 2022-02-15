(module
  (import "env" "f" (func $f (param i32) (result i32)))
  (func (param i32) (result i32)
    (i32.const 10)
    (call $f)
    (call 1)
  )
)
