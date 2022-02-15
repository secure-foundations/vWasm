(module
  (type (;0;) (func (param i32)))
  (type (;1;) (func))
  (import "wasi_snapshot_preview1" "proc_exit" (func (;0;) (type 0)))
  (func (;1;) (type 1)
    i32.const 42
    call 0
    unreachable)
  (memory (;0;) 2)
  (export "memory" (memory 0))
  (export "_start" (func 1)))
