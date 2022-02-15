(module
  (func $unreachable_0 (result i32)
    i32.const 1
    if (result i32)
      i32.const 0
    else
      unreachable
      drop
    end
  )

  (func $unreachable_1 (result i32)
    i32.const 1
    if
      i32.const 0
      return
    else
      unreachable
      drop
    end
    unreachable
  )

  (func $unreachable_3
    i32.const 1
    if
      br 1
    else
      i32.const 0
      unreachable
    end
  )

  (func $unreachable_4 (result i32)
    i32.const 0
    i32.const 1
    br_if 0
    if
      i32.const 0
      return
    else
      unreachable
      drop
    end
    unreachable
    unreachable
  )
)