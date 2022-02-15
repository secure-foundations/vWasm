(module
  (func $if_simple
    i32.const 0
    if
      i32.const 0
      drop
    else
      i32.const 1
      drop
    end
  )

  (func $if_stack (result i32)
    i32.const 0
    if (result i32)
      i32.const 0
    else
		  i32.const 1
    end
  )

  (func $if_returnif (result i32)
    i32.const 0
    if (result i32)
      i32.const 0
      return 
    else
      i32.const 1
    end
  )

  (func $if_returnelse (result i32)
    i32.const 0
    if (result i32)
      i32.const 0
    else
      i32.const 1
      return
    end
  )

  (func $if_returnboth (result i32)
    i32.const 0
    if (result i32)
      i32.const 0
      return
    else
      i32.const 1
      return
    end
  )
)