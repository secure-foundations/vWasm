(module
  (global $g0 (mut i32) (i32.const 1))
  (func (result i32)
    (block $b0 ;; 0
      (block $b1 ;; 1
        (block $b2 ;; 2
          (block $b3 ;; 3
            (global.get $g0)
            (br_table $b2 $b3 $b1)
          )
          (i32.const 1)
          (global.set $g0)
          (br $b0)
        )
        (i32.const 0)
        (global.set $g0)
        (br $b0)
      )
      (i32.const 100)
      (global.set $g0)
    )
    (global.get $g0)
  )
)
