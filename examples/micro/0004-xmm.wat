(module
  (func $xmmtest_0
    (result f32)
    f32.const 1.0
    f32.const 2.0
    f32.add
    drop

    f64.const 1.0
    f64.const 2.0
    f64.add
    drop

    f32.const 0.0
  )

  (func $xmmtest_1
    i32.const 1
    f64.convert_i32_u
    f32.demote_f64
    i32.trunc_f32_s
    drop
  )

  (func $xmmtest_2
    f32.const 1.0
    f32.const 2.0
    f32.lt
    drop
  )

  (func $callme
    (param i32 f32 i32 f32 i32 f32 i32 f32 i32 f32 i32 f32)
  )

  (func $xmmtest_3
    i32.const 1
    f32.const 1.0
    i32.const 2
    f32.const 2.0
    i32.const 3
    f32.const 3.0
    i32.const 4
    f32.const 4.0
    i32.const 5
    f32.const 5.0
    i32.const 6
    f32.const 6.0
    call $callme
  )

  (func $callme_spill
	(param f32
		   f32
		   f32
		   f32
		   f32
		   f32
		   f32
		   f32
		   f32)
	local.get 0
	local.get 1
	local.get 2
	local.get 3
	local.get 4
	local.get 5
	local.get 6
	local.get 7
	local.get 8
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
  )

  (func $xmmtest_4
    f32.const 1.0
    f32.const 2.0
    f32.const 3.0
    f32.const 4.0
    f32.const 5.0
    f32.const 6.0
    f32.const 7.0
    f32.const 8.0
    f32.const 9.0
    call $callme_spill
  )

  (func $callme_spillint
	(param i32
		   i32
		   i32
		   i32
		   i32
		   i32
		   i32
		   i32
		   i32)
	local.get 0
	local.get 1
	local.get 2
	local.get 3
	local.get 4
	local.get 5
	local.get 6
	local.get 7
	local.get 8
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
  )

  (func $xmmtest_5
    i32.const 1
    i32.const 2
    i32.const 3
    i32.const 4
    i32.const 5
    i32.const 6
    i32.const 7
    i32.const 8
    i32.const 9
    call $callme_spillint
  )

  (func $callme_spillboth
	(param f32 i32
		   f32 i32
		   f32 i32
		   f32 i32
		   f32 i32
		   f32 i32
		   f32 i32
		   f32 i32
		   f32 i32)
	local.get 0
	local.get 1
	local.get 2
	local.get 3
	local.get 4
	local.get 5
	local.get 6
	local.get 7
	local.get 8
	local.get 9
	local.get 10 
	local.get 11
	local.get 12
	local.get 13
	local.get 14
	local.get 15
	local.get 16
	local.get 17
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
	drop
  )

  (func $xmmtest_6
    f32.const 1
    i32.const 1
    f32.const 2
    i32.const 2
    f32.const 3
    i32.const 3
    f32.const 4
    i32.const 4
    f32.const 5
    i32.const 5
    f32.const 6
    i32.const 6
    f32.const 7
    i32.const 7
    f32.const 8
    i32.const 8
    f32.const 9
    i32.const 9
    call $callme_spillboth
  )
)
