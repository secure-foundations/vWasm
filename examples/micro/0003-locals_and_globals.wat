(module
  (global $g1 (mut i32) (i32.const 1))
  (global $g2 (mut i32) (i32.const 2))

  (export "myglobal" (global $g1))

  (func $argtest_0
	(param i32 i32)
	local.get 0
	local.get 1
	local.set 0
	local.set 1
	i32.const 100
	local.tee 0
	local.tee 1
	drop
  )

  (func $argtest_1
	(param i32 i32)
	(local i32 i32)
	local.get 0
	local.get 1
	local.set 2
	local.set 3
	i32.const 100
	local.tee 3
	local.tee 2
	drop
	local.get 3
	local.get 2
	local.set 0
	local.set 1
  )

  (func $globtest_0
    global.get 0
	global.get 1
	global.set 0
	global.set 1
  )
)
