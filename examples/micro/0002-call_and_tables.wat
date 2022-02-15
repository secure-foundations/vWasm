(module
  (func $brtable_deep (result i32)
    block $l0 (result i32)
      block $l1 (result i32)
        block $l2 (result i32)
          block $l3 (result i32)
            block $l4 (result i32)
              block $l5 (result i32)
                block $l6 (result i32)
                  block $l7 (result i32)
                    block $l8 (result i32)
                      block $l9 (result i32)
                        block $l10 (result i32)
                          block $l11 (result i32)
                            block $l12 (result i32)
                              block $l13 (result i32)
                                block $l14 (result i32)
                                  block $l15 (result i32)
                                    block $l16 (result i32)
                                      block $l17 (result i32)
                                        block $l18 (result i32)
                                          block $l19 (result i32)
                                            block $l20 (result i32)
                                              i32.const 10
                                              i32.const 8
                                              br_table $l0 $l1 $l2 $l3 $l4 $l5 $l6 $l7 $l8 $l9 $l10 $l11 $l12 $l13 $l14 $l15 $l16 $l17 $l18 $l19 $l20
                                            end
                                            i32.const 20
                                            drop
                                          end
                                          i32.const 19
                                          drop
                                        end
                                        i32.const 18
                                        drop
                                      end
                                      i32.const 17
                                      drop
                                    end
                                    i32.const 16
                                    drop
                                  end
                                  i32.const 15
                                  drop
                                end
                                i32.const 14
                                drop
                              end
                              i32.const 13
                              drop
                            end
                            i32.const 12
                            drop
                          end
                          i32.const 11
                          drop
                        end
                        i32.const 10
                        drop
                      end
                      i32.const 9
                      drop
                    end
                    i32.const 8
                    drop
                  end
                  i32.const 7
                  drop
                end
                i32.const 6
                drop
              end
              i32.const 5
              drop
            end
            i32.const 4
            drop
          end
          i32.const 3
          drop
        end
        i32.const 2
        drop
      end
      i32.const 1
      drop
    end
    i32.const 0
    drop
  )

  (func $dummy (param i32 i32) (result i32)
    i32.const 0
    i32.const 1
    i32.add
  )

  (func $call_simple
    i32.const 10
    i32.const 20
    call $dummy
    drop
  )

  (func $call_local (local i32 i32)
    i32.const 10
    i32.const 20
    call $dummy
    drop
  )

  (func $dummy_args
	(param i32 i32 i32 i32 i32 i32 i32 i32 i32)
	(result i32)
	i32.const 100
	i32.const 200
	i32.add
  )

  (func $call_args
	(result i32)
	i32.const 1
	i32.const 2
	i32.const 3
	i32.const 4
	i32.const 5
	i32.const 6
	i32.const 7
	i32.const 8
	i32.const 9
	call $dummy_args
  )

  (func $dummy_fargs
	(param f32 f32 f32 f32 f32 f32 f32 f32 f32)
	(result f32)
	local.get 0
  )

  (func $call_fargs
	(result f32)
	(local f32 f32 f32 f32 f32 f32 f32 f32 f32)
	local.get 0
	local.get 1
	local.get 2
	local.get 3
	local.get 4
	local.get 5
	local.get 6
	local.get 7
	local.get 8
	call $dummy_fargs
  )

  (func $dummy_mixed
    (param i32 f32 i64 f64 i32 f32 i64 f64 i32 f32 i64 f64 i32 f32 i64 f64 i32 f32 i64 f64)
	(result i32)
	local.get 0
  )

  (func $call_mixed
	(result i32)
	(local f32 f64 f32 f64 f32 f64 f32 f64 f32 f64)
	i32.const 0
	local.get 0
	i64.const 1
	local.get 1
	i32.const 2
	local.get 2
	i64.const 3
	local.get 3
	i32.const 4
	local.get 4
	i64.const 5
	local.get 5
	i32.const 6
	local.get 6
	i64.const 7
	local.get 7
	i32.const 8
	local.get 8
	i64.const 9
	local.get 9
	call $dummy_mixed
  )

  (type $dummy_sig (func (param i32 i32) (result i32)))

  (func $call_indirect
    i32.const 10
    i32.const 20
    i32.const 3
    call_indirect (type $dummy_sig)
    drop
  )

  (func $call_indirect_local (local i32 i32)
    i32.const 10
    i32.const 20
    i32.const 3
    call_indirect (type $dummy_sig)
    drop
  )

  (export "dummy0" (func $dummy0))

  (func $dummy0 (param i32 i32) (result i32)
    i32.const 0
    i32.const 1
    i32.add
  )

  (func $dummy1 (param i32 i32) (result i32)
    i32.const 0
    i32.const 1
    i32.add
  )

  (func $dummy2 (param i32 i32) (result i32)
    i32.const 0
    i32.const 1
    i32.add
  )

  (func $dummy3 (param i32 i32) (result i32)
    i32.const 0
    i32.const 1
    i32.add
  )

  (func $dummy4 (param i32 i32) (result i32)
    i32.const 0
    i32.const 1
    i32.add
  )

  (table $tbl 5 5 funcref)
  (elem $tbl (i32.const 0) $dummy0 $dummy1 $dummy2 $dummy3 $dummy4)
)
