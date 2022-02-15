(module
  (func $loop_empty
    i32.const 0
    loop
    end
    i32.const 1
    drop
    drop
  )

  (func $loop_infinite
    loop $l0
      br $l0
    end
  )

  (func $loop_simple
    block $b0
      loop $l0
        i32.const 0
        br_if $l0
        br $b0
      end
      i32.const 1234 ;; unreachable
      drop
    end
    i32.const 5678
    drop
  )

  (func $loop_exits (result i32)
    block $b0
      loop $l0
        i32.const 0
        br_if $l0
        i32.const 1
        br_if $b0
        i32.const 2
        br_if $l0
        i32.const 3
        br_if $b0
        i32.const 4
        return
      end
    end
    i32.const 1234
  )

  (func $loop_deep (result i32)
    loop $l0 (result i32)
      loop $l1 (result i32)
        loop $l2 (result i32)
          loop $l3 (result i32)
            loop $l4 (result i32)
              loop $l5 (result i32)
                loop $l6 (result i32)
                  loop $l7 (result i32)
                    loop $l8 (result i32)
                      loop $l9 (result i32)
                        loop $l10 (result i32)
                          loop $l11 (result i32)
                            loop $l12 (result i32)
                              loop $l13 (result i32)
                                loop $l14 (result i32)
                                  loop $l15 (result i32)
                                    loop $l16 (result i32)
                                      loop $l17 (result i32)
                                        loop $l18 (result i32)
                                          loop $l19 (result i32)
                                            loop $l20 (result i32)
                                              i32.const 0
                                              i32.const 1
                                              br_if $l0
                                            end
                                          end
                                        end
                                      end
                                    end
                                  end
                                end
                              end
                            end
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  )

  (func $loop_mixed
    block $b0
      loop $l0
        i32.const 0
        drop
        block $b1
          loop $l1
          i32.const 1
          drop
            block $b2
              loop $l2
                i32.const 2
                drop
                br $b0
                br $l0
                br $b1
                br $l1
                br $b2
                br $l2
              end
            end
            i32.const 8002
            drop
          end
        end
        i32.const 8001
        drop
      end
    end
    i32.const 8000
    drop
  )
)