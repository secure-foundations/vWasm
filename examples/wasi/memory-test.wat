(module
  (type (;0;) (func (param i32)))
  (type (;1;) (func (param i32 i32 i32 i32) (result i32)))
  (type (;2;) (func))
  (import "wasi_snapshot_preview1" "proc_exit" (func (;0;) (type 0)))
  (import "wasi_snapshot_preview1" "fd_write" (func (;1;) (type 1)))
  (func (;2;) (type 2)
    block  ;; label = @1
      block  ;; label = @2
        i32.const 1
        i32.const 8
        i32.const 1
        i32.const 0
        call 1
        i32.eqz
        if  ;; label = @3
        else
          i32.const 1
          call 0
          unreachable
        end
      end
      block (result i32)  ;; label = @2
        memory.size
        i32.const 0
        i32.gt_u
      end
      if  ;; label = @2
        block  ;; label = @3
          i32.const 1
          i32.const 16
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
      else
        block  ;; label = @3
          i32.const 1
          i32.const 24
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
        block  ;; label = @3
          i32.const 2
          call 0
          unreachable
        end
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        i32.const 1
        i32.const 32
        i32.const 1
        i32.const 0
        call 1
        i32.eqz
        if  ;; label = @3
        else
          i32.const 1
          call 0
          unreachable
        end
      end
      block (result i32)  ;; label = @2
        memory.size
        i32.const 0
        i32.gt_u
      end
      if  ;; label = @2
        block  ;; label = @3
          i32.const 1
          i32.const 16
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
      else
        block  ;; label = @3
          i32.const 1
          i32.const 24
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
        block  ;; label = @3
          i32.const 2
          call 0
          unreachable
        end
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        i32.const 1
        i32.const 40
        i32.const 1
        i32.const 0
        call 1
        i32.eqz
        if  ;; label = @3
        else
          i32.const 1
          call 0
          unreachable
        end
      end
      block (result i32)  ;; label = @2
        i32.const 0
        memory.grow
        memory.size
        i32.eq
      end
      if  ;; label = @2
        block  ;; label = @3
          i32.const 1
          i32.const 16
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
      else
        block  ;; label = @3
          i32.const 1
          i32.const 24
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
        block  ;; label = @3
          i32.const 2
          call 0
          unreachable
        end
      end
    end
    block  ;; label = @1
      block  ;; label = @2
        i32.const 1
        i32.const 48
        i32.const 1
        i32.const 0
        call 1
        i32.eqz
        if  ;; label = @3
        else
          i32.const 1
          call 0
          unreachable
        end
      end
      block (result i32)  ;; label = @2
        i32.const 1
        memory.grow
        memory.size
        i32.const 1
        i32.sub
        i32.eq
      end
      if  ;; label = @2
        block  ;; label = @3
          i32.const 1
          i32.const 16
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
      else
        block  ;; label = @3
          i32.const 1
          i32.const 24
          i32.const 1
          i32.const 0
          call 1
          i32.eqz
          if  ;; label = @4
          else
            i32.const 1
            call 0
            unreachable
          end
        end
        block  ;; label = @3
          i32.const 2
          call 0
          unreachable
        end
      end
    end)
  (memory (;0;) 2)
  (export "memory" (memory 0))
  (export "_start" (func 2))
  (data (;0;) (i32.const 0) "\00\00\00\00\00\00\00\008\00\00\00/\00\00\00g\00\00\00\0c\00\00\00s\00\00\00\16\00\00\00\89\00\00\001\00\00\00\ba\00\00\00%\00\00\00\df\00\00\00%\00\00\00[ ] Testing memory size: signed greater than 0\0a[+] Success\0a[!] Failure. Exiting.\0a[ ] Testing memory size: unsigned greater than 0\0a[ ] Testing memory resize by 0 pages\0a[ ] Testing memory resize by 1 pages\0a"))
