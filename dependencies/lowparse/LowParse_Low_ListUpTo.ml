open Prims
type ('k, 't, 'p, 'cond, 'prf, 'rrel, 'rel, 'sl, 'pos0, 'h0, 'bpos, 'h,
  'stop) validate_list_up_to_inv = unit
let (validate_list_up_to_body :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Prims.bool) ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Prims.bool)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t ->
                        FStar_Monotonic_HyperStack.mem ->
                          FStar_UInt64.t LowStar_Buffer.buffer -> Prims.bool)
  =
  fun k ->
    fun t ->
      fun p ->
        fun cond ->
          fun prf ->
            fun v ->
              fun cond_impl ->
                fun rrel ->
                  fun rel ->
                    fun sl ->
                      fun pos0 ->
                        fun h0 ->
                          fun bpos ->
                            let h = FStar_HyperStack_ST.get () in
                            let pos =
                              LowStar_Monotonic_Buffer.index bpos
                                (FStar_UInt32.uint_to_t Prims.int_zero) in
                            let pos1 = v () () sl pos in
                            (let h1 = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd' bpos
                               (FStar_UInt32.uint_to_t Prims.int_zero) pos1);
                            if LowParse_Low_ErrorCode.is_error pos1
                            then true
                            else
                              cond_impl () () sl
                                (FStar_Int_Cast.uint64_to_uint32 pos)
let (validate_list_up_to :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Prims.bool) ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Prims.bool)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun cond ->
          fun prf ->
            fun v ->
              fun cond_impl ->
                fun rrel ->
                  fun rel ->
                    fun sl ->
                      fun pos ->
                        FStar_HyperStack_ST.push_frame ();
                        (let bpos =
                           LowStar_Monotonic_Buffer.malloca pos
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let h2 = FStar_HyperStack_ST.get () in
                         C_Loops.do_while
                           (fun uu___2 ->
                              let h = FStar_HyperStack_ST.get () in
                              let pos1 =
                                LowStar_Monotonic_Buffer.index bpos
                                  (FStar_UInt32.uint_to_t Prims.int_zero) in
                              let pos11 = v () () sl pos1 in
                              (let h1 = FStar_HyperStack_ST.get () in
                               LowStar_Monotonic_Buffer.upd' bpos
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 pos11);
                              if LowParse_Low_ErrorCode.is_error pos11
                              then true
                              else
                                cond_impl () () sl
                                  (FStar_Int_Cast.uint64_to_uint32 pos1));
                         (let res =
                            LowStar_Monotonic_Buffer.index bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          FStar_HyperStack_ST.pop_frame (); res))
type ('k, 't, 'p, 'cond, 'prf, 'rrel, 'rel, 'sl, 'pos0, 'h0, 'bpos, 'h,
  'stop) jump_list_up_to_inv = unit
let (jump_list_up_to_body :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Prims.bool) ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Prims.bool)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t ->
                        FStar_Monotonic_HyperStack.mem ->
                          FStar_UInt32.t LowStar_Buffer.buffer -> Prims.bool)
  =
  fun k ->
    fun t ->
      fun p ->
        fun cond ->
          fun prf ->
            fun j ->
              fun cond_impl ->
                fun rrel ->
                  fun rel ->
                    fun sl ->
                      fun pos0 ->
                        fun h0 ->
                          fun bpos ->
                            let h = FStar_HyperStack_ST.get () in
                            let pos =
                              LowStar_Monotonic_Buffer.index bpos
                                (FStar_UInt32.uint_to_t Prims.int_zero) in
                            let pos1 = j () () sl pos in
                            (let h1 = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd' bpos
                               (FStar_UInt32.uint_to_t Prims.int_zero) pos1);
                            cond_impl () () sl pos
let (jump_list_up_to :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Prims.bool) ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Prims.bool)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun cond ->
          fun prf ->
            fun j ->
              fun cond_impl ->
                fun rrel ->
                  fun rel ->
                    fun sl ->
                      fun pos ->
                        FStar_HyperStack_ST.push_frame ();
                        (let bpos =
                           LowStar_Monotonic_Buffer.malloca pos
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let h2 = FStar_HyperStack_ST.get () in
                         C_Loops.do_while
                           (fun uu___2 ->
                              let h = FStar_HyperStack_ST.get () in
                              let pos1 =
                                LowStar_Monotonic_Buffer.index bpos
                                  (FStar_UInt32.uint_to_t Prims.int_zero) in
                              let pos11 = j () () sl pos1 in
                              (let h1 = FStar_HyperStack_ST.get () in
                               LowStar_Monotonic_Buffer.upd' bpos
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 pos11);
                              cond_impl () () sl pos1);
                         (let res =
                            LowStar_Monotonic_Buffer.index bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          FStar_HyperStack_ST.pop_frame (); res))