open Prims






let (validate_nlist :
  FStar_UInt32.t ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt64.t -> FStar_UInt64.t)
            ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun n ->
    fun k ->
      fun t ->
        fun p ->
          fun v ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h0 = FStar_HyperStack_ST.get () in
                    FStar_HyperStack_ST.push_frame ();
                    (let bpos1 =
                       LowStar_Monotonic_Buffer.malloca pos
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let br =
                       LowStar_Monotonic_Buffer.malloca n
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let h1 = FStar_HyperStack_ST.get () in
                     C_Loops.do_while
                       (fun uu___2 ->
                          let r =
                            LowStar_Monotonic_Buffer.index br
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          if r = (FStar_UInt32.uint_to_t Prims.int_zero)
                          then true
                          else
                            (let pos1 =
                               LowStar_Monotonic_Buffer.index bpos1
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let pos2 = v () () input pos1 in
                             (let h = FStar_HyperStack_ST.get () in
                              LowStar_Monotonic_Buffer.upd' br
                                (FStar_UInt32.uint_to_t Prims.int_zero)
                                (FStar_UInt32.sub r
                                   (FStar_UInt32.uint_to_t Prims.int_one)));
                             (let h = FStar_HyperStack_ST.get () in
                              LowStar_Monotonic_Buffer.upd' bpos1
                                (FStar_UInt32.uint_to_t Prims.int_zero) pos2);
                             LowParse_Low_ErrorCode.is_error pos2));
                     (let res =
                        LowStar_Monotonic_Buffer.index bpos1
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      FStar_HyperStack_ST.pop_frame (); res))
let (jump_nlist :
  FStar_UInt32.t ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun n ->
    fun k ->
      fun t ->
        fun p ->
          fun v ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h0 = FStar_HyperStack_ST.get () in
                    FStar_HyperStack_ST.push_frame ();
                    (let bpos1 =
                       LowStar_Monotonic_Buffer.malloca pos
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let br =
                       LowStar_Monotonic_Buffer.malloca n
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let h1 = FStar_HyperStack_ST.get () in
                     C_Loops.do_while
                       (fun uu___2 ->
                          let r =
                            LowStar_Monotonic_Buffer.index br
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          if r = (FStar_UInt32.uint_to_t Prims.int_zero)
                          then true
                          else
                            (let pos1 =
                               LowStar_Monotonic_Buffer.index bpos1
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let pos2 = v () () input pos1 in
                             (let h = FStar_HyperStack_ST.get () in
                              LowStar_Monotonic_Buffer.upd' br
                                (FStar_UInt32.uint_to_t Prims.int_zero)
                                (FStar_UInt32.sub r
                                   (FStar_UInt32.uint_to_t Prims.int_one)));
                             (let h = FStar_HyperStack_ST.get () in
                              LowStar_Monotonic_Buffer.upd' bpos1
                                (FStar_UInt32.uint_to_t Prims.int_zero) pos2);
                             false));
                     (let res =
                        LowStar_Monotonic_Buffer.index bpos1
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      FStar_HyperStack_ST.pop_frame (); res))


let (validate_vclist :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt64.t -> FStar_UInt64.t)
            ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    (unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
                      ->
                      unit ->
                        unit ->
                          (Obj.t, Obj.t) LowParse_Slice.slice ->
                            FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun lk ->
        fun lp ->
          fun lv ->
            fun lr ->
              fun k ->
                fun t ->
                  fun p ->
                    fun v ->
                      fun rrel ->
                        fun rel ->
                          fun input ->
                            fun pos ->
                              let h = FStar_HyperStack_ST.get () in
                              let pos1 = lv () () input pos in
                              if LowParse_Low_ErrorCode.is_error pos1
                              then pos1
                              else
                                (let n =
                                   lr () () input
                                     (FStar_Int_Cast.uint64_to_uint32 pos) in
                                 if
                                   (FStar_UInt32.lt n min) ||
                                     (FStar_UInt32.lt max n)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_generic
                                 else
                                   (let h0 = FStar_HyperStack_ST.get () in
                                    FStar_HyperStack_ST.push_frame ();
                                    (let bpos1 =
                                       LowStar_Monotonic_Buffer.malloca pos1
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_one) in
                                     let br =
                                       LowStar_Monotonic_Buffer.malloca n
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_one) in
                                     let h1 = FStar_HyperStack_ST.get () in
                                     C_Loops.do_while
                                       (fun uu___4 ->
                                          let r =
                                            LowStar_Monotonic_Buffer.index br
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero) in
                                          if
                                            r =
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)
                                          then true
                                          else
                                            (let pos11 =
                                               LowStar_Monotonic_Buffer.index
                                                 bpos1
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero) in
                                             let pos2 = v () () input pos11 in
                                             (let h2 =
                                                FStar_HyperStack_ST.get () in
                                              LowStar_Monotonic_Buffer.upd'
                                                br
                                                (FStar_UInt32.uint_to_t
                                                   Prims.int_zero)
                                                (FStar_UInt32.sub r
                                                   (FStar_UInt32.uint_to_t
                                                      Prims.int_one)));
                                             (let h2 =
                                                FStar_HyperStack_ST.get () in
                                              LowStar_Monotonic_Buffer.upd'
                                                bpos1
                                                (FStar_UInt32.uint_to_t
                                                   Prims.int_zero) pos2);
                                             LowParse_Low_ErrorCode.is_error
                                               pos2));
                                     (let res =
                                        LowStar_Monotonic_Buffer.index bpos1
                                          (FStar_UInt32.uint_to_t
                                             Prims.int_zero) in
                                      FStar_HyperStack_ST.pop_frame (); res))))
let (jump_vclist :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    (unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      unit ->
                        unit ->
                          (Obj.t, Obj.t) LowParse_Slice.slice ->
                            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun lk ->
        fun lp ->
          fun lv ->
            fun lr ->
              fun k ->
                fun t ->
                  fun p ->
                    fun v ->
                      fun rrel ->
                        fun rel ->
                          fun input ->
                            fun pos ->
                              let h = FStar_HyperStack_ST.get () in
                              let pos1 = lv () () input pos in
                              let n = lr () () input pos in
                              let h0 = FStar_HyperStack_ST.get () in
                              FStar_HyperStack_ST.push_frame ();
                              (let bpos1 =
                                 LowStar_Monotonic_Buffer.malloca pos1
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let br =
                                 LowStar_Monotonic_Buffer.malloca n
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let h1 = FStar_HyperStack_ST.get () in
                               C_Loops.do_while
                                 (fun uu___2 ->
                                    let r =
                                      LowStar_Monotonic_Buffer.index br
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero) in
                                    if
                                      r =
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)
                                    then true
                                    else
                                      (let pos11 =
                                         LowStar_Monotonic_Buffer.index bpos1
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero) in
                                       let pos2 = v () () input pos11 in
                                       (let h2 = FStar_HyperStack_ST.get () in
                                        LowStar_Monotonic_Buffer.upd' br
                                          (FStar_UInt32.uint_to_t
                                             Prims.int_zero)
                                          (FStar_UInt32.sub r
                                             (FStar_UInt32.uint_to_t
                                                Prims.int_one)));
                                       (let h2 = FStar_HyperStack_ST.get () in
                                        LowStar_Monotonic_Buffer.upd' bpos1
                                          (FStar_UInt32.uint_to_t
                                             Prims.int_zero) pos2);
                                       false));
                               (let res =
                                  LowStar_Monotonic_Buffer.index bpos1
                                    (FStar_UInt32.uint_to_t Prims.int_zero) in
                                FStar_HyperStack_ST.pop_frame (); res))

