open Prims






type ('k, 't, 'p, 'g0, 'g1, 'rrel, 'rel, 'sl, 'pos0, 'bpos, 'h,
  'stop) validate_list_inv = unit
let (validate_list_body :
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
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t ->
                      FStar_UInt64.t LowStar_Buffer.buffer -> Prims.bool)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun g0 ->
            fun g1 ->
              fun rrel ->
                fun rel ->
                  fun sl ->
                    fun pos0 ->
                      fun bpos ->
                        let pos1 =
                          LowStar_Monotonic_Buffer.index bpos
                            (FStar_UInt32.uint_to_t Prims.int_zero) in
                        if
                          pos1 =
                            (FStar_Int_Cast.uint32_to_uint64
                               (match sl with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len;_} -> len))
                        then true
                        else
                          (let pos11 = v () () sl pos1 in
                           (let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd' bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) pos11);
                           LowParse_Low_ErrorCode.is_error pos11)
let (validate_list' :
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
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun rrel ->
            fun rel ->
              fun sl ->
                fun pos ->
                  let h0 = FStar_HyperStack_ST.get () in
                  FStar_HyperStack_ST.push_frame ();
                  (let h02 = FStar_HyperStack_ST.get () in
                   let bpos =
                     LowStar_Monotonic_Buffer.malloca pos
                       (FStar_UInt32.uint_to_t Prims.int_one) in
                   let h1 = FStar_HyperStack_ST.get () in
                   C_Loops.do_while
                     (fun uu___2 ->
                        let pos1 =
                          LowStar_Monotonic_Buffer.index bpos
                            (FStar_UInt32.uint_to_t Prims.int_zero) in
                        if
                          pos1 =
                            (FStar_Int_Cast.uint32_to_uint64
                               (match sl with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len;_} -> len))
                        then true
                        else
                          (let pos11 = v () () sl pos1 in
                           (let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd' bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) pos11);
                           LowParse_Low_ErrorCode.is_error pos11));
                   (let posf =
                      LowStar_Monotonic_Buffer.index bpos
                        (FStar_UInt32.uint_to_t Prims.int_zero) in
                    FStar_HyperStack_ST.pop_frame (); posf))
let (validate_list :
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
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun u ->
            fun rrel ->
              fun rel ->
                fun sl ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let h0 = FStar_HyperStack_ST.get () in
                    FStar_HyperStack_ST.push_frame ();
                    (let h02 = FStar_HyperStack_ST.get () in
                     let bpos =
                       LowStar_Monotonic_Buffer.malloca pos
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let h1 = FStar_HyperStack_ST.get () in
                     C_Loops.do_while
                       (fun uu___2 ->
                          let pos1 =
                            LowStar_Monotonic_Buffer.index bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          if
                            pos1 =
                              (FStar_Int_Cast.uint32_to_uint64
                                 (match sl with
                                  | { LowParse_Slice.base = base;
                                      LowParse_Slice.len = len;_} -> len))
                          then true
                          else
                            (let pos11 = v () () sl pos1 in
                             (let h2 = FStar_HyperStack_ST.get () in
                              LowStar_Monotonic_Buffer.upd' bpos
                                (FStar_UInt32.uint_to_t Prims.int_zero) pos11);
                             LowParse_Low_ErrorCode.is_error pos11));
                     (let posf =
                        LowStar_Monotonic_Buffer.index bpos
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      FStar_HyperStack_ST.pop_frame (); posf))

let rec (list_last_pos :
  LowParse_Spec_Base.parser_kind ->
    unit ->
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
                  FStar_UInt32.t -> FStar_UInt32.t -> unit -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun j ->
            fun rrel ->
              fun rel ->
                fun sl ->
                  fun pos ->
                    fun pos' ->
                      fun l ->
                        let h0 = FStar_HyperStack_ST.get () in
                        FStar_HyperStack_ST.push_frame ();
                        (let h1 = FStar_HyperStack_ST.get () in
                         let bgleft =
                           LowStar_Monotonic_Buffer.malloca ()
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let bgright =
                           LowStar_Monotonic_Buffer.malloca ()
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let bpos1 =
                           LowStar_Monotonic_Buffer.malloca pos
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         C_Loops.do_while
                           (fun uu___2 ->
                              let pos1 =
                                LowStar_Monotonic_Buffer.index bpos1
                                  (FStar_UInt32.uint_to_t Prims.int_zero) in
                              LowStar_Monotonic_Buffer.index bgright
                                (FStar_UInt32.uint_to_t Prims.int_zero);
                              (let pos2 =
                                 let h = FStar_HyperStack_ST.get () in
                                 j () () sl pos1 in
                               if pos2 = pos'
                               then true
                               else
                                 (LowStar_Monotonic_Buffer.index bgleft
                                    (FStar_UInt32.uint_to_t Prims.int_zero);
                                  (let h = FStar_HyperStack_ST.get () in
                                   LowStar_Monotonic_Buffer.upd' bgleft
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     ());
                                  (let h = FStar_HyperStack_ST.get () in
                                   LowStar_Monotonic_Buffer.upd' bgright
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     ());
                                  (let h = FStar_HyperStack_ST.get () in
                                   LowStar_Monotonic_Buffer.upd' bpos1
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     pos2);
                                  false)));
                         (let res =
                            LowStar_Monotonic_Buffer.index bpos1
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_HyperStack_ST.pop_frame (); res))