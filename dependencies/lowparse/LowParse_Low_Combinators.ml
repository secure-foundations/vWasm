open Prims


let (validate_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
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
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun p1' ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun p2' ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let pos1 = p1' () () input pos in
                          if LowParse_Low_ErrorCode.is_error pos1
                          then pos1
                          else p2' () () input pos1
let (jump_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
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
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun p1' ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun p2' ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let uu___ = p1' () () input pos in
                          p2' () () input uu___
let (read_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  (unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> Obj.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> (Obj.t * Obj.t))
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun p1' ->
          fun r1 ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun r2 ->
                    fun uu___ ->
                      fun uu___1 ->
                        fun sl ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            let x1 = r1 () () sl pos in
                            let pos2 = p1' () () sl pos in
                            let x2 = r2 () () sl pos2 in (x1, x2)
let (serialize32_nondep_then_aux :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t ->
                       unit ->
                         unit ->
                           (LowParse_Bytes.byte, Obj.t, Obj.t)
                             LowStar_Monotonic_Buffer.mbuffer ->
                             FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      Obj.t ->
                        Obj.t ->
                          unit ->
                            unit ->
                              (LowParse_Bytes.byte, Obj.t, Obj.t)
                                LowStar_Monotonic_Buffer.mbuffer ->
                                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun x1 ->
                        fun x2 ->
                          fun rrel ->
                            fun rel ->
                              fun b ->
                                fun pos ->
                                  let len1 =
                                    let h0 = FStar_HyperStack_ST.get () in
                                    let res = s1' x1 () () b pos in
                                    let h1 = FStar_HyperStack_ST.get () in
                                    let pos' = FStar_UInt32.add pos res in
                                    res in
                                  let pos1 = FStar_UInt32.add pos len1 in
                                  let len2 =
                                    let h0 = FStar_HyperStack_ST.get () in
                                    let res = s2' x2 () () b pos1 in
                                    let h1 = FStar_HyperStack_ST.get () in
                                    let pos' = FStar_UInt32.add pos1 res in
                                    res in
                                  let h1 = FStar_HyperStack_ST.get () in
                                  FStar_UInt32.add len1 len2
let (serialize32_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t ->
                       unit ->
                         unit ->
                           (LowParse_Bytes.byte, Obj.t, Obj.t)
                             LowStar_Monotonic_Buffer.mbuffer ->
                             FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      (Obj.t * Obj.t) ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun b ->
                              fun pos ->
                                match x with
                                | (x1, x2) ->
                                    let len1 =
                                      let h0 = FStar_HyperStack_ST.get () in
                                      let res = s1' x1 () () b pos in
                                      let h1 = FStar_HyperStack_ST.get () in
                                      let pos' = FStar_UInt32.add pos res in
                                      res in
                                    let pos1 = FStar_UInt32.add pos len1 in
                                    let len2 =
                                      let h0 = FStar_HyperStack_ST.get () in
                                      let res = s2' x2 () () b pos1 in
                                      let h1 = FStar_HyperStack_ST.get () in
                                      let pos' = FStar_UInt32.add pos1 res in
                                      res in
                                    let h1 = FStar_HyperStack_ST.get () in
                                    FStar_UInt32.add len1 len2


let (validate_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
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
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun p1' ->
            fun f2 ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        p1' () () input pos
let (jump_synth :
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
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun p1' ->
            fun f2 ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        p1' () () input pos

let (validate_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  (Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun v1 ->
          fun r1 ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun v2 ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            let pos1 = v1 () () input pos in
                            if LowParse_Low_ErrorCode.is_error pos1
                            then pos1
                            else
                              (let x =
                                 r1 () () input
                                   (FStar_Int_Cast.uint64_to_uint32 pos) in
                               v2 x () () input pos1)
let (jump_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  (Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun v1 ->
          fun r1 ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun v2 ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            let pos1 = v1 () () input pos in
                            let x = r1 () () input pos in
                            v2 x () () input pos1
let (jump_dtuple2_constant_size_dsnd :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                FStar_UInt32.t ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun v1 ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun sz ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let pos1 = v1 () () input pos in
                          let h1 = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos1 sz
let (read_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  (Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> Obj.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> (Obj.t, Obj.t) Prims.dtuple2)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun v1 ->
          fun r1 ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun r2 ->
                    fun uu___ ->
                      fun uu___1 ->
                        fun sl ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            let x1 = r1 () () sl pos in
                            let pos2 = v1 () () sl pos in
                            let x2 = r2 x1 () () sl pos2 in
                            Prims.Mkdtuple2 (x1, x2)
let (serialize32_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t ->
                       Obj.t ->
                         unit ->
                           unit ->
                             (LowParse_Bytes.byte, Obj.t, Obj.t)
                               LowStar_Monotonic_Buffer.mbuffer ->
                               FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      (Obj.t, Obj.t) Prims.dtuple2 ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun x ->
                        fun uu___ ->
                          fun uu___1 ->
                            fun b ->
                              fun pos ->
                                match x with
                                | Prims.Mkdtuple2 (x1, x2) ->
                                    let len1 =
                                      let h0 = FStar_HyperStack_ST.get () in
                                      let res = s1' x1 () () b pos in
                                      let h1 = FStar_HyperStack_ST.get () in
                                      let pos' = FStar_UInt32.add pos res in
                                      res in
                                    let pos1 = FStar_UInt32.add pos len1 in
                                    let len2 =
                                      let h0 = FStar_HyperStack_ST.get () in
                                      let res = s2' x1 x2 () () b pos1 in
                                      let h1 = FStar_HyperStack_ST.get () in
                                      let pos' = FStar_UInt32.add pos1 res in
                                      res in
                                    let h1 = FStar_HyperStack_ST.get () in
                                    FStar_UInt32.add len1 len2
let validate_ret :
  't .
    't ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt64.t -> FStar_UInt64.t
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            if
              FStar_UInt64.lt
                (FStar_UInt64.sub
                   (FStar_Int_Cast.uint32_to_uint64
                      (match sl with
                       | { LowParse_Slice.base = base;
                           LowParse_Slice.len = len;_} -> len)) pos)
                (FStar_UInt64.uint_to_t Prims.int_zero)
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else FStar_UInt64.add pos (FStar_UInt64.uint_to_t Prims.int_zero)
let (validate_empty :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            if
              FStar_UInt64.lt
                (FStar_UInt64.sub
                   (FStar_Int_Cast.uint32_to_uint64
                      (match sl with
                       | { LowParse_Slice.base = base;
                           LowParse_Slice.len = len;_} -> len)) pos)
                (FStar_UInt64.uint_to_t Prims.int_zero)
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else FStar_UInt64.add pos (FStar_UInt64.uint_to_t Prims.int_zero)
let (validate_false :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            LowParse_Low_ErrorCode.validator_error_generic
let (jump_empty :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_zero)
let (jump_false :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_zero)
let read_ret :
  't .
    't ->
      unit ->
        unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 't
  =
  fun v ->
    fun rrel ->
      fun rel -> fun sl -> fun pos -> let h = FStar_HyperStack_ST.get () in v
let (read_empty :
  unit ->
    unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> unit)
  =
  fun rrel ->
    fun rel -> fun sl -> fun pos -> let h = FStar_HyperStack_ST.get () in ()
let (read_false :
  unit ->
    unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> unit)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          LowStar_Failure.failwith "read_false: should not be called"
let serialize32_ret :
  't .
    't ->
      unit ->
        't ->
          unit ->
            unit ->
              (LowParse_Bytes.byte, Obj.t, Obj.t)
                LowStar_Monotonic_Buffer.mbuffer ->
                FStar_UInt32.t -> FStar_UInt32.t
  =
  fun v ->
    fun v_unique ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 -> fun uu___4 -> FStar_UInt32.uint_to_t Prims.int_zero
let (serialize32_empty :
  unit ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 -> fun uu___4 -> FStar_UInt32.uint_to_t Prims.int_zero
let (serialize32_false :
  unit ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 -> fun uu___4 -> FStar_UInt32.uint_to_t Prims.int_zero

let (validate_lift_parser :
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
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in v () () input pos
let (jump_lift_parser :
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
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in v () () input pos
let clens_synth :
  't1 't2 . unit -> unit -> ('t1, 't2) LowParse_Low_Base_Spec.clens =
  fun f ->
    fun g ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }



let (accessor_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f ->
            fun g ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos -> let h = FStar_HyperStack_ST.get () in pos
let clens_synth_inv :
  't1 't2 . unit -> unit -> ('t2, 't1) LowParse_Low_Base_Spec.clens =
  fun f ->
    fun g ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }



let (accessor_synth_inv :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f ->
            fun g ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos -> let h = FStar_HyperStack_ST.get () in pos
let clens_fst :
  't1 't2 . unit -> (('t1 * 't2), 't1) LowParse_Low_Base_Spec.clens =
  fun uu___ ->
    {
      LowParse_Low_Base_Spec.clens_cond = ();
      LowParse_Low_Base_Spec.clens_get = ()
    }
let clens_snd :
  't1 't2 . unit -> (('t1 * 't2), 't2) LowParse_Low_Base_Spec.clens =
  fun uu___ ->
    {
      LowParse_Low_Base_Spec.clens_cond = ();
      LowParse_Low_Base_Spec.clens_get = ()
    }











let (accessor_fst :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun sq ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos -> let h = FStar_HyperStack_ST.get () in pos
let (accessor_fst_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens ->
                unit ->
                  (unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    LowParse_Spec_Base.parser_kind ->
                      unit ->
                        unit ->
                          unit ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun k' ->
          fun t' ->
            fun p' ->
              fun cl ->
                fun g ->
                  fun a ->
                    fun k2 ->
                      fun t2 ->
                        fun p2 ->
                          fun u ->
                            fun rrel ->
                              fun rel ->
                                fun input ->
                                  fun pos ->
                                    let h = FStar_HyperStack_ST.get () in
                                    let pos2 =
                                      let h1 = FStar_HyperStack_ST.get () in
                                      pos in
                                    let pos3 = a () () input pos2 in pos3
let (accessor_then_fst :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    (Obj.t, (Obj.t * Obj.t)) LowParse_Low_Base_Spec.clens ->
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
  fun k0 ->
    fun t0 ->
      fun p0 ->
        fun k1 ->
          fun t1 ->
            fun p1 ->
              fun k2 ->
                fun t2 ->
                  fun p2 ->
                    fun cl ->
                      fun g ->
                        fun a ->
                          fun rrel ->
                            fun rel ->
                              fun input ->
                                fun pos ->
                                  let h = FStar_HyperStack_ST.get () in
                                  let pos2 = a () () input pos in
                                  let pos3 =
                                    let h1 = FStar_HyperStack_ST.get () in
                                    pos2 in
                                  pos3
let (accessor_snd :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun j1 ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let res = j1 () () input pos in res
let (accessor_then_snd :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    (Obj.t, (Obj.t * Obj.t)) LowParse_Low_Base_Spec.clens ->
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
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k0 ->
    fun t0 ->
      fun p0 ->
        fun k1 ->
          fun t1 ->
            fun p1 ->
              fun k2 ->
                fun t2 ->
                  fun p2 ->
                    fun cl ->
                      fun g ->
                        fun a ->
                          fun j1 ->
                            fun rrel ->
                              fun rel ->
                                fun input ->
                                  fun pos ->
                                    let h = FStar_HyperStack_ST.get () in
                                    let pos2 = a () () input pos in
                                    let pos3 =
                                      let h1 = FStar_HyperStack_ST.get () in
                                      let res = j1 () () input pos2 in res in
                                    pos3
let (make_total_constant_size_reader :
  Prims.nat ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          unit ->
            (unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> Obj.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> Obj.t)
  =
  fun sz ->
    fun sz' ->
      fun t ->
        fun f ->
          fun u ->
            fun f' ->
              fun rrel ->
                fun rel ->
                  fun sl ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      f' () ()
                        (match sl with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len;_} -> base) pos

let (validate_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            unit ->
              (Obj.t -> Prims.bool) ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v32 ->
          fun p32 ->
            fun f ->
              fun f' ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let res = v32 () () input pos in
                        if LowParse_Low_ErrorCode.is_error res
                        then res
                        else
                          (let va =
                             p32 () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           if Prims.op_Negation (f' va)
                           then
                             LowParse_Low_ErrorCode.validator_error_generic
                           else res)
let (validate_filter_with_error_code :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            unit ->
              (Obj.t -> Prims.bool) ->
                FStar_UInt64.t ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v32 ->
          fun p32 ->
            fun f ->
              fun f' ->
                fun c ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let res = v32 () () input pos in
                          if LowParse_Low_ErrorCode.is_error res
                          then
                            LowParse_Low_ErrorCode.maybe_set_validator_error_pos_and_code
                              res pos c
                          else
                            (let va =
                               p32 () () input
                                 (FStar_Int_Cast.uint64_to_uint32 pos) in
                             if Prims.op_Negation (f' va)
                             then
                               LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                                 LowParse_Low_ErrorCode.validator_error_generic
                                 pos c
                             else res)
let validate_filter_ret :
  't .
    't ->
      unit ->
        ('t -> Prims.bool) ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt64.t -> FStar_UInt64.t
  =
  fun r ->
    fun f ->
      fun f' ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                if Prims.op_Negation (f' r)
                then LowParse_Low_ErrorCode.validator_error_generic
                else pos
let validate_filter_ret_with_error_code :
  't .
    't ->
      unit ->
        ('t -> Prims.bool) ->
          FStar_UInt64.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t
  =
  fun r ->
    fun f ->
      fun f' ->
        fun c ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  if Prims.op_Negation (f' r)
                  then
                    LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                      LowParse_Low_ErrorCode.validator_error_generic pos c
                  else pos
let (jump_filter :
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
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun f ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in j () () input pos
let (read_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
          ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> Obj.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun f ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in p32 () () input pos
let (write_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              Obj.t ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun f ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let res = s32 x () () input pos in
                        let h = FStar_HyperStack_ST.get () in res
let (write_filter_weak :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              Obj.t ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun f ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let res = s32 x () () input pos in
                        let h = FStar_HyperStack_ST.get () in res
let (serialize32_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              Obj.t ->
                unit ->
                  unit ->
                    (LowParse_Bytes.byte, Obj.t, Obj.t)
                      LowStar_Monotonic_Buffer.mbuffer ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun f ->
              fun x ->
                fun rrel ->
                  fun rel -> fun input -> fun pos -> s32 x () () input pos
let (read_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> Obj.t) ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Obj.t)
                ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> Obj.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun f2' ->
              fun p1' ->
                fun u ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let res = p1' () () input pos in f2' res
let (read_synth' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> Obj.t) ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> Obj.t)
              ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> Obj.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun p1' ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let res = p1' () () input pos in f2 res
let (read_inline_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> Obj.t) ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Obj.t)
                ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> Obj.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun f2' ->
              fun p1' ->
                fun u ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let uu___ = p1' () () input pos in f2' uu___
let (read_inline_synth' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> Obj.t) ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> Obj.t)
              ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> Obj.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun p1' ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let uu___ = p1' () () input pos in f2 uu___
let (write_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              unit ->
                unit ->
                  (Obj.t -> Obj.t) ->
                    unit ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun t2 ->
              fun f2 ->
                fun g1 ->
                  fun g1' ->
                    fun u ->
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos ->
                                let pos' = s1' (g1' x) () () input pos in
                                let h = FStar_HyperStack_ST.get () in pos'
let (write_synth_weak :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              unit ->
                unit ->
                  (Obj.t -> Obj.t) ->
                    unit ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun t2 ->
              fun f2 ->
                fun g1 ->
                  fun g1' ->
                    fun u ->
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos ->
                                let pos' = s1' (g1' x) () () input pos in
                                let h = FStar_HyperStack_ST.get () in pos'
let (serialize32_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            unit ->
              unit ->
                unit ->
                  (Obj.t -> Obj.t) ->
                    unit ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun t2 ->
              fun f2 ->
                fun g1 ->
                  fun g1' ->
                    fun u ->
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos -> s1' (g1' x) () () input pos
let (validate_filter_and_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            unit ->
              (Obj.t -> Prims.bool) ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    unit ->
                      (Obj.t ->
                         unit ->
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
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun v1 ->
          fun p1' ->
            fun f ->
              fun f' ->
                fun k2 ->
                  fun t2 ->
                    fun p2 ->
                      fun v2 ->
                        fun u ->
                          fun rrel ->
                            fun rel ->
                              fun input ->
                                fun pos ->
                                  let h = FStar_HyperStack_ST.get () in
                                  let res = v1 () () input pos in
                                  if LowParse_Low_ErrorCode.is_error res
                                  then res
                                  else
                                    (let va =
                                       p1' () () input
                                         (FStar_Int_Cast.uint64_to_uint32 pos) in
                                     if f' va
                                     then v2 va () () input res
                                     else
                                       LowParse_Low_ErrorCode.validator_error_generic)
let (validate_weaken :
  LowParse_Spec_Base.parser_kind ->
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
  fun k1 ->
    fun k2 ->
      fun t ->
        fun p2 ->
          fun v2 ->
            fun sq ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      v2 () () input pos
let (jump_weaken :
  LowParse_Spec_Base.parser_kind ->
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
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun k2 ->
      fun t ->
        fun p2 ->
          fun v2 ->
            fun sq ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      v2 () () input pos
let (validate_strengthen :
  LowParse_Spec_Base.parser_kind ->
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
  fun k2 ->
    fun k1 ->
      fun t ->
        fun p1 ->
          fun v1 ->
            fun sq ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      v1 () () input pos
let (validate_compose_context :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Obj.t) ->
          unit ->
            unit ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                ->
                Obj.t ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun pk ->
    fun kt1 ->
      fun kt2 ->
        fun f ->
          fun t ->
            fun p ->
              fun v ->
                fun k ->
                  fun rrel ->
                    fun rel ->
                      fun input -> fun pos -> v (f k) () () input pos
let (jump_compose_context :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Obj.t) ->
          unit ->
            unit ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
                Obj.t ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun pk ->
    fun kt1 ->
      fun kt2 ->
        fun f ->
          fun t ->
            fun p ->
              fun v ->
                fun k ->
                  fun rrel ->
                    fun rel ->
                      fun input -> fun pos -> v (f k) () () input pos
let clens_tagged_union_tag :
  'tagut 'dataut . unit -> ('dataut, 'tagut) LowParse_Low_Base_Spec.clens =
  fun tag_of_data ->
    {
      LowParse_Low_Base_Spec.clens_cond = ();
      LowParse_Low_Base_Spec.clens_get = ()
    }


let (accessor_tagged_union_tag :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun tag_t ->
      fun pt ->
        fun data_t ->
          fun tag_of_data ->
            fun k ->
              fun p ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos -> let h = FStar_HyperStack_ST.get () in pos
let clens_tagged_union_payload :
  'tagut 'dataut .
    unit -> 'tagut -> ('dataut, 'dataut) LowParse_Low_Base_Spec.clens
  =
  fun tag_of_data ->
    fun t ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }




let (accessor_tagged_union_payload :
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
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  Obj.t ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun tag_t ->
      fun pt ->
        fun jt ->
          fun data_t ->
            fun tag_of_data ->
              fun k ->
                fun p ->
                  fun t ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            let res = jt () () input pos in res