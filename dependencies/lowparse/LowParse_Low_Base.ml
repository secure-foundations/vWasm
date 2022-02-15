open Prims
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'g) accessor =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
let (make_accessor_from_pure :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens ->
                unit ->
                  (unit -> FStar_UInt32.t) ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun k2 ->
          fun t2 ->
            fun p2 ->
              fun cl ->
                fun g ->
                  fun f ->
                    fun rrel ->
                      fun rel ->
                        fun sl ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            FStar_UInt32.add pos (f ())
let (accessor_id :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun rrel ->
          fun rel ->
            fun input -> fun pos -> let h = FStar_HyperStack_ST.get () in pos
let (accessor_ext :
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
                    (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens ->
                      unit ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun k2 ->
          fun t2 ->
            fun p2 ->
              fun cl ->
                fun g ->
                  fun a ->
                    fun cl' ->
                      fun sq ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos ->
                                let h = FStar_HyperStack_ST.get () in
                                a () () input pos
let (accessor_compose :
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
                          (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens ->
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
    fun t1 ->
      fun p1 ->
        fun k2 ->
          fun t2 ->
            fun p2 ->
              fun cl12 ->
                fun a12 ->
                  fun a12' ->
                    fun k3 ->
                      fun t3 ->
                        fun p3 ->
                          fun cl23 ->
                            fun a23 ->
                              fun a23' ->
                                fun sq ->
                                  fun rrel ->
                                    fun rel ->
                                      fun input ->
                                        fun pos ->
                                          let h = FStar_HyperStack_ST.get () in
                                          let pos2 = a12' () () input pos in
                                          let pos3 = a23' () () input pos2 in
                                          pos3
type ('k, 't, 'p) validator =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t
type ('k, 't, 'p) validator_no_read =
  unit -> unit -> unit -> FStar_UInt32.t -> FStar_UInt64.t -> FStar_UInt64.t
let (validate_no_read :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit -> unit -> FStar_UInt32.t -> FStar_UInt64.t -> FStar_UInt64.t)
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
                  v () () ()
                    (match sl with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> len) pos
let (validate_with_error_code :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          FStar_UInt64.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun c ->
            fun rrel ->
              fun rel ->
                fun sl ->
                  fun pos ->
                    let res = v () () sl pos in
                    LowParse_Low_ErrorCode.maybe_set_error_code res pos c
let (validate :
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
              (LowParse_Bytes.byte, Obj.t, Obj.t)
                LowStar_Monotonic_Buffer.mbuffer ->
                FStar_UInt32.t -> Prims.bool)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun rrel ->
            fun rel ->
              fun b ->
                fun len ->
                  if
                    LowParse_Low_ErrorCode.is_error
                      (FStar_Int_Cast.uint32_to_uint64 len)
                  then false
                  else
                    (let uu___1 =
                       v () ()
                         { LowParse_Slice.base = b; LowParse_Slice.len = len
                         } (FStar_UInt64.uint_to_t Prims.int_zero) in
                     LowParse_Low_ErrorCode.is_success uu___1)

let (validate_total_constant_size_no_read :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        FStar_UInt64.t ->
          unit ->
            unit ->
              unit ->
                unit -> FStar_UInt32.t -> FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun sz ->
          fun u ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun len ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      if
                        FStar_UInt64.lt
                          (FStar_UInt64.sub
                             (FStar_Int_Cast.uint32_to_uint64 len) pos) sz
                      then
                        LowParse_Low_ErrorCode.validator_error_not_enough_data
                      else FStar_UInt64.add pos sz
let (validate_total_constant_size :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        FStar_UInt64.t ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun sz ->
          fun u ->
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
                        sz
                    then
                      LowParse_Low_ErrorCode.validator_error_not_enough_data
                    else FStar_UInt64.add pos sz
let (validate_total_constant_size_with_error_code :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        FStar_UInt64.t ->
          FStar_UInt64.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun sz ->
          fun c ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    if
                      FStar_UInt64.lt
                        (FStar_UInt64.sub
                           (FStar_Int_Cast.uint32_to_uint64
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len;_} -> len)) pos)
                        sz
                    then
                      LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                        LowParse_Low_ErrorCode.validator_error_not_enough_data
                        pos c
                    else FStar_UInt64.add pos sz

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
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k1 ->
    fun k2 ->
      fun t ->
        fun p2 ->
          fun v2 ->
            fun rrel ->
              fun rel ->
                fun sl ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in v2 () () sl pos
type ('k, 't, 'p) jumper =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
let (jump_constant_size' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun sz ->
          fun u ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos sz
let (jump_constant_size :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun sz ->
          fun u ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos sz
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
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun k2 ->
      fun t ->
        fun p2 ->
          fun v2 ->
            fun rrel ->
              fun rel ->
                fun sl ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in v2 () () sl pos
type ('t, 'slong, 'sshort) seq_starts_with = unit



type ('k, 't, 'p) leaf_reader =
  unit -> unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 't
let (leaf_reader_ext :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> Obj.t)
  =
  fun k1 ->
    fun t ->
      fun p1 ->
        fun p32 ->
          fun k2 ->
            fun p2 ->
              fun lem ->
                fun rrel ->
                  fun rel ->
                    fun sl ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        p32 () () sl pos
type ('t, 'rrel, 'rel, 'b, 'pos, 'posu, 'h) writable = unit








type ('k, 't, 'p, 's) leaf_writer_weak =
  't ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t
type ('k, 't, 'p, 's) leaf_writer_strong =
  't ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t
type ('k, 't, 'p, 's) serializer32 =
  't ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t
let (serialize32_ext :
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
                  fun u ->
                    fun x ->
                      fun rrel ->
                        fun rel -> fun b -> fun pos -> s1' x () () b pos
let (frame_serializer32 :
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
              unit ->
                unit ->
                  (LowParse_Bytes.byte, Obj.t, Obj.t)
                    LowStar_Monotonic_Buffer.mbuffer ->
                    unit -> unit -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun x ->
              fun rrel ->
                fun rel ->
                  fun b ->
                    fun posl ->
                      fun posr ->
                        fun pos ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let res = s32 x () () b pos in
                          let h1 = FStar_HyperStack_ST.get () in
                          let pos' = FStar_UInt32.add pos res in res
let (leaf_writer_strong_of_serializer32 :
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
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun u ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h0 = FStar_HyperStack_ST.get () in
                        let len =
                          s32 x () ()
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len1;_} -> base) pos in
                        let h = FStar_HyperStack_ST.get () in
                        FStar_UInt32.add pos len
let (leaf_writer_weak_of_strong_constant_size :
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
            FStar_UInt32.t ->
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
            fun sz ->
              fun u ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          if
                            FStar_UInt32.lt
                              (FStar_UInt32.sub
                                 (match input with
                                  | { LowParse_Slice.base = base;
                                      LowParse_Slice.len = len;_} -> len) pos)
                              sz
                          then LowParse_Low_ErrorCode.max_uint32
                          else
                            (let h = FStar_HyperStack_ST.get () in
                             s32 x () () input pos)
let (serializer32_of_leaf_writer_strong_constant_size :
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
            FStar_UInt32.t ->
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
            fun sz ->
              fun u ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun b ->
                        fun pos ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let pos' =
                            s32 x () ()
                              {
                                LowParse_Slice.base = b;
                                LowParse_Slice.len =
                                  (FStar_UInt32.add pos sz)
                              } pos in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.sub pos' pos
let blit_strong :
  'a 'rrel1 'rrel2 'rel1 'rel2 .
    ('a, 'rrel1, 'rel1) LowStar_Monotonic_Buffer.mbuffer ->
      FStar_UInt32.t ->
        ('a, 'rrel2, 'rel2) LowStar_Monotonic_Buffer.mbuffer ->
          FStar_UInt32.t -> FStar_UInt32.t -> unit
  =
  fun src ->
    fun idx_src ->
      fun dst ->
        fun idx_dst ->
          fun len ->
            let h = FStar_HyperStack_ST.get () in
            LowStar_Monotonic_Buffer.blit src idx_src dst idx_dst len;
            (let h' = FStar_HyperStack_ST.get () in ())
let copy_strong :
  'rrel1 'rrel2 'rel1 'rel2 .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('rrel1, 'rel1) LowParse_Slice.slice ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('rrel2, 'rel2) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun t ->
      fun p ->
        fun src ->
          fun spos ->
            fun spos' ->
              fun dst ->
                fun dpos ->
                  let h0 = FStar_HyperStack_ST.get () in
                  let len = FStar_UInt32.sub spos' spos in
                  (let h = FStar_HyperStack_ST.get () in
                   LowStar_Monotonic_Buffer.blit
                     (match src with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) spos
                     (match dst with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) dpos len;
                   (let h' = FStar_HyperStack_ST.get () in ()));
                  (let h = FStar_HyperStack_ST.get () in
                   FStar_UInt32.add dpos len)
let copy_strong' :
  'rrel1 'rrel2 'rel1 'rel2 .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('rrel1, 'rel1) LowParse_Slice.slice ->
              FStar_UInt32.t ->
                ('rrel2, 'rel2) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun src ->
            fun spos ->
              fun dst ->
                fun dpos ->
                  let spos' = j () () (Obj.magic src) spos in
                  let h0 = FStar_HyperStack_ST.get () in
                  let len = FStar_UInt32.sub spos' spos in
                  (let h = FStar_HyperStack_ST.get () in
                   LowStar_Monotonic_Buffer.blit
                     (match src with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) spos
                     (match dst with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) dpos len;
                   (let h' = FStar_HyperStack_ST.get () in ()));
                  (let h = FStar_HyperStack_ST.get () in
                   FStar_UInt32.add dpos len)
let copy_weak_with_length :
  'rrel1 'rrel2 'rel1 'rel2 .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('rrel1, 'rel1) LowParse_Slice.slice ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                ('rrel2, 'rel2) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun t ->
      fun p ->
        fun src ->
          fun spos ->
            fun spos' ->
              fun dst ->
                fun dpos ->
                  if
                    FStar_UInt32.lt
                      (FStar_UInt32.sub
                         (match dst with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len;_} -> len) dpos)
                      (FStar_UInt32.sub spos' spos)
                  then LowParse_Low_ErrorCode.max_uint32
                  else
                    (let h0 = FStar_HyperStack_ST.get () in
                     let len = FStar_UInt32.sub spos' spos in
                     (let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.blit
                        (match src with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) spos
                        (match dst with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) dpos len;
                      (let h' = FStar_HyperStack_ST.get () in ()));
                     (let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add dpos len))
let copy_weak :
  'rrel1 'rrel2 'rel1 'rel2 .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('rrel1, 'rel1) LowParse_Slice.slice ->
              FStar_UInt32.t ->
                ('rrel2, 'rel2) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun t ->
      fun p ->
        fun jmp ->
          fun src ->
            fun spos ->
              fun dst ->
                fun dpos ->
                  let spos' = jmp () () (Obj.magic src) spos in
                  if
                    FStar_UInt32.lt
                      (FStar_UInt32.sub
                         (match dst with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len;_} -> len) dpos)
                      (FStar_UInt32.sub spos' spos)
                  then LowParse_Low_ErrorCode.max_uint32
                  else
                    (let h0 = FStar_HyperStack_ST.get () in
                     let len = FStar_UInt32.sub spos' spos in
                     (let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.blit
                        (match src with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) spos
                        (match dst with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) dpos len;
                      (let h' = FStar_HyperStack_ST.get () in ()));
                     (let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add dpos len))
let list_fold_left_gen :
  'rrel 'rel .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('rrel, 'rel) LowParse_Slice.slice ->
              FStar_UInt32.t ->
                FStar_UInt32.t ->
                  FStar_Monotonic_HyperStack.mem ->
                    unit ->
                      unit ->
                        unit ->
                          unit ->
                            unit ->
                              (FStar_UInt32.t -> FStar_UInt32.t -> Prims.bool)
                                -> Prims.bool
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun sl ->
            fun pos ->
              fun pos' ->
                fun h0 ->
                  fun l ->
                    fun inv ->
                      fun inv_frame ->
                        fun post_interrupt ->
                          fun post_interrupt_frame ->
                            fun body ->
                              FStar_HyperStack_ST.push_frame ();
                              (let h1 = FStar_HyperStack_ST.get () in
                               let bpos =
                                 LowStar_Monotonic_Buffer.malloca pos
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let bctinue =
                                 LowStar_Monotonic_Buffer.malloca true
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let btest =
                                 LowStar_Monotonic_Buffer.malloca
                                   (FStar_UInt32.lt pos pos')
                                   (FStar_UInt32.uint_to_t Prims.int_one) in
                               let h2 = FStar_HyperStack_ST.get () in
                               Obj.magic (fun h -> ());
                               Obj.magic (fun cond -> fun h -> ());
                               C_Loops.while1
                                 (fun uu___2 ->
                                    LowStar_Monotonic_Buffer.index btest
                                      (FStar_UInt32.uint_to_t Prims.int_zero))
                                 (fun uu___2 ->
                                    let h51 = FStar_HyperStack_ST.get () in
                                    let pos1 =
                                      LowStar_Monotonic_Buffer.index bpos
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero) in
                                    let pos2 = j () () (Obj.magic sl) pos1 in
                                    let h52 = FStar_HyperStack_ST.get () in
                                    let ctinue = body pos1 pos2 in
                                    let h53 = FStar_HyperStack_ST.get () in
                                    (let h = FStar_HyperStack_ST.get () in
                                     LowStar_Monotonic_Buffer.upd' bpos
                                       (FStar_UInt32.uint_to_t Prims.int_zero)
                                       pos2);
                                    (let h = FStar_HyperStack_ST.get () in
                                     LowStar_Monotonic_Buffer.upd' bctinue
                                       (FStar_UInt32.uint_to_t Prims.int_zero)
                                       ctinue);
                                    (let h = FStar_HyperStack_ST.get () in
                                     LowStar_Monotonic_Buffer.upd' btest
                                       (FStar_UInt32.uint_to_t Prims.int_zero)
                                       ((FStar_UInt32.lt pos2 pos') && ctinue));
                                    (let h54 = FStar_HyperStack_ST.get () in
                                     ()));
                               (let res =
                                  LowStar_Monotonic_Buffer.index bctinue
                                    (FStar_UInt32.uint_to_t Prims.int_zero) in
                                let h3 = FStar_HyperStack_ST.get () in
                                FStar_HyperStack_ST.pop_frame ();
                                (let h4 = FStar_HyperStack_ST.get () in res)))
let list_fold_left :
  'rrel 'rel .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('rrel, 'rel) LowParse_Slice.slice ->
              FStar_UInt32.t ->
                FStar_UInt32.t ->
                  FStar_Monotonic_HyperStack.mem ->
                    unit ->
                      unit ->
                        unit ->
                          (FStar_UInt32.t ->
                             FStar_UInt32.t -> unit -> unit -> unit -> unit)
                            -> unit
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun sl ->
            fun pos ->
              fun pos' ->
                fun h0 ->
                  fun l ->
                    fun inv ->
                      fun inv_frame ->
                        fun body ->
                          let uu___ =
                            FStar_HyperStack_ST.push_frame ();
                            (let h1 = FStar_HyperStack_ST.get () in
                             let bpos =
                               LowStar_Monotonic_Buffer.malloca pos
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let bctinue =
                               LowStar_Monotonic_Buffer.malloca true
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let btest =
                               LowStar_Monotonic_Buffer.malloca
                                 (FStar_UInt32.lt pos pos')
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let h2 = FStar_HyperStack_ST.get () in
                             Obj.magic (fun h -> ());
                             Obj.magic (fun cond -> fun h -> ());
                             C_Loops.while1
                               (fun uu___3 ->
                                  LowStar_Monotonic_Buffer.index btest
                                    (FStar_UInt32.uint_to_t Prims.int_zero))
                               (fun uu___3 ->
                                  let h51 = FStar_HyperStack_ST.get () in
                                  let pos1 =
                                    LowStar_Monotonic_Buffer.index bpos
                                      (FStar_UInt32.uint_to_t Prims.int_zero) in
                                  let pos2 = j () () (Obj.magic sl) pos1 in
                                  let h52 = FStar_HyperStack_ST.get () in
                                  let ctinue =
                                    let h = FStar_HyperStack_ST.get () in
                                    body pos1 pos2 () () (); true in
                                  let h53 = FStar_HyperStack_ST.get () in
                                  (let h = FStar_HyperStack_ST.get () in
                                   LowStar_Monotonic_Buffer.upd' bpos
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     pos2);
                                  (let h = FStar_HyperStack_ST.get () in
                                   LowStar_Monotonic_Buffer.upd' bctinue
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     ctinue);
                                  (let h = FStar_HyperStack_ST.get () in
                                   LowStar_Monotonic_Buffer.upd' btest
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     ((FStar_UInt32.lt pos2 pos') && ctinue));
                                  (let h54 = FStar_HyperStack_ST.get () in ()));
                             (let res =
                                LowStar_Monotonic_Buffer.index bctinue
                                  (FStar_UInt32.uint_to_t Prims.int_zero) in
                              let h3 = FStar_HyperStack_ST.get () in
                              FStar_HyperStack_ST.pop_frame ();
                              (let h4 = FStar_HyperStack_ST.get () in res))) in
                          ()
let list_length :
  'rrel 'rel .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('rrel, 'rel) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun sl ->
            fun pos ->
              fun pos' ->
                let h0 = FStar_HyperStack_ST.get () in
                FStar_HyperStack_ST.push_frame ();
                (let h1 = FStar_HyperStack_ST.get () in
                 let blen =
                   LowStar_Monotonic_Buffer.malloca
                     (FStar_UInt32.uint_to_t Prims.int_zero)
                     (FStar_UInt32.uint_to_t Prims.int_one) in
                 let h2 = FStar_HyperStack_ST.get () in
                 (let uu___2 =
                    FStar_HyperStack_ST.push_frame ();
                    (let h11 = FStar_HyperStack_ST.get () in
                     let bpos =
                       LowStar_Monotonic_Buffer.malloca pos
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let bctinue =
                       LowStar_Monotonic_Buffer.malloca true
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let btest =
                       LowStar_Monotonic_Buffer.malloca
                         (FStar_UInt32.lt pos pos')
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let h21 = FStar_HyperStack_ST.get () in
                     Obj.magic (fun h -> ());
                     Obj.magic (fun cond -> fun h -> ());
                     C_Loops.while1
                       (fun uu___5 ->
                          LowStar_Monotonic_Buffer.index btest
                            (FStar_UInt32.uint_to_t Prims.int_zero))
                       (fun uu___5 ->
                          let h51 = FStar_HyperStack_ST.get () in
                          let pos1 =
                            LowStar_Monotonic_Buffer.index bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          let pos2 = j () () (Obj.magic sl) pos1 in
                          let h52 = FStar_HyperStack_ST.get () in
                          let ctinue =
                            let h = FStar_HyperStack_ST.get () in
                            (let uu___8 =
                               let uu___9 =
                                 LowStar_Monotonic_Buffer.index blen
                                   (FStar_UInt32.uint_to_t Prims.int_zero) in
                               FStar_UInt32.add uu___9
                                 (FStar_UInt32.uint_to_t Prims.int_one) in
                             let h3 = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd' blen
                               (FStar_UInt32.uint_to_t Prims.int_zero) uu___8);
                            true in
                          let h53 = FStar_HyperStack_ST.get () in
                          (let h = FStar_HyperStack_ST.get () in
                           LowStar_Monotonic_Buffer.upd' bpos
                             (FStar_UInt32.uint_to_t Prims.int_zero) pos2);
                          (let h = FStar_HyperStack_ST.get () in
                           LowStar_Monotonic_Buffer.upd' bctinue
                             (FStar_UInt32.uint_to_t Prims.int_zero) ctinue);
                          (let h = FStar_HyperStack_ST.get () in
                           LowStar_Monotonic_Buffer.upd' btest
                             (FStar_UInt32.uint_to_t Prims.int_zero)
                             ((FStar_UInt32.lt pos2 pos') && ctinue));
                          (let h54 = FStar_HyperStack_ST.get () in ()));
                     (let res =
                        LowStar_Monotonic_Buffer.index bctinue
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      let h3 = FStar_HyperStack_ST.get () in
                      FStar_HyperStack_ST.pop_frame ();
                      (let h4 = FStar_HyperStack_ST.get () in res))) in
                  ());
                 (let len =
                    LowStar_Monotonic_Buffer.index blen
                      (FStar_UInt32.uint_to_t Prims.int_zero) in
                  FStar_HyperStack_ST.pop_frame (); len))
let (list_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> Prims.bool) ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> unit -> Prims.bool)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t ->
                      FStar_UInt32.t ->
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
            fun f' ->
              fun rrel ->
                fun rel ->
                  fun sl ->
                    fun pos ->
                      fun pos' ->
                        fun rrel_out ->
                          fun rel_out ->
                            fun sl_out ->
                              fun pos_out ->
                                let h0 = FStar_HyperStack_ST.get () in
                                FStar_HyperStack_ST.push_frame ();
                                (let h1 = FStar_HyperStack_ST.get () in
                                 let bpos_out' =
                                   LowStar_Monotonic_Buffer.malloca pos_out
                                     (FStar_UInt32.uint_to_t Prims.int_one) in
                                 let h2 = FStar_HyperStack_ST.get () in
                                 Obj.magic
                                   (fun h ->
                                      fun l1 -> fun l2 -> fun pos1 -> ());
                                 (let uu___2 =
                                    FStar_HyperStack_ST.push_frame ();
                                    (let h11 = FStar_HyperStack_ST.get () in
                                     let bpos =
                                       LowStar_Monotonic_Buffer.malloca pos
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_one) in
                                     let bctinue =
                                       LowStar_Monotonic_Buffer.malloca true
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_one) in
                                     let btest =
                                       LowStar_Monotonic_Buffer.malloca
                                         (FStar_UInt32.lt pos pos')
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_one) in
                                     let h21 = FStar_HyperStack_ST.get () in
                                     Obj.magic (fun h -> ());
                                     Obj.magic (fun cond -> fun h -> ());
                                     C_Loops.while1
                                       (fun uu___5 ->
                                          LowStar_Monotonic_Buffer.index
                                            btest
                                            (FStar_UInt32.uint_to_t
                                               Prims.int_zero))
                                       (fun uu___5 ->
                                          let h51 =
                                            FStar_HyperStack_ST.get () in
                                          let pos1 =
                                            LowStar_Monotonic_Buffer.index
                                              bpos
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero) in
                                          let pos2 = j () () sl pos1 in
                                          let h52 =
                                            FStar_HyperStack_ST.get () in
                                          let ctinue =
                                            let h =
                                              FStar_HyperStack_ST.get () in
                                            (let pos_out1 =
                                               LowStar_Monotonic_Buffer.index
                                                 bpos_out'
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero) in
                                             let uu___7 = f' () () sl pos1 () in
                                             if uu___7
                                             then
                                               let h3 =
                                                 FStar_HyperStack_ST.get () in
                                               let pos_out2 =
                                                 let h01 =
                                                   FStar_HyperStack_ST.get () in
                                                 let len =
                                                   FStar_UInt32.sub pos2 pos1 in
                                                 (let h4 =
                                                    FStar_HyperStack_ST.get
                                                      () in
                                                  LowStar_Monotonic_Buffer.blit
                                                    (match sl with
                                                     | {
                                                         LowParse_Slice.base
                                                           = base;
                                                         LowParse_Slice.len =
                                                           len1;_}
                                                         -> base) pos1
                                                    (match sl_out with
                                                     | {
                                                         LowParse_Slice.base
                                                           = base;
                                                         LowParse_Slice.len =
                                                           len1;_}
                                                         -> base) pos_out1
                                                    len;
                                                  (let h' =
                                                     FStar_HyperStack_ST.get
                                                       () in
                                                   ()));
                                                 (let h4 =
                                                    FStar_HyperStack_ST.get
                                                      () in
                                                  FStar_UInt32.add pos_out1
                                                    len) in
                                               ((let h4 =
                                                   FStar_HyperStack_ST.get () in
                                                 LowStar_Monotonic_Buffer.upd'
                                                   bpos_out'
                                                   (FStar_UInt32.uint_to_t
                                                      Prims.int_zero)
                                                   pos_out2);
                                                (let h' =
                                                   FStar_HyperStack_ST.get () in
                                                 ()))
                                             else ());
                                            true in
                                          let h53 =
                                            FStar_HyperStack_ST.get () in
                                          (let h = FStar_HyperStack_ST.get () in
                                           LowStar_Monotonic_Buffer.upd' bpos
                                             (FStar_UInt32.uint_to_t
                                                Prims.int_zero) pos2);
                                          (let h = FStar_HyperStack_ST.get () in
                                           LowStar_Monotonic_Buffer.upd'
                                             bctinue
                                             (FStar_UInt32.uint_to_t
                                                Prims.int_zero) ctinue);
                                          (let h = FStar_HyperStack_ST.get () in
                                           LowStar_Monotonic_Buffer.upd'
                                             btest
                                             (FStar_UInt32.uint_to_t
                                                Prims.int_zero)
                                             ((FStar_UInt32.lt pos2 pos') &&
                                                ctinue));
                                          (let h54 =
                                             FStar_HyperStack_ST.get () in
                                           ()));
                                     (let res =
                                        LowStar_Monotonic_Buffer.index
                                          bctinue
                                          (FStar_UInt32.uint_to_t
                                             Prims.int_zero) in
                                      let h3 = FStar_HyperStack_ST.get () in
                                      FStar_HyperStack_ST.pop_frame ();
                                      (let h4 = FStar_HyperStack_ST.get () in
                                       res))) in
                                  ());
                                 (let pos_out' =
                                    LowStar_Monotonic_Buffer.index bpos_out'
                                      (FStar_UInt32.uint_to_t Prims.int_zero) in
                                  FStar_HyperStack_ST.pop_frame (); pos_out'))
let list_nth :
  'rrel 'rel .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('rrel, 'rel) LowParse_Slice.slice ->
              FStar_UInt32.t ->
                FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun sl ->
            fun pos ->
              fun pos' ->
                fun i ->
                  let h0 = FStar_HyperStack_ST.get () in
                  FStar_HyperStack_ST.push_frame ();
                  (let h1 = FStar_HyperStack_ST.get () in
                   let bpos1 =
                     LowStar_Monotonic_Buffer.malloca pos
                       (FStar_UInt32.uint_to_t Prims.int_one) in
                   let bk =
                     LowStar_Monotonic_Buffer.malloca
                       (FStar_UInt32.uint_to_t Prims.int_zero)
                       (FStar_UInt32.uint_to_t Prims.int_one) in
                   let h2 = FStar_HyperStack_ST.get () in
                   let uu___1 =
                     FStar_HyperStack_ST.push_frame ();
                     (let h11 = FStar_HyperStack_ST.get () in
                      let bpos =
                        LowStar_Monotonic_Buffer.malloca pos
                          (FStar_UInt32.uint_to_t Prims.int_one) in
                      let bctinue =
                        LowStar_Monotonic_Buffer.malloca true
                          (FStar_UInt32.uint_to_t Prims.int_one) in
                      let btest =
                        LowStar_Monotonic_Buffer.malloca
                          (FStar_UInt32.lt pos pos')
                          (FStar_UInt32.uint_to_t Prims.int_one) in
                      let h21 = FStar_HyperStack_ST.get () in
                      Obj.magic (fun h -> ());
                      Obj.magic (fun cond -> fun h -> ());
                      C_Loops.while1
                        (fun uu___4 ->
                           LowStar_Monotonic_Buffer.index btest
                             (FStar_UInt32.uint_to_t Prims.int_zero))
                        (fun uu___4 ->
                           let h51 = FStar_HyperStack_ST.get () in
                           let pos1 =
                             LowStar_Monotonic_Buffer.index bpos
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                           let pos2 = j () () (Obj.magic sl) pos1 in
                           let h52 = FStar_HyperStack_ST.get () in
                           let ctinue =
                             let k1 =
                               LowStar_Monotonic_Buffer.index bk
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             if k1 = i
                             then
                               ((let h = FStar_HyperStack_ST.get () in
                                 LowStar_Monotonic_Buffer.upd' bpos1
                                   (FStar_UInt32.uint_to_t Prims.int_zero)
                                   pos1);
                                false)
                             else
                               ((let h = FStar_HyperStack_ST.get () in
                                 LowStar_Monotonic_Buffer.upd' bk
                                   (FStar_UInt32.uint_to_t Prims.int_zero)
                                   (FStar_UInt32.add k1
                                      (FStar_UInt32.uint_to_t Prims.int_one)));
                                (let h = FStar_HyperStack_ST.get () in true)) in
                           let h53 = FStar_HyperStack_ST.get () in
                           (let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd' bpos
                              (FStar_UInt32.uint_to_t Prims.int_zero) pos2);
                           (let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd' bctinue
                              (FStar_UInt32.uint_to_t Prims.int_zero) ctinue);
                           (let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd' btest
                              (FStar_UInt32.uint_to_t Prims.int_zero)
                              ((FStar_UInt32.lt pos2 pos') && ctinue));
                           (let h54 = FStar_HyperStack_ST.get () in ()));
                      (let res =
                         LowStar_Monotonic_Buffer.index bctinue
                           (FStar_UInt32.uint_to_t Prims.int_zero) in
                       let h3 = FStar_HyperStack_ST.get () in
                       FStar_HyperStack_ST.pop_frame ();
                       (let h4 = FStar_HyperStack_ST.get () in res))) in
                   let res =
                     LowStar_Monotonic_Buffer.index bpos1
                       (FStar_UInt32.uint_to_t Prims.int_zero) in
                   FStar_HyperStack_ST.pop_frame (); res)
let (list_find :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> Prims.bool) ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> Prims.bool)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun f ->
            fun f' ->
              fun rrel ->
                fun rel ->
                  fun sl ->
                    fun pos ->
                      fun pos' ->
                        let h0 = FStar_HyperStack_ST.get () in
                        FStar_HyperStack_ST.push_frame ();
                        (let h1 = FStar_HyperStack_ST.get () in
                         let bres =
                           LowStar_Monotonic_Buffer.malloca
                             (FStar_UInt32.uint_to_t Prims.int_zero)
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let h2 = FStar_HyperStack_ST.get () in
                         let not_found =
                           FStar_HyperStack_ST.push_frame ();
                           (let h11 = FStar_HyperStack_ST.get () in
                            let bpos =
                              LowStar_Monotonic_Buffer.malloca pos
                                (FStar_UInt32.uint_to_t Prims.int_one) in
                            let bctinue =
                              LowStar_Monotonic_Buffer.malloca true
                                (FStar_UInt32.uint_to_t Prims.int_one) in
                            let btest =
                              LowStar_Monotonic_Buffer.malloca
                                (FStar_UInt32.lt pos pos')
                                (FStar_UInt32.uint_to_t Prims.int_one) in
                            let h21 = FStar_HyperStack_ST.get () in
                            Obj.magic (fun h -> ());
                            Obj.magic (fun cond -> fun h -> ());
                            C_Loops.while1
                              (fun uu___3 ->
                                 LowStar_Monotonic_Buffer.index btest
                                   (FStar_UInt32.uint_to_t Prims.int_zero))
                              (fun uu___3 ->
                                 let h51 = FStar_HyperStack_ST.get () in
                                 let pos1 =
                                   LowStar_Monotonic_Buffer.index bpos
                                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                                 let pos2 = j () () sl pos1 in
                                 let h52 = FStar_HyperStack_ST.get () in
                                 let ctinue =
                                   let uu___4 = f' () () sl pos1 in
                                   if uu___4
                                   then
                                     ((let h = FStar_HyperStack_ST.get () in
                                       LowStar_Monotonic_Buffer.upd' bres
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_zero) pos1);
                                      false)
                                   else true in
                                 let h53 = FStar_HyperStack_ST.get () in
                                 (let h = FStar_HyperStack_ST.get () in
                                  LowStar_Monotonic_Buffer.upd' bpos
                                    (FStar_UInt32.uint_to_t Prims.int_zero)
                                    pos2);
                                 (let h = FStar_HyperStack_ST.get () in
                                  LowStar_Monotonic_Buffer.upd' bctinue
                                    (FStar_UInt32.uint_to_t Prims.int_zero)
                                    ctinue);
                                 (let h = FStar_HyperStack_ST.get () in
                                  LowStar_Monotonic_Buffer.upd' btest
                                    (FStar_UInt32.uint_to_t Prims.int_zero)
                                    ((FStar_UInt32.lt pos2 pos') && ctinue));
                                 (let h54 = FStar_HyperStack_ST.get () in ()));
                            (let res =
                               LowStar_Monotonic_Buffer.index bctinue
                                 (FStar_UInt32.uint_to_t Prims.int_zero) in
                             let h3 = FStar_HyperStack_ST.get () in
                             FStar_HyperStack_ST.pop_frame ();
                             (let h4 = FStar_HyperStack_ST.get () in res))) in
                         let res =
                           if not_found
                           then pos'
                           else
                             LowStar_Monotonic_Buffer.index bres
                               (FStar_UInt32.uint_to_t Prims.int_zero) in
                         FStar_HyperStack_ST.pop_frame (); res)

let (print_list :
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
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> unit)
            ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun k ->
    fun t ->
      fun p ->
        fun j ->
          fun print ->
            fun rrel ->
              fun rel ->
                fun sl ->
                  fun pos ->
                    fun pos' ->
                      let h0 = FStar_HyperStack_ST.get () in
                      let uu___ =
                        FStar_HyperStack_ST.push_frame ();
                        (let h1 = FStar_HyperStack_ST.get () in
                         let bpos =
                           LowStar_Monotonic_Buffer.malloca pos
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let bctinue =
                           LowStar_Monotonic_Buffer.malloca true
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let btest =
                           LowStar_Monotonic_Buffer.malloca
                             (FStar_UInt32.lt pos pos')
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         let h2 = FStar_HyperStack_ST.get () in
                         Obj.magic (fun h -> ());
                         Obj.magic (fun cond -> fun h -> ());
                         C_Loops.while1
                           (fun uu___3 ->
                              LowStar_Monotonic_Buffer.index btest
                                (FStar_UInt32.uint_to_t Prims.int_zero))
                           (fun uu___3 ->
                              let h51 = FStar_HyperStack_ST.get () in
                              let pos1 =
                                LowStar_Monotonic_Buffer.index bpos
                                  (FStar_UInt32.uint_to_t Prims.int_zero) in
                              let pos2 = j () () sl pos1 in
                              let h52 = FStar_HyperStack_ST.get () in
                              let ctinue =
                                let h = FStar_HyperStack_ST.get () in
                                print () () sl pos1; true in
                              let h53 = FStar_HyperStack_ST.get () in
                              (let h = FStar_HyperStack_ST.get () in
                               LowStar_Monotonic_Buffer.upd' bpos
                                 (FStar_UInt32.uint_to_t Prims.int_zero) pos2);
                              (let h = FStar_HyperStack_ST.get () in
                               LowStar_Monotonic_Buffer.upd' bctinue
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 ctinue);
                              (let h = FStar_HyperStack_ST.get () in
                               LowStar_Monotonic_Buffer.upd' btest
                                 (FStar_UInt32.uint_to_t Prims.int_zero)
                                 ((FStar_UInt32.lt pos2 pos') && ctinue));
                              (let h54 = FStar_HyperStack_ST.get () in ()));
                         (let res =
                            LowStar_Monotonic_Buffer.index bctinue
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          let h3 = FStar_HyperStack_ST.get () in
                          FStar_HyperStack_ST.pop_frame ();
                          (let h4 = FStar_HyperStack_ST.get () in res))) in
                      ()
type 't compl_t = unit
type ('t, 'k, 'p, 'rrel, 'rel, 's, 'compl, 'pos, 'gposu, 'gv, 'x) wvalid =
  unit
type ('t, 'k, 'p, 'rrel, 'rel, 's, 'compl) irepr =
  | IRepr of FStar_UInt32.t * unit * unit * unit 
let uu___is_IRepr :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              unit ->
                ('t, unit, unit, Obj.t, Obj.t, unit, Obj.t) irepr ->
                  Prims.bool
  =
  fun k ->
    fun p ->
      fun rrel -> fun rel -> fun s -> fun compl -> fun projectee -> true
let __proj__IRepr__item__pos :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              unit ->
                ('t, unit, unit, Obj.t, Obj.t, unit, Obj.t) irepr ->
                  FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun rrel ->
        fun rel ->
          fun s ->
            fun compl ->
              fun projectee ->
                match projectee with
                | IRepr (pos, gpos', gv, irepr_correct) -> pos



let irepr_pos :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              unit ->
                ('t, unit, unit, Obj.t, Obj.t, unit, Obj.t) irepr ->
                  FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun rrel ->
        fun rel ->
          fun s ->
            fun compl ->
              fun x ->
                match x with | IRepr (pos, gpos', gv, irepr_correct) -> pos



let witness_valid_gen :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              unit ->
                FStar_UInt32.t ->
                  ('t, unit, unit, Obj.t, Obj.t, unit, Obj.t) irepr
  =
  fun k ->
    fun p ->
      fun rrel ->
        fun rel ->
          fun s ->
            fun compl ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                LowStar_Monotonic_Buffer.witness_p
                  (match s with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base) ();
                IRepr (pos, (), (), ())
let recall_valid_gen :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              unit ->
                ('t, unit, unit, Obj.t, Obj.t, unit, Obj.t) irepr -> unit
  =
  fun k ->
    fun p ->
      fun rrel ->
        fun rel ->
          fun s ->
            fun compl ->
              fun i ->
                let h = FStar_HyperStack_ST.get () in
                LowStar_Monotonic_Buffer.recall_p
                  (match s with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base) ()