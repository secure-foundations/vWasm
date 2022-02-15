open Prims
let (validate_flbytes :
  Prims.nat ->
    FStar_UInt64.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun sz ->
    fun sz64 ->
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
                             LowParse_Slice.len = len;_} -> len)) pos) sz64
              then LowParse_Low_ErrorCode.validator_error_not_enough_data
              else FStar_UInt64.add pos sz64
let (jump_flbytes :
  Prims.nat ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz ->
    fun sz32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos sz32



let (clens_flbytes_slice :
  Prims.nat ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        (unit FStar_Bytes.lbytes, unit FStar_Bytes.lbytes)
          LowParse_Low_Base_Spec.clens)
  =
  fun sz ->
    fun from ->
      fun to1 ->
        {
          LowParse_Low_Base_Spec.clens_cond = ();
          LowParse_Low_Base_Spec.clens_get = ()
        }


let (accessor_flbytes_slice :
  Prims.nat ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz ->
    fun from ->
      fun to1 ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos from
let (clens_flbytes_get :
  Prims.nat ->
    FStar_UInt32.t ->
      (unit FStar_Bytes.lbytes, LowParse_Bytes.byte)
        LowParse_Low_Base_Spec.clens)
  =
  fun sz ->
    fun i ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }


let (accessor_flbytes_get :
  Prims.nat ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz ->
    fun i ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos i
let (store_bytes :
  FStar_Bytes.bytes ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (LowParse_Bytes.byte, Obj.t, Obj.t)
              LowStar_Monotonic_Buffer.mbuffer -> FStar_UInt32.t -> unit)
  =
  fun src ->
    fun src_from ->
      fun src_to ->
        fun rrel ->
          fun rel ->
            fun dst ->
              fun dst_pos ->
                let h0 = FStar_HyperStack_ST.get () in
                FStar_HyperStack_ST.push_frame ();
                (let h1 = FStar_HyperStack_ST.get () in
                 let bi =
                   LowStar_Monotonic_Buffer.malloca
                     (FStar_UInt32.uint_to_t Prims.int_zero)
                     (FStar_UInt32.uint_to_t Prims.int_one) in
                 let h2 = FStar_HyperStack_ST.get () in
                 let len = FStar_UInt32.sub src_to src_from in
                 C_Loops.do_while
                   (fun uu___2 ->
                      let i =
                        LowStar_Monotonic_Buffer.index bi
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      if i = len
                      then true
                      else
                        (let x =
                           FStar_Bytes.get src (FStar_UInt32.add src_from i) in
                         (let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd' dst
                            (FStar_UInt32.add dst_pos i) x);
                         (let i' =
                            FStar_UInt32.add i
                              (FStar_UInt32.uint_to_t Prims.int_one) in
                          (let h = FStar_HyperStack_ST.get () in
                           LowStar_Monotonic_Buffer.upd' bi
                             (FStar_UInt32.uint_to_t Prims.int_zero) i');
                          (let h' = FStar_HyperStack_ST.get () in i' = len))));
                 FStar_HyperStack_ST.pop_frame ())
let (serialize32_flbytes :
  FStar_UInt32.t ->
    unit FStar_Bytes.lbytes ->
      unit ->
        unit ->
          (LowParse_Bytes.byte, Obj.t, Obj.t)
            LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz32 ->
    fun x ->
      fun rrel ->
        fun rel ->
          fun b ->
            fun pos ->
              (let h0 = FStar_HyperStack_ST.get () in
               FStar_HyperStack_ST.push_frame ();
               (let h1 = FStar_HyperStack_ST.get () in
                let bi =
                  LowStar_Monotonic_Buffer.malloca
                    (FStar_UInt32.uint_to_t Prims.int_zero)
                    (FStar_UInt32.uint_to_t Prims.int_one) in
                let h2 = FStar_HyperStack_ST.get () in
                let len =
                  FStar_UInt32.sub sz32
                    (FStar_UInt32.uint_to_t Prims.int_zero) in
                C_Loops.do_while
                  (fun uu___3 ->
                     let i =
                       LowStar_Monotonic_Buffer.index bi
                         (FStar_UInt32.uint_to_t Prims.int_zero) in
                     if i = len
                     then true
                     else
                       (let x1 =
                          FStar_Bytes.get x
                            (FStar_UInt32.add
                               (FStar_UInt32.uint_to_t Prims.int_zero) i) in
                        (let h = FStar_HyperStack_ST.get () in
                         LowStar_Monotonic_Buffer.upd' b
                           (FStar_UInt32.add pos i) x1);
                        (let i' =
                           FStar_UInt32.add i
                             (FStar_UInt32.uint_to_t Prims.int_one) in
                         (let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd' bi
                            (FStar_UInt32.uint_to_t Prims.int_zero) i');
                         (let h' = FStar_HyperStack_ST.get () in i' = len))));
                FStar_HyperStack_ST.pop_frame ()));
              sz32
let (write_flbytes :
  FStar_UInt32.t ->
    unit FStar_Bytes.lbytes ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz32 ->
    fun x ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                (let h01 = FStar_HyperStack_ST.get () in
                 FStar_HyperStack_ST.push_frame ();
                 (let h1 = FStar_HyperStack_ST.get () in
                  let bi =
                    LowStar_Monotonic_Buffer.malloca
                      (FStar_UInt32.uint_to_t Prims.int_zero)
                      (FStar_UInt32.uint_to_t Prims.int_one) in
                  let h2 = FStar_HyperStack_ST.get () in
                  let len1 =
                    FStar_UInt32.sub sz32
                      (FStar_UInt32.uint_to_t Prims.int_zero) in
                  C_Loops.do_while
                    (fun uu___3 ->
                       let i =
                         LowStar_Monotonic_Buffer.index bi
                           (FStar_UInt32.uint_to_t Prims.int_zero) in
                       if i = len1
                       then true
                       else
                         (let x1 =
                            FStar_Bytes.get x
                              (FStar_UInt32.add
                                 (FStar_UInt32.uint_to_t Prims.int_zero) i) in
                          (let h = FStar_HyperStack_ST.get () in
                           LowStar_Monotonic_Buffer.upd'
                             (match input with
                              | { LowParse_Slice.base = base;
                                  LowParse_Slice.len = len2;_} -> base)
                             (FStar_UInt32.add pos i) x1);
                          (let i' =
                             FStar_UInt32.add i
                               (FStar_UInt32.uint_to_t Prims.int_one) in
                           (let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd' bi
                              (FStar_UInt32.uint_to_t Prims.int_zero) i');
                           (let h' = FStar_HyperStack_ST.get () in i' = len1))));
                  FStar_HyperStack_ST.pop_frame ()));
                sz32 in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_flbytes_weak :
  FStar_UInt32.t ->
    unit FStar_Bytes.lbytes ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz32 ->
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
                          LowParse_Slice.len = len;_} -> len) pos) sz32
              then LowParse_Low_ErrorCode.max_uint32
              else
                (let h = FStar_HyperStack_ST.get () in
                 let h0 = FStar_HyperStack_ST.get () in
                 let len =
                   (let h01 = FStar_HyperStack_ST.get () in
                    FStar_HyperStack_ST.push_frame ();
                    (let h1 = FStar_HyperStack_ST.get () in
                     let bi =
                       LowStar_Monotonic_Buffer.malloca
                         (FStar_UInt32.uint_to_t Prims.int_zero)
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let h2 = FStar_HyperStack_ST.get () in
                     let len1 =
                       FStar_UInt32.sub sz32
                         (FStar_UInt32.uint_to_t Prims.int_zero) in
                     C_Loops.do_while
                       (fun uu___4 ->
                          let i =
                            LowStar_Monotonic_Buffer.index bi
                              (FStar_UInt32.uint_to_t Prims.int_zero) in
                          if i = len1
                          then true
                          else
                            (let x1 =
                               FStar_Bytes.get x
                                 (FStar_UInt32.add
                                    (FStar_UInt32.uint_to_t Prims.int_zero) i) in
                             (let h3 = FStar_HyperStack_ST.get () in
                              LowStar_Monotonic_Buffer.upd'
                                (match input with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len2;_} -> base)
                                (FStar_UInt32.add pos i) x1);
                             (let i' =
                                FStar_UInt32.add i
                                  (FStar_UInt32.uint_to_t Prims.int_one) in
                              (let h3 = FStar_HyperStack_ST.get () in
                               LowStar_Monotonic_Buffer.upd' bi
                                 (FStar_UInt32.uint_to_t Prims.int_zero) i');
                              (let h' = FStar_HyperStack_ST.get () in
                               i' = len1))));
                     FStar_HyperStack_ST.pop_frame ()));
                   sz32 in
                 let h1 = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add pos len)
let (buffer_equals_bytes :
  FStar_Bytes.bytes ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> Prims.bool)
  =
  fun const ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let h0 = FStar_HyperStack_ST.get () in
            FStar_HyperStack_ST.push_frame ();
            (let len = FStar_Bytes.len const in
             let bi =
               LowStar_Monotonic_Buffer.malloca
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let bres =
               LowStar_Monotonic_Buffer.malloca true
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let h1 = FStar_HyperStack_ST.get () in
             C_Loops.do_while
               (fun uu___2 ->
                  let i =
                    LowStar_Monotonic_Buffer.index bi
                      (FStar_UInt32.uint_to_t Prims.int_zero) in
                  if i = len
                  then true
                  else
                    (let i' =
                       FStar_UInt32.add i
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let res =
                       let uu___4 =
                         LowStar_Monotonic_Buffer.index b
                           (FStar_UInt32.add pos i) in
                       uu___4 = (FStar_Bytes.get const i) in
                     (let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' bres
                        (FStar_UInt32.uint_to_t Prims.int_zero) res);
                     (let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' bi
                        (FStar_UInt32.uint_to_t Prims.int_zero) i');
                     Prims.op_Negation res));
             (let res =
                LowStar_Monotonic_Buffer.index bres
                  (FStar_UInt32.uint_to_t Prims.int_zero) in
              FStar_HyperStack_ST.pop_frame (); res))
let (valid_slice_equals_bytes :
  FStar_Bytes.bytes ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Prims.bool)
  =
  fun const ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let h0 = FStar_HyperStack_ST.get () in
            FStar_HyperStack_ST.push_frame ();
            (let len = FStar_Bytes.len const in
             let bi =
               LowStar_Monotonic_Buffer.malloca
                 (FStar_UInt32.uint_to_t Prims.int_zero)
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let bres =
               LowStar_Monotonic_Buffer.malloca true
                 (FStar_UInt32.uint_to_t Prims.int_one) in
             let h1 = FStar_HyperStack_ST.get () in
             C_Loops.do_while
               (fun uu___2 ->
                  let i =
                    LowStar_Monotonic_Buffer.index bi
                      (FStar_UInt32.uint_to_t Prims.int_zero) in
                  if i = len
                  then true
                  else
                    (let i' =
                       FStar_UInt32.add i
                         (FStar_UInt32.uint_to_t Prims.int_one) in
                     let res =
                       let uu___4 =
                         LowStar_Monotonic_Buffer.index
                           (match input with
                            | { LowParse_Slice.base = base;
                                LowParse_Slice.len = len1;_} -> base)
                           (FStar_UInt32.add pos i) in
                       uu___4 = (FStar_Bytes.get const i) in
                     (let h2 = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' bres
                        (FStar_UInt32.uint_to_t Prims.int_zero) res);
                     (let h2 = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' bi
                        (FStar_UInt32.uint_to_t Prims.int_zero) i');
                     Prims.op_Negation res));
             (let res =
                LowStar_Monotonic_Buffer.index bres
                  (FStar_UInt32.uint_to_t Prims.int_zero) in
              FStar_HyperStack_ST.pop_frame (); res))
let (validate_all_bytes :
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
            FStar_Int_Cast.uint32_to_uint64
              (match input with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   len)
let (validate_bounded_vlbytes' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let res =
                  let h4 = FStar_HyperStack_ST.get () in
                  if
                    FStar_UInt64.lt
                      (FStar_UInt64.sub
                         (FStar_Int_Cast.uint32_to_uint64
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len;_} -> len)) pos)
                      (FStar_UInt64.uint_to_t l)
                  then LowParse_Low_ErrorCode.validator_error_not_enough_data
                  else FStar_UInt64.add pos (FStar_UInt64.uint_to_t l) in
                if LowParse_Low_ErrorCode.is_error res
                then res
                else
                  (let va =
                     (match l with
                      | uu___1 when uu___1 = Prims.int_one ->
                          LowParse_Low_BoundedInt.read_bounded_integer_1 ()
                      | uu___1 when uu___1 = (Prims.of_int (2)) ->
                          LowParse_Low_BoundedInt.read_bounded_integer_2 ()
                      | uu___1 when uu___1 = (Prims.of_int (3)) ->
                          LowParse_Low_BoundedInt.read_bounded_integer_3 ()
                      | uu___1 when uu___1 = (Prims.of_int (4)) ->
                          LowParse_Low_BoundedInt.read_bounded_integer_4 ())
                       () () input (FStar_Int_Cast.uint64_to_uint32 pos) in
                   if
                     (if min = Prims.int_zero
                      then FStar_UInt32.lte va (FStar_UInt32.uint_to_t max)
                      else
                        (FStar_UInt32.lte (FStar_UInt32.uint_to_t min) va) &&
                          (FStar_UInt32.lte va (FStar_UInt32.uint_to_t max)))
                   then
                     let h4 = FStar_HyperStack_ST.get () in
                     let h5 = FStar_HyperStack_ST.get () in
                     (if
                        FStar_UInt64.lt
                          (FStar_UInt64.sub
                             (FStar_Int_Cast.uint32_to_uint64
                                (match input with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len;_} -> len)) res)
                          (FStar_Int_Cast.uint32_to_uint64 va)
                      then
                        LowParse_Low_ErrorCode.validator_error_not_enough_data
                      else
                        (let pos' =
                           let h6 = FStar_HyperStack_ST.get () in
                           FStar_Int_Cast.uint32_to_uint64
                             (FStar_UInt32.add
                                (FStar_Int_Cast.uint64_to_uint32 res) va) in
                         if LowParse_Low_ErrorCode.is_error pos'
                         then
                           (if
                              pos' =
                                LowParse_Low_ErrorCode.validator_error_not_enough_data
                            then
                              LowParse_Low_ErrorCode.validator_error_generic
                            else pos')
                         else pos'))
                   else LowParse_Low_ErrorCode.validator_error_generic)
let (validate_bounded_vlbytes :
  Prims.nat ->
    Prims.nat ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              let h3 = FStar_HyperStack_ST.get () in
              let res =
                let h4 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t
                       (if max < (Prims.of_int (256))
                        then Prims.int_one
                        else
                          if max < (Prims.parse_int "65536")
                          then (Prims.of_int (2))
                          else
                            if max < (Prims.parse_int "16777216")
                            then (Prims.of_int (3))
                            else (Prims.of_int (4))))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t
                       (if max < (Prims.of_int (256))
                        then Prims.int_one
                        else
                          if max < (Prims.parse_int "65536")
                          then (Prims.of_int (2))
                          else
                            if max < (Prims.parse_int "16777216")
                            then (Prims.of_int (3))
                            else (Prims.of_int (4)))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   (match if max < (Prims.of_int (256))
                          then Prims.int_one
                          else
                            if max < (Prims.parse_int "65536")
                            then (Prims.of_int (2))
                            else
                              if max < (Prims.parse_int "16777216")
                              then (Prims.of_int (3))
                              else (Prims.of_int (4))
                    with
                    | uu___1 when uu___1 = Prims.int_one ->
                        LowParse_Low_BoundedInt.read_bounded_integer_1 ()
                    | uu___1 when uu___1 = (Prims.of_int (2)) ->
                        LowParse_Low_BoundedInt.read_bounded_integer_2 ()
                    | uu___1 when uu___1 = (Prims.of_int (3)) ->
                        LowParse_Low_BoundedInt.read_bounded_integer_3 ()
                    | uu___1 when uu___1 = (Prims.of_int (4)) ->
                        LowParse_Low_BoundedInt.read_bounded_integer_4 ()) ()
                     () input (FStar_Int_Cast.uint64_to_uint32 pos) in
                 if
                   (if min = Prims.int_zero
                    then FStar_UInt32.lte va (FStar_UInt32.uint_to_t max)
                    else
                      (FStar_UInt32.lte (FStar_UInt32.uint_to_t min) va) &&
                        (FStar_UInt32.lte va (FStar_UInt32.uint_to_t max)))
                 then
                   let h4 = FStar_HyperStack_ST.get () in
                   let h5 = FStar_HyperStack_ST.get () in
                   (if
                      FStar_UInt64.lt
                        (FStar_UInt64.sub
                           (FStar_Int_Cast.uint32_to_uint64
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len;_} -> len)) res)
                        (FStar_Int_Cast.uint32_to_uint64 va)
                    then
                      LowParse_Low_ErrorCode.validator_error_not_enough_data
                    else
                      (let pos' =
                         let h6 = FStar_HyperStack_ST.get () in
                         FStar_Int_Cast.uint32_to_uint64
                           (FStar_UInt32.add
                              (FStar_Int_Cast.uint64_to_uint32 res) va) in
                       if LowParse_Low_ErrorCode.is_error pos'
                       then
                         (if
                            pos' =
                              LowParse_Low_ErrorCode.validator_error_not_enough_data
                          then LowParse_Low_ErrorCode.validator_error_generic
                          else pos')
                       else pos'))
                 else LowParse_Low_ErrorCode.validator_error_generic)
let (jump_all_bytes :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            match input with
            | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                len
let (jump_bounded_vlbytes' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let uu___ =
                  let uu___1 =
                    match l with
                    | uu___2 when uu___2 = Prims.int_one ->
                        (LowParse_Low_BoundedInt.read_bounded_integer_1 ())
                          () () input pos
                    | uu___2 when uu___2 = (Prims.of_int (2)) ->
                        (LowParse_Low_BoundedInt.read_bounded_integer_2 ())
                          () () input pos
                    | uu___2 when uu___2 = (Prims.of_int (3)) ->
                        (LowParse_Low_BoundedInt.read_bounded_integer_3 ())
                          () () input pos
                    | uu___2 when uu___2 = (Prims.of_int (4)) ->
                        (LowParse_Low_BoundedInt.read_bounded_integer_4 ())
                          () () input pos in
                  FStar_UInt32.add (FStar_UInt32.uint_to_t l) uu___1 in
                FStar_UInt32.add pos uu___
let (jump_bounded_vlbytes :
  Prims.nat ->
    Prims.nat ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              let h3 = FStar_HyperStack_ST.get () in
              let uu___ =
                let uu___1 =
                  match if max < (Prims.of_int (256))
                        then Prims.int_one
                        else
                          if max < (Prims.parse_int "65536")
                          then (Prims.of_int (2))
                          else
                            if max < (Prims.parse_int "16777216")
                            then (Prims.of_int (3))
                            else (Prims.of_int (4))
                  with
                  | uu___2 when uu___2 = Prims.int_one ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_1 ()) ()
                        () input pos
                  | uu___2 when uu___2 = (Prims.of_int (2)) ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_2 ()) ()
                        () input pos
                  | uu___2 when uu___2 = (Prims.of_int (3)) ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_3 ()) ()
                        () input pos
                  | uu___2 when uu___2 = (Prims.of_int (4)) ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_4 ()) ()
                        () input pos in
                FStar_UInt32.add
                  (FStar_UInt32.uint_to_t
                     (if max < (Prims.of_int (256))
                      then Prims.int_one
                      else
                        if max < (Prims.parse_int "65536")
                        then (Prims.of_int (2))
                        else
                          if max < (Prims.parse_int "16777216")
                          then (Prims.of_int (3))
                          else (Prims.of_int (4)))) uu___1 in
              FStar_UInt32.add pos uu___




let (bounded_vlbytes'_payload_length :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let len =
                  match l with
                  | uu___ when uu___ = Prims.int_one ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_1 ()) ()
                        () input pos
                  | uu___ when uu___ = (Prims.of_int (2)) ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_2 ()) ()
                        () input pos
                  | uu___ when uu___ = (Prims.of_int (3)) ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_3 ()) ()
                        () input pos
                  | uu___ when uu___ = (Prims.of_int (4)) ->
                      (LowParse_Low_BoundedInt.read_bounded_integer_4 ()) ()
                        () input pos in
                len
let (bounded_vlbytes_payload_length :
  Prims.nat ->
    Prims.nat ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let len =
                match if max < (Prims.of_int (256))
                      then Prims.int_one
                      else
                        if max < (Prims.parse_int "65536")
                        then (Prims.of_int (2))
                        else
                          if max < (Prims.parse_int "16777216")
                          then (Prims.of_int (3))
                          else (Prims.of_int (4))
                with
                | uu___ when uu___ = Prims.int_one ->
                    (LowParse_Low_BoundedInt.read_bounded_integer_1 ()) () ()
                      input pos
                | uu___ when uu___ = (Prims.of_int (2)) ->
                    (LowParse_Low_BoundedInt.read_bounded_integer_2 ()) () ()
                      input pos
                | uu___ when uu___ = (Prims.of_int (3)) ->
                    (LowParse_Low_BoundedInt.read_bounded_integer_3 ()) () ()
                      input pos
                | uu___ when uu___ = (Prims.of_int (4)) ->
                    (LowParse_Low_BoundedInt.read_bounded_integer_4 ()) () ()
                      input pos in
              len
let (get_vlbytes'_contents :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        ((LowParse_Bytes.byte, unit, unit) LowStar_Buffer.trivial_preorder,
          (LowParse_Bytes.byte, unit, unit) LowStar_Buffer.trivial_preorder)
          LowParse_Slice.slice ->
          FStar_UInt32.t -> LowParse_Bytes.byte LowStar_Buffer.buffer)
  =
  fun min ->
    fun max ->
      fun l ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let len =
              (match l with
               | uu___ when uu___ = Prims.int_one ->
                   LowParse_Low_BoundedInt.read_bounded_integer_1 ()
               | uu___ when uu___ = (Prims.of_int (2)) ->
                   LowParse_Low_BoundedInt.read_bounded_integer_2 ()
               | uu___ when uu___ = (Prims.of_int (3)) ->
                   LowParse_Low_BoundedInt.read_bounded_integer_3 ()
               | uu___ when uu___ = (Prims.of_int (4)) ->
                   LowParse_Low_BoundedInt.read_bounded_integer_4 ()) () ()
                (Obj.magic input) pos in
            LowStar_Monotonic_Buffer.msub
              (match input with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                   -> base) (FStar_UInt32.add pos (FStar_UInt32.uint_to_t l))
              ()
let (get_vlbytes_contents :
  Prims.nat ->
    Prims.nat ->
      ((LowParse_Bytes.byte, unit, unit) LowStar_Buffer.trivial_preorder,
        (LowParse_Bytes.byte, unit, unit) LowStar_Buffer.trivial_preorder)
        LowParse_Slice.slice ->
        FStar_UInt32.t -> LowParse_Bytes.byte LowStar_Buffer.buffer)
  =
  fun min ->
    fun max ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let len =
            (match if max < (Prims.of_int (256))
                   then Prims.int_one
                   else
                     if max < (Prims.parse_int "65536")
                     then (Prims.of_int (2))
                     else
                       if max < (Prims.parse_int "16777216")
                       then (Prims.of_int (3))
                       else (Prims.of_int (4))
             with
             | uu___ when uu___ = Prims.int_one ->
                 LowParse_Low_BoundedInt.read_bounded_integer_1 ()
             | uu___ when uu___ = (Prims.of_int (2)) ->
                 LowParse_Low_BoundedInt.read_bounded_integer_2 ()
             | uu___ when uu___ = (Prims.of_int (3)) ->
                 LowParse_Low_BoundedInt.read_bounded_integer_3 ()
             | uu___ when uu___ = (Prims.of_int (4)) ->
                 LowParse_Low_BoundedInt.read_bounded_integer_4 ()) () ()
              (Obj.magic input) pos in
          LowStar_Monotonic_Buffer.msub
            (match input with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_} ->
                 base)
            (FStar_UInt32.add pos
               (FStar_UInt32.uint_to_t
                  (if max < (Prims.of_int (256))
                   then Prims.int_one
                   else
                     if max < (Prims.parse_int "65536")
                     then (Prims.of_int (2))
                     else
                       if max < (Prims.parse_int "16777216")
                       then (Prims.of_int (3))
                       else (Prims.of_int (4))))) ()
type ('min, 'max, 'length, 'x) clens_vlbytes_cond = unit
let (clens_vlbytes :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        ((unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t,
          unit FStar_Bytes.lbytes) LowParse_Low_Base_Spec.clens)
  =
  fun min ->
    fun max ->
      fun length ->
        {
          LowParse_Low_Base_Spec.clens_cond = ();
          LowParse_Low_Base_Spec.clens_get = ()
        }



let (accessor_vlbytes' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun length ->
          fun rrel ->
            fun rel ->
              fun sl ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  FStar_UInt32.add pos (FStar_UInt32.uint_to_t l)
let (accessor_vlbytes :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun length ->
        fun rrel ->
          fun rel ->
            fun sl ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos
                  (FStar_UInt32.uint_to_t
                     (if max < (Prims.of_int (256))
                      then Prims.int_one
                      else
                        if max < (Prims.parse_int "65536")
                        then (Prims.of_int (2))
                        else
                          if max < (Prims.parse_int "16777216")
                          then (Prims.of_int (3))
                          else (Prims.of_int (4))))
let (clens_vlbytes_slice :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          ((unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t,
            unit FStar_Bytes.lbytes) LowParse_Low_Base_Spec.clens)
  =
  fun min ->
    fun max ->
      fun from ->
        fun to1 ->
          {
            LowParse_Low_Base_Spec.clens_cond = ();
            LowParse_Low_Base_Spec.clens_get = ()
          }



let (accessor_vlbytes'_slice :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        FStar_UInt32.t ->
          FStar_UInt32.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun from ->
          fun to1 ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add
                      (FStar_UInt32.add pos (FStar_UInt32.uint_to_t l)) from
let (accessor_vlbytes_slice :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun from ->
        fun to1 ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  FStar_UInt32.add
                    (FStar_UInt32.add pos
                       (FStar_UInt32.uint_to_t
                          (if max < (Prims.of_int (256))
                           then Prims.int_one
                           else
                             if max < (Prims.parse_int "65536")
                             then (Prims.of_int (2))
                             else
                               if max < (Prims.parse_int "16777216")
                               then (Prims.of_int (3))
                               else (Prims.of_int (4))))) from
let (clens_vlbytes_get :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        ((unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t,
          LowParse_Bytes.byte) LowParse_Low_Base_Spec.clens)
  =
  fun min ->
    fun max ->
      fun i ->
        {
          LowParse_Low_Base_Spec.clens_cond = ();
          LowParse_Low_Base_Spec.clens_get = ()
        }


let (accessor_vlbytes'_get :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun i ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  FStar_UInt32.add
                    (FStar_UInt32.add pos (FStar_UInt32.uint_to_t l)) i

let (accessor_vlbytes_get :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun i ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                FStar_UInt32.add
                  (FStar_UInt32.add pos
                     (FStar_UInt32.uint_to_t
                        (if max < (Prims.of_int (256))
                         then Prims.int_one
                         else
                           if max < (Prims.parse_int "65536")
                           then (Prims.of_int (2))
                           else
                             if max < (Prims.parse_int "16777216")
                             then (Prims.of_int (3))
                             else (Prims.of_int (4))))) i


let (finalize_bounded_vlbytes' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                fun len ->
                  let h0 = FStar_HyperStack_ST.get () in
                  let pos_payload =
                    match l with
                    | uu___ when uu___ = Prims.int_one ->
                        let h01 = FStar_HyperStack_ST.get () in
                        let len1 =
                          LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                            () len () ()
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len2;_} -> base) pos in
                        let h = FStar_HyperStack_ST.get () in
                        FStar_UInt32.add pos len1
                    | uu___ when uu___ = (Prims.of_int (2)) ->
                        let h01 = FStar_HyperStack_ST.get () in
                        let len1 =
                          LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                            () len () ()
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len2;_} -> base) pos in
                        let h = FStar_HyperStack_ST.get () in
                        FStar_UInt32.add pos len1
                    | uu___ when uu___ = (Prims.of_int (3)) ->
                        let h01 = FStar_HyperStack_ST.get () in
                        let len1 =
                          LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                            () len () ()
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len2;_} -> base) pos in
                        let h = FStar_HyperStack_ST.get () in
                        FStar_UInt32.add pos len1
                    | uu___ when uu___ = (Prims.of_int (4)) ->
                        let h01 = FStar_HyperStack_ST.get () in
                        let len1 =
                          LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                            () len () ()
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len2;_} -> base) pos in
                        let h = FStar_HyperStack_ST.get () in
                        FStar_UInt32.add pos len1 in
                  let h = FStar_HyperStack_ST.get () in
                  FStar_UInt32.add pos_payload len
let (finalize_bounded_vlbytes :
  Prims.nat ->
    Prims.nat ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              fun len ->
                let h0 = FStar_HyperStack_ST.get () in
                let pos_payload =
                  match if max < (Prims.of_int (256))
                        then Prims.int_one
                        else
                          if max < (Prims.parse_int "65536")
                          then (Prims.of_int (2))
                          else
                            if max < (Prims.parse_int "16777216")
                            then (Prims.of_int (3))
                            else (Prims.of_int (4))
                  with
                  | uu___ when uu___ = Prims.int_one ->
                      let h01 = FStar_HyperStack_ST.get () in
                      let len1 =
                        LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                          () len () ()
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len2;_} -> base) pos in
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos len1
                  | uu___ when uu___ = (Prims.of_int (2)) ->
                      let h01 = FStar_HyperStack_ST.get () in
                      let len1 =
                        LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                          () len () ()
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len2;_} -> base) pos in
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos len1
                  | uu___ when uu___ = (Prims.of_int (3)) ->
                      let h01 = FStar_HyperStack_ST.get () in
                      let len1 =
                        LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                          () len () ()
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len2;_} -> base) pos in
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos len1
                  | uu___ when uu___ = (Prims.of_int (4)) ->
                      let h01 = FStar_HyperStack_ST.get () in
                      let len1 =
                        LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                          () len () ()
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len2;_} -> base) pos in
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos len1 in
                let h = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos_payload len
let (validate_bounded_vlgenbytes :
  LowParse_Spec_DER.der_length_t ->
    FStar_UInt32.t ->
      LowParse_Spec_DER.der_length_t ->
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
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun kk ->
            fun pk ->
              fun vk ->
                fun rk ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let h1 = FStar_HyperStack_ST.get () in
                          let n = vk () () input pos in
                          if LowParse_Low_ErrorCode.is_error n
                          then n
                          else
                            (let len =
                               rk () () input
                                 (FStar_Int_Cast.uint64_to_uint32 pos) in
                             let h2 = FStar_HyperStack_ST.get () in
                             let h3 = FStar_HyperStack_ST.get () in
                             if
                               FStar_UInt64.lt
                                 (FStar_UInt64.sub
                                    (FStar_Int_Cast.uint32_to_uint64
                                       (match input with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len1;_} ->
                                            len1)) n)
                                 (FStar_Int_Cast.uint32_to_uint64 len)
                             then
                               LowParse_Low_ErrorCode.validator_error_not_enough_data
                             else
                               (let pos' =
                                  let h4 = FStar_HyperStack_ST.get () in
                                  FStar_Int_Cast.uint32_to_uint64
                                    (FStar_UInt32.add
                                       (FStar_Int_Cast.uint64_to_uint32 n)
                                       len) in
                                if LowParse_Low_ErrorCode.is_error pos'
                                then
                                  (if
                                     pos' =
                                       LowParse_Low_ErrorCode.validator_error_not_enough_data
                                   then
                                     LowParse_Low_ErrorCode.validator_error_generic
                                   else pos')
                                else pos'))
let (jump_bounded_vlgenbytes :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
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
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun kk ->
        fun pk ->
          fun vk ->
            fun rk ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      let h1 = FStar_HyperStack_ST.get () in
                      let n = vk () () input pos in
                      let len = rk () () input pos in
                      let h2 = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add n len
let (bounded_vlgenbytes_payload_length :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      LowParse_Spec_Base.parser_kind ->
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
  fun vmin ->
    fun vmax ->
      fun kk ->
        fun pk ->
          fun rk ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let len = rk () () input pos in len
let (get_bounded_vlgenbytes_contents :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
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
              ((LowParse_Bytes.byte, unit, unit)
                 LowStar_Buffer.trivial_preorder,
                (LowParse_Bytes.byte, unit, unit)
                  LowStar_Buffer.trivial_preorder)
                LowParse_Slice.slice ->
                FStar_UInt32.t -> LowParse_Bytes.byte LowStar_Buffer.buffer)
  =
  fun vmin ->
    fun vmax ->
      fun kk ->
        fun pk ->
          fun rk ->
            fun jk ->
              fun input ->
                fun pos ->
                  let len =
                    let h = FStar_HyperStack_ST.get () in
                    let len1 = rk () () (Obj.magic input) pos in len1 in
                  let pos1 = jk () () (Obj.magic input) pos in
                  LowStar_Monotonic_Buffer.msub
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len1;_} -> base) pos1 ()

