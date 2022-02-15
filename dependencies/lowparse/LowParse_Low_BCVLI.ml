open Prims
let (validate_bcvli :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let pos1 =
            let h1 = FStar_HyperStack_ST.get () in
            if
              FStar_UInt64.lt
                (FStar_UInt64.sub
                   (FStar_Int_Cast.uint32_to_uint64
                      (match input with
                       | { LowParse_Slice.base = base;
                           LowParse_Slice.len = len;_} -> len)) pos)
                (FStar_UInt64.uint_to_t Prims.int_one)
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else FStar_UInt64.add pos (FStar_UInt64.uint_to_t Prims.int_one) in
          if LowParse_Low_ErrorCode.is_error pos1
          then pos1
          else
            (let r =
               LowParse_Low_BoundedInt.read_bounded_integer_le_1 () () input
                 (FStar_Int_Cast.uint64_to_uint32 pos) in
             if
               FStar_UInt32.lt r
                 (FStar_UInt32.uint_to_t (Prims.of_int (253)))
             then pos1
             else
               if r = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
               then
                 (let pos2 =
                    let h1 = FStar_HyperStack_ST.get () in
                    if
                      FStar_UInt64.lt
                        (FStar_UInt64.sub
                           (FStar_Int_Cast.uint32_to_uint64
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len;_} -> len)) pos1)
                        (FStar_UInt64.uint_to_t (Prims.of_int (2)))
                    then
                      LowParse_Low_ErrorCode.validator_error_not_enough_data
                    else
                      FStar_UInt64.add pos1
                        (FStar_UInt64.uint_to_t (Prims.of_int (2))) in
                  if LowParse_Low_ErrorCode.is_error pos2
                  then pos2
                  else
                    (let r1 =
                       LowParse_Low_BoundedInt.read_bounded_integer_le_2 ()
                         () input (FStar_Int_Cast.uint64_to_uint32 pos1) in
                     if
                       FStar_UInt32.lt r1
                         (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                     then LowParse_Low_ErrorCode.validator_error_generic
                     else pos2))
               else
                 if r = (FStar_UInt32.uint_to_t (Prims.of_int (254)))
                 then
                   (let pos2 =
                      let h1 = FStar_HyperStack_ST.get () in
                      if
                        FStar_UInt64.lt
                          (FStar_UInt64.sub
                             (FStar_Int_Cast.uint32_to_uint64
                                (match input with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len;_} -> len))
                             pos1)
                          (FStar_UInt64.uint_to_t (Prims.of_int (4)))
                      then
                        LowParse_Low_ErrorCode.validator_error_not_enough_data
                      else
                        FStar_UInt64.add pos1
                          (FStar_UInt64.uint_to_t (Prims.of_int (4))) in
                    if LowParse_Low_ErrorCode.is_error pos2
                    then pos2
                    else
                      (let r1 =
                         LowParse_Low_BoundedInt.read_bounded_integer_le_4 ()
                           () input (FStar_Int_Cast.uint64_to_uint32 pos1) in
                       if
                         FStar_UInt32.lt r1
                           (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                       then LowParse_Low_ErrorCode.validator_error_generic
                       else pos2))
                 else LowParse_Low_ErrorCode.validator_error_generic)
let (jump_bcvli :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let pos1 =
            let h1 = FStar_HyperStack_ST.get () in
            FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one) in
          let r =
            LowParse_Low_BoundedInt.read_bounded_integer_le_1 () () input pos in
          if FStar_UInt32.lt r (FStar_UInt32.uint_to_t (Prims.of_int (253)))
          then pos1
          else
            if r = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
            then
              (let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos1
                 (FStar_UInt32.uint_to_t (Prims.of_int (2))))
            else
              (let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos1
                 (FStar_UInt32.uint_to_t (Prims.of_int (4))))
let (read_bcvli :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let r =
            LowParse_Low_BoundedInt.read_bounded_integer_le_1 () () input pos in
          if FStar_UInt32.lt r (FStar_UInt32.uint_to_t (Prims.of_int (253)))
          then r
          else
            (let pos1 =
               let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one) in
             if r = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
             then
               LowParse_Low_BoundedInt.read_bounded_integer_le_2 () () input
                 pos1
             else
               LowParse_Low_BoundedInt.read_bounded_integer_le_4 () () input
                 pos1)
let (serialize32_bcvli' :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (FStar_UInt8.t, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let c =
              if
                FStar_UInt32.lt x
                  (FStar_UInt32.uint_to_t (Prims.of_int (253)))
              then x
              else
                if
                  FStar_UInt32.lt x
                    (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                then FStar_UInt32.uint_to_t (Prims.of_int (253))
                else FStar_UInt32.uint_to_t (Prims.of_int (254)) in
            let h = FStar_HyperStack_ST.get () in
            let len1 =
              LowParse_Low_BoundedInt.serialize32_bounded_integer_le_1 c ()
                () b pos in
            let h1 = FStar_HyperStack_ST.get () in
            if
              FStar_UInt32.lt c (FStar_UInt32.uint_to_t (Prims.of_int (253)))
            then len1
            else
              if c = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
              then
                (let len2 =
                   LowParse_Low_BoundedInt.serialize32_bounded_integer_le_2 x
                     () () b (FStar_UInt32.add pos len1) in
                 let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add len1 len2)
              else
                (let len2 =
                   LowParse_Low_BoundedInt.serialize32_bounded_integer_le_4 x
                     () () b (FStar_UInt32.add pos len1) in
                 let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add len1 len2)
let (serialize32_bcvli :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let c =
              if
                FStar_UInt32.lt x
                  (FStar_UInt32.uint_to_t (Prims.of_int (253)))
              then x
              else
                if
                  FStar_UInt32.lt x
                    (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                then FStar_UInt32.uint_to_t (Prims.of_int (253))
                else FStar_UInt32.uint_to_t (Prims.of_int (254)) in
            let h = FStar_HyperStack_ST.get () in
            let len1 =
              LowParse_Low_BoundedInt.serialize32_bounded_integer_le_1 c ()
                () b pos in
            let h1 = FStar_HyperStack_ST.get () in
            if
              FStar_UInt32.lt c (FStar_UInt32.uint_to_t (Prims.of_int (253)))
            then len1
            else
              if c = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
              then
                (let len2 =
                   LowParse_Low_BoundedInt.serialize32_bounded_integer_le_2 x
                     () () b (FStar_UInt32.add pos len1) in
                 let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add len1 len2)
              else
                (let len2 =
                   LowParse_Low_BoundedInt.serialize32_bounded_integer_le_4 x
                     () () b (FStar_UInt32.add pos len1) in
                 let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add len1 len2)
let (write_bcvli :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h0 = FStar_HyperStack_ST.get () in
            let len =
              let c =
                if
                  FStar_UInt32.lt x
                    (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                then x
                else
                  if
                    FStar_UInt32.lt x
                      (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                  then FStar_UInt32.uint_to_t (Prims.of_int (253))
                  else FStar_UInt32.uint_to_t (Prims.of_int (254)) in
              let h = FStar_HyperStack_ST.get () in
              let len1 =
                LowParse_Low_BoundedInt.serialize32_bounded_integer_le_1 c ()
                  ()
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len2;_} -> base) pos in
              let h1 = FStar_HyperStack_ST.get () in
              if
                FStar_UInt32.lt c
                  (FStar_UInt32.uint_to_t (Prims.of_int (253)))
              then len1
              else
                if c = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                then
                  (let len2 =
                     LowParse_Low_BoundedInt.serialize32_bounded_integer_le_2
                       x () ()
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len3;_} -> base)
                       (FStar_UInt32.add pos len1) in
                   let h' = FStar_HyperStack_ST.get () in
                   FStar_UInt32.add len1 len2)
                else
                  (let len2 =
                     LowParse_Low_BoundedInt.serialize32_bounded_integer_le_4
                       x () ()
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len3;_} -> base)
                       (FStar_UInt32.add pos len1) in
                   let h' = FStar_HyperStack_ST.get () in
                   FStar_UInt32.add len1 len2) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (validate_bounded_bcvli' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let pos1 =
                let h1 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t Prims.int_one)
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos (FStar_UInt64.uint_to_t Prims.int_one) in
              if LowParse_Low_ErrorCode.is_error pos1
              then pos1
              else
                (let r =
                   LowParse_Low_BoundedInt.read_bounded_integer_le_1 () ()
                     input (FStar_Int_Cast.uint64_to_uint32 pos) in
                 if
                   ((FStar_UInt32.lt r
                       (FStar_UInt32.uint_to_t (Prims.of_int (253))))
                      && (FStar_UInt32.lte min32 r))
                     && (FStar_UInt32.lte r max32)
                 then pos1
                 else
                   if
                     FStar_UInt32.lt max32
                       (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                   then LowParse_Low_ErrorCode.validator_error_generic
                   else
                     if r = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                     then
                       (if
                          FStar_UInt32.lte
                            (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                            min32
                        then LowParse_Low_ErrorCode.validator_error_generic
                        else
                          (let pos2 =
                             let h1 = FStar_HyperStack_ST.get () in
                             if
                               FStar_UInt64.lt
                                 (FStar_UInt64.sub
                                    (FStar_Int_Cast.uint32_to_uint64
                                       (match input with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            len)) pos1)
                                 (FStar_UInt64.uint_to_t (Prims.of_int (2)))
                             then
                               LowParse_Low_ErrorCode.validator_error_not_enough_data
                             else
                               FStar_UInt64.add pos1
                                 (FStar_UInt64.uint_to_t (Prims.of_int (2))) in
                           if LowParse_Low_ErrorCode.is_error pos2
                           then pos2
                           else
                             (let r1 =
                                LowParse_Low_BoundedInt.read_bounded_integer_le_2
                                  () () input
                                  (FStar_Int_Cast.uint64_to_uint32 pos1) in
                              if
                                ((FStar_UInt32.lt r1
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (253))))
                                   || (FStar_UInt32.lt r1 min32))
                                  || (FStar_UInt32.lt max32 r1)
                              then
                                LowParse_Low_ErrorCode.validator_error_generic
                              else pos2)))
                     else
                       if
                         FStar_UInt32.lt max32
                           (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                       then LowParse_Low_ErrorCode.validator_error_generic
                       else
                         if r = (FStar_UInt32.uint_to_t (Prims.of_int (254)))
                         then
                           (let pos2 =
                              let h1 = FStar_HyperStack_ST.get () in
                              if
                                FStar_UInt64.lt
                                  (FStar_UInt64.sub
                                     (FStar_Int_Cast.uint32_to_uint64
                                        (match input with
                                         | { LowParse_Slice.base = base;
                                             LowParse_Slice.len = len;_} ->
                                             len)) pos1)
                                  (FStar_UInt64.uint_to_t (Prims.of_int (4)))
                              then
                                LowParse_Low_ErrorCode.validator_error_not_enough_data
                              else
                                FStar_UInt64.add pos1
                                  (FStar_UInt64.uint_to_t (Prims.of_int (4))) in
                            if LowParse_Low_ErrorCode.is_error pos2
                            then pos2
                            else
                              (let r1 =
                                 LowParse_Low_BoundedInt.read_bounded_integer_le_4
                                   () () input
                                   (FStar_Int_Cast.uint64_to_uint32 pos1) in
                               if
                                 ((FStar_UInt32.lt r1
                                     (FStar_UInt32.uint_to_t
                                        (Prims.parse_int "65536")))
                                    || (FStar_UInt32.lt r1 min32))
                                   || (FStar_UInt32.lt max32 r1)
                               then
                                 LowParse_Low_ErrorCode.validator_error_generic
                               else pos2))
                         else LowParse_Low_ErrorCode.validator_error_generic)