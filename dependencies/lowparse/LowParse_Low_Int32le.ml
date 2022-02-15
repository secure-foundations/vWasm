open Prims
let (read_int32le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let h1 = FStar_HyperStack_ST.get () in
          let r0 =
            LowStar_Monotonic_Buffer.index
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base) pos in
          let r1 =
            LowStar_Monotonic_Buffer.index
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base)
              (FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one)) in
          let r2 =
            LowStar_Monotonic_Buffer.index
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base)
              (FStar_UInt32.add pos
                 (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
          let r3 =
            LowStar_Monotonic_Buffer.index
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base)
              (FStar_UInt32.add pos
                 (FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
          FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 r0)
            (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (256)))
               (FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 r1)
                  (FStar_UInt32.mul
                     (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                     (FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 r2)
                        (FStar_UInt32.mul
                           (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                           (FStar_Int_Cast.uint8_to_uint32 r3))))))
let (validate_int32le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t)
  =
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
              (FStar_UInt64.uint_to_t (Prims.of_int (4)))
          then LowParse_Low_ErrorCode.validator_error_not_enough_data
          else
            FStar_UInt64.add pos (FStar_UInt64.uint_to_t (Prims.of_int (4)))