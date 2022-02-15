open Prims
let (mul256 : FStar_UInt16.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.shift_left (FStar_Int_Cast.uint16_to_uint32 x)
      (FStar_UInt32.uint_to_t (Prims.of_int (8)))
let (div256 : FStar_UInt32.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.shift_right x (FStar_UInt32.uint_to_t (Prims.of_int (8)))
let (read_bounded_integer_1 :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let h1 = FStar_HyperStack_ST.get () in
            let r =
              LowStar_Monotonic_Buffer.index
                (match sl with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len;_}
                     -> base) pos in
            FStar_Int_Cast.uint8_to_uint32 r
let (read_bounded_integer_2 :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let h1 = FStar_HyperStack_ST.get () in
            let r =
              LowStar_Endianness.load16_be_i
                (match sl with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len;_}
                     -> base) pos in
            FStar_Int_Cast.uint16_to_uint32 r
let (read_bounded_integer_3 :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let h1 = FStar_HyperStack_ST.get () in
            let lo =
              LowStar_Monotonic_Buffer.index
                (match sl with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len;_}
                     -> base)
                (FStar_UInt32.add pos
                   (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
            let hi =
              LowStar_Endianness.load16_be_i
                (match sl with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len;_}
                     -> base) pos in
            FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
              (FStar_UInt32.shift_left (FStar_Int_Cast.uint16_to_uint32 hi)
                 (FStar_UInt32.uint_to_t (Prims.of_int (8))))
let (read_bounded_integer_4 :
  unit ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let h1 = FStar_HyperStack_ST.get () in
            LowStar_Endianness.load32_be_i
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base) pos
let (read_bounded_integer' :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun i ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            if i = (FStar_UInt32.uint_to_t Prims.int_one)
            then
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let r =
                LowStar_Monotonic_Buffer.index
                  (match sl with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base) pos in
              FStar_Int_Cast.uint8_to_uint32 r
            else
              if i = (FStar_UInt32.uint_to_t (Prims.of_int (2)))
              then
                (let h = FStar_HyperStack_ST.get () in
                 let h1 = FStar_HyperStack_ST.get () in
                 let r =
                   LowStar_Endianness.load16_be_i
                     (match sl with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base) pos in
                 FStar_Int_Cast.uint16_to_uint32 r)
              else
                if i = (FStar_UInt32.uint_to_t (Prims.of_int (3)))
                then
                  (let h = FStar_HyperStack_ST.get () in
                   let h1 = FStar_HyperStack_ST.get () in
                   let lo =
                     LowStar_Monotonic_Buffer.index
                       (match sl with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_UInt32.add pos
                          (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
                   let hi =
                     LowStar_Endianness.load16_be_i
                       (match sl with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base) pos in
                   FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                     (FStar_UInt32.shift_left
                        (FStar_Int_Cast.uint16_to_uint32 hi)
                        (FStar_UInt32.uint_to_t (Prims.of_int (8)))))
                else
                  (let h = FStar_HyperStack_ST.get () in
                   let h1 = FStar_HyperStack_ST.get () in
                   LowStar_Endianness.load32_be_i
                     (match sl with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base) pos)
let (read_bounded_integer_ct :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun i ->
    fun rrel ->
      fun rel ->
        fun sl ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let r =
              LowStar_Endianness.load32_be_i
                (match sl with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len;_}
                     -> base) pos in
            (match LowParse_BitFields.uint32 with
             | { LowParse_BitFields.v = v;
                 LowParse_BitFields.uint_to_t = uint_to_t;
                 LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                 LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                 LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
                 LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
                 LowParse_BitFields.get_bitfield = get_bitfield;
                 LowParse_BitFields.set_bitfield = set_bitfield;
                 LowParse_BitFields.logor = logor;
                 LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
                 LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
                 get_bitfield_gen) r
              (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                 (FStar_UInt32.sub
                    (FStar_UInt32.uint_to_t (Prims.of_int (4))) i))
              (FStar_UInt32.uint_to_t (Prims.of_int (32)))
let (validate_bounded_integer' :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun i ->
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
                (FStar_Int_Cast.uint32_to_uint64 i)
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else FStar_UInt64.add pos (FStar_Int_Cast.uint32_to_uint64 i)
let (jump_bounded_integer' :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun i ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos i
let (serialize32_bounded_integer_1 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (LowParse_Bytes.byte, Obj.t, Obj.t)
            LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun v ->
      fun rrel ->
        fun rel ->
          fun out ->
            fun pos ->
              (let h = FStar_HyperStack_ST.get () in
               LowStar_Monotonic_Buffer.upd' out pos
                 (FStar_Int_Cast.uint32_to_uint8 v));
              FStar_UInt32.uint_to_t Prims.int_one
let (serialize32_bounded_integer_2 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (LowParse_Bytes.byte, Obj.t, Obj.t)
            LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun v ->
      fun rrel ->
        fun rel ->
          fun out ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let v' = FStar_Int_Cast.uint32_to_uint16 v in
              LowStar_Endianness.store16_be_i out pos v';
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (2)))
let (serialize32_bounded_integer_3 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (LowParse_Bytes.byte, Obj.t, Obj.t)
            LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun v ->
      fun rrel ->
        fun rel ->
          fun out ->
            fun pos ->
              let lo = FStar_Int_Cast.uint32_to_uint8 v in
              (let h = FStar_HyperStack_ST.get () in
               LowStar_Monotonic_Buffer.upd' out
                 (FStar_UInt32.add pos
                    (FStar_UInt32.uint_to_t (Prims.of_int (2)))) lo);
              (let hi' =
                 FStar_UInt32.shift_right v
                   (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
               let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
               let h1 = FStar_HyperStack_ST.get () in
               LowStar_Endianness.store16_be_i out pos hi;
               (let h2 = FStar_HyperStack_ST.get () in
                FStar_UInt32.uint_to_t (Prims.of_int (3))))
let (serialize32_bounded_integer_4 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (LowParse_Bytes.byte, Obj.t, Obj.t)
            LowStar_Monotonic_Buffer.mbuffer ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun v ->
      fun rrel ->
        fun rel ->
          fun out ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              LowStar_Endianness.store32_be_i out pos v;
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (write_bounded_integer_1 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun x ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd'
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len1;_} -> base) pos
                   (FStar_Int_Cast.uint32_to_uint8 x));
                FStar_UInt32.uint_to_t Prims.int_one in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_bounded_integer_2 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun x ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                let h = FStar_HyperStack_ST.get () in
                let v' = FStar_Int_Cast.uint32_to_uint16 x in
                LowStar_Endianness.store16_be_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len1;_} -> base) pos v';
                (let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.uint_to_t (Prims.of_int (2))) in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_bounded_integer_3 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun x ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                let lo = FStar_Int_Cast.uint32_to_uint8 x in
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd'
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len1;_} -> base)
                   (FStar_UInt32.add pos
                      (FStar_UInt32.uint_to_t (Prims.of_int (2)))) lo);
                (let hi' =
                   FStar_UInt32.shift_right x
                     (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                 let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                 let h1 = FStar_HyperStack_ST.get () in
                 LowStar_Endianness.store16_be_i
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len1;_} -> base) pos hi;
                 (let h2 = FStar_HyperStack_ST.get () in
                  FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_bounded_integer_4 :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
    fun x ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                let h = FStar_HyperStack_ST.get () in
                LowStar_Endianness.store32_be_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len1;_} -> base) pos x;
                (let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.uint_to_t (Prims.of_int (4))) in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_bounded_integer' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun i ->
    fun v ->
      fun rrel ->
        fun rel ->
          fun sl ->
            fun pos ->
              if i = (FStar_UInt32.uint_to_t Prims.int_one)
              then
                let h0 = FStar_HyperStack_ST.get () in
                let len =
                  (let h = FStar_HyperStack_ST.get () in
                   LowStar_Monotonic_Buffer.upd'
                     (match sl with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) pos
                     (FStar_Int_Cast.uint32_to_uint8 v));
                  FStar_UInt32.uint_to_t Prims.int_one in
                let h = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos len
              else
                if i = (FStar_UInt32.uint_to_t (Prims.of_int (2)))
                then
                  (let h0 = FStar_HyperStack_ST.get () in
                   let len =
                     let h = FStar_HyperStack_ST.get () in
                     let v' = FStar_Int_Cast.uint32_to_uint16 v in
                     LowStar_Endianness.store16_be_i
                       (match sl with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len1;_} -> base) pos v';
                     (let h' = FStar_HyperStack_ST.get () in
                      FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                   let h = FStar_HyperStack_ST.get () in
                   FStar_UInt32.add pos len)
                else
                  if i = (FStar_UInt32.uint_to_t (Prims.of_int (3)))
                  then
                    (let h0 = FStar_HyperStack_ST.get () in
                     let len =
                       let lo = FStar_Int_Cast.uint32_to_uint8 v in
                       (let h = FStar_HyperStack_ST.get () in
                        LowStar_Monotonic_Buffer.upd'
                          (match sl with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len1;_} -> base)
                          (FStar_UInt32.add pos
                             (FStar_UInt32.uint_to_t (Prims.of_int (2)))) lo);
                       (let hi' =
                          FStar_UInt32.shift_right v
                            (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                        let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                        let h1 = FStar_HyperStack_ST.get () in
                        LowStar_Endianness.store16_be_i
                          (match sl with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len1;_} -> base) pos hi;
                        (let h2 = FStar_HyperStack_ST.get () in
                         FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                     let h = FStar_HyperStack_ST.get () in
                     FStar_UInt32.add pos len)
                  else
                    (let h0 = FStar_HyperStack_ST.get () in
                     let len =
                       let h = FStar_HyperStack_ST.get () in
                       LowStar_Endianness.store32_be_i
                         (match sl with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base) pos v;
                       (let h' = FStar_HyperStack_ST.get () in
                        FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                     let h = FStar_HyperStack_ST.get () in
                     FStar_UInt32.add pos len)
let (write_bounded_integer_1_weak :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
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
                  (FStar_UInt32.uint_to_t Prims.int_one)
              then LowParse_Low_ErrorCode.max_uint32
              else
                (let h = FStar_HyperStack_ST.get () in
                 let h0 = FStar_HyperStack_ST.get () in
                 let len =
                   (let h1 = FStar_HyperStack_ST.get () in
                    LowStar_Monotonic_Buffer.upd'
                      (match input with
                       | { LowParse_Slice.base = base;
                           LowParse_Slice.len = len1;_} -> base) pos
                      (FStar_Int_Cast.uint32_to_uint8 x));
                   FStar_UInt32.uint_to_t Prims.int_one in
                 let h1 = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add pos len)
let (write_bounded_integer_2_weak :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
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
                  (FStar_UInt32.uint_to_t (Prims.of_int (2)))
              then LowParse_Low_ErrorCode.max_uint32
              else
                (let h = FStar_HyperStack_ST.get () in
                 let h0 = FStar_HyperStack_ST.get () in
                 let len =
                   let h1 = FStar_HyperStack_ST.get () in
                   let v' = FStar_Int_Cast.uint32_to_uint16 x in
                   LowStar_Endianness.store16_be_i
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) pos v';
                   (let h' = FStar_HyperStack_ST.get () in
                    FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                 let h1 = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add pos len)
let (write_bounded_integer_3_weak :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
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
                  (FStar_UInt32.uint_to_t (Prims.of_int (3)))
              then LowParse_Low_ErrorCode.max_uint32
              else
                (let h = FStar_HyperStack_ST.get () in
                 let h0 = FStar_HyperStack_ST.get () in
                 let len =
                   let lo = FStar_Int_Cast.uint32_to_uint8 x in
                   (let h1 = FStar_HyperStack_ST.get () in
                    LowStar_Monotonic_Buffer.upd'
                      (match input with
                       | { LowParse_Slice.base = base;
                           LowParse_Slice.len = len1;_} -> base)
                      (FStar_UInt32.add pos
                         (FStar_UInt32.uint_to_t (Prims.of_int (2)))) lo);
                   (let hi' =
                      FStar_UInt32.shift_right x
                        (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                    let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                    let h1 = FStar_HyperStack_ST.get () in
                    LowStar_Endianness.store16_be_i
                      (match input with
                       | { LowParse_Slice.base = base;
                           LowParse_Slice.len = len1;_} -> base) pos hi;
                    (let h2 = FStar_HyperStack_ST.get () in
                     FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                 let h1 = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add pos len)
let (write_bounded_integer_4_weak :
  unit ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun uu___ ->
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
                  (FStar_UInt32.uint_to_t (Prims.of_int (4)))
              then LowParse_Low_ErrorCode.max_uint32
              else
                (let h = FStar_HyperStack_ST.get () in
                 let h0 = FStar_HyperStack_ST.get () in
                 let len =
                   let h1 = FStar_HyperStack_ST.get () in
                   LowStar_Endianness.store32_be_i
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len1;_} -> base) pos x;
                   (let h' = FStar_HyperStack_ST.get () in
                    FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                 let h1 = FStar_HyperStack_ST.get () in
                 FStar_UInt32.add pos len)
let (write_bounded_int32' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun x ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let pos' =
                    let res =
                      match sz with
                      | uu___ when uu___ = Prims.int_one ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            (let h = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd'
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len1;_} -> base) pos
                               (FStar_Int_Cast.uint32_to_uint8 x));
                            FStar_UInt32.uint_to_t Prims.int_one in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len
                      | uu___ when uu___ = (Prims.of_int (2)) ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            let h = FStar_HyperStack_ST.get () in
                            let v' = FStar_Int_Cast.uint32_to_uint16 x in
                            LowStar_Endianness.store16_be_i
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base) pos
                              v';
                            (let h' = FStar_HyperStack_ST.get () in
                             FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len
                      | uu___ when uu___ = (Prims.of_int (3)) ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            let lo = FStar_Int_Cast.uint32_to_uint8 x in
                            (let h = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd'
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len1;_} -> base)
                               (FStar_UInt32.add pos
                                  (FStar_UInt32.uint_to_t (Prims.of_int (2))))
                               lo);
                            (let hi' =
                               FStar_UInt32.shift_right x
                                 (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                             let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                             let h1 = FStar_HyperStack_ST.get () in
                             LowStar_Endianness.store16_be_i
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len1;_} -> base) pos
                               hi;
                             (let h2 = FStar_HyperStack_ST.get () in
                              FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len
                      | uu___ when uu___ = (Prims.of_int (4)) ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            let h = FStar_HyperStack_ST.get () in
                            LowStar_Endianness.store32_be_i
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base) pos
                              x;
                            (let h' = FStar_HyperStack_ST.get () in
                             FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len in
                    let h = FStar_HyperStack_ST.get () in res in
                  let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      (let h = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd'
                         (match input with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base) pos
                         (FStar_Int_Cast.uint32_to_uint8 x));
                      FStar_UInt32.uint_to_t Prims.int_one in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let h = FStar_HyperStack_ST.get () in
                      let v' = FStar_Int_Cast.uint32_to_uint16 x in
                      LowStar_Endianness.store16_be_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) pos v';
                      (let h' = FStar_HyperStack_ST.get () in
                       FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let lo = FStar_Int_Cast.uint32_to_uint8 x in
                      (let h = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd'
                         (match input with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base)
                         (FStar_UInt32.add pos
                            (FStar_UInt32.uint_to_t (Prims.of_int (2)))) lo);
                      (let hi' =
                         FStar_UInt32.shift_right x
                           (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                       let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                       let h1 = FStar_HyperStack_ST.get () in
                       LowStar_Endianness.store16_be_i
                         (match input with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base) pos hi;
                       (let h2 = FStar_HyperStack_ST.get () in
                        FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let h = FStar_HyperStack_ST.get () in
                      LowStar_Endianness.store32_be_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) pos x;
                      (let h' = FStar_HyperStack_ST.get () in
                       FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        fun rrel ->
          fun rel ->
            fun out ->
              fun pos ->
                if (FStar_UInt32.v max32) < (Prims.of_int (256))
                then write_bounded_int32_1 min32 max32 input () () out pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                  then write_bounded_int32_2 min32 max32 input () () out pos
                  else
                    if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                    then
                      write_bounded_int32_3 min32 max32 input () () out pos
                    else
                      write_bounded_int32_4 min32 max32 input () () out pos
let (read_bounded_int32' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let uu___ =
                  let h1 = FStar_HyperStack_ST.get () in
                  match sz with
                  | uu___1 when uu___1 = Prims.int_one ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      let r =
                        LowStar_Monotonic_Buffer.index
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base) pos in
                      FStar_Int_Cast.uint8_to_uint32 r
                  | uu___1 when uu___1 = (Prims.of_int (2)) ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      let r =
                        LowStar_Endianness.load16_be_i
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base) pos in
                      FStar_Int_Cast.uint16_to_uint32 r
                  | uu___1 when uu___1 = (Prims.of_int (3)) ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      let lo =
                        LowStar_Monotonic_Buffer.index
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base)
                          (FStar_UInt32.add pos
                             (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
                      let hi =
                        LowStar_Endianness.load16_be_i
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base) pos in
                      FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                        (FStar_UInt32.shift_left
                           (FStar_Int_Cast.uint16_to_uint32 hi)
                           (FStar_UInt32.uint_to_t (Prims.of_int (8))))
                  | uu___1 when uu___1 = (Prims.of_int (4)) ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      LowStar_Endianness.load32_be_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len;_} -> base) pos in
                uu___
let (read_bounded_int32_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let r =
                  LowStar_Monotonic_Buffer.index
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base) pos in
                FStar_Int_Cast.uint8_to_uint32 r in
              uu___
let (read_bounded_int32_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let r =
                  LowStar_Endianness.load16_be_i
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base) pos in
                FStar_Int_Cast.uint16_to_uint32 r in
              uu___
let (read_bounded_int32_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let lo =
                  LowStar_Monotonic_Buffer.index
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base)
                    (FStar_UInt32.add pos
                       (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
                let hi =
                  LowStar_Endianness.load16_be_i
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base) pos in
                FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                  (FStar_UInt32.shift_left
                     (FStar_Int_Cast.uint16_to_uint32 hi)
                     (FStar_UInt32.uint_to_t (Prims.of_int (8)))) in
              uu___
let (read_bounded_int32_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                LowStar_Endianness.load32_be_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base) pos in
              uu___
let (read_bounded_int32 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun sl ->
            fun pos ->
              if (FStar_UInt32.v max32) < (Prims.of_int (256))
              then read_bounded_int32_1 min32 max32 () () sl pos
              else
                if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                then read_bounded_int32_2 min32 max32 () () sl pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                  then read_bounded_int32_3 min32 max32 () () sl pos
                  else read_bounded_int32_4 min32 max32 () () sl pos
let (validate_bounded_int32' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in
                let res =
                  let h2 = FStar_HyperStack_ST.get () in
                  if
                    FStar_UInt64.lt
                      (FStar_UInt64.sub
                         (FStar_Int_Cast.uint32_to_uint64
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len;_} -> len)) pos)
                      (FStar_UInt64.uint_to_t sz)
                  then LowParse_Low_ErrorCode.validator_error_not_enough_data
                  else FStar_UInt64.add pos (FStar_UInt64.uint_to_t sz) in
                if LowParse_Low_ErrorCode.is_error res
                then res
                else
                  (let va =
                     (match sz with
                      | uu___1 when uu___1 = Prims.int_one ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   let r =
                                     LowStar_Monotonic_Buffer.index
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base) pos1 in
                                   FStar_Int_Cast.uint8_to_uint32 r)
                      | uu___1 when uu___1 = (Prims.of_int (2)) ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   let r =
                                     LowStar_Endianness.load16_be_i
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base) pos1 in
                                   FStar_Int_Cast.uint16_to_uint32 r)
                      | uu___1 when uu___1 = (Prims.of_int (3)) ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   let lo =
                                     LowStar_Monotonic_Buffer.index
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base)
                                       (FStar_UInt32.add pos1
                                          (FStar_UInt32.uint_to_t
                                             (Prims.of_int (2)))) in
                                   let hi =
                                     LowStar_Endianness.load16_be_i
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base) pos1 in
                                   FStar_UInt32.add
                                     (FStar_Int_Cast.uint8_to_uint32 lo)
                                     (FStar_UInt32.shift_left
                                        (FStar_Int_Cast.uint16_to_uint32 hi)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (8)))))
                      | uu___1 when uu___1 = (Prims.of_int (4)) ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   LowStar_Endianness.load32_be_i
                                     (match sl with
                                      | { LowParse_Slice.base = base;
                                          LowParse_Slice.len = len;_} -> base)
                                     pos1)) () () input
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   if
                     Prims.op_Negation
                       (Prims.op_Negation
                          ((FStar_UInt32.lt va min32) ||
                             (FStar_UInt32.lt max32 va)))
                   then LowParse_Low_ErrorCode.validator_error_generic
                   else res)
let (validate_bounded_int32_1 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
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
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   let r =
                     LowStar_Monotonic_Buffer.index
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   FStar_Int_Cast.uint8_to_uint32 r in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_2 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (2)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (2))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   let r =
                     LowStar_Endianness.load16_be_i
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   FStar_Int_Cast.uint16_to_uint32 r in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_3 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (3)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (3))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   let lo =
                     LowStar_Monotonic_Buffer.index
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_UInt32.add
                          (FStar_Int_Cast.uint64_to_uint32 pos)
                          (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
                   let hi =
                     LowStar_Endianness.load16_be_i
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                     (FStar_UInt32.shift_left
                        (FStar_Int_Cast.uint16_to_uint32 hi)
                        (FStar_UInt32.uint_to_t (Prims.of_int (8)))) in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_4 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (4)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (4))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   LowStar_Endianness.load32_be_i
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base)
                     (FStar_Int_Cast.uint64_to_uint32 pos) in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32 :
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
          fun sl ->
            fun pos ->
              if (FStar_UInt32.v max32) < (Prims.of_int (256))
              then validate_bounded_int32_1 min32 max32 () () sl pos
              else
                if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                then validate_bounded_int32_2 min32 max32 () () sl pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                  then validate_bounded_int32_3 min32 max32 () () sl pos
                  else validate_bounded_int32_4 min32 max32 () () sl pos
let (jump_bounded_int32' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos (FStar_UInt32.uint_to_t sz)
let (jump_bounded_int32_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one)
let (jump_bounded_int32_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (2)))
let (jump_bounded_int32_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (3)))
let (jump_bounded_int32_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (jump_bounded_int32 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun sl ->
            fun pos ->
              if (FStar_UInt32.v max32) < (Prims.of_int (256))
              then jump_bounded_int32_1 min32 max32 () () sl pos
              else
                if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                then jump_bounded_int32_2 min32 max32 () () sl pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                  then jump_bounded_int32_3 min32 max32 () () sl pos
                  else jump_bounded_int32_4 min32 max32 () () sl pos
let (validate_u16_le :
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
                (FStar_UInt64.uint_to_t (Prims.of_int (2)))
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (2)))
let (validate_u16_le_with_error_code :
  FStar_UInt64.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
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
                (FStar_UInt64.uint_to_t (Prims.of_int (2)))
            then
              LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                LowParse_Low_ErrorCode.validator_error_not_enough_data pos c
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (2)))
let (validate_u32_le :
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
                (FStar_UInt64.uint_to_t (Prims.of_int (4)))
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (4)))
let (validate_u32_le_with_error_code :
  FStar_UInt64.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
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
                (FStar_UInt64.uint_to_t (Prims.of_int (4)))
            then
              LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                LowParse_Low_ErrorCode.validator_error_not_enough_data pos c
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (4)))
let (jump_u16_le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t (Prims.of_int (2)))
let (jump_u32_le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (read_bounded_integer_le_1 :
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
          let r =
            LowStar_Monotonic_Buffer.index
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base) pos in
          FStar_Int_Cast.uint8_to_uint32 r
let (read_bounded_integer_le_2 :
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
          let r =
            LowStar_Endianness.load16_le_i
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base) pos in
          FStar_Int_Cast.uint16_to_uint32 r
let (read_bounded_integer_le_3 :
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
          let lo =
            LowStar_Monotonic_Buffer.index
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base) pos in
          let hi =
            LowStar_Endianness.load16_le_i
              (match sl with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base)
              (FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one)) in
          FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
            (FStar_UInt32.shift_left (FStar_Int_Cast.uint16_to_uint32 hi)
               (FStar_UInt32.uint_to_t (Prims.of_int (8))))
let (read_bounded_integer_le_4 :
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
          LowStar_Endianness.load32_le_i
            (match sl with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                 base) pos
let (read_u16_le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt16.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let uu___ =
            let h1 = FStar_HyperStack_ST.get () in
            let h2 = FStar_HyperStack_ST.get () in
            let r =
              LowStar_Endianness.load16_le_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len;_}
                     -> base) pos in
            FStar_Int_Cast.uint16_to_uint32 r in
          FStar_Int_Cast.uint32_to_uint16 uu___
let (read_u32_le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let uu___ =
            let h1 = FStar_HyperStack_ST.get () in
            let h2 = FStar_HyperStack_ST.get () in
            LowStar_Endianness.load32_le_i
              (match input with
               | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                   base) pos in
          uu___
let (serialize32_bounded_integer_le_1 :
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
            (let h = FStar_HyperStack_ST.get () in
             LowStar_Monotonic_Buffer.upd' b pos
               (FStar_Int_Cast.uint32_to_uint8 x));
            FStar_UInt32.uint_to_t Prims.int_one
let (write_bounded_integer_le_1 :
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
              (let h = FStar_HyperStack_ST.get () in
               LowStar_Monotonic_Buffer.upd'
                 (match input with
                  | { LowParse_Slice.base = base;
                      LowParse_Slice.len = len1;_} -> base) pos
                 (FStar_Int_Cast.uint32_to_uint8 x));
              FStar_UInt32.uint_to_t Prims.int_one in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (serialize32_bounded_integer_le_2 :
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
            let h = FStar_HyperStack_ST.get () in
            let x' = FStar_Int_Cast.uint32_to_uint16 x in
            LowStar_Endianness.store16_le_i b pos x';
            (let h' = FStar_HyperStack_ST.get () in
             FStar_UInt32.uint_to_t (Prims.of_int (2)))
let (write_bounded_integer_le_2 :
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
              let h = FStar_HyperStack_ST.get () in
              let x' = FStar_Int_Cast.uint32_to_uint16 x in
              LowStar_Endianness.store16_le_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                     -> base) pos x';
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (2))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (serialize32_bounded_integer_le_3 :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun out ->
          fun pos ->
            let lo = FStar_Int_Cast.uint32_to_uint8 v in
            (let h = FStar_HyperStack_ST.get () in
             LowStar_Monotonic_Buffer.upd' out pos lo);
            (let hi' =
               FStar_UInt32.shift_right v
                 (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
             let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
             let h1 = FStar_HyperStack_ST.get () in
             LowStar_Endianness.store16_le_i out
               (FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one))
               hi;
             (let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.uint_to_t (Prims.of_int (3))))
let (write_bounded_integer_le_3 :
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
              let lo = FStar_Int_Cast.uint32_to_uint8 x in
              (let h = FStar_HyperStack_ST.get () in
               LowStar_Monotonic_Buffer.upd'
                 (match input with
                  | { LowParse_Slice.base = base;
                      LowParse_Slice.len = len1;_} -> base) pos lo);
              (let hi' =
                 FStar_UInt32.shift_right x
                   (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
               let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
               let h1 = FStar_HyperStack_ST.get () in
               LowStar_Endianness.store16_le_i
                 (match input with
                  | { LowParse_Slice.base = base;
                      LowParse_Slice.len = len1;_} -> base)
                 (FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one))
                 hi;
               (let h2 = FStar_HyperStack_ST.get () in
                FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (serialize32_bounded_integer_le_4 :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun out ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            LowStar_Endianness.store32_le_i out pos v;
            (let h' = FStar_HyperStack_ST.get () in
             FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (write_bounded_integer_le_4 :
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
              let h = FStar_HyperStack_ST.get () in
              LowStar_Endianness.store32_le_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                     -> base) pos x;
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (4))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_u16_le :
  FStar_UInt16.t ->
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
            let pos' =
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                let h = FStar_HyperStack_ST.get () in
                let x' =
                  FStar_Int_Cast.uint32_to_uint16
                    (FStar_Int_Cast.uint16_to_uint32 x) in
                LowStar_Endianness.store16_le_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len1;_} -> base) pos x';
                (let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.uint_to_t (Prims.of_int (2))) in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len in
            let h = FStar_HyperStack_ST.get () in pos'
let (write_u32_le :
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
            let pos' =
              let h0 = FStar_HyperStack_ST.get () in
              let len =
                let h = FStar_HyperStack_ST.get () in
                LowStar_Endianness.store32_le_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len1;_} -> base) pos x;
                (let h' = FStar_HyperStack_ST.get () in
                 FStar_UInt32.uint_to_t (Prims.of_int (4))) in
              let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len in
            let h = FStar_HyperStack_ST.get () in pos'
let (validate_bounded_int32_le' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in
                let res =
                  let h2 = FStar_HyperStack_ST.get () in
                  if
                    FStar_UInt64.lt
                      (FStar_UInt64.sub
                         (FStar_Int_Cast.uint32_to_uint64
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len;_} -> len)) pos)
                      (FStar_UInt64.uint_to_t sz)
                  then LowParse_Low_ErrorCode.validator_error_not_enough_data
                  else FStar_UInt64.add pos (FStar_UInt64.uint_to_t sz) in
                if LowParse_Low_ErrorCode.is_error res
                then res
                else
                  (let va =
                     (match sz with
                      | uu___1 when uu___1 = Prims.int_one ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   let r =
                                     LowStar_Monotonic_Buffer.index
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base) pos1 in
                                   FStar_Int_Cast.uint8_to_uint32 r)
                      | uu___1 when uu___1 = (Prims.of_int (2)) ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   let r =
                                     LowStar_Endianness.load16_le_i
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base) pos1 in
                                   FStar_Int_Cast.uint16_to_uint32 r)
                      | uu___1 when uu___1 = (Prims.of_int (3)) ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   let lo =
                                     LowStar_Monotonic_Buffer.index
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base) pos1 in
                                   let hi =
                                     LowStar_Endianness.load16_le_i
                                       (match sl with
                                        | { LowParse_Slice.base = base;
                                            LowParse_Slice.len = len;_} ->
                                            base)
                                       (FStar_UInt32.add pos1
                                          (FStar_UInt32.uint_to_t
                                             Prims.int_one)) in
                                   FStar_UInt32.add
                                     (FStar_Int_Cast.uint8_to_uint32 lo)
                                     (FStar_UInt32.shift_left
                                        (FStar_Int_Cast.uint16_to_uint32 hi)
                                        (FStar_UInt32.uint_to_t
                                           (Prims.of_int (8)))))
                      | uu___1 when uu___1 = (Prims.of_int (4)) ->
                          (fun rrel1 ->
                             fun rel1 ->
                               fun sl ->
                                 fun pos1 ->
                                   let h2 = FStar_HyperStack_ST.get () in
                                   let h3 = FStar_HyperStack_ST.get () in
                                   LowStar_Endianness.load32_le_i
                                     (match sl with
                                      | { LowParse_Slice.base = base;
                                          LowParse_Slice.len = len;_} -> base)
                                     pos1)) () () input
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   if
                     Prims.op_Negation
                       (Prims.op_Negation
                          ((FStar_UInt32.lt va min32) ||
                             (FStar_UInt32.lt max32 va)))
                   then LowParse_Low_ErrorCode.validator_error_generic
                   else res)
let (validate_bounded_int32_le_1 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
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
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   let r =
                     LowStar_Monotonic_Buffer.index
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   FStar_Int_Cast.uint8_to_uint32 r in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_le_2 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (2)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (2))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   let r =
                     LowStar_Endianness.load16_le_i
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   FStar_Int_Cast.uint16_to_uint32 r in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_le_3 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (3)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (3))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   let lo =
                     LowStar_Monotonic_Buffer.index
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   let hi =
                     LowStar_Endianness.load16_le_i
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_UInt32.add
                          (FStar_Int_Cast.uint64_to_uint32 pos)
                          (FStar_UInt32.uint_to_t Prims.int_one)) in
                   FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                     (FStar_UInt32.shift_left
                        (FStar_Int_Cast.uint16_to_uint32 hi)
                        (FStar_UInt32.uint_to_t (Prims.of_int (8)))) in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_le_4 :
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
              let h1 = FStar_HyperStack_ST.get () in
              let res =
                let h2 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (4)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (4))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h2 = FStar_HyperStack_ST.get () in
                   let h3 = FStar_HyperStack_ST.get () in
                   LowStar_Endianness.load32_le_i
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base)
                     (FStar_Int_Cast.uint64_to_uint32 pos) in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (validate_bounded_int32_le :
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
          fun sl ->
            fun pos ->
              if (FStar_UInt32.v max32) < (Prims.of_int (256))
              then validate_bounded_int32_le_1 min32 max32 () () sl pos
              else
                if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                then validate_bounded_int32_le_2 min32 max32 () () sl pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                  then validate_bounded_int32_le_3 min32 max32 () () sl pos
                  else validate_bounded_int32_le_4 min32 max32 () () sl pos
let (jump_bounded_int32_le' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos (FStar_UInt32.uint_to_t sz)
let (jump_bounded_int32_le_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one)
let (jump_bounded_int32_le_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (2)))
let (jump_bounded_int32_le_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (3)))
let (jump_bounded_int32_le_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let h2 = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (jump_bounded_int32_le :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun sl ->
            fun pos ->
              if (FStar_UInt32.v max32) < (Prims.of_int (256))
              then jump_bounded_int32_le_1 min32 max32 () () sl pos
              else
                if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                then jump_bounded_int32_le_2 min32 max32 () () sl pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                  then jump_bounded_int32_le_3 min32 max32 () () sl pos
                  else jump_bounded_int32_le_4 min32 max32 () () sl pos
let (write_bounded_int32_le' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun x ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let pos' =
                    let res =
                      match sz with
                      | uu___ when uu___ = Prims.int_one ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            (let h = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd'
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len1;_} -> base) pos
                               (FStar_Int_Cast.uint32_to_uint8 x));
                            FStar_UInt32.uint_to_t Prims.int_one in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len
                      | uu___ when uu___ = (Prims.of_int (2)) ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            let h = FStar_HyperStack_ST.get () in
                            let x' = FStar_Int_Cast.uint32_to_uint16 x in
                            LowStar_Endianness.store16_le_i
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base) pos
                              x';
                            (let h' = FStar_HyperStack_ST.get () in
                             FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len
                      | uu___ when uu___ = (Prims.of_int (3)) ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            let lo = FStar_Int_Cast.uint32_to_uint8 x in
                            (let h = FStar_HyperStack_ST.get () in
                             LowStar_Monotonic_Buffer.upd'
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len1;_} -> base) pos
                               lo);
                            (let hi' =
                               FStar_UInt32.shift_right x
                                 (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                             let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                             let h1 = FStar_HyperStack_ST.get () in
                             LowStar_Endianness.store16_le_i
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len1;_} -> base)
                               (FStar_UInt32.add pos
                                  (FStar_UInt32.uint_to_t Prims.int_one)) hi;
                             (let h2 = FStar_HyperStack_ST.get () in
                              FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len
                      | uu___ when uu___ = (Prims.of_int (4)) ->
                          let h0 = FStar_HyperStack_ST.get () in
                          let len =
                            let h = FStar_HyperStack_ST.get () in
                            LowStar_Endianness.store32_le_i
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base) pos
                              x;
                            (let h' = FStar_HyperStack_ST.get () in
                             FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos len in
                    let h = FStar_HyperStack_ST.get () in res in
                  let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_le_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      (let h = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd'
                         (match input with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base) pos
                         (FStar_Int_Cast.uint32_to_uint8 x));
                      FStar_UInt32.uint_to_t Prims.int_one in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_le_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let h = FStar_HyperStack_ST.get () in
                      let x' = FStar_Int_Cast.uint32_to_uint16 x in
                      LowStar_Endianness.store16_le_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) pos x';
                      (let h' = FStar_HyperStack_ST.get () in
                       FStar_UInt32.uint_to_t (Prims.of_int (2))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_le_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let lo = FStar_Int_Cast.uint32_to_uint8 x in
                      (let h = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd'
                         (match input with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base) pos lo);
                      (let hi' =
                         FStar_UInt32.shift_right x
                           (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
                       let hi = FStar_Int_Cast.uint32_to_uint16 hi' in
                       let h1 = FStar_HyperStack_ST.get () in
                       LowStar_Endianness.store16_le_i
                         (match input with
                          | { LowParse_Slice.base = base;
                              LowParse_Slice.len = len1;_} -> base)
                         (FStar_UInt32.add pos
                            (FStar_UInt32.uint_to_t Prims.int_one)) hi;
                       (let h2 = FStar_HyperStack_ST.get () in
                        FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_le_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let pos' =
                  let res =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let h = FStar_HyperStack_ST.get () in
                      LowStar_Endianness.store32_le_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) pos x;
                      (let h' = FStar_HyperStack_ST.get () in
                       FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in res in
                let h = FStar_HyperStack_ST.get () in pos'
let (write_bounded_int32_le :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun input ->
        fun rrel ->
          fun rel ->
            fun out ->
              fun pos ->
                if (FStar_UInt32.v max32) < (Prims.of_int (256))
                then write_bounded_int32_le_1 min32 max32 input () () out pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                  then
                    write_bounded_int32_le_2 min32 max32 input () () out pos
                  else
                    if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                    then
                      write_bounded_int32_le_3 min32 max32 input () () out
                        pos
                    else
                      write_bounded_int32_le_4 min32 max32 input () () out
                        pos
let (read_bounded_int32_le' :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      Prims.nat ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun sz ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let uu___ =
                  let h1 = FStar_HyperStack_ST.get () in
                  match sz with
                  | uu___1 when uu___1 = Prims.int_one ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      let r =
                        LowStar_Monotonic_Buffer.index
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base) pos in
                      FStar_Int_Cast.uint8_to_uint32 r
                  | uu___1 when uu___1 = (Prims.of_int (2)) ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      let r =
                        LowStar_Endianness.load16_le_i
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base) pos in
                      FStar_Int_Cast.uint16_to_uint32 r
                  | uu___1 when uu___1 = (Prims.of_int (3)) ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      let lo =
                        LowStar_Monotonic_Buffer.index
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base) pos in
                      let hi =
                        LowStar_Endianness.load16_le_i
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> base)
                          (FStar_UInt32.add pos
                             (FStar_UInt32.uint_to_t Prims.int_one)) in
                      FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                        (FStar_UInt32.shift_left
                           (FStar_Int_Cast.uint16_to_uint32 hi)
                           (FStar_UInt32.uint_to_t (Prims.of_int (8))))
                  | uu___1 when uu___1 = (Prims.of_int (4)) ->
                      let h2 = FStar_HyperStack_ST.get () in
                      let h3 = FStar_HyperStack_ST.get () in
                      LowStar_Endianness.load32_le_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len;_} -> base) pos in
                uu___
let (read_bounded_int32_le_1 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let r =
                  LowStar_Monotonic_Buffer.index
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base) pos in
                FStar_Int_Cast.uint8_to_uint32 r in
              uu___
let (read_bounded_int32_le_2 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let r =
                  LowStar_Endianness.load16_le_i
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base) pos in
                FStar_Int_Cast.uint16_to_uint32 r in
              uu___
let (read_bounded_int32_le_3 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                let lo =
                  LowStar_Monotonic_Buffer.index
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base) pos in
                let hi =
                  LowStar_Endianness.load16_le_i
                    (match input with
                     | { LowParse_Slice.base = base;
                         LowParse_Slice.len = len;_} -> base)
                    (FStar_UInt32.add pos
                       (FStar_UInt32.uint_to_t Prims.int_one)) in
                FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 lo)
                  (FStar_UInt32.shift_left
                     (FStar_Int_Cast.uint16_to_uint32 hi)
                     (FStar_UInt32.uint_to_t (Prims.of_int (8)))) in
              uu___
let (read_bounded_int32_le_4 :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                let h1 = FStar_HyperStack_ST.get () in
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                LowStar_Endianness.load32_le_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base) pos in
              uu___
let (read_bounded_int32_le :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun sl ->
            fun pos ->
              if (FStar_UInt32.v max32) < (Prims.of_int (256))
              then read_bounded_int32_le_1 min32 max32 () () sl pos
              else
                if (FStar_UInt32.v max32) < (Prims.parse_int "65536")
                then read_bounded_int32_le_2 min32 max32 () () sl pos
                else
                  if (FStar_UInt32.v max32) < (Prims.parse_int "16777216")
                  then read_bounded_int32_le_3 min32 max32 () () sl pos
                  else read_bounded_int32_le_4 min32 max32 () () sl pos
let (validate_bounded_int32_le_fixed_size :
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
              let res =
                let h1 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt64.lt
                    (FStar_UInt64.sub
                       (FStar_Int_Cast.uint32_to_uint64
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> len)) pos)
                    (FStar_UInt64.uint_to_t (Prims.of_int (4)))
                then LowParse_Low_ErrorCode.validator_error_not_enough_data
                else
                  FStar_UInt64.add pos
                    (FStar_UInt64.uint_to_t (Prims.of_int (4))) in
              if LowParse_Low_ErrorCode.is_error res
              then res
              else
                (let va =
                   let h1 = FStar_HyperStack_ST.get () in
                   let uu___1 =
                     let h2 = FStar_HyperStack_ST.get () in
                     let h3 = FStar_HyperStack_ST.get () in
                     LowStar_Endianness.load32_le_i
                       (match input with
                        | { LowParse_Slice.base = base;
                            LowParse_Slice.len = len;_} -> base)
                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                   uu___1 in
                 if
                   Prims.op_Negation
                     (Prims.op_Negation
                        ((FStar_UInt32.lt va min32) ||
                           (FStar_UInt32.lt max32 va)))
                 then LowParse_Low_ErrorCode.validator_error_generic
                 else res)
let (jump_bounded_int32_le_fixed_size :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              FStar_UInt32.add pos
                (FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (read_bounded_int32_le_fixed_size :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let h1 = FStar_HyperStack_ST.get () in
              let uu___ =
                let h2 = FStar_HyperStack_ST.get () in
                let h3 = FStar_HyperStack_ST.get () in
                LowStar_Endianness.load32_le_i
                  (match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base) pos in
              uu___
let (write_bounded_int32_le_fixed_size :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min32 ->
    fun max32 ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let res =
                  let pos' =
                    let h0 = FStar_HyperStack_ST.get () in
                    let len =
                      let h = FStar_HyperStack_ST.get () in
                      LowStar_Endianness.store32_le_i
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) pos x;
                      (let h' = FStar_HyperStack_ST.get () in
                       FStar_UInt32.uint_to_t (Prims.of_int (4))) in
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos len in
                  let h = FStar_HyperStack_ST.get () in pos' in
                let h = FStar_HyperStack_ST.get () in res