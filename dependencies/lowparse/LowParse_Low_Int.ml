open Prims
let (read_u8 :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt8.t)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          LowStar_Monotonic_Buffer.index
            (match sl with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                 base) pos
let (read_u16 :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt16.t)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          LowStar_Endianness.load16_be_i
            (match sl with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                 base) pos
let (read_u32 :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          LowStar_Endianness.load32_be_i
            (match sl with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                 base) pos
let (read_u64 :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt64.t)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          LowStar_Endianness.load64_be_i
            (match sl with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                 base) pos
let (read_u64_le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt64.t)
  =
  fun rrel ->
    fun rel ->
      fun sl ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          LowStar_Endianness.load64_le_i
            (match sl with
             | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                 base) pos
let (validate_u8 :
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
                (FStar_UInt64.uint_to_t Prims.int_one)
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else FStar_UInt64.add pos (FStar_UInt64.uint_to_t Prims.int_one)
let (validate_u8_with_error_code :
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
                (FStar_UInt64.uint_to_t Prims.int_one)
            then
              LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                LowParse_Low_ErrorCode.validator_error_not_enough_data pos c
            else FStar_UInt64.add pos (FStar_UInt64.uint_to_t Prims.int_one)
let (validate_u16 :
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
let (validate_u32 :
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
let (validate_u64 :
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
                (FStar_UInt64.uint_to_t (Prims.of_int (8)))
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (8)))
let (validate_u64_le :
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
                (FStar_UInt64.uint_to_t (Prims.of_int (8)))
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (8)))
let (validate_u64_le_with_error_code :
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
                (FStar_UInt64.uint_to_t (Prims.of_int (8)))
            then
              LowParse_Low_ErrorCode.set_validator_error_pos_and_code
                LowParse_Low_ErrorCode.validator_error_not_enough_data pos c
            else
              FStar_UInt64.add pos
                (FStar_UInt64.uint_to_t (Prims.of_int (8)))
let (jump_u8 :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one)
let (jump_u16 :
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
let (jump_u32 :
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
let (jump_u64 :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t (Prims.of_int (8)))
let (jump_u64_le :
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun rrel ->
    fun rel ->
      fun input ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          FStar_UInt32.add pos (FStar_UInt32.uint_to_t (Prims.of_int (8)))
let (serialize32_u8 :
  FStar_UInt8.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            (let h = FStar_HyperStack_ST.get () in
             LowStar_Monotonic_Buffer.upd' b pos v);
            FStar_UInt32.uint_to_t Prims.int_one
let (serialize32_u16 :
  FStar_UInt16.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            LowStar_Endianness.store16_be_i b pos v;
            (let h' = FStar_HyperStack_ST.get () in
             FStar_UInt32.uint_to_t (Prims.of_int (2)))
let (serialize32_u32 :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            LowStar_Endianness.store32_be_i b pos v;
            (let h' = FStar_HyperStack_ST.get () in
             FStar_UInt32.uint_to_t (Prims.of_int (4)))
let (serialize32_u64 :
  FStar_UInt64.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            LowStar_Endianness.store64_be_i b pos v;
            (let h' = FStar_HyperStack_ST.get () in
             FStar_UInt32.uint_to_t (Prims.of_int (8)))
let (serialize32_u64_le :
  FStar_UInt64.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun b ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            LowStar_Endianness.store64_le_i b pos v;
            (let h' = FStar_HyperStack_ST.get () in
             FStar_UInt32.uint_to_t (Prims.of_int (8)))
let (write_u8 :
  FStar_UInt8.t ->
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
                      LowParse_Slice.len = len1;_} -> base) pos x);
              FStar_UInt32.uint_to_t Prims.int_one in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_u8_weak :
  FStar_UInt8.t ->
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
                         LowParse_Slice.len = len1;_} -> base) pos x);
                 FStar_UInt32.uint_to_t Prims.int_one in
               let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos len)
let (write_u16 :
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
            let h0 = FStar_HyperStack_ST.get () in
            let len =
              let h = FStar_HyperStack_ST.get () in
              LowStar_Endianness.store16_be_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                     -> base) pos x;
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (2))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_u16_weak :
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
                 LowStar_Endianness.store16_be_i
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len1;_} -> base) pos x;
                 (let h' = FStar_HyperStack_ST.get () in
                  FStar_UInt32.uint_to_t (Prims.of_int (2))) in
               let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos len)
let (write_u32 :
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
              LowStar_Endianness.store32_be_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                     -> base) pos x;
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (4))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_u32_weak :
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
let (write_u64 :
  FStar_UInt64.t ->
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
              LowStar_Endianness.store64_be_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                     -> base) pos x;
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (8))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_u64_weak :
  FStar_UInt64.t ->
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
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len;_} -> len) pos)
                (FStar_UInt32.uint_to_t (Prims.of_int (8)))
            then LowParse_Low_ErrorCode.max_uint32
            else
              (let h = FStar_HyperStack_ST.get () in
               let h0 = FStar_HyperStack_ST.get () in
               let len =
                 let h1 = FStar_HyperStack_ST.get () in
                 LowStar_Endianness.store64_be_i
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len1;_} -> base) pos x;
                 (let h' = FStar_HyperStack_ST.get () in
                  FStar_UInt32.uint_to_t (Prims.of_int (8))) in
               let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos len)
let (write_u64_le :
  FStar_UInt64.t ->
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
              LowStar_Endianness.store64_le_i
                (match input with
                 | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_}
                     -> base) pos x;
              (let h' = FStar_HyperStack_ST.get () in
               FStar_UInt32.uint_to_t (Prims.of_int (8))) in
            let h = FStar_HyperStack_ST.get () in FStar_UInt32.add pos len
let (write_u64_le_weak :
  FStar_UInt64.t ->
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
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len;_} -> len) pos)
                (FStar_UInt32.uint_to_t (Prims.of_int (8)))
            then LowParse_Low_ErrorCode.max_uint32
            else
              (let h = FStar_HyperStack_ST.get () in
               let h0 = FStar_HyperStack_ST.get () in
               let len =
                 let h1 = FStar_HyperStack_ST.get () in
                 LowStar_Endianness.store64_le_i
                   (match input with
                    | { LowParse_Slice.base = base;
                        LowParse_Slice.len = len1;_} -> base) pos x;
                 (let h' = FStar_HyperStack_ST.get () in
                  FStar_UInt32.uint_to_t (Prims.of_int (8))) in
               let h1 = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos len)