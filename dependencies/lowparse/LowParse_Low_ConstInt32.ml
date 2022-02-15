open Prims

let (validate_constint32le_slow :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun v ->
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
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else
              (let v' =
                 let h1 = FStar_HyperStack_ST.get () in
                 let h2 = FStar_HyperStack_ST.get () in
                 let r0 =
                   LowStar_Monotonic_Buffer.index
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base)
                     (FStar_Int_Cast.uint64_to_uint32 pos) in
                 let r1 =
                   LowStar_Monotonic_Buffer.index
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base)
                     (FStar_UInt32.add (FStar_Int_Cast.uint64_to_uint32 pos)
                        (FStar_UInt32.uint_to_t Prims.int_one)) in
                 let r2 =
                   LowStar_Monotonic_Buffer.index
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base)
                     (FStar_UInt32.add (FStar_Int_Cast.uint64_to_uint32 pos)
                        (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
                 let r3 =
                   LowStar_Monotonic_Buffer.index
                     (match input with
                      | { LowParse_Slice.base = base;
                          LowParse_Slice.len = len;_} -> base)
                     (FStar_UInt32.add (FStar_Int_Cast.uint64_to_uint32 pos)
                        (FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                 FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 r0)
                   (FStar_UInt32.mul
                      (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                      (FStar_UInt32.add (FStar_Int_Cast.uint8_to_uint32 r1)
                         (FStar_UInt32.mul
                            (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                            (FStar_UInt32.add
                               (FStar_Int_Cast.uint8_to_uint32 r2)
                               (FStar_UInt32.mul
                                  (FStar_UInt32.uint_to_t
                                     (Prims.of_int (256)))
                                  (FStar_Int_Cast.uint8_to_uint32 r3)))))) in
               if FStar_UInt32.eq v v'
               then
                 FStar_UInt64.add pos
                   (FStar_UInt64.uint_to_t (Prims.of_int (4)))
               else LowParse_Low_ErrorCode.validator_error_generic)
let (read_constint32le :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> unit LowParse_Spec_ConstInt32.constint32)
  = fun v -> fun rrel -> fun rel -> fun input -> fun pos -> v
let (decompose_int32le_0 : Prims.nat -> Prims.nat) =
  fun v -> v mod (Prims.of_int (256))
let (decompose_int32le_1 : Prims.nat -> Prims.nat) =
  fun v -> (v / (Prims.of_int (256))) mod (Prims.of_int (256))
let (decompose_int32le_2 : Prims.nat -> Prims.nat) =
  fun v -> (v / (Prims.parse_int "65536")) mod (Prims.of_int (256))
let (decompose_int32le_3 : Prims.nat -> Prims.nat) =
  fun v -> v / (Prims.parse_int "16777216")
let (compose_int32le :
  Prims.nat -> Prims.nat -> Prims.nat -> Prims.nat -> Prims.nat) =
  fun b0 ->
    fun b1 ->
      fun b2 ->
        fun b3 ->
          b0 +
            ((Prims.of_int (256)) *
               (b1 +
                  ((Prims.of_int (256)) * (b2 + ((Prims.of_int (256)) * b3)))))

let (compare_by_bytes :
  FStar_UInt8.t ->
    FStar_UInt8.t ->
      FStar_UInt8.t ->
        FStar_UInt8.t ->
          FStar_UInt8.t ->
            FStar_UInt8.t -> FStar_UInt8.t -> FStar_UInt8.t -> Prims.bool)
  =
  fun a0 ->
    fun a1 ->
      fun a2 ->
        fun a3 ->
          fun b0 ->
            fun b1 ->
              fun b2 ->
                fun b3 ->
                  (((a0 = b0) && (a1 = b1)) && (a2 = b2)) && (a3 = b3)
let (compare_by_bytes' :
  FStar_UInt8.t ->
    FStar_UInt8.t ->
      FStar_UInt8.t ->
        FStar_UInt8.t ->
          FStar_UInt8.t ->
            FStar_UInt8.t -> FStar_UInt8.t -> FStar_UInt8.t -> Prims.bool)
  =
  fun a0 ->
    fun a1 ->
      fun a2 ->
        fun a3 ->
          fun b0 ->
            fun b1 ->
              fun b2 ->
                fun b3 ->
                  (compose_int32le (FStar_UInt8.v a0) (FStar_UInt8.v a1)
                     (FStar_UInt8.v a2) (FStar_UInt8.v a3))
                    =
                    (compose_int32le (FStar_UInt8.v b0) (FStar_UInt8.v b1)
                       (FStar_UInt8.v b2) (FStar_UInt8.v b3))


let (inplace_compare :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Prims.bool)
  =
  fun v ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            let b =
              match input with
              | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} ->
                  base in
            let r0 = LowStar_Monotonic_Buffer.index b pos in
            let r1 =
              LowStar_Monotonic_Buffer.index b
                (FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one)) in
            let r2 =
              LowStar_Monotonic_Buffer.index b
                (FStar_UInt32.add pos
                   (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
            let r3 =
              LowStar_Monotonic_Buffer.index b
                (FStar_UInt32.add pos
                   (FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
            (((r0 =
                 (FStar_UInt8.uint_to_t
                    ((FStar_UInt32.v v) mod (Prims.of_int (256)))))
                &&
                (r1 =
                   (FStar_UInt8.uint_to_t
                      (((FStar_UInt32.v v) / (Prims.of_int (256))) mod
                         (Prims.of_int (256))))))
               &&
               (r2 =
                  (FStar_UInt8.uint_to_t
                     (((FStar_UInt32.v v) / (Prims.parse_int "65536")) mod
                        (Prims.of_int (256))))))
              &&
              (r3 =
                 (FStar_UInt8.uint_to_t
                    ((FStar_UInt32.v v) / (Prims.parse_int "16777216"))))
let (validate_constint32le :
  FStar_UInt32.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun v ->
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
            then LowParse_Low_ErrorCode.validator_error_not_enough_data
            else
              (let uu___1 =
                 let h1 = FStar_HyperStack_ST.get () in
                 let b =
                   match input with
                   | { LowParse_Slice.base = base;
                       LowParse_Slice.len = len;_} -> base in
                 let r0 =
                   LowStar_Monotonic_Buffer.index b
                     (FStar_Int_Cast.uint64_to_uint32 pos) in
                 let r1 =
                   LowStar_Monotonic_Buffer.index b
                     (FStar_UInt32.add (FStar_Int_Cast.uint64_to_uint32 pos)
                        (FStar_UInt32.uint_to_t Prims.int_one)) in
                 let r2 =
                   LowStar_Monotonic_Buffer.index b
                     (FStar_UInt32.add (FStar_Int_Cast.uint64_to_uint32 pos)
                        (FStar_UInt32.uint_to_t (Prims.of_int (2)))) in
                 let r3 =
                   LowStar_Monotonic_Buffer.index b
                     (FStar_UInt32.add (FStar_Int_Cast.uint64_to_uint32 pos)
                        (FStar_UInt32.uint_to_t (Prims.of_int (3)))) in
                 (((r0 =
                      (FStar_UInt8.uint_to_t
                         ((FStar_UInt32.v v) mod (Prims.of_int (256)))))
                     &&
                     (r1 =
                        (FStar_UInt8.uint_to_t
                           (((FStar_UInt32.v v) / (Prims.of_int (256))) mod
                              (Prims.of_int (256))))))
                    &&
                    (r2 =
                       (FStar_UInt8.uint_to_t
                          (((FStar_UInt32.v v) / (Prims.parse_int "65536"))
                             mod (Prims.of_int (256))))))
                   &&
                   (r3 =
                      (FStar_UInt8.uint_to_t
                         ((FStar_UInt32.v v) / (Prims.parse_int "16777216")))) in
               if uu___1
               then
                 FStar_UInt64.add pos
                   (FStar_UInt64.uint_to_t (Prims.of_int (4)))
               else LowParse_Low_ErrorCode.validator_error_generic)