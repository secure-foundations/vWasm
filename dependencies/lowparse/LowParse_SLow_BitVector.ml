open Prims
let (parse32_bv8 :
  LowParse_SLow_Base.bytes32 ->
    (unit FStar_BitVector.bv_t * FStar_UInt32.t)
      FStar_Pervasives_Native.option)
  =
  fun input ->
    match LowParse_SLow_Int.parse32_u8 input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          ((LowParse_Spec_BitVector.synth_bv8 v1), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_bv8 :
  unit FStar_BitVector.bv_t -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = LowParse_Spec_BitVector.synth_bv8_recip input in
    LowParse_SLow_Int.serialize32_u8 x
let (size32_bv8 : unit FStar_BitVector.bv_t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one
let rec (parse32_byte_bv :
  Prims.nat ->
    LowParse_SLow_Base.bytes32 ->
      (unit FStar_BitVector.bv_t * FStar_UInt32.t)
        FStar_Pervasives_Native.option)
  =
  fun n ->
    if n = Prims.int_zero
    then
      fun input ->
        FStar_Pervasives_Native.Some
          ((FStar_Seq_Base.empty ()),
            (FStar_UInt32.uint_to_t Prims.int_zero))
    else
      (fun input ->
         match match parse32_bv8 input with
               | FStar_Pervasives_Native.Some (v, l) ->
                   let input' =
                     FStar_Bytes.slice input l (FStar_Bytes.len input) in
                   (match parse32_byte_bv (n - Prims.int_one) input' with
                    | FStar_Pervasives_Native.Some (v', l') ->
                        FStar_Pervasives_Native.Some
                          ((v, v'), (FStar_UInt32.add l l'))
                    | uu___1 -> FStar_Pervasives_Native.None)
               | uu___1 -> FStar_Pervasives_Native.None
         with
         | FStar_Pervasives_Native.Some (v1, consumed) ->
             FStar_Pervasives_Native.Some
               ((LowParse_Spec_BitVector.synth_byte_bv (n - Prims.int_one) v1),
                 consumed)
         | uu___1 -> FStar_Pervasives_Native.None)
let rec (serialize32_byte_bv :
  Prims.nat -> unit FStar_BitVector.bv_t -> LowParse_SLow_Base.bytes32) =
  fun n ->
    if n = Prims.int_zero
    then fun input -> FStar_Bytes.empty_bytes
    else
      (fun input ->
         let x =
           LowParse_Spec_BitVector.synth_byte_bv_recip (n - Prims.int_one)
             input in
         match x with
         | (fs, sn) ->
             let output1 = serialize32_bv8 fs in
             let output2 = serialize32_byte_bv (n - Prims.int_one) sn in
             FStar_Bytes.append output1 output2)
let (size32_byte_bv :
  Prims.nat -> unit FStar_BitVector.bv_t -> FStar_UInt32.t) =
  fun n -> fun x -> FStar_UInt32.uint_to_t n
let (parse32_extra_bv8 :
  Prims.nat ->
    LowParse_SLow_Base.bytes32 ->
      (unit FStar_BitVector.bv_t * FStar_UInt32.t)
        FStar_Pervasives_Native.option)
  =
  fun n ->
    fun input ->
      match match LowParse_SLow_Int.parse32_u8 input with
            | FStar_Pervasives_Native.Some (v, consumed) ->
                if LowParse_Spec_BitVector.extra_bytes_prop n v
                then FStar_Pervasives_Native.Some (v, consumed)
                else FStar_Pervasives_Native.None
            | uu___ -> FStar_Pervasives_Native.None
      with
      | FStar_Pervasives_Native.Some (v1, consumed) ->
          FStar_Pervasives_Native.Some
            ((LowParse_Spec_BitVector.synth_extra_bv8 n v1), consumed)
      | uu___ -> FStar_Pervasives_Native.None
let (serialize32_extra_bv8 :
  Prims.nat -> unit FStar_BitVector.bv_t -> LowParse_SLow_Base.bytes32) =
  fun n ->
    fun input ->
      let x = LowParse_Spec_BitVector.synth_extra_bv8_recip n input in
      LowParse_SLow_Int.serialize32_u8 x
let (size32_extra_bv8 :
  Prims.nat -> unit FStar_BitVector.bv_t -> FStar_UInt32.t) =
  fun n -> fun x -> FStar_UInt32.uint_to_t Prims.int_one
let (parse32_bv :
  Prims.nat ->
    LowParse_SLow_Base.bytes32 ->
      (unit FStar_BitVector.bv_t * FStar_UInt32.t)
        FStar_Pervasives_Native.option)
  =
  fun n ->
    if (n mod (Prims.of_int (8))) = Prims.int_zero
    then parse32_byte_bv (n / (Prims.of_int (8)))
    else
      (fun input ->
         match match parse32_extra_bv8 n input with
               | FStar_Pervasives_Native.Some (v, l) ->
                   let input' =
                     FStar_Bytes.slice input l (FStar_Bytes.len input) in
                   (match parse32_byte_bv (n / (Prims.of_int (8))) input'
                    with
                    | FStar_Pervasives_Native.Some (v', l') ->
                        FStar_Pervasives_Native.Some
                          ((v, v'), (FStar_UInt32.add l l'))
                    | uu___1 -> FStar_Pervasives_Native.None)
               | uu___1 -> FStar_Pervasives_Native.None
         with
         | FStar_Pervasives_Native.Some (v1, consumed) ->
             FStar_Pervasives_Native.Some
               ((LowParse_Spec_BitVector.synth_bv n v1), consumed)
         | uu___1 -> FStar_Pervasives_Native.None)
let (serialize32_bv :
  Prims.nat -> unit FStar_BitVector.bv_t -> LowParse_SLow_Base.bytes32) =
  fun n ->
    if (n mod (Prims.of_int (8))) = Prims.int_zero
    then serialize32_byte_bv (n / (Prims.of_int (8)))
    else
      (fun input ->
         let x = LowParse_Spec_BitVector.synth_bv_recip n input in
         match x with
         | (fs, sn) ->
             let output1 = serialize32_extra_bv8 n fs in
             let output2 = serialize32_byte_bv (n / (Prims.of_int (8))) sn in
             FStar_Bytes.append output1 output2)
let (size32_bv : Prims.nat -> unit FStar_BitVector.bv_t -> FStar_UInt32.t) =
  fun n ->
    fun x ->
      if (n mod (Prims.of_int (8))) = Prims.int_zero
      then FStar_UInt32.uint_to_t (n / (Prims.of_int (8)))
      else FStar_UInt32.uint_to_t (Prims.int_one + (n / (Prims.of_int (8))))
let (parse32_bounded_bv :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            LowParse_SLow_Base.bytes32 ->
              ((FStar_UInt32.t, unit FStar_BitVector.bv_t) Prims.dtuple2 *
                FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun hk ->
        fun hp ->
          fun hp32 ->
            fun input ->
              match hp32 input with
              | FStar_Pervasives_Native.Some (v, l) ->
                  let input' =
                    FStar_Bytes.slice input l (FStar_Bytes.len input) in
                  (match parse32_bv (FStar_UInt32.v v) input' with
                   | FStar_Pervasives_Native.Some (v', l') ->
                       FStar_Pervasives_Native.Some
                         ((Prims.Mkdtuple2 (v, v')), (FStar_UInt32.add l l'))
                   | uu___ -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None
let (serialize32_bounded_bv :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> LowParse_SLow_Base.bytes32) ->
              (FStar_UInt32.t, unit FStar_BitVector.bv_t) Prims.dtuple2 ->
                LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun hk ->
        fun hp ->
          fun hs ->
            fun hs32 ->
              fun input ->
                match input with
                | Prims.Mkdtuple2 (fs, sn) ->
                    let output1 = hs32 fs in
                    let output2 = serialize32_bv (FStar_UInt32.v fs) sn in
                    FStar_Bytes.append output1 output2
let (size32_bounded_bv :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> FStar_UInt32.t) ->
              (FStar_UInt32.t, unit FStar_BitVector.bv_t) Prims.dtuple2 ->
                FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun hk ->
        fun hp ->
          fun hs ->
            fun hs32 ->
              fun x ->
                match x with
                | Prims.Mkdtuple2 (x1, x2) ->
                    let v1 = hs32 x1 in
                    let v2 = size32_bv (FStar_UInt32.v x1) x2 in
                    let res =
                      if
                        FStar_UInt32.lt
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")) v2) v1
                      then
                        FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                      else FStar_UInt32.add v1 v2 in
                    res