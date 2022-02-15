open Prims
type uint64 = {
  high: FStar_UInt32.t ;
  low: FStar_UInt32.t }
let (__proj__Mkuint64__item__high : uint64 -> FStar_UInt32.t) =
  fun projectee -> match projectee with | { high; low;_} -> high
let (__proj__Mkuint64__item__low : uint64 -> FStar_UInt32.t) =
  fun projectee -> match projectee with | { high; low;_} -> low
type uint64' = (FStar_UInt32.t * FStar_UInt32.t)
let (synth_uint64 : uint64' -> uint64) =
  fun x -> match x with | (high, low) -> { high; low }
let (synth_uint64_recip : uint64 -> uint64') = fun x -> ((x.high), (x.low))




let (uint64'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (uint64' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match LowParse_SLow_Int.parse32_u32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match LowParse_SLow_Int.parse32_u32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (uint64_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (uint64 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match LowParse_SLow_Int.parse32_u32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (high, low) -> { high; low })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (uint64'_serializer32 : uint64' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = LowParse_SLow_Int.serialize32_u32 sn in
        FStar_Bytes.append output1 output2
let (uint64_serializer32 : uint64 -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.high), (input.low)) in
    match x with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = LowParse_SLow_Int.serialize32_u32 sn in
        FStar_Bytes.append output1 output2
let (uint64'_size32 : uint64' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
        let v2 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (uint64_size32 : uint64 -> FStar_UInt32.t) =
  fun input ->
    let v1 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
    let v2 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
