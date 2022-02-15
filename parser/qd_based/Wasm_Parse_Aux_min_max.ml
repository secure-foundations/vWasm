open Prims
type aux_min_max = {
  min: FStar_UInt32.t ;
  max: FStar_UInt32.t }
let (__proj__Mkaux_min_max__item__min : aux_min_max -> FStar_UInt32.t) =
  fun projectee -> match projectee with | { min; max;_} -> min
let (__proj__Mkaux_min_max__item__max : aux_min_max -> FStar_UInt32.t) =
  fun projectee -> match projectee with | { min; max;_} -> max
type aux_min_max' = (FStar_UInt32.t * FStar_UInt32.t)
let (synth_aux_min_max : aux_min_max' -> aux_min_max) =
  fun x -> match x with | (min, max) -> { min; max }
let (synth_aux_min_max_recip : aux_min_max -> aux_min_max') =
  fun x -> ((x.min), (x.max))




let (aux_min_max'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_min_max' * FStar_UInt32.t) FStar_Pervasives_Native.option)
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
let (aux_min_max_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_min_max * FStar_UInt32.t) FStar_Pervasives_Native.option)
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
          (((match v1 with | (min, max) -> { min; max })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_min_max'_serializer32 : aux_min_max' -> LowParse_SLow_Base.bytes32)
  =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = LowParse_SLow_Int.serialize32_u32 sn in
        FStar_Bytes.append output1 output2
let (aux_min_max_serializer32 : aux_min_max -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.min), (input.max)) in
    match x with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = LowParse_SLow_Int.serialize32_u32 sn in
        FStar_Bytes.append output1 output2
let (aux_min_max'_size32 : aux_min_max' -> FStar_UInt32.t) =
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
let (aux_min_max_size32 : aux_min_max -> FStar_UInt32.t) =
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
