open Prims
type tabletype =
  {
  et: Wasm_Parse_Elemtype.elemtype ;
  lim: Wasm_Parse_Limits.limits }
let (__proj__Mktabletype__item__et :
  tabletype -> Wasm_Parse_Elemtype.elemtype) =
  fun projectee -> match projectee with | { et; lim;_} -> et
let (__proj__Mktabletype__item__lim : tabletype -> Wasm_Parse_Limits.limits)
  = fun projectee -> match projectee with | { et; lim;_} -> lim
type tabletype' = (Wasm_Parse_Elemtype.elemtype * Wasm_Parse_Limits.limits)
let (synth_tabletype : tabletype' -> tabletype) =
  fun x -> match x with | (et, lim) -> { et; lim }
let (synth_tabletype_recip : tabletype -> tabletype') =
  fun x -> ((x.et), (x.lim))




let (tabletype'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (tabletype' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Elemtype.elemtype_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Limits.limits_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (tabletype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (tabletype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Elemtype.elemtype_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Limits.limits_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (et, lim) -> { et; lim })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (tabletype'_serializer32 : tabletype' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Elemtype.elemtype_serializer32 fs in
        let output2 = Wasm_Parse_Limits.limits_serializer32 sn in
        FStar_Bytes.append output1 output2
let (tabletype_serializer32 : tabletype -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.et), (input.lim)) in
    match x with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Elemtype.elemtype_serializer32 fs in
        let output2 = Wasm_Parse_Limits.limits_serializer32 sn in
        FStar_Bytes.append output1 output2
let (tabletype'_size32 : tabletype' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Elemtype.elemtype_size32 x1 in
        let v2 = Wasm_Parse_Limits.limits_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (tabletype_size32 : tabletype -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Elemtype.elemtype_size32 input.et in
    let v2 = Wasm_Parse_Limits.limits_size32 input.lim in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
