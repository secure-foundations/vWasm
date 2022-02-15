open Prims
type locals = {
  n: FStar_UInt32.t ;
  t: Wasm_Parse_Valtype.valtype }
let (__proj__Mklocals__item__n : locals -> FStar_UInt32.t) =
  fun projectee -> match projectee with | { n; t;_} -> n
let (__proj__Mklocals__item__t : locals -> Wasm_Parse_Valtype.valtype) =
  fun projectee -> match projectee with | { n; t;_} -> t
type locals' = (FStar_UInt32.t * Wasm_Parse_Valtype.valtype)
let (synth_locals : locals' -> locals) =
  fun x -> match x with | (n, t) -> { n; t }
let (synth_locals_recip : locals -> locals') = fun x -> ((x.n), (x.t))




let (locals'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (locals' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match LowParse_SLow_Int.parse32_u32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Valtype.valtype_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (locals_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (locals * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Valtype.valtype_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (n, t) -> { n; t })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (locals'_serializer32 : locals' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = Wasm_Parse_Valtype.valtype_serializer32 sn in
        FStar_Bytes.append output1 output2
let (locals_serializer32 : locals -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.n), (input.t)) in
    match x with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = Wasm_Parse_Valtype.valtype_serializer32 sn in
        FStar_Bytes.append output1 output2
let (locals'_size32 : locals' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
        let v2 = Wasm_Parse_Valtype.valtype_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (locals_size32 : locals -> FStar_UInt32.t) =
  fun input ->
    let v1 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
    let v2 = Wasm_Parse_Valtype.valtype_size32 input.t in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
