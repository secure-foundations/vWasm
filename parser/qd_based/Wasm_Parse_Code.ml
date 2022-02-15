open Prims
type code = {
  size: FStar_UInt32.t ;
  code_: Wasm_Parse_Func.func }
let (__proj__Mkcode__item__size : code -> FStar_UInt32.t) =
  fun projectee -> match projectee with | { size; code_;_} -> size
let (__proj__Mkcode__item__code_ : code -> Wasm_Parse_Func.func) =
  fun projectee -> match projectee with | { size; code_;_} -> code_
type code' = (FStar_UInt32.t * Wasm_Parse_Func.func)
let (synth_code : code' -> code) =
  fun x -> match x with | (size, code_) -> { size; code_ }
let (synth_code_recip : code -> code') = fun x -> ((x.size), (x.code_))




let (code'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (code' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match LowParse_SLow_Int.parse32_u32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Func.func_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (code_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (code * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Func.func_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (size, code_) -> { size; code_ })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (code'_serializer32 : code' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = Wasm_Parse_Func.func_serializer32 sn in
        FStar_Bytes.append output1 output2
let (code_serializer32 : code -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.size), (input.code_)) in
    match x with
    | (fs, sn) ->
        let output1 = LowParse_SLow_Int.serialize32_u32 fs in
        let output2 = Wasm_Parse_Func.func_serializer32 sn in
        FStar_Bytes.append output1 output2
let (code'_size32 : code' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
        let v2 = Wasm_Parse_Func.func_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (code_size32 : code -> FStar_UInt32.t) =
  fun input ->
    let v1 = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
    let v2 = Wasm_Parse_Func.func_size32 input.code_ in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
