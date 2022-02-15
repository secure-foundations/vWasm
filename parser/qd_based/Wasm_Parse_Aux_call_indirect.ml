open Prims
type aux_call_indirect =
  {
  x: Wasm_Parse_Typeidx.typeidx ;
  z: Wasm_Parse_Aux_constbyte0.aux_constbyte0 }
let (__proj__Mkaux_call_indirect__item__x :
  aux_call_indirect -> Wasm_Parse_Typeidx.typeidx) =
  fun projectee -> match projectee with | { x; z;_} -> x
let (__proj__Mkaux_call_indirect__item__z :
  aux_call_indirect -> Wasm_Parse_Aux_constbyte0.aux_constbyte0) =
  fun projectee -> match projectee with | { x; z;_} -> z
type aux_call_indirect' =
  (Wasm_Parse_Typeidx.typeidx * Wasm_Parse_Aux_constbyte0.aux_constbyte0)
let (synth_aux_call_indirect : aux_call_indirect' -> aux_call_indirect) =
  fun x -> match x with | (x1, z) -> { x = x1; z }
let (synth_aux_call_indirect_recip : aux_call_indirect -> aux_call_indirect')
  = fun x -> ((x.x), (x.z))




let (aux_call_indirect'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_call_indirect' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Typeidx.typeidx_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Aux_constbyte0.aux_constbyte0_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_call_indirect_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_call_indirect * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Typeidx.typeidx_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Aux_constbyte0.aux_constbyte0_parser32 input'
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (x, z) -> { x; z })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_call_indirect'_serializer32 :
  aux_call_indirect' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Typeidx.typeidx_serializer32 fs in
        let output2 =
          Wasm_Parse_Aux_constbyte0.aux_constbyte0_serializer32 sn in
        FStar_Bytes.append output1 output2
let (aux_call_indirect_serializer32 :
  aux_call_indirect -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.x), (input.z)) in
    match x with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Typeidx.typeidx_serializer32 fs in
        let output2 =
          Wasm_Parse_Aux_constbyte0.aux_constbyte0_serializer32 sn in
        FStar_Bytes.append output1 output2
let (aux_call_indirect'_size32 : aux_call_indirect' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Typeidx.typeidx_size32 x1 in
        let v2 = Wasm_Parse_Aux_constbyte0.aux_constbyte0_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (aux_call_indirect_size32 : aux_call_indirect -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Typeidx.typeidx_size32 input.x in
    let v2 = Wasm_Parse_Aux_constbyte0.aux_constbyte0_size32 input.z in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
