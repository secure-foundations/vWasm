open Prims
type data =
  {
  x: Wasm_Parse_Memidx.memidx ;
  e: Wasm_Parse_Constexpr.constexpr ;
  b: Wasm_Parse_Aux_vecbyte.aux_vecbyte }
let (__proj__Mkdata__item__x : data -> Wasm_Parse_Memidx.memidx) =
  fun projectee -> match projectee with | { x; e; b;_} -> x
let (__proj__Mkdata__item__e : data -> Wasm_Parse_Constexpr.constexpr) =
  fun projectee -> match projectee with | { x; e; b;_} -> e
let (__proj__Mkdata__item__b : data -> Wasm_Parse_Aux_vecbyte.aux_vecbyte) =
  fun projectee -> match projectee with | { x; e; b;_} -> b
type data' =
  ((Wasm_Parse_Memidx.memidx * Wasm_Parse_Constexpr.constexpr) *
    Wasm_Parse_Aux_vecbyte.aux_vecbyte)
let (synth_data : data' -> data) =
  fun x -> match x with | ((x1, e), b) -> { x = x1; e; b }
let (synth_data_recip : data -> data') = fun x -> (((x.x), (x.e)), (x.b))




let (data'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (data' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Memidx.memidx_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Constexpr.constexpr_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Aux_vecbyte.aux_vecbyte_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (data_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (data * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Memidx.memidx_parser32 input with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match Wasm_Parse_Constexpr.constexpr_parser32 input'
                     with
                     | FStar_Pervasives_Native.Some (v', l') ->
                         FStar_Pervasives_Native.Some
                           ((v, v'), (FStar_UInt32.add l l'))
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Aux_vecbyte.aux_vecbyte_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | ((x, e), b) -> { x; e; b })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (data'_serializer32 : data' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 = Wasm_Parse_Memidx.memidx_serializer32 fs1 in
              let output2 = Wasm_Parse_Constexpr.constexpr_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 = Wasm_Parse_Aux_vecbyte.aux_vecbyte_serializer32 sn in
        FStar_Bytes.append output1 output2
let (data_serializer32 : data -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.x), (input.e)), (input.b)) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 = Wasm_Parse_Memidx.memidx_serializer32 fs1 in
              let output2 = Wasm_Parse_Constexpr.constexpr_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 = Wasm_Parse_Aux_vecbyte.aux_vecbyte_serializer32 sn in
        FStar_Bytes.append output1 output2
let (data'_size32 : data' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 = Wasm_Parse_Memidx.memidx_size32 x11 in
              let v2 = Wasm_Parse_Constexpr.constexpr_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v2) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v2 in
              res in
        let v2 = Wasm_Parse_Aux_vecbyte.aux_vecbyte_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (data_size32 : data -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 = Wasm_Parse_Memidx.memidx_size32 input.x in
      let v2 = Wasm_Parse_Constexpr.constexpr_size32 input.e in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v2 in
      res in
    let v2 = Wasm_Parse_Aux_vecbyte.aux_vecbyte_size32 input.b in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
