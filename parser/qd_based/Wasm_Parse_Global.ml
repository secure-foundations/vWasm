open Prims
type global =
  {
  gt: Wasm_Parse_Globaltype.globaltype ;
  e: Wasm_Parse_Constexpr.constexpr }
let (__proj__Mkglobal__item__gt : global -> Wasm_Parse_Globaltype.globaltype)
  = fun projectee -> match projectee with | { gt; e;_} -> gt
let (__proj__Mkglobal__item__e : global -> Wasm_Parse_Constexpr.constexpr) =
  fun projectee -> match projectee with | { gt; e;_} -> e
type global' =
  (Wasm_Parse_Globaltype.globaltype * Wasm_Parse_Constexpr.constexpr)
let (synth_global : global' -> global) =
  fun x -> match x with | (gt, e) -> { gt; e }
let (synth_global_recip : global -> global') = fun x -> ((x.gt), (x.e))




let (global'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (global' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Globaltype.globaltype_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Constexpr.constexpr_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (global_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (global * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Globaltype.globaltype_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Constexpr.constexpr_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (gt, e) -> { gt; e })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (global'_serializer32 : global' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Globaltype.globaltype_serializer32 fs in
        let output2 = Wasm_Parse_Constexpr.constexpr_serializer32 sn in
        FStar_Bytes.append output1 output2
let (global_serializer32 : global -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.gt), (input.e)) in
    match x with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Globaltype.globaltype_serializer32 fs in
        let output2 = Wasm_Parse_Constexpr.constexpr_serializer32 sn in
        FStar_Bytes.append output1 output2
let (global'_size32 : global' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Globaltype.globaltype_size32 x1 in
        let v2 = Wasm_Parse_Constexpr.constexpr_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (global_size32 : global -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Globaltype.globaltype_size32 input.gt in
    let v2 = Wasm_Parse_Constexpr.constexpr_size32 input.e in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
