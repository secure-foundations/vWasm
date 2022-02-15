open Prims
type globaltype = {
  t: Wasm_Parse_Valtype.valtype ;
  m: Wasm_Parse_Mut.mut }
let (__proj__Mkglobaltype__item__t :
  globaltype -> Wasm_Parse_Valtype.valtype) =
  fun projectee -> match projectee with | { t; m;_} -> t
let (__proj__Mkglobaltype__item__m : globaltype -> Wasm_Parse_Mut.mut) =
  fun projectee -> match projectee with | { t; m;_} -> m
type globaltype' = (Wasm_Parse_Valtype.valtype * Wasm_Parse_Mut.mut)
let (synth_globaltype : globaltype' -> globaltype) =
  fun x -> match x with | (t, m) -> { t; m }
let (synth_globaltype_recip : globaltype -> globaltype') =
  fun x -> ((x.t), (x.m))




let (globaltype'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (globaltype' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Valtype.valtype_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Mut.mut_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (globaltype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (globaltype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Valtype.valtype_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Mut.mut_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (t, m) -> { t; m })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (globaltype'_serializer32 : globaltype' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Valtype.valtype_serializer32 fs in
        let output2 = Wasm_Parse_Mut.mut_serializer32 sn in
        FStar_Bytes.append output1 output2
let (globaltype_serializer32 : globaltype -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.t), (input.m)) in
    match x with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Valtype.valtype_serializer32 fs in
        let output2 = Wasm_Parse_Mut.mut_serializer32 sn in
        FStar_Bytes.append output1 output2
let (globaltype'_size32 : globaltype' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Valtype.valtype_size32 x1 in
        let v2 = Wasm_Parse_Mut.mut_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (globaltype_size32 : globaltype -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Valtype.valtype_size32 input.t in
    let v2 = Wasm_Parse_Mut.mut_size32 input.m in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
