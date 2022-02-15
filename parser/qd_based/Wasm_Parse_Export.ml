open Prims
type export =
  {
  nm: Wasm_Parse_Name.name ;
  d: Wasm_Parse_Exportdesc.exportdesc }
let (__proj__Mkexport__item__nm : export -> Wasm_Parse_Name.name) =
  fun projectee -> match projectee with | { nm; d;_} -> nm
let (__proj__Mkexport__item__d : export -> Wasm_Parse_Exportdesc.exportdesc)
  = fun projectee -> match projectee with | { nm; d;_} -> d
type export' = (Wasm_Parse_Name.name * Wasm_Parse_Exportdesc.exportdesc)
let (synth_export : export' -> export) =
  fun x -> match x with | (nm, d) -> { nm; d }
let (synth_export_recip : export -> export') = fun x -> ((x.nm), (x.d))




let (export'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (export' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Name.name_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Exportdesc.exportdesc_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (export_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (export * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Name.name_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Exportdesc.exportdesc_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (nm, d) -> { nm; d })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (export'_serializer32 : export' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Name.name_serializer32 fs in
        let output2 = Wasm_Parse_Exportdesc.exportdesc_serializer32 sn in
        FStar_Bytes.append output1 output2
let (export_serializer32 : export -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.nm), (input.d)) in
    match x with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Name.name_serializer32 fs in
        let output2 = Wasm_Parse_Exportdesc.exportdesc_serializer32 sn in
        FStar_Bytes.append output1 output2
let (export'_size32 : export' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Name.name_size32 x1 in
        let v2 = Wasm_Parse_Exportdesc.exportdesc_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (export_size32 : export -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Name.name_size32 input.nm in
    let v2 = Wasm_Parse_Exportdesc.exportdesc_size32 input.d in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
