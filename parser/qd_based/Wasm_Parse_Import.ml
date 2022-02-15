open Prims
type import =
  {
  modu: Wasm_Parse_Name.name ;
  nm: Wasm_Parse_Name.name ;
  d: Wasm_Parse_Importdesc.importdesc }
let (__proj__Mkimport__item__modu : import -> Wasm_Parse_Name.name) =
  fun projectee -> match projectee with | { modu; nm; d;_} -> modu
let (__proj__Mkimport__item__nm : import -> Wasm_Parse_Name.name) =
  fun projectee -> match projectee with | { modu; nm; d;_} -> nm
let (__proj__Mkimport__item__d : import -> Wasm_Parse_Importdesc.importdesc)
  = fun projectee -> match projectee with | { modu; nm; d;_} -> d
type import' =
  ((Wasm_Parse_Name.name * Wasm_Parse_Name.name) *
    Wasm_Parse_Importdesc.importdesc)
let (synth_import : import' -> import) =
  fun x -> match x with | ((modu, nm), d) -> { modu; nm; d }
let (synth_import_recip : import -> import') =
  fun x -> (((x.modu), (x.nm)), (x.d))




let (import'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (import' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Name.name_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Name.name_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Importdesc.importdesc_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (import_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (import * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Name.name_parser32 input with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match Wasm_Parse_Name.name_parser32 input' with
                     | FStar_Pervasives_Native.Some (v', l') ->
                         FStar_Pervasives_Native.Some
                           ((v, v'), (FStar_UInt32.add l l'))
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Importdesc.importdesc_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | ((modu, nm), d) -> { modu; nm; d })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (import'_serializer32 : import' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 = Wasm_Parse_Name.name_serializer32 fs1 in
              let output2 = Wasm_Parse_Name.name_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 = Wasm_Parse_Importdesc.importdesc_serializer32 sn in
        FStar_Bytes.append output1 output2
let (import_serializer32 : import -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.modu), (input.nm)), (input.d)) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 = Wasm_Parse_Name.name_serializer32 fs1 in
              let output2 = Wasm_Parse_Name.name_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 = Wasm_Parse_Importdesc.importdesc_serializer32 sn in
        FStar_Bytes.append output1 output2
let (import'_size32 : import' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 = Wasm_Parse_Name.name_size32 x11 in
              let v2 = Wasm_Parse_Name.name_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v2) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v2 in
              res in
        let v2 = Wasm_Parse_Importdesc.importdesc_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (import_size32 : import -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 = Wasm_Parse_Name.name_size32 input.modu in
      let v2 = Wasm_Parse_Name.name_size32 input.nm in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v2 in
      res in
    let v2 = Wasm_Parse_Importdesc.importdesc_size32 input.d in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
