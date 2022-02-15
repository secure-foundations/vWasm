open Prims
type version =
  {
  v0: Wasm_Parse_Aux_version_1.aux_version_1 ;
  v1: Wasm_Parse_Aux_version_0.aux_version_0 ;
  v2: Wasm_Parse_Aux_version_0.aux_version_0 ;
  v3: Wasm_Parse_Aux_version_0.aux_version_0 }
let (__proj__Mkversion__item__v0 :
  version -> Wasm_Parse_Aux_version_1.aux_version_1) =
  fun projectee -> match projectee with | { v0; v1; v2; v3;_} -> v0
let (__proj__Mkversion__item__v1 :
  version -> Wasm_Parse_Aux_version_0.aux_version_0) =
  fun projectee -> match projectee with | { v0; v1; v2; v3;_} -> v1
let (__proj__Mkversion__item__v2 :
  version -> Wasm_Parse_Aux_version_0.aux_version_0) =
  fun projectee -> match projectee with | { v0; v1; v2; v3;_} -> v2
let (__proj__Mkversion__item__v3 :
  version -> Wasm_Parse_Aux_version_0.aux_version_0) =
  fun projectee -> match projectee with | { v0; v1; v2; v3;_} -> v3
type version' =
  ((Wasm_Parse_Aux_version_1.aux_version_1 *
    Wasm_Parse_Aux_version_0.aux_version_0) *
    (Wasm_Parse_Aux_version_0.aux_version_0 *
    Wasm_Parse_Aux_version_0.aux_version_0))
let (synth_version : version' -> version) =
  fun x -> match x with | ((v0, v1), (v2, v3)) -> { v0; v1; v2; v3 }
let (synth_version_recip : version -> version') =
  fun x -> (((x.v0), (x.v1)), ((x.v2), (x.v3)))




let (version'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (version' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_version_1.aux_version_1_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Aux_version_0.aux_version_0_parser32 input'
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match match Wasm_Parse_Aux_version_0.aux_version_0_parser32 input'
               with
               | FStar_Pervasives_Native.Some (v1, l1) ->
                   let input'1 =
                     FStar_Bytes.slice input' l1 (FStar_Bytes.len input') in
                   (match Wasm_Parse_Aux_version_0.aux_version_0_parser32
                            input'1
                    with
                    | FStar_Pervasives_Native.Some (v', l') ->
                        FStar_Pervasives_Native.Some
                          ((v1, v'), (FStar_UInt32.add l1 l'))
                    | uu___ -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None
         with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (version_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (version * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Aux_version_1.aux_version_1_parser32 input
                with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match Wasm_Parse_Aux_version_0.aux_version_0_parser32
                             input'
                     with
                     | FStar_Pervasives_Native.Some (v', l') ->
                         FStar_Pervasives_Native.Some
                           ((v, v'), (FStar_UInt32.add l l'))
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match match Wasm_Parse_Aux_version_0.aux_version_0_parser32
                             input'
                     with
                     | FStar_Pervasives_Native.Some (v1, l1) ->
                         let input'1 =
                           FStar_Bytes.slice input' l1
                             (FStar_Bytes.len input') in
                         (match Wasm_Parse_Aux_version_0.aux_version_0_parser32
                                  input'1
                          with
                          | FStar_Pervasives_Native.Some (v', l') ->
                              FStar_Pervasives_Native.Some
                                ((v1, v'), (FStar_UInt32.add l1 l'))
                          | uu___ -> FStar_Pervasives_Native.None)
                     | uu___ -> FStar_Pervasives_Native.None
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with
             | ((v0, v11), (v2, v3)) -> { v0; v1 = v11; v2; v3 })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (version'_serializer32 : version' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_version_1.aux_version_1_serializer32 fs1 in
              let output2 =
                Wasm_Parse_Aux_version_0.aux_version_0_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          match sn with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_version_0.aux_version_0_serializer32 fs1 in
              let output21 =
                Wasm_Parse_Aux_version_0.aux_version_0_serializer32 sn1 in
              FStar_Bytes.append output11 output21 in
        FStar_Bytes.append output1 output2
let (version_serializer32 : version -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.v0), (input.v1)), ((input.v2), (input.v3))) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_version_1.aux_version_1_serializer32 fs1 in
              let output2 =
                Wasm_Parse_Aux_version_0.aux_version_0_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          match sn with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_version_0.aux_version_0_serializer32 fs1 in
              let output21 =
                Wasm_Parse_Aux_version_0.aux_version_0_serializer32 sn1 in
              FStar_Bytes.append output11 output21 in
        FStar_Bytes.append output1 output2
let (version'_size32 : version' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 = Wasm_Parse_Aux_version_1.aux_version_1_size32 x11 in
              let v2 = Wasm_Parse_Aux_version_0.aux_version_0_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v2) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v2 in
              res in
        let v2 =
          match x2 with
          | (x11, x21) ->
              let v11 = Wasm_Parse_Aux_version_0.aux_version_0_size32 x11 in
              let v21 = Wasm_Parse_Aux_version_0.aux_version_0_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v21) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v21 in
              res in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (version_size32 : version -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 = Wasm_Parse_Aux_version_1.aux_version_1_size32 input.v0 in
      let v2 = Wasm_Parse_Aux_version_0.aux_version_0_size32 input.v1 in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v2 in
      res in
    let v2 =
      let v11 = Wasm_Parse_Aux_version_0.aux_version_0_size32 input.v2 in
      let v21 = Wasm_Parse_Aux_version_0.aux_version_0_size32 input.v3 in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v21)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v21 in
      res in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
