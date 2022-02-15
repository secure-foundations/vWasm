open Prims
type magic_ =
  {
  m0: Wasm_Parse_Aux_magic_0.aux_magic_0 ;
  m1: Wasm_Parse_Aux_magic_1.aux_magic_1 ;
  m2: Wasm_Parse_Aux_magic_2.aux_magic_2 ;
  m3: Wasm_Parse_Aux_magic_3.aux_magic_3 }
let (__proj__Mkmagic___item__m0 :
  magic_ -> Wasm_Parse_Aux_magic_0.aux_magic_0) =
  fun projectee -> match projectee with | { m0; m1; m2; m3;_} -> m0
let (__proj__Mkmagic___item__m1 :
  magic_ -> Wasm_Parse_Aux_magic_1.aux_magic_1) =
  fun projectee -> match projectee with | { m0; m1; m2; m3;_} -> m1
let (__proj__Mkmagic___item__m2 :
  magic_ -> Wasm_Parse_Aux_magic_2.aux_magic_2) =
  fun projectee -> match projectee with | { m0; m1; m2; m3;_} -> m2
let (__proj__Mkmagic___item__m3 :
  magic_ -> Wasm_Parse_Aux_magic_3.aux_magic_3) =
  fun projectee -> match projectee with | { m0; m1; m2; m3;_} -> m3
type magic_' =
  ((Wasm_Parse_Aux_magic_0.aux_magic_0 * Wasm_Parse_Aux_magic_1.aux_magic_1)
    * (Wasm_Parse_Aux_magic_2.aux_magic_2 *
    Wasm_Parse_Aux_magic_3.aux_magic_3))
let (synth_magic_ : magic_' -> magic_) =
  fun x -> match x with | ((m0, m1), (m2, m3)) -> { m0; m1; m2; m3 }
let (synth_magic__recip : magic_ -> magic_') =
  fun x -> (((x.m0), (x.m1)), ((x.m2), (x.m3)))




let (magic_'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (magic_' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_magic_0.aux_magic_0_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Aux_magic_1.aux_magic_1_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match match Wasm_Parse_Aux_magic_2.aux_magic_2_parser32 input' with
               | FStar_Pervasives_Native.Some (v1, l1) ->
                   let input'1 =
                     FStar_Bytes.slice input' l1 (FStar_Bytes.len input') in
                   (match Wasm_Parse_Aux_magic_3.aux_magic_3_parser32 input'1
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
let (magic__parser32 :
  LowParse_SLow_Base.bytes32 ->
    (magic_ * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Aux_magic_0.aux_magic_0_parser32 input with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match Wasm_Parse_Aux_magic_1.aux_magic_1_parser32 input'
                     with
                     | FStar_Pervasives_Native.Some (v', l') ->
                         FStar_Pervasives_Native.Some
                           ((v, v'), (FStar_UInt32.add l l'))
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match match Wasm_Parse_Aux_magic_2.aux_magic_2_parser32 input'
                     with
                     | FStar_Pervasives_Native.Some (v1, l1) ->
                         let input'1 =
                           FStar_Bytes.slice input' l1
                             (FStar_Bytes.len input') in
                         (match Wasm_Parse_Aux_magic_3.aux_magic_3_parser32
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
          (((match v1 with | ((m0, m1), (m2, m3)) -> { m0; m1; m2; m3 })),
            consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (magic_'_serializer32 : magic_' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_magic_0.aux_magic_0_serializer32 fs1 in
              let output2 =
                Wasm_Parse_Aux_magic_1.aux_magic_1_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          match sn with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_magic_2.aux_magic_2_serializer32 fs1 in
              let output21 =
                Wasm_Parse_Aux_magic_3.aux_magic_3_serializer32 sn1 in
              FStar_Bytes.append output11 output21 in
        FStar_Bytes.append output1 output2
let (magic__serializer32 : magic_ -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.m0), (input.m1)), ((input.m2), (input.m3))) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_magic_0.aux_magic_0_serializer32 fs1 in
              let output2 =
                Wasm_Parse_Aux_magic_1.aux_magic_1_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          match sn with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_magic_2.aux_magic_2_serializer32 fs1 in
              let output21 =
                Wasm_Parse_Aux_magic_3.aux_magic_3_serializer32 sn1 in
              FStar_Bytes.append output11 output21 in
        FStar_Bytes.append output1 output2
let (magic_'_size32 : magic_' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 = Wasm_Parse_Aux_magic_0.aux_magic_0_size32 x11 in
              let v2 = Wasm_Parse_Aux_magic_1.aux_magic_1_size32 x21 in
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
              let v11 = Wasm_Parse_Aux_magic_2.aux_magic_2_size32 x11 in
              let v21 = Wasm_Parse_Aux_magic_3.aux_magic_3_size32 x21 in
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
let (magic__size32 : magic_ -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 = Wasm_Parse_Aux_magic_0.aux_magic_0_size32 input.m0 in
      let v2 = Wasm_Parse_Aux_magic_1.aux_magic_1_size32 input.m1 in
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
      let v11 = Wasm_Parse_Aux_magic_2.aux_magic_2_size32 input.m2 in
      let v21 = Wasm_Parse_Aux_magic_3.aux_magic_3_size32 input.m3 in
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
