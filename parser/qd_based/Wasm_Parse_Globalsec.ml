open Prims
type globalsec =
  {
  n: Wasm_Parse_Aux_section_const6.aux_section_const6 ;
  aux_ignore_byte: Wasm_Parse_Aux_constbyte0.aux_constbyte0 ;
  cont: Wasm_Parse_Globalsec_cont.globalsec_cont }
let (__proj__Mkglobalsec__item__n :
  globalsec -> Wasm_Parse_Aux_section_const6.aux_section_const6) =
  fun projectee -> match projectee with | { n; aux_ignore_byte; cont;_} -> n
let (__proj__Mkglobalsec__item__aux_ignore_byte :
  globalsec -> Wasm_Parse_Aux_constbyte0.aux_constbyte0) =
  fun projectee ->
    match projectee with | { n; aux_ignore_byte; cont;_} -> aux_ignore_byte
let (__proj__Mkglobalsec__item__cont :
  globalsec -> Wasm_Parse_Globalsec_cont.globalsec_cont) =
  fun projectee ->
    match projectee with | { n; aux_ignore_byte; cont;_} -> cont
type globalsec' =
  ((Wasm_Parse_Aux_section_const6.aux_section_const6 *
    Wasm_Parse_Aux_constbyte0.aux_constbyte0) *
    Wasm_Parse_Globalsec_cont.globalsec_cont)
let (synth_globalsec : globalsec' -> globalsec) =
  fun x ->
    match x with
    | ((n, aux_ignore_byte), cont) -> { n; aux_ignore_byte; cont }
let (synth_globalsec_recip : globalsec -> globalsec') =
  fun x -> (((x.n), (x.aux_ignore_byte)), (x.cont))




let (globalsec'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (globalsec' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_section_const6.aux_section_const6_parser32
                  input
          with
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
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Globalsec_cont.globalsec_cont_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (globalsec_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (globalsec * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Aux_section_const6.aux_section_const6_parser32
                        input
                with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match Wasm_Parse_Aux_constbyte0.aux_constbyte0_parser32
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
              (match Wasm_Parse_Globalsec_cont.globalsec_cont_parser32 input'
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
             | ((n, aux_ignore_byte), cont) -> { n; aux_ignore_byte; cont })),
            consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (globalsec'_serializer32 : globalsec' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_section_const6.aux_section_const6_serializer32
                  fs1 in
              let output2 =
                Wasm_Parse_Aux_constbyte0.aux_constbyte0_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Globalsec_cont.globalsec_cont_serializer32 sn in
        FStar_Bytes.append output1 output2
let (globalsec_serializer32 : globalsec -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.n), (input.aux_ignore_byte)), (input.cont)) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_section_const6.aux_section_const6_serializer32
                  fs1 in
              let output2 =
                Wasm_Parse_Aux_constbyte0.aux_constbyte0_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Globalsec_cont.globalsec_cont_serializer32 sn in
        FStar_Bytes.append output1 output2
let (globalsec'_size32 : globalsec' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 =
                Wasm_Parse_Aux_section_const6.aux_section_const6_size32 x11 in
              let v2 = Wasm_Parse_Aux_constbyte0.aux_constbyte0_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v2) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v2 in
              res in
        let v2 = Wasm_Parse_Globalsec_cont.globalsec_cont_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (globalsec_size32 : globalsec -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 =
        Wasm_Parse_Aux_section_const6.aux_section_const6_size32 input.n in
      let v2 =
        Wasm_Parse_Aux_constbyte0.aux_constbyte0_size32 input.aux_ignore_byte in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v2 in
      res in
    let v2 = Wasm_Parse_Globalsec_cont.globalsec_cont_size32 input.cont in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
