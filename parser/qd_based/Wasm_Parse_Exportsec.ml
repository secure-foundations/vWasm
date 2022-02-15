open Prims
type exportsec =
  {
  n: Wasm_Parse_Aux_section_const7.aux_section_const7 ;
  aux_ignore_byte: Wasm_Parse_Aux_constbyte0.aux_constbyte0 ;
  cont: Wasm_Parse_Exportsec_cont.exportsec_cont }
let (__proj__Mkexportsec__item__n :
  exportsec -> Wasm_Parse_Aux_section_const7.aux_section_const7) =
  fun projectee -> match projectee with | { n; aux_ignore_byte; cont;_} -> n
let (__proj__Mkexportsec__item__aux_ignore_byte :
  exportsec -> Wasm_Parse_Aux_constbyte0.aux_constbyte0) =
  fun projectee ->
    match projectee with | { n; aux_ignore_byte; cont;_} -> aux_ignore_byte
let (__proj__Mkexportsec__item__cont :
  exportsec -> Wasm_Parse_Exportsec_cont.exportsec_cont) =
  fun projectee ->
    match projectee with | { n; aux_ignore_byte; cont;_} -> cont
type exportsec' =
  ((Wasm_Parse_Aux_section_const7.aux_section_const7 *
    Wasm_Parse_Aux_constbyte0.aux_constbyte0) *
    Wasm_Parse_Exportsec_cont.exportsec_cont)
let (synth_exportsec : exportsec' -> exportsec) =
  fun x ->
    match x with
    | ((n, aux_ignore_byte), cont) -> { n; aux_ignore_byte; cont }
let (synth_exportsec_recip : exportsec -> exportsec') =
  fun x -> (((x.n), (x.aux_ignore_byte)), (x.cont))




let (exportsec'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (exportsec' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_section_const7.aux_section_const7_parser32
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
        (match Wasm_Parse_Exportsec_cont.exportsec_cont_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (exportsec_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (exportsec * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Aux_section_const7.aux_section_const7_parser32
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
              (match Wasm_Parse_Exportsec_cont.exportsec_cont_parser32 input'
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
let (exportsec'_serializer32 : exportsec' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_section_const7.aux_section_const7_serializer32
                  fs1 in
              let output2 =
                Wasm_Parse_Aux_constbyte0.aux_constbyte0_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Exportsec_cont.exportsec_cont_serializer32 sn in
        FStar_Bytes.append output1 output2
let (exportsec_serializer32 : exportsec -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.n), (input.aux_ignore_byte)), (input.cont)) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_section_const7.aux_section_const7_serializer32
                  fs1 in
              let output2 =
                Wasm_Parse_Aux_constbyte0.aux_constbyte0_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Exportsec_cont.exportsec_cont_serializer32 sn in
        FStar_Bytes.append output1 output2
let (exportsec'_size32 : exportsec' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 =
                Wasm_Parse_Aux_section_const7.aux_section_const7_size32 x11 in
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
        let v2 = Wasm_Parse_Exportsec_cont.exportsec_cont_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (exportsec_size32 : exportsec -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 =
        Wasm_Parse_Aux_section_const7.aux_section_const7_size32 input.n in
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
    let v2 = Wasm_Parse_Exportsec_cont.exportsec_cont_size32 input.cont in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
