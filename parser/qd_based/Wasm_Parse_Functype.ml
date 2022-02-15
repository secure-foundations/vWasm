open Prims
type functype =
  {
  m: Wasm_Parse_Aux_functype_magic.aux_functype_magic ;
  params: Wasm_Parse_Aux_vecvaltype.aux_vecvaltype ;
  results: Wasm_Parse_Aux_vecvaltype.aux_vecvaltype }
let (__proj__Mkfunctype__item__m :
  functype -> Wasm_Parse_Aux_functype_magic.aux_functype_magic) =
  fun projectee -> match projectee with | { m; params; results;_} -> m
let (__proj__Mkfunctype__item__params :
  functype -> Wasm_Parse_Aux_vecvaltype.aux_vecvaltype) =
  fun projectee -> match projectee with | { m; params; results;_} -> params
let (__proj__Mkfunctype__item__results :
  functype -> Wasm_Parse_Aux_vecvaltype.aux_vecvaltype) =
  fun projectee -> match projectee with | { m; params; results;_} -> results
type functype' =
  ((Wasm_Parse_Aux_functype_magic.aux_functype_magic *
    Wasm_Parse_Aux_vecvaltype.aux_vecvaltype) *
    Wasm_Parse_Aux_vecvaltype.aux_vecvaltype)
let (synth_functype : functype' -> functype) =
  fun x -> match x with | ((m, params), results) -> { m; params; results }
let (synth_functype_recip : functype -> functype') =
  fun x -> (((x.m), (x.params)), (x.results))




let (functype'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (functype' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_functype_magic.aux_functype_magic_parser32
                  input
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_parser32 input'
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (functype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (functype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Aux_functype_magic.aux_functype_magic_parser32
                        input
                with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_parser32
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
              (match Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_parser32 input'
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | ((m, params), results) -> { m; params; results })),
            consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (functype'_serializer32 : functype' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_functype_magic.aux_functype_magic_serializer32
                  fs1 in
              let output2 =
                Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_serializer32 sn in
        FStar_Bytes.append output1 output2
let (functype_serializer32 : functype -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.m), (input.params)), (input.results)) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                Wasm_Parse_Aux_functype_magic.aux_functype_magic_serializer32
                  fs1 in
              let output2 =
                Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_serializer32 sn in
        FStar_Bytes.append output1 output2
let (functype'_size32 : functype' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 =
                Wasm_Parse_Aux_functype_magic.aux_functype_magic_size32 x11 in
              let v2 = Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v2) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v2 in
              res in
        let v2 = Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (functype_size32 : functype -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 =
        Wasm_Parse_Aux_functype_magic.aux_functype_magic_size32 input.m in
      let v2 = Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_size32 input.params in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v2 in
      res in
    let v2 = Wasm_Parse_Aux_vecvaltype.aux_vecvaltype_size32 input.results in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
