open Prims
type elem =
  {
  x: Wasm_Parse_Tableidx.tableidx ;
  e: Wasm_Parse_Constexpr.constexpr ;
  y: Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx }
let (__proj__Mkelem__item__x : elem -> Wasm_Parse_Tableidx.tableidx) =
  fun projectee -> match projectee with | { x; e; y;_} -> x
let (__proj__Mkelem__item__e : elem -> Wasm_Parse_Constexpr.constexpr) =
  fun projectee -> match projectee with | { x; e; y;_} -> e
let (__proj__Mkelem__item__y :
  elem -> Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx) =
  fun projectee -> match projectee with | { x; e; y;_} -> y
type elem' =
  ((Wasm_Parse_Tableidx.tableidx * Wasm_Parse_Constexpr.constexpr) *
    Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx)
let (synth_elem : elem' -> elem) =
  fun x -> match x with | ((x1, e), y) -> { x = x1; e; y }
let (synth_elem_recip : elem -> elem') = fun x -> (((x.x), (x.e)), (x.y))




let (elem'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (elem' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Tableidx.tableidx_parser32 input with
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
        (match Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (elem_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (elem * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match Wasm_Parse_Tableidx.tableidx_parser32 input with
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
              (match Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx_parser32 input'
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | ((x, e), y) -> { x; e; y })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (elem'_serializer32 : elem' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 = Wasm_Parse_Tableidx.tableidx_serializer32 fs1 in
              let output2 = Wasm_Parse_Constexpr.constexpr_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx_serializer32 sn in
        FStar_Bytes.append output1 output2
let (elem_serializer32 : elem -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = (((input.x), (input.e)), (input.y)) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 = Wasm_Parse_Tableidx.tableidx_serializer32 fs1 in
              let output2 = Wasm_Parse_Constexpr.constexpr_serializer32 sn1 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx_serializer32 sn in
        FStar_Bytes.append output1 output2
let (elem'_size32 : elem' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 = Wasm_Parse_Tableidx.tableidx_size32 x11 in
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
        let v2 = Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (elem_size32 : elem -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 = Wasm_Parse_Tableidx.tableidx_size32 input.x in
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
    let v2 = Wasm_Parse_Aux_vecfuncidx.aux_vecfuncidx_size32 input.y in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
