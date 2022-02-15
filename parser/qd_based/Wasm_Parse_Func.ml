open Prims
type func =
  {
  t: Wasm_Parse_Aux_veclocals.aux_veclocals ;
  e: Wasm_Parse_Expr.expr }
let (__proj__Mkfunc__item__t :
  func -> Wasm_Parse_Aux_veclocals.aux_veclocals) =
  fun projectee -> match projectee with | { t; e;_} -> t
let (__proj__Mkfunc__item__e : func -> Wasm_Parse_Expr.expr) =
  fun projectee -> match projectee with | { t; e;_} -> e
type func' = (Wasm_Parse_Aux_veclocals.aux_veclocals * Wasm_Parse_Expr.expr)
let (synth_func : func' -> func) = fun x -> match x with | (t, e) -> { t; e }
let (synth_func_recip : func -> func') = fun x -> ((x.t), (x.e))




let (func'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (func' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Aux_veclocals.aux_veclocals_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Expr.expr_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (func_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (func * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_veclocals.aux_veclocals_parser32 input with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Expr.expr_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (t, e) -> { t; e })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (func'_serializer32 : func' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Aux_veclocals.aux_veclocals_serializer32 fs in
        let output2 = Wasm_Parse_Expr.expr_serializer32 sn in
        FStar_Bytes.append output1 output2
let (func_serializer32 : func -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = ((input.t), (input.e)) in
    match x with
    | (fs, sn) ->
        let output1 = Wasm_Parse_Aux_veclocals.aux_veclocals_serializer32 fs in
        let output2 = Wasm_Parse_Expr.expr_serializer32 sn in
        FStar_Bytes.append output1 output2
let (func'_size32 : func' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Aux_veclocals.aux_veclocals_size32 x1 in
        let v2 = Wasm_Parse_Expr.expr_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (func_size32 : func -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Aux_veclocals.aux_veclocals_size32 input.t in
    let v2 = Wasm_Parse_Expr.expr_size32 input.e in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
