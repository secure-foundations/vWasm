open Prims
type aux_br_table =
  {
  ls: Wasm_Parse_Aux_veclabelidx.aux_veclabelidx ;
  ln: Wasm_Parse_Labelidx.labelidx }
let (__proj__Mkaux_br_table__item__ls :
  aux_br_table -> Wasm_Parse_Aux_veclabelidx.aux_veclabelidx) =
  fun projectee -> match projectee with | { ls; ln;_} -> ls
let (__proj__Mkaux_br_table__item__ln :
  aux_br_table -> Wasm_Parse_Labelidx.labelidx) =
  fun projectee -> match projectee with | { ls; ln;_} -> ln
type aux_br_table' =
  (Wasm_Parse_Aux_veclabelidx.aux_veclabelidx * Wasm_Parse_Labelidx.labelidx)
let (synth_aux_br_table : aux_br_table' -> aux_br_table) =
  fun x -> match x with | (ls, ln) -> { ls; ln }
let (synth_aux_br_table_recip : aux_br_table -> aux_br_table') =
  fun x -> ((x.ls), (x.ln))




let (aux_br_table'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_br_table' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match Wasm_Parse_Aux_veclabelidx.aux_veclabelidx_parser32 input with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match Wasm_Parse_Labelidx.labelidx_parser32 input' with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_br_table_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_br_table * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match Wasm_Parse_Aux_veclabelidx.aux_veclabelidx_parser32 input
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match Wasm_Parse_Labelidx.labelidx_parser32 input' with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with | (ls, ln) -> { ls; ln })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_br_table'_serializer32 :
  aux_br_table' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          Wasm_Parse_Aux_veclabelidx.aux_veclabelidx_serializer32 fs in
        let output2 = Wasm_Parse_Labelidx.labelidx_serializer32 sn in
        FStar_Bytes.append output1 output2
let (aux_br_table_serializer32 : aux_br_table -> LowParse_SLow_Base.bytes32)
  =
  fun input ->
    let x = ((input.ls), (input.ln)) in
    match x with
    | (fs, sn) ->
        let output1 =
          Wasm_Parse_Aux_veclabelidx.aux_veclabelidx_serializer32 fs in
        let output2 = Wasm_Parse_Labelidx.labelidx_serializer32 sn in
        FStar_Bytes.append output1 output2
let (aux_br_table'_size32 : aux_br_table' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 = Wasm_Parse_Aux_veclabelidx.aux_veclabelidx_size32 x1 in
        let v2 = Wasm_Parse_Labelidx.labelidx_size32 x2 in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (aux_br_table_size32 : aux_br_table -> FStar_UInt32.t) =
  fun input ->
    let v1 = Wasm_Parse_Aux_veclabelidx.aux_veclabelidx_size32 input.ls in
    let v2 = Wasm_Parse_Labelidx.labelidx_size32 input.ln in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
