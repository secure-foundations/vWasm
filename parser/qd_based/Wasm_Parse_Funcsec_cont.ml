open Prims
type funcsec_cont = Wasm_Parse_Aux_vectypeidx.aux_vectypeidx
let (funcsec_cont_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (funcsec_cont * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_BoundedInt.parse32_bounded_integer_3 input with
          | FStar_Pervasives_Native.Some (v, consumed) ->
              if
                Prims.op_Negation
                  ((FStar_UInt32.lt v (FStar_UInt32.uint_to_t Prims.int_zero))
                     ||
                     (FStar_UInt32.lt
                        (FStar_UInt32.uint_to_t (Prims.parse_int "16777215"))
                        v))
              then FStar_Pervasives_Native.Some (v, consumed)
              else FStar_Pervasives_Native.None
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match if FStar_UInt32.lt (FStar_Bytes.len input') v
               then FStar_Pervasives_Native.None
               else
                 (match Wasm_Parse_Aux_vectypeidx.aux_vectypeidx_parser32
                          (FStar_Bytes.slice input'
                             (FStar_UInt32.uint_to_t Prims.int_zero) v)
                  with
                  | FStar_Pervasives_Native.Some (v1, consumed) ->
                      if consumed = v
                      then FStar_Pervasives_Native.Some (v1, consumed)
                      else FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None)
         with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some (v', (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (funcsec_cont_serializer32 : funcsec_cont -> LowParse_SLow_Base.bytes32)
  =
  fun input ->
    let pl = Wasm_Parse_Aux_vectypeidx.aux_vectypeidx_serializer32 input in
    let len = FStar_Bytes.len pl in
    let slen = LowParse_SLow_BoundedInt.serialize32_bounded_integer_3 len in
    let res = FStar_Bytes.append slen pl in res
let (funcsec_cont_size32 : funcsec_cont -> FStar_UInt32.t) =
  fun input ->
    let len = Wasm_Parse_Aux_vectypeidx.aux_vectypeidx_size32 input in
    FStar_UInt32.add (FStar_UInt32.uint_to_t (Prims.of_int (3))) len
