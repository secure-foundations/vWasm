open Prims
type memtype = Wasm_Parse_Limits.limits
let (memtype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (memtype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = Wasm_Parse_Limits.limits_parser32
let (memtype_serializer32 : memtype -> LowParse_SLow_Base.bytes32) =
  Wasm_Parse_Limits.limits_serializer32
let (memtype_size32 : memtype -> FStar_UInt32.t) =
  Wasm_Parse_Limits.limits_size32

