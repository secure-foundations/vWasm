open Prims
type mem = Wasm_Parse_Memtype.memtype
let (mem_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (mem * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = Wasm_Parse_Memtype.memtype_parser32
let (mem_serializer32 : mem -> LowParse_SLow_Base.bytes32) =
  Wasm_Parse_Memtype.memtype_serializer32
let (mem_size32 : mem -> FStar_UInt32.t) = Wasm_Parse_Memtype.memtype_size32

