open Prims
type start = Wasm_Parse_Funcidx.funcidx
let (start_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (start * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = Wasm_Parse_Funcidx.funcidx_parser32
let (start_serializer32 : start -> LowParse_SLow_Base.bytes32) =
  Wasm_Parse_Funcidx.funcidx_serializer32
let (start_size32 : start -> FStar_UInt32.t) =
  Wasm_Parse_Funcidx.funcidx_size32

