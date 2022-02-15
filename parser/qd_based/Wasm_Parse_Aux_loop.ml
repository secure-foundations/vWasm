open Prims
type aux_loop = Wasm_Parse_Blocktype.blocktype
let (aux_loop_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_loop * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = Wasm_Parse_Blocktype.blocktype_parser32
let (aux_loop_serializer32 : aux_loop -> LowParse_SLow_Base.bytes32) =
  Wasm_Parse_Blocktype.blocktype_serializer32
let (aux_loop_size32 : aux_loop -> FStar_UInt32.t) =
  Wasm_Parse_Blocktype.blocktype_size32

