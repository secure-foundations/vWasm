open Prims
type aux_if = Wasm_Parse_Blocktype.blocktype
let (aux_if_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_if * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = Wasm_Parse_Blocktype.blocktype_parser32
let (aux_if_serializer32 : aux_if -> LowParse_SLow_Base.bytes32) =
  Wasm_Parse_Blocktype.blocktype_serializer32
let (aux_if_size32 : aux_if -> FStar_UInt32.t) =
  Wasm_Parse_Blocktype.blocktype_size32

