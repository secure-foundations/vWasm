open Prims
type table = Wasm_Parse_Tabletype.tabletype
let (table_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (table * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = Wasm_Parse_Tabletype.tabletype_parser32
let (table_serializer32 : table -> LowParse_SLow_Base.bytes32) =
  Wasm_Parse_Tabletype.tabletype_serializer32
let (table_size32 : table -> FStar_UInt32.t) =
  Wasm_Parse_Tabletype.tabletype_size32

