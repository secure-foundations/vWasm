open Prims
type typeidx = FStar_UInt32.t
let (typeidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (typeidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (typeidx_serializer32 : typeidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (typeidx_size32 : typeidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

