open Prims
type tableidx = FStar_UInt32.t
let (tableidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (tableidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (tableidx_serializer32 : tableidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (tableidx_size32 : tableidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

