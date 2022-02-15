open Prims
type labelidx = FStar_UInt32.t
let (labelidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (labelidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (labelidx_serializer32 : labelidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (labelidx_size32 : labelidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

