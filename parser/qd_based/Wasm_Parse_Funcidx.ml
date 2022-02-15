open Prims
type funcidx = FStar_UInt32.t
let (funcidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (funcidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (funcidx_serializer32 : funcidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (funcidx_size32 : funcidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

