open Prims
type globalidx = FStar_UInt32.t
let (globalidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (globalidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (globalidx_serializer32 : globalidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (globalidx_size32 : globalidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

