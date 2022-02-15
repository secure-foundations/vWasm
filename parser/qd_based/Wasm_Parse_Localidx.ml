open Prims
type localidx = FStar_UInt32.t
let (localidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (localidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (localidx_serializer32 : localidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (localidx_size32 : localidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

