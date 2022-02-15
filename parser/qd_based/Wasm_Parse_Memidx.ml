open Prims
type memidx = FStar_UInt32.t
let (memidx_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (memidx * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (memidx_serializer32 : memidx -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (memidx_size32 : memidx -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

