open Prims
type i32 = FStar_UInt32.t
let (i32_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (i32 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (i32_serializer32 : i32 -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u32
let (i32_size32 : i32 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

