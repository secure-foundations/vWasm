open Prims
type i64 = FStar_UInt64.t
let (i64_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (i64 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u64
let (i64_serializer32 : i64 -> LowParse_SLow_Base.bytes32) =
  LowParse_SLow_Int.serialize32_u64
let (i64_size32 : i64 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (8))

