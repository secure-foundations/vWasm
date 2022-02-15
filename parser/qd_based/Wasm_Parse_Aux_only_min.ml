open Prims
type aux_only_min = FStar_UInt32.t
let (aux_only_min_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_only_min * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = LowParse_SLow_Int.parse32_u32
let (aux_only_min_serializer32 : aux_only_min -> LowParse_SLow_Base.bytes32)
  = LowParse_SLow_Int.serialize32_u32
let (aux_only_min_size32 : aux_only_min -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))

