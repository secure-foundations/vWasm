open Prims
type f32 = unit FStar_Bytes.lbytes
let (f32_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (f32 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (4)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (4))) in
       FStar_Pervasives_Native.Some
         (s', (FStar_UInt32.uint_to_t (Prims.of_int (4)))))
let (f32_serializer32 : f32 -> LowParse_SLow_Base.bytes32) =
  fun input -> input
let (f32_size32 : f32 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (4))
