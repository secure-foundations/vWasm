open Prims
type f64 = unit FStar_Bytes.lbytes
let (f64_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (f64 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    if
      FStar_UInt32.lt (FStar_Bytes.len input)
        (FStar_UInt32.uint_to_t (Prims.of_int (8)))
    then FStar_Pervasives_Native.None
    else
      (let s' =
         FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
           (FStar_UInt32.uint_to_t (Prims.of_int (8))) in
       FStar_Pervasives_Native.Some
         (s', (FStar_UInt32.uint_to_t (Prims.of_int (8)))))
let (f64_serializer32 : f64 -> LowParse_SLow_Base.bytes32) =
  fun input -> input
let (f64_size32 : f64 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (Prims.of_int (8))
