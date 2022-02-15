open Prims
let (decode_int32le : LowParse_Bytes.bytes -> FStar_UInt32.t) =
  fun b -> let res = FStar_Endianness.le_to_n b in FStar_UInt32.uint_to_t res









