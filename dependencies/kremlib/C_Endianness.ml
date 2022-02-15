open Prims
let (htole16 : FStar_UInt16.t -> FStar_UInt16.t) =
  fun uu___ -> failwith "Not yet implemented:htole16"
let (le16toh : FStar_UInt16.t -> FStar_UInt16.t) =
  fun uu___ -> failwith "Not yet implemented:le16toh"
let (htole32 : FStar_UInt32.t -> FStar_UInt32.t) =
  fun uu___ -> failwith "Not yet implemented:htole32"
let (le32toh : FStar_UInt32.t -> FStar_UInt32.t) =
  fun uu___ -> failwith "Not yet implemented:le32toh"
let (htole64 : FStar_UInt64.t -> FStar_UInt64.t) =
  fun uu___ -> failwith "Not yet implemented:htole64"
let (le64toh : FStar_UInt64.t -> FStar_UInt64.t) =
  fun uu___ -> failwith "Not yet implemented:le64toh"
let (htobe16 : FStar_UInt16.t -> FStar_UInt16.t) =
  fun uu___ -> failwith "Not yet implemented:htobe16"
let (be16toh : FStar_UInt16.t -> FStar_UInt16.t) =
  fun uu___ -> failwith "Not yet implemented:be16toh"
let (htobe32 : FStar_UInt32.t -> FStar_UInt32.t) =
  fun uu___ -> failwith "Not yet implemented:htobe32"
let (be32toh : FStar_UInt32.t -> FStar_UInt32.t) =
  fun uu___ -> failwith "Not yet implemented:be32toh"
let (htobe64 : FStar_UInt64.t -> FStar_UInt64.t) =
  fun uu___ -> failwith "Not yet implemented:htobe64"
let (be64toh : FStar_UInt64.t -> FStar_UInt64.t) =
  fun uu___ -> failwith "Not yet implemented:be64toh"
let (store16_le :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt16.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store16_le"
let (load16_le : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt16.t) =
  fun b -> failwith "Not yet implemented:load16_le"
let (store16_be :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt16.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store16_be"
let (load16_be : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt16.t) =
  fun b -> failwith "Not yet implemented:load16_be"
let (store32_le :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store32_le"
let (load32_le : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t) =
  fun b -> failwith "Not yet implemented:load32_le"
let (store32_be :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store32_be"
let (load32_be : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t) =
  fun b -> failwith "Not yet implemented:load32_be"
let (store64_le :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt64.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store64_le"
let (load64_le : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt64.t) =
  fun b -> failwith "Not yet implemented:load64_le"
let (load64_be : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt64.t) =
  fun b -> failwith "Not yet implemented:load64_be"
let (store64_be :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt64.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store64_be"
let (load128_le : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt128.t) =
  fun b -> failwith "Not yet implemented:load128_le"
let (store128_le :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt128.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store128_le"
let (load128_be : FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt128.t) =
  fun b -> failwith "Not yet implemented:load128_be"
let (store128_be :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt128.t -> unit) =
  fun b -> fun z -> failwith "Not yet implemented:store128_be"
let (index_32_be :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun b ->
    fun i ->
      let uu___ =
        LowStar_Monotonic_Buffer.msub b
          (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (4))) i) () in
      load32_be uu___
let (index_32_le :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun b ->
    fun i ->
      let uu___ =
        LowStar_Monotonic_Buffer.msub b
          (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (4))) i) () in
      load32_le uu___
let (index_64_be :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun b ->
    fun i ->
      let uu___ =
        LowStar_Monotonic_Buffer.msub b
          (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (8))) i) () in
      load64_be uu___
let (index_64_le :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun b ->
    fun i ->
      let uu___ =
        LowStar_Monotonic_Buffer.msub b
          (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (8))) i) () in
      load64_le uu___

let (upd_32_be :
  FStar_UInt8.t LowStar_Buffer.buffer ->
    FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun b ->
    fun i ->
      fun v ->
        let h0 = FStar_HyperStack_ST.get () in
        (let uu___1 =
           LowStar_Monotonic_Buffer.msub b
             (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (4))) i)
             () in
         store32_be uu___1 v);
        (let h1 = FStar_HyperStack_ST.get () in ())