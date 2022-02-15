open Prims
let (b32slice :
  FStar_Bytes.bytes -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_Bytes.bytes)
  = fun b -> fun s -> fun e -> FStar_Bytes.slice b s e
let (b32append : FStar_Bytes.bytes -> FStar_Bytes.bytes -> FStar_Bytes.bytes)
  = fun b1 -> fun b2 -> FStar_Bytes.append b1 b2



