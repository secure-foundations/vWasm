module Common.Memory

open Types_s
open Opaque_s
open Words_s

type heap = Map.t int nat8
let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

val mod_8: (n:nat{n < pow2_64}) -> nat8
let mod_8 n = n % 0x100

/// Which addresses are valid in the heap?

let valid_addr (ptr:int) (mem:heap) : bool =
  Map.contains mem ptr

let valid_addr8 (ptr:int) (mem:heap) : bool =
  valid_addr ptr mem

let valid_addr16 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr+1) mem

let valid_addr32 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr+1) mem &&
  valid_addr (ptr+2) mem &&
  valid_addr (ptr+3) mem

let valid_addr64 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr+1) mem &&
  valid_addr (ptr+2) mem &&
  valid_addr (ptr+3) mem &&
  valid_addr (ptr+4) mem &&
  valid_addr (ptr+5) mem &&
  valid_addr (ptr+6) mem &&
  valid_addr (ptr+7) mem

let valid_addr128 (ptr:int) (mem:heap) =
  valid_addr ptr mem &&
  valid_addr (ptr+1) mem &&
  valid_addr (ptr+2) mem &&
  valid_addr (ptr+3) mem &&
  valid_addr (ptr+4) mem &&
  valid_addr (ptr+5) mem &&
  valid_addr (ptr+6) mem &&
  valid_addr (ptr+7) mem &&
  valid_addr (ptr+8) mem &&
  valid_addr (ptr+9) mem &&
  valid_addr (ptr+10) mem &&
  valid_addr (ptr+11) mem &&
  valid_addr (ptr+12) mem &&
  valid_addr (ptr+13) mem &&
  valid_addr (ptr+14) mem &&
  valid_addr (ptr+15) mem

/// Reading a value from the heap

// TODO: Need to be sure that load/store_mem does an appropriate little-endian load

let get_heap_val8_def (ptr:int) (mem:heap) : nat8 =
  mem.[ptr]
let get_heap_val8 = make_opaque get_heap_val8_def

let get_heap_val16_def (ptr:int) (mem:heap) : nat16 =
  Views.nat8s_to_nat16
    mem.[ptr]
    mem.[ptr+1]
let get_heap_val16 = make_opaque get_heap_val16_def

let get_heap_val32_def (ptr:int) (mem:heap) : nat32 =
  Views.nat8s_to_nat32
    mem.[ptr]
    mem.[ptr+1]
    mem.[ptr+2]
    mem.[ptr+3]
let get_heap_val32 = make_opaque get_heap_val32_def

let get_heap_val64_def (ptr:int) (mem:heap) : nat64 =
    Views.nat8s_to_nat64
      mem.[ptr]
      mem.[ptr+1]
      mem.[ptr+2]
      mem.[ptr+3]
      mem.[ptr+4]
      mem.[ptr+5]
      mem.[ptr+6]
      mem.[ptr+7]
let get_heap_val64 = make_opaque get_heap_val64_def

let get_heap_val128_def (ptr:int) (mem:heap) : quad32 = Mkfour
  (get_heap_val32 ptr mem)
  (get_heap_val32 (ptr+4) mem)
  (get_heap_val32 (ptr+8) mem)
  (get_heap_val32 (ptr+12) mem)
let get_heap_val128 = make_opaque get_heap_val128_def

/// Updating the heap

let update_heap8_def (ptr:int) (v:nat8) (mem:heap) : heap =
  let mem = mem.[ptr] <- (mod_8 v) in
  mem
let update_heap8 = make_opaque update_heap8_def

let update_heap16_def (ptr:int) (v:nat16) (mem:heap) : heap =
  let mem = mem.[ptr] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+1] <- (mod_8 v) in
  mem
let update_heap16 = make_opaque update_heap16_def

let update_heap32_def (ptr:int) (v:nat32) (mem:heap) : heap =
  let mem = mem.[ptr] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+1] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+2] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+3] <- (mod_8 v) in
  mem
let update_heap32 = make_opaque update_heap32_def

let update_heap64_def (ptr:int) (v:nat64) (mem:heap) : heap =
  let mem = mem.[ptr] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+1] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+2] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+3] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+4] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+5] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+6] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+7] <- (mod_8 v) in
  mem
let update_heap64 = make_opaque update_heap64_def

let update_heap128 (ptr:int) (v:quad32) (mem:heap) =
  let mem = update_heap32 ptr v.lo0 mem in
  let mem = update_heap32 (ptr+4) v.lo1 mem in
  let mem = update_heap32 (ptr+8) v.hi2 mem in
  let mem = update_heap32 (ptr+12) v.hi3 mem in
mem
