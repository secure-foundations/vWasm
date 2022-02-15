(**
Wasm-compliant wrappers for F32 conversion operations.

@summary F32 conversions.
*)
module Wasm.F32_convert

open Wasm.Optr

/// ####################
/// DECLARATIONS
/// ####################
val demote_f64 : Wasm.F64.t -> Tot Wasm.F32.t
val convert_i32_s : Wasm.I32.t -> Tot Wasm.F32.t
val convert_i32_u : Wasm.I32.t -> Tot Wasm.F32.t
val convert_i64_s : Wasm.I64.t -> Tot Wasm.F32.t
val convert_i64_u : Wasm.I64.t -> Tot Wasm.F32.t
val reinterpret_i32 : Wasm.I32.t -> Tot Wasm.F32.t

/// ####################
/// DEFINITIONS
/// ####################
let demote_f64 x = admit()

let convert_i32_s x = admit()
let convert_i32_u x = admit()
let convert_i64_s x = admit()
let convert_i64_u x = admit()

let reinterpret_i32 x = admit()
