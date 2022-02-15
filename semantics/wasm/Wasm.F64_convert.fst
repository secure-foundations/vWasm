(**
Wasm-compliant wrappers for F64 conversion operations.

@summary F64 conversions.
*)
module Wasm.F64_convert

open Wasm.Optr

/// ####################
/// DECLARATIONS
/// ####################
val promote_f32 : Wasm.F32.t -> Tot Wasm.F64.t
val convert_i32_s : Wasm.I32.t -> Tot Wasm.F64.t
val convert_i32_u : Wasm.I32.t -> Tot Wasm.F64.t
val convert_i64_s : Wasm.I64.t -> Tot Wasm.F64.t
val convert_i64_u : Wasm.I64.t -> Tot Wasm.F64.t
val reinterpret_i64 : Wasm.I64.t -> Tot Wasm.F64.t

/// ####################
/// DEFINITIONS
/// ####################
let promote_f32 x = admit()

let convert_i32_s x = admit()
let convert_i32_u x = admit()
let convert_i64_s x = admit()
let convert_i64_u x = admit()

let reinterpret_i32 x = admit()
let reinterpret_i64 x = admit()
