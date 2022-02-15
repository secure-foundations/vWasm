(**
Wasm-compliant wrappers for I64 conversion operations.

@summary I64 conversions.
*)
module Wasm.I64_convert

open Wasm.Optr

/// ####################
/// DECLARATIONS
/// ####################
val extend_i32_s: Wasm.I32.t -> Tot Wasm.I64.t
val extend_i32_u: Wasm.I32.t -> Tot Wasm.I64.t
val trunc_f32_s: Wasm.F32.t -> Tot (optr Wasm.I64.t)
val trunc_f32_u: Wasm.F32.t -> Tot (optr Wasm.I64.t)
val trunc_f64_s: Wasm.F64.t -> Tot (optr Wasm.I64.t)
val trunc_f64_u: Wasm.F64.t -> Tot (optr Wasm.I64.t)
val reinterpret_f64: Wasm.F64.t -> Tot Wasm.I64.t

/// ####################
/// DEFINITIONS
/// ####################
let extend_i32_s x = Wasm.I64.of_int_s (Wasm.I32.to_int_s x)

let extend_i32_u x = Wasm.I64.of_int_u (Wasm.I32.to_int_u x)

let trunc_f32_s x = admit()
let trunc_f32_u x = admit()
let trunc_f64_s x = admit()
let trunc_f64_u x = admit()

let reinterpret_f64 x = admit()
