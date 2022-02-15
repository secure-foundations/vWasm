(**
Wasm-compliant wrappers for I32 conversion operations.

@summary I32 conversions.
*)
module Wasm.I32_convert

open Wasm.Optr

/// ####################
/// DECLARATIONS
/// ####################
val wrap_i64: Wasm.I64.t -> Tot Wasm.I32.t
val trunc_f32_s: Wasm.F32.t -> Tot (optr Wasm.I32.t)
val trunc_f32_u: Wasm.F32.t -> Tot (optr Wasm.I32.t)
val trunc_f64_s: Wasm.F64.t -> Tot (optr Wasm.I32.t)
val trunc_f64_u: Wasm.F64.t -> Tot (optr Wasm.I32.t)
val reinterpret_f32: Wasm.F32.t -> Tot Wasm.I32.t

/// ####################
/// DEFINITIONS
/// ####################
let wrap_i64 x = Wasm.I32.of_int_u (Wasm.I64.to_int_u x)

let trunc_f32_s x = admit()
let trunc_f32_u x = admit()
let trunc_f64_s x = admit()
let trunc_f64_u x = admit()

let reinterpret_f32 x = admit()
