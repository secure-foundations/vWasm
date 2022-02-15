/// WARNING:
/// - No longer uses the 'typeclass' indirection as it was very redundant.

(**
Primitive values of wasm.

@summary Wasm values.
*)
module Wasm.Values

open Wasm.Optr
open Wasm.Types

module I32 = Wasm.I32
module I64 = Wasm.I64
module F32 = Wasm.F32
module F64 = Wasm.F64

(* Values and operators *)

(** op is sort of both an operand or something which returns a value *)
type op (i32:Type) (i64:Type) (f32:Type) (f64:Type) =
  | I32 of i32
  | I64 of i64
  | F32 of f32
  | F64 of f64

type value = op I32.t I64.t F32.t F64.t

(* Typing *)
let type_of v =
  match v with
  | I32 _ -> I32Type
  | I64 _ -> I64Type
  | F32 _ -> F32Type
  | F64 _ -> F64Type

let default_value vty =
  match vty with
  | I32Type -> I32 I32.zero
  | I64Type -> I64 I64.zero
  | F32Type -> F32 F32.zero
  | F64Type -> F64 F64.zero

(* Conversion *)
let value_of_bool b = I32 (if b then I32.of_int_s 1 else I32.of_int_s 0)

let string_of_value v =
  match v with
  | I32 i -> I32.to_string_s i
  | I64 i -> I64.to_string_s i
  | F32 z -> F32.to_string z
  | F64 z -> F64.to_string z

let string_of_values vs =
  match vs with
  | [v] -> string_of_value v
  | vs -> "[" ^ String.concat " " (List.map string_of_value vs) ^ "]"

let e_Value vt = Left (string_of_value_type vt)
