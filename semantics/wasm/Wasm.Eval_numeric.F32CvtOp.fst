(**
Evaluation of F32 conversion operations.

@summary F32CvtOp eval.
*)
module Wasm.Eval_numeric.F32CvtOp

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.FloatOp

module F32_convert = Wasm.F32_convert
module F64Op = Wasm.Eval_numeric.F64Op
module I32Op = Wasm.Eval_numeric.I32Op
module I64Op = Wasm.Eval_numeric.I64Op

let e_TypeError = Left "TypeError"

let cvtop_ (op:cvtop) v: optr value =
  match op with
  | DemoteF64 -> o_fmap F32 (o_fmap F32_convert.demote_f64 (F64Op.of_value v))
  | ConvertSI32 -> o_fmap F32 (o_fmap F32_convert.convert_i32_s (I32Op.of_value v))
  | ConvertUI32 -> o_fmap F32 (o_fmap F32_convert.convert_i32_u (I32Op.of_value v))
  | ConvertSI64 -> o_fmap F32 (o_fmap F32_convert.convert_i64_s (I64Op.of_value v))
  | ConvertUI64 -> o_fmap F32 (o_fmap F32_convert.convert_i64_u (I64Op.of_value v))
  | ReinterpretInt -> o_fmap F32 (o_fmap F32_convert.reinterpret_i32 (I32Op.of_value v))
  | PromoteF32 -> e_TypeError
