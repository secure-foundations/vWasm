(**
Evaluation of F64 conversion operations.

@summary F64CvtOp eval.
*)
module Wasm.Eval_numeric.F64CvtOp

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.FloatOp

module F32Op = Wasm.Eval_numeric.F32Op
module F64_convert = Wasm.F64_convert
module I32Op = Wasm.Eval_numeric.I32Op
module I64Op = Wasm.Eval_numeric.I64Op

let e_TypeError = Left "TypeError"

let cvtop_ (op:cvtop) v: optr value =
  match op with
  | PromoteF32 -> o_fmap F64 (o_fmap F64_convert.promote_f32 (F32Op.of_value v))
  | ConvertSI32 -> o_fmap F64 (o_fmap F64_convert.convert_i32_s (I32Op.of_value v))
  | ConvertUI32 -> o_fmap F64 (o_fmap F64_convert.convert_i32_u (I32Op.of_value v))
  | ConvertSI64 -> o_fmap F64 (o_fmap F64_convert.convert_i64_s (I64Op.of_value v))
  | ConvertUI64 -> o_fmap F64 (o_fmap F64_convert.convert_i64_u (I64Op.of_value v))
  | ReinterpretInt -> o_fmap F64 (o_fmap F64_convert.reinterpret_i32 (I32Op.of_value v))
  | DemoteF64 -> e_TypeError
