(**
Evaluation of I32 conversion operations.

@summary I32CvtOp eval.
*)
module Wasm.Eval_numeric.I32CvtOp

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.IntOp

module F32Op = Wasm.Eval_numeric.F32Op
module F64Op = Wasm.Eval_numeric.F64Op
module I32_convert = Wasm.I32_convert
module I64Op = Wasm.Eval_numeric.I64Op

let e_TypeError = Left "TypeError"

let cvtop_ (op:cvtop) v: optr value =
  match op with
  | WrapI64 -> o_fmap I32 (o_fmap I32_convert.wrap_i64 (I64Op.of_value v))
  | TruncSF32 -> o_fmap I32 (o_bind I32_convert.trunc_f32_s (F32Op.of_value v))
  | TruncUF32 -> o_fmap I32 (o_bind I32_convert.trunc_f32_u (F32Op.of_value v))
  | TruncSF64 -> o_fmap I32 (o_bind I32_convert.trunc_f64_s (F64Op.of_value v))
  | TruncUF64 -> o_fmap I32 (o_bind I32_convert.trunc_f64_u (F64Op.of_value v))
  | ReinterpretFloat -> o_fmap I32 (o_fmap I32_convert.reinterpret_f32 (F32Op.of_value v))
  | ExtendSI32 -> e_TypeError
  | ExtendUI32 -> e_TypeError
