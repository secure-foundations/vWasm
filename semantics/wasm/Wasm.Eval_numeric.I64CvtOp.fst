(**
Evaluation of I64 conversion operations.

@summary I64CvtOp eval.
*)
module Wasm.Eval_numeric.I64CvtOp

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.IntOp

module F32Op = Wasm.Eval_numeric.F32Op
module F64Op = Wasm.Eval_numeric.F64Op
module I32Op = Wasm.Eval_numeric.I32Op
module I64_convert = Wasm.I64_convert

let e_TypeError = Left "TypeError"

let cvtop_ (op:cvtop) v: optr value =
  match op with
  | ExtendSI32 -> o_fmap I64 (o_fmap I64_convert.extend_i32_s (I32Op.of_value v))
  | ExtendUI32 -> o_fmap I64 (o_fmap I64_convert.extend_i32_u (I32Op.of_value v))
  | TruncSF32 -> o_fmap I64 (o_bind I64_convert.trunc_f32_s (F32Op.of_value v))
  | TruncUF32 -> o_fmap I64 (o_bind I64_convert.trunc_f32_u (F32Op.of_value v))
  | TruncSF64 -> o_fmap I64 (o_bind I64_convert.trunc_f64_s (F64Op.of_value v))
  | TruncUF64 -> o_fmap I64 (o_bind I64_convert.trunc_f64_u (F64Op.of_value v))
  | ReinterpretFloat -> o_fmap I64 (o_fmap I64_convert.reinterpret_f64 (F64Op.of_value v))
  | WrapI64 -> e_TypeError
