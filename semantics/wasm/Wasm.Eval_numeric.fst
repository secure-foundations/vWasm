/// WARNING: Indirection reduced by unfolding dispatch.

(**
Evaluation of numeric operations.

@summary Numeric eval.
*)
module Wasm.Eval_numeric

open Wasm.Optr
open Wasm.Types
open Wasm.Values

module Ast = Wasm.Ast

(* Runtime type errors *)
let e_TypeError = Left "TypeError"

/// ####################
/// DECLARATIONS
/// ####################
val eval_unop: Ast.unop -> value -> Tot (optr value)
val eval_binop: Ast.binop -> value -> value -> Tot (optr value)
val eval_testop: Ast.testop -> value -> Tot (optr bool)
val eval_relop: Ast.relop -> value -> value -> Tot (optr bool)
val eval_cvtop: Ast.cvtop -> value -> Tot (optr value)

module I32Op = Wasm.Eval_numeric.I32Op
module I64Op = Wasm.Eval_numeric.I64Op
module F32Op = Wasm.Eval_numeric.F32Op
module F64Op = Wasm.Eval_numeric.F64Op

(* The following are needed to avoid cirular dependencies, because
 * the cvtops depend on the defs in the type being converted from *)
module I32CvtOp = Wasm.Eval_numeric.I32CvtOp
module I64CvtOp = Wasm.Eval_numeric.I64CvtOp
module F32CvtOp = Wasm.Eval_numeric.F32CvtOp
module F64CvtOp = Wasm.Eval_numeric.F64CvtOp

/// ####################
/// DEFINITIONS
/// ####################
let eval_unop x v =
  match x with
  | I32 x' -> I32Op.unop x' v
  | I64 x' -> I64Op.unop x' v
  | F32 x' -> F32Op.unop x' v
  | F64 x' -> F64Op.unop x' v

let eval_binop x v1 v2 =
  match x with
  | I32 x' -> I32Op.binop x' v1 v2
  | I64 x' -> I64Op.binop x' v1 v2
  | F32 x' -> F32Op.binop x' v1 v2
  | F64 x' -> F64Op.binop x' v1 v2

let eval_testop x v =
  match x with
  | I32 x' -> I32Op.testop x' v
  | I64 x' -> I64Op.testop x' v
  | F32 x' -> F32Op.testop x' v
  | F64 x' -> F64Op.testop x' v

let eval_relop x v1 v2 =
  match x with
  | I32 x' -> I32Op.relop x' v1 v2
  | I64 x' -> I64Op.relop x' v1 v2
  | F32 x' -> F32Op.relop x' v1 v2
  | F64 x' -> F64Op.relop x' v1 v2

let eval_cvtop x v =
  match x with
  | I32 x' -> I32CvtOp.cvtop_ x' v
  | I64 x' -> I64CvtOp.cvtop_ x' v
  | F32 x' -> F32CvtOp.cvtop_ x' v
  | F64 x' -> F64CvtOp.cvtop_ x' v
