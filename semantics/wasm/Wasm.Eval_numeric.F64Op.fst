(**
Evaluation of F64 operations.

@summary F64Op eval.
*)
module Wasm.Eval_numeric.F64Op

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.FloatOp

module F64 = Wasm.F64

let e_TypeError = Left "TypeError"

let to_value (i: F64.t) = F64 i
let of_value x =
  match x with
  | F64 i -> Right i
  | _ -> e_TypeError

let unop op v =
  let f = match op with
    | Neg -> F64.neg
    | Abs -> F64.abs
    | Sqrt -> F64.sqrt
    | Ceil -> F64.ceil
    | Floor -> F64.floor
    | Trunc -> F64.trunc
    | Nearest -> F64.nearest
  in o_fmap to_value (o_fmap f (of_value v))

let binop op v1 v2 =
  let f = match op with
    | Add -> F64.add
    | Sub -> F64.sub
    | Mul -> F64.mul
    | Div -> F64.div
    | Min -> F64.min
    | Max -> F64.max
    | CopySign -> F64.copysign
  in o_fmap to_value (o_fmap2 f (of_value v1) (of_value v2))

(* Maybe change this error in future *)
let testop op v: optr bool = e_TypeError

let relop op v1 v2 =
  let f = match op with
    | Eq -> F64.eq
    | Ne -> F64.ne
    | Lt -> F64.lt
    | Le -> F64.le
    | Gt -> F64.gt
    | Ge -> F64.ge
  in o_fmap2 f (of_value v1) (of_value v2)
