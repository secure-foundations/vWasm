(**
Evaluation of F32 operations.

@summary F32Op eval.
*)
module Wasm.Eval_numeric.F32Op

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.FloatOp

module F32 = Wasm.F32

let e_TypeError = Left "TypeError"

let to_value (i: F32.t) = F32 i
let of_value x =
  match x with
  | F32 i -> Right i
  | _ -> e_TypeError

let unop op v =
  let f = match op with
    | Neg -> F32.neg
    | Abs -> F32.abs
    | Sqrt -> F32.sqrt
    | Ceil -> F32.ceil
    | Floor -> F32.floor
    | Trunc -> F32.trunc
    | Nearest -> F32.nearest
  in o_fmap to_value (o_fmap f (of_value v))

let binop op v1 v2 =
  let f = match op with
    | Add -> F32.add
    | Sub -> F32.sub
    | Mul -> F32.mul
    | Div -> F32.div
    | Min -> F32.min
    | Max -> F32.max
    | CopySign -> F32.copysign
  in o_fmap to_value (o_fmap2 f (of_value v1) (of_value v2))

(* Maybe change this error in future *)
let testop op v: optr bool = e_TypeError

let relop op v1 v2 =
  let f = match op with
    | Eq -> F32.eq
    | Ne -> F32.ne
    | Lt -> F32.lt
    | Le -> F32.le
    | Gt -> F32.gt
    | Ge -> F32.ge
  in o_fmap2 f (of_value v1) (of_value v2)
