(**
Evaluation of I64 operations.

@summary I64Op eval.
*)
module Wasm.Eval_numeric.I64Op

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.IntOp

module I64 = Wasm.I64

let e_TypeError = Left "TypeError"

let to_value (i: I64.t) = I64 i
let of_value x =
  match x with
  | I64 i -> Right i
  | _ -> e_TypeError

let unop op v =
  let f = match op with
    | Clz -> o_wrap I64.clz
    | Ctz -> o_wrap I64.ctz
    | Popcnt -> o_wrap I64.popcnt
  in o_fmap to_value (o_bind f (of_value v))

let binop op v1 v2=
  let f = match op with
    | Add -> o_wrap2 I64.add
    | Sub -> o_wrap2 I64.sub
    | Mul -> o_wrap2 I64.mul
    | DivS -> I64.div_s
    | DivU -> I64.div_u
    | RemS -> I64.rem_s
    | RemU -> I64.rem_u
    | And -> o_wrap2 I64.and_
    | Or -> o_wrap2 I64.or_
    | Xor -> o_wrap2 I64.xor
    | Shl -> o_wrap2 I64.shl
    | ShrU -> o_wrap2 I64.shr_u
    | ShrS -> o_wrap2 I64.shr_s
    | Rotl -> o_wrap2 I64.rotl
    | Rotr -> o_wrap2 I64.rotr
  in o_fmap to_value (o_bind2 f (of_value v1) (of_value v2))

let testop op v =
  let f = match op with
    | Eqz -> I64.eqz
  in o_fmap f (of_value v)

let relop op v1 v2=
  let f = match op with
    | Eq -> I64.eq
    | Ne -> I64.ne
    | LtS -> I64.lt_s
    | LtU -> I64.lt_u
    | LeS -> I64.le_s
    | LeU -> I64.le_u
    | GtS -> I64.gt_s
    | GtU -> I64.gt_u
    | GeS -> I64.ge_s
    | GeU -> I64.ge_u
  in o_fmap2 f (of_value v1) (of_value v2)
