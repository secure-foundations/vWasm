(**
Evaluation of I32 operations.

@summary I32Op eval.
*)
module Wasm.Eval_numeric.I32Op

open Wasm.Optr
open Wasm.Types
open Wasm.Values
open Wasm.Ast.IntOp

module I32 = Wasm.I32

let e_TypeError = Left "TypeError"

let to_value (i: I32.t) = I32 i
let of_value x =
  match x with
  | I32 i -> Right i
  | _ -> e_TypeError

let unop op v =
  let f = match op with
    | Clz -> o_wrap I32.clz
    | Ctz -> o_wrap I32.ctz
    | Popcnt -> o_wrap I32.popcnt
  in o_fmap to_value (o_bind f (of_value v))

let binop op v1 v2 =
  let f = match op with
    | Add -> o_wrap2 I32.add
    | Sub -> o_wrap2 I32.sub
    | Mul -> o_wrap2 I32.mul
    | DivS -> I32.div_s
    | DivU -> I32.div_u
    | RemS -> I32.rem_s
    | RemU -> I32.rem_u
    | And -> o_wrap2 I32.and_
    | Or -> o_wrap2 I32.or_
    | Xor -> o_wrap2 I32.xor
    | Shl -> o_wrap2 I32.shl
    | ShrU -> o_wrap2 I32.shr_u
    | ShrS -> o_wrap2 I32.shr_s
    | Rotl -> o_wrap2 I32.rotl
    | Rotr -> o_wrap2 I32.rotr
  in o_fmap to_value (o_bind2 f (of_value v1) (of_value v2))

let testop op v =
  let f = match op with
    | Eqz -> I32.eqz
  in o_fmap f (of_value v)

let relop op v1 v2=
  let f = match op with
    | Eq -> I32.eq
    | Ne -> I32.ne
    | LtS -> I32.lt_s
    | LtU -> I32.lt_u
    | LeS -> I32.le_s
    | LeU -> I32.le_u
    | GtS -> I32.gt_s
    | GtU -> I32.gt_u
    | GeS -> I32.ge_s
    | GeU -> I32.ge_u
  in o_fmap2 f (of_value v1) (of_value v2)
