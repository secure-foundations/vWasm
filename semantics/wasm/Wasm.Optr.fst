(**
Error monad with some helper functions.

@summary Error monad.
*)
module Wasm.Optr

type optr 'a =
  | Left: v:string -> optr 'a
  | Right: v:'a -> optr 'a

let left s = Left s
let right x = Right x

let extr x def =
  match x with
  | Right x' -> x'
  | Left _ -> def

let o_fmap f x =
  match x with
  | Left x' -> Left x'
  | Right x' -> Right (f x')

let o_fmap2 f x y =
  match x, y with
  | Left x', _ -> Left x'
  | _, Left y' -> Left y'
  | Right x', Right y' -> Right (f x' y')

let o_bind f x =
  match x with
  | Left x' -> Left x'
  | Right x' -> f x'

let o_bind2 f x y =
  match x, y with
  | Left x', _ -> Left x'
  | _, Left y' -> Left y'
  | Right x', Right y' -> f x' y'

let o_wrap f = fun x -> Right (f x)
let o_wrap2 f = fun x y -> Right (f x y)
