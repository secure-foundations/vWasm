(**
Numeric errors.

@summary Numeric errors.
*)
module Wasm.Numeric_error

open Wasm.Optr

let e_IntegerDivideByZero = Left "IntegerDivideByZero"
let e_IntegerOverflow = Left "IntegerOverflow"
