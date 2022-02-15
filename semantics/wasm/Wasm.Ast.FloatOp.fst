(**
AST representation of Float operations.

@summary AST for FloatOp.
*)
module Wasm.Ast.FloatOp

type unop =
  | Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt
type binop =
  | Add | Sub | Mul | Div | Min | Max | CopySign
type testop = | NoSuch (* empty *)
type relop =
  | Eq | Ne | Lt | Gt | Le | Ge
type cvtop =
  | ConvertSI32 | ConvertUI32 | ConvertSI64 | ConvertUI64
  | PromoteF32 | DemoteF64
  | ReinterpretInt
