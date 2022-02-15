(**
AST representation of Int operations

@summary AST for IntOp.
*)
module Wasm.Ast.IntOp

type unop =
  | Clz | Ctz | Popcnt
type binop =
  | Add | Sub | Mul | DivS | DivU | RemS | RemU
  | And | Or | Xor | Shl | ShrS | ShrU | Rotl | Rotr
type testop =
  | Eqz
type relop =
  | Eq | Ne | LtS | LtU | GtS | GtU | LeS | LeU | GeS | GeU
type cvtop =
  | ExtendSI32 | ExtendUI32 | WrapI64
  | TruncSF32 | TruncUF32 | TruncSF64 | TruncUF64
  | ReinterpretFloat
