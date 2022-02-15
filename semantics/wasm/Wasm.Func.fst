/// WARNING:
/// - HostFuncs need to be considered more carefully in future.
/// - AstFuncs kept a reference back to the original module instance
///   (the inst type). Instead, we just keep an integer index into
///   an array of module instances.

(**
Representation of an instantiation of a function.

@summary Func instances.
*)
module Wasm.Func

open Wasm.Types
open Wasm.Values

/// ####################
/// DECLARATIONS
/// ####################
noeq type func inst =
  | AstFunc of func_type * inst * Wasm.Ast.func
  | HostFunc of func_type * (list value -> list value)
type t inst = func inst

val alloc : func_type -> 'inst -> Wasm.Ast.func -> Tot (func 'inst)
val alloc_host : func_type -> (list value -> list value) -> Tot (func 'inst)
val type_of : func 'inst -> Tot func_type

/// ####################
/// DEFINITIONS
/// ####################
let alloc ft inst f = AstFunc (ft, inst, f)
let alloc_host ft f = HostFunc (ft, f)

let type_of f =
  match f with
  | AstFunc (ft, _, _) -> ft
  | HostFunc (ft, _) -> ft
