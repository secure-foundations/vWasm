/// WARNING:
/// - Globals store refs to their contents in the OCaml implementation.
///   Here we just store the contents and do a functional update.

(**
Representation of an instantiation of a global.

@summary Global instances.
*)
module Wasm.Global

open Wasm.Optr

open Wasm.Types
open Wasm.Values

module Values = Wasm.Values

/// ####################
/// DECLARATIONS
/// ####################
type global = {content: value; mut: mutability}
type t = global

val alloc : global_type -> value -> Tot (optr global)
val type_of : global -> Tot (global_type)

val load : global -> Tot value
val store : global -> value -> Tot (optr global)

/// ####################
/// DEFINITIONS
/// ####################
let e_Type = Left "Type"
let e_NotMutable = Left "NotMutable"

let alloc (GlobalType (t, mut)) v =
  if type_of v <> t then
    e_Type
  else
    Right ({content = v; mut = mut})

let type_of glob =
  GlobalType (Values.type_of glob.content, glob.mut)

let load glob = glob.content

let store glob v =
  if glob.mut <> Mutable then
    e_NotMutable
  else (
    if Values.type_of v <> Values.type_of glob.content then
      e_Type
    else
      Right ({glob with content = v})
  )
