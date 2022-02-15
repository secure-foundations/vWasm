(**
Representation of source locations in the AST.

@summary Source locations.
*)
module Wasm.Source

/// ####################
/// DECLARATIONS
/// ####################
type pos = {file: string; line: int; column: int}
type region = {left: pos; right: pos}
type phrase 'a = {at: region; it: 'a}

val no_pos: pos
val no_region: region

val string_of_pos: pos -> Tot string
val string_of_region: region -> Tot string

val op_At_At: 'a -> region -> phrase 'a

/// ####################
/// DEFINITIONS
/// ####################
(* Positions and regions *)
let no_pos = {file = ""; line = 0; column = 0}
let no_region = {left = no_pos; right = no_pos}

let string_of_pos pos = ""
let string_of_region r = ""

let op_At_At x region = {it = x; at = region}
