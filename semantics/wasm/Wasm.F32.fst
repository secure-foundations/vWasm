(**
Wasm-compliant wrappers for F32 arithmetic.
TODO: Currently using t = float = list nat8, just so we can get floats to compile.

@summary F32 arithmetic.
*)
module Wasm.F32

open Wasm.Optr

open Words_s

/// ####################
/// DECLARATIONS
/// ####################

(* TODO: Temporary definitions to get floats to pass through. *)
type t = list nat8
type bytes = list nat8
type float = t

assume val pos_nan : t
assume val neg_nan : t
assume val of_float : float -> Tot t
assume val to_float : t -> Tot float
assume val of_string : string -> Tot (optr t)
assume val to_string : t -> Tot string

val of_bytes : bytes -> Tot t
val to_bytes : t -> Tot bytes

assume val add : t -> t -> Tot t
assume val sub : t -> t -> Tot t
assume val mul : t -> t -> Tot t
assume val div : t -> t -> Tot t
assume val sqrt : t -> Tot t
assume val min : t -> t -> Tot t
assume val max : t -> t -> Tot t
assume val ceil : t -> Tot t
assume val floor : t -> Tot t
assume val trunc : t -> Tot t
assume val nearest : t -> Tot t
assume val abs : t -> Tot t
assume val neg : t -> Tot t
assume val copysign : t -> t -> Tot t
assume val eq : t -> t -> Tot bool
assume val ne : t -> t -> Tot bool
assume val lt : t -> t -> Tot bool
assume val le : t -> t -> Tot bool
assume val gt : t -> t -> Tot bool
assume val ge : t -> t -> Tot bool
assume val zero : t

/// ####################
/// DEFINITIONS
/// ####################

(* TODO: Temporary definitions just to get floats to pass through *)
let of_bytes bs = bs
let to_bytes bs = bs
