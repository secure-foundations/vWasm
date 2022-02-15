/// WARNING:
/// - In implementing shifts my understanding of the F* library is that the
///   unsigned int shifts are unsigned (not signed) and that the signed int
///   ones are signed.

(**
Wasm-compliant wrappers for I32 arithmetic.

@summary I32 arithmetic.
*)
module Wasm.I32

open FStar.UInt
open FStar.UInt32

open Wasm.Optr

open Words_s

module Numeric_error = Wasm.Numeric_error

#reset-options "--z3cliopt smt.arith.nl=true"

/// ####################
/// DECLARATIONS
/// ####################
unfold let n = 32
let bitwidth = 32

type t = UInt32.t
type bytes = (l: list nat8{List.Tot.length l = 4})

val of_bytes: bytes -> Tot t
val to_bytes: t -> Tot bytes

val zero: t

val add: t -> t -> Tot t
val sub: t -> t -> Tot t
val mul: t -> t -> Tot t
val div_s: t -> t -> Tot (optr t)
val div_u: t -> t -> Tot (optr t)
val rem_s: t -> t -> Tot (optr t)
val rem_u: t -> t -> Tot (optr t)
val and_: t -> t -> Tot t
val or_: t -> t -> Tot t
val xor: t -> t -> Tot t
val shl: t -> t -> Tot t
val shr_s: t -> t -> Tot t
val shr_u: t -> t -> Tot t
val rotl: t -> t -> Tot t
val rotr: t -> t -> Tot t
val clz: t -> Tot t
val ctz: t -> Tot t
val popcnt: t -> Tot t
val eqz: t -> Tot bool
val eq: t -> t -> Tot bool
val ne: t -> t -> Tot bool
val lt_s: t -> t -> Tot bool
val lt_u: t -> t -> Tot bool
val le_s: t -> t -> Tot bool
val le_u: t -> t -> Tot bool
val gt_s: t -> t -> Tot bool
val gt_u: t -> t -> Tot bool
val ge_s: t -> t -> Tot bool
val ge_u: t -> t -> Tot bool

val of_int_s: int -> Tot t
val of_int_u: int -> Tot t

val to_int_s: t -> Tot int
val to_int_u: t -> Tot nat
val of_string_s: string -> Tot (optr t)
val of_string_u: string -> Tot (optr t)
val of_string: string -> Tot (optr t)
val to_string_s: t -> Tot string
val to_string_u: t -> Tot string

/// ####################
/// DEFINITIONS
/// ####################
let of_int_s x = uint_to_t (to_uint_t n x)
let of_int_u x = uint_to_t (to_uint_t n x)

let to_int_s x = Int.to_int_t n (v x)
let to_int_u x = v x

#push-options "--fuel 5"
let of_bytes bs =
  let Cons acc (b :: bs) = bs in
  let acc, (b :: bs) = acc + (b `op_Multiply` 0x100), bs in
  let acc, (b :: Nil) = acc + (b `op_Multiply` 0x10000), bs in
  let acc = acc + (b `op_Multiply` 0x1000000) in
  of_int_u acc
#pop-options

#push-options "--fuel 5"
let to_bytes x =
  let bs, acc = [], to_int_u x in
  let bs, acc = (acc `op_Modulus` 0x100) :: bs, acc `op_Division` 0x100 in
  let bs, acc = (acc `op_Modulus` 0x100) :: bs, acc `op_Division` 0x100 in
  let bs, acc = (acc `op_Modulus` 0x100) :: bs, acc `op_Division` 0x100 in
  acc :: bs
#pop-options

let zero = of_int_s 0
let one = of_int_s 1

(* add, sub, and mul are sign-agnostic and do not trap on overflow *)
let add x y = x +%^ y
let sub x y = x -%^ y
let mul x y = x *%^ y

private val to_s: t -> Tot Int32.t
let to_s x = Int32.int_to_t (Int.to_int_t n (v x))

private val fr_s: Int32.t -> Tot t
let fr_s x = uint_to_t (to_uint_t n (Int32.v x))

private let _v = Int32.v

(* result truncated towards zero *)
let div_s x y =
  let sx = to_s x in
  let sy = to_s y in
  if _v sy = 0 then
    Numeric_error.e_IntegerDivideByZero
  else if _v sx = Int.min_int n && _v sy = -1 then
    Numeric_error.e_IntegerOverflow
  else
    Right (fr_s (Int32.div sx sy))

let div_u x y =
  if y = zero then
    Numeric_error.e_IntegerDivideByZero
  else
    Right (x /^ y)

(* result has sign of dividend *)
let rem_s x y =
  let sx = to_s x in
  let sy = to_s y in
  if _v sy = 0 then
    Numeric_error.e_IntegerDivideByZero
  else if _v sx = Int.min_int n && _v sy = -1 then
    Numeric_error.e_IntegerOverflow
  else
    Right (fr_s (Int32.rem sx sy))

let rem_u x y =
  if y = zero then
    Numeric_error.e_IntegerDivideByZero
  else
    Right (x %^ y)

let and_ x y = x &^ y
let or_ x y = x |^ y
let xor x y = x ^^ y

(* WebAssembly's shifts mask the shift count according to bitwidth *)
let clamp_mask y = UInt32.uint_to_t (v (y %^ (of_int_s n)))

let shl x y =
  let y' = clamp_mask y in
  x <<^ y'

let shr_s x y =
  let y' = clamp_mask y in
  if y' = zero then x else (
    let x' = to_s x in
    let sign = if Int32.lt x' (Int32.int_to_t 0) then of_int_s (-1) else zero in
    let sign_shifted = sign <<^ (of_int_u n -^ y') in
    (x >>^ y') |^ sign_shifted
  )

let shr_u x y =
  let y' = clamp_mask y in
  x >>^ y'

(* We must mask the count to implement rotates via shifts. *)
let rotl x y =
  let y' = clamp_mask y in
  let ny' = UInt32.sub_mod (UInt32.uint_to_t n) y' in
  if UInt32.v y' = 0 then
    x
  else
    (x <<^ y') |^ (x >>^ ny')

let rotr x y =
  let y' = clamp_mask y in
  let ny' = UInt32.sub_mod (UInt32.uint_to_t n) y' in
  if UInt32.v y' = 0 then
    x
  else
    (x >>^ y') |^ (x <<^ ny')

(* TODO: Define clz, ctz, popcnt *)
(* clz is defined for all values, including all-zeros. *)
let clz x = admit()
let ctz x = admit()

let popcnt x = admit()

let eqz x = x = zero

let cmp_s x op y = op (to_s x) (to_s y)

let eq x y = x = y
let ne x y = x <> y
let lt_s x y = x <^ y
let lt_u x y = cmp_s x Int32.lt y
let le_s x y = x <=^ y
let le_u x y = cmp_s x Int32.lte y
let gt_s x y = x >^ y
let gt_u x y = cmp_s x Int32.gt y
let ge_s x y = x >=^ y
let ge_u x y = cmp_s x Int32.gte y

let of_string_s x = admit()
let of_string_u x = admit()
let of_string x = admit()

let to_string_s x = admit()
let to_string_u x = admit()
let to_string x = admit()
