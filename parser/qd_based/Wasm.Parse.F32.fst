module Wasm.Parse.F32

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec
module LS = LowParse.SLow
module LPI = LowParse.Spec.AllIntegers
module L = FStar.List.Tot
module BY = FStar.Bytes

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

noextract let f32_parser = LP.parse_flbytes 4

noextract let f32_serializer = LP.serialize_flbytes 4

let f32_bytesize (x:f32) : GTot nat = Seq.length (f32_serializer x)

let f32_bytesize_eq x = ()

let f32_parser32 = LS.parse32_flbytes 4 4ul

let f32_serializer32 = LS.serialize32_flbytes 4

let f32_size32 = LS.size32_constant f32_serializer 4ul ()

let f32_bytesize_eqn x = ()

