module Wasm.Parse.Labelidx

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

noextract let labelidx_parser = LPI.parse_u32

noextract let labelidx_serializer = LPI.serialize_u32

let labelidx_bytesize (x:labelidx) : GTot nat = Seq.length (labelidx_serializer x)

let labelidx_bytesize_eq x = ()

let labelidx_parser32 = LS.parse32_u32

let labelidx_serializer32 = LS.serialize32_u32

let labelidx_size32 = LS.size32_u32

let labelidx_bytesize_eqn x = (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x)) == 4))

let labelidx_parser_serializer_eq _ = ()

