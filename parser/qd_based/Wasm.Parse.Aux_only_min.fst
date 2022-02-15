module Wasm.Parse.Aux_only_min

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

noextract let aux_only_min_parser = LPI.parse_u32

noextract let aux_only_min_serializer = LPI.serialize_u32

let aux_only_min_bytesize (x:aux_only_min) : GTot nat = Seq.length (aux_only_min_serializer x)

let aux_only_min_bytesize_eq x = ()

let aux_only_min_parser32 = LS.parse32_u32

let aux_only_min_serializer32 = LS.serialize32_u32

let aux_only_min_size32 = LS.size32_u32

let aux_only_min_bytesize_eqn x = (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x)) == 4))

let aux_only_min_parser_serializer_eq _ = ()
