module Wasm.Parse.Aux_veccode

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

let aux_veccode_parser' = LP.parse_vclist 0 2047 LPI.parse_u32 code_parser

private let kind_eq : squash (LP.get_parser_kind aux_veccode_parser' == aux_veccode_parser_kind) = _ by (FStar.Tactics.trefl ())

private let type_eq : squash (aux_veccode == LP.vlarray code 0 2047) = _ by (FStar.Tactics.trefl ())

let aux_veccode_parser = aux_veccode_parser'
let aux_veccode_serializer = LP.serialize_vclist 0 2047 LPI.serialize_u32 code_serializer

let aux_veccode_bytesize (x:aux_veccode) : GTot nat = Seq.length (aux_veccode_serializer x)

let aux_veccode_bytesize_eq x = ()

let aux_veccode_parser32 = LS.parse32_vclist 0ul 2047ul LS.parse32_u32 code_parser32

let aux_veccode_serializer32 =
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 0 2047 (LP.get_parser_kind LPI.parse_u32) (LP.get_parser_kind code_parser)) in
  LS.serialize32_vclist 0 2047 LS.serialize32_u32 code_serializer32

let aux_veccode_size32 =
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 0 2047 (LP.get_parser_kind LPI.parse_u32) (LP.get_parser_kind code_parser)) in
  LS.size32_vclist 0 2047 LS.size32_u32 code_size32

