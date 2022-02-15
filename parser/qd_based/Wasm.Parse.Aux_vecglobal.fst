module Wasm.Parse.Aux_vecglobal

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

let aux_vecglobal_parser' = LP.parse_vclist 0 16383 LPI.parse_u32 global_parser

private let kind_eq : squash (LP.get_parser_kind aux_vecglobal_parser' == aux_vecglobal_parser_kind) = _ by (FStar.Tactics.trefl ())

private let type_eq : squash (aux_vecglobal == LP.vlarray global 0 16383) = _ by (FStar.Tactics.trefl ())

let aux_vecglobal_parser = aux_vecglobal_parser'
let aux_vecglobal_serializer = LP.serialize_vclist 0 16383 LPI.serialize_u32 global_serializer

let aux_vecglobal_bytesize (x:aux_vecglobal) : GTot nat = Seq.length (aux_vecglobal_serializer x)

let aux_vecglobal_bytesize_eq x = ()

let aux_vecglobal_parser32 = LS.parse32_vclist 0ul 16383ul LS.parse32_u32 global_parser32

let aux_vecglobal_serializer32 =
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 0 16383 (LP.get_parser_kind LPI.parse_u32) (LP.get_parser_kind global_parser)) in
  LS.serialize32_vclist 0 16383 LS.serialize32_u32 global_serializer32

let aux_vecglobal_size32 =
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 0 16383 (LP.get_parser_kind LPI.parse_u32) (LP.get_parser_kind global_parser)) in
  LS.size32_vclist 0 16383 LS.size32_u32 global_size32

