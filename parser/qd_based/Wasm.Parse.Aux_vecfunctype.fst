module Wasm.Parse.Aux_vecfunctype

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

let aux_vecfunctype_parser' = LP.parse_vclist 0 8191 LPI.parse_u32 functype_parser

private let kind_eq : squash (LP.get_parser_kind aux_vecfunctype_parser' == aux_vecfunctype_parser_kind) = _ by (FStar.Tactics.trefl ())

private let type_eq : squash (aux_vecfunctype == LP.vlarray functype 0 8191) = _ by (FStar.Tactics.trefl ())

let aux_vecfunctype_parser = aux_vecfunctype_parser'
let aux_vecfunctype_serializer = LP.serialize_vclist 0 8191 LPI.serialize_u32 functype_serializer

let aux_vecfunctype_bytesize (x:aux_vecfunctype) : GTot nat = Seq.length (aux_vecfunctype_serializer x)

let aux_vecfunctype_bytesize_eq x = ()

let aux_vecfunctype_parser32 = LS.parse32_vclist 0ul 8191ul LS.parse32_u32 functype_parser32

let aux_vecfunctype_serializer32 =
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 0 8191 (LP.get_parser_kind LPI.parse_u32) (LP.get_parser_kind functype_parser)) in
  LS.serialize32_vclist 0 8191 LS.serialize32_u32 functype_serializer32

let aux_vecfunctype_size32 =
  [@inline_let] let _ = assert_norm (LS.serialize32_vclist_precond 0 8191 (LP.get_parser_kind LPI.parse_u32) (LP.get_parser_kind functype_parser)) in
  LS.size32_vclist 0 8191 LS.size32_u32 functype_size32

