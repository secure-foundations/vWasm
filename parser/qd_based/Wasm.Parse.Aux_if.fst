module Wasm.Parse.Aux_if

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

noextract let aux_if_parser = blocktype_parser

noextract let aux_if_serializer = blocktype_serializer

let aux_if_bytesize (x:aux_if) : GTot nat = Seq.length (aux_if_serializer x)

let aux_if_bytesize_eq x = ()

let aux_if_parser32 = blocktype_parser32

let aux_if_serializer32 = blocktype_serializer32

let aux_if_size32 = blocktype_size32

let aux_if_bytesize_eqn x = (blocktype_bytesize_eq (x))

let aux_if_parser_serializer_eq _ = ()

