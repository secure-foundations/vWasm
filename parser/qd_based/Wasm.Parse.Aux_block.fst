module Wasm.Parse.Aux_block

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

noextract let aux_block_parser = blocktype_parser

noextract let aux_block_serializer = blocktype_serializer

let aux_block_bytesize (x:aux_block) : GTot nat = Seq.length (aux_block_serializer x)

let aux_block_bytesize_eq x = ()

let aux_block_parser32 = blocktype_parser32

let aux_block_serializer32 = blocktype_serializer32

let aux_block_size32 = blocktype_size32

let aux_block_bytesize_eqn x = (blocktype_bytesize_eq (x))

let aux_block_parser_serializer_eq _ = ()

