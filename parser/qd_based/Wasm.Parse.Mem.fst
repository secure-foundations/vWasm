module Wasm.Parse.Mem

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

noextract let mem_parser = memtype_parser

noextract let mem_serializer = memtype_serializer

let mem_bytesize (x:mem) : GTot nat = Seq.length (mem_serializer x)

let mem_bytesize_eq x = ()

let mem_parser32 = memtype_parser32

let mem_serializer32 = memtype_serializer32

let mem_size32 = memtype_size32

let mem_bytesize_eqn x = (memtype_bytesize_eq (x))

let mem_parser_serializer_eq _ = ()

