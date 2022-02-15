module Wasm.Parse.Funcsec_cont

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

let funcsec_cont_parser =
  LP.parse_bounded_vldata 0 16777215 aux_vectypeidx_parser

let funcsec_cont_serializer =
  LP.serialize_bounded_vldata 0 16777215 aux_vectypeidx_serializer

let funcsec_cont_bytesize (x:funcsec_cont) : GTot nat = Seq.length (funcsec_cont_serializer x)

let funcsec_cont_bytesize_eq x = ()

let funcsec_cont_parser32 =
  LS.parse32_bounded_vldata 0 0ul 16777215 16777215ul aux_vectypeidx_parser32

let funcsec_cont_serializer32 =
  LS.serialize32_bounded_vldata 0 16777215 aux_vectypeidx_serializer32

let funcsec_cont_size32 =
  LS.size32_bounded_vldata 0 16777215 aux_vectypeidx_size32 3ul

let funcsec_cont_bytesize_eqn x =
  (aux_vectypeidx_bytesize_eq (x))

