module Wasm.Parse.Aux_call_indirect

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec.Base
module LS = LowParse.SLow.Base
module LPI = LowParse.Spec.AllIntegers
module L = FStar.List.Tot
module BY = FStar.Bytes

open Wasm.Parse.Typeidx
open Wasm.Parse.Aux_constbyte0

type aux_call_indirect = {
  x : typeidx;
  z : aux_constbyte0;
}

inline_for_extraction noextract let aux_call_indirect_parser_kind = LP.strong_parser_kind 5 5 None

noextract val aux_call_indirect_parser: LP.parser aux_call_indirect_parser_kind aux_call_indirect

noextract val aux_call_indirect_serializer: LP.serializer aux_call_indirect_parser

noextract val aux_call_indirect_bytesize (x:aux_call_indirect) : GTot nat

noextract val aux_call_indirect_bytesize_eq (x:aux_call_indirect) : Lemma (aux_call_indirect_bytesize x == Seq.length (LP.serialize aux_call_indirect_serializer x))

val aux_call_indirect_parser32: LS.parser32 aux_call_indirect_parser

val aux_call_indirect_serializer32: LS.serializer32 aux_call_indirect_serializer

val aux_call_indirect_size32: LS.size32 aux_call_indirect_serializer

val aux_call_indirect_bytesize_eqn (x: aux_call_indirect) : Lemma (aux_call_indirect_bytesize x == (typeidx_bytesize (x.x)) + (aux_constbyte0_bytesize (x.z))) [SMTPat (aux_call_indirect_bytesize x)]

