module Wasm.Parse.Global

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

open Wasm.Parse.Globaltype
open Wasm.Parse.Constexpr

type global = {
  gt : globaltype;
  e : constexpr;
}

inline_for_extraction noextract let global_parser_kind = LP.strong_parser_kind 4 1027 None

noextract val global_parser: LP.parser global_parser_kind global

noextract val global_serializer: LP.serializer global_parser

noextract val global_bytesize (x:global) : GTot nat

noextract val global_bytesize_eq (x:global) : Lemma (global_bytesize x == Seq.length (LP.serialize global_serializer x))

val global_parser32: LS.parser32 global_parser

val global_serializer32: LS.serializer32 global_serializer

val global_size32: LS.size32 global_serializer

val global_bytesize_eqn (x: global) : Lemma (global_bytesize x == (globaltype_bytesize (x.gt)) + (constexpr_bytesize (x.e))) [SMTPat (global_bytesize x)]

