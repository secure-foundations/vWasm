module Wasm.Parse.Uint64

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


type uint64 = {
  high : U32.t;
  low : U32.t;
}

inline_for_extraction noextract let uint64_parser_kind = LP.strong_parser_kind 8 8 (Some LP.ParserKindMetadataTotal)

noextract val uint64_parser: LP.parser uint64_parser_kind uint64

noextract val uint64_serializer: LP.serializer uint64_parser

noextract val uint64_bytesize (x:uint64) : GTot nat

noextract val uint64_bytesize_eq (x:uint64) : Lemma (uint64_bytesize x == Seq.length (LP.serialize uint64_serializer x))

val uint64_parser32: LS.parser32 uint64_parser

val uint64_serializer32: LS.serializer32 uint64_serializer

val uint64_size32: LS.size32 uint64_serializer

val uint64_bytesize_eqn (x: uint64) : Lemma (uint64_bytesize x == 4 + 4) [SMTPat (uint64_bytesize x)]

