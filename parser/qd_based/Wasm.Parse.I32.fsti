module Wasm.Parse.I32

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


type i32 = U32.t

inline_for_extraction noextract let i32_parser_kind = LP.strong_parser_kind 4 4 (Some LP.ParserKindMetadataTotal)

noextract val i32_parser: LP.parser i32_parser_kind i32

noextract val i32_serializer: LP.serializer i32_parser

noextract val i32_bytesize (x:i32) : GTot nat

noextract val i32_bytesize_eq (x:i32) : Lemma (i32_bytesize x == Seq.length (LP.serialize i32_serializer x))

val i32_parser32: LS.parser32 i32_parser

val i32_serializer32: LS.serializer32 i32_serializer

val i32_size32: LS.size32 i32_serializer

val i32_bytesize_eqn (x: i32) : Lemma (i32_bytesize x == 4) [SMTPat (i32_bytesize x)]

val i32_parser_serializer_eq (_: unit) : Lemma (i32_parser == LPI.parse_u32 /\ i32_serializer == LPI.serialize_u32)

