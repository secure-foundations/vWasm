module Wasm.Parse.Globalidx

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


type globalidx = U32.t

inline_for_extraction noextract let globalidx_parser_kind = LP.strong_parser_kind 4 4 (Some LP.ParserKindMetadataTotal)

noextract val globalidx_parser: LP.parser globalidx_parser_kind globalidx

noextract val globalidx_serializer: LP.serializer globalidx_parser

noextract val globalidx_bytesize (x:globalidx) : GTot nat

noextract val globalidx_bytesize_eq (x:globalidx) : Lemma (globalidx_bytesize x == Seq.length (LP.serialize globalidx_serializer x))

val globalidx_parser32: LS.parser32 globalidx_parser

val globalidx_serializer32: LS.serializer32 globalidx_serializer

val globalidx_size32: LS.size32 globalidx_serializer

val globalidx_bytesize_eqn (x: globalidx) : Lemma (globalidx_bytesize x == 4) [SMTPat (globalidx_bytesize x)]

val globalidx_parser_serializer_eq (_: unit) : Lemma (globalidx_parser == LPI.parse_u32 /\ globalidx_serializer == LPI.serialize_u32)
