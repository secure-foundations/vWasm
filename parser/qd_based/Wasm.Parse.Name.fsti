module Wasm.Parse.Name

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


inline_for_extraction noextract let min_count = 0
inline_for_extraction noextract let max_count = 255
type name = l:list U8.t{0 <= L.length l /\ L.length l <= 255}

inline_for_extraction noextract let name_parser_kind = LP.strong_parser_kind 4 259 None

noextract val name_parser: LP.parser name_parser_kind name

noextract val name_serializer: LP.serializer name_parser

noextract val name_bytesize (x:name) : GTot nat

noextract val name_bytesize_eq (x:name) : Lemma (name_bytesize x == Seq.length (LP.serialize name_serializer x))

val name_parser32: LS.parser32 name_parser

val name_serializer32: LS.serializer32 name_serializer

val name_size32: LS.size32 name_serializer
