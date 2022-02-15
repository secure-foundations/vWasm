module Wasm.Parse.Aux_vecbyte

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
inline_for_extraction noextract let max_count = 262143
type aux_vecbyte = l:list U8.t{0 <= L.length l /\ L.length l <= 262143}

inline_for_extraction noextract let aux_vecbyte_parser_kind = LP.strong_parser_kind 4 262147 None

noextract val aux_vecbyte_parser: LP.parser aux_vecbyte_parser_kind aux_vecbyte

noextract val aux_vecbyte_serializer: LP.serializer aux_vecbyte_parser

noextract val aux_vecbyte_bytesize (x:aux_vecbyte) : GTot nat

noextract val aux_vecbyte_bytesize_eq (x:aux_vecbyte) : Lemma (aux_vecbyte_bytesize x == Seq.length (LP.serialize aux_vecbyte_serializer x))

val aux_vecbyte_parser32: LS.parser32 aux_vecbyte_parser

val aux_vecbyte_serializer32: LS.serializer32 aux_vecbyte_serializer

val aux_vecbyte_size32: LS.size32 aux_vecbyte_serializer

