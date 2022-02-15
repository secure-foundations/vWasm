module Wasm.Parse.Aux_vecvaltype

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

open Wasm.Parse.Valtype

inline_for_extraction noextract let min_count = 0
inline_for_extraction noextract let max_count = 4095
type aux_vecvaltype = l:list valtype{0 <= L.length l /\ L.length l <= 4095}

inline_for_extraction noextract let aux_vecvaltype_parser_kind = LP.strong_parser_kind 4 4099 None

noextract val aux_vecvaltype_parser: LP.parser aux_vecvaltype_parser_kind aux_vecvaltype

noextract val aux_vecvaltype_serializer: LP.serializer aux_vecvaltype_parser

noextract val aux_vecvaltype_bytesize (x:aux_vecvaltype) : GTot nat

noextract val aux_vecvaltype_bytesize_eq (x:aux_vecvaltype) : Lemma (aux_vecvaltype_bytesize x == Seq.length (LP.serialize aux_vecvaltype_serializer x))

val aux_vecvaltype_parser32: LS.parser32 aux_vecvaltype_parser

val aux_vecvaltype_serializer32: LS.serializer32 aux_vecvaltype_serializer

val aux_vecvaltype_size32: LS.size32 aux_vecvaltype_serializer

