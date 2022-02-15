module Wasm.Parse.Aux_vecelem

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

open Wasm.Parse.Elem

inline_for_extraction noextract let min_count = 0
inline_for_extraction noextract let max_count = 16383
type aux_vecelem = l:list elem{0 <= L.length l /\ L.length l <= 16383}

inline_for_extraction noextract let aux_vecelem_parser_kind = LP.strong_parser_kind 4 83962879 None

noextract val aux_vecelem_parser: LP.parser aux_vecelem_parser_kind aux_vecelem

noextract val aux_vecelem_serializer: LP.serializer aux_vecelem_parser

noextract val aux_vecelem_bytesize (x:aux_vecelem) : GTot nat

noextract val aux_vecelem_bytesize_eq (x:aux_vecelem) : Lemma (aux_vecelem_bytesize x == Seq.length (LP.serialize aux_vecelem_serializer x))

val aux_vecelem_parser32: LS.parser32 aux_vecelem_parser

val aux_vecelem_serializer32: LS.serializer32 aux_vecelem_serializer

val aux_vecelem_size32: LS.size32 aux_vecelem_serializer

