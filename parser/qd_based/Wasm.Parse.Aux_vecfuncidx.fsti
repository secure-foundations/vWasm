module Wasm.Parse.Aux_vecfuncidx

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

open Wasm.Parse.Funcidx

inline_for_extraction noextract let min_count = 0
inline_for_extraction noextract let max_count = 1023
type aux_vecfuncidx = l:list funcidx{0 <= L.length l /\ L.length l <= 1023}

inline_for_extraction noextract let aux_vecfuncidx_parser_kind = LP.strong_parser_kind 4 4096 None

noextract val aux_vecfuncidx_parser: LP.parser aux_vecfuncidx_parser_kind aux_vecfuncidx

noextract val aux_vecfuncidx_serializer: LP.serializer aux_vecfuncidx_parser

noextract val aux_vecfuncidx_bytesize (x:aux_vecfuncidx) : GTot nat

noextract val aux_vecfuncidx_bytesize_eq (x:aux_vecfuncidx) : Lemma (aux_vecfuncidx_bytesize x == Seq.length (LP.serialize aux_vecfuncidx_serializer x))

val aux_vecfuncidx_parser32: LS.parser32 aux_vecfuncidx_parser

val aux_vecfuncidx_serializer32: LS.serializer32 aux_vecfuncidx_serializer

val aux_vecfuncidx_size32: LS.size32 aux_vecfuncidx_serializer

