module Wasm.Parse.Aux_vecglobal

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

open Wasm.Parse.Global

inline_for_extraction noextract let min_count = 0
inline_for_extraction noextract let max_count = 16383
type aux_vecglobal = l:list global{0 <= L.length l /\ L.length l <= 16383}

inline_for_extraction noextract let aux_vecglobal_parser_kind = LP.strong_parser_kind 4 16825345 None

noextract val aux_vecglobal_parser: LP.parser aux_vecglobal_parser_kind aux_vecglobal

noextract val aux_vecglobal_serializer: LP.serializer aux_vecglobal_parser

noextract val aux_vecglobal_bytesize (x:aux_vecglobal) : GTot nat

noextract val aux_vecglobal_bytesize_eq (x:aux_vecglobal) : Lemma (aux_vecglobal_bytesize x == Seq.length (LP.serialize aux_vecglobal_serializer x))

val aux_vecglobal_parser32: LS.parser32 aux_vecglobal_parser

val aux_vecglobal_serializer32: LS.serializer32 aux_vecglobal_serializer

val aux_vecglobal_size32: LS.size32 aux_vecglobal_serializer

