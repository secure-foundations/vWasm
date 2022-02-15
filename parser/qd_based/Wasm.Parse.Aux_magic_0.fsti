module Wasm.Parse.Aux_magic_0

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


type aux_magic_0 =
  | Magic_0

let string_of_aux_magic_0 = function
  | Magic_0 -> "magic_0"

inline_for_extraction noextract let aux_magic_0_parser_kind = LP.strong_parser_kind 1 1 None

noextract val aux_magic_0_parser: LP.parser aux_magic_0_parser_kind aux_magic_0

noextract val aux_magic_0_serializer: LP.serializer aux_magic_0_parser

noextract val aux_magic_0_bytesize (x:aux_magic_0) : GTot nat

noextract val aux_magic_0_bytesize_eq (x:aux_magic_0) : Lemma (aux_magic_0_bytesize x == Seq.length (LP.serialize aux_magic_0_serializer x))

val aux_magic_0_parser32: LS.parser32 aux_magic_0_parser

val aux_magic_0_serializer32: LS.serializer32 aux_magic_0_serializer

val aux_magic_0_size32: LS.size32 aux_magic_0_serializer
