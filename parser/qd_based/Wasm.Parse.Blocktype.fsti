module Wasm.Parse.Blocktype

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


type blocktype =
  | R_none
  | R_i32
  | R_i64
  | R_f32
  | R_f64

let string_of_blocktype = function
  | R_none -> "r_none"
  | R_i32 -> "r_i32"
  | R_i64 -> "r_i64"
  | R_f32 -> "r_f32"
  | R_f64 -> "r_f64"

inline_for_extraction noextract let blocktype_parser_kind = LP.strong_parser_kind 1 1 None

noextract val blocktype_parser: LP.parser blocktype_parser_kind blocktype

noextract val blocktype_serializer: LP.serializer blocktype_parser

noextract val blocktype_bytesize (x:blocktype) : GTot nat

noextract val blocktype_bytesize_eq (x:blocktype) : Lemma (blocktype_bytesize x == Seq.length (LP.serialize blocktype_serializer x))

val blocktype_parser32: LS.parser32 blocktype_parser

val blocktype_serializer32: LS.serializer32 blocktype_serializer

val blocktype_size32: LS.size32 blocktype_serializer

