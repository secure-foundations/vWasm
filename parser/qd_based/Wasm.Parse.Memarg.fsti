module Wasm.Parse.Memarg

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


type memarg = {
  align : U32.t;
  offset : U32.t;
}

inline_for_extraction noextract let memarg_parser_kind = LP.strong_parser_kind 8 8 (Some LP.ParserKindMetadataTotal)

noextract val memarg_parser: LP.parser memarg_parser_kind memarg

noextract val memarg_serializer: LP.serializer memarg_parser

noextract val memarg_bytesize (x:memarg) : GTot nat

noextract val memarg_bytesize_eq (x:memarg) : Lemma (memarg_bytesize x == Seq.length (LP.serialize memarg_serializer x))

val memarg_parser32: LS.parser32 memarg_parser

val memarg_serializer32: LS.serializer32 memarg_serializer

val memarg_size32: LS.size32 memarg_serializer

val memarg_bytesize_eqn (x: memarg) : Lemma (memarg_bytesize x == 4 + 4) [SMTPat (memarg_bytesize x)]

