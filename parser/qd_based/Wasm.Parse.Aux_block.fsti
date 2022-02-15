module Wasm.Parse.Aux_block

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

open Wasm.Parse.Blocktype

type aux_block = blocktype

inline_for_extraction noextract let aux_block_parser_kind = LP.strong_parser_kind 1 1 None

noextract val aux_block_parser: LP.parser aux_block_parser_kind aux_block

noextract val aux_block_serializer: LP.serializer aux_block_parser

noextract val aux_block_bytesize (x:aux_block) : GTot nat

noextract val aux_block_bytesize_eq (x:aux_block) : Lemma (aux_block_bytesize x == Seq.length (LP.serialize aux_block_serializer x))

val aux_block_parser32: LS.parser32 aux_block_parser

val aux_block_serializer32: LS.serializer32 aux_block_serializer

val aux_block_size32: LS.size32 aux_block_serializer

val aux_block_bytesize_eqn (x: aux_block) : Lemma (aux_block_bytesize x == (blocktype_bytesize (x))) [SMTPat (aux_block_bytesize x)]

val aux_block_parser_serializer_eq (_: unit) : Lemma (aux_block_parser == blocktype_parser /\ aux_block_serializer == blocktype_serializer)

