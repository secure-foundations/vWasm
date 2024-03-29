module Wasm.Parse.Mem

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

open Wasm.Parse.Memtype

type mem = memtype

inline_for_extraction noextract let mem_parser_kind = LP.strong_parser_kind 5 9 None

noextract val mem_parser: LP.parser mem_parser_kind mem

noextract val mem_serializer: LP.serializer mem_parser

noextract val mem_bytesize (x:mem) : GTot nat

noextract val mem_bytesize_eq (x:mem) : Lemma (mem_bytesize x == Seq.length (LP.serialize mem_serializer x))

val mem_parser32: LS.parser32 mem_parser

val mem_serializer32: LS.serializer32 mem_serializer

val mem_size32: LS.size32 mem_serializer

val mem_bytesize_eqn (x: mem) : Lemma (mem_bytesize x == (memtype_bytesize (x))) [SMTPat (mem_bytesize x)]

val mem_parser_serializer_eq (_: unit) : Lemma (mem_parser == memtype_parser /\ mem_serializer == memtype_serializer)

