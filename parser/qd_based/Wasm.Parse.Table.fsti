module Wasm.Parse.Table

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

open Wasm.Parse.Tabletype

type table = tabletype

inline_for_extraction noextract let table_parser_kind = LP.strong_parser_kind 6 10 None

noextract val table_parser: LP.parser table_parser_kind table

noextract val table_serializer: LP.serializer table_parser

noextract val table_bytesize (x:table) : GTot nat

noextract val table_bytesize_eq (x:table) : Lemma (table_bytesize x == Seq.length (LP.serialize table_serializer x))

val table_parser32: LS.parser32 table_parser

val table_serializer32: LS.serializer32 table_serializer

val table_size32: LS.size32 table_serializer

val table_bytesize_eqn (x: table) : Lemma (table_bytesize x == (tabletype_bytesize (x))) [SMTPat (table_bytesize x)]

val table_parser_serializer_eq (_: unit) : Lemma (table_parser == tabletype_parser /\ table_serializer == tabletype_serializer)

