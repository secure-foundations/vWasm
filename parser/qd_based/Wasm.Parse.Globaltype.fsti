module Wasm.Parse.Globaltype

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
open Wasm.Parse.Mut

type globaltype = {
  t : valtype;
  m : mut;
}

inline_for_extraction noextract let globaltype_parser_kind = LP.strong_parser_kind 2 2 None

noextract val globaltype_parser: LP.parser globaltype_parser_kind globaltype

noextract val globaltype_serializer: LP.serializer globaltype_parser

noextract val globaltype_bytesize (x:globaltype) : GTot nat

noextract val globaltype_bytesize_eq (x:globaltype) : Lemma (globaltype_bytesize x == Seq.length (LP.serialize globaltype_serializer x))

val globaltype_parser32: LS.parser32 globaltype_parser

val globaltype_serializer32: LS.serializer32 globaltype_serializer

val globaltype_size32: LS.size32 globaltype_serializer

val globaltype_bytesize_eqn (x: globaltype) : Lemma (globaltype_bytesize x == (valtype_bytesize (x.t)) + (mut_bytesize (x.m))) [SMTPat (globaltype_bytesize x)]

