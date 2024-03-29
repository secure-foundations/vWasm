module Wasm.Parse.Elemsec

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

open Wasm.Parse.Aux_section_const9
open Wasm.Parse.Aux_constbyte0
open Wasm.Parse.Aux_vecelem

(* Type of field cont*)
include Wasm.Parse.Elemsec_cont

type elemsec = {
  n : aux_section_const9;
  aux_ignore_byte : aux_constbyte0;
  cont : elemsec_cont;
}

inline_for_extraction noextract let elemsec_parser_kind = LP.strong_parser_kind 9 16777220 None

noextract val elemsec_parser: LP.parser elemsec_parser_kind elemsec

noextract val elemsec_serializer: LP.serializer elemsec_parser

noextract val elemsec_bytesize (x:elemsec) : GTot nat

noextract val elemsec_bytesize_eq (x:elemsec) : Lemma (elemsec_bytesize x == Seq.length (LP.serialize elemsec_serializer x))

val elemsec_parser32: LS.parser32 elemsec_parser

val elemsec_serializer32: LS.serializer32 elemsec_serializer

val elemsec_size32: LS.size32 elemsec_serializer

val elemsec_bytesize_eqn (x: elemsec) : Lemma (elemsec_bytesize x == (aux_section_const9_bytesize (x.n)) + (aux_constbyte0_bytesize (x.aux_ignore_byte)) + (elemsec_cont_bytesize (x.cont))) [SMTPat (elemsec_bytesize x)]

