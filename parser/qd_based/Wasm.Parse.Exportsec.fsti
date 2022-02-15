module Wasm.Parse.Exportsec

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

open Wasm.Parse.Aux_section_const7
open Wasm.Parse.Aux_constbyte0
open Wasm.Parse.Aux_vecexport

(* Type of field cont*)
include Wasm.Parse.Exportsec_cont

type exportsec = {
  n : aux_section_const7;
  aux_ignore_byte : aux_constbyte0;
  cont : exportsec_cont;
}

inline_for_extraction noextract let exportsec_parser_kind = LP.strong_parser_kind 9 16777220 None

noextract val exportsec_parser: LP.parser exportsec_parser_kind exportsec

noextract val exportsec_serializer: LP.serializer exportsec_parser

noextract val exportsec_bytesize (x:exportsec) : GTot nat

noextract val exportsec_bytesize_eq (x:exportsec) : Lemma (exportsec_bytesize x == Seq.length (LP.serialize exportsec_serializer x))

val exportsec_parser32: LS.parser32 exportsec_parser

val exportsec_serializer32: LS.serializer32 exportsec_serializer

val exportsec_size32: LS.size32 exportsec_serializer

val exportsec_bytesize_eqn (x: exportsec) : Lemma (exportsec_bytesize x == (aux_section_const7_bytesize (x.n)) + (aux_constbyte0_bytesize (x.aux_ignore_byte)) + (exportsec_cont_bytesize (x.cont))) [SMTPat (exportsec_bytesize x)]
