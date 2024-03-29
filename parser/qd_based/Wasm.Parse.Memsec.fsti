module Wasm.Parse.Memsec

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

open Wasm.Parse.Aux_section_const5
open Wasm.Parse.Aux_constbyte0
open Wasm.Parse.Aux_vecmem

(* Type of field cont*)
include Wasm.Parse.Memsec_cont

type memsec = {
  n : aux_section_const5;
  aux_ignore_byte : aux_constbyte0;
  cont : memsec_cont;
}

inline_for_extraction noextract let memsec_parser_kind = LP.strong_parser_kind 9 16777220 None

noextract val memsec_parser: LP.parser memsec_parser_kind memsec

noextract val memsec_serializer: LP.serializer memsec_parser

noextract val memsec_bytesize (x:memsec) : GTot nat

noextract val memsec_bytesize_eq (x:memsec) : Lemma (memsec_bytesize x == Seq.length (LP.serialize memsec_serializer x))

val memsec_parser32: LS.parser32 memsec_parser

val memsec_serializer32: LS.serializer32 memsec_serializer

val memsec_size32: LS.size32 memsec_serializer

val memsec_bytesize_eqn (x: memsec) : Lemma (memsec_bytesize x == (aux_section_const5_bytesize (x.n)) + (aux_constbyte0_bytesize (x.aux_ignore_byte)) + (memsec_cont_bytesize (x.cont))) [SMTPat (memsec_bytesize x)]

