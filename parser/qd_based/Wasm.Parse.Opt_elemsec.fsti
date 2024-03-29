module Wasm.Parse.Opt_elemsec

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

open Wasm.Parse.Optional_tag
open Wasm.Parse.Elemsec

type opt_elemsec =
  | X_absent of unit
  | X_present of elemsec

inline_for_extraction let tag_of_opt_elemsec (x:opt_elemsec) : optional_tag = match x with
  | X_absent _ -> Absent
  | X_present _ -> Present

inline_for_extraction noextract let opt_elemsec_parser_kind = LP.strong_parser_kind 1 16777221 None

noextract val opt_elemsec_parser: LP.parser opt_elemsec_parser_kind opt_elemsec

noextract val opt_elemsec_serializer: LP.serializer opt_elemsec_parser

noextract val opt_elemsec_bytesize (x:opt_elemsec) : GTot nat

noextract val opt_elemsec_bytesize_eq (x:opt_elemsec) : Lemma (opt_elemsec_bytesize x == Seq.length (LP.serialize opt_elemsec_serializer x))

val opt_elemsec_parser32: LS.parser32 opt_elemsec_parser

val opt_elemsec_serializer32: LS.serializer32 opt_elemsec_serializer

val opt_elemsec_size32: LS.size32 opt_elemsec_serializer

val opt_elemsec_bytesize_eqn_absent (x: unit) : Lemma (opt_elemsec_bytesize (X_absent x) == 1 + 0) [SMTPat (opt_elemsec_bytesize (X_absent x))]

val opt_elemsec_bytesize_eqn_present (x: elemsec) : Lemma (opt_elemsec_bytesize (X_present x) == 1 + (elemsec_bytesize (x))) [SMTPat (opt_elemsec_bytesize (X_present x))]

