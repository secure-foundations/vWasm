module Wasm.Parse.Opt_codesec

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
open Wasm.Parse.Codesec

type opt_codesec =
  | X_absent of unit
  | X_present of codesec

inline_for_extraction let tag_of_opt_codesec (x:opt_codesec) : optional_tag = match x with
  | X_absent _ -> Absent
  | X_present _ -> Present

inline_for_extraction noextract let opt_codesec_parser_kind = LP.strong_parser_kind 1 16777221 None

noextract val opt_codesec_parser: LP.parser opt_codesec_parser_kind opt_codesec

noextract val opt_codesec_serializer: LP.serializer opt_codesec_parser

noextract val opt_codesec_bytesize (x:opt_codesec) : GTot nat

noextract val opt_codesec_bytesize_eq (x:opt_codesec) : Lemma (opt_codesec_bytesize x == Seq.length (LP.serialize opt_codesec_serializer x))

val opt_codesec_parser32: LS.parser32 opt_codesec_parser

val opt_codesec_serializer32: LS.serializer32 opt_codesec_serializer

val opt_codesec_size32: LS.size32 opt_codesec_serializer

val opt_codesec_bytesize_eqn_absent (x: unit) : Lemma (opt_codesec_bytesize (X_absent x) == 1 + 0) [SMTPat (opt_codesec_bytesize (X_absent x))]

val opt_codesec_bytesize_eqn_present (x: codesec) : Lemma (opt_codesec_bytesize (X_present x) == 1 + (codesec_bytesize (x))) [SMTPat (opt_codesec_bytesize (X_present x))]
