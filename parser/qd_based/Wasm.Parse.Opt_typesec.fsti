module Wasm.Parse.Opt_typesec

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
open Wasm.Parse.Typesec

type opt_typesec =
  | X_absent of unit
  | X_present of typesec

inline_for_extraction let tag_of_opt_typesec (x:opt_typesec) : optional_tag = match x with
  | X_absent _ -> Absent
  | X_present _ -> Present

inline_for_extraction noextract let opt_typesec_parser_kind = LP.strong_parser_kind 1 16777221 None

noextract val opt_typesec_parser: LP.parser opt_typesec_parser_kind opt_typesec

noextract val opt_typesec_serializer: LP.serializer opt_typesec_parser

noextract val opt_typesec_bytesize (x:opt_typesec) : GTot nat

noextract val opt_typesec_bytesize_eq (x:opt_typesec) : Lemma (opt_typesec_bytesize x == Seq.length (LP.serialize opt_typesec_serializer x))

val opt_typesec_parser32: LS.parser32 opt_typesec_parser

val opt_typesec_serializer32: LS.serializer32 opt_typesec_serializer

val opt_typesec_size32: LS.size32 opt_typesec_serializer

val opt_typesec_bytesize_eqn_absent (x: unit) : Lemma (opt_typesec_bytesize (X_absent x) == 1 + 0) [SMTPat (opt_typesec_bytesize (X_absent x))]

val opt_typesec_bytesize_eqn_present (x: typesec) : Lemma (opt_typesec_bytesize (X_present x) == 1 + (typesec_bytesize (x))) [SMTPat (opt_typesec_bytesize (X_present x))]

