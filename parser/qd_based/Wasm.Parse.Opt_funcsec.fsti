module Wasm.Parse.Opt_funcsec

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
open Wasm.Parse.Funcsec

type opt_funcsec =
  | X_absent of unit
  | X_present of funcsec

inline_for_extraction let tag_of_opt_funcsec (x:opt_funcsec) : optional_tag = match x with
  | X_absent _ -> Absent
  | X_present _ -> Present

inline_for_extraction noextract let opt_funcsec_parser_kind = LP.strong_parser_kind 1 8198 None

noextract val opt_funcsec_parser: LP.parser opt_funcsec_parser_kind opt_funcsec

noextract val opt_funcsec_serializer: LP.serializer opt_funcsec_parser

noextract val opt_funcsec_bytesize (x:opt_funcsec) : GTot nat

noextract val opt_funcsec_bytesize_eq (x:opt_funcsec) : Lemma (opt_funcsec_bytesize x == Seq.length (LP.serialize opt_funcsec_serializer x))

val opt_funcsec_parser32: LS.parser32 opt_funcsec_parser

val opt_funcsec_serializer32: LS.serializer32 opt_funcsec_serializer

val opt_funcsec_size32: LS.size32 opt_funcsec_serializer

val opt_funcsec_bytesize_eqn_absent (x: unit) : Lemma (opt_funcsec_bytesize (X_absent x) == 1 + 0) [SMTPat (opt_funcsec_bytesize (X_absent x))]

val opt_funcsec_bytesize_eqn_present (x: funcsec) : Lemma (opt_funcsec_bytesize (X_present x) == 1 + (funcsec_bytesize (x))) [SMTPat (opt_funcsec_bytesize (X_present x))]

