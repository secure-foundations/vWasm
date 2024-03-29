module Wasm.Parse.Opt_datasec

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
open Wasm.Parse.Datasec

type opt_datasec =
  | X_absent of unit
  | X_present of datasec

inline_for_extraction let tag_of_opt_datasec (x:opt_datasec) : optional_tag = match x with
  | X_absent _ -> Absent
  | X_present _ -> Present

inline_for_extraction noextract let opt_datasec_parser_kind = LP.strong_parser_kind 1 16777221 None

noextract val opt_datasec_parser: LP.parser opt_datasec_parser_kind opt_datasec

noextract val opt_datasec_serializer: LP.serializer opt_datasec_parser

noextract val opt_datasec_bytesize (x:opt_datasec) : GTot nat

noextract val opt_datasec_bytesize_eq (x:opt_datasec) : Lemma (opt_datasec_bytesize x == Seq.length (LP.serialize opt_datasec_serializer x))

val opt_datasec_parser32: LS.parser32 opt_datasec_parser

val opt_datasec_serializer32: LS.serializer32 opt_datasec_serializer

val opt_datasec_size32: LS.size32 opt_datasec_serializer

val opt_datasec_bytesize_eqn_absent (x: unit) : Lemma (opt_datasec_bytesize (X_absent x) == 1 + 0) [SMTPat (opt_datasec_bytesize (X_absent x))]

val opt_datasec_bytesize_eqn_present (x: datasec) : Lemma (opt_datasec_bytesize (X_present x) == 1 + (datasec_bytesize (x))) [SMTPat (opt_datasec_bytesize (X_present x))]

