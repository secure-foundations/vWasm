module Wasm.Parse.Importsec_cont

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

open Wasm.Parse.Aux_vecimport

type importsec_cont = x:aux_vecimport{let l = (aux_vecimport_bytesize (x)) in 0 <= l /\ l <= 16777215}

val check_importsec_cont_bytesize (x: aux_vecimport) : Tot (b: bool {b == (let l = (aux_vecimport_bytesize (x)) in 0 <= l && l <= 16777215)})

inline_for_extraction noextract let importsec_cont_parser_kind = LP.strong_parser_kind 7 16777218 None

noextract val importsec_cont_parser: LP.parser importsec_cont_parser_kind importsec_cont

noextract val importsec_cont_serializer: LP.serializer importsec_cont_parser

noextract val importsec_cont_bytesize (x:importsec_cont) : GTot nat

noextract val importsec_cont_bytesize_eq (x:importsec_cont) : Lemma (importsec_cont_bytesize x == Seq.length (LP.serialize importsec_cont_serializer x))

val importsec_cont_parser32: LS.parser32 importsec_cont_parser

val importsec_cont_serializer32: LS.serializer32 importsec_cont_serializer

val importsec_cont_size32: LS.size32 importsec_cont_serializer

val importsec_cont_bytesize_eqn (x: importsec_cont) : Lemma (importsec_cont_bytesize x == 3 + (aux_vecimport_bytesize (x))) [SMTPat (importsec_cont_bytesize x)]

