module Wasm.Parse.Elemsec_cont

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

open Wasm.Parse.Aux_vecelem

type elemsec_cont = x:aux_vecelem{let l = (aux_vecelem_bytesize (x)) in 0 <= l /\ l <= 16777215}

val check_elemsec_cont_bytesize (x: aux_vecelem) : Tot (b: bool {b == (let l = (aux_vecelem_bytesize (x)) in 0 <= l && l <= 16777215)})

inline_for_extraction noextract let elemsec_cont_parser_kind = LP.strong_parser_kind 7 16777218 None

noextract val elemsec_cont_parser: LP.parser elemsec_cont_parser_kind elemsec_cont

noextract val elemsec_cont_serializer: LP.serializer elemsec_cont_parser

noextract val elemsec_cont_bytesize (x:elemsec_cont) : GTot nat

noextract val elemsec_cont_bytesize_eq (x:elemsec_cont) : Lemma (elemsec_cont_bytesize x == Seq.length (LP.serialize elemsec_cont_serializer x))

val elemsec_cont_parser32: LS.parser32 elemsec_cont_parser

val elemsec_cont_serializer32: LS.serializer32 elemsec_cont_serializer

val elemsec_cont_size32: LS.size32 elemsec_cont_serializer

val elemsec_cont_bytesize_eqn (x: elemsec_cont) : Lemma (elemsec_cont_bytesize x == 3 + (aux_vecelem_bytesize (x))) [SMTPat (elemsec_cont_bytesize x)]

