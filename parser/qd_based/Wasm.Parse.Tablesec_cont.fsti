module Wasm.Parse.Tablesec_cont

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

open Wasm.Parse.Aux_vectable

type tablesec_cont = x:aux_vectable{let l = (aux_vectable_bytesize (x)) in 0 <= l /\ l <= 16777215}

val check_tablesec_cont_bytesize (x: aux_vectable) : Tot (b: bool {b == (let l = (aux_vectable_bytesize (x)) in 0 <= l && l <= 16777215)})

inline_for_extraction noextract let tablesec_cont_parser_kind = LP.strong_parser_kind 7 16777218 None

noextract val tablesec_cont_parser: LP.parser tablesec_cont_parser_kind tablesec_cont

noextract val tablesec_cont_serializer: LP.serializer tablesec_cont_parser

noextract val tablesec_cont_bytesize (x:tablesec_cont) : GTot nat

noextract val tablesec_cont_bytesize_eq (x:tablesec_cont) : Lemma (tablesec_cont_bytesize x == Seq.length (LP.serialize tablesec_cont_serializer x))

val tablesec_cont_parser32: LS.parser32 tablesec_cont_parser

val tablesec_cont_serializer32: LS.serializer32 tablesec_cont_serializer

val tablesec_cont_size32: LS.size32 tablesec_cont_serializer

val tablesec_cont_bytesize_eqn (x: tablesec_cont) : Lemma (tablesec_cont_bytesize x == 3 + (aux_vectable_bytesize (x))) [SMTPat (tablesec_cont_bytesize x)]

