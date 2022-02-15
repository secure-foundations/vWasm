module Wasm.Parse.Funcsec_cont

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

open Wasm.Parse.Aux_vectypeidx

type funcsec_cont = aux_vectypeidx

inline_for_extraction noextract let funcsec_cont_parser_kind = LP.strong_parser_kind 7 8195 None

noextract val funcsec_cont_parser: LP.parser funcsec_cont_parser_kind funcsec_cont

noextract val funcsec_cont_serializer: LP.serializer funcsec_cont_parser

noextract val funcsec_cont_bytesize (x:funcsec_cont) : GTot nat

noextract val funcsec_cont_bytesize_eq (x:funcsec_cont) : Lemma (funcsec_cont_bytesize x == Seq.length (LP.serialize funcsec_cont_serializer x))

val funcsec_cont_parser32: LS.parser32 funcsec_cont_parser

val funcsec_cont_serializer32: LS.serializer32 funcsec_cont_serializer

val funcsec_cont_size32: LS.size32 funcsec_cont_serializer

val funcsec_cont_bytesize_eqn (x: funcsec_cont) : Lemma (funcsec_cont_bytesize x == 3 + (aux_vectypeidx_bytesize (x))) [SMTPat (funcsec_cont_bytesize x)]

