module Wasm.Parse.Constexpr

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

open Wasm.Parse.Instr

noextract val constexpr_list_bytesize: list instr -> GTot nat

type constexpr = l:list instr{let x = constexpr_list_bytesize l in 0 <= x /\ x <= 1023}

val constexpr_list_bytesize_nil : squash (constexpr_list_bytesize [] == 0)

val constexpr_list_bytesize_cons (x: instr) (y: list instr) : Lemma (constexpr_list_bytesize (x :: y) == (instr_bytesize (x)) + constexpr_list_bytesize y) [SMTPat (constexpr_list_bytesize (x :: y))]

val check_constexpr_list_bytesize (l: list instr) : Tot (b: bool {b == (let x = constexpr_list_bytesize l in 0 <= x && x <= 1023)})

inline_for_extraction noextract let constexpr_parser_kind = LP.strong_parser_kind 2 1025 None

noextract val constexpr_parser: LP.parser constexpr_parser_kind constexpr

noextract val constexpr_serializer: LP.serializer constexpr_parser

noextract val constexpr_bytesize (x:constexpr) : GTot nat

noextract val constexpr_bytesize_eq (x:constexpr) : Lemma (constexpr_bytesize x == Seq.length (LP.serialize constexpr_serializer x))

val constexpr_parser32: LS.parser32 constexpr_parser

val constexpr_serializer32: LS.serializer32 constexpr_serializer

val constexpr_size32: LS.size32 constexpr_serializer

val constexpr_bytesize_eqn (x: constexpr) : Lemma (constexpr_bytesize x == 2 + constexpr_list_bytesize x) [SMTPat (constexpr_bytesize x)]
