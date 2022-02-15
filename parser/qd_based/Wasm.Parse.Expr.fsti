module Wasm.Parse.Expr

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

noextract val expr_list_bytesize: list instr -> GTot nat

type expr = l:list instr{let x = expr_list_bytesize l in 0 <= x /\ x <= 1048575}

val expr_list_bytesize_nil : squash (expr_list_bytesize [] == 0)

val expr_list_bytesize_cons (x: instr) (y: list instr) : Lemma (expr_list_bytesize (x :: y) == (instr_bytesize (x)) + expr_list_bytesize y) [SMTPat (expr_list_bytesize (x :: y))]

val check_expr_list_bytesize (l: list instr) : Tot (b: bool {b == (let x = expr_list_bytesize l in 0 <= x && x <= 1048575)})

inline_for_extraction noextract let expr_parser_kind = LP.strong_parser_kind 3 1048578 None

noextract val expr_parser: LP.parser expr_parser_kind expr

noextract val expr_serializer: LP.serializer expr_parser

noextract val expr_bytesize (x:expr) : GTot nat

noextract val expr_bytesize_eq (x:expr) : Lemma (expr_bytesize x == Seq.length (LP.serialize expr_serializer x))

val expr_parser32: LS.parser32 expr_parser

val expr_serializer32: LS.serializer32 expr_serializer

val expr_size32: LS.size32 expr_serializer

val expr_bytesize_eqn (x: expr) : Lemma (expr_bytesize x == 3 + expr_list_bytesize x) [SMTPat (expr_bytesize x)]

