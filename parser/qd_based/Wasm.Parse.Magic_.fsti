module Wasm.Parse.Magic_

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

open Wasm.Parse.Aux_magic_0
open Wasm.Parse.Aux_magic_1
open Wasm.Parse.Aux_magic_2
open Wasm.Parse.Aux_magic_3

type magic_ = {
  m0 : aux_magic_0;
  m1 : aux_magic_1;
  m2 : aux_magic_2;
  m3 : aux_magic_3;
}

inline_for_extraction noextract let magic__parser_kind = LP.strong_parser_kind 4 4 None

noextract val magic__parser: LP.parser magic__parser_kind magic_

noextract val magic__serializer: LP.serializer magic__parser

noextract val magic__bytesize (x:magic_) : GTot nat

noextract val magic__bytesize_eq (x:magic_) : Lemma (magic__bytesize x == Seq.length (LP.serialize magic__serializer x))

val magic__parser32: LS.parser32 magic__parser

val magic__serializer32: LS.serializer32 magic__serializer

val magic__size32: LS.size32 magic__serializer

val magic__bytesize_eqn (x: magic_) : Lemma (magic__bytesize x == (aux_magic_0_bytesize (x.m0)) + (aux_magic_1_bytesize (x.m1)) + (aux_magic_2_bytesize (x.m2)) + (aux_magic_3_bytesize (x.m3))) [SMTPat (magic__bytesize x)]

