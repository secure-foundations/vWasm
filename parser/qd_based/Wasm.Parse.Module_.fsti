module Wasm.Parse.Module_

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

open Wasm.Parse.Magic_
open Wasm.Parse.Version
open Wasm.Parse.Opt_typesec
open Wasm.Parse.Opt_importsec
open Wasm.Parse.Opt_funcsec
open Wasm.Parse.Opt_tablesec
open Wasm.Parse.Opt_memsec
open Wasm.Parse.Opt_globalsec
open Wasm.Parse.Opt_exportsec
open Wasm.Parse.Opt_startsec
open Wasm.Parse.Opt_elemsec
open Wasm.Parse.Opt_codesec
open Wasm.Parse.Opt_datasec

type module_ = {
  _m : magic_;
  _v : version;
  functype : opt_typesec;
  import : opt_importsec;
  typeidx : opt_funcsec;
  table : opt_tablesec;
  mem : opt_memsec;
  global : opt_globalsec;
  export : opt_exportsec;
  start : opt_startsec;
  elem : opt_elemsec;
  code : opt_codesec;
  data : opt_datasec;
}

inline_for_extraction noextract let module__parser_kind = LP.strong_parser_kind 19 151003205 None

noextract val module__parser: LP.parser module__parser_kind module_

noextract val module__serializer: LP.serializer module__parser

noextract val module__bytesize (x:module_) : GTot nat

noextract val module__bytesize_eq (x:module_) : Lemma (module__bytesize x == Seq.length (LP.serialize module__serializer x))

val module__parser32: LS.parser32 module__parser

val module__serializer32: LS.serializer32 module__serializer

val module__size32: LS.size32 module__serializer

val module__bytesize_eqn (x: module_) : Lemma (module__bytesize x == (magic__bytesize (x._m)) + (version_bytesize (x._v)) + (opt_typesec_bytesize (x.functype)) + (opt_importsec_bytesize (x.import)) + (opt_funcsec_bytesize (x.typeidx)) + (opt_tablesec_bytesize (x.table)) + (opt_memsec_bytesize (x.mem)) + (opt_globalsec_bytesize (x.global)) + (opt_exportsec_bytesize (x.export)) + (opt_startsec_bytesize (x.start)) + (opt_elemsec_bytesize (x.elem)) + (opt_codesec_bytesize (x.code)) + (opt_datasec_bytesize (x.data))) [SMTPat (module__bytesize x)]

