module Wasm.Parse.Code

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec
module LS = LowParse.SLow
module LPI = LowParse.Spec.AllIntegers
module L = FStar.List.Tot
module BY = FStar.Bytes

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

type code' = (U32.t & func)

inline_for_extraction let synth_code (x: code') : code =
  match x with (size,code_) -> {
    size = size;
    code_ = code_;
  }

inline_for_extraction let synth_code_recip (x: code) : code' = (x.size,x.code_)

let synth_code_recip_inverse () : Lemma (LP.synth_inverse synth_code_recip synth_code) = ()

let synth_code_injective () : Lemma (LP.synth_injective synth_code) =
  LP.synth_inverse_synth_injective synth_code_recip synth_code;
  synth_code_recip_inverse ()

let synth_code_inverse () : Lemma (LP.synth_inverse synth_code synth_code_recip) =
  assert_norm (LP.synth_inverse synth_code synth_code_recip)

let synth_code_recip_injective () : Lemma (LP.synth_injective synth_code_recip) =
  synth_code_recip_inverse ();
  LP.synth_inverse_synth_injective synth_code synth_code_recip

noextract let code'_parser : LP.parser _ code' = (LPI.parse_u32 `LP.nondep_then` func_parser)

noextract let code'_parser_kind = LP.get_parser_kind code'_parser

let code_parser =
  synth_code_injective ();
  assert_norm (code_parser_kind == code'_parser_kind);
  code'_parser `LP.parse_synth` synth_code

noextract let code'_serializer : LP.serializer code'_parser = (LPI.serialize_u32 `LP.serialize_nondep_then` func_serializer)

let code_serializer =
  [@inline_let] let _ = synth_code_injective () in
  [@inline_let] let _ = synth_code_inverse () in
  [@inline_let] let _ = assert_norm (code_parser_kind == code'_parser_kind) in
  LP.serialize_synth _ synth_code code'_serializer synth_code_recip ()

let code_bytesize (x:code) : GTot nat = Seq.length (code_serializer x)

let code_bytesize_eq x = ()

inline_for_extraction let code'_parser32 : LS.parser32 code'_parser = (LS.parse32_u32 `LS.parse32_nondep_then` func_parser32)

let code_parser32 =
  [@inline_let] let _ = synth_code_injective () in
  [@inline_let] let _ = assert_norm (code_parser_kind == code'_parser_kind) in
  LS.parse32_synth _ synth_code (fun x -> synth_code x) code'_parser32 ()

inline_for_extraction let code'_serializer32 : LS.serializer32 code'_serializer = (LS.serialize32_u32 `LS.serialize32_nondep_then` func_serializer32)

let code_serializer32 =
  [@inline_let] let _ = synth_code_injective () in
  [@inline_let] let _ = synth_code_inverse () in
  [@inline_let] let _ = assert_norm (code_parser_kind == code'_parser_kind) in
  LS.serialize32_synth _ synth_code _ code'_serializer32 synth_code_recip (fun x -> synth_code_recip x) ()

inline_for_extraction let code'_size32 : LS.size32 code'_serializer = (LS.size32_u32 `LS.size32_nondep_then` func_size32)

let code_size32 =
  [@inline_let] let _ = synth_code_injective () in
  [@inline_let] let _ = synth_code_inverse () in
  [@inline_let] let _ = assert_norm (code_parser_kind == code'_parser_kind) in
  LS.size32_synth _ synth_code _ code'_size32 synth_code_recip (fun x -> synth_code_recip x) ()

let code_bytesize_eqn x =
  [@inline_let] let _ = synth_code_injective () in
  [@inline_let] let _ = synth_code_inverse () in
  [@inline_let] let _ = assert_norm (code_parser_kind == code'_parser_kind) in
  LP.serialize_synth_eq _ synth_code code'_serializer synth_code_recip () x;
LP.length_serialize_nondep_then LPI.serialize_u32 func_serializer x.size x.code_;
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.size)) == 4));
  (func_bytesize_eq (x.code_));
  assert(code_bytesize x == Seq.length (LP.serialize LPI.serialize_u32 x.size) + Seq.length (LP.serialize func_serializer x.code_))
