module Wasm.Parse.Uint64

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

type uint64' = (U32.t & U32.t)

inline_for_extraction let synth_uint64 (x: uint64') : uint64 =
  match x with (high,low) -> {
    high = high;
    low = low;
  }

inline_for_extraction let synth_uint64_recip (x: uint64) : uint64' = (x.high,x.low)

let synth_uint64_recip_inverse () : Lemma (LP.synth_inverse synth_uint64_recip synth_uint64) = ()

let synth_uint64_injective () : Lemma (LP.synth_injective synth_uint64) =
  LP.synth_inverse_synth_injective synth_uint64_recip synth_uint64;
  synth_uint64_recip_inverse ()

let synth_uint64_inverse () : Lemma (LP.synth_inverse synth_uint64 synth_uint64_recip) =
  assert_norm (LP.synth_inverse synth_uint64 synth_uint64_recip)

let synth_uint64_recip_injective () : Lemma (LP.synth_injective synth_uint64_recip) =
  synth_uint64_recip_inverse ();
  LP.synth_inverse_synth_injective synth_uint64 synth_uint64_recip

noextract let uint64'_parser : LP.parser _ uint64' = (LPI.parse_u32 `LP.nondep_then` LPI.parse_u32)

noextract let uint64'_parser_kind = LP.get_parser_kind uint64'_parser

let uint64_parser =
  synth_uint64_injective ();
  assert_norm (uint64_parser_kind == uint64'_parser_kind);
  uint64'_parser `LP.parse_synth` synth_uint64

noextract let uint64'_serializer : LP.serializer uint64'_parser = (LPI.serialize_u32 `LP.serialize_nondep_then` LPI.serialize_u32)

let uint64_serializer =
  [@inline_let] let _ = synth_uint64_injective () in
  [@inline_let] let _ = synth_uint64_inverse () in
  [@inline_let] let _ = assert_norm (uint64_parser_kind == uint64'_parser_kind) in
  LP.serialize_synth _ synth_uint64 uint64'_serializer synth_uint64_recip ()

let uint64_bytesize (x:uint64) : GTot nat = Seq.length (uint64_serializer x)

let uint64_bytesize_eq x = ()

inline_for_extraction let uint64'_parser32 : LS.parser32 uint64'_parser = (LS.parse32_u32 `LS.parse32_nondep_then` LS.parse32_u32)

let uint64_parser32 =
  [@inline_let] let _ = synth_uint64_injective () in
  [@inline_let] let _ = assert_norm (uint64_parser_kind == uint64'_parser_kind) in
  LS.parse32_synth _ synth_uint64 (fun x -> synth_uint64 x) uint64'_parser32 ()

inline_for_extraction let uint64'_serializer32 : LS.serializer32 uint64'_serializer = (LS.serialize32_u32 `LS.serialize32_nondep_then` LS.serialize32_u32)

let uint64_serializer32 =
  [@inline_let] let _ = synth_uint64_injective () in
  [@inline_let] let _ = synth_uint64_inverse () in
  [@inline_let] let _ = assert_norm (uint64_parser_kind == uint64'_parser_kind) in
  LS.serialize32_synth _ synth_uint64 _ uint64'_serializer32 synth_uint64_recip (fun x -> synth_uint64_recip x) ()

inline_for_extraction let uint64'_size32 : LS.size32 uint64'_serializer = (LS.size32_u32 `LS.size32_nondep_then` LS.size32_u32)

let uint64_size32 =
  [@inline_let] let _ = synth_uint64_injective () in
  [@inline_let] let _ = synth_uint64_inverse () in
  [@inline_let] let _ = assert_norm (uint64_parser_kind == uint64'_parser_kind) in
  LS.size32_synth _ synth_uint64 _ uint64'_size32 synth_uint64_recip (fun x -> synth_uint64_recip x) ()

let uint64_bytesize_eqn x =
  [@inline_let] let _ = synth_uint64_injective () in
  [@inline_let] let _ = synth_uint64_inverse () in
  [@inline_let] let _ = assert_norm (uint64_parser_kind == uint64'_parser_kind) in
  LP.serialize_synth_eq _ synth_uint64 uint64'_serializer synth_uint64_recip () x;
LP.length_serialize_nondep_then LPI.serialize_u32 LPI.serialize_u32 x.high x.low;
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.high)) == 4));
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.low)) == 4));
  assert(uint64_bytesize x == Seq.length (LP.serialize LPI.serialize_u32 x.high) + Seq.length (LP.serialize LPI.serialize_u32 x.low))

