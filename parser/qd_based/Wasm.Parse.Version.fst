module Wasm.Parse.Version

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

type version' = ((aux_version_1 & aux_version_0) & (aux_version_0 & aux_version_0))

inline_for_extraction let synth_version (x: version') : version =
  match x with ((v0,v1),(v2,v3)) -> {
    v0 = v0;
    v1 = v1;
    v2 = v2;
    v3 = v3;
  }

inline_for_extraction let synth_version_recip (x: version) : version' = ((x.v0,x.v1),(x.v2,x.v3))

let synth_version_recip_inverse () : Lemma (LP.synth_inverse synth_version_recip synth_version) = ()

let synth_version_injective () : Lemma (LP.synth_injective synth_version) =
  LP.synth_inverse_synth_injective synth_version_recip synth_version;
  synth_version_recip_inverse ()

let synth_version_inverse () : Lemma (LP.synth_inverse synth_version synth_version_recip) =
  assert_norm (LP.synth_inverse synth_version synth_version_recip)

let synth_version_recip_injective () : Lemma (LP.synth_injective synth_version_recip) =
  synth_version_recip_inverse ();
  LP.synth_inverse_synth_injective synth_version synth_version_recip

noextract let version'_parser : LP.parser _ version' = ((aux_version_1_parser `LP.nondep_then` aux_version_0_parser) `LP.nondep_then` (aux_version_0_parser `LP.nondep_then` aux_version_0_parser))

noextract let version'_parser_kind = LP.get_parser_kind version'_parser

let version_parser =
  synth_version_injective ();
  assert_norm (version_parser_kind == version'_parser_kind);
  version'_parser `LP.parse_synth` synth_version

noextract let version'_serializer : LP.serializer version'_parser = ((aux_version_1_serializer `LP.serialize_nondep_then` aux_version_0_serializer) `LP.serialize_nondep_then` (aux_version_0_serializer `LP.serialize_nondep_then` aux_version_0_serializer))

let version_serializer =
  [@inline_let] let _ = synth_version_injective () in
  [@inline_let] let _ = synth_version_inverse () in
  [@inline_let] let _ = assert_norm (version_parser_kind == version'_parser_kind) in
  LP.serialize_synth _ synth_version version'_serializer synth_version_recip ()

let version_bytesize (x:version) : GTot nat = Seq.length (version_serializer x)

let version_bytesize_eq x = ()

inline_for_extraction let version'_parser32 : LS.parser32 version'_parser = ((aux_version_1_parser32 `LS.parse32_nondep_then` aux_version_0_parser32) `LS.parse32_nondep_then` (aux_version_0_parser32 `LS.parse32_nondep_then` aux_version_0_parser32))

let version_parser32 =
  [@inline_let] let _ = synth_version_injective () in
  [@inline_let] let _ = assert_norm (version_parser_kind == version'_parser_kind) in
  LS.parse32_synth _ synth_version (fun x -> synth_version x) version'_parser32 ()

inline_for_extraction let version'_serializer32 : LS.serializer32 version'_serializer = ((aux_version_1_serializer32 `LS.serialize32_nondep_then` aux_version_0_serializer32) `LS.serialize32_nondep_then` (aux_version_0_serializer32 `LS.serialize32_nondep_then` aux_version_0_serializer32))

let version_serializer32 =
  [@inline_let] let _ = synth_version_injective () in
  [@inline_let] let _ = synth_version_inverse () in
  [@inline_let] let _ = assert_norm (version_parser_kind == version'_parser_kind) in
  LS.serialize32_synth _ synth_version _ version'_serializer32 synth_version_recip (fun x -> synth_version_recip x) ()

inline_for_extraction let version'_size32 : LS.size32 version'_serializer = ((aux_version_1_size32 `LS.size32_nondep_then` aux_version_0_size32) `LS.size32_nondep_then` (aux_version_0_size32 `LS.size32_nondep_then` aux_version_0_size32))

let version_size32 =
  [@inline_let] let _ = synth_version_injective () in
  [@inline_let] let _ = synth_version_inverse () in
  [@inline_let] let _ = assert_norm (version_parser_kind == version'_parser_kind) in
  LS.size32_synth _ synth_version _ version'_size32 synth_version_recip (fun x -> synth_version_recip x) ()

let version_bytesize_eqn x =
  [@inline_let] let _ = synth_version_injective () in
  [@inline_let] let _ = synth_version_inverse () in
  [@inline_let] let _ = assert_norm (version_parser_kind == version'_parser_kind) in
  LP.serialize_synth_eq _ synth_version version'_serializer synth_version_recip () x;
LP.length_serialize_nondep_then aux_version_1_serializer aux_version_0_serializer x.v0 x.v1;
LP.length_serialize_nondep_then aux_version_0_serializer aux_version_0_serializer x.v2 x.v3;
LP.length_serialize_nondep_then (aux_version_1_serializer `LP.serialize_nondep_then` aux_version_0_serializer) (aux_version_0_serializer `LP.serialize_nondep_then` aux_version_0_serializer) (x.v0, x.v1) (x.v2, x.v3);
  (aux_version_1_bytesize_eq (x.v0));
  (aux_version_0_bytesize_eq (x.v1));
  (aux_version_0_bytesize_eq (x.v2));
  (aux_version_0_bytesize_eq (x.v3));
  assert(version_bytesize x == Seq.length (LP.serialize aux_version_1_serializer x.v0) + Seq.length (LP.serialize aux_version_0_serializer x.v1) + Seq.length (LP.serialize aux_version_0_serializer x.v2) + Seq.length (LP.serialize aux_version_0_serializer x.v3))

