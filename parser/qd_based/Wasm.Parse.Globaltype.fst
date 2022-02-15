module Wasm.Parse.Globaltype

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

type globaltype' = (valtype & mut)

inline_for_extraction let synth_globaltype (x: globaltype') : globaltype =
  match x with (t,m) -> {
    t = t;
    m = m;
  }

inline_for_extraction let synth_globaltype_recip (x: globaltype) : globaltype' = (x.t,x.m)

let synth_globaltype_recip_inverse () : Lemma (LP.synth_inverse synth_globaltype_recip synth_globaltype) = ()

let synth_globaltype_injective () : Lemma (LP.synth_injective synth_globaltype) =
  LP.synth_inverse_synth_injective synth_globaltype_recip synth_globaltype;
  synth_globaltype_recip_inverse ()

let synth_globaltype_inverse () : Lemma (LP.synth_inverse synth_globaltype synth_globaltype_recip) =
  assert_norm (LP.synth_inverse synth_globaltype synth_globaltype_recip)

let synth_globaltype_recip_injective () : Lemma (LP.synth_injective synth_globaltype_recip) =
  synth_globaltype_recip_inverse ();
  LP.synth_inverse_synth_injective synth_globaltype synth_globaltype_recip

noextract let globaltype'_parser : LP.parser _ globaltype' = (valtype_parser `LP.nondep_then` mut_parser)

noextract let globaltype'_parser_kind = LP.get_parser_kind globaltype'_parser

let globaltype_parser =
  synth_globaltype_injective ();
  assert_norm (globaltype_parser_kind == globaltype'_parser_kind);
  globaltype'_parser `LP.parse_synth` synth_globaltype

noextract let globaltype'_serializer : LP.serializer globaltype'_parser = (valtype_serializer `LP.serialize_nondep_then` mut_serializer)

let globaltype_serializer =
  [@inline_let] let _ = synth_globaltype_injective () in
  [@inline_let] let _ = synth_globaltype_inverse () in
  [@inline_let] let _ = assert_norm (globaltype_parser_kind == globaltype'_parser_kind) in
  LP.serialize_synth _ synth_globaltype globaltype'_serializer synth_globaltype_recip ()

let globaltype_bytesize (x:globaltype) : GTot nat = Seq.length (globaltype_serializer x)

let globaltype_bytesize_eq x = ()

inline_for_extraction let globaltype'_parser32 : LS.parser32 globaltype'_parser = (valtype_parser32 `LS.parse32_nondep_then` mut_parser32)

let globaltype_parser32 =
  [@inline_let] let _ = synth_globaltype_injective () in
  [@inline_let] let _ = assert_norm (globaltype_parser_kind == globaltype'_parser_kind) in
  LS.parse32_synth _ synth_globaltype (fun x -> synth_globaltype x) globaltype'_parser32 ()

inline_for_extraction let globaltype'_serializer32 : LS.serializer32 globaltype'_serializer = (valtype_serializer32 `LS.serialize32_nondep_then` mut_serializer32)

let globaltype_serializer32 =
  [@inline_let] let _ = synth_globaltype_injective () in
  [@inline_let] let _ = synth_globaltype_inverse () in
  [@inline_let] let _ = assert_norm (globaltype_parser_kind == globaltype'_parser_kind) in
  LS.serialize32_synth _ synth_globaltype _ globaltype'_serializer32 synth_globaltype_recip (fun x -> synth_globaltype_recip x) ()

inline_for_extraction let globaltype'_size32 : LS.size32 globaltype'_serializer = (valtype_size32 `LS.size32_nondep_then` mut_size32)

let globaltype_size32 =
  [@inline_let] let _ = synth_globaltype_injective () in
  [@inline_let] let _ = synth_globaltype_inverse () in
  [@inline_let] let _ = assert_norm (globaltype_parser_kind == globaltype'_parser_kind) in
  LS.size32_synth _ synth_globaltype _ globaltype'_size32 synth_globaltype_recip (fun x -> synth_globaltype_recip x) ()

let globaltype_bytesize_eqn x =
  [@inline_let] let _ = synth_globaltype_injective () in
  [@inline_let] let _ = synth_globaltype_inverse () in
  [@inline_let] let _ = assert_norm (globaltype_parser_kind == globaltype'_parser_kind) in
  LP.serialize_synth_eq _ synth_globaltype globaltype'_serializer synth_globaltype_recip () x;
LP.length_serialize_nondep_then valtype_serializer mut_serializer x.t x.m;
  (valtype_bytesize_eq (x.t));
  (mut_bytesize_eq (x.m));
  assert(globaltype_bytesize x == Seq.length (LP.serialize valtype_serializer x.t) + Seq.length (LP.serialize mut_serializer x.m))
