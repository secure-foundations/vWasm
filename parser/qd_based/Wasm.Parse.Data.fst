module Wasm.Parse.Data

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

type data' = ((memidx & constexpr) & aux_vecbyte)

inline_for_extraction let synth_data (x: data') : data =
  match x with ((x,e),b) -> {
    x = x;
    e = e;
    b = b;
  }

inline_for_extraction let synth_data_recip (x: data) : data' = ((x.x,x.e),x.b)

let synth_data_recip_inverse () : Lemma (LP.synth_inverse synth_data_recip synth_data) = ()

let synth_data_injective () : Lemma (LP.synth_injective synth_data) =
  LP.synth_inverse_synth_injective synth_data_recip synth_data;
  synth_data_recip_inverse ()

let synth_data_inverse () : Lemma (LP.synth_inverse synth_data synth_data_recip) =
  assert_norm (LP.synth_inverse synth_data synth_data_recip)

let synth_data_recip_injective () : Lemma (LP.synth_injective synth_data_recip) =
  synth_data_recip_inverse ();
  LP.synth_inverse_synth_injective synth_data synth_data_recip

noextract let data'_parser : LP.parser _ data' = ((memidx_parser `LP.nondep_then` constexpr_parser) `LP.nondep_then` aux_vecbyte_parser)

noextract let data'_parser_kind = LP.get_parser_kind data'_parser

let data_parser =
  synth_data_injective ();
  assert_norm (data_parser_kind == data'_parser_kind);
  data'_parser `LP.parse_synth` synth_data

noextract let data'_serializer : LP.serializer data'_parser = ((memidx_serializer `LP.serialize_nondep_then` constexpr_serializer) `LP.serialize_nondep_then` aux_vecbyte_serializer)

let data_serializer =
  [@inline_let] let _ = synth_data_injective () in
  [@inline_let] let _ = synth_data_inverse () in
  [@inline_let] let _ = assert_norm (data_parser_kind == data'_parser_kind) in
  LP.serialize_synth _ synth_data data'_serializer synth_data_recip ()

let data_bytesize (x:data) : GTot nat = Seq.length (data_serializer x)

let data_bytesize_eq x = ()

inline_for_extraction let data'_parser32 : LS.parser32 data'_parser = ((memidx_parser32 `LS.parse32_nondep_then` constexpr_parser32) `LS.parse32_nondep_then` aux_vecbyte_parser32)

let data_parser32 =
  [@inline_let] let _ = synth_data_injective () in
  [@inline_let] let _ = assert_norm (data_parser_kind == data'_parser_kind) in
  LS.parse32_synth _ synth_data (fun x -> synth_data x) data'_parser32 ()

inline_for_extraction let data'_serializer32 : LS.serializer32 data'_serializer = ((memidx_serializer32 `LS.serialize32_nondep_then` constexpr_serializer32) `LS.serialize32_nondep_then` aux_vecbyte_serializer32)

let data_serializer32 =
  [@inline_let] let _ = synth_data_injective () in
  [@inline_let] let _ = synth_data_inverse () in
  [@inline_let] let _ = assert_norm (data_parser_kind == data'_parser_kind) in
  LS.serialize32_synth _ synth_data _ data'_serializer32 synth_data_recip (fun x -> synth_data_recip x) ()

inline_for_extraction let data'_size32 : LS.size32 data'_serializer = ((memidx_size32 `LS.size32_nondep_then` constexpr_size32) `LS.size32_nondep_then` aux_vecbyte_size32)

let data_size32 =
  [@inline_let] let _ = synth_data_injective () in
  [@inline_let] let _ = synth_data_inverse () in
  [@inline_let] let _ = assert_norm (data_parser_kind == data'_parser_kind) in
  LS.size32_synth _ synth_data _ data'_size32 synth_data_recip (fun x -> synth_data_recip x) ()

let data_bytesize_eqn x =
  [@inline_let] let _ = synth_data_injective () in
  [@inline_let] let _ = synth_data_inverse () in
  [@inline_let] let _ = assert_norm (data_parser_kind == data'_parser_kind) in
  LP.serialize_synth_eq _ synth_data data'_serializer synth_data_recip () x;
LP.length_serialize_nondep_then memidx_serializer constexpr_serializer x.x x.e;
LP.length_serialize_nondep_then (memidx_serializer `LP.serialize_nondep_then` constexpr_serializer) aux_vecbyte_serializer (x.x, x.e) x.b;
  (memidx_bytesize_eq (x.x));
  (constexpr_bytesize_eq (x.e));
  (aux_vecbyte_bytesize_eq (x.b));
  assert(data_bytesize x == Seq.length (LP.serialize memidx_serializer x.x) + Seq.length (LP.serialize constexpr_serializer x.e) + Seq.length (LP.serialize aux_vecbyte_serializer x.b))

