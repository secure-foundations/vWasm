module Wasm.Parse.Aux_min_max

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

type aux_min_max' = (U32.t & U32.t)

inline_for_extraction let synth_aux_min_max (x: aux_min_max') : aux_min_max =
  match x with (min,max) -> {
    min = min;
    max = max;
  }

inline_for_extraction let synth_aux_min_max_recip (x: aux_min_max) : aux_min_max' = (x.min,x.max)

let synth_aux_min_max_recip_inverse () : Lemma (LP.synth_inverse synth_aux_min_max_recip synth_aux_min_max) = ()

let synth_aux_min_max_injective () : Lemma (LP.synth_injective synth_aux_min_max) =
  LP.synth_inverse_synth_injective synth_aux_min_max_recip synth_aux_min_max;
  synth_aux_min_max_recip_inverse ()

let synth_aux_min_max_inverse () : Lemma (LP.synth_inverse synth_aux_min_max synth_aux_min_max_recip) =
  assert_norm (LP.synth_inverse synth_aux_min_max synth_aux_min_max_recip)

let synth_aux_min_max_recip_injective () : Lemma (LP.synth_injective synth_aux_min_max_recip) =
  synth_aux_min_max_recip_inverse ();
  LP.synth_inverse_synth_injective synth_aux_min_max synth_aux_min_max_recip

noextract let aux_min_max'_parser : LP.parser _ aux_min_max' = (LPI.parse_u32 `LP.nondep_then` LPI.parse_u32)

noextract let aux_min_max'_parser_kind = LP.get_parser_kind aux_min_max'_parser

let aux_min_max_parser =
  synth_aux_min_max_injective ();
  assert_norm (aux_min_max_parser_kind == aux_min_max'_parser_kind);
  aux_min_max'_parser `LP.parse_synth` synth_aux_min_max

noextract let aux_min_max'_serializer : LP.serializer aux_min_max'_parser = (LPI.serialize_u32 `LP.serialize_nondep_then` LPI.serialize_u32)

let aux_min_max_serializer =
  [@inline_let] let _ = synth_aux_min_max_injective () in
  [@inline_let] let _ = synth_aux_min_max_inverse () in
  [@inline_let] let _ = assert_norm (aux_min_max_parser_kind == aux_min_max'_parser_kind) in
  LP.serialize_synth _ synth_aux_min_max aux_min_max'_serializer synth_aux_min_max_recip ()

let aux_min_max_bytesize (x:aux_min_max) : GTot nat = Seq.length (aux_min_max_serializer x)

let aux_min_max_bytesize_eq x = ()

inline_for_extraction let aux_min_max'_parser32 : LS.parser32 aux_min_max'_parser = (LS.parse32_u32 `LS.parse32_nondep_then` LS.parse32_u32)

let aux_min_max_parser32 =
  [@inline_let] let _ = synth_aux_min_max_injective () in
  [@inline_let] let _ = assert_norm (aux_min_max_parser_kind == aux_min_max'_parser_kind) in
  LS.parse32_synth _ synth_aux_min_max (fun x -> synth_aux_min_max x) aux_min_max'_parser32 ()

inline_for_extraction let aux_min_max'_serializer32 : LS.serializer32 aux_min_max'_serializer = (LS.serialize32_u32 `LS.serialize32_nondep_then` LS.serialize32_u32)

let aux_min_max_serializer32 =
  [@inline_let] let _ = synth_aux_min_max_injective () in
  [@inline_let] let _ = synth_aux_min_max_inverse () in
  [@inline_let] let _ = assert_norm (aux_min_max_parser_kind == aux_min_max'_parser_kind) in
  LS.serialize32_synth _ synth_aux_min_max _ aux_min_max'_serializer32 synth_aux_min_max_recip (fun x -> synth_aux_min_max_recip x) ()

inline_for_extraction let aux_min_max'_size32 : LS.size32 aux_min_max'_serializer = (LS.size32_u32 `LS.size32_nondep_then` LS.size32_u32)

let aux_min_max_size32 =
  [@inline_let] let _ = synth_aux_min_max_injective () in
  [@inline_let] let _ = synth_aux_min_max_inverse () in
  [@inline_let] let _ = assert_norm (aux_min_max_parser_kind == aux_min_max'_parser_kind) in
  LS.size32_synth _ synth_aux_min_max _ aux_min_max'_size32 synth_aux_min_max_recip (fun x -> synth_aux_min_max_recip x) ()

let aux_min_max_bytesize_eqn x =
  [@inline_let] let _ = synth_aux_min_max_injective () in
  [@inline_let] let _ = synth_aux_min_max_inverse () in
  [@inline_let] let _ = assert_norm (aux_min_max_parser_kind == aux_min_max'_parser_kind) in
  LP.serialize_synth_eq _ synth_aux_min_max aux_min_max'_serializer synth_aux_min_max_recip () x;
LP.length_serialize_nondep_then LPI.serialize_u32 LPI.serialize_u32 x.min x.max;
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.min)) == 4));
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.max)) == 4));
  assert(aux_min_max_bytesize x == Seq.length (LP.serialize LPI.serialize_u32 x.min) + Seq.length (LP.serialize LPI.serialize_u32 x.max))
