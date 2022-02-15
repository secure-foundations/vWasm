module Wasm.Parse.Elem

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

type elem' = ((tableidx & constexpr) & aux_vecfuncidx)

inline_for_extraction let synth_elem (x: elem') : elem =
  match x with ((x,e),y) -> {
    x = x;
    e = e;
    y = y;
  }

inline_for_extraction let synth_elem_recip (x: elem) : elem' = ((x.x,x.e),x.y)

let synth_elem_recip_inverse () : Lemma (LP.synth_inverse synth_elem_recip synth_elem) = ()

let synth_elem_injective () : Lemma (LP.synth_injective synth_elem) =
  LP.synth_inverse_synth_injective synth_elem_recip synth_elem;
  synth_elem_recip_inverse ()

let synth_elem_inverse () : Lemma (LP.synth_inverse synth_elem synth_elem_recip) =
  assert_norm (LP.synth_inverse synth_elem synth_elem_recip)

let synth_elem_recip_injective () : Lemma (LP.synth_injective synth_elem_recip) =
  synth_elem_recip_inverse ();
  LP.synth_inverse_synth_injective synth_elem synth_elem_recip

noextract let elem'_parser : LP.parser _ elem' = ((tableidx_parser `LP.nondep_then` constexpr_parser) `LP.nondep_then` aux_vecfuncidx_parser)

noextract let elem'_parser_kind = LP.get_parser_kind elem'_parser

let elem_parser =
  synth_elem_injective ();
  assert_norm (elem_parser_kind == elem'_parser_kind);
  elem'_parser `LP.parse_synth` synth_elem

noextract let elem'_serializer : LP.serializer elem'_parser = ((tableidx_serializer `LP.serialize_nondep_then` constexpr_serializer) `LP.serialize_nondep_then` aux_vecfuncidx_serializer)

let elem_serializer =
  [@inline_let] let _ = synth_elem_injective () in
  [@inline_let] let _ = synth_elem_inverse () in
  [@inline_let] let _ = assert_norm (elem_parser_kind == elem'_parser_kind) in
  LP.serialize_synth _ synth_elem elem'_serializer synth_elem_recip ()

let elem_bytesize (x:elem) : GTot nat = Seq.length (elem_serializer x)

let elem_bytesize_eq x = ()

inline_for_extraction let elem'_parser32 : LS.parser32 elem'_parser = ((tableidx_parser32 `LS.parse32_nondep_then` constexpr_parser32) `LS.parse32_nondep_then` aux_vecfuncidx_parser32)

let elem_parser32 =
  [@inline_let] let _ = synth_elem_injective () in
  [@inline_let] let _ = assert_norm (elem_parser_kind == elem'_parser_kind) in
  LS.parse32_synth _ synth_elem (fun x -> synth_elem x) elem'_parser32 ()

inline_for_extraction let elem'_serializer32 : LS.serializer32 elem'_serializer = ((tableidx_serializer32 `LS.serialize32_nondep_then` constexpr_serializer32) `LS.serialize32_nondep_then` aux_vecfuncidx_serializer32)

let elem_serializer32 =
  [@inline_let] let _ = synth_elem_injective () in
  [@inline_let] let _ = synth_elem_inverse () in
  [@inline_let] let _ = assert_norm (elem_parser_kind == elem'_parser_kind) in
  LS.serialize32_synth _ synth_elem _ elem'_serializer32 synth_elem_recip (fun x -> synth_elem_recip x) ()

inline_for_extraction let elem'_size32 : LS.size32 elem'_serializer = ((tableidx_size32 `LS.size32_nondep_then` constexpr_size32) `LS.size32_nondep_then` aux_vecfuncidx_size32)

let elem_size32 =
  [@inline_let] let _ = synth_elem_injective () in
  [@inline_let] let _ = synth_elem_inverse () in
  [@inline_let] let _ = assert_norm (elem_parser_kind == elem'_parser_kind) in
  LS.size32_synth _ synth_elem _ elem'_size32 synth_elem_recip (fun x -> synth_elem_recip x) ()

let elem_bytesize_eqn x =
  [@inline_let] let _ = synth_elem_injective () in
  [@inline_let] let _ = synth_elem_inverse () in
  [@inline_let] let _ = assert_norm (elem_parser_kind == elem'_parser_kind) in
  LP.serialize_synth_eq _ synth_elem elem'_serializer synth_elem_recip () x;
LP.length_serialize_nondep_then tableidx_serializer constexpr_serializer x.x x.e;
LP.length_serialize_nondep_then (tableidx_serializer `LP.serialize_nondep_then` constexpr_serializer) aux_vecfuncidx_serializer (x.x, x.e) x.y;
  (tableidx_bytesize_eq (x.x));
  (constexpr_bytesize_eq (x.e));
  (aux_vecfuncidx_bytesize_eq (x.y));
  assert(elem_bytesize x == Seq.length (LP.serialize tableidx_serializer x.x) + Seq.length (LP.serialize constexpr_serializer x.e) + Seq.length (LP.serialize aux_vecfuncidx_serializer x.y))

