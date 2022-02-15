module Wasm.Parse.Functype

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

type functype' = ((aux_functype_magic & aux_vecvaltype) & aux_vecvaltype)

inline_for_extraction let synth_functype (x: functype') : functype =
  match x with ((m,params),results) -> {
    m = m;
    params = params;
    results = results;
  }

inline_for_extraction let synth_functype_recip (x: functype) : functype' = ((x.m,x.params),x.results)

let synth_functype_recip_inverse () : Lemma (LP.synth_inverse synth_functype_recip synth_functype) = ()

let synth_functype_injective () : Lemma (LP.synth_injective synth_functype) =
  LP.synth_inverse_synth_injective synth_functype_recip synth_functype;
  synth_functype_recip_inverse ()

let synth_functype_inverse () : Lemma (LP.synth_inverse synth_functype synth_functype_recip) =
  assert_norm (LP.synth_inverse synth_functype synth_functype_recip)

let synth_functype_recip_injective () : Lemma (LP.synth_injective synth_functype_recip) =
  synth_functype_recip_inverse ();
  LP.synth_inverse_synth_injective synth_functype synth_functype_recip

noextract let functype'_parser : LP.parser _ functype' = ((aux_functype_magic_parser `LP.nondep_then` aux_vecvaltype_parser) `LP.nondep_then` aux_vecvaltype_parser)

noextract let functype'_parser_kind = LP.get_parser_kind functype'_parser

let functype_parser =
  synth_functype_injective ();
  assert_norm (functype_parser_kind == functype'_parser_kind);
  functype'_parser `LP.parse_synth` synth_functype

noextract let functype'_serializer : LP.serializer functype'_parser = ((aux_functype_magic_serializer `LP.serialize_nondep_then` aux_vecvaltype_serializer) `LP.serialize_nondep_then` aux_vecvaltype_serializer)

let functype_serializer =
  [@inline_let] let _ = synth_functype_injective () in
  [@inline_let] let _ = synth_functype_inverse () in
  [@inline_let] let _ = assert_norm (functype_parser_kind == functype'_parser_kind) in
  LP.serialize_synth _ synth_functype functype'_serializer synth_functype_recip ()

let functype_bytesize (x:functype) : GTot nat = Seq.length (functype_serializer x)

let functype_bytesize_eq x = ()

inline_for_extraction let functype'_parser32 : LS.parser32 functype'_parser = ((aux_functype_magic_parser32 `LS.parse32_nondep_then` aux_vecvaltype_parser32) `LS.parse32_nondep_then` aux_vecvaltype_parser32)

let functype_parser32 =
  [@inline_let] let _ = synth_functype_injective () in
  [@inline_let] let _ = assert_norm (functype_parser_kind == functype'_parser_kind) in
  LS.parse32_synth _ synth_functype (fun x -> synth_functype x) functype'_parser32 ()

inline_for_extraction let functype'_serializer32 : LS.serializer32 functype'_serializer = ((aux_functype_magic_serializer32 `LS.serialize32_nondep_then` aux_vecvaltype_serializer32) `LS.serialize32_nondep_then` aux_vecvaltype_serializer32)

let functype_serializer32 =
  [@inline_let] let _ = synth_functype_injective () in
  [@inline_let] let _ = synth_functype_inverse () in
  [@inline_let] let _ = assert_norm (functype_parser_kind == functype'_parser_kind) in
  LS.serialize32_synth _ synth_functype _ functype'_serializer32 synth_functype_recip (fun x -> synth_functype_recip x) ()

inline_for_extraction let functype'_size32 : LS.size32 functype'_serializer = ((aux_functype_magic_size32 `LS.size32_nondep_then` aux_vecvaltype_size32) `LS.size32_nondep_then` aux_vecvaltype_size32)

let functype_size32 =
  [@inline_let] let _ = synth_functype_injective () in
  [@inline_let] let _ = synth_functype_inverse () in
  [@inline_let] let _ = assert_norm (functype_parser_kind == functype'_parser_kind) in
  LS.size32_synth _ synth_functype _ functype'_size32 synth_functype_recip (fun x -> synth_functype_recip x) ()

let functype_bytesize_eqn x =
  [@inline_let] let _ = synth_functype_injective () in
  [@inline_let] let _ = synth_functype_inverse () in
  [@inline_let] let _ = assert_norm (functype_parser_kind == functype'_parser_kind) in
  LP.serialize_synth_eq _ synth_functype functype'_serializer synth_functype_recip () x;
LP.length_serialize_nondep_then aux_functype_magic_serializer aux_vecvaltype_serializer x.m x.params;
LP.length_serialize_nondep_then (aux_functype_magic_serializer `LP.serialize_nondep_then` aux_vecvaltype_serializer) aux_vecvaltype_serializer (x.m, x.params) x.results;
  (aux_functype_magic_bytesize_eq (x.m));
  (aux_vecvaltype_bytesize_eq (x.params));
  (aux_vecvaltype_bytesize_eq (x.results));
  assert(functype_bytesize x == Seq.length (LP.serialize aux_functype_magic_serializer x.m) + Seq.length (LP.serialize aux_vecvaltype_serializer x.params) + Seq.length (LP.serialize aux_vecvaltype_serializer x.results))

