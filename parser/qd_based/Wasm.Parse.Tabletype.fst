module Wasm.Parse.Tabletype

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

type tabletype' = (elemtype & limits)

inline_for_extraction let synth_tabletype (x: tabletype') : tabletype =
  match x with (et,lim) -> {
    et = et;
    lim = lim;
  }

inline_for_extraction let synth_tabletype_recip (x: tabletype) : tabletype' = (x.et,x.lim)

let synth_tabletype_recip_inverse () : Lemma (LP.synth_inverse synth_tabletype_recip synth_tabletype) = ()

let synth_tabletype_injective () : Lemma (LP.synth_injective synth_tabletype) =
  LP.synth_inverse_synth_injective synth_tabletype_recip synth_tabletype;
  synth_tabletype_recip_inverse ()

let synth_tabletype_inverse () : Lemma (LP.synth_inverse synth_tabletype synth_tabletype_recip) =
  assert_norm (LP.synth_inverse synth_tabletype synth_tabletype_recip)

let synth_tabletype_recip_injective () : Lemma (LP.synth_injective synth_tabletype_recip) =
  synth_tabletype_recip_inverse ();
  LP.synth_inverse_synth_injective synth_tabletype synth_tabletype_recip

noextract let tabletype'_parser : LP.parser _ tabletype' = (elemtype_parser `LP.nondep_then` limits_parser)

noextract let tabletype'_parser_kind = LP.get_parser_kind tabletype'_parser

let tabletype_parser =
  synth_tabletype_injective ();
  assert_norm (tabletype_parser_kind == tabletype'_parser_kind);
  tabletype'_parser `LP.parse_synth` synth_tabletype

noextract let tabletype'_serializer : LP.serializer tabletype'_parser = (elemtype_serializer `LP.serialize_nondep_then` limits_serializer)

let tabletype_serializer =
  [@inline_let] let _ = synth_tabletype_injective () in
  [@inline_let] let _ = synth_tabletype_inverse () in
  [@inline_let] let _ = assert_norm (tabletype_parser_kind == tabletype'_parser_kind) in
  LP.serialize_synth _ synth_tabletype tabletype'_serializer synth_tabletype_recip ()

let tabletype_bytesize (x:tabletype) : GTot nat = Seq.length (tabletype_serializer x)

let tabletype_bytesize_eq x = ()

inline_for_extraction let tabletype'_parser32 : LS.parser32 tabletype'_parser = (elemtype_parser32 `LS.parse32_nondep_then` limits_parser32)

let tabletype_parser32 =
  [@inline_let] let _ = synth_tabletype_injective () in
  [@inline_let] let _ = assert_norm (tabletype_parser_kind == tabletype'_parser_kind) in
  LS.parse32_synth _ synth_tabletype (fun x -> synth_tabletype x) tabletype'_parser32 ()

inline_for_extraction let tabletype'_serializer32 : LS.serializer32 tabletype'_serializer = (elemtype_serializer32 `LS.serialize32_nondep_then` limits_serializer32)

let tabletype_serializer32 =
  [@inline_let] let _ = synth_tabletype_injective () in
  [@inline_let] let _ = synth_tabletype_inverse () in
  [@inline_let] let _ = assert_norm (tabletype_parser_kind == tabletype'_parser_kind) in
  LS.serialize32_synth _ synth_tabletype _ tabletype'_serializer32 synth_tabletype_recip (fun x -> synth_tabletype_recip x) ()

inline_for_extraction let tabletype'_size32 : LS.size32 tabletype'_serializer = (elemtype_size32 `LS.size32_nondep_then` limits_size32)

let tabletype_size32 =
  [@inline_let] let _ = synth_tabletype_injective () in
  [@inline_let] let _ = synth_tabletype_inverse () in
  [@inline_let] let _ = assert_norm (tabletype_parser_kind == tabletype'_parser_kind) in
  LS.size32_synth _ synth_tabletype _ tabletype'_size32 synth_tabletype_recip (fun x -> synth_tabletype_recip x) ()

let tabletype_bytesize_eqn x =
  [@inline_let] let _ = synth_tabletype_injective () in
  [@inline_let] let _ = synth_tabletype_inverse () in
  [@inline_let] let _ = assert_norm (tabletype_parser_kind == tabletype'_parser_kind) in
  LP.serialize_synth_eq _ synth_tabletype tabletype'_serializer synth_tabletype_recip () x;
LP.length_serialize_nondep_then elemtype_serializer limits_serializer x.et x.lim;
  (elemtype_bytesize_eq (x.et));
  (limits_bytesize_eq (x.lim));
  assert(tabletype_bytesize x == Seq.length (LP.serialize elemtype_serializer x.et) + Seq.length (LP.serialize limits_serializer x.lim))
