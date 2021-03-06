module Wasm.Parse.Memarg

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

type memarg' = (U32.t & U32.t)

inline_for_extraction let synth_memarg (x: memarg') : memarg =
  match x with (align,offset) -> {
    align = align;
    offset = offset;
  }

inline_for_extraction let synth_memarg_recip (x: memarg) : memarg' = (x.align,x.offset)

let synth_memarg_recip_inverse () : Lemma (LP.synth_inverse synth_memarg_recip synth_memarg) = ()

let synth_memarg_injective () : Lemma (LP.synth_injective synth_memarg) =
  LP.synth_inverse_synth_injective synth_memarg_recip synth_memarg;
  synth_memarg_recip_inverse ()

let synth_memarg_inverse () : Lemma (LP.synth_inverse synth_memarg synth_memarg_recip) =
  assert_norm (LP.synth_inverse synth_memarg synth_memarg_recip)

let synth_memarg_recip_injective () : Lemma (LP.synth_injective synth_memarg_recip) =
  synth_memarg_recip_inverse ();
  LP.synth_inverse_synth_injective synth_memarg synth_memarg_recip

noextract let memarg'_parser : LP.parser _ memarg' = (LPI.parse_u32 `LP.nondep_then` LPI.parse_u32)

noextract let memarg'_parser_kind = LP.get_parser_kind memarg'_parser

let memarg_parser =
  synth_memarg_injective ();
  assert_norm (memarg_parser_kind == memarg'_parser_kind);
  memarg'_parser `LP.parse_synth` synth_memarg

noextract let memarg'_serializer : LP.serializer memarg'_parser = (LPI.serialize_u32 `LP.serialize_nondep_then` LPI.serialize_u32)

let memarg_serializer =
  [@inline_let] let _ = synth_memarg_injective () in
  [@inline_let] let _ = synth_memarg_inverse () in
  [@inline_let] let _ = assert_norm (memarg_parser_kind == memarg'_parser_kind) in
  LP.serialize_synth _ synth_memarg memarg'_serializer synth_memarg_recip ()

let memarg_bytesize (x:memarg) : GTot nat = Seq.length (memarg_serializer x)

let memarg_bytesize_eq x = ()

inline_for_extraction let memarg'_parser32 : LS.parser32 memarg'_parser = (LS.parse32_u32 `LS.parse32_nondep_then` LS.parse32_u32)

let memarg_parser32 =
  [@inline_let] let _ = synth_memarg_injective () in
  [@inline_let] let _ = assert_norm (memarg_parser_kind == memarg'_parser_kind) in
  LS.parse32_synth _ synth_memarg (fun x -> synth_memarg x) memarg'_parser32 ()

inline_for_extraction let memarg'_serializer32 : LS.serializer32 memarg'_serializer = (LS.serialize32_u32 `LS.serialize32_nondep_then` LS.serialize32_u32)

let memarg_serializer32 =
  [@inline_let] let _ = synth_memarg_injective () in
  [@inline_let] let _ = synth_memarg_inverse () in
  [@inline_let] let _ = assert_norm (memarg_parser_kind == memarg'_parser_kind) in
  LS.serialize32_synth _ synth_memarg _ memarg'_serializer32 synth_memarg_recip (fun x -> synth_memarg_recip x) ()

inline_for_extraction let memarg'_size32 : LS.size32 memarg'_serializer = (LS.size32_u32 `LS.size32_nondep_then` LS.size32_u32)

let memarg_size32 =
  [@inline_let] let _ = synth_memarg_injective () in
  [@inline_let] let _ = synth_memarg_inverse () in
  [@inline_let] let _ = assert_norm (memarg_parser_kind == memarg'_parser_kind) in
  LS.size32_synth _ synth_memarg _ memarg'_size32 synth_memarg_recip (fun x -> synth_memarg_recip x) ()

let memarg_bytesize_eqn x =
  [@inline_let] let _ = synth_memarg_injective () in
  [@inline_let] let _ = synth_memarg_inverse () in
  [@inline_let] let _ = assert_norm (memarg_parser_kind == memarg'_parser_kind) in
  LP.serialize_synth_eq _ synth_memarg memarg'_serializer synth_memarg_recip () x;
LP.length_serialize_nondep_then LPI.serialize_u32 LPI.serialize_u32 x.align x.offset;
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.align)) == 4));
  (assert (FStar.Seq.length (LP.serialize LP.serialize_u32 (x.offset)) == 4));
  assert(memarg_bytesize x == Seq.length (LP.serialize LPI.serialize_u32 x.align) + Seq.length (LP.serialize LPI.serialize_u32 x.offset))

