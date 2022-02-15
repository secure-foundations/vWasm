module Wasm.Parse.Aux_constbyte0

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

[@LP.Norm] inline_for_extraction let aux_constbyte0_enum : LP.enum aux_constbyte0 U8.t =
  [@inline_let] let e = [
    Zero, 0z;
  ] in
  [@inline_let] let _ =
    assert_norm (L.noRepeats (LP.list_map fst e))
  in
  [@inline_let] let _ = 
    assert_norm (L.noRepeats (LP.list_map snd e))
  in e

noextract let aux_constbyte0_repr_parser = LPI.parse_u8

noextract let aux_constbyte0_repr_serializer = LPI.serialize_u8

inline_for_extraction noextract let aux_constbyte0_repr_parser32 = LS.parse32_u8

inline_for_extraction noextract let aux_constbyte0_repr_serializer32 = LS.serialize32_u8

inline_for_extraction noextract let aux_constbyte0_repr_size32 = LS.size32_u8

inline_for_extraction let synth_aux_constbyte0 (x: LP.enum_key aux_constbyte0_enum) : Tot aux_constbyte0 = x

inline_for_extraction let synth_aux_constbyte0_inv (x: aux_constbyte0) : Tot (LP.enum_key aux_constbyte0_enum) =
  [@inline_let] let _ : squash (LP.list_mem x (LP.list_map fst aux_constbyte0_enum)) =
    _ by (LP.synth_maybe_enum_key_inv_unknown_tac x)
  in
  x

let lemma_synth_aux_constbyte0_inj () : Lemma
  (LP.synth_injective synth_aux_constbyte0) = ()

let lemma_synth_aux_constbyte0_inv () : Lemma
  (LP.synth_inverse synth_aux_constbyte0 synth_aux_constbyte0_inv) = ()

noextract let parse_aux_constbyte0_key : LP.parser _ (LP.enum_key aux_constbyte0_enum) =
  LP.parse_enum_key aux_constbyte0_repr_parser aux_constbyte0_enum

noextract let serialize_aux_constbyte0_key : LP.serializer parse_aux_constbyte0_key =
  LP.serialize_enum_key aux_constbyte0_repr_parser aux_constbyte0_repr_serializer aux_constbyte0_enum

noextract let aux_constbyte0_parser : LP.parser _ aux_constbyte0 =
  lemma_synth_aux_constbyte0_inj ();
  parse_aux_constbyte0_key `LP.parse_synth` synth_aux_constbyte0

noextract let aux_constbyte0_serializer : LP.serializer aux_constbyte0_parser =
  lemma_synth_aux_constbyte0_inj ();
  lemma_synth_aux_constbyte0_inv ();
  LP.serialize_synth _ synth_aux_constbyte0 serialize_aux_constbyte0_key synth_aux_constbyte0_inv ()

let aux_constbyte0_bytesize (x:aux_constbyte0) : GTot nat = Seq.length (aux_constbyte0_serializer x)

let aux_constbyte0_bytesize_eq x = ()

let parse32_aux_constbyte0_key : LS.parser32 parse_aux_constbyte0_key =
  FStar.Tactics.synth_by_tactic (LS.parse32_enum_key_tac aux_constbyte0_repr_parser32 aux_constbyte0_enum)

let aux_constbyte0_parser32 : LS.parser32 aux_constbyte0_parser =
  lemma_synth_aux_constbyte0_inj ();
  LS.parse32_synth _ synth_aux_constbyte0 (fun x->synth_aux_constbyte0 x) parse32_aux_constbyte0_key ()

let serialize32_aux_constbyte0_key : LS.serializer32 serialize_aux_constbyte0_key =
  FStar.Tactics.synth_by_tactic (LS.serialize32_enum_key_gen_tac
    aux_constbyte0_repr_serializer32 aux_constbyte0_enum)

let aux_constbyte0_serializer32 : LS.serializer32 aux_constbyte0_serializer =
  lemma_synth_aux_constbyte0_inj ();
  lemma_synth_aux_constbyte0_inv ();
  LS.serialize32_synth _ synth_aux_constbyte0 _ serialize32_aux_constbyte0_key synth_aux_constbyte0_inv (fun x->synth_aux_constbyte0_inv x) ()

let aux_constbyte0_size32 =
  [@inline_let] let _ = assert_norm (LS.size32_constant_precond aux_constbyte0_serializer 1ul) in
  LS.size32_constant aux_constbyte0_serializer 1ul ()

