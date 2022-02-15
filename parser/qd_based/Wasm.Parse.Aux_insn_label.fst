module Wasm.Parse.Aux_insn_label

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

[@LP.Norm] inline_for_extraction let aux_insn_label_enum : LP.enum aux_insn_label U8.t =
  [@inline_let] let e = [
    Unreachable, 0z;
    Nop, 1z;
    Block, 2z;
    Loop, 3z;
    If_, 4z;
    Br, 12z;
    Br_if, 13z;
    Br_table, 14z;
    Ret, 15z;
    Call, 16z;
    Call_indirect, 17z;
    Drop, 26z;
    Select_, 27z;
    Local_get, 32z;
    Local_set, 33z;
    Local_tee, 34z;
    Global_get, 35z;
    Global_set, 36z;
    I32_load, 40z;
    I64_load, 41z;
    F32_load, 42z;
    F64_load, 43z;
    I32_load8_s, 44z;
    I32_load8_u, 45z;
    I32_load16_s, 46z;
    I32_load16_u, 47z;
    I64_load8_s, 48z;
    I64_load8_u, 49z;
    I64_load16_s, 50z;
    I64_load16_u, 51z;
    I64_load32_s, 52z;
    I64_load32_u, 53z;
    I32_store, 54z;
    I64_store, 55z;
    F32_store, 56z;
    F64_store, 57z;
    I32_store8, 58z;
    I32_store16, 59z;
    I64_store8, 60z;
    I64_store16, 61z;
    I64_store32, 62z;
    Memory_size, 63z;
    Memory_grow, 64z;
    I32_const, 65z;
    I64_const, 66z;
    F32_const, 67z;
    F64_const, 68z;
    I32_eqz, 69z;
    I32_eq, 70z;
    I32_ne, 71z;
    I32_lt_s, 72z;
    I32_lt_u, 73z;
    I32_gt_s, 74z;
    I32_gt_u, 75z;
    I32_le_s, 76z;
    I32_le_u, 77z;
    I32_ge_s, 78z;
    I32_ge_u, 79z;
    I64_eqz, 80z;
    I64_eq, 81z;
    I64_ne, 82z;
    I64_lt_s, 83z;
    I64_lt_u, 84z;
    I64_gt_s, 85z;
    I64_gt_u, 86z;
    I64_le_s, 87z;
    I64_le_u, 88z;
    I64_ge_s, 89z;
    I64_ge_u, 90z;
    F32_eq, 91z;
    F32_ne, 92z;
    F32_lt, 93z;
    F32_gt, 94z;
    F32_le, 95z;
    F32_ge, 96z;
    F64_eq, 97z;
    F64_ne, 98z;
    F64_lt, 99z;
    F64_gt, 100z;
    F64_le, 101z;
    F64_ge, 102z;
    I32_clz, 103z;
    I32_ctz, 104z;
    I32_popcnt, 105z;
    I32_add, 106z;
    I32_sub, 107z;
    I32_mul, 108z;
    I32_div_s, 109z;
    I32_div_u, 110z;
    I32_rem_s, 111z;
    I32_rem_u, 112z;
    I32_and, 113z;
    I32_or, 114z;
    I32_xor, 115z;
    I32_shl, 116z;
    I32_shr_s, 117z;
    I32_shr_u, 118z;
    I32_rotl, 119z;
    I32_rotr, 120z;
    I64_clz, 121z;
    I64_ctz, 122z;
    I64_popcnt, 123z;
    I64_add, 124z;
    I64_sub, 125z;
    I64_mul, 126z;
    I64_div_s, 127z;
    I64_div_u, 128z;
    I64_rem_s, 129z;
    I64_rem_u, 130z;
    I64_and, 131z;
    I64_or, 132z;
    I64_xor, 133z;
    I64_shl, 134z;
    I64_shr_s, 135z;
    I64_shr_u, 136z;
    I64_rotl, 137z;
    I64_rotr, 138z;
    F32_abs, 139z;
    F32_neg, 140z;
    F32_ceil, 141z;
    F32_floor, 142z;
    F32_trunc, 143z;
    F32_nearest, 144z;
    F32_sqrt, 145z;
    F32_add, 146z;
    F32_sub, 147z;
    F32_mul, 148z;
    F32_div, 149z;
    F32_min, 150z;
    F32_max, 151z;
    F32_copysign, 152z;
    F64_abs, 153z;
    F64_neg, 154z;
    F64_ceil, 155z;
    F64_floor, 156z;
    F64_trunc, 157z;
    F64_nearest, 158z;
    F64_sqrt, 159z;
    F64_add, 160z;
    F64_sub, 161z;
    F64_mul, 162z;
    F64_div, 163z;
    F64_min, 164z;
    F64_max, 165z;
    F64_copysign, 166z;
    I32_wrap_i64, 167z;
    I32_trunc_f32_s, 168z;
    I32_trunc_f32_u, 169z;
    I32_trunc_f64_s, 170z;
    I32_trunc_f64_u, 171z;
    I64_extend_i32_s, 172z;
    I64_extend_i32_u, 173z;
    I64_trunc_f32_s, 174z;
    I64_trunc_f32_u, 175z;
    I64_trunc_f64_s, 176z;
    I64_trunc_f64_u, 177z;
    F32_convert_i32_s, 178z;
    F32_convert_i32_u, 179z;
    F32_convert_i64_s, 180z;
    F32_convert_i64_u, 181z;
    F32_demote_f64, 182z;
    F64_convert_i32_s, 183z;
    F64_convert_i32_u, 184z;
    F64_convert_i64_s, 185z;
    F64_convert_i64_u, 186z;
    F64_promote_f32, 187z;
    I32_reinterpret_f32, 188z;
    I64_reinterpret_f64, 189z;
    F32_reinterpret_i32, 190z;
    F64_reinterpret_i64, 191z;
    End_of_contiguous_instructions, 255z;
  ] in
  [@inline_let] let _ =
    assert_norm (L.noRepeats (LP.list_map fst e))
  in
  [@inline_let] let _ = 
    assert_norm (L.noRepeats (LP.list_map snd e))
  in e

noextract let aux_insn_label_repr_parser = LPI.parse_u8

noextract let aux_insn_label_repr_serializer = LPI.serialize_u8

inline_for_extraction noextract let aux_insn_label_repr_parser32 = LS.parse32_u8

inline_for_extraction noextract let aux_insn_label_repr_serializer32 = LS.serialize32_u8

inline_for_extraction noextract let aux_insn_label_repr_size32 = LS.size32_u8

inline_for_extraction let synth_aux_insn_label (x: LP.enum_key aux_insn_label_enum) : Tot aux_insn_label = x

inline_for_extraction let synth_aux_insn_label_inv (x: aux_insn_label) : Tot (LP.enum_key aux_insn_label_enum) =
  [@inline_let] let _ : squash (LP.list_mem x (LP.list_map fst aux_insn_label_enum)) =
    _ by (LP.synth_maybe_enum_key_inv_unknown_tac x)
  in
  x

let lemma_synth_aux_insn_label_inj () : Lemma
  (LP.synth_injective synth_aux_insn_label) = ()

let lemma_synth_aux_insn_label_inv () : Lemma
  (LP.synth_inverse synth_aux_insn_label synth_aux_insn_label_inv) = ()

noextract let parse_aux_insn_label_key : LP.parser _ (LP.enum_key aux_insn_label_enum) =
  LP.parse_enum_key aux_insn_label_repr_parser aux_insn_label_enum

noextract let serialize_aux_insn_label_key : LP.serializer parse_aux_insn_label_key =
  LP.serialize_enum_key aux_insn_label_repr_parser aux_insn_label_repr_serializer aux_insn_label_enum

noextract let aux_insn_label_parser : LP.parser _ aux_insn_label =
  lemma_synth_aux_insn_label_inj ();
  parse_aux_insn_label_key `LP.parse_synth` synth_aux_insn_label

noextract let aux_insn_label_serializer : LP.serializer aux_insn_label_parser =
  lemma_synth_aux_insn_label_inj ();
  lemma_synth_aux_insn_label_inv ();
  LP.serialize_synth _ synth_aux_insn_label serialize_aux_insn_label_key synth_aux_insn_label_inv ()

let aux_insn_label_bytesize (x:aux_insn_label) : GTot nat = Seq.length (aux_insn_label_serializer x)

let aux_insn_label_bytesize_eq x = ()

let parse32_aux_insn_label_key : LS.parser32 parse_aux_insn_label_key =
  FStar.Tactics.synth_by_tactic (LS.parse32_enum_key_tac aux_insn_label_repr_parser32 aux_insn_label_enum)

let aux_insn_label_parser32 : LS.parser32 aux_insn_label_parser =
  lemma_synth_aux_insn_label_inj ();
  LS.parse32_synth _ synth_aux_insn_label (fun x->synth_aux_insn_label x) parse32_aux_insn_label_key ()

let serialize32_aux_insn_label_key : LS.serializer32 serialize_aux_insn_label_key =
  FStar.Tactics.synth_by_tactic (LS.serialize32_enum_key_gen_tac
    aux_insn_label_repr_serializer32 aux_insn_label_enum)

let aux_insn_label_serializer32 : LS.serializer32 aux_insn_label_serializer =
  lemma_synth_aux_insn_label_inj ();
  lemma_synth_aux_insn_label_inv ();
  LS.serialize32_synth _ synth_aux_insn_label _ serialize32_aux_insn_label_key synth_aux_insn_label_inv (fun x->synth_aux_insn_label_inv x) ()

let aux_insn_label_size32 =
  [@inline_let] let _ = assert_norm (LS.size32_constant_precond aux_insn_label_serializer 1ul) in
  LS.size32_constant aux_insn_label_serializer 1ul ()
