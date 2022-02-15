module Wasm.Parse.Instr

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec.Base
module LS = LowParse.SLow.Base
module LPI = LowParse.Spec.AllIntegers
module L = FStar.List.Tot
module BY = FStar.Bytes

open Wasm.Parse.Aux_insn_label
open Wasm.Parse.Aux_block
open Wasm.Parse.Aux_loop
open Wasm.Parse.Aux_if
open Wasm.Parse.Labelidx
open Wasm.Parse.Aux_br_table
open Wasm.Parse.Funcidx
open Wasm.Parse.Aux_call_indirect
open Wasm.Parse.Localidx
open Wasm.Parse.Globalidx
open Wasm.Parse.Memarg
open Wasm.Parse.Aux_constbyte0
open Wasm.Parse.F32
open Wasm.Parse.F64

type instr =
  | Rest_block of aux_block
  | Rest_loop of aux_loop
  | Rest_if_ of aux_if
  | Rest_br of labelidx
  | Rest_br_if of labelidx
  | Rest_br_table of aux_br_table
  | Rest_call of funcidx
  | Rest_call_indirect of aux_call_indirect
  | Rest_local_get of localidx
  | Rest_local_set of localidx
  | Rest_local_tee of localidx
  | Rest_global_get of globalidx
  | Rest_global_set of globalidx
  | Rest_i32_load of memarg
  | Rest_i64_load of memarg
  | Rest_f32_load of memarg
  | Rest_f64_load of memarg
  | Rest_i32_load8_s of memarg
  | Rest_i32_load8_u of memarg
  | Rest_i32_load16_s of memarg
  | Rest_i32_load16_u of memarg
  | Rest_i64_load8_s of memarg
  | Rest_i64_load8_u of memarg
  | Rest_i64_load16_s of memarg
  | Rest_i64_load16_u of memarg
  | Rest_i64_load32_s of memarg
  | Rest_i64_load32_u of memarg
  | Rest_i32_store of memarg
  | Rest_i64_store of memarg
  | Rest_f32_store of memarg
  | Rest_f64_store of memarg
  | Rest_i32_store8 of memarg
  | Rest_i32_store16 of memarg
  | Rest_i64_store8 of memarg
  | Rest_i64_store16 of memarg
  | Rest_i64_store32 of memarg
  | Rest_memory_size of aux_constbyte0
  | Rest_memory_grow of aux_constbyte0
  | Rest_i32_const of U32.t
  | Rest_i64_const of U64.t
  | Rest_f32_const of f32
  | Rest_f64_const of f64
  | Rest_end_of_contiguous_instructions of unit
  | Rest_f64_reinterpret_i64 of unit
  | Rest_f32_reinterpret_i32 of unit
  | Rest_i64_reinterpret_f64 of unit
  | Rest_i32_reinterpret_f32 of unit
  | Rest_f64_promote_f32 of unit
  | Rest_f64_convert_i64_u of unit
  | Rest_f64_convert_i64_s of unit
  | Rest_f64_convert_i32_u of unit
  | Rest_f64_convert_i32_s of unit
  | Rest_f32_demote_f64 of unit
  | Rest_f32_convert_i64_u of unit
  | Rest_f32_convert_i64_s of unit
  | Rest_f32_convert_i32_u of unit
  | Rest_f32_convert_i32_s of unit
  | Rest_i64_trunc_f64_u of unit
  | Rest_i64_trunc_f64_s of unit
  | Rest_i64_trunc_f32_u of unit
  | Rest_i64_trunc_f32_s of unit
  | Rest_i64_extend_i32_u of unit
  | Rest_i64_extend_i32_s of unit
  | Rest_i32_trunc_f64_u of unit
  | Rest_i32_trunc_f64_s of unit
  | Rest_i32_trunc_f32_u of unit
  | Rest_i32_trunc_f32_s of unit
  | Rest_i32_wrap_i64 of unit
  | Rest_f64_copysign of unit
  | Rest_f64_max of unit
  | Rest_f64_min of unit
  | Rest_f64_div of unit
  | Rest_f64_mul of unit
  | Rest_f64_sub of unit
  | Rest_f64_add of unit
  | Rest_f64_sqrt of unit
  | Rest_f64_nearest of unit
  | Rest_f64_trunc of unit
  | Rest_f64_floor of unit
  | Rest_f64_ceil of unit
  | Rest_f64_neg of unit
  | Rest_f64_abs of unit
  | Rest_f32_copysign of unit
  | Rest_f32_max of unit
  | Rest_f32_min of unit
  | Rest_f32_div of unit
  | Rest_f32_mul of unit
  | Rest_f32_sub of unit
  | Rest_f32_add of unit
  | Rest_f32_sqrt of unit
  | Rest_f32_nearest of unit
  | Rest_f32_trunc of unit
  | Rest_f32_floor of unit
  | Rest_f32_ceil of unit
  | Rest_f32_neg of unit
  | Rest_f32_abs of unit
  | Rest_i64_rotr of unit
  | Rest_i64_rotl of unit
  | Rest_i64_shr_u of unit
  | Rest_i64_shr_s of unit
  | Rest_i64_shl of unit
  | Rest_i64_xor of unit
  | Rest_i64_or of unit
  | Rest_i64_and of unit
  | Rest_i64_rem_u of unit
  | Rest_i64_rem_s of unit
  | Rest_i64_div_u of unit
  | Rest_i64_div_s of unit
  | Rest_i64_mul of unit
  | Rest_i64_sub of unit
  | Rest_i64_add of unit
  | Rest_i64_popcnt of unit
  | Rest_i64_ctz of unit
  | Rest_i64_clz of unit
  | Rest_i32_rotr of unit
  | Rest_i32_rotl of unit
  | Rest_i32_shr_u of unit
  | Rest_i32_shr_s of unit
  | Rest_i32_shl of unit
  | Rest_i32_xor of unit
  | Rest_i32_or of unit
  | Rest_i32_and of unit
  | Rest_i32_rem_u of unit
  | Rest_i32_rem_s of unit
  | Rest_i32_div_u of unit
  | Rest_i32_div_s of unit
  | Rest_i32_mul of unit
  | Rest_i32_sub of unit
  | Rest_i32_add of unit
  | Rest_i32_popcnt of unit
  | Rest_i32_ctz of unit
  | Rest_i32_clz of unit
  | Rest_f64_ge of unit
  | Rest_f64_le of unit
  | Rest_f64_gt of unit
  | Rest_f64_lt of unit
  | Rest_f64_ne of unit
  | Rest_f64_eq of unit
  | Rest_f32_ge of unit
  | Rest_f32_le of unit
  | Rest_f32_gt of unit
  | Rest_f32_lt of unit
  | Rest_f32_ne of unit
  | Rest_f32_eq of unit
  | Rest_i64_ge_u of unit
  | Rest_i64_ge_s of unit
  | Rest_i64_le_u of unit
  | Rest_i64_le_s of unit
  | Rest_i64_gt_u of unit
  | Rest_i64_gt_s of unit
  | Rest_i64_lt_u of unit
  | Rest_i64_lt_s of unit
  | Rest_i64_ne of unit
  | Rest_i64_eq of unit
  | Rest_i64_eqz of unit
  | Rest_i32_ge_u of unit
  | Rest_i32_ge_s of unit
  | Rest_i32_le_u of unit
  | Rest_i32_le_s of unit
  | Rest_i32_gt_u of unit
  | Rest_i32_gt_s of unit
  | Rest_i32_lt_u of unit
  | Rest_i32_lt_s of unit
  | Rest_i32_ne of unit
  | Rest_i32_eq of unit
  | Rest_i32_eqz of unit
  | Rest_select_ of unit
  | Rest_drop of unit
  | Rest_ret of unit
  | Rest_nop of unit
  | Rest_unreachable of unit

inline_for_extraction let tag_of_instr (x:instr) : aux_insn_label = match x with
  | Rest_block _ -> Block
  | Rest_loop _ -> Loop
  | Rest_if_ _ -> If_
  | Rest_br _ -> Br
  | Rest_br_if _ -> Br_if
  | Rest_br_table _ -> Br_table
  | Rest_call _ -> Call
  | Rest_call_indirect _ -> Call_indirect
  | Rest_local_get _ -> Local_get
  | Rest_local_set _ -> Local_set
  | Rest_local_tee _ -> Local_tee
  | Rest_global_get _ -> Global_get
  | Rest_global_set _ -> Global_set
  | Rest_i32_load _ -> I32_load
  | Rest_i64_load _ -> I64_load
  | Rest_f32_load _ -> F32_load
  | Rest_f64_load _ -> F64_load
  | Rest_i32_load8_s _ -> I32_load8_s
  | Rest_i32_load8_u _ -> I32_load8_u
  | Rest_i32_load16_s _ -> I32_load16_s
  | Rest_i32_load16_u _ -> I32_load16_u
  | Rest_i64_load8_s _ -> I64_load8_s
  | Rest_i64_load8_u _ -> I64_load8_u
  | Rest_i64_load16_s _ -> I64_load16_s
  | Rest_i64_load16_u _ -> I64_load16_u
  | Rest_i64_load32_s _ -> I64_load32_s
  | Rest_i64_load32_u _ -> I64_load32_u
  | Rest_i32_store _ -> I32_store
  | Rest_i64_store _ -> I64_store
  | Rest_f32_store _ -> F32_store
  | Rest_f64_store _ -> F64_store
  | Rest_i32_store8 _ -> I32_store8
  | Rest_i32_store16 _ -> I32_store16
  | Rest_i64_store8 _ -> I64_store8
  | Rest_i64_store16 _ -> I64_store16
  | Rest_i64_store32 _ -> I64_store32
  | Rest_memory_size _ -> Memory_size
  | Rest_memory_grow _ -> Memory_grow
  | Rest_i32_const _ -> I32_const
  | Rest_i64_const _ -> I64_const
  | Rest_f32_const _ -> F32_const
  | Rest_f64_const _ -> F64_const
  | Rest_end_of_contiguous_instructions _ -> End_of_contiguous_instructions
  | Rest_f64_reinterpret_i64 _ -> F64_reinterpret_i64
  | Rest_f32_reinterpret_i32 _ -> F32_reinterpret_i32
  | Rest_i64_reinterpret_f64 _ -> I64_reinterpret_f64
  | Rest_i32_reinterpret_f32 _ -> I32_reinterpret_f32
  | Rest_f64_promote_f32 _ -> F64_promote_f32
  | Rest_f64_convert_i64_u _ -> F64_convert_i64_u
  | Rest_f64_convert_i64_s _ -> F64_convert_i64_s
  | Rest_f64_convert_i32_u _ -> F64_convert_i32_u
  | Rest_f64_convert_i32_s _ -> F64_convert_i32_s
  | Rest_f32_demote_f64 _ -> F32_demote_f64
  | Rest_f32_convert_i64_u _ -> F32_convert_i64_u
  | Rest_f32_convert_i64_s _ -> F32_convert_i64_s
  | Rest_f32_convert_i32_u _ -> F32_convert_i32_u
  | Rest_f32_convert_i32_s _ -> F32_convert_i32_s
  | Rest_i64_trunc_f64_u _ -> I64_trunc_f64_u
  | Rest_i64_trunc_f64_s _ -> I64_trunc_f64_s
  | Rest_i64_trunc_f32_u _ -> I64_trunc_f32_u
  | Rest_i64_trunc_f32_s _ -> I64_trunc_f32_s
  | Rest_i64_extend_i32_u _ -> I64_extend_i32_u
  | Rest_i64_extend_i32_s _ -> I64_extend_i32_s
  | Rest_i32_trunc_f64_u _ -> I32_trunc_f64_u
  | Rest_i32_trunc_f64_s _ -> I32_trunc_f64_s
  | Rest_i32_trunc_f32_u _ -> I32_trunc_f32_u
  | Rest_i32_trunc_f32_s _ -> I32_trunc_f32_s
  | Rest_i32_wrap_i64 _ -> I32_wrap_i64
  | Rest_f64_copysign _ -> F64_copysign
  | Rest_f64_max _ -> F64_max
  | Rest_f64_min _ -> F64_min
  | Rest_f64_div _ -> F64_div
  | Rest_f64_mul _ -> F64_mul
  | Rest_f64_sub _ -> F64_sub
  | Rest_f64_add _ -> F64_add
  | Rest_f64_sqrt _ -> F64_sqrt
  | Rest_f64_nearest _ -> F64_nearest
  | Rest_f64_trunc _ -> F64_trunc
  | Rest_f64_floor _ -> F64_floor
  | Rest_f64_ceil _ -> F64_ceil
  | Rest_f64_neg _ -> F64_neg
  | Rest_f64_abs _ -> F64_abs
  | Rest_f32_copysign _ -> F32_copysign
  | Rest_f32_max _ -> F32_max
  | Rest_f32_min _ -> F32_min
  | Rest_f32_div _ -> F32_div
  | Rest_f32_mul _ -> F32_mul
  | Rest_f32_sub _ -> F32_sub
  | Rest_f32_add _ -> F32_add
  | Rest_f32_sqrt _ -> F32_sqrt
  | Rest_f32_nearest _ -> F32_nearest
  | Rest_f32_trunc _ -> F32_trunc
  | Rest_f32_floor _ -> F32_floor
  | Rest_f32_ceil _ -> F32_ceil
  | Rest_f32_neg _ -> F32_neg
  | Rest_f32_abs _ -> F32_abs
  | Rest_i64_rotr _ -> I64_rotr
  | Rest_i64_rotl _ -> I64_rotl
  | Rest_i64_shr_u _ -> I64_shr_u
  | Rest_i64_shr_s _ -> I64_shr_s
  | Rest_i64_shl _ -> I64_shl
  | Rest_i64_xor _ -> I64_xor
  | Rest_i64_or _ -> I64_or
  | Rest_i64_and _ -> I64_and
  | Rest_i64_rem_u _ -> I64_rem_u
  | Rest_i64_rem_s _ -> I64_rem_s
  | Rest_i64_div_u _ -> I64_div_u
  | Rest_i64_div_s _ -> I64_div_s
  | Rest_i64_mul _ -> I64_mul
  | Rest_i64_sub _ -> I64_sub
  | Rest_i64_add _ -> I64_add
  | Rest_i64_popcnt _ -> I64_popcnt
  | Rest_i64_ctz _ -> I64_ctz
  | Rest_i64_clz _ -> I64_clz
  | Rest_i32_rotr _ -> I32_rotr
  | Rest_i32_rotl _ -> I32_rotl
  | Rest_i32_shr_u _ -> I32_shr_u
  | Rest_i32_shr_s _ -> I32_shr_s
  | Rest_i32_shl _ -> I32_shl
  | Rest_i32_xor _ -> I32_xor
  | Rest_i32_or _ -> I32_or
  | Rest_i32_and _ -> I32_and
  | Rest_i32_rem_u _ -> I32_rem_u
  | Rest_i32_rem_s _ -> I32_rem_s
  | Rest_i32_div_u _ -> I32_div_u
  | Rest_i32_div_s _ -> I32_div_s
  | Rest_i32_mul _ -> I32_mul
  | Rest_i32_sub _ -> I32_sub
  | Rest_i32_add _ -> I32_add
  | Rest_i32_popcnt _ -> I32_popcnt
  | Rest_i32_ctz _ -> I32_ctz
  | Rest_i32_clz _ -> I32_clz
  | Rest_f64_ge _ -> F64_ge
  | Rest_f64_le _ -> F64_le
  | Rest_f64_gt _ -> F64_gt
  | Rest_f64_lt _ -> F64_lt
  | Rest_f64_ne _ -> F64_ne
  | Rest_f64_eq _ -> F64_eq
  | Rest_f32_ge _ -> F32_ge
  | Rest_f32_le _ -> F32_le
  | Rest_f32_gt _ -> F32_gt
  | Rest_f32_lt _ -> F32_lt
  | Rest_f32_ne _ -> F32_ne
  | Rest_f32_eq _ -> F32_eq
  | Rest_i64_ge_u _ -> I64_ge_u
  | Rest_i64_ge_s _ -> I64_ge_s
  | Rest_i64_le_u _ -> I64_le_u
  | Rest_i64_le_s _ -> I64_le_s
  | Rest_i64_gt_u _ -> I64_gt_u
  | Rest_i64_gt_s _ -> I64_gt_s
  | Rest_i64_lt_u _ -> I64_lt_u
  | Rest_i64_lt_s _ -> I64_lt_s
  | Rest_i64_ne _ -> I64_ne
  | Rest_i64_eq _ -> I64_eq
  | Rest_i64_eqz _ -> I64_eqz
  | Rest_i32_ge_u _ -> I32_ge_u
  | Rest_i32_ge_s _ -> I32_ge_s
  | Rest_i32_le_u _ -> I32_le_u
  | Rest_i32_le_s _ -> I32_le_s
  | Rest_i32_gt_u _ -> I32_gt_u
  | Rest_i32_gt_s _ -> I32_gt_s
  | Rest_i32_lt_u _ -> I32_lt_u
  | Rest_i32_lt_s _ -> I32_lt_s
  | Rest_i32_ne _ -> I32_ne
  | Rest_i32_eq _ -> I32_eq
  | Rest_i32_eqz _ -> I32_eqz
  | Rest_select_ _ -> Select_
  | Rest_drop _ -> Drop
  | Rest_ret _ -> Ret
  | Rest_nop _ -> Nop
  | Rest_unreachable _ -> Unreachable

inline_for_extraction noextract let instr_parser_kind = LP.strong_parser_kind 1 1029 None

noextract val instr_parser: LP.parser instr_parser_kind instr

noextract val instr_serializer: LP.serializer instr_parser

noextract val instr_bytesize (x:instr) : GTot nat

noextract val instr_bytesize_eq (x:instr) : Lemma (instr_bytesize x == Seq.length (LP.serialize instr_serializer x))

val instr_parser32: LS.parser32 instr_parser

val instr_serializer32: LS.serializer32 instr_serializer

val instr_size32: LS.size32 instr_serializer

val instr_bytesize_eqn_block (x: aux_block) : Lemma (instr_bytesize (Rest_block x) == 1 + (aux_block_bytesize (x))) [SMTPat (instr_bytesize (Rest_block x))]

val instr_bytesize_eqn_loop (x: aux_loop) : Lemma (instr_bytesize (Rest_loop x) == 1 + (aux_loop_bytesize (x))) [SMTPat (instr_bytesize (Rest_loop x))]

val instr_bytesize_eqn_if_ (x: aux_if) : Lemma (instr_bytesize (Rest_if_ x) == 1 + (aux_if_bytesize (x))) [SMTPat (instr_bytesize (Rest_if_ x))]

val instr_bytesize_eqn_br (x: labelidx) : Lemma (instr_bytesize (Rest_br x) == 1 + (labelidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_br x))]

val instr_bytesize_eqn_br_if (x: labelidx) : Lemma (instr_bytesize (Rest_br_if x) == 1 + (labelidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_br_if x))]

val instr_bytesize_eqn_br_table (x: aux_br_table) : Lemma (instr_bytesize (Rest_br_table x) == 1 + (aux_br_table_bytesize (x))) [SMTPat (instr_bytesize (Rest_br_table x))]

val instr_bytesize_eqn_call (x: funcidx) : Lemma (instr_bytesize (Rest_call x) == 1 + (funcidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_call x))]

val instr_bytesize_eqn_call_indirect (x: aux_call_indirect) : Lemma (instr_bytesize (Rest_call_indirect x) == 1 + (aux_call_indirect_bytesize (x))) [SMTPat (instr_bytesize (Rest_call_indirect x))]

val instr_bytesize_eqn_local_get (x: localidx) : Lemma (instr_bytesize (Rest_local_get x) == 1 + (localidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_local_get x))]

val instr_bytesize_eqn_local_set (x: localidx) : Lemma (instr_bytesize (Rest_local_set x) == 1 + (localidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_local_set x))]

val instr_bytesize_eqn_local_tee (x: localidx) : Lemma (instr_bytesize (Rest_local_tee x) == 1 + (localidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_local_tee x))]

val instr_bytesize_eqn_global_get (x: globalidx) : Lemma (instr_bytesize (Rest_global_get x) == 1 + (globalidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_global_get x))]

val instr_bytesize_eqn_global_set (x: globalidx) : Lemma (instr_bytesize (Rest_global_set x) == 1 + (globalidx_bytesize (x))) [SMTPat (instr_bytesize (Rest_global_set x))]

val instr_bytesize_eqn_i32_load (x: memarg) : Lemma (instr_bytesize (Rest_i32_load x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_load x))]

val instr_bytesize_eqn_i64_load (x: memarg) : Lemma (instr_bytesize (Rest_i64_load x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load x))]

val instr_bytesize_eqn_f32_load (x: memarg) : Lemma (instr_bytesize (Rest_f32_load x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_f32_load x))]

val instr_bytesize_eqn_f64_load (x: memarg) : Lemma (instr_bytesize (Rest_f64_load x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_f64_load x))]

val instr_bytesize_eqn_i32_load8_s (x: memarg) : Lemma (instr_bytesize (Rest_i32_load8_s x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_load8_s x))]

val instr_bytesize_eqn_i32_load8_u (x: memarg) : Lemma (instr_bytesize (Rest_i32_load8_u x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_load8_u x))]

val instr_bytesize_eqn_i32_load16_s (x: memarg) : Lemma (instr_bytesize (Rest_i32_load16_s x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_load16_s x))]

val instr_bytesize_eqn_i32_load16_u (x: memarg) : Lemma (instr_bytesize (Rest_i32_load16_u x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_load16_u x))]

val instr_bytesize_eqn_i64_load8_s (x: memarg) : Lemma (instr_bytesize (Rest_i64_load8_s x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load8_s x))]

val instr_bytesize_eqn_i64_load8_u (x: memarg) : Lemma (instr_bytesize (Rest_i64_load8_u x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load8_u x))]

val instr_bytesize_eqn_i64_load16_s (x: memarg) : Lemma (instr_bytesize (Rest_i64_load16_s x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load16_s x))]

val instr_bytesize_eqn_i64_load16_u (x: memarg) : Lemma (instr_bytesize (Rest_i64_load16_u x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load16_u x))]

val instr_bytesize_eqn_i64_load32_s (x: memarg) : Lemma (instr_bytesize (Rest_i64_load32_s x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load32_s x))]

val instr_bytesize_eqn_i64_load32_u (x: memarg) : Lemma (instr_bytesize (Rest_i64_load32_u x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_load32_u x))]

val instr_bytesize_eqn_i32_store (x: memarg) : Lemma (instr_bytesize (Rest_i32_store x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_store x))]

val instr_bytesize_eqn_i64_store (x: memarg) : Lemma (instr_bytesize (Rest_i64_store x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_store x))]

val instr_bytesize_eqn_f32_store (x: memarg) : Lemma (instr_bytesize (Rest_f32_store x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_f32_store x))]

val instr_bytesize_eqn_f64_store (x: memarg) : Lemma (instr_bytesize (Rest_f64_store x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_f64_store x))]

val instr_bytesize_eqn_i32_store8 (x: memarg) : Lemma (instr_bytesize (Rest_i32_store8 x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_store8 x))]

val instr_bytesize_eqn_i32_store16 (x: memarg) : Lemma (instr_bytesize (Rest_i32_store16 x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i32_store16 x))]

val instr_bytesize_eqn_i64_store8 (x: memarg) : Lemma (instr_bytesize (Rest_i64_store8 x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_store8 x))]

val instr_bytesize_eqn_i64_store16 (x: memarg) : Lemma (instr_bytesize (Rest_i64_store16 x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_store16 x))]

val instr_bytesize_eqn_i64_store32 (x: memarg) : Lemma (instr_bytesize (Rest_i64_store32 x) == 1 + (memarg_bytesize (x))) [SMTPat (instr_bytesize (Rest_i64_store32 x))]

val instr_bytesize_eqn_memory_size (x: aux_constbyte0) : Lemma (instr_bytesize (Rest_memory_size x) == 1 + (aux_constbyte0_bytesize (x))) [SMTPat (instr_bytesize (Rest_memory_size x))]

val instr_bytesize_eqn_memory_grow (x: aux_constbyte0) : Lemma (instr_bytesize (Rest_memory_grow x) == 1 + (aux_constbyte0_bytesize (x))) [SMTPat (instr_bytesize (Rest_memory_grow x))]

val instr_bytesize_eqn_i32_const (x: U32.t) : Lemma (instr_bytesize (Rest_i32_const x) == 1 + 4) [SMTPat (instr_bytesize (Rest_i32_const x))]

val instr_bytesize_eqn_i64_const (x: U64.t) : Lemma (instr_bytesize (Rest_i64_const x) == 1 + 8) [SMTPat (instr_bytesize (Rest_i64_const x))]

val instr_bytesize_eqn_f32_const (x: f32) : Lemma (instr_bytesize (Rest_f32_const x) == 1 + (f32_bytesize (x))) [SMTPat (instr_bytesize (Rest_f32_const x))]

val instr_bytesize_eqn_f64_const (x: f64) : Lemma (instr_bytesize (Rest_f64_const x) == 1 + (f64_bytesize (x))) [SMTPat (instr_bytesize (Rest_f64_const x))]

val instr_bytesize_eqn_end_of_contiguous_instructions (x: unit) : Lemma (instr_bytesize (Rest_end_of_contiguous_instructions x) == 1 + 0) [SMTPat (instr_bytesize (Rest_end_of_contiguous_instructions x))]

val instr_bytesize_eqn_f64_reinterpret_i64 (x: unit) : Lemma (instr_bytesize (Rest_f64_reinterpret_i64 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_reinterpret_i64 x))]

val instr_bytesize_eqn_f32_reinterpret_i32 (x: unit) : Lemma (instr_bytesize (Rest_f32_reinterpret_i32 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_reinterpret_i32 x))]

val instr_bytesize_eqn_i64_reinterpret_f64 (x: unit) : Lemma (instr_bytesize (Rest_i64_reinterpret_f64 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_reinterpret_f64 x))]

val instr_bytesize_eqn_i32_reinterpret_f32 (x: unit) : Lemma (instr_bytesize (Rest_i32_reinterpret_f32 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_reinterpret_f32 x))]

val instr_bytesize_eqn_f64_promote_f32 (x: unit) : Lemma (instr_bytesize (Rest_f64_promote_f32 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_promote_f32 x))]

val instr_bytesize_eqn_f64_convert_i64_u (x: unit) : Lemma (instr_bytesize (Rest_f64_convert_i64_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_convert_i64_u x))]

val instr_bytesize_eqn_f64_convert_i64_s (x: unit) : Lemma (instr_bytesize (Rest_f64_convert_i64_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_convert_i64_s x))]

val instr_bytesize_eqn_f64_convert_i32_u (x: unit) : Lemma (instr_bytesize (Rest_f64_convert_i32_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_convert_i32_u x))]

val instr_bytesize_eqn_f64_convert_i32_s (x: unit) : Lemma (instr_bytesize (Rest_f64_convert_i32_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_convert_i32_s x))]

val instr_bytesize_eqn_f32_demote_f64 (x: unit) : Lemma (instr_bytesize (Rest_f32_demote_f64 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_demote_f64 x))]

val instr_bytesize_eqn_f32_convert_i64_u (x: unit) : Lemma (instr_bytesize (Rest_f32_convert_i64_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_convert_i64_u x))]

val instr_bytesize_eqn_f32_convert_i64_s (x: unit) : Lemma (instr_bytesize (Rest_f32_convert_i64_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_convert_i64_s x))]

val instr_bytesize_eqn_f32_convert_i32_u (x: unit) : Lemma (instr_bytesize (Rest_f32_convert_i32_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_convert_i32_u x))]

val instr_bytesize_eqn_f32_convert_i32_s (x: unit) : Lemma (instr_bytesize (Rest_f32_convert_i32_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_convert_i32_s x))]

val instr_bytesize_eqn_i64_trunc_f64_u (x: unit) : Lemma (instr_bytesize (Rest_i64_trunc_f64_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_trunc_f64_u x))]

val instr_bytesize_eqn_i64_trunc_f64_s (x: unit) : Lemma (instr_bytesize (Rest_i64_trunc_f64_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_trunc_f64_s x))]

val instr_bytesize_eqn_i64_trunc_f32_u (x: unit) : Lemma (instr_bytesize (Rest_i64_trunc_f32_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_trunc_f32_u x))]

val instr_bytesize_eqn_i64_trunc_f32_s (x: unit) : Lemma (instr_bytesize (Rest_i64_trunc_f32_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_trunc_f32_s x))]

val instr_bytesize_eqn_i64_extend_i32_u (x: unit) : Lemma (instr_bytesize (Rest_i64_extend_i32_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_extend_i32_u x))]

val instr_bytesize_eqn_i64_extend_i32_s (x: unit) : Lemma (instr_bytesize (Rest_i64_extend_i32_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_extend_i32_s x))]

val instr_bytesize_eqn_i32_trunc_f64_u (x: unit) : Lemma (instr_bytesize (Rest_i32_trunc_f64_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_trunc_f64_u x))]

val instr_bytesize_eqn_i32_trunc_f64_s (x: unit) : Lemma (instr_bytesize (Rest_i32_trunc_f64_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_trunc_f64_s x))]

val instr_bytesize_eqn_i32_trunc_f32_u (x: unit) : Lemma (instr_bytesize (Rest_i32_trunc_f32_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_trunc_f32_u x))]

val instr_bytesize_eqn_i32_trunc_f32_s (x: unit) : Lemma (instr_bytesize (Rest_i32_trunc_f32_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_trunc_f32_s x))]

val instr_bytesize_eqn_i32_wrap_i64 (x: unit) : Lemma (instr_bytesize (Rest_i32_wrap_i64 x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_wrap_i64 x))]

val instr_bytesize_eqn_f64_copysign (x: unit) : Lemma (instr_bytesize (Rest_f64_copysign x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_copysign x))]

val instr_bytesize_eqn_f64_max (x: unit) : Lemma (instr_bytesize (Rest_f64_max x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_max x))]

val instr_bytesize_eqn_f64_min (x: unit) : Lemma (instr_bytesize (Rest_f64_min x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_min x))]

val instr_bytesize_eqn_f64_div (x: unit) : Lemma (instr_bytesize (Rest_f64_div x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_div x))]

val instr_bytesize_eqn_f64_mul (x: unit) : Lemma (instr_bytesize (Rest_f64_mul x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_mul x))]

val instr_bytesize_eqn_f64_sub (x: unit) : Lemma (instr_bytesize (Rest_f64_sub x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_sub x))]

val instr_bytesize_eqn_f64_add (x: unit) : Lemma (instr_bytesize (Rest_f64_add x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_add x))]

val instr_bytesize_eqn_f64_sqrt (x: unit) : Lemma (instr_bytesize (Rest_f64_sqrt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_sqrt x))]

val instr_bytesize_eqn_f64_nearest (x: unit) : Lemma (instr_bytesize (Rest_f64_nearest x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_nearest x))]

val instr_bytesize_eqn_f64_trunc (x: unit) : Lemma (instr_bytesize (Rest_f64_trunc x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_trunc x))]

val instr_bytesize_eqn_f64_floor (x: unit) : Lemma (instr_bytesize (Rest_f64_floor x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_floor x))]

val instr_bytesize_eqn_f64_ceil (x: unit) : Lemma (instr_bytesize (Rest_f64_ceil x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_ceil x))]

val instr_bytesize_eqn_f64_neg (x: unit) : Lemma (instr_bytesize (Rest_f64_neg x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_neg x))]

val instr_bytesize_eqn_f64_abs (x: unit) : Lemma (instr_bytesize (Rest_f64_abs x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_abs x))]

val instr_bytesize_eqn_f32_copysign (x: unit) : Lemma (instr_bytesize (Rest_f32_copysign x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_copysign x))]

val instr_bytesize_eqn_f32_max (x: unit) : Lemma (instr_bytesize (Rest_f32_max x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_max x))]

val instr_bytesize_eqn_f32_min (x: unit) : Lemma (instr_bytesize (Rest_f32_min x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_min x))]

val instr_bytesize_eqn_f32_div (x: unit) : Lemma (instr_bytesize (Rest_f32_div x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_div x))]

val instr_bytesize_eqn_f32_mul (x: unit) : Lemma (instr_bytesize (Rest_f32_mul x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_mul x))]

val instr_bytesize_eqn_f32_sub (x: unit) : Lemma (instr_bytesize (Rest_f32_sub x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_sub x))]

val instr_bytesize_eqn_f32_add (x: unit) : Lemma (instr_bytesize (Rest_f32_add x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_add x))]

val instr_bytesize_eqn_f32_sqrt (x: unit) : Lemma (instr_bytesize (Rest_f32_sqrt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_sqrt x))]

val instr_bytesize_eqn_f32_nearest (x: unit) : Lemma (instr_bytesize (Rest_f32_nearest x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_nearest x))]

val instr_bytesize_eqn_f32_trunc (x: unit) : Lemma (instr_bytesize (Rest_f32_trunc x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_trunc x))]

val instr_bytesize_eqn_f32_floor (x: unit) : Lemma (instr_bytesize (Rest_f32_floor x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_floor x))]

val instr_bytesize_eqn_f32_ceil (x: unit) : Lemma (instr_bytesize (Rest_f32_ceil x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_ceil x))]

val instr_bytesize_eqn_f32_neg (x: unit) : Lemma (instr_bytesize (Rest_f32_neg x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_neg x))]

val instr_bytesize_eqn_f32_abs (x: unit) : Lemma (instr_bytesize (Rest_f32_abs x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_abs x))]

val instr_bytesize_eqn_i64_rotr (x: unit) : Lemma (instr_bytesize (Rest_i64_rotr x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_rotr x))]

val instr_bytesize_eqn_i64_rotl (x: unit) : Lemma (instr_bytesize (Rest_i64_rotl x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_rotl x))]

val instr_bytesize_eqn_i64_shr_u (x: unit) : Lemma (instr_bytesize (Rest_i64_shr_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_shr_u x))]

val instr_bytesize_eqn_i64_shr_s (x: unit) : Lemma (instr_bytesize (Rest_i64_shr_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_shr_s x))]

val instr_bytesize_eqn_i64_shl (x: unit) : Lemma (instr_bytesize (Rest_i64_shl x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_shl x))]

val instr_bytesize_eqn_i64_xor (x: unit) : Lemma (instr_bytesize (Rest_i64_xor x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_xor x))]

val instr_bytesize_eqn_i64_or (x: unit) : Lemma (instr_bytesize (Rest_i64_or x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_or x))]

val instr_bytesize_eqn_i64_and (x: unit) : Lemma (instr_bytesize (Rest_i64_and x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_and x))]

val instr_bytesize_eqn_i64_rem_u (x: unit) : Lemma (instr_bytesize (Rest_i64_rem_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_rem_u x))]

val instr_bytesize_eqn_i64_rem_s (x: unit) : Lemma (instr_bytesize (Rest_i64_rem_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_rem_s x))]

val instr_bytesize_eqn_i64_div_u (x: unit) : Lemma (instr_bytesize (Rest_i64_div_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_div_u x))]

val instr_bytesize_eqn_i64_div_s (x: unit) : Lemma (instr_bytesize (Rest_i64_div_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_div_s x))]

val instr_bytesize_eqn_i64_mul (x: unit) : Lemma (instr_bytesize (Rest_i64_mul x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_mul x))]

val instr_bytesize_eqn_i64_sub (x: unit) : Lemma (instr_bytesize (Rest_i64_sub x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_sub x))]

val instr_bytesize_eqn_i64_add (x: unit) : Lemma (instr_bytesize (Rest_i64_add x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_add x))]

val instr_bytesize_eqn_i64_popcnt (x: unit) : Lemma (instr_bytesize (Rest_i64_popcnt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_popcnt x))]

val instr_bytesize_eqn_i64_ctz (x: unit) : Lemma (instr_bytesize (Rest_i64_ctz x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_ctz x))]

val instr_bytesize_eqn_i64_clz (x: unit) : Lemma (instr_bytesize (Rest_i64_clz x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_clz x))]

val instr_bytesize_eqn_i32_rotr (x: unit) : Lemma (instr_bytesize (Rest_i32_rotr x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_rotr x))]

val instr_bytesize_eqn_i32_rotl (x: unit) : Lemma (instr_bytesize (Rest_i32_rotl x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_rotl x))]

val instr_bytesize_eqn_i32_shr_u (x: unit) : Lemma (instr_bytesize (Rest_i32_shr_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_shr_u x))]

val instr_bytesize_eqn_i32_shr_s (x: unit) : Lemma (instr_bytesize (Rest_i32_shr_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_shr_s x))]

val instr_bytesize_eqn_i32_shl (x: unit) : Lemma (instr_bytesize (Rest_i32_shl x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_shl x))]

val instr_bytesize_eqn_i32_xor (x: unit) : Lemma (instr_bytesize (Rest_i32_xor x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_xor x))]

val instr_bytesize_eqn_i32_or (x: unit) : Lemma (instr_bytesize (Rest_i32_or x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_or x))]

val instr_bytesize_eqn_i32_and (x: unit) : Lemma (instr_bytesize (Rest_i32_and x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_and x))]

val instr_bytesize_eqn_i32_rem_u (x: unit) : Lemma (instr_bytesize (Rest_i32_rem_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_rem_u x))]

val instr_bytesize_eqn_i32_rem_s (x: unit) : Lemma (instr_bytesize (Rest_i32_rem_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_rem_s x))]

val instr_bytesize_eqn_i32_div_u (x: unit) : Lemma (instr_bytesize (Rest_i32_div_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_div_u x))]

val instr_bytesize_eqn_i32_div_s (x: unit) : Lemma (instr_bytesize (Rest_i32_div_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_div_s x))]

val instr_bytesize_eqn_i32_mul (x: unit) : Lemma (instr_bytesize (Rest_i32_mul x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_mul x))]

val instr_bytesize_eqn_i32_sub (x: unit) : Lemma (instr_bytesize (Rest_i32_sub x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_sub x))]

val instr_bytesize_eqn_i32_add (x: unit) : Lemma (instr_bytesize (Rest_i32_add x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_add x))]

val instr_bytesize_eqn_i32_popcnt (x: unit) : Lemma (instr_bytesize (Rest_i32_popcnt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_popcnt x))]

val instr_bytesize_eqn_i32_ctz (x: unit) : Lemma (instr_bytesize (Rest_i32_ctz x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_ctz x))]

val instr_bytesize_eqn_i32_clz (x: unit) : Lemma (instr_bytesize (Rest_i32_clz x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_clz x))]

val instr_bytesize_eqn_f64_ge (x: unit) : Lemma (instr_bytesize (Rest_f64_ge x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_ge x))]

val instr_bytesize_eqn_f64_le (x: unit) : Lemma (instr_bytesize (Rest_f64_le x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_le x))]

val instr_bytesize_eqn_f64_gt (x: unit) : Lemma (instr_bytesize (Rest_f64_gt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_gt x))]

val instr_bytesize_eqn_f64_lt (x: unit) : Lemma (instr_bytesize (Rest_f64_lt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_lt x))]

val instr_bytesize_eqn_f64_ne (x: unit) : Lemma (instr_bytesize (Rest_f64_ne x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_ne x))]

val instr_bytesize_eqn_f64_eq (x: unit) : Lemma (instr_bytesize (Rest_f64_eq x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f64_eq x))]

val instr_bytesize_eqn_f32_ge (x: unit) : Lemma (instr_bytesize (Rest_f32_ge x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_ge x))]

val instr_bytesize_eqn_f32_le (x: unit) : Lemma (instr_bytesize (Rest_f32_le x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_le x))]

val instr_bytesize_eqn_f32_gt (x: unit) : Lemma (instr_bytesize (Rest_f32_gt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_gt x))]

val instr_bytesize_eqn_f32_lt (x: unit) : Lemma (instr_bytesize (Rest_f32_lt x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_lt x))]

val instr_bytesize_eqn_f32_ne (x: unit) : Lemma (instr_bytesize (Rest_f32_ne x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_ne x))]

val instr_bytesize_eqn_f32_eq (x: unit) : Lemma (instr_bytesize (Rest_f32_eq x) == 1 + 0) [SMTPat (instr_bytesize (Rest_f32_eq x))]

val instr_bytesize_eqn_i64_ge_u (x: unit) : Lemma (instr_bytesize (Rest_i64_ge_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_ge_u x))]

val instr_bytesize_eqn_i64_ge_s (x: unit) : Lemma (instr_bytesize (Rest_i64_ge_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_ge_s x))]

val instr_bytesize_eqn_i64_le_u (x: unit) : Lemma (instr_bytesize (Rest_i64_le_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_le_u x))]

val instr_bytesize_eqn_i64_le_s (x: unit) : Lemma (instr_bytesize (Rest_i64_le_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_le_s x))]

val instr_bytesize_eqn_i64_gt_u (x: unit) : Lemma (instr_bytesize (Rest_i64_gt_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_gt_u x))]

val instr_bytesize_eqn_i64_gt_s (x: unit) : Lemma (instr_bytesize (Rest_i64_gt_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_gt_s x))]

val instr_bytesize_eqn_i64_lt_u (x: unit) : Lemma (instr_bytesize (Rest_i64_lt_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_lt_u x))]

val instr_bytesize_eqn_i64_lt_s (x: unit) : Lemma (instr_bytesize (Rest_i64_lt_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_lt_s x))]

val instr_bytesize_eqn_i64_ne (x: unit) : Lemma (instr_bytesize (Rest_i64_ne x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_ne x))]

val instr_bytesize_eqn_i64_eq (x: unit) : Lemma (instr_bytesize (Rest_i64_eq x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_eq x))]

val instr_bytesize_eqn_i64_eqz (x: unit) : Lemma (instr_bytesize (Rest_i64_eqz x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i64_eqz x))]

val instr_bytesize_eqn_i32_ge_u (x: unit) : Lemma (instr_bytesize (Rest_i32_ge_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_ge_u x))]

val instr_bytesize_eqn_i32_ge_s (x: unit) : Lemma (instr_bytesize (Rest_i32_ge_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_ge_s x))]

val instr_bytesize_eqn_i32_le_u (x: unit) : Lemma (instr_bytesize (Rest_i32_le_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_le_u x))]

val instr_bytesize_eqn_i32_le_s (x: unit) : Lemma (instr_bytesize (Rest_i32_le_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_le_s x))]

val instr_bytesize_eqn_i32_gt_u (x: unit) : Lemma (instr_bytesize (Rest_i32_gt_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_gt_u x))]

val instr_bytesize_eqn_i32_gt_s (x: unit) : Lemma (instr_bytesize (Rest_i32_gt_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_gt_s x))]

val instr_bytesize_eqn_i32_lt_u (x: unit) : Lemma (instr_bytesize (Rest_i32_lt_u x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_lt_u x))]

val instr_bytesize_eqn_i32_lt_s (x: unit) : Lemma (instr_bytesize (Rest_i32_lt_s x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_lt_s x))]

val instr_bytesize_eqn_i32_ne (x: unit) : Lemma (instr_bytesize (Rest_i32_ne x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_ne x))]

val instr_bytesize_eqn_i32_eq (x: unit) : Lemma (instr_bytesize (Rest_i32_eq x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_eq x))]

val instr_bytesize_eqn_i32_eqz (x: unit) : Lemma (instr_bytesize (Rest_i32_eqz x) == 1 + 0) [SMTPat (instr_bytesize (Rest_i32_eqz x))]

val instr_bytesize_eqn_select_ (x: unit) : Lemma (instr_bytesize (Rest_select_ x) == 1 + 0) [SMTPat (instr_bytesize (Rest_select_ x))]

val instr_bytesize_eqn_drop (x: unit) : Lemma (instr_bytesize (Rest_drop x) == 1 + 0) [SMTPat (instr_bytesize (Rest_drop x))]

val instr_bytesize_eqn_ret (x: unit) : Lemma (instr_bytesize (Rest_ret x) == 1 + 0) [SMTPat (instr_bytesize (Rest_ret x))]

val instr_bytesize_eqn_nop (x: unit) : Lemma (instr_bytesize (Rest_nop x) == 1 + 0) [SMTPat (instr_bytesize (Rest_nop x))]

val instr_bytesize_eqn_unreachable (x: unit) : Lemma (instr_bytesize (Rest_unreachable x) == 1 + 0) [SMTPat (instr_bytesize (Rest_unreachable x))]
