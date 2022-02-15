module Semantics.Printer.AuxiliaryRoutines

open FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open Common.Err
open Common.Memory
open Types_s
open Common.Conversions
open Semantics.Common.CFG
open Semantics.Common.CFG.Instructions

open I2.Semantics
module I = Semantics.Common.CFG.LLInstructionSemantics

open Semantics.Printer.Helper
open Semantics.Printer.Effect

(** Get a temporary xmm register. These registers are guaranteed to be
    reserved and unused by the compiler, and thus are safe to use. The
    assertion within this definition guarantees this. *)
let temporary_xmm (i:nat{i < 4}) : Tot string =
  let reg_num = max_reg_float + i in
  let max_allowed_xmm = 15 in
  assert (reg_num <= max_allowed_xmm);
  "xmm" ^ string_of_int reg_num

(** Set up the right temporaries for all the auxiliary routines. *)
val print_aux_temporaries : unit -> Printer unit

(** Print dword-based floating point constants, provided the name and list of dwords. *)
val print_floating_constant_dds : string -> list nat32 -> Printer unit

(** Print qword-based floating point constants, provided the name and list of qwords. *)
val print_floating_constant_dqs : string -> list nat64 -> Printer unit

(** Print routines for conversion to/from floats & unsigned numbers.

    Calling convention for these routines: input and output argument
    comes from [temporary_xmm 0]. *)
val print_unsigned_conversion_routines : unit -> Printer unit
