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

let pr (s:section) (l:list string) : Printer unit =
  let f (x:string) : Printer unit = print s x; print s "\n" in
  printer_for_each l f;
  print s "\n"

let t0 = temporary_xmm 0
let t1 = temporary_xmm 1
let t2 = temporary_xmm 2
let t3 = temporary_xmm 3

let print_aux_temporaries () : Printer unit =
  printer_for_each [0; 1; 2; 3] (fun i ->
      pr AuxRWData ["STATIC AUX_TEMP" ^ string_of_int i;
                    "AUX_TEMP" ^ string_of_int i ^ ": dq 0, 0"])

let print_floating_constant_dds (name:string) (ns:list nat32) : Printer unit =
  prints Constants [
    "STATIC " ^ name ^ "\n";
    name ^ ":\n";
  ];
  printer_for_each ns (fun n -> print Constants ("  dd " ^ string_of_int n ^ "\n"));
  print Constants "\n"

let print_floating_constant_dqs (name:string) (ns:list nat64) : Printer unit =
  prints Constants [
    "STATIC " ^ name ^ "\n";
    name ^ ":\n";
  ];
  printer_for_each ns (fun n -> print Constants ("  dq " ^ string_of_int n ^ "\n"));
  print Constants "\n"

let print_u32_f32_conversions () : Printer unit =
  pr AuxRoutines [
    "STATIC CONVERT_F32_TO_U32";
    "CONVERT_F32_TO_U32:";
    (* Store original registers into temporaries *)
    "  mov       [AUX_TEMP0], rax";
    (* Do the conversion. *)
    "  vcvttss2si      rax, " ^ t0;
    "  movd            " ^ t0 ^ ", eax";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ];
  pr AuxRoutines [
    "STATIC CONVERT_U32_TO_F32";
    "CONVERT_U32_TO_F32:";
    (* Store original registers into temporaries *)
    "  mov       [AUX_TEMP0], rax";
    (* Do the conversion. *)
    "  movd            eax, " ^ t0;
    "  vxorps          " ^ t0 ^ ", " ^ t0 ^ ", " ^ t0;
    "  vcvtsi2ss       " ^ t0 ^ ", " ^ t0 ^ ", rax";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ]

let print_u32_f64_conversions () : Printer unit =
  pr AuxRoutines [
    "STATIC CONVERT_F64_TO_U32";
    "CONVERT_F64_TO_U32:";
    (* Store original registers into temporaries *)
    "  mov       [AUX_TEMP0], rax";
    (* Do the conversion. *)
    "  vcvttsd2si      rax, " ^ t0;
    "  movq            " ^ t0 ^ ", rax";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ];
  pr AuxRoutines [
    "STATIC CONVERT_U32_TO_F64";
    "CONVERT_U32_TO_F64:";
    (* Store original registers into temporaries *)
    "  mov       [AUX_TEMP0], rax";
    (* Do the conversion. *)
    "  movd            eax, " ^ t0;
    "  vxorps          " ^ t0 ^ ", " ^ t0 ^ ", " ^ t0;
    "  vcvtsi2sd       " ^ t0 ^ ", " ^ t0 ^ ", rax";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ]

let print_u64_f32_conversions () : Printer unit =
  print_floating_constant_dds "CONST_CONV_F32U64" [1593835520; 0; 0; 0];
  pr AuxRoutines [
    "STATIC CONVERT_F32_TO_U64";
    "CONVERT_F32_TO_U64:";
    (* Store original registers into temporaries *)
    "  mov        [AUX_TEMP0], rax";
    (* Do the conversion. *)
    "  vcomiss    " ^ t0 ^ ", DWORD [CONST_CONV_F32U64]";
    "  jnb        CONV_F32U64_LBL_A";
    "  vcvttss2si rax, " ^ t0;
    "  jmp        CONV_F32U64_LBL_B";
    "CONV_F32U64_LBL_A:";
    "  vsubss     " ^ t0 ^ ", " ^ t0 ^ ", DWORD [CONST_CONV_F32U64]";
    "  vcvttss2si rax, " ^ t0;
    "  btc        rax, 63";
    "CONV_F32U64_LBL_B:";
    "  movq       " ^ t0 ^ ", rax";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ];
  pr AuxRoutines [
    "STATIC CONVERT_U64_TO_F32";
    "CONVERT_U64_TO_F32:";
    (* Store original registers into temporaries *)
    "  mov       [AUX_TEMP0], rdi";
    "  mov       [AUX_TEMP1], rax";
    (* Do the conversion. *)
    "  movq      rdi, " ^ t0;
    "  vxorps    " ^ t0 ^ ", " ^ t0 ^ ", " ^ t0;
    "  test      rdi, rdi";
    "  js        CONV_U64F32_LBL_A";
    "  vcvtsi2ss " ^ t0 ^ ", " ^ t0 ^ ", rdi";
    "  jmp       CONV_U64F32_LBL_B";
    "CONV_U64F32_LBL_A:";
    "  mov       rax, rdi";
    "  and       edi, 1";
    "  shr       rax, 1";
    "  or        rax, rdi";
    "  vcvtsi2ss " ^ t0 ^ ", " ^ t0 ^ ", rax";
    "  vaddss    " ^ t0 ^ ", " ^ t0 ^ ", " ^ t0;
    "CONV_U64F32_LBL_B:";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP1]";
    "  mov       rdi,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ]

let print_u64_f64_conversions () : Printer unit =
  print_floating_constant_dds "CONST_CONV_F64U64" [0; 1138753536; 0; 0];
  pr AuxRoutines [
    "STATIC CONVERT_F64_TO_U64";
    "CONVERT_F64_TO_U64:";
    (* Store original registers into temporaries *)
    "  mov        [AUX_TEMP0], rax";
    (* Do the conversion. *)
    "  vmovsd     " ^ t1 ^ ", QWORD [CONST_CONV_F64U64]";
    "  vcomisd    " ^ t0 ^ ", " ^ t1;
    "  jnb        CONV_F64U64_LBL_A";
    "  vcvttsd2si rax, " ^ t0;
    "  jmp        CONV_F64U64_LBL_B";
    "CONV_F64U64_LBL_A:";
    "  vsubsd     " ^ t0 ^ ", " ^ t0 ^ ", " ^ t1;
    "  vcvttsd2si rax, " ^ t0;
    "  btc        rax, 63";
    "CONV_F64U64_LBL_B:";
    "  movq       " ^ t0 ^ ", rax";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ];
  pr AuxRoutines [
    "STATIC CONVERT_U64_TO_F64";
    "CONVERT_U64_TO_F64:";
    (* Store original registers into temporaries *)
    "  mov       [AUX_TEMP0], rdi";
    "  mov       [AUX_TEMP1], rax";
    (* Do the conversion. *)
    "  movq      rdi, " ^ t0;
    "  vxorps    " ^ t0 ^ ", " ^ t0 ^ ", " ^ t0;
    "  test      rdi, rdi";
    "  js        CONV_U64F64_LBL_A";
    "  vcvtsi2sd " ^ t0 ^ ", " ^ t0 ^ ", rdi";
    "  jmp       CONV_U64F64_LBL_B";
    "CONV_U64F64_LBL_A:";
    "  mov       rax, rdi";
    "  and       edi, 1";
    "  shr       rax, 1";
    "  or        rax, rdi";
    "  vcvtsi2sd " ^ t0 ^ ", " ^ t0 ^ ", rax";
    "  vaddsd    " ^ t0 ^ ", " ^ t0 ^ ", " ^ t0;
    "CONV_U64F64_LBL_B:";
    (* Revert original values of registers *)
    "  mov       rax,  [AUX_TEMP1]";
    "  mov       rdi,  [AUX_TEMP0]";
    (* Return *)
    "  ret";
  ]

let print_unsigned_conversion_routines () : Printer unit =
  (*

  All these routines are based on the output of the following C code,
  compiled with `gcc -O2 -march=sandybridge`:

     ```
     #include <stdint.h>

     typedef float f32;
     typedef double f64;
     typedef int32_t i32;
     typedef int64_t i64;
     typedef uint32_t u32;
     typedef uint64_t u64;

     #define CONV(F, T) T CONVERT_##F##_TO_##T (F f) { return f; }

     CONV(f32, u32)
     CONV(f32, u64)
     CONV(f64, u32)
     CONV(f64, u64)
     CONV(u32, f32)
     CONV(u64, f32)
     CONV(u32, f64)
     CONV(u64, f64)
     ```

  The only modifications done to the output assembly code (from gcc
  10.2) is to utilize the calling convention of using `t0` for input
  and output, and to make sure that no registers are being clobbered.

  We don't need (or indeed want) the standard calling convention since
  these routines won't be accessed outside of the places where _we_
  explicitly call them (i.e. they are 'static' to our
  compiler). Additionally, by utilizing the calling convention here,
  we don't need to worry about anything being callee-saved, and
  instead can make them purely caller-saved, which is a massive
  convenience since it localizes those issues in a single place (here)
  rather than scattering them across the the codebase.

  *)
  print_u32_f32_conversions ();
  print_u32_f64_conversions ();
  print_u64_f32_conversions ();
  print_u64_f64_conversions ()
