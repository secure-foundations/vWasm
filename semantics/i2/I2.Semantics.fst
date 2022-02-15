module I2.Semantics

open Semantics.Common.CFG
open Semantics.Common.CFG.LowLevelSemantics
open Semantics.Common.CFG.Instructions
open Semantics.Common.CFG.Printer
open Semantics.Common.CFG.LLInstructionSemantics

/// Order of registers:
/// rdi rsi rdx rcx r8 r9 r10 r11 rax rbx rbp r12 r13 r14 r15 rsp
/// ----- arguments ----- caller  ret ------- callee ---- ext reserved (unusable)
///
/// xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15
/// -ret--------- arguments --------------- ----caller-----  ext  --reserved (unusable)--

let max_reg_int = 15 // rsp is reserved, and thus unusable
let max_reg_float = 12 // xmm12 to xmm15 are reserved for temporaries, and thus unusable

let max_int_use = 14 // r15 reserved for moving stuff around to avoid second reg
let max_float_use = 11 // xmm11 reserved for moving stuff around to avoid second reg allocation pass

let temp_int = 14
let temp_float = 15

let reg_int_ret = 8
let reg_float_ret = 0
let max_int_args = 6
let max_float_args = 8
let int_caller_saved = 9

let valid_reg_int (n:int) = n >= 0 && n < max_reg_int
let valid_reg_float (n:int) = n >= 0 && n < max_reg_float

let regi = regi #valid_reg_int
let regf = regf #valid_reg_float
let maddr = maddr #valid_reg_int
let operandi = operandi #valid_reg_int
let operandf = operandf #valid_reg_int #valid_reg_float
let ins_t = ins_t #valid_reg_int #valid_reg_float
let eval_ins = eval_ins #valid_reg_int #valid_reg_float
let eval_inss = eval_inss #_ #eval_ins
let ocmp = ocmp #valid_reg_int #valid_reg_float
let target_t = target_t #valid_reg_int
let precode = precode #ins_t #valid_reg_int #valid_reg_float
let cfg = cfg #ins_t #valid_reg_int #valid_reg_float
let module_ = module_ #ins_t #valid_reg_int #valid_reg_float
let eval_step' (c:cfg) (p:precode) (s:state) = eval_step' #_ #_ #_ #eval_ins c p s
let eval_step (c:cfg) (s:state) = eval_step #_ #_ #_ #eval_ins c s
let string_of_precode (p:precode) = string_of_precode #_ #_ #_ #string_of_inst p
let string_of_cfg (c:cfg) = string_of_cfg #_ #_ #_ #string_of_inst c
let print_strings_of_cfg (c:cfg) = print_strings_of_cfg #_ #_ #_ #string_of_inst c
