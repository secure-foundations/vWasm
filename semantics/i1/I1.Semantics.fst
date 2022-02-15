module I1.Semantics

open Semantics.Common.CFG
open Semantics.Common.CFG.HighLevelSemantics
open Semantics.Common.CFG.Instructions
open Semantics.Common.CFG.Printer

let valid_reg_int (n:int) = n >= 0
let valid_reg_float (n:int) = n >= 0

let regi = regi #valid_reg_int
let regf = regf #valid_reg_float
let maddr = maddr #valid_reg_int
let operandi = operandi #valid_reg_int
let operandf = operandf #valid_reg_int #valid_reg_float
let target_t = target_t #valid_reg_int
let ins_t = ins_t #valid_reg_int #valid_reg_float
//let eval_ins = admit() // TODO: after proper state split
let ocmp = ocmp #valid_reg_int #valid_reg_float
let precode = precode #ins_t #valid_reg_int #valid_reg_float
let cfg = cfg #ins_t #valid_reg_int #valid_reg_float
let module_ = module_ #ins_t #valid_reg_int #valid_reg_float
//let eval_step (c:cfg) (s:state) = eval_step #_ #_ #_ #eval_ins c s // TODO: after proper state split
let string_of_cfg (c:cfg) = string_of_cfg #_ #_ #_ #string_of_inst c
let print_strings_of_cfg (c:cfg) = print_strings_of_cfg #_ #_ #_ #string_of_inst c
