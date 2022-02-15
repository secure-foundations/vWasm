open Prims
type aux_insn_label =
  | Unreachable 
  | Nop 
  | Block 
  | Loop 
  | If_ 
  | Br 
  | Br_if 
  | Br_table 
  | Ret 
  | Call 
  | Call_indirect 
  | Drop 
  | Select_ 
  | Local_get 
  | Local_set 
  | Local_tee 
  | Global_get 
  | Global_set 
  | I32_load 
  | I64_load 
  | F32_load 
  | F64_load 
  | I32_load8_s 
  | I32_load8_u 
  | I32_load16_s 
  | I32_load16_u 
  | I64_load8_s 
  | I64_load8_u 
  | I64_load16_s 
  | I64_load16_u 
  | I64_load32_s 
  | I64_load32_u 
  | I32_store 
  | I64_store 
  | F32_store 
  | F64_store 
  | I32_store8 
  | I32_store16 
  | I64_store8 
  | I64_store16 
  | I64_store32 
  | Memory_size 
  | Memory_grow 
  | I32_const 
  | I64_const 
  | F32_const 
  | F64_const 
  | I32_eqz 
  | I32_eq 
  | I32_ne 
  | I32_lt_s 
  | I32_lt_u 
  | I32_gt_s 
  | I32_gt_u 
  | I32_le_s 
  | I32_le_u 
  | I32_ge_s 
  | I32_ge_u 
  | I64_eqz 
  | I64_eq 
  | I64_ne 
  | I64_lt_s 
  | I64_lt_u 
  | I64_gt_s 
  | I64_gt_u 
  | I64_le_s 
  | I64_le_u 
  | I64_ge_s 
  | I64_ge_u 
  | F32_eq 
  | F32_ne 
  | F32_lt 
  | F32_gt 
  | F32_le 
  | F32_ge 
  | F64_eq 
  | F64_ne 
  | F64_lt 
  | F64_gt 
  | F64_le 
  | F64_ge 
  | I32_clz 
  | I32_ctz 
  | I32_popcnt 
  | I32_add 
  | I32_sub 
  | I32_mul 
  | I32_div_s 
  | I32_div_u 
  | I32_rem_s 
  | I32_rem_u 
  | I32_and 
  | I32_or 
  | I32_xor 
  | I32_shl 
  | I32_shr_s 
  | I32_shr_u 
  | I32_rotl 
  | I32_rotr 
  | I64_clz 
  | I64_ctz 
  | I64_popcnt 
  | I64_add 
  | I64_sub 
  | I64_mul 
  | I64_div_s 
  | I64_div_u 
  | I64_rem_s 
  | I64_rem_u 
  | I64_and 
  | I64_or 
  | I64_xor 
  | I64_shl 
  | I64_shr_s 
  | I64_shr_u 
  | I64_rotl 
  | I64_rotr 
  | F32_abs 
  | F32_neg 
  | F32_ceil 
  | F32_floor 
  | F32_trunc 
  | F32_nearest 
  | F32_sqrt 
  | F32_add 
  | F32_sub 
  | F32_mul 
  | F32_div 
  | F32_min 
  | F32_max 
  | F32_copysign 
  | F64_abs 
  | F64_neg 
  | F64_ceil 
  | F64_floor 
  | F64_trunc 
  | F64_nearest 
  | F64_sqrt 
  | F64_add 
  | F64_sub 
  | F64_mul 
  | F64_div 
  | F64_min 
  | F64_max 
  | F64_copysign 
  | I32_wrap_i64 
  | I32_trunc_f32_s 
  | I32_trunc_f32_u 
  | I32_trunc_f64_s 
  | I32_trunc_f64_u 
  | I64_extend_i32_s 
  | I64_extend_i32_u 
  | I64_trunc_f32_s 
  | I64_trunc_f32_u 
  | I64_trunc_f64_s 
  | I64_trunc_f64_u 
  | F32_convert_i32_s 
  | F32_convert_i32_u 
  | F32_convert_i64_s 
  | F32_convert_i64_u 
  | F32_demote_f64 
  | F64_convert_i32_s 
  | F64_convert_i32_u 
  | F64_convert_i64_s 
  | F64_convert_i64_u 
  | F64_promote_f32 
  | I32_reinterpret_f32 
  | I64_reinterpret_f64 
  | F32_reinterpret_i32 
  | F64_reinterpret_i64 
  | End_of_contiguous_instructions 
let (uu___is_Unreachable : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | Unreachable -> true | uu___ -> false
let (uu___is_Nop : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Nop -> true | uu___ -> false
let (uu___is_Block : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Block -> true | uu___ -> false
let (uu___is_Loop : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Loop -> true | uu___ -> false
let (uu___is_If_ : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | If_ -> true | uu___ -> false
let (uu___is_Br : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Br -> true | uu___ -> false
let (uu___is_Br_if : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Br_if -> true | uu___ -> false
let (uu___is_Br_table : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Br_table -> true | uu___ -> false
let (uu___is_Ret : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Ret -> true | uu___ -> false
let (uu___is_Call : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Call -> true | uu___ -> false
let (uu___is_Call_indirect : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | Call_indirect -> true | uu___ -> false
let (uu___is_Drop : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Drop -> true | uu___ -> false
let (uu___is_Select_ : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Select_ -> true | uu___ -> false
let (uu___is_Local_get : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Local_get -> true | uu___ -> false
let (uu___is_Local_set : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Local_set -> true | uu___ -> false
let (uu___is_Local_tee : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Local_tee -> true | uu___ -> false
let (uu___is_Global_get : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Global_get -> true | uu___ -> false
let (uu___is_Global_set : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | Global_set -> true | uu___ -> false
let (uu___is_I32_load : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_load -> true | uu___ -> false
let (uu___is_I64_load : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_load -> true | uu___ -> false
let (uu___is_F32_load : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_load -> true | uu___ -> false
let (uu___is_F64_load : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_load -> true | uu___ -> false
let (uu___is_I32_load8_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_load8_s -> true | uu___ -> false
let (uu___is_I32_load8_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_load8_u -> true | uu___ -> false
let (uu___is_I32_load16_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_load16_s -> true | uu___ -> false
let (uu___is_I32_load16_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_load16_u -> true | uu___ -> false
let (uu___is_I64_load8_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_load8_s -> true | uu___ -> false
let (uu___is_I64_load8_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_load8_u -> true | uu___ -> false
let (uu___is_I64_load16_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_load16_s -> true | uu___ -> false
let (uu___is_I64_load16_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_load16_u -> true | uu___ -> false
let (uu___is_I64_load32_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_load32_s -> true | uu___ -> false
let (uu___is_I64_load32_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_load32_u -> true | uu___ -> false
let (uu___is_I32_store : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_store -> true | uu___ -> false
let (uu___is_I64_store : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_store -> true | uu___ -> false
let (uu___is_F32_store : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_store -> true | uu___ -> false
let (uu___is_F64_store : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_store -> true | uu___ -> false
let (uu___is_I32_store8 : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_store8 -> true | uu___ -> false
let (uu___is_I32_store16 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_store16 -> true | uu___ -> false
let (uu___is_I64_store8 : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_store8 -> true | uu___ -> false
let (uu___is_I64_store16 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_store16 -> true | uu___ -> false
let (uu___is_I64_store32 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_store32 -> true | uu___ -> false
let (uu___is_Memory_size : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | Memory_size -> true | uu___ -> false
let (uu___is_Memory_grow : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | Memory_grow -> true | uu___ -> false
let (uu___is_I32_const : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_const -> true | uu___ -> false
let (uu___is_I64_const : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_const -> true | uu___ -> false
let (uu___is_F32_const : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_const -> true | uu___ -> false
let (uu___is_F64_const : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_const -> true | uu___ -> false
let (uu___is_I32_eqz : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_eqz -> true | uu___ -> false
let (uu___is_I32_eq : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_eq -> true | uu___ -> false
let (uu___is_I32_ne : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_ne -> true | uu___ -> false
let (uu___is_I32_lt_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_lt_s -> true | uu___ -> false
let (uu___is_I32_lt_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_lt_u -> true | uu___ -> false
let (uu___is_I32_gt_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_gt_s -> true | uu___ -> false
let (uu___is_I32_gt_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_gt_u -> true | uu___ -> false
let (uu___is_I32_le_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_le_s -> true | uu___ -> false
let (uu___is_I32_le_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_le_u -> true | uu___ -> false
let (uu___is_I32_ge_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_ge_s -> true | uu___ -> false
let (uu___is_I32_ge_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_ge_u -> true | uu___ -> false
let (uu___is_I64_eqz : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_eqz -> true | uu___ -> false
let (uu___is_I64_eq : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_eq -> true | uu___ -> false
let (uu___is_I64_ne : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_ne -> true | uu___ -> false
let (uu___is_I64_lt_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_lt_s -> true | uu___ -> false
let (uu___is_I64_lt_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_lt_u -> true | uu___ -> false
let (uu___is_I64_gt_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_gt_s -> true | uu___ -> false
let (uu___is_I64_gt_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_gt_u -> true | uu___ -> false
let (uu___is_I64_le_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_le_s -> true | uu___ -> false
let (uu___is_I64_le_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_le_u -> true | uu___ -> false
let (uu___is_I64_ge_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_ge_s -> true | uu___ -> false
let (uu___is_I64_ge_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_ge_u -> true | uu___ -> false
let (uu___is_F32_eq : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_eq -> true | uu___ -> false
let (uu___is_F32_ne : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_ne -> true | uu___ -> false
let (uu___is_F32_lt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_lt -> true | uu___ -> false
let (uu___is_F32_gt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_gt -> true | uu___ -> false
let (uu___is_F32_le : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_le -> true | uu___ -> false
let (uu___is_F32_ge : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_ge -> true | uu___ -> false
let (uu___is_F64_eq : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_eq -> true | uu___ -> false
let (uu___is_F64_ne : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_ne -> true | uu___ -> false
let (uu___is_F64_lt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_lt -> true | uu___ -> false
let (uu___is_F64_gt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_gt -> true | uu___ -> false
let (uu___is_F64_le : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_le -> true | uu___ -> false
let (uu___is_F64_ge : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_ge -> true | uu___ -> false
let (uu___is_I32_clz : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_clz -> true | uu___ -> false
let (uu___is_I32_ctz : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_ctz -> true | uu___ -> false
let (uu___is_I32_popcnt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_popcnt -> true | uu___ -> false
let (uu___is_I32_add : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_add -> true | uu___ -> false
let (uu___is_I32_sub : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_sub -> true | uu___ -> false
let (uu___is_I32_mul : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_mul -> true | uu___ -> false
let (uu___is_I32_div_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_div_s -> true | uu___ -> false
let (uu___is_I32_div_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_div_u -> true | uu___ -> false
let (uu___is_I32_rem_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_rem_s -> true | uu___ -> false
let (uu___is_I32_rem_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_rem_u -> true | uu___ -> false
let (uu___is_I32_and : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_and -> true | uu___ -> false
let (uu___is_I32_or : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_or -> true | uu___ -> false
let (uu___is_I32_xor : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_xor -> true | uu___ -> false
let (uu___is_I32_shl : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_shl -> true | uu___ -> false
let (uu___is_I32_shr_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_shr_s -> true | uu___ -> false
let (uu___is_I32_shr_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_shr_u -> true | uu___ -> false
let (uu___is_I32_rotl : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_rotl -> true | uu___ -> false
let (uu___is_I32_rotr : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I32_rotr -> true | uu___ -> false
let (uu___is_I64_clz : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_clz -> true | uu___ -> false
let (uu___is_I64_ctz : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_ctz -> true | uu___ -> false
let (uu___is_I64_popcnt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_popcnt -> true | uu___ -> false
let (uu___is_I64_add : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_add -> true | uu___ -> false
let (uu___is_I64_sub : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_sub -> true | uu___ -> false
let (uu___is_I64_mul : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_mul -> true | uu___ -> false
let (uu___is_I64_div_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_div_s -> true | uu___ -> false
let (uu___is_I64_div_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_div_u -> true | uu___ -> false
let (uu___is_I64_rem_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_rem_s -> true | uu___ -> false
let (uu___is_I64_rem_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_rem_u -> true | uu___ -> false
let (uu___is_I64_and : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_and -> true | uu___ -> false
let (uu___is_I64_or : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_or -> true | uu___ -> false
let (uu___is_I64_xor : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_xor -> true | uu___ -> false
let (uu___is_I64_shl : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_shl -> true | uu___ -> false
let (uu___is_I64_shr_s : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_shr_s -> true | uu___ -> false
let (uu___is_I64_shr_u : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_shr_u -> true | uu___ -> false
let (uu___is_I64_rotl : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_rotl -> true | uu___ -> false
let (uu___is_I64_rotr : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | I64_rotr -> true | uu___ -> false
let (uu___is_F32_abs : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_abs -> true | uu___ -> false
let (uu___is_F32_neg : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_neg -> true | uu___ -> false
let (uu___is_F32_ceil : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_ceil -> true | uu___ -> false
let (uu___is_F32_floor : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_floor -> true | uu___ -> false
let (uu___is_F32_trunc : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_trunc -> true | uu___ -> false
let (uu___is_F32_nearest : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_nearest -> true | uu___ -> false
let (uu___is_F32_sqrt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_sqrt -> true | uu___ -> false
let (uu___is_F32_add : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_add -> true | uu___ -> false
let (uu___is_F32_sub : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_sub -> true | uu___ -> false
let (uu___is_F32_mul : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_mul -> true | uu___ -> false
let (uu___is_F32_div : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_div -> true | uu___ -> false
let (uu___is_F32_min : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_min -> true | uu___ -> false
let (uu___is_F32_max : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F32_max -> true | uu___ -> false
let (uu___is_F32_copysign : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_copysign -> true | uu___ -> false
let (uu___is_F64_abs : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_abs -> true | uu___ -> false
let (uu___is_F64_neg : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_neg -> true | uu___ -> false
let (uu___is_F64_ceil : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_ceil -> true | uu___ -> false
let (uu___is_F64_floor : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_floor -> true | uu___ -> false
let (uu___is_F64_trunc : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_trunc -> true | uu___ -> false
let (uu___is_F64_nearest : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_nearest -> true | uu___ -> false
let (uu___is_F64_sqrt : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_sqrt -> true | uu___ -> false
let (uu___is_F64_add : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_add -> true | uu___ -> false
let (uu___is_F64_sub : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_sub -> true | uu___ -> false
let (uu___is_F64_mul : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_mul -> true | uu___ -> false
let (uu___is_F64_div : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_div -> true | uu___ -> false
let (uu___is_F64_min : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_min -> true | uu___ -> false
let (uu___is_F64_max : aux_insn_label -> Prims.bool) =
  fun projectee -> match projectee with | F64_max -> true | uu___ -> false
let (uu___is_F64_copysign : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_copysign -> true | uu___ -> false
let (uu___is_I32_wrap_i64 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_wrap_i64 -> true | uu___ -> false
let (uu___is_I32_trunc_f32_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_trunc_f32_s -> true | uu___ -> false
let (uu___is_I32_trunc_f32_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_trunc_f32_u -> true | uu___ -> false
let (uu___is_I32_trunc_f64_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_trunc_f64_s -> true | uu___ -> false
let (uu___is_I32_trunc_f64_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_trunc_f64_u -> true | uu___ -> false
let (uu___is_I64_extend_i32_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_extend_i32_s -> true | uu___ -> false
let (uu___is_I64_extend_i32_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_extend_i32_u -> true | uu___ -> false
let (uu___is_I64_trunc_f32_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_trunc_f32_s -> true | uu___ -> false
let (uu___is_I64_trunc_f32_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_trunc_f32_u -> true | uu___ -> false
let (uu___is_I64_trunc_f64_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_trunc_f64_s -> true | uu___ -> false
let (uu___is_I64_trunc_f64_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_trunc_f64_u -> true | uu___ -> false
let (uu___is_F32_convert_i32_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_convert_i32_s -> true | uu___ -> false
let (uu___is_F32_convert_i32_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_convert_i32_u -> true | uu___ -> false
let (uu___is_F32_convert_i64_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_convert_i64_s -> true | uu___ -> false
let (uu___is_F32_convert_i64_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_convert_i64_u -> true | uu___ -> false
let (uu___is_F32_demote_f64 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_demote_f64 -> true | uu___ -> false
let (uu___is_F64_convert_i32_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_convert_i32_s -> true | uu___ -> false
let (uu___is_F64_convert_i32_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_convert_i32_u -> true | uu___ -> false
let (uu___is_F64_convert_i64_s : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_convert_i64_s -> true | uu___ -> false
let (uu___is_F64_convert_i64_u : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_convert_i64_u -> true | uu___ -> false
let (uu___is_F64_promote_f32 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_promote_f32 -> true | uu___ -> false
let (uu___is_I32_reinterpret_f32 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I32_reinterpret_f32 -> true | uu___ -> false
let (uu___is_I64_reinterpret_f64 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | I64_reinterpret_f64 -> true | uu___ -> false
let (uu___is_F32_reinterpret_i32 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F32_reinterpret_i32 -> true | uu___ -> false
let (uu___is_F64_reinterpret_i64 : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with | F64_reinterpret_i64 -> true | uu___ -> false
let (uu___is_End_of_contiguous_instructions : aux_insn_label -> Prims.bool) =
  fun projectee ->
    match projectee with
    | End_of_contiguous_instructions -> true
    | uu___ -> false
let (string_of_aux_insn_label : aux_insn_label -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Unreachable -> "unreachable"
    | Nop -> "nop"
    | Block -> "block"
    | Loop -> "loop"
    | If_ -> "if_"
    | Br -> "br"
    | Br_if -> "br_if"
    | Br_table -> "br_table"
    | Ret -> "ret"
    | Call -> "call"
    | Call_indirect -> "call_indirect"
    | Drop -> "drop"
    | Select_ -> "select_"
    | Local_get -> "local_get"
    | Local_set -> "local_set"
    | Local_tee -> "local_tee"
    | Global_get -> "global_get"
    | Global_set -> "global_set"
    | I32_load -> "i32_load"
    | I64_load -> "i64_load"
    | F32_load -> "f32_load"
    | F64_load -> "f64_load"
    | I32_load8_s -> "i32_load8_s"
    | I32_load8_u -> "i32_load8_u"
    | I32_load16_s -> "i32_load16_s"
    | I32_load16_u -> "i32_load16_u"
    | I64_load8_s -> "i64_load8_s"
    | I64_load8_u -> "i64_load8_u"
    | I64_load16_s -> "i64_load16_s"
    | I64_load16_u -> "i64_load16_u"
    | I64_load32_s -> "i64_load32_s"
    | I64_load32_u -> "i64_load32_u"
    | I32_store -> "i32_store"
    | I64_store -> "i64_store"
    | F32_store -> "f32_store"
    | F64_store -> "f64_store"
    | I32_store8 -> "i32_store8"
    | I32_store16 -> "i32_store16"
    | I64_store8 -> "i64_store8"
    | I64_store16 -> "i64_store16"
    | I64_store32 -> "i64_store32"
    | Memory_size -> "memory_size"
    | Memory_grow -> "memory_grow"
    | I32_const -> "i32_const"
    | I64_const -> "i64_const"
    | F32_const -> "f32_const"
    | F64_const -> "f64_const"
    | I32_eqz -> "i32_eqz"
    | I32_eq -> "i32_eq"
    | I32_ne -> "i32_ne"
    | I32_lt_s -> "i32_lt_s"
    | I32_lt_u -> "i32_lt_u"
    | I32_gt_s -> "i32_gt_s"
    | I32_gt_u -> "i32_gt_u"
    | I32_le_s -> "i32_le_s"
    | I32_le_u -> "i32_le_u"
    | I32_ge_s -> "i32_ge_s"
    | I32_ge_u -> "i32_ge_u"
    | I64_eqz -> "i64_eqz"
    | I64_eq -> "i64_eq"
    | I64_ne -> "i64_ne"
    | I64_lt_s -> "i64_lt_s"
    | I64_lt_u -> "i64_lt_u"
    | I64_gt_s -> "i64_gt_s"
    | I64_gt_u -> "i64_gt_u"
    | I64_le_s -> "i64_le_s"
    | I64_le_u -> "i64_le_u"
    | I64_ge_s -> "i64_ge_s"
    | I64_ge_u -> "i64_ge_u"
    | F32_eq -> "f32_eq"
    | F32_ne -> "f32_ne"
    | F32_lt -> "f32_lt"
    | F32_gt -> "f32_gt"
    | F32_le -> "f32_le"
    | F32_ge -> "f32_ge"
    | F64_eq -> "f64_eq"
    | F64_ne -> "f64_ne"
    | F64_lt -> "f64_lt"
    | F64_gt -> "f64_gt"
    | F64_le -> "f64_le"
    | F64_ge -> "f64_ge"
    | I32_clz -> "i32_clz"
    | I32_ctz -> "i32_ctz"
    | I32_popcnt -> "i32_popcnt"
    | I32_add -> "i32_add"
    | I32_sub -> "i32_sub"
    | I32_mul -> "i32_mul"
    | I32_div_s -> "i32_div_s"
    | I32_div_u -> "i32_div_u"
    | I32_rem_s -> "i32_rem_s"
    | I32_rem_u -> "i32_rem_u"
    | I32_and -> "i32_and"
    | I32_or -> "i32_or"
    | I32_xor -> "i32_xor"
    | I32_shl -> "i32_shl"
    | I32_shr_s -> "i32_shr_s"
    | I32_shr_u -> "i32_shr_u"
    | I32_rotl -> "i32_rotl"
    | I32_rotr -> "i32_rotr"
    | I64_clz -> "i64_clz"
    | I64_ctz -> "i64_ctz"
    | I64_popcnt -> "i64_popcnt"
    | I64_add -> "i64_add"
    | I64_sub -> "i64_sub"
    | I64_mul -> "i64_mul"
    | I64_div_s -> "i64_div_s"
    | I64_div_u -> "i64_div_u"
    | I64_rem_s -> "i64_rem_s"
    | I64_rem_u -> "i64_rem_u"
    | I64_and -> "i64_and"
    | I64_or -> "i64_or"
    | I64_xor -> "i64_xor"
    | I64_shl -> "i64_shl"
    | I64_shr_s -> "i64_shr_s"
    | I64_shr_u -> "i64_shr_u"
    | I64_rotl -> "i64_rotl"
    | I64_rotr -> "i64_rotr"
    | F32_abs -> "f32_abs"
    | F32_neg -> "f32_neg"
    | F32_ceil -> "f32_ceil"
    | F32_floor -> "f32_floor"
    | F32_trunc -> "f32_trunc"
    | F32_nearest -> "f32_nearest"
    | F32_sqrt -> "f32_sqrt"
    | F32_add -> "f32_add"
    | F32_sub -> "f32_sub"
    | F32_mul -> "f32_mul"
    | F32_div -> "f32_div"
    | F32_min -> "f32_min"
    | F32_max -> "f32_max"
    | F32_copysign -> "f32_copysign"
    | F64_abs -> "f64_abs"
    | F64_neg -> "f64_neg"
    | F64_ceil -> "f64_ceil"
    | F64_floor -> "f64_floor"
    | F64_trunc -> "f64_trunc"
    | F64_nearest -> "f64_nearest"
    | F64_sqrt -> "f64_sqrt"
    | F64_add -> "f64_add"
    | F64_sub -> "f64_sub"
    | F64_mul -> "f64_mul"
    | F64_div -> "f64_div"
    | F64_min -> "f64_min"
    | F64_max -> "f64_max"
    | F64_copysign -> "f64_copysign"
    | I32_wrap_i64 -> "i32_wrap_i64"
    | I32_trunc_f32_s -> "i32_trunc_f32_s"
    | I32_trunc_f32_u -> "i32_trunc_f32_u"
    | I32_trunc_f64_s -> "i32_trunc_f64_s"
    | I32_trunc_f64_u -> "i32_trunc_f64_u"
    | I64_extend_i32_s -> "i64_extend_i32_s"
    | I64_extend_i32_u -> "i64_extend_i32_u"
    | I64_trunc_f32_s -> "i64_trunc_f32_s"
    | I64_trunc_f32_u -> "i64_trunc_f32_u"
    | I64_trunc_f64_s -> "i64_trunc_f64_s"
    | I64_trunc_f64_u -> "i64_trunc_f64_u"
    | F32_convert_i32_s -> "f32_convert_i32_s"
    | F32_convert_i32_u -> "f32_convert_i32_u"
    | F32_convert_i64_s -> "f32_convert_i64_s"
    | F32_convert_i64_u -> "f32_convert_i64_u"
    | F32_demote_f64 -> "f32_demote_f64"
    | F64_convert_i32_s -> "f64_convert_i32_s"
    | F64_convert_i32_u -> "f64_convert_i32_u"
    | F64_convert_i64_s -> "f64_convert_i64_s"
    | F64_convert_i64_u -> "f64_convert_i64_u"
    | F64_promote_f32 -> "f64_promote_f32"
    | I32_reinterpret_f32 -> "i32_reinterpret_f32"
    | I64_reinterpret_f64 -> "i64_reinterpret_f64"
    | F32_reinterpret_i32 -> "f32_reinterpret_i32"
    | F64_reinterpret_i64 -> "f64_reinterpret_i64"
    | End_of_contiguous_instructions -> "end_of_contiguous_instructions"
let (aux_insn_label_enum :
  (aux_insn_label, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Unreachable, (FStar_UInt8.uint_to_t Prims.int_zero));
  (Nop, (FStar_UInt8.uint_to_t Prims.int_one));
  (Block, (FStar_UInt8.uint_to_t (Prims.of_int (2))));
  (Loop, (FStar_UInt8.uint_to_t (Prims.of_int (3))));
  (If_, (FStar_UInt8.uint_to_t (Prims.of_int (4))));
  (Br, (FStar_UInt8.uint_to_t (Prims.of_int (12))));
  (Br_if, (FStar_UInt8.uint_to_t (Prims.of_int (13))));
  (Br_table, (FStar_UInt8.uint_to_t (Prims.of_int (14))));
  (Ret, (FStar_UInt8.uint_to_t (Prims.of_int (15))));
  (Call, (FStar_UInt8.uint_to_t (Prims.of_int (16))));
  (Call_indirect, (FStar_UInt8.uint_to_t (Prims.of_int (17))));
  (Drop, (FStar_UInt8.uint_to_t (Prims.of_int (26))));
  (Select_, (FStar_UInt8.uint_to_t (Prims.of_int (27))));
  (Local_get, (FStar_UInt8.uint_to_t (Prims.of_int (32))));
  (Local_set, (FStar_UInt8.uint_to_t (Prims.of_int (33))));
  (Local_tee, (FStar_UInt8.uint_to_t (Prims.of_int (34))));
  (Global_get, (FStar_UInt8.uint_to_t (Prims.of_int (35))));
  (Global_set, (FStar_UInt8.uint_to_t (Prims.of_int (36))));
  (I32_load, (FStar_UInt8.uint_to_t (Prims.of_int (40))));
  (I64_load, (FStar_UInt8.uint_to_t (Prims.of_int (41))));
  (F32_load, (FStar_UInt8.uint_to_t (Prims.of_int (42))));
  (F64_load, (FStar_UInt8.uint_to_t (Prims.of_int (43))));
  (I32_load8_s, (FStar_UInt8.uint_to_t (Prims.of_int (44))));
  (I32_load8_u, (FStar_UInt8.uint_to_t (Prims.of_int (45))));
  (I32_load16_s, (FStar_UInt8.uint_to_t (Prims.of_int (46))));
  (I32_load16_u, (FStar_UInt8.uint_to_t (Prims.of_int (47))));
  (I64_load8_s, (FStar_UInt8.uint_to_t (Prims.of_int (48))));
  (I64_load8_u, (FStar_UInt8.uint_to_t (Prims.of_int (49))));
  (I64_load16_s, (FStar_UInt8.uint_to_t (Prims.of_int (50))));
  (I64_load16_u, (FStar_UInt8.uint_to_t (Prims.of_int (51))));
  (I64_load32_s, (FStar_UInt8.uint_to_t (Prims.of_int (52))));
  (I64_load32_u, (FStar_UInt8.uint_to_t (Prims.of_int (53))));
  (I32_store, (FStar_UInt8.uint_to_t (Prims.of_int (54))));
  (I64_store, (FStar_UInt8.uint_to_t (Prims.of_int (55))));
  (F32_store, (FStar_UInt8.uint_to_t (Prims.of_int (56))));
  (F64_store, (FStar_UInt8.uint_to_t (Prims.of_int (57))));
  (I32_store8, (FStar_UInt8.uint_to_t (Prims.of_int (58))));
  (I32_store16, (FStar_UInt8.uint_to_t (Prims.of_int (59))));
  (I64_store8, (FStar_UInt8.uint_to_t (Prims.of_int (60))));
  (I64_store16, (FStar_UInt8.uint_to_t (Prims.of_int (61))));
  (I64_store32, (FStar_UInt8.uint_to_t (Prims.of_int (62))));
  (Memory_size, (FStar_UInt8.uint_to_t (Prims.of_int (63))));
  (Memory_grow, (FStar_UInt8.uint_to_t (Prims.of_int (64))));
  (I32_const, (FStar_UInt8.uint_to_t (Prims.of_int (65))));
  (I64_const, (FStar_UInt8.uint_to_t (Prims.of_int (66))));
  (F32_const, (FStar_UInt8.uint_to_t (Prims.of_int (67))));
  (F64_const, (FStar_UInt8.uint_to_t (Prims.of_int (68))));
  (I32_eqz, (FStar_UInt8.uint_to_t (Prims.of_int (69))));
  (I32_eq, (FStar_UInt8.uint_to_t (Prims.of_int (70))));
  (I32_ne, (FStar_UInt8.uint_to_t (Prims.of_int (71))));
  (I32_lt_s, (FStar_UInt8.uint_to_t (Prims.of_int (72))));
  (I32_lt_u, (FStar_UInt8.uint_to_t (Prims.of_int (73))));
  (I32_gt_s, (FStar_UInt8.uint_to_t (Prims.of_int (74))));
  (I32_gt_u, (FStar_UInt8.uint_to_t (Prims.of_int (75))));
  (I32_le_s, (FStar_UInt8.uint_to_t (Prims.of_int (76))));
  (I32_le_u, (FStar_UInt8.uint_to_t (Prims.of_int (77))));
  (I32_ge_s, (FStar_UInt8.uint_to_t (Prims.of_int (78))));
  (I32_ge_u, (FStar_UInt8.uint_to_t (Prims.of_int (79))));
  (I64_eqz, (FStar_UInt8.uint_to_t (Prims.of_int (80))));
  (I64_eq, (FStar_UInt8.uint_to_t (Prims.of_int (81))));
  (I64_ne, (FStar_UInt8.uint_to_t (Prims.of_int (82))));
  (I64_lt_s, (FStar_UInt8.uint_to_t (Prims.of_int (83))));
  (I64_lt_u, (FStar_UInt8.uint_to_t (Prims.of_int (84))));
  (I64_gt_s, (FStar_UInt8.uint_to_t (Prims.of_int (85))));
  (I64_gt_u, (FStar_UInt8.uint_to_t (Prims.of_int (86))));
  (I64_le_s, (FStar_UInt8.uint_to_t (Prims.of_int (87))));
  (I64_le_u, (FStar_UInt8.uint_to_t (Prims.of_int (88))));
  (I64_ge_s, (FStar_UInt8.uint_to_t (Prims.of_int (89))));
  (I64_ge_u, (FStar_UInt8.uint_to_t (Prims.of_int (90))));
  (F32_eq, (FStar_UInt8.uint_to_t (Prims.of_int (91))));
  (F32_ne, (FStar_UInt8.uint_to_t (Prims.of_int (92))));
  (F32_lt, (FStar_UInt8.uint_to_t (Prims.of_int (93))));
  (F32_gt, (FStar_UInt8.uint_to_t (Prims.of_int (94))));
  (F32_le, (FStar_UInt8.uint_to_t (Prims.of_int (95))));
  (F32_ge, (FStar_UInt8.uint_to_t (Prims.of_int (96))));
  (F64_eq, (FStar_UInt8.uint_to_t (Prims.of_int (97))));
  (F64_ne, (FStar_UInt8.uint_to_t (Prims.of_int (98))));
  (F64_lt, (FStar_UInt8.uint_to_t (Prims.of_int (99))));
  (F64_gt, (FStar_UInt8.uint_to_t (Prims.of_int (100))));
  (F64_le, (FStar_UInt8.uint_to_t (Prims.of_int (101))));
  (F64_ge, (FStar_UInt8.uint_to_t (Prims.of_int (102))));
  (I32_clz, (FStar_UInt8.uint_to_t (Prims.of_int (103))));
  (I32_ctz, (FStar_UInt8.uint_to_t (Prims.of_int (104))));
  (I32_popcnt, (FStar_UInt8.uint_to_t (Prims.of_int (105))));
  (I32_add, (FStar_UInt8.uint_to_t (Prims.of_int (106))));
  (I32_sub, (FStar_UInt8.uint_to_t (Prims.of_int (107))));
  (I32_mul, (FStar_UInt8.uint_to_t (Prims.of_int (108))));
  (I32_div_s, (FStar_UInt8.uint_to_t (Prims.of_int (109))));
  (I32_div_u, (FStar_UInt8.uint_to_t (Prims.of_int (110))));
  (I32_rem_s, (FStar_UInt8.uint_to_t (Prims.of_int (111))));
  (I32_rem_u, (FStar_UInt8.uint_to_t (Prims.of_int (112))));
  (I32_and, (FStar_UInt8.uint_to_t (Prims.of_int (113))));
  (I32_or, (FStar_UInt8.uint_to_t (Prims.of_int (114))));
  (I32_xor, (FStar_UInt8.uint_to_t (Prims.of_int (115))));
  (I32_shl, (FStar_UInt8.uint_to_t (Prims.of_int (116))));
  (I32_shr_s, (FStar_UInt8.uint_to_t (Prims.of_int (117))));
  (I32_shr_u, (FStar_UInt8.uint_to_t (Prims.of_int (118))));
  (I32_rotl, (FStar_UInt8.uint_to_t (Prims.of_int (119))));
  (I32_rotr, (FStar_UInt8.uint_to_t (Prims.of_int (120))));
  (I64_clz, (FStar_UInt8.uint_to_t (Prims.of_int (121))));
  (I64_ctz, (FStar_UInt8.uint_to_t (Prims.of_int (122))));
  (I64_popcnt, (FStar_UInt8.uint_to_t (Prims.of_int (123))));
  (I64_add, (FStar_UInt8.uint_to_t (Prims.of_int (124))));
  (I64_sub, (FStar_UInt8.uint_to_t (Prims.of_int (125))));
  (I64_mul, (FStar_UInt8.uint_to_t (Prims.of_int (126))));
  (I64_div_s, (FStar_UInt8.uint_to_t (Prims.of_int (127))));
  (I64_div_u, (FStar_UInt8.uint_to_t (Prims.of_int (128))));
  (I64_rem_s, (FStar_UInt8.uint_to_t (Prims.of_int (129))));
  (I64_rem_u, (FStar_UInt8.uint_to_t (Prims.of_int (130))));
  (I64_and, (FStar_UInt8.uint_to_t (Prims.of_int (131))));
  (I64_or, (FStar_UInt8.uint_to_t (Prims.of_int (132))));
  (I64_xor, (FStar_UInt8.uint_to_t (Prims.of_int (133))));
  (I64_shl, (FStar_UInt8.uint_to_t (Prims.of_int (134))));
  (I64_shr_s, (FStar_UInt8.uint_to_t (Prims.of_int (135))));
  (I64_shr_u, (FStar_UInt8.uint_to_t (Prims.of_int (136))));
  (I64_rotl, (FStar_UInt8.uint_to_t (Prims.of_int (137))));
  (I64_rotr, (FStar_UInt8.uint_to_t (Prims.of_int (138))));
  (F32_abs, (FStar_UInt8.uint_to_t (Prims.of_int (139))));
  (F32_neg, (FStar_UInt8.uint_to_t (Prims.of_int (140))));
  (F32_ceil, (FStar_UInt8.uint_to_t (Prims.of_int (141))));
  (F32_floor, (FStar_UInt8.uint_to_t (Prims.of_int (142))));
  (F32_trunc, (FStar_UInt8.uint_to_t (Prims.of_int (143))));
  (F32_nearest, (FStar_UInt8.uint_to_t (Prims.of_int (144))));
  (F32_sqrt, (FStar_UInt8.uint_to_t (Prims.of_int (145))));
  (F32_add, (FStar_UInt8.uint_to_t (Prims.of_int (146))));
  (F32_sub, (FStar_UInt8.uint_to_t (Prims.of_int (147))));
  (F32_mul, (FStar_UInt8.uint_to_t (Prims.of_int (148))));
  (F32_div, (FStar_UInt8.uint_to_t (Prims.of_int (149))));
  (F32_min, (FStar_UInt8.uint_to_t (Prims.of_int (150))));
  (F32_max, (FStar_UInt8.uint_to_t (Prims.of_int (151))));
  (F32_copysign, (FStar_UInt8.uint_to_t (Prims.of_int (152))));
  (F64_abs, (FStar_UInt8.uint_to_t (Prims.of_int (153))));
  (F64_neg, (FStar_UInt8.uint_to_t (Prims.of_int (154))));
  (F64_ceil, (FStar_UInt8.uint_to_t (Prims.of_int (155))));
  (F64_floor, (FStar_UInt8.uint_to_t (Prims.of_int (156))));
  (F64_trunc, (FStar_UInt8.uint_to_t (Prims.of_int (157))));
  (F64_nearest, (FStar_UInt8.uint_to_t (Prims.of_int (158))));
  (F64_sqrt, (FStar_UInt8.uint_to_t (Prims.of_int (159))));
  (F64_add, (FStar_UInt8.uint_to_t (Prims.of_int (160))));
  (F64_sub, (FStar_UInt8.uint_to_t (Prims.of_int (161))));
  (F64_mul, (FStar_UInt8.uint_to_t (Prims.of_int (162))));
  (F64_div, (FStar_UInt8.uint_to_t (Prims.of_int (163))));
  (F64_min, (FStar_UInt8.uint_to_t (Prims.of_int (164))));
  (F64_max, (FStar_UInt8.uint_to_t (Prims.of_int (165))));
  (F64_copysign, (FStar_UInt8.uint_to_t (Prims.of_int (166))));
  (I32_wrap_i64, (FStar_UInt8.uint_to_t (Prims.of_int (167))));
  (I32_trunc_f32_s, (FStar_UInt8.uint_to_t (Prims.of_int (168))));
  (I32_trunc_f32_u, (FStar_UInt8.uint_to_t (Prims.of_int (169))));
  (I32_trunc_f64_s, (FStar_UInt8.uint_to_t (Prims.of_int (170))));
  (I32_trunc_f64_u, (FStar_UInt8.uint_to_t (Prims.of_int (171))));
  (I64_extend_i32_s, (FStar_UInt8.uint_to_t (Prims.of_int (172))));
  (I64_extend_i32_u, (FStar_UInt8.uint_to_t (Prims.of_int (173))));
  (I64_trunc_f32_s, (FStar_UInt8.uint_to_t (Prims.of_int (174))));
  (I64_trunc_f32_u, (FStar_UInt8.uint_to_t (Prims.of_int (175))));
  (I64_trunc_f64_s, (FStar_UInt8.uint_to_t (Prims.of_int (176))));
  (I64_trunc_f64_u, (FStar_UInt8.uint_to_t (Prims.of_int (177))));
  (F32_convert_i32_s, (FStar_UInt8.uint_to_t (Prims.of_int (178))));
  (F32_convert_i32_u, (FStar_UInt8.uint_to_t (Prims.of_int (179))));
  (F32_convert_i64_s, (FStar_UInt8.uint_to_t (Prims.of_int (180))));
  (F32_convert_i64_u, (FStar_UInt8.uint_to_t (Prims.of_int (181))));
  (F32_demote_f64, (FStar_UInt8.uint_to_t (Prims.of_int (182))));
  (F64_convert_i32_s, (FStar_UInt8.uint_to_t (Prims.of_int (183))));
  (F64_convert_i32_u, (FStar_UInt8.uint_to_t (Prims.of_int (184))));
  (F64_convert_i64_s, (FStar_UInt8.uint_to_t (Prims.of_int (185))));
  (F64_convert_i64_u, (FStar_UInt8.uint_to_t (Prims.of_int (186))));
  (F64_promote_f32, (FStar_UInt8.uint_to_t (Prims.of_int (187))));
  (I32_reinterpret_f32, (FStar_UInt8.uint_to_t (Prims.of_int (188))));
  (I64_reinterpret_f64, (FStar_UInt8.uint_to_t (Prims.of_int (189))));
  (F32_reinterpret_i32, (FStar_UInt8.uint_to_t (Prims.of_int (190))));
  (F64_reinterpret_i64, (FStar_UInt8.uint_to_t (Prims.of_int (191))));
  (End_of_contiguous_instructions,
    (FStar_UInt8.uint_to_t (Prims.of_int (255))))]
let (synth_aux_insn_label : aux_insn_label -> aux_insn_label) = fun x -> x
let (synth_aux_insn_label_inv : aux_insn_label -> aux_insn_label) =
  fun x -> x


let (parse32_aux_insn_label_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_insn_label * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                  then LowParse_Spec_Enum.Known Unreachable
                  else
                    (let y =
                       if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                       then LowParse_Spec_Enum.Known Nop
                       else
                         (let y1 =
                            if
                              (FStar_UInt8.uint_to_t (Prims.of_int (2))) = v1
                            then LowParse_Spec_Enum.Known Block
                            else
                              (let y2 =
                                 if
                                   (FStar_UInt8.uint_to_t (Prims.of_int (3)))
                                     = v1
                                 then LowParse_Spec_Enum.Known Loop
                                 else
                                   (let y3 =
                                      if
                                        (FStar_UInt8.uint_to_t
                                           (Prims.of_int (4)))
                                          = v1
                                      then LowParse_Spec_Enum.Known If_
                                      else
                                        (let y4 =
                                           if
                                             (FStar_UInt8.uint_to_t
                                                (Prims.of_int (12)))
                                               = v1
                                           then LowParse_Spec_Enum.Known Br
                                           else
                                             (let y5 =
                                                if
                                                  (FStar_UInt8.uint_to_t
                                                     (Prims.of_int (13)))
                                                    = v1
                                                then
                                                  LowParse_Spec_Enum.Known
                                                    Br_if
                                                else
                                                  (let y6 =
                                                     if
                                                       (FStar_UInt8.uint_to_t
                                                          (Prims.of_int (14)))
                                                         = v1
                                                     then
                                                       LowParse_Spec_Enum.Known
                                                         Br_table
                                                     else
                                                       (let y7 =
                                                          if
                                                            (FStar_UInt8.uint_to_t
                                                               (Prims.of_int (15)))
                                                              = v1
                                                          then
                                                            LowParse_Spec_Enum.Known
                                                              Ret
                                                          else
                                                            (let y8 =
                                                               if
                                                                 (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (16)))
                                                                   = v1
                                                               then
                                                                 LowParse_Spec_Enum.Known
                                                                   Call
                                                               else
                                                                 (let y9 =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (17)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Call_indirect
                                                                    else
                                                                    (let y10
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (26)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Drop
                                                                    else
                                                                    (let y11
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (27)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Select_
                                                                    else
                                                                    (let y12
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (32)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Local_get
                                                                    else
                                                                    (let y13
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (33)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Local_set
                                                                    else
                                                                    (let y14
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (34)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Local_tee
                                                                    else
                                                                    (let y15
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (35)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Global_get
                                                                    else
                                                                    (let y16
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (36)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Global_set
                                                                    else
                                                                    (let y17
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (40)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_load
                                                                    else
                                                                    (let y18
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (41)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load
                                                                    else
                                                                    (let y19
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (42)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_load
                                                                    else
                                                                    (let y20
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (43)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_load
                                                                    else
                                                                    (let y21
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (44)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_load8_s
                                                                    else
                                                                    (let y22
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (45)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_load8_u
                                                                    else
                                                                    (let y23
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (46)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_load16_s
                                                                    else
                                                                    (let y24
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (47)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_load16_u
                                                                    else
                                                                    (let y25
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (48)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load8_s
                                                                    else
                                                                    (let y26
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (49)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load8_u
                                                                    else
                                                                    (let y27
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (50)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load16_s
                                                                    else
                                                                    (let y28
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (51)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load16_u
                                                                    else
                                                                    (let y29
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (52)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load32_s
                                                                    else
                                                                    (let y30
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (53)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_load32_u
                                                                    else
                                                                    (let y31
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (54)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_store
                                                                    else
                                                                    (let y32
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (55)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_store
                                                                    else
                                                                    (let y33
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (56)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_store
                                                                    else
                                                                    (let y34
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (57)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_store
                                                                    else
                                                                    (let y35
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (58)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_store8
                                                                    else
                                                                    (let y36
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (59)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_store16
                                                                    else
                                                                    (let y37
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (60)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_store8
                                                                    else
                                                                    (let y38
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (61)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_store16
                                                                    else
                                                                    (let y39
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (62)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_store32
                                                                    else
                                                                    (let y40
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (63)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Memory_size
                                                                    else
                                                                    (let y41
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (64)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    Memory_grow
                                                                    else
                                                                    (let y42
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (65)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_const
                                                                    else
                                                                    (let y43
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (66)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_const
                                                                    else
                                                                    (let y44
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (67)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_const
                                                                    else
                                                                    (let y45
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (68)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_const
                                                                    else
                                                                    (let y46
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (69)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_eqz
                                                                    else
                                                                    (let y47
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (70)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_eq
                                                                    else
                                                                    (let y48
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (71)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_ne
                                                                    else
                                                                    (let y49
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (72)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_lt_s
                                                                    else
                                                                    (let y50
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (73)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_lt_u
                                                                    else
                                                                    (let y51
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (74)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_gt_s
                                                                    else
                                                                    (let y52
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (75)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_gt_u
                                                                    else
                                                                    (let y53
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (76)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_le_s
                                                                    else
                                                                    (let y54
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (77)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_le_u
                                                                    else
                                                                    (let y55
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (78)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_ge_s
                                                                    else
                                                                    (let y56
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (79)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_ge_u
                                                                    else
                                                                    (let y57
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (80)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_eqz
                                                                    else
                                                                    (let y58
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (81)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_eq
                                                                    else
                                                                    (let y59
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (82)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_ne
                                                                    else
                                                                    (let y60
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (83)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_lt_s
                                                                    else
                                                                    (let y61
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (84)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_lt_u
                                                                    else
                                                                    (let y62
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (85)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_gt_s
                                                                    else
                                                                    (let y63
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (86)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_gt_u
                                                                    else
                                                                    (let y64
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (87)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_le_s
                                                                    else
                                                                    (let y65
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (88)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_le_u
                                                                    else
                                                                    (let y66
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (89)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_ge_s
                                                                    else
                                                                    (let y67
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (90)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_ge_u
                                                                    else
                                                                    (let y68
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (91)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_eq
                                                                    else
                                                                    (let y69
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (92)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_ne
                                                                    else
                                                                    (let y70
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (93)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_lt
                                                                    else
                                                                    (let y71
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (94)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_gt
                                                                    else
                                                                    (let y72
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (95)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_le
                                                                    else
                                                                    (let y73
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (96)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_ge
                                                                    else
                                                                    (let y74
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (97)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_eq
                                                                    else
                                                                    (let y75
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (98)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_ne
                                                                    else
                                                                    (let y76
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (99)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_lt
                                                                    else
                                                                    (let y77
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (100)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_gt
                                                                    else
                                                                    (let y78
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (101)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_le
                                                                    else
                                                                    (let y79
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (102)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_ge
                                                                    else
                                                                    (let y80
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (103)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_clz
                                                                    else
                                                                    (let y81
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (104)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_ctz
                                                                    else
                                                                    (let y82
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (105)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_popcnt
                                                                    else
                                                                    (let y83
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (106)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_add
                                                                    else
                                                                    (let y84
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (107)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_sub
                                                                    else
                                                                    (let y85
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (108)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_mul
                                                                    else
                                                                    (let y86
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (109)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_div_s
                                                                    else
                                                                    (let y87
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (110)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_div_u
                                                                    else
                                                                    (let y88
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (111)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_rem_s
                                                                    else
                                                                    (let y89
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (112)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_rem_u
                                                                    else
                                                                    (let y90
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (113)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_and
                                                                    else
                                                                    (let y91
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (114)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_or
                                                                    else
                                                                    (let y92
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (115)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_xor
                                                                    else
                                                                    (let y93
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (116)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_shl
                                                                    else
                                                                    (let y94
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (117)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_shr_s
                                                                    else
                                                                    (let y95
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (118)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_shr_u
                                                                    else
                                                                    (let y96
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (119)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_rotl
                                                                    else
                                                                    (let y97
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (120)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_rotr
                                                                    else
                                                                    (let y98
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (121)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_clz
                                                                    else
                                                                    (let y99
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (122)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_ctz
                                                                    else
                                                                    (let y100
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (123)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_popcnt
                                                                    else
                                                                    (let y101
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (124)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_add
                                                                    else
                                                                    (let y102
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (125)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_sub
                                                                    else
                                                                    (let y103
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (126)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_mul
                                                                    else
                                                                    (let y104
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (127)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_div_s
                                                                    else
                                                                    (let y105
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (128)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_div_u
                                                                    else
                                                                    (let y106
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (129)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_rem_s
                                                                    else
                                                                    (let y107
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (130)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_rem_u
                                                                    else
                                                                    (let y108
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (131)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_and
                                                                    else
                                                                    (let y109
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (132)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_or
                                                                    else
                                                                    (let y110
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (133)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_xor
                                                                    else
                                                                    (let y111
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (134)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_shl
                                                                    else
                                                                    (let y112
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (135)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_shr_s
                                                                    else
                                                                    (let y113
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (136)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_shr_u
                                                                    else
                                                                    (let y114
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (137)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_rotl
                                                                    else
                                                                    (let y115
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (138)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_rotr
                                                                    else
                                                                    (let y116
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (139)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_abs
                                                                    else
                                                                    (let y117
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (140)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_neg
                                                                    else
                                                                    (let y118
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (141)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_ceil
                                                                    else
                                                                    (let y119
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (142)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_floor
                                                                    else
                                                                    (let y120
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (143)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_trunc
                                                                    else
                                                                    (let y121
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (144)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_nearest
                                                                    else
                                                                    (let y122
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (145)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_sqrt
                                                                    else
                                                                    (let y123
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (146)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_add
                                                                    else
                                                                    (let y124
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (147)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_sub
                                                                    else
                                                                    (let y125
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (148)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_mul
                                                                    else
                                                                    (let y126
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (149)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_div
                                                                    else
                                                                    (let y127
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (150)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_min
                                                                    else
                                                                    (let y128
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (151)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_max
                                                                    else
                                                                    (let y129
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (152)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_copysign
                                                                    else
                                                                    (let y130
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (153)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_abs
                                                                    else
                                                                    (let y131
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (154)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_neg
                                                                    else
                                                                    (let y132
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (155)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_ceil
                                                                    else
                                                                    (let y133
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (156)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_floor
                                                                    else
                                                                    (let y134
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (157)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_trunc
                                                                    else
                                                                    (let y135
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (158)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_nearest
                                                                    else
                                                                    (let y136
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (159)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_sqrt
                                                                    else
                                                                    (let y137
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (160)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_add
                                                                    else
                                                                    (let y138
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (161)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_sub
                                                                    else
                                                                    (let y139
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (162)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_mul
                                                                    else
                                                                    (let y140
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (163)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_div
                                                                    else
                                                                    (let y141
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (164)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_min
                                                                    else
                                                                    (let y142
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (165)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_max
                                                                    else
                                                                    (let y143
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (166)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_copysign
                                                                    else
                                                                    (let y144
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (167)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_wrap_i64
                                                                    else
                                                                    (let y145
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (168)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_trunc_f32_s
                                                                    else
                                                                    (let y146
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (169)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_trunc_f32_u
                                                                    else
                                                                    (let y147
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (170)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_trunc_f64_s
                                                                    else
                                                                    (let y148
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (171)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_trunc_f64_u
                                                                    else
                                                                    (let y149
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (172)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_extend_i32_s
                                                                    else
                                                                    (let y150
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (173)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_extend_i32_u
                                                                    else
                                                                    (let y151
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (174)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_trunc_f32_s
                                                                    else
                                                                    (let y152
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (175)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_trunc_f32_u
                                                                    else
                                                                    (let y153
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (176)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_trunc_f64_s
                                                                    else
                                                                    (let y154
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (177)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_trunc_f64_u
                                                                    else
                                                                    (let y155
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (178)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_convert_i32_s
                                                                    else
                                                                    (let y156
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (179)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_convert_i32_u
                                                                    else
                                                                    (let y157
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (180)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_convert_i64_s
                                                                    else
                                                                    (let y158
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (181)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_convert_i64_u
                                                                    else
                                                                    (let y159
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (182)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_demote_f64
                                                                    else
                                                                    (let y160
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (183)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_convert_i32_s
                                                                    else
                                                                    (let y161
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (184)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_convert_i32_u
                                                                    else
                                                                    (let y162
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (185)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_convert_i64_s
                                                                    else
                                                                    (let y163
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (186)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_convert_i64_u
                                                                    else
                                                                    (let y164
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (187)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_promote_f32
                                                                    else
                                                                    (let y165
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (188)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I32_reinterpret_f32
                                                                    else
                                                                    (let y166
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (189)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    I64_reinterpret_f64
                                                                    else
                                                                    (let y167
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (190)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F32_reinterpret_i32
                                                                    else
                                                                    (let y168
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (191)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    F64_reinterpret_i64
                                                                    else
                                                                    (let y169
                                                                    =
                                                                    if
                                                                    (FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (255)))
                                                                    = v1
                                                                    then
                                                                    LowParse_Spec_Enum.Known
                                                                    End_of_contiguous_instructions
                                                                    else
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1 in
                                                                    match y169
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y168
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y167
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y166
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y165
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y164
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y163
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y162
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y161
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y160
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y159
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y158
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y157
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y156
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y155
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y154
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y153
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y152
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y151
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y150
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y149
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y148
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y147
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y146
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y145
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y144
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y143
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y142
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y141
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y140
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y139
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y138
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y137
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y136
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y135
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y134
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y133
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y132
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y131
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y130
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y129
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y128
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y127
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y126
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y125
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y124
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y123
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y122
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y121
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y120
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y119
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y118
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y117
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y116
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y115
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y114
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y113
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y112
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y111
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y110
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y109
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y108
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y107
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y106
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y105
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y104
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y103
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y102
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y101
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y100
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y99
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y98
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y97
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y96
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y95
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y94
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y93
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y92
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y91
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y90
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y89
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y88
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y87
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y86
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y85
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y84
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y83
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y82
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y81
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y80
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y79
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y78
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y77
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y76
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y75
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y74
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y73
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y72
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y71
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y70
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y69
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y68
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y67
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y66
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y65
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y64
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y63
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y62
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y61
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y60
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y59
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y58
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y57
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y56
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y55
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y54
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y53
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y52
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y51
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y50
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y49
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y48
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y47
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y46
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y45
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y44
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y43
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y42
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y41
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y40
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y39
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y38
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y37
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y36
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y35
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y34
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y33
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y32
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y31
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y30
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y29
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y28
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y27
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y26
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y25
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y24
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y23
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y22
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y21
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y20
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y19
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y18
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y17
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y16
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y15
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y14
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y13
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y12
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y11
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                    match y10
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                                  match y9
                                                                  with
                                                                  | LowParse_Spec_Enum.Known
                                                                    k' ->
                                                                    LowParse_Spec_Enum.Known
                                                                    k'
                                                                  | LowParse_Spec_Enum.Unknown
                                                                    x' ->
                                                                    LowParse_Spec_Enum.Unknown
                                                                    v1) in
                                                             match y8 with
                                                             | LowParse_Spec_Enum.Known
                                                                 k' ->
                                                                 LowParse_Spec_Enum.Known
                                                                   k'
                                                             | LowParse_Spec_Enum.Unknown
                                                                 x' ->
                                                                 LowParse_Spec_Enum.Unknown
                                                                   v1) in
                                                        match y7 with
                                                        | LowParse_Spec_Enum.Known
                                                            k' ->
                                                            LowParse_Spec_Enum.Known
                                                              k'
                                                        | LowParse_Spec_Enum.Unknown
                                                            x' ->
                                                            LowParse_Spec_Enum.Unknown
                                                              v1) in
                                                   match y6 with
                                                   | LowParse_Spec_Enum.Known
                                                       k' ->
                                                       LowParse_Spec_Enum.Known
                                                         k'
                                                   | LowParse_Spec_Enum.Unknown
                                                       x' ->
                                                       LowParse_Spec_Enum.Unknown
                                                         v1) in
                                              match y5 with
                                              | LowParse_Spec_Enum.Known k'
                                                  ->
                                                  LowParse_Spec_Enum.Known k'
                                              | LowParse_Spec_Enum.Unknown x'
                                                  ->
                                                  LowParse_Spec_Enum.Unknown
                                                    v1) in
                                         match y4 with
                                         | LowParse_Spec_Enum.Known k' ->
                                             LowParse_Spec_Enum.Known k'
                                         | LowParse_Spec_Enum.Unknown x' ->
                                             LowParse_Spec_Enum.Unknown v1) in
                                    match y3 with
                                    | LowParse_Spec_Enum.Known k' ->
                                        LowParse_Spec_Enum.Known k'
                                    | LowParse_Spec_Enum.Unknown x' ->
                                        LowParse_Spec_Enum.Unknown v1) in
                               match y2 with
                               | LowParse_Spec_Enum.Known k' ->
                                   LowParse_Spec_Enum.Known k'
                               | LowParse_Spec_Enum.Unknown x' ->
                                   LowParse_Spec_Enum.Unknown v1) in
                          match y1 with
                          | LowParse_Spec_Enum.Known k' ->
                              LowParse_Spec_Enum.Known k'
                          | LowParse_Spec_Enum.Unknown x' ->
                              LowParse_Spec_Enum.Unknown v1) in
                     match y with
                     | LowParse_Spec_Enum.Known k' ->
                         LowParse_Spec_Enum.Known k'
                     | LowParse_Spec_Enum.Unknown x' ->
                         LowParse_Spec_Enum.Unknown v1)), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_insn_label_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_insn_label * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_insn_label_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_insn_label_key :
  aux_insn_label -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if Unreachable = input
       then FStar_UInt8.uint_to_t Prims.int_zero
       else
         if Nop = input
         then FStar_UInt8.uint_to_t Prims.int_one
         else
           if Block = input
           then FStar_UInt8.uint_to_t (Prims.of_int (2))
           else
             if Loop = input
             then FStar_UInt8.uint_to_t (Prims.of_int (3))
             else
               if If_ = input
               then FStar_UInt8.uint_to_t (Prims.of_int (4))
               else
                 if Br = input
                 then FStar_UInt8.uint_to_t (Prims.of_int (12))
                 else
                   if Br_if = input
                   then FStar_UInt8.uint_to_t (Prims.of_int (13))
                   else
                     if Br_table = input
                     then FStar_UInt8.uint_to_t (Prims.of_int (14))
                     else
                       if Ret = input
                       then FStar_UInt8.uint_to_t (Prims.of_int (15))
                       else
                         if Call = input
                         then FStar_UInt8.uint_to_t (Prims.of_int (16))
                         else
                           if Call_indirect = input
                           then FStar_UInt8.uint_to_t (Prims.of_int (17))
                           else
                             if Drop = input
                             then FStar_UInt8.uint_to_t (Prims.of_int (26))
                             else
                               if Select_ = input
                               then FStar_UInt8.uint_to_t (Prims.of_int (27))
                               else
                                 if Local_get = input
                                 then
                                   FStar_UInt8.uint_to_t (Prims.of_int (32))
                                 else
                                   if Local_set = input
                                   then
                                     FStar_UInt8.uint_to_t
                                       (Prims.of_int (33))
                                   else
                                     if Local_tee = input
                                     then
                                       FStar_UInt8.uint_to_t
                                         (Prims.of_int (34))
                                     else
                                       if Global_get = input
                                       then
                                         FStar_UInt8.uint_to_t
                                           (Prims.of_int (35))
                                       else
                                         if Global_set = input
                                         then
                                           FStar_UInt8.uint_to_t
                                             (Prims.of_int (36))
                                         else
                                           if I32_load = input
                                           then
                                             FStar_UInt8.uint_to_t
                                               (Prims.of_int (40))
                                           else
                                             if I64_load = input
                                             then
                                               FStar_UInt8.uint_to_t
                                                 (Prims.of_int (41))
                                             else
                                               if F32_load = input
                                               then
                                                 FStar_UInt8.uint_to_t
                                                   (Prims.of_int (42))
                                               else
                                                 if F64_load = input
                                                 then
                                                   FStar_UInt8.uint_to_t
                                                     (Prims.of_int (43))
                                                 else
                                                   if I32_load8_s = input
                                                   then
                                                     FStar_UInt8.uint_to_t
                                                       (Prims.of_int (44))
                                                   else
                                                     if I32_load8_u = input
                                                     then
                                                       FStar_UInt8.uint_to_t
                                                         (Prims.of_int (45))
                                                     else
                                                       if
                                                         I32_load16_s = input
                                                       then
                                                         FStar_UInt8.uint_to_t
                                                           (Prims.of_int (46))
                                                       else
                                                         if
                                                           I32_load16_u =
                                                             input
                                                         then
                                                           FStar_UInt8.uint_to_t
                                                             (Prims.of_int (47))
                                                         else
                                                           if
                                                             I64_load8_s =
                                                               input
                                                           then
                                                             FStar_UInt8.uint_to_t
                                                               (Prims.of_int (48))
                                                           else
                                                             if
                                                               I64_load8_u =
                                                                 input
                                                             then
                                                               FStar_UInt8.uint_to_t
                                                                 (Prims.of_int (49))
                                                             else
                                                               if
                                                                 I64_load16_s
                                                                   = input
                                                               then
                                                                 FStar_UInt8.uint_to_t
                                                                   (Prims.of_int (50))
                                                               else
                                                                 if
                                                                   I64_load16_u
                                                                    = input
                                                                 then
                                                                   FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (51))
                                                                 else
                                                                   if
                                                                    I64_load32_s
                                                                    = input
                                                                   then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (52))
                                                                   else
                                                                    if
                                                                    I64_load32_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (53))
                                                                    else
                                                                    if
                                                                    I32_store
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (54))
                                                                    else
                                                                    if
                                                                    I64_store
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (55))
                                                                    else
                                                                    if
                                                                    F32_store
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (56))
                                                                    else
                                                                    if
                                                                    F64_store
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (57))
                                                                    else
                                                                    if
                                                                    I32_store8
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (58))
                                                                    else
                                                                    if
                                                                    I32_store16
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (59))
                                                                    else
                                                                    if
                                                                    I64_store8
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (60))
                                                                    else
                                                                    if
                                                                    I64_store16
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (61))
                                                                    else
                                                                    if
                                                                    I64_store32
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (62))
                                                                    else
                                                                    if
                                                                    Memory_size
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (63))
                                                                    else
                                                                    if
                                                                    Memory_grow
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (64))
                                                                    else
                                                                    if
                                                                    I32_const
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (65))
                                                                    else
                                                                    if
                                                                    I64_const
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (66))
                                                                    else
                                                                    if
                                                                    F32_const
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (67))
                                                                    else
                                                                    if
                                                                    F64_const
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (68))
                                                                    else
                                                                    if
                                                                    I32_eqz =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (69))
                                                                    else
                                                                    if
                                                                    I32_eq =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (70))
                                                                    else
                                                                    if
                                                                    I32_ne =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (71))
                                                                    else
                                                                    if
                                                                    I32_lt_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (72))
                                                                    else
                                                                    if
                                                                    I32_lt_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (73))
                                                                    else
                                                                    if
                                                                    I32_gt_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (74))
                                                                    else
                                                                    if
                                                                    I32_gt_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (75))
                                                                    else
                                                                    if
                                                                    I32_le_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (76))
                                                                    else
                                                                    if
                                                                    I32_le_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (77))
                                                                    else
                                                                    if
                                                                    I32_ge_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (78))
                                                                    else
                                                                    if
                                                                    I32_ge_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (79))
                                                                    else
                                                                    if
                                                                    I64_eqz =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (80))
                                                                    else
                                                                    if
                                                                    I64_eq =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (81))
                                                                    else
                                                                    if
                                                                    I64_ne =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (82))
                                                                    else
                                                                    if
                                                                    I64_lt_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (83))
                                                                    else
                                                                    if
                                                                    I64_lt_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (84))
                                                                    else
                                                                    if
                                                                    I64_gt_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (85))
                                                                    else
                                                                    if
                                                                    I64_gt_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (86))
                                                                    else
                                                                    if
                                                                    I64_le_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (87))
                                                                    else
                                                                    if
                                                                    I64_le_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (88))
                                                                    else
                                                                    if
                                                                    I64_ge_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (89))
                                                                    else
                                                                    if
                                                                    I64_ge_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (90))
                                                                    else
                                                                    if
                                                                    F32_eq =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (91))
                                                                    else
                                                                    if
                                                                    F32_ne =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (92))
                                                                    else
                                                                    if
                                                                    F32_lt =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (93))
                                                                    else
                                                                    if
                                                                    F32_gt =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (94))
                                                                    else
                                                                    if
                                                                    F32_le =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (95))
                                                                    else
                                                                    if
                                                                    F32_ge =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (96))
                                                                    else
                                                                    if
                                                                    F64_eq =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (97))
                                                                    else
                                                                    if
                                                                    F64_ne =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (98))
                                                                    else
                                                                    if
                                                                    F64_lt =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (99))
                                                                    else
                                                                    if
                                                                    F64_gt =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (100))
                                                                    else
                                                                    if
                                                                    F64_le =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (101))
                                                                    else
                                                                    if
                                                                    F64_ge =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (102))
                                                                    else
                                                                    if
                                                                    I32_clz =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (103))
                                                                    else
                                                                    if
                                                                    I32_ctz =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (104))
                                                                    else
                                                                    if
                                                                    I32_popcnt
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (105))
                                                                    else
                                                                    if
                                                                    I32_add =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (106))
                                                                    else
                                                                    if
                                                                    I32_sub =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (107))
                                                                    else
                                                                    if
                                                                    I32_mul =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (108))
                                                                    else
                                                                    if
                                                                    I32_div_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (109))
                                                                    else
                                                                    if
                                                                    I32_div_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (110))
                                                                    else
                                                                    if
                                                                    I32_rem_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (111))
                                                                    else
                                                                    if
                                                                    I32_rem_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (112))
                                                                    else
                                                                    if
                                                                    I32_and =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (113))
                                                                    else
                                                                    if
                                                                    I32_or =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (114))
                                                                    else
                                                                    if
                                                                    I32_xor =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (115))
                                                                    else
                                                                    if
                                                                    I32_shl =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (116))
                                                                    else
                                                                    if
                                                                    I32_shr_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (117))
                                                                    else
                                                                    if
                                                                    I32_shr_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (118))
                                                                    else
                                                                    if
                                                                    I32_rotl
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (119))
                                                                    else
                                                                    if
                                                                    I32_rotr
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (120))
                                                                    else
                                                                    if
                                                                    I64_clz =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (121))
                                                                    else
                                                                    if
                                                                    I64_ctz =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (122))
                                                                    else
                                                                    if
                                                                    I64_popcnt
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (123))
                                                                    else
                                                                    if
                                                                    I64_add =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (124))
                                                                    else
                                                                    if
                                                                    I64_sub =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (125))
                                                                    else
                                                                    if
                                                                    I64_mul =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (126))
                                                                    else
                                                                    if
                                                                    I64_div_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (127))
                                                                    else
                                                                    if
                                                                    I64_div_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (128))
                                                                    else
                                                                    if
                                                                    I64_rem_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (129))
                                                                    else
                                                                    if
                                                                    I64_rem_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (130))
                                                                    else
                                                                    if
                                                                    I64_and =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (131))
                                                                    else
                                                                    if
                                                                    I64_or =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (132))
                                                                    else
                                                                    if
                                                                    I64_xor =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (133))
                                                                    else
                                                                    if
                                                                    I64_shl =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (134))
                                                                    else
                                                                    if
                                                                    I64_shr_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (135))
                                                                    else
                                                                    if
                                                                    I64_shr_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (136))
                                                                    else
                                                                    if
                                                                    I64_rotl
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (137))
                                                                    else
                                                                    if
                                                                    I64_rotr
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (138))
                                                                    else
                                                                    if
                                                                    F32_abs =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (139))
                                                                    else
                                                                    if
                                                                    F32_neg =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (140))
                                                                    else
                                                                    if
                                                                    F32_ceil
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (141))
                                                                    else
                                                                    if
                                                                    F32_floor
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (142))
                                                                    else
                                                                    if
                                                                    F32_trunc
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (143))
                                                                    else
                                                                    if
                                                                    F32_nearest
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (144))
                                                                    else
                                                                    if
                                                                    F32_sqrt
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (145))
                                                                    else
                                                                    if
                                                                    F32_add =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (146))
                                                                    else
                                                                    if
                                                                    F32_sub =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (147))
                                                                    else
                                                                    if
                                                                    F32_mul =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (148))
                                                                    else
                                                                    if
                                                                    F32_div =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (149))
                                                                    else
                                                                    if
                                                                    F32_min =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (150))
                                                                    else
                                                                    if
                                                                    F32_max =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (151))
                                                                    else
                                                                    if
                                                                    F32_copysign
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (152))
                                                                    else
                                                                    if
                                                                    F64_abs =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (153))
                                                                    else
                                                                    if
                                                                    F64_neg =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (154))
                                                                    else
                                                                    if
                                                                    F64_ceil
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (155))
                                                                    else
                                                                    if
                                                                    F64_floor
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (156))
                                                                    else
                                                                    if
                                                                    F64_trunc
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (157))
                                                                    else
                                                                    if
                                                                    F64_nearest
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (158))
                                                                    else
                                                                    if
                                                                    F64_sqrt
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (159))
                                                                    else
                                                                    if
                                                                    F64_add =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (160))
                                                                    else
                                                                    if
                                                                    F64_sub =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (161))
                                                                    else
                                                                    if
                                                                    F64_mul =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (162))
                                                                    else
                                                                    if
                                                                    F64_div =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (163))
                                                                    else
                                                                    if
                                                                    F64_min =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (164))
                                                                    else
                                                                    if
                                                                    F64_max =
                                                                    input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (165))
                                                                    else
                                                                    if
                                                                    F64_copysign
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (166))
                                                                    else
                                                                    if
                                                                    I32_wrap_i64
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (167))
                                                                    else
                                                                    if
                                                                    I32_trunc_f32_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (168))
                                                                    else
                                                                    if
                                                                    I32_trunc_f32_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (169))
                                                                    else
                                                                    if
                                                                    I32_trunc_f64_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (170))
                                                                    else
                                                                    if
                                                                    I32_trunc_f64_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (171))
                                                                    else
                                                                    if
                                                                    I64_extend_i32_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (172))
                                                                    else
                                                                    if
                                                                    I64_extend_i32_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (173))
                                                                    else
                                                                    if
                                                                    I64_trunc_f32_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (174))
                                                                    else
                                                                    if
                                                                    I64_trunc_f32_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (175))
                                                                    else
                                                                    if
                                                                    I64_trunc_f64_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (176))
                                                                    else
                                                                    if
                                                                    I64_trunc_f64_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (177))
                                                                    else
                                                                    if
                                                                    F32_convert_i32_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (178))
                                                                    else
                                                                    if
                                                                    F32_convert_i32_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (179))
                                                                    else
                                                                    if
                                                                    F32_convert_i64_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (180))
                                                                    else
                                                                    if
                                                                    F32_convert_i64_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (181))
                                                                    else
                                                                    if
                                                                    F32_demote_f64
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (182))
                                                                    else
                                                                    if
                                                                    F64_convert_i32_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (183))
                                                                    else
                                                                    if
                                                                    F64_convert_i32_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (184))
                                                                    else
                                                                    if
                                                                    F64_convert_i64_s
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (185))
                                                                    else
                                                                    if
                                                                    F64_convert_i64_u
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (186))
                                                                    else
                                                                    if
                                                                    F64_promote_f32
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (187))
                                                                    else
                                                                    if
                                                                    I32_reinterpret_f32
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (188))
                                                                    else
                                                                    if
                                                                    I64_reinterpret_f64
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (189))
                                                                    else
                                                                    if
                                                                    F32_reinterpret_i32
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (190))
                                                                    else
                                                                    if
                                                                    F64_reinterpret_i64
                                                                    = input
                                                                    then
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (191))
                                                                    else
                                                                    FStar_UInt8.uint_to_t
                                                                    (Prims.of_int (255)))
let (aux_insn_label_serializer32 :
  aux_insn_label -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_insn_label_key x
let (aux_insn_label_size32 : aux_insn_label -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one