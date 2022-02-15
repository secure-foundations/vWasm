module Semantics.Common.CFG.LLInstructionSemantics

#reset-options "--fuel 0 --ifuel 0"

module L = FStar.List.Tot

open Types_s
open Common.Conversions
open Semantics.Common.CFG
open Semantics.Common.CFG.Instructions
open Semantics.Common.CFG.LowLevelSemantics
open Semantics.Common.CFG.Utils

/// Defines low level instruction semantics
///
/// Specifically, the `eval_ins` that we need :)

val eval_ins : (#vali:_) -> (#valf:_) ->
  (i:ins_t #vali #valf) ->
  s:state -> (s_new:state{maintained_property s s_new})

type ins_tag_t =
  | Misc
  | StackOp
  | Mov
  | Movzx
  | Movsx
  | FMov
  | I32_Unop
  | I64_Unop
  | F32_Unop
  | F64_Unop
  | I32_Binop
  | I64_Binop
  | F32_Binop
  | F64_Binop
  | Conversion

let tag_of_ins #vali #valf (i:ins_t #vali #valf) : Tot ins_tag_t =
  allow_inversion (ins_t #vali #valf);
  match i with
  | Unreachable | CMov64 _ _ _ -> Misc
  | Alloc _ | Dealloc _ | Push _ | Pop _ -> StackOp
  | Mov8 _ _ | Mov16 _ _ | Mov32 _ _ | Mov64 _ _ -> Mov
  | MovZX8to32 _ _ | MovZX8to64 _ _ | MovZX16to32 _ _ | MovZX16to64 _ _ | MovZX32to64 _ _ -> Movzx
  | MovSX8to32 _ _ | MovSX8to64 _ _ | MovSX16to32 _ _ | MovSX16to64 _ _ | MovSX32to64 _ _ -> Movsx
  | FMov32 _ _ | FMov64 _ _ -> FMov
  | Clz32 _ _ | Ctz32 _ _ | Popcnt32 _ _ -> I32_Unop
  | Clz64 _ _ | Ctz64 _ _ | Popcnt64 _ _ -> I64_Unop
  | FNeg32 _ _ | FAbs32 _ _ | FCeil32 _ _ | FFloor32 _ _ | FTrunc32 _ _ | FNearest32 _ _ | FSqrt32 _ _ -> F32_Unop
  | FNeg64 _ _ | FAbs64 _ _ | FCeil64 _ _ | FFloor64 _ _ | FTrunc64 _ _ | FNearest64 _ _ | FSqrt64 _ _ -> F64_Unop
  | Add32 _ _ | Sub32 _ _ | Mul32 _ _ | DivS32 _ _ | DivU32 _ _ | RemS32 _ _ | RemU32 _ _ | And32 _ _ | Or32 _ _ | Xor32 _ _ | Shl32 _ _ | ShrS32 _ _ | ShrU32 _ _ | Rotl32 _ _ | Rotr32 _ _ -> I32_Binop
  | Add64 _ _ | Sub64 _ _ | Mul64 _ _ | DivS64 _ _ | DivU64 _ _ | RemS64 _ _ | RemU64 _ _ | And64 _ _ | Or64 _ _ | Xor64 _ _ | Shl64 _ _ | ShrS64 _ _ | ShrU64 _ _ | Rotl64 _ _ | Rotr64 _ _ -> I64_Binop
  | FAdd32 _ _ | FSub32 _ _ | FMul32 _ _ | FDiv32 _ _ | FMin32 _ _ | FMax32 _ _ | FCopySign32 _ _ -> F32_Binop
  | FAdd64 _ _ | FSub64 _ _ | FMul64 _ _ | FDiv64 _ _ | FMin64 _ _ | FMax64 _ _ | FCopySign64 _ _ -> F64_Binop
  | I32TruncSF32 _ _ | I32TruncUF32 _ _ | I32TruncSF64 _ _ | I32TruncUF64 _ _ -> Conversion
  | I64TruncSF32 _ _ | I64TruncUF32 _ _ | I64TruncSF64 _ _ | I64TruncUF64 _ _ -> Conversion
  | F32DemoteF64 _ _ | F32ConvertSI32 _ _ | F32ConvertUI32 _ _ | F32ConvertSI64 _ _ | F32ConvertUI64 _ _ -> Conversion
  | F64PromoteF32 _ _ | F64ConvertSI32 _ _ | F64ConvertUI32 _ _ | F64ConvertSI64 _ _ | F64ConvertUI64 _ _ -> Conversion
  | ReinterpretFloat32 _ _ | ReinterpretFloat64 _ _ | ReinterpretInt32 _ _ | ReinterpretInt64 _ _ -> Conversion

let ins #vali #valf tag = (i:ins_t #vali #valf{tag_of_ins i == tag})

type _eval_ins_t tag = (#vali:_) -> (#valf:_) -> (i:ins #vali #valf tag) -> Tot (st_maintained unit)

/// This is a way to speed things up by showing that non-ip-changing
/// operations compose. Unfortunately, due to the way F*'s syntax
/// sugar works, we are forced to overload [bind]. Notice however that
/// it is equal to the pre-existing [bind], just acting in a
/// restricted context. We restrict it to this module by only applying
/// it within the functions in here.
#push-options "--ifuel 1"
let bind_maintained
    (#a:Type) (#b:Type)
    (m:st_maintained a)
    (f:a -> st_maintained b) :
  st_maintained b =
  assert (forall s. maintained_property s s); (* OBSERVE: Needed due to patterns *)
  bind #a #b m f
private unfold
let original_bind #a #b m f = bind #a #b m f
#pop-options

let _eval_ins_Misc : _eval_ins_t Misc =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i  ->
    let bind #a #b m f = original_bind #a #b m f in
    match i with
    | Unreachable ->
      s1 <-- get;
      set ({s1 with explicitly_safely_killed = true})
    | CMov64 cond dst src ->
      s1 <-- get;
      if eval_ocmp cond s1 then (
        v <-- read_operand64 src s1;
        update_operandi64 dst v
      ) else (
        set s1
      )

let _eval_ins_StackOp : _eval_ins_t StackOp =
  let bind #i #f = bind_maintained #i #f in
  fun #vali #_ i ->
    let bind #a #b m f = original_bind #a #b m f in
    s <-- get;
    match i with
    | Alloc n ->
      set ({s with stack_pointer = s.stack_pointer - n})
    | Dealloc n ->
      let old_rsp = s.stack_pointer in
      let stack_pointer = old_rsp + n in
      let stack = (* The deallocated stack memory should now be considered invalid *)
        free_stack old_rsp stack_pointer s.stack in
      set ({s with stack; stack_pointer})
    | Push src ->
      v <-- read_operand64 src s;
      let stack_pointer = s.stack_pointer - 8 in
      set ({update_stack64 stack_pointer v s with stack_pointer})
    | Pop dst ->
      let src : operandi #vali = OStackRel 0 in
      v <-- read_operand64 src s;
      let old_rsp = s.stack_pointer in
      let stack_pointer = old_rsp + 8 in
      let stack = free_stack old_rsp stack_pointer s.stack in
      update_operandi64 dst v;;
      set ({s with stack; stack_pointer})

let _eval_ins_Mov : _eval_ins_t Mov =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    s <-- get;
    match i with
    | Mov8 dst src ->
      v <-- read_operand8 src s;
      update_operandi8 dst v
    | Mov16 dst src ->
      v <-- read_operand16 src s;
      update_operandi16 dst v
    | Mov32 dst src ->
      v <-- read_operand32 src s;
      update_operandi32 dst v
    | Mov64 dst src ->
      v <-- read_operand64 src s;
      update_operandi64 dst v

let _eval_ins_Movzx : _eval_ins_t Movzx =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    s <-- get;
    match i with
    | MovZX8to32 dst src ->
      v <-- read_operand8 src s;
      update_operandi32 dst v
    | MovZX8to64 dst src ->
      v <-- read_operand8 src s;
      update_operandi64 dst v
    | MovZX16to32 dst src ->
      v <-- read_operand16 src s;
      update_operandi32 dst v
    | MovZX16to64 dst src ->
      v <-- read_operand16 src s;
      update_operandi64 dst v
    | MovZX32to64 dst src ->
      v <-- read_operand32 src s;
      update_operandi64 dst v

let _eval_ins_Movsx : _eval_ins_t Movsx =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    s <-- get;
    match i with
    | MovSX8to32 dst src ->
      v <-- read_operand8 src s;
      update_operandi32 dst (sign_extend v)
    | MovSX8to64 dst src ->
      v <-- read_operand8 src s;
      update_operandi64 dst (sign_extend v)
    | MovSX16to32 dst src ->
      v <-- read_operand16 src s;
      update_operandi32 dst (sign_extend v)
    | MovSX16to64 dst src ->
      v <-- read_operand16 src s;
      update_operandi64 dst (sign_extend v)
    | MovSX32to64 dst src ->
      v <-- read_operand32 src s;
      update_operandi64 dst (sign_extend v)

let _eval_ins_FMov : _eval_ins_t FMov =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    s <-- get;
    match i with
    | FMov32 dst src ->
      v <-- read_operandf32 src s;
      update_operandf32 dst v
    | FMov64 dst src ->
      v <-- read_operandf64 src s;
      update_operandf64 dst v

let args_I32_Unop #vali #valf (i:ins #vali #valf I32_Unop) : operandi & operandi =
  match i with
  | Clz32 dst src | Ctz32 dst src | Popcnt32 dst src ->
    dst, src

[@"opaque_to_smt"]
let op_I32_Unop #vali #valf (i:ins #vali #valf I32_Unop) (v:nat32) : nat32 =
  admit () (* Underspecified numeric operation *)

let _eval_ins_I32_Unop : _eval_ins_t I32_Unop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let dst, src = args_I32_Unop i in
    s <-- get;
    src_v <-- read_operand32 src s;
    (* NOTE: We explicitly underspecify flags in our state, so this is ok *)
    let v = op_I32_Unop i src_v in
    update_operandi32 dst v

let args_I64_Unop #vali #valf (i:ins #vali #valf I64_Unop) : operandi & operandi =
  match i with
  | Clz64 dst src | Ctz64 dst src | Popcnt64 dst src ->
    dst, src

[@"opaque_to_smt"]
let op_I64_Unop #vali #valf (i:ins #vali #valf I64_Unop) (v:nat64) : nat64 =
  admit () (* Underspecified numeric operation *)

let _eval_ins_I64_Unop : _eval_ins_t I64_Unop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let dst, src = args_I64_Unop i in
    s <-- get;
    src_v <-- read_operand64 src s;
    (* NOTE: We explicitly underspecify flags in our state, so this is ok *)
    let v = op_I64_Unop i src_v in
    update_operandi64 dst v

let args_F32_Unop #vali #valf (i:ins #vali #valf F32_Unop) : operandf & operandf =
  match i with
  | FNeg32 dst src
  | FAbs32 dst src
  | FCeil32 dst src
  | FFloor32 dst src
  | FTrunc32 dst src
  | FNearest32 dst src
  | FSqrt32 dst src
    -> dst, src

[@"opaque_to_smt"]
let op_F32_Unop #vali #valf (i:ins #vali #valf F32_Unop) (v:float) : float =
  admit () (* Underspecified numeric operation *)

let _eval_ins_F32_Unop : _eval_ins_t F32_Unop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let operands = args_F32_Unop i in
    let dst = fst operands in
    let src = snd operands in
    s <-- get;
    src_v <-- read_operandf32 src s;
    let v = op_F32_Unop i src_v in
    update_operandf32 dst v

let args_F64_Unop #vali #valf (i:ins #vali #valf F64_Unop) : operandf & operandf =
  match i with
  | FNeg64 dst src
  | FAbs64 dst src
  | FCeil64 dst src
  | FFloor64 dst src
  | FTrunc64 dst src
  | FNearest64 dst src
  | FSqrt64 dst src
    -> dst, src

[@"opaque_to_smt"]
let op_F64_Unop #vali #valf (i:ins #vali #valf F64_Unop) (v:float) : float =
  admit () (* Underspecified numeric operation *)

let _eval_ins_F64_Unop : _eval_ins_t F64_Unop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let operands = args_F64_Unop i in
    let dst = fst operands in
    let src = snd operands in
    s <-- get;
    src_v <-- read_operandf64 src s;
    let v = op_F64_Unop i src_v in
    update_operandf64 dst v

let args_I32_Binop #vali #valf (i:ins #vali #valf I32_Binop) : operandi & operandi =
  match i with
  | Add32 dst src
  | Sub32 dst src
  | Mul32 dst src
  | DivS32 dst src
  | DivU32 dst src
  | RemS32 dst src
  | RemU32 dst src
  | And32 dst src
  | Or32 dst src
  | Xor32 dst src
  | Shl32 dst src
  | ShrS32 dst src
  | ShrU32 dst src
  | Rotl32 dst src
  | Rotr32 dst src -> dst, src

[@"opaque_to_smt"]
let op_I32_Binop #vali #valf (i:ins #vali #valf I32_Binop) (v1 v2:nat32) : nat32 =
  match i with
  | Add32 _ _ -> (v1 + v2) % pow2_32
  | Sub32 _ _ -> (v1 - v2) % pow2_32
  | Mul32 _ _ -> (v1 `op_Multiply` v2) % pow2_32
  | DivS32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | DivU32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | RemS32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | RemU32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | And32 _ _ -> iand v1 v2
  | Or32 _ _ -> ior v1 v2
  | Xor32 _ _ -> ixor v1 v2
  | Shl32 _ _ -> ishl v1 v2
  | ShrS32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | ShrU32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | Rotl32 _ _ -> admit () (* Underspecified pure numeric operation *)
  | Rotr32 _ _ -> admit () (* Underspecified pure numeric operation *)

let _eval_ins_I32_Binop : _eval_ins_t I32_Binop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let dst, src = args_I32_Binop i in
    s <-- get;
    v1 <-- read_operand32 dst s;
    v2 <-- read_operand32 src s;
    (* NOTE: We explicitly underspecify flags in our state, so this is ok *)
    let v = op_I32_Binop i v1 v2 in
    update_operandi32 dst v

let args_I64_Binop #vali #valf (i:ins #vali #valf I64_Binop) : operandi & operandi =
  match i with
  | Add64 dst src
  | Sub64 dst src
  | Mul64 dst src
  | DivS64 dst src
  | DivU64 dst src
  | RemS64 dst src
  | RemU64 dst src
  | And64 dst src
  | Or64 dst src
  | Xor64 dst src
  | Shl64 dst src
  | ShrS64 dst src
  | ShrU64 dst src
  | Rotl64 dst src
  | Rotr64 dst src -> dst, src

[@"opaque_to_smt"]
let op_I64_Binop #vali #valf (i:ins #vali #valf I64_Binop) (v1 v2:nat64) : nat64 =
  match i with
  | Add64 _ _ -> (v1 + v2) % pow2_64
  | Sub64 _ _ -> (v1 - v2) % pow2_64
  | Mul64 _ _ -> (v1 `op_Multiply` v2) % pow2_64
  | DivS64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | DivU64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | RemS64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | RemU64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | And64 _ _ -> iand v1 v2
  | Or64 _ _ -> ior v1 v2
  | Xor64 _ _ -> ixor v1 v2
  | Shl64 _ _ -> ishl v1 v2
  | ShrS64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | ShrU64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | Rotl64 _ _ -> admit () (* Underspecified pure numeric operation *)
  | Rotr64 _ _ -> admit () (* Underspecified pure numeric operation *)

let _eval_ins_I64_Binop : _eval_ins_t I64_Binop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let dst, src = args_I64_Binop i in
    s <-- get;
    v1 <-- read_operand64 dst s;
    v2 <-- read_operand64 src s;
    (* NOTE: We explicitly underspecify flags in our state, so this is ok *)
    let v = op_I64_Binop i v1 v2 in
    update_operandi64 dst v

let args_F32_Binop #vali #valf (i:ins #vali #valf F32_Binop) : operandf & operandf =
  match i with
  | FAdd32 dst src
  | FSub32 dst src
  | FMul32 dst src
  | FDiv32 dst src
  | FMin32 dst src
  | FMax32 dst src
  | FCopySign32 dst src
    -> dst, src

[@"opaque_to_smt"]
let op_F32_Binop #vali #valf (i:ins #vali #valf F32_Binop) (v1 v2:float) : float =
  admit () (* Underspecified numeric operation *)

let _eval_ins_F32_Binop : _eval_ins_t F32_Binop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let operands = args_F32_Binop i in
    let dst = fst operands in
    let src = snd operands in
    s <-- get;
    v1 <-- read_operandf32 dst s;
    v2 <-- read_operandf32 src s;
    let v = op_F32_Binop i v1 v2 in
    update_operandf32 dst v

let args_F64_Binop #vali #valf (i:ins #vali #valf F64_Binop) : operandf & operandf =
  match i with
  | FAdd64 dst src
  | FSub64 dst src
  | FMul64 dst src
  | FDiv64 dst src
  | FMin64 dst src
  | FMax64 dst src
  | FCopySign64 dst src
    -> dst, src

[@"opaque_to_smt"]
let op_F64_Binop #vali #valf (i:ins #vali #valf F64_Binop) (v1 v2:float) : float =
  admit () (* Underspecified numeric operation *)

let _eval_ins_F64_Binop : _eval_ins_t F64_Binop =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    let operands = args_F64_Binop i in
    let dst = fst operands in
    let src = snd operands in
    s <-- get;
    v1 <-- read_operandf64 dst s;
    v2 <-- read_operandf64 src s;
    let v = op_F64_Binop i v1 v2 in
    update_operandf64 dst v

[@"opaque_to_smt"]
let op_Conversion_float_to_i32 #vali #valf (i:ins #vali #valf Conversion{
    match i with
    | I32TruncSF32 _ _ | I32TruncUF32 _ _ | I32TruncSF64 _ _ | I32TruncUF64 _ _ -> True
    | ReinterpretFloat32 _ _ -> True
    | _ -> False
  }) (v:float) : nat32 =
  admit () (* Underspecified numeric operation *)

[@"opaque_to_smt"]
let op_Conversion_float_to_i64 #vali #valf (i:ins #vali #valf Conversion{
    match i with
    | I64TruncSF32 _ _ | I64TruncUF32 _ _ | I64TruncSF64 _ _ | I64TruncUF64 _ _ -> True
    | ReinterpretFloat64 _ _ -> True
    | _ -> False
  }) (v:float) : nat64 =
  admit () (* Underspecified numeric operation *)

[@"opaque_to_smt"]
let op_Conversion_float_to_float #vali #valf (i:ins #vali #valf Conversion{
    match i with
    | F32DemoteF64 _ _ | F64PromoteF32 _ _ -> True
    | _ -> False
  }) (v:float) : float =
  admit () (* Underspecified numeric operation *)

[@"opaque_to_smt"]
let op_Conversion_i32_to_float #vali #valf (i:ins #vali #valf Conversion{
    match i with
    | F32ConvertSI32 _ _ | F32ConvertUI32 _ _ | F64ConvertSI32 _ _ | F64ConvertUI32 _ _ -> True
    | ReinterpretInt32 _ _ -> True
    | _ -> False
  }) (v:nat32) : float =
  admit () (* Underspecified numeric operation *)

[@"opaque_to_smt"]
let op_Conversion_i64_to_float #vali #valf (i:ins #vali #valf Conversion{
    match i with
    | F32ConvertSI64 _ _ | F32ConvertUI64 _ _ | F64ConvertSI64 _ _ | F64ConvertUI64 _ _ -> True
    | ReinterpretInt64 _ _ -> True
    | _ -> False
  }) (v:nat64) : float =
  admit () (* Underspecified numeric operation *)

let _eval_ins_Conversion : _eval_ins_t Conversion =
  let bind #i #f = bind_maintained #i #f in
  fun #_ #_ i ->
    s <-- get;
    match i with
    | I32TruncSF32 dst src | I32TruncUF32 dst src | ReinterpretFloat32 dst src ->
      v <-- read_operandf32 src s;
      update_operandi32 dst (op_Conversion_float_to_i32 i v)
    | I32TruncSF64 dst src | I32TruncUF64 dst src ->
      v <-- read_operandf64 src s;
      update_operandi32 dst (op_Conversion_float_to_i32 i v)
    | I64TruncSF32 dst src | I64TruncUF32 dst src ->
      v <-- read_operandf32 src s;
      update_operandi64 dst (op_Conversion_float_to_i64 i v)
    | I64TruncSF64 dst src | I64TruncUF64 dst src | ReinterpretFloat64 dst src ->
      v <-- read_operandf64 src s;
      update_operandi64 dst (op_Conversion_float_to_i64 i v)
    | F32DemoteF64 dst src ->
      v <-- read_operandf64 src s;
      update_operandf32 dst (op_Conversion_float_to_float i v)
    | F64PromoteF32 dst src ->
      v <-- read_operandf32 src s;
      update_operandf64 dst (op_Conversion_float_to_float i v)
    | F32ConvertSI32 dst src | F32ConvertUI32 dst src | ReinterpretInt32 dst src ->
      v <-- read_operand32 src s;
      update_operandf32 dst (op_Conversion_i32_to_float i v)
    | F64ConvertSI32 dst src | F64ConvertUI32 dst src ->
      v <-- read_operand32 src s;
      update_operandf64 dst (op_Conversion_i32_to_float i v)
    | F32ConvertSI64 dst src | F32ConvertUI64 dst src ->
      v <-- read_operand64 src s;
      update_operandf32 dst (op_Conversion_i64_to_float i v)
    | F64ConvertSI64 dst src | F64ConvertUI64 dst src | ReinterpretInt64 dst src ->
      v <-- read_operand64 src s;
      update_operandf64 dst (op_Conversion_i64_to_float i v)

let eval_ins #vali #valf i s =
  run (
    match tag_of_ins i with
    | Misc -> _eval_ins_Misc i
    | StackOp -> _eval_ins_StackOp i
    | Mov -> _eval_ins_Mov i
    | Movzx -> _eval_ins_Movzx i
    | Movsx -> _eval_ins_Movsx i
    | FMov -> _eval_ins_FMov i
    | I32_Unop -> _eval_ins_I32_Unop i
    | I64_Unop -> _eval_ins_I64_Unop i
    | F32_Unop -> _eval_ins_F32_Unop i
    | F64_Unop -> _eval_ins_F64_Unop i
    | I32_Binop -> _eval_ins_I32_Binop i
    | I64_Binop -> _eval_ins_I64_Binop i
    | F32_Binop -> _eval_ins_F32_Binop i
    | F64_Binop -> _eval_ins_F64_Binop i
    | Conversion -> _eval_ins_Conversion i
  ) s
