(** A module that places commonly used instructions into an
    easy-to-import module *)
module Semantics.Common.CFG.Instructions

/// If importing this module, all you need to define within the
/// intermediate language is:
///
/// + val valid_reg_int : int -> bool
/// + val valid_reg_float : int -> bool
///
/// Following this, you can just explicitly collapse the implicit
/// arguments to make things easier to use:
///
/// let operandi = operandi #valid_reg_int
/// let operandf = operandf #valid_reg_int #valid_reg_float
/// let cfg = cfg #(ins_t #valid_reg_int #valid_reg_float) #valid_reg_int #valid_reg_float
/// let string_of_cfg (c:cfg) = string_of_cfg #_ #_ #_ #string_of_inst c

open Semantics.Common.CFG
open Semantics.Common.CFG.Printer

type ins_t (#vali:int -> bool) (#valf:int -> bool): eqtype =
  | Unreachable: ins_t #vali #valf

  | Alloc   : n:nat -> ins_t #vali #valf
  | Dealloc : n:nat -> ins_t #vali #valf
  | Push    : src:operandi #vali -> ins_t #vali #valf
  | Pop     : dst:operandi #vali -> ins_t #vali #valf

  | CMov64 : cond:ocmp #vali #valf -> dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf

  | Mov8       : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Mov16      : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Mov32      : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Mov64      : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovZX8to32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovZX8to64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovSX8to32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovSX8to64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovZX16to32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovZX16to64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovSX16to32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovSX16to64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovZX32to64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | MovSX32to64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf

  | FMov32: dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMov64: dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf

  | Clz32   : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Ctz32   : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Popcnt32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf

  | Clz64   : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Ctz64   : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Popcnt64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf

  | FNeg32    : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FAbs32    : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FCeil32   : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FFloor32  : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FTrunc32  : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FNearest32: dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FSqrt32   : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf

  | FNeg64    : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FAbs64    : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FCeil64   : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FFloor64  : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FTrunc64  : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FNearest64: dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FSqrt64   : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf

  | Add32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Sub32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Mul32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | DivS32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | DivU32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | RemS32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | RemU32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | And32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Or32  : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Xor32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Shl32 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | ShrS32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | ShrU32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Rotl32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Rotr32: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf

  | Add64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Sub64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Mul64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | DivS64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | DivU64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | RemS64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | RemU64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | And64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Or64  : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Xor64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Shl64 : dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | ShrS64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | ShrU64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Rotl64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf
  | Rotr64: dst:operandi #vali -> src:operandi #vali -> ins_t #vali #valf

  | FAdd32     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FSub32     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMul32     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FDiv32     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMin32     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMax32     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FCopySign32: dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf

  | FAdd64     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FSub64     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMul64     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FDiv64     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMin64     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FMax64     : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | FCopySign64: dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf

  | I32TruncSF32: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | I32TruncUF32: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | I32TruncSF64: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | I32TruncUF64: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf

  | I64TruncSF32: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | I64TruncUF32: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | I64TruncSF64: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | I64TruncUF64: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf

  | F32DemoteF64  : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | F32ConvertSI32: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | F32ConvertUI32: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | F32ConvertSI64: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | F32ConvertUI64: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf

  | F64PromoteF32 : dst:operandf #vali #valf -> src:operandf #vali #valf -> ins_t #vali #valf
  | F64ConvertSI32: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | F64ConvertUI32: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | F64ConvertSI64: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | F64ConvertUI64: dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf

  | ReinterpretFloat32: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | ReinterpretFloat64: dst:operandi #vali -> src:operandf #vali #valf -> ins_t #vali #valf
  | ReinterpretInt32  : dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf
  | ReinterpretInt64  : dst:operandf #vali #valf -> src:operandi #vali -> ins_t #vali #valf

  (* TODO: Add more instructions! *)

val string_of_inst : (#vali:(int -> bool)) -> (#valf:(int -> bool)) -> ins_t #vali #valf -> string
let string_of_inst #_ #_ i =
  match i with
  | Unreachable -> "Unreachable"

  | Alloc n   -> "Alloc " ^ string_of_int n
  | Dealloc n -> "Dealloc " ^ string_of_int n
  | Push src  -> "Push " ^ string_of_operandi src
  | Pop dst   -> "Pop " ^ string_of_operandi dst

  | CMov64 cond dst src -> "CMov64 " ^ string_of_ocmp cond ^ " " ^ string_of_operandi dst ^ " " ^ string_of_operandi src

  | Mov8        dst src -> "Mov8 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Mov16       dst src -> "Mov16 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Mov32       dst src -> "Mov32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Mov64       dst src -> "Mov64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovZX8to32  dst src -> "MovZX8to32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovZX8to64  dst src -> "MovZX8to64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovSX8to32  dst src -> "MovSX8to32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovSX8to64  dst src -> "MovSX8to64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovZX16to32 dst src -> "MovZX16to32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovZX16to64 dst src -> "MovZX16to64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovSX16to32 dst src -> "MovSX16to32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovSX16to64 dst src -> "MovSX16to64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovZX32to64 dst src -> "MovZX32to64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | MovSX32to64 dst src -> "MovSX32to64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src

  | FMov32 dst src -> "FMov32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMov64 dst src -> "FMov64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src

  | Clz32    dst src -> "Clz32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Ctz32    dst src -> "Ctz32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Popcnt32 dst src -> "Popcnt32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src

  | Clz64    dst src -> "Clz64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Ctz64    dst src -> "Ctz64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Popcnt64 dst src -> "Popcnt64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src

  | FNeg32     dst src -> "FNeg32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FAbs32     dst src -> "FAbs32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FCeil32    dst src -> "FCeil32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FFloor32   dst src -> "FFloor32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FTrunc32   dst src -> "FTrunc32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FNearest32 dst src -> "FNearest32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FSqrt32    dst src -> "FSqrt32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src

  | FNeg64     dst src -> "FNeg64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FAbs64     dst src -> "FAbs64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FCeil64    dst src -> "FCeil64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FFloor64   dst src -> "FFloor64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FTrunc64   dst src -> "FTrunc64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FNearest64 dst src -> "FNearest64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FSqrt64    dst src -> "FSqrt64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src

  | Add32  dst src -> "Add32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Sub32  dst src -> "Sub32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Mul32  dst src -> "Mul32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | DivS32 dst src -> "DivS32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | DivU32 dst src -> "DivU32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | RemS32 dst src -> "RemS32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | RemU32 dst src -> "RemU32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | And32  dst src -> "And32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Or32   dst src -> "Or32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Xor32  dst src -> "Xor32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Shl32  dst src -> "Shl32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | ShrS32 dst src -> "ShrS32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | ShrU32 dst src -> "ShrU32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Rotl32 dst src -> "Rotl32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Rotr32 dst src -> "Rotr32 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src

  | Add64  dst src -> "Add64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Sub64  dst src -> "Sub64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Mul64  dst src -> "Mul64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | DivS64 dst src -> "DivS64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | DivU64 dst src -> "DivU64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | RemS64 dst src -> "RemS64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | RemU64 dst src -> "RemU64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | And64  dst src -> "And64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Or64   dst src -> "Or64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Xor64  dst src -> "Xor64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Shl64  dst src -> "Shl64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | ShrS64 dst src -> "ShrS64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | ShrU64 dst src -> "ShrU64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Rotl64 dst src -> "Rotl64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src
  | Rotr64 dst src -> "Rotr64 " ^ string_of_operandi dst ^ " " ^ string_of_operandi src

  | FAdd32      dst src -> "FAdd32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FSub32      dst src -> "FSub32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMul32      dst src -> "FMul32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FDiv32      dst src -> "FDiv32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMin32      dst src -> "FMin32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMax32      dst src -> "FMax32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FCopySign32 dst src -> "FCopySign32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src

  | FAdd64      dst src -> "FAdd64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FSub64      dst src -> "FSub64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMul64      dst src -> "FMul64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FDiv64      dst src -> "FDiv64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMin64      dst src -> "FMin64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FMax64      dst src -> "FMax64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | FCopySign64 dst src -> "FCopySign64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src

  | I32TruncSF32 dst src -> "I32TruncSF32 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | I32TruncUF32 dst src -> "I32TruncUF32 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | I32TruncSF64 dst src -> "I32TruncSF64 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | I32TruncUF64 dst src -> "I32TruncUF64 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src

  | I64TruncSF32 dst src -> "I64TruncSF32 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | I64TruncUF32 dst src -> "I64TruncUF32 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | I64TruncSF64 dst src -> "I64TruncSF64 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | I64TruncUF64 dst src -> "I64TruncUF64 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src

  | F32DemoteF64   dst src -> "F32DemoteF64 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | F32ConvertSI32 dst src -> "F32ConvertSI32 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | F32ConvertUI32 dst src -> "F32ConvertUI32 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | F32ConvertSI64 dst src -> "F32ConvertSI64 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | F32ConvertUI64 dst src -> "F32ConvertUI64 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src

  | F64PromoteF32  dst src -> "F64PromoteF32 " ^ string_of_operandf dst ^ " " ^ string_of_operandf src
  | F64ConvertSI32 dst src -> "F64ConvertSI32 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | F64ConvertUI32 dst src -> "F64ConvertUI32 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | F64ConvertSI64 dst src -> "F64ConvertSI64 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | F64ConvertUI64 dst src -> "F64ConvertUI64 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src

  | ReinterpretFloat32 dst src -> "ReinterpretFloat32 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | ReinterpretFloat64 dst src -> "ReinterpretFloat64 " ^ string_of_operandi dst ^ " " ^ string_of_operandf src
  | ReinterpretInt32   dst src -> "ReinterpretInt32 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
  | ReinterpretInt64   dst src -> "ReinterpretInt64 " ^ string_of_operandf dst ^ " " ^ string_of_operandi src
