module Compiler.Phase.Allocator

open Common.Err
open Semantics.Common.CFG
open Semantics.Common.CFG.Instructions
open Semantics.Common.CFG.Printer
open Common.Print

//open Compiler.Phase.Analysis

open Words_s

module Sem1 = I1.Semantics
module Sem2 = I2.Semantics
module L = FStar.List.Tot
module M = FStar.Map
module S = Common.OrdSet
module AOL = Common.AppendOptimizedList

private let op_String_Access = Map.sel
private let op_String_Assignment = Map.upd

/// Convenience structures and functions
type usage = option nat

let max a b = if a < b then b else a

val umax: usage -> usage -> usage
let umax u1 u2 =
  match u1, u2 with
  | Some umax1, Some umax2 -> Some (max umax1 umax2)
  | Some umax1, None -> Some umax1
  | None, Some umax2 -> Some umax2
  | None, None -> None

/// Reg usage calculation
val calculate_reg_usage_maddr: Sem1.maddr -> Tot usage
let calculate_reg_usage_maddr m =
  match m with
  | MIndex scale index offset -> Some index

val calculate_reg_usage_opndi: Sem1.operandi -> Err_ usage
let calculate_reg_usage_opndi opnd =
  match opnd with
  | OConst n -> None
  | OReg r sz -> Some r
  | OMemRel m -> calculate_reg_usage_maddr m
  | OStackRel offset -> fail_with "calculate_reg_usage_opndi: unexpected OStackRel" // Should not appear
  | ONamedGlobal ident -> None

val calculate_reg_usage_opndf: Sem1.operandf -> Err_ usage
let calculate_reg_usage_opndf opnd =
  match opnd with
  | OConst_f f -> None
  | OReg_f r sz -> Some r
  | OMemRel_f m -> calculate_reg_usage_maddr m
  | OStackRel_f offset -> fail_with "calculate_reg_usage_opndf: unexpected OStackRel_f" // Should not appear
  | ONamedGlobal_f ident -> None

val calculate_reg_usage_cond: Sem1.ocmp -> Err_ usage
let calculate_reg_usage_cond cond1 =
  match cond1 with
  (* 32 bit comparisons *)
  | OEq32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | ONe32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLe32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGe32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLt32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGt32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLeS32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGeS32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLtS32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGtS32 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  (* 64 bit comparisons *)
  | OEq64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | ONe64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLe64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGe64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLt64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGt64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLeS64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGeS64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OLtS64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  | OGtS64 o1 o2 -> umax (calculate_reg_usage_opndi o1) (calculate_reg_usage_opndi o2)
  (* 32 bit floats *)
  | OFEq32 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFNe32 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFLt32 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFGt32 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFLe32 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFGe32 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  (* 64 bit floats *)
  | OFEq64 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFNe64 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFLt64 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFGt64 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFLe64 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)
  | OFGe64 o1 o2 -> umax (calculate_reg_usage_opndf o1) (calculate_reg_usage_opndf o2)

val calculate_reg_usage_ins: Sem1.ins_t -> Err_ usage
let calculate_reg_usage_ins ins1 =
  match ins1 with
  | Unreachable -> None

  | Alloc   n -> None
  | Dealloc n -> None
  | Push    src -> calculate_reg_usage_opndi src
  | Pop     dst -> calculate_reg_usage_opndi dst

  | CMov64 _ _ _ -> fail_with "CMov64 found at allocator. Should not happen."

  | Mov8        dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Mov16       dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Mov32       dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Mov64       dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovZX8to32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovZX8to64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovSX8to32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovSX8to64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovZX16to32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovZX16to64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovSX16to32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovSX16to64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovZX32to64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | MovSX32to64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)

  | FMov32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMov64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)

  | Clz32    dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Ctz32    dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Popcnt32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)

  | Clz64    dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Ctz64    dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Popcnt64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)

  | FNeg32     dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FAbs32     dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FCeil32    dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FFloor32   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FTrunc32   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FNearest32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FSqrt32    dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)

  | FNeg64     dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FAbs64     dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FCeil64    dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FFloor64   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FTrunc64   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FNearest64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FSqrt64    dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)

  | Add32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Sub32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Mul32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | DivS32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | DivU32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | RemS32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | RemU32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | And32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Or32   dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Xor32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Shl32  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | ShrS32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | ShrU32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Rotl32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Rotr32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)

  | Add64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Sub64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Mul64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | DivS64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | DivU64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | RemS64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | RemU64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | And64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Or64   dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Xor64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Shl64  dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | ShrS64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | ShrU64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Rotl64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)
  | Rotr64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndi src)

  | FAdd32      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FSub32      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMul32      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FDiv32      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMin32      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMax32      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FCopySign32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)

  | FAdd64      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FSub64      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMul64      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FDiv64      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMin64      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FMax64      dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | FCopySign64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)

  | I32TruncSF32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | I32TruncUF32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | I32TruncSF64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | I32TruncUF64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)

  | I64TruncSF32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | I64TruncUF32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | I64TruncSF64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | I64TruncUF64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)

  | F32DemoteF64   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | F32ConvertSI32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | F32ConvertUI32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | F32ConvertSI64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | F32ConvertUI64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)

  | F64PromoteF32  dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndf src)
  | F64ConvertSI32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | F64ConvertUI32 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | F64ConvertSI64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | F64ConvertUI64 dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)

  | ReinterpretFloat32 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | ReinterpretFloat64 dst src -> umax (calculate_reg_usage_opndi dst) (calculate_reg_usage_opndf src)
  | ReinterpretInt32   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)
  | ReinterpretInt64   dst src -> umax (calculate_reg_usage_opndf dst) (calculate_reg_usage_opndi src)

val calculate_reg_usage_precode: Sem1.precode -> Err_ usage
let calculate_reg_usage_precode c =
  let f_ arg : usage =
    match arg with
    | ArgInt r _ -> Some r
    | ArgFloat r _ -> Some r
  in
  match c with
  | FnEntry name next -> None
  | FnExit name -> None
  | Ins i next -> calculate_reg_usage_ins i
  | InsList is next -> None // should not happen
  | Nop next -> None
  | Cmp cond nextTrue nextFalse -> calculate_reg_usage_cond cond
  | Switch case_table case -> Some case
  | Call (CallDirect n) onreturn -> None //should not happen
  | Call (CallIndirect r) onreturn -> Some r // should not happen
  | HighCall target args retval_store onreturn ->
    let cr =
      match target with
      | CallDirect n -> None
      | CallIndirect r -> Some r
    in
    let regs = L.map f_ args in
    let store =
      match retval_store with
      | None -> None
      | Some arg -> f_ arg
    in
    let acc = L.fold_left umax cr regs in
    umax acc store
  | Ret next -> None // should not happen
  | HighRet retval_load next ->
    (match retval_load with
     | None -> None
     | Some arg -> f_ arg
    )

val efold_left: ('a -> 'b -> Err_ 'a) -> 'a -> (l:list 'b) -> (Err_ 'a) (decreases l)
let rec efold_left f acc l =
  match l with
  | [] -> acc
  | b :: l ->
    let acc' = f acc b in
    efold_left f acc' l

val calculate_reg_usage_precodes: list Sem1.precode -> Err_ usage
let calculate_reg_usage_precodes cs =
  efold_left (fun acc c -> umax acc (calculate_reg_usage_precode c)) None cs

/// Compilation utility

noeq type context = {
  m1: Sem1.module_;
  fn_ax: aux_fn; // current aux_fn being compiled
  pc: loc;     // next empty pc in compiled
  old_pc: loc; // current pc being processsed in original
  c: AOL.t Sem2.precode; // generated code for current function
  c_all: AOL.t Sem2.precode;// aggregated code
  top_regs: nat;  // no. of regs used (not counting for calls)
  mapping: M.t loc (option (loc * loc)); // mapping old_pc |-> [new_pc_lower, new_pc_upper)
  pending: list (loc * list loc) // list (new_pc_pending_update * list old_next_pc)
}

val add_code: Sem2.precode -> (ctx:context) -> Err context True (fun ctx' -> ctx'.pc > ctx.pc)
let add_code code ctx = {ctx with pc = ctx.pc + 1; c = AOL.snoc (ctx.c, code)}

val inc_old: (ctx:context) -> Err context True (fun ctx' -> ctx'.old_pc > ctx.old_pc)
let inc_old ctx = {ctx with old_pc = ctx.old_pc + 1}

val set_map: loc -> loc -> loc -> context -> Err_ context
let set_map old_pc new_pc_lower new_pc_upper ctx =
  let mapping' = ctx.mapping.[old_pc] <- Some (new_pc_lower, new_pc_upper) in
  {ctx with mapping = mapping'}

val get_map: loc -> context -> Err_ (loc * loc)
let get_map old_pc ctx =
  match ctx.mapping.[old_pc] with
  | None -> fail_with ("get_map: " ^ string_of_int old_pc ^ " not found")
  | Some p -> p

val set_pending: loc -> list loc -> context -> Err_ context
let set_pending new_pc_pending old_next_pcs ctx =
  let pending' = (new_pc_pending, old_next_pcs) :: ctx.pending in
  {ctx with pending = pending'}

type opii = Sem2.operandi -> Sem2.operandi -> Sem2.ins_t
type opff = Sem2.operandf -> Sem2.operandf -> Sem2.ins_t
type opif = Sem2.operandi -> Sem2.operandf -> Sem2.ins_t
type opfi = Sem2.operandf -> Sem2.operandi -> Sem2.ins_t
type cmpii = Sem2.operandi -> Sem2.operandi -> Sem2.ocmp
type cmpff = Sem2.operandf -> Sem2.operandf -> Sem2.ocmp

/// Compilation helpers

val trans_regi: Sem1.regi -> context -> Tot Sem2.operandi
let trans_regi n ctx = OStackRel ((ctx.top_regs - 1 - n) `op_Multiply` 8)

val trans_regf: Sem1.regf -> context -> Tot Sem2.operandf
let trans_regf n ctx = OStackRel_f ((ctx.top_regs - 1 - n) `op_Multiply` 8)

// NB: Regs are always 32 or 64
val load_regi: Sem2.regi -> Sem1.regi -> rsize -> context -> Tot Sem2.precode
let load_regi dst2 src1 sz ctx =
  let odst2 = OReg dst2 sz in
  let osrc2 = trans_regi src1 ctx in
  let movop = if sz = 8 then Mov64 else Mov32 in
  Ins (movop odst2 osrc2) (ctx.pc + 1)

val load_regf: Sem2.regf -> Sem1.regf -> rsize -> context -> Tot Sem2.precode
let load_regf dst2 src1 sz ctx =
  let odst2 = OReg_f dst2 sz in
  let osrc2 = trans_regf src1 ctx in
  let movop = if sz = 8 then FMov64 else FMov32 in
  Ins (movop odst2 osrc2) (ctx.pc + 1)

val store_regi: Sem1.regi -> Sem2.regi -> rsize -> context -> Tot Sem2.precode
let store_regi dst1 src2 sz ctx =
  let odst2 = trans_regi dst1 ctx in
  let osrc2 = OReg src2 sz in
  let movop = if sz = 8 then Mov64 else Mov32 in
  Ins (movop odst2 osrc2) (ctx.pc + 1)

val store_regf: Sem1.regf -> Sem2.regf -> rsize -> context -> Tot Sem2.precode
let store_regf dst1 src2 sz ctx =
  let odst2 = trans_regf dst1 ctx in
  let osrc2 = OReg_f src2 sz in
  let movop = if sz = 8 then FMov64 else FMov32 in
  Ins (movop odst2 osrc2) (ctx.pc + 1)

// NB: Sign extend 32 -> 64 to avoid issues with sandboxing
val trans_mem: Sem1.maddr -> Sem2.regi -> context -> Tot (Sem2.maddr * Sem2.precode)
let trans_mem m1 rfree2 ctx =
  match m1 with
  | MIndex scale index offset ->
    let odst2 = OReg rfree2 8 in
    let osrc2 = trans_regi index ctx in
    let load_ins = Ins (MovZX32to64 odst2 osrc2) (ctx.pc + 1) in
    let m2 = MIndex scale rfree2 offset in
    m2, load_ins

// TODO: Maybe need exact size instead of just is64?
val loadi_mem: opii -> Sem2.regi -> Sem1.maddr -> rsize -> context -> Err_ context
let loadi_mem mov dst2 m1 sz ctx =
  let m2, load_ins = trans_mem m1 dst2 ctx in
  let ctx = add_code load_ins ctx in
  let osrc2 = OMemRel m2 in
  let odst2 = OReg dst2 sz in
  let ins = Ins (mov odst2 osrc2) (ctx.pc + 1) in
  add_code ins ctx

val loadf_mem: opff -> Sem2.regf -> Sem1.maddr -> Sem2.regi -> rsize -> context -> Err_ context
let loadf_mem fmov dst2 m1 rfree2 sz ctx =
  let m2, load_ins = trans_mem m1 rfree2 ctx in
  let ctx = add_code load_ins ctx in
  let osrc2 = OMemRel_f m2 in
  let odst2 = OReg_f dst2 sz in
  let ins = Ins (fmov odst2 osrc2) (ctx.pc + 1) in
  add_code ins ctx

val storei_mem: opii -> Sem1.maddr -> Sem2.regi -> Sem2.regi -> rsize -> context -> Err_ context
let storei_mem mov m1 src2 rfree2 sz ctx =
  let m2, load_ins = trans_mem m1 rfree2 ctx in
  let ctx = add_code load_ins ctx in
  let osrc2 = OReg src2 sz in
  let odst2 = OMemRel m2 in
  let ins = Ins (mov odst2 osrc2) (ctx.pc + 1) in
  add_code ins ctx

val storef_mem: opff -> Sem1.maddr -> Sem2.regf -> Sem2.regi -> rsize -> context -> Err_ context
let storef_mem fmov m1 src2 rfree2 sz ctx =
  let m2, load_ins = trans_mem m1 rfree2 ctx in
  let ctx = add_code load_ins ctx in
  let osrc2 = OReg_f src2 sz in
  let odst2 = OMemRel_f m2 in
  let ins = Ins (fmov odst2 osrc2) (ctx.pc + 1) in
  add_code ins ctx

val trans_operandi: Sem1.operandi -> Sem2.regi -> context -> Err_ (Sem2.operandi * option Sem2.precode)
let trans_operandi o1 rfree2 ctx =
  match o1 with
  | OConst n ->
    OConst n, None
  | OReg r _ ->
    trans_regi r ctx, None
  | OMemRel offset ->
    let m2, load_ins = trans_mem offset rfree2 ctx in
    OMemRel m2, Some load_ins
  | OStackRel offset ->
    fail_with "trans_operandi: unexpected OStackRel"
  | ONamedGlobal ident ->
    ONamedGlobal ident, None

val trans_operandf: Sem1.operandf -> Sem2.regi -> context -> Err_ (Sem2.operandf * option Sem2.precode)
let trans_operandf o1 rfree2 ctx =
  match o1 with
  | OConst_f n ->
    OConst_f n, None
  | OReg_f r _ ->
    trans_regf r ctx, None
  | OMemRel_f offset ->
    let m2, load_ins = trans_mem offset rfree2 ctx in
    OMemRel_f m2, Some load_ins
  | OStackRel_f offset ->
    fail_with "trans_operandi: unexpected OStackRel_f"
  | ONamedGlobal_f ident ->
    ONamedGlobal_f ident, None

val load_opi: opii -> Sem2.regi -> Sem1.operandi -> Sem2.regi -> rsize -> context -> Err_ (context * Sem2.operandi)
let load_opi mov dst2 osrc1 rfree2 sz ctx =
  let osrc2, oc = trans_operandi osrc1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let odst2 = OReg dst2 sz in
  let load_ins = Ins (mov odst2 osrc2) (ctx.pc + 1) in
  (add_code load_ins ctx, osrc2)

val load_opf: opff -> Sem2.regf -> Sem1.operandf -> Sem2.regi -> rsize -> context -> Err_ (context * Sem2.operandf)
let load_opf fmov dst2 osrc1 rfree2 sz ctx =
  let osrc2, oc = trans_operandf osrc1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let odst2 = OReg_f dst2 sz in
  let load_ins = Ins (fmov odst2 osrc2) (ctx.pc + 1) in
  (add_code load_ins ctx, osrc2)

val binopii: opii -> Sem1.operandi -> Sem2.regi -> Sem2.regi -> rsize -> context -> Err_ context
let binopii op odst1 src2 rfree2 sz ctx =
  let odst2, oc = trans_operandi odst1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let osrc2 = OReg src2 sz in
  let op_ins = Ins (op odst2 osrc2) (ctx.pc + 1) in
  add_code op_ins ctx

val binopff: opff -> Sem1.operandf -> Sem2.regf -> Sem2.regi -> rsize -> context -> Err_ context
let binopff op odst1 src2 rfree2 sz ctx =
  let odst2, oc = trans_operandf odst1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let osrc2 = OReg_f src2 sz in
  let op_ins = Ins (op odst2 osrc2) (ctx.pc + 1) in
  add_code op_ins ctx

// Float stuff is handled differently, as (non-mov) xmm instructions mostly are of the form
// addss xmm, xmm/m32
// Hence the operands are reversed here as we will need this as well

val binopff_opp: opff -> Sem2.regf -> Sem1.operandf -> Sem2.regi -> rsize -> context -> Err_ context
let binopff_opp op dst2 osrc1 rfree2 sz ctx =
  let osrc2, oc = trans_operandf osrc1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let odst2 = OReg_f dst2 sz in
  let op_ins = Ins (op odst2 osrc2) (ctx.pc + 1) in
  add_code op_ins ctx

val binopif_opp: opif -> Sem2.regi -> Sem1.operandf -> Sem2.regi -> rsize -> context -> Err_ context
let binopif_opp op dst2 osrc1 rfree2 sz ctx =
  let osrc2, oc = trans_operandf osrc1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let odst2 = OReg dst2 sz in
  let op_ins = Ins (op odst2 osrc2) (ctx.pc + 1) in
  add_code op_ins ctx

val binopfi_opp: opfi -> Sem2.regf -> Sem1.operandi -> Sem2.regi -> rsize -> context -> Err_ context
let binopfi_opp op dst2 osrc1 rfree2 sz ctx =
  let osrc2, oc = trans_operandi osrc1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let odst2 = OReg_f dst2 sz in
  let op_ins = Ins (op odst2 osrc2) (ctx.pc + 1) in
  add_code op_ins ctx

// We load the first argument to be consistent with xmm operations
val cmpopii: cmpii -> opii -> Sem1.operandi -> Sem1.operandi -> Sem2.regi -> Sem2.regi -> rsize -> context -> Err_ context
let cmpopii cmp mov oa1 ob1 rfreea2 rfreeb2 sz ctx =
  let ctx, _ = load_opi mov rfreea2 oa1 rfreea2 sz ctx in
  let ob2, oc = trans_operandi ob1 rfreeb2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let oa2 = OReg rfreea2 sz in
  let cmp_ins = Cmp (cmp oa2 ob2) (ctx.pc + 1) (ctx.pc + 1) in
  add_code cmp_ins ctx

// We load the first argument because xmm operations only allow the second arg to be mem
val cmpopff: cmpff -> opff -> Sem1.operandf -> Sem1.operandf -> Sem2.regf -> Sem2.regi -> rsize -> context -> Err_ context
let cmpopff cmp mov oa1 ob1 ffreea2 rfree2 sz ctx =
  let ctx, _ = load_opf mov ffreea2 oa1 rfree2 sz ctx in
  let ob2, oc = trans_operandf ob1 rfree2 ctx in
  let ctx =
    match oc with
    | None -> ctx
    | Some c -> add_code c ctx
  in
  let oa2 = OReg_f ffreea2 sz in
  let cmp_ins = Cmp (cmp oa2 ob2) (ctx.pc + 1) (ctx.pc + 1) in
  add_code cmp_ins ctx

/// Compilation

// TODO: Any small edge cases with sizes?
val compile_ins: Sem1.ins_t -> context -> Err_ context
let compile_ins ins1 ctx =
  let ri0: Sem2.regi = 0 in
  let ri1: Sem2.regi = 1 in
  let rf0: Sem2.regf = 0 in
  let rf1: Sem2.regf = 1 in

  let oii (opii0:opii) (opii1:opii) dst src sz ctx: Err_ context =
    let ctx, _ = load_opi opii0 ri0 src ri1 sz ctx in
    binopii opii1 dst ri0 ri1 sz ctx
  in
  // For FMov instructions, where we don't have to worry about dst being memory
  let off_mov (opff:opff) dst src sz ctx: Err_ context =
    let ctx, _ = load_opf opff rf0 src ri1 sz ctx in
    binopff opff dst rf0 ri1 sz ctx
  in
  // Most floating point instructions only accept xmm dst
  // We load dst first and store it back later
  // We use different free registers (ri0, ri1) so that odst2 is still
  // valid at the end.
  let off_arith (opff0:opff) (opff1:opff) dst src sz ctx: Err_ context =
    let ctx, odst2 = load_opf opff0 rf0 dst ri0 sz ctx in
    let ctx = binopff_opp opff1 rf0 src ri1 sz ctx in
    let store_ins = Ins (opff0 odst2 (OReg_f rf0 sz)) (ctx.pc + 1) in
    add_code store_ins ctx
  in
  // Only used for conversion routines, see comments on oif_conv.
  // sz is resultant size of the float.
  let off_conv (opff0:opff) (opff1:opff) dst src sz ctx: Err_ context =
    let ctx = binopff_opp opff1 rf0 src ri0 sz ctx in
    let odst2, oc = trans_operandf dst ri0 ctx in
    let ctx =
      match oc with
      | None -> ctx
      | Some c -> add_code c ctx
    in
    let store_ins = Ins (opff0 odst2 (OReg_f rf0 sz)) (ctx.pc + 1) in
    add_code store_ins ctx
  in
  // These are used ONLY for conversion routines, and have the same issue as the
  // other floating point instructions. This time, we do not have to load the dst
  // integer as it is not used in the conversion, only as a destination. We do not
  // need to load the source float as memory arguments are allowed.
  // dst int, src float. sz is the resultant integer size
  let oif_conv (opii0:opii) (opif1:opif) dst src sz ctx: Err_ context =
    let ctx = binopif_opp opif1 ri0 src ri1 sz ctx in
    let odst2, oc = trans_operandi dst ri1 ctx in
    let ctx =
      match oc with
      | None -> ctx
      | Some c -> add_code c ctx
    in
    let store_ins = Ins (opii0 odst2 (OReg ri0 sz)) (ctx.pc + 1) in
    add_code store_ins ctx
  in
  // Similar to oif_conv, these are also only used for conversion. Likewise, we
  // do not need to load the src integer as memory arguments are allowed. The dst
  // float need not be loaded as it is not used in the conversion, only as a destination.
  // dst float, src int. sz is the resultant float size
  let ofi_conv (opff0:opff) (opfi1:opfi) dst src sz ctx: Err_ context =
    let ctx = binopfi_opp opfi1 rf0 src ri0 sz ctx in
    let odst2, oc = trans_operandf dst ri0 ctx in
    let ctx =
      match oc with
      | None -> ctx
      | Some c -> add_code c ctx
    in
    let store_ins = Ins (opff0 odst2 (OReg_f rf0 sz)) (ctx.pc + 1) in
    add_code store_ins ctx
  in
  match ins1 with
  | Unreachable ->
    add_code (Ins Unreachable ctx.pc) ctx

  | Alloc   n -> fail_with "compile_ins: bad Alloc"
  | Dealloc n -> fail_with "compile_ins: bad Dealloc"
  | Push    src -> fail_with "compile_ins: bad Push"
  | Pop     dst -> fail_with "compile_ins: bad Pop"

  | CMov64 _ _ _ -> fail_with "CMov64 found at allocator. Should not happen."

  | Mov8        dst src -> oii Mov8 Mov8 dst src 1 ctx
  | Mov16       dst src -> oii Mov16 Mov16 dst src 2 ctx
  | Mov32       dst src -> oii Mov32 Mov32 dst src 4 ctx
  | Mov64       dst src -> oii Mov64 Mov64 dst src 8 ctx
  | MovZX8to32  dst src -> oii MovZX8to32 Mov32 dst src 4 ctx
  | MovZX8to64  dst src -> oii MovZX8to64 Mov64 dst src 8 ctx
  | MovSX8to32  dst src -> oii MovSX8to32 Mov32 dst src 4 ctx
  | MovSX8to64  dst src -> oii MovSX8to64 Mov64 dst src 8 ctx
  | MovZX16to32 dst src -> oii MovZX16to32 Mov32 dst src 4 ctx
  | MovZX16to64 dst src -> oii MovZX16to64 Mov64 dst src 8 ctx
  | MovSX16to32 dst src -> oii MovSX16to32 Mov32 dst src 4 ctx
  | MovSX16to64 dst src -> oii MovSX16to64 Mov64 dst src 8 ctx
  | MovZX32to64 dst src -> oii MovZX32to64 Mov64 dst src 8 ctx
  | MovSX32to64 dst src -> oii MovSX32to64 Mov64 dst src 8 ctx

  | FMov32 dst src -> off_mov FMov32 dst src 4 ctx
  | FMov64 dst src -> off_mov FMov64 dst src 8 ctx

  | Clz32    dst src -> oii Mov32 Clz32 dst src 4 ctx
  | Ctz32    dst src -> oii Mov32 Ctz32 dst src 4 ctx
  | Popcnt32 dst src -> oii Mov32 Popcnt32 dst src 4 ctx

  | Clz64    dst src -> oii Mov64 Clz64 dst src 8 ctx
  | Ctz64    dst src -> oii Mov64 Ctz64 dst src 8 ctx
  | Popcnt64 dst src -> oii Mov64 Popcnt64 dst src 8 ctx

  | FNeg32     dst src -> off_arith FMov32 FNeg32 dst src 4 ctx
  | FAbs32     dst src -> off_arith FMov32 FAbs32 dst src 4 ctx
  | FCeil32    dst src -> off_arith FMov32 FCeil32 dst src 4 ctx
  | FFloor32   dst src -> off_arith FMov32 FFloor32 dst src 4 ctx
  | FTrunc32   dst src -> off_arith FMov32 FTrunc32 dst src 4 ctx
  | FNearest32 dst src -> off_arith FMov32 FNearest32 dst src 4 ctx
  | FSqrt32    dst src -> off_arith FMov32 FSqrt32 dst src 4 ctx

  | FNeg64     dst src -> off_arith FMov64 FNeg64 dst src 8 ctx
  | FAbs64     dst src -> off_arith FMov64 FAbs64 dst src 8 ctx
  | FCeil64    dst src -> off_arith FMov64 FCeil64 dst src 8 ctx
  | FFloor64   dst src -> off_arith FMov64 FFloor64 dst src 8 ctx
  | FTrunc64   dst src -> off_arith FMov64 FTrunc64 dst src 8 ctx
  | FNearest64 dst src -> off_arith FMov64 FNearest64 dst src 8 ctx
  | FSqrt64    dst src -> off_arith FMov64 FSqrt64 dst src 8 ctx

  | Add32  dst src -> oii Mov32 Add32 dst src 4 ctx
  | Sub32  dst src -> oii Mov32 Sub32 dst src 4 ctx
  | Mul32  dst src -> oii Mov32 Mul32 dst src 4 ctx
  | DivS32 dst src -> oii Mov32 DivS32 dst src 4 ctx
  | DivU32 dst src -> oii Mov32 DivU32 dst src 4 ctx
  | RemS32 dst src -> oii Mov32 RemS32 dst src 4 ctx
  | RemU32 dst src -> oii Mov32 RemU32 dst src 4 ctx
  | And32  dst src -> oii Mov32 And32 dst src 4 ctx
  | Or32   dst src -> oii Mov32 Or32 dst src 4 ctx
  | Xor32  dst src -> oii Mov32 Xor32 dst src 4 ctx
  | Shl32  dst src -> oii Mov32 Shl32 dst src 4 ctx
  | ShrS32 dst src -> oii Mov32 ShrS32 dst src 4 ctx
  | ShrU32 dst src -> oii Mov32 ShrU32 dst src 4 ctx
  | Rotl32 dst src -> oii Mov32 Rotl32 dst src 4 ctx
  | Rotr32 dst src -> oii Mov32 Rotr32 dst src 4 ctx

  | Add64  dst src -> oii Mov64 Add64 dst src 8 ctx
  | Sub64  dst src -> oii Mov64 Sub64 dst src 8 ctx
  | Mul64  dst src -> oii Mov64 Mul64 dst src 8 ctx
  | DivS64 dst src -> oii Mov64 DivS64 dst src 8 ctx
  | DivU64 dst src -> oii Mov64 DivU64 dst src 8 ctx
  | RemS64 dst src -> oii Mov64 RemS64 dst src 8 ctx
  | RemU64 dst src -> oii Mov64 RemU64 dst src 8 ctx
  | And64  dst src -> oii Mov64 And64 dst src 8 ctx
  | Or64   dst src -> oii Mov64 Or64 dst src 8 ctx
  | Xor64  dst src -> oii Mov64 Xor64 dst src 8 ctx
  | Shl64  dst src -> oii Mov64 Shl64 dst src 8 ctx
  | ShrS64 dst src -> oii Mov64 ShrS64 dst src 8 ctx
  | ShrU64 dst src -> oii Mov64 ShrU64 dst src 8 ctx
  | Rotl64 dst src -> oii Mov64 Rotl64 dst src 8 ctx
  | Rotr64 dst src -> oii Mov64 Rotr64 dst src 8 ctx

  | FAdd32      dst src -> off_arith FMov32 FAdd32 dst src 4 ctx
  | FSub32      dst src -> off_arith FMov32 FSub32 dst src 4 ctx
  | FMul32      dst src -> off_arith FMov32 FMul32 dst src 4 ctx
  | FDiv32      dst src -> off_arith FMov32 FDiv32 dst src 4 ctx
  | FMin32      dst src -> off_arith FMov32 FMin32 dst src 4 ctx
  | FMax32      dst src -> off_arith FMov32 FMax32 dst src 4 ctx
  | FCopySign32 dst src -> off_arith FMov32 FCopySign32 dst src 4 ctx

  | FAdd64      dst src -> off_arith FMov64 FAdd64 dst src 8 ctx
  | FSub64      dst src -> off_arith FMov64 FSub64 dst src 8 ctx
  | FMul64      dst src -> off_arith FMov64 FMul64 dst src 8 ctx
  | FDiv64      dst src -> off_arith FMov64 FDiv64 dst src 8 ctx
  | FMin64      dst src -> off_arith FMov64 FMin64 dst src 8 ctx
  | FMax64      dst src -> off_arith FMov64 FMax64 dst src 8 ctx
  | FCopySign64 dst src -> off_arith FMov64 FCopySign64 dst src 8 ctx

  | I32TruncSF32 dst src -> oif_conv Mov32 I32TruncSF32 dst src 4 ctx
  | I32TruncUF32 dst src -> oif_conv Mov32 I32TruncUF32 dst src 4 ctx
  | I32TruncSF64 dst src -> oif_conv Mov32 I32TruncSF64 dst src 4 ctx
  | I32TruncUF64 dst src -> oif_conv Mov32 I32TruncUF64 dst src 4 ctx

  | I64TruncSF32 dst src -> oif_conv Mov64 I64TruncSF32 dst src 8 ctx
  | I64TruncUF32 dst src -> oif_conv Mov64 I64TruncUF32 dst src 8 ctx
  | I64TruncSF64 dst src -> oif_conv Mov64 I64TruncSF64 dst src 8 ctx
  | I64TruncUF64 dst src -> oif_conv Mov64 I64TruncUF64 dst src 8 ctx

  | F32DemoteF64   dst src -> off_conv FMov32 F32DemoteF64 dst src 4 ctx
  | F32ConvertSI32 dst src -> ofi_conv FMov32 F32ConvertSI32 dst src 4 ctx
  | F32ConvertUI32 dst src -> ofi_conv FMov32 F32ConvertUI32 dst src 4 ctx
  | F32ConvertSI64 dst src -> ofi_conv FMov32 F32ConvertSI64 dst src 4 ctx
  | F32ConvertUI64 dst src -> ofi_conv FMov32 F32ConvertUI64 dst src 4 ctx

  | F64PromoteF32  dst src -> off_conv FMov64 F64PromoteF32 dst src 8 ctx
  | F64ConvertSI32 dst src -> ofi_conv FMov64 F64ConvertSI32 dst src 8 ctx
  | F64ConvertUI32 dst src -> ofi_conv FMov64 F64ConvertUI32 dst src 8 ctx
  | F64ConvertSI64 dst src -> ofi_conv FMov64 F64ConvertSI64 dst src 8 ctx
  | F64ConvertUI64 dst src -> ofi_conv FMov64 F64ConvertUI64 dst src 8 ctx

  | ReinterpretFloat32 dst src -> oif_conv Mov32 ReinterpretFloat32 dst src 4 ctx
  | ReinterpretFloat64 dst src -> oif_conv Mov64 ReinterpretFloat64 dst src 8 ctx
  | ReinterpretInt32   dst src -> ofi_conv FMov32 ReinterpretInt32 dst src 4 ctx
  | ReinterpretInt64   dst src -> ofi_conv FMov64 ReinterpretInt64 dst src 8 ctx

val compile_ocmp: Sem1.ocmp -> context -> Err_ context
let compile_ocmp ocmp1 ctx =
  let ri0: Sem2.regi = 0 in
  let ri1: Sem2.regi = 1 in
  let rf0: Sem2.regf = 0 in
  let rf1: Sem2.regf = 1 in

  match ocmp1 with
  (* 32 bit comparisons *)
  | OEq32  oa1 ob1 -> cmpopii OEq32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | ONe32  oa1 ob1 -> cmpopii ONe32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OLe32  oa1 ob1 -> cmpopii OLe32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OGe32  oa1 ob1 -> cmpopii OGe32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OLt32  oa1 ob1 -> cmpopii OLt32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OGt32  oa1 ob1 -> cmpopii OGt32 Mov32 oa1 ob1 ri0 ri1 4 ctx

  | OLeS32 oa1 ob1 -> cmpopii OLeS32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OGeS32 oa1 ob1 -> cmpopii OGeS32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OLtS32 oa1 ob1 -> cmpopii OLtS32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  | OGtS32 oa1 ob1 -> cmpopii OGtS32 Mov32 oa1 ob1 ri0 ri1 4 ctx
  (* 64 bit comparisons *)
  | OEq64  oa1 ob1 -> cmpopii OEq64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | ONe64  oa1 ob1 -> cmpopii ONe64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OLe64  oa1 ob1 -> cmpopii OLe64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OGe64  oa1 ob1 -> cmpopii OGe64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OLt64  oa1 ob1 -> cmpopii OLt64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OGt64  oa1 ob1 -> cmpopii OGt64 Mov64 oa1 ob1 ri0 ri1 8 ctx

  | OLeS64 oa1 ob1 -> cmpopii OLeS64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OGeS64 oa1 ob1 -> cmpopii OGeS64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OLtS64 oa1 ob1 -> cmpopii OLtS64 Mov64 oa1 ob1 ri0 ri1 8 ctx
  | OGtS64 oa1 ob1 -> cmpopii OGtS64 Mov64 oa1 ob1 ri0 ri1 8 ctx

  (* 32 bit floats *)
  | OFEq32 oa1 ob1 -> cmpopff OFEq32 FMov32 oa1 ob1 rf0 ri0 4 ctx
  | OFNe32 oa1 ob1 -> cmpopff OFNe32 FMov32 oa1 ob1 rf0 ri0 4 ctx
  | OFLt32 oa1 ob1 -> cmpopff OFLt32 FMov32 oa1 ob1 rf0 ri0 4 ctx
  | OFGt32 oa1 ob1 -> cmpopff OFGt32 FMov32 oa1 ob1 rf0 ri0 4 ctx
  | OFLe32 oa1 ob1 -> cmpopff OFLe32 FMov32 oa1 ob1 rf0 ri0 4 ctx
  | OFGe32 oa1 ob1 -> cmpopff OFGe32 FMov32 oa1 ob1 rf0 ri0 4 ctx
  (* 64 bit floats *)
  | OFEq64 oa1 ob1 -> cmpopff OFEq64 FMov64 oa1 ob1 rf0 ri0 8 ctx
  | OFNe64 oa1 ob1 -> cmpopff OFNe64 FMov64 oa1 ob1 rf0 ri0 8 ctx
  | OFLt64 oa1 ob1 -> cmpopff OFLt64 FMov64 oa1 ob1 rf0 ri0 8 ctx
  | OFGt64 oa1 ob1 -> cmpopff OFGt64 FMov64 oa1 ob1 rf0 ri0 8 ctx
  | OFLe64 oa1 ob1 -> cmpopff OFLe64 FMov64 oa1 ob1 rf0 ri0 8 ctx
  | OFGe64 oa1 ob1 -> cmpopff OFGe64 FMov64 oa1 ob1 rf0 ri0 8 ctx

val store_args: list val_ty -> Sem1.regi -> Sem1.regf -> nat -> context -> Err_ context
let rec store_args argtys idx fidx stack ctx =
  let do_int sz: Err_ (nat * context) =
    if idx < Sem2.max_int_args then (
      // argument passed in register
      let store_ins = store_regi (idx + fidx) idx sz ctx in
      let ctx' = add_code store_ins ctx in
      stack, ctx'
    ) else (
      // argument passed on stack
      // one extra slot offset for return value on stack
      let offset = (ctx.top_regs + 1 + stack) `op_Multiply` 8 in
      let oreg = OReg Sem2.reg_int_ret sz in
      let ostack = OStackRel offset in
      let movop = if sz = 4 then Mov32 else Mov64 in
      let load_ins = Ins (movop oreg ostack) (ctx.pc + 1) in
      let ctx' = add_code load_ins ctx in
      let store_ins = store_regi (idx + fidx) Sem2.reg_int_ret sz ctx' in
      let ctx'' = add_code store_ins ctx' in
      stack + 1, ctx''
    )
  in
  let do_float sz: Err_ (nat * context) =
    if fidx < Sem2.max_float_args then (
      // argument passed in register
      let store_ins = store_regf (idx + fidx) fidx sz ctx in
      let ctx' = add_code store_ins ctx in
      stack, ctx'
    ) else (
      // argument passed on stack
      // one extra slot offset for return value on stack
      let offset = (ctx.top_regs + 1 + stack) `op_Multiply` 8 in
      let oreg = OReg_f Sem2.reg_float_ret sz in
      let ostack = OStackRel_f offset in
      let movop = if sz = 4 then FMov32 else FMov64 in
      let load_ins = Ins (movop oreg ostack) (ctx.pc + 1) in
      let ctx' = add_code load_ins ctx in
      let store_ins = store_regf (idx + fidx) Sem2.reg_float_ret sz ctx' in
      let ctx'' = add_code store_ins ctx' in
      stack + 1, ctx''
    )
  in
  match argtys with
  | [] -> ctx
  | I32_ty :: argtys ->
    let stack', ctx' = do_int 4 in
    store_args argtys (idx + 1) fidx stack' ctx'
  | I64_ty :: argtys ->
    let stack', ctx' = do_int 8 in
    store_args argtys (idx + 1) fidx stack' ctx'
  | F32_ty :: argtys ->
    let stack', ctx' = do_float 4 in
    store_args argtys idx (fidx + 1) stack' ctx'
  | F64_ty :: argtys ->
    let stack', ctx' = do_float 8 in
    store_args argtys idx (fidx + 1) stack' ctx'

let rec compile_locals_init_ (idx:Sem1.regi) ctx (top:Sem1.regi{idx <= top}): Err_ context (decreases (top - idx)) =
  if idx = top then ctx else (
    let store_ins = store_regi idx Sem2.reg_int_ret 8 ctx in
    let ctx' = add_code store_ins ctx in
    compile_locals_init_ (idx + 1) ctx' top
  )

/// Set up the stack frame. WASM semantics (4.4.7 in our copy) places the arguments
/// as the first few locals followed by the rest of the locals. Arguments should already
/// be included in the locals array.
/// Remainder of the locals should be initialized to zero.
/// HIMEM -> args || return || stored_args || locals_rem <- LOMEM stack_top
val compile_locals_init: context -> Err_ context
let compile_locals_init ctx =
  let argtys = ctx.fn_ax.fn_argtys in
  let locals = ctx.fn_ax.fn_locals in
  if L.length argtys > L.length locals then fail_with "compile_locals_init: invalid locals";
  let ctx' = store_args argtys 0 0 0 ctx in
  let xor = Xor64 (OReg Sem2.reg_int_ret 8) (OReg Sem2.reg_int_ret 8) in
  let clear_ins = Ins xor (ctx'.pc + 1) in
  if L.length locals > L.length argtys then (
    let ctx'' = add_code clear_ins ctx' in
    compile_locals_init_ (L.length argtys) ctx'' (L.length locals)
  ) else (
    ctx'
  )

/// NB: Loading is done in reverse to not clobber xmm0
val load_args: list ins_arg -> nat -> Sem1.regi -> Sem1.regf -> nat -> context -> Err_ context
let rec load_args args spilled_padded idx fidx stack ctx =
  match args with
  | [] -> ctx
  | ArgInt r is64 :: args ->
    let sz = if is64 then 8 else 4 in
    let movop = if is64 then Mov64 else Mov32 in
    let offset = (spilled_padded + ctx.top_regs - 1 - r) `op_Multiply` 8 in
    let ostack = OStackRel offset in
    if idx < Sem2.max_int_args then (
      // argument passed in register, do args backwards
      let ctx' = load_args args spilled_padded (idx + 1) fidx stack ctx in
      let v: Sem2.regi = idx in
      let oreg = OReg v sz in
      let load_ins = Ins (movop oreg ostack) (ctx'.pc + 1) in
      add_code load_ins ctx'
    ) else (
      // argument passed on stack, do args backwards
      let ctx' = load_args args spilled_padded (idx + 1) fidx (stack + 1) ctx in
      let oreg = OReg Sem2.reg_int_ret sz in
      let load_ins = Ins (movop oreg ostack) (ctx'.pc + 1) in
      let ctx'' = add_code load_ins ctx' in
      let arg_offset = stack `op_Multiply` 8 in
      let arg_stack = OStackRel arg_offset in
      let store_ins = Ins (movop arg_stack oreg) (ctx''.pc + 1) in
      add_code store_ins ctx''
    )
  | ArgFloat r is64 :: args ->
    let sz = if is64 then 8 else 4 in
    let movop = if is64 then FMov64 else FMov32 in
    let offset = (spilled_padded + ctx.top_regs - 1 - r) `op_Multiply` 8 in
    let ostack = OStackRel_f offset in
    if fidx < Sem2.max_float_args then (
      // argument passed in register, do args backwards
      let ctx' = load_args args spilled_padded idx (fidx + 1) stack ctx in
      let v: Sem2.regf = fidx in
      let oreg = OReg_f v sz in
      let load_ins = Ins (movop oreg ostack) (ctx'.pc + 1) in
      add_code load_ins ctx'
    ) else (
      // argument passed on stack, do args backwards
      let ctx' = load_args args spilled_padded idx (fidx + 1) (stack + 1) ctx in
      let oreg = OReg_f Sem2.reg_float_ret sz in
      let load_ins = Ins (movop oreg ostack) (ctx'.pc + 1) in
      let ctx'' = add_code load_ins ctx' in
      let arg_offset = stack `op_Multiply` 8 in
      let arg_stack = OStackRel_f arg_offset in
      let store_ins = Ins (movop arg_stack oreg) (ctx''.pc + 1) in
      add_code store_ins ctx''
    )

val compile_highcall: Sem1.target_t -> list ins_arg -> option ins_arg -> context -> Err_ context
let compile_highcall target args retval_store ctx1 =
  // Compute stack arguments
  let num_int_args, num_float_args =
    L.fold_left (fun v arg -> if ArgInt? arg
                           then (fst v + 1, snd v)
                           else (fst v, snd v + 1)) (0, 0) args in
  let spilled = max 0 (num_int_args - Sem2.max_int_args) + max 0 (num_float_args - Sem2.max_float_args) in
  // Upon function entry, stack is 8 mod 16. Before call, stack has to be 0 mod 16 (sysv abi).
  let pad = (spilled + ctx1.top_regs) `op_Modulus` 2 = 0 in
  let spilled_padded = if pad then spilled + 1 else spilled in
  // Allocate space for stack arguments
  let ctx2 =
    if spilled_padded = 0
    then ctx1
    else (
      let alloc_ins = Ins (Alloc (spilled_padded `op_Multiply` 8)) (ctx1.pc + 1) in
      add_code alloc_ins ctx1
    )
  in
  // Load arguments TODO: edit load_args
  let ctx3 = load_args args spilled_padded 0 0 0 ctx2 in
  // Emit call instruction, loading register if necessary
  let ctx4 =
    match target with
    | CallDirect n ->
      add_code (Call (CallDirect n) (ctx3.pc + 1)) ctx3
    | CallIndirect r ->
      let offset = (spilled_padded + ctx3.top_regs - 1 - r) `op_Multiply` 8 in
      let ostack = OStackRel offset in
      let oreg = OReg Sem2.reg_int_ret 4 in
      // indirect indexing is 32-bit only
      let load_ind_ins = Ins (Mov32 oreg ostack) (ctx3.pc + 1) in
      let ctx3' = add_code load_ind_ins ctx3 in
      add_code (Call (CallIndirect Sem2.reg_int_ret) (ctx3'.pc + 1)) ctx3'
  in
  // Tear down stack arguments
  let ctx5 =
    if spilled_padded = 0
    then ctx4
    else (
      let dealloc_ins = Ins (Dealloc (spilled_padded `op_Multiply` 8)) (ctx4.pc + 1) in
      add_code dealloc_ins ctx4
    )
  in
  // Save return value
  match retval_store with
  | None -> ctx5
  | Some (ArgInt r is64) ->
    let sz = if is64 then 8 else 4 in
    let store_ins = store_regi r Sem2.reg_int_ret sz ctx5 in
    add_code store_ins ctx5
  | Some (ArgFloat r is64) ->
    let sz = if is64 then 8 else 4 in
    let store_ins = store_regf r Sem2.reg_float_ret sz ctx5 in
    add_code store_ins ctx5

#push-options "--z3cliopt smt.arith.nl=true"
val compile_precode: Sem1.precode -> context -> Err_ context
let compile_precode c1 ctx1 =
  let old_pc = ctx1.old_pc in
  let old_follows:loc = old_pc + 1 in
  let new_pc_lower = ctx1.pc in
  let r0 : Sem2.regi = 0 in
  let f0 : Sem1.regf = 0 in
  // Process precode
  let ctx2 =
    match c1 with
    | FnEntry name next ->
      // NB: Spill allocator never uses callee-saved regs
      let ctx_ = add_code (FnEntry name (ctx1.pc + 1)) ctx1 in
      // NB: We skip allocation and storing of locals/params if the function has no
      // register usage, in order to avoid negative stack offsets
      if ctx_.top_regs = 0 then ctx_ else (
      	 let alloc_ins = Ins (Alloc (ctx_.top_regs `op_Multiply` 8)) (ctx_.pc + 1) in
      	 let ctx_' = add_code alloc_ins ctx_ in
      	 compile_locals_init ctx_'
      )
    | FnExit name ->
      add_code (FnExit name) ctx1
    | Ins i next ->
      compile_ins i ctx1
    | InsList is next ->
      fail_with "compile_precode: bad ins_list"
    | Nop next ->
      add_code (Nop (ctx1.pc + 1)) ctx1
    | Cmp cond nextTrue nextFalse ->
      compile_ocmp cond ctx1
    | Switch case_table case ->
      // Case value is 32-bit only
      let c = load_regi r0 case 4 ctx1 in
      let ctx_ = add_code c ctx1 in
      let switch_ins = Switch case_table r0 in
      add_code switch_ins ctx_
    | Call target onreturn ->
      fail_with "compile_precode: bad Call"
    | HighCall target args retval_store onreturn ->
      compile_highcall target args retval_store ctx1
    | Ret next ->
      fail_with "compile_precode: bad Ret"
    | HighRet retval_load next ->
      // NB: Same as FnEntry, we skip the entire deallocation if the function has
      // no register usage. In this case there can also be no return value.
      let ctx_ =
        match retval_load with
        | None ->
          ctx1
        | Some (ArgInt r is64) ->
          if not (Sem1.valid_reg_int r) || ctx1.top_regs = 0 then (
            fail_with "compile_precode: bad ArgInt"
          ) else (
            let sz = if is64 then 8 else 4 in
            let movop = if is64 then Mov64 else Mov32 in
            fst (load_opi movop Sem2.reg_int_ret (OReg r sz) r0 sz ctx1)
          )
        | Some (ArgFloat r is64) ->
          if not (Sem1.valid_reg_float r) || ctx1.top_regs = 0 then (
            fail_with "compile_precode: bad ArgFloat"
          ) else (
            let sz = if is64 then 8 else 4 in
            let movop = if is64 then FMov64 else FMov32 in
            fst (load_opf movop Sem2.reg_float_ret (OReg_f r sz) r0 sz ctx1)
          )
      in
      let ctx_' = if ctx_.top_regs = 0 then ctx_ else (
      	  let dealloc_ins = Ins (Dealloc (ctx_.top_regs `op_Multiply` 8)) (ctx_.pc + 1) in
      	  add_code dealloc_ins ctx_
      )
      in
      let ret_ins = Ret (ctx_'.pc + 1) in
      add_code ret_ins ctx_'
  in
  // Grab next pointers
  let old_nexts = get_next ctx1.m1.module_aux c1 in
  let new_pc_upper = ctx2.pc in
  // Set range of current instruction mapping
  let ctx3 = set_map old_pc new_pc_lower new_pc_upper ctx2 in
  // Set pending next rewrite if necessary
  // Pending instruction (if any) is always last in sequence
  let check_set_pending lnext pc_pending ctx: Err_ context =
    match lnext with
    | [] -> fail_with "check_set_pending: empty lnext"
    | [next] ->
      if next = old_follows
      then ctx
      else set_pending pc_pending lnext ctx
    | lnext ->
      set_pending pc_pending lnext ctx
  in
  if new_pc_upper = 0
  then fail_with "compile_precode: new_pc_upper failed"
  else (
    if (FnExit? c1) || (Switch? c1)
    then ctx3 // these don't need fixing/fixed separately
    else check_set_pending old_nexts (new_pc_upper - 1) ctx3
  )
#pop-options

val compile_precodes: Sem1.cfg -> context -> Err_ context
let rec compile_precodes cs ctx =
  match cs with
  | [] -> ctx
  | c :: cs ->
    let ctx' = compile_precode c ctx in
    let ctx'' = inc_old ctx' in
    compile_precodes cs ctx''

val compile_fn: aux_fn -> context -> Err_ (aux_fn * context)
let compile_fn fn_ax ctx1 =
  let {fn_name; fn_str; fn_loc; fn_end;
       fn_argtys; fn_rettys; fn_isImported;
       fn_isExported} = fn_ax in
  let ctx2 = {ctx1 with c = AOL.empty} in
  // Skip imported, nothing to compile here
  if fn_isImported
  then (fn_ax, ctx2)
  else (
    if fn_end <= fn_loc
    then fail_with "compile_fn: bad fn_end"
    else (
      // Compile codes of function
      // NB: fn_end is not inclusive
      let cs, _ = L.splitAt (fn_end - fn_loc) (snd (L.splitAt fn_loc ctx2.m1.module_cfg)) in
      let top_regs =
        match calculate_reg_usage_precodes cs with
        | None -> 0
        | Some idx -> idx + 1
      in
      let ctx3 = {ctx2 with fn_ax = fn_ax; old_pc = fn_loc; top_regs = top_regs} in
      let ctx4 = compile_precodes cs ctx3 in
      // Calculate updated aux
      let fn_loc' = ctx3.pc in
      let fn_end' = ctx4.pc in
      if fn_end' <= fn_loc'
      then fail_with ("compile_fn (" ^ fn_ax.fn_str ^ "): bad fn_end' (" ^ string_of_int fn_loc' ^ " " ^  string_of_int fn_end' ^ ")")
      else (
        let fn_ax' = {fn_ax with fn_loc = fn_loc'; fn_end = fn_end'} in
        (fn_ax', ctx4)
      )
    )
  )

val compile_fns: list aux_fn -> context -> Err_ (list aux_fn * context)
let rec compile_fns fn_axs ctx1 =
  match fn_axs with
  | [] -> ([], ctx1)
  | fn_ax :: fn_axs ->
    let fn_ax', ctx2 = compile_fn fn_ax ctx1 in
    let ctx3 = {ctx2 with c_all = AOL.append ctx2.c_all ctx2.c} in
    let fn_axs', ctx4 = compile_fns fn_axs ctx3 in
    (fn_ax' :: fn_axs', ctx4)

val map_pending: list loc -> context -> Err_ (list loc)
let rec map_pending old_next_pcs ctx =
  match old_next_pcs with
  | [] -> []
  | old_next_pc :: old_next_pcs ->
    let new_lower, _ = get_map old_next_pc ctx in
    let mapped = map_pending old_next_pcs ctx in
    (new_lower :: mapped)

val set_next: Sem2.precode -> list loc -> Err_ Sem2.precode
let set_next c locs =
  match c, locs with
  | FnEntry name _, [next] -> FnEntry name next
  | FnExit name, [] -> FnExit name
  | Ins i _, [next] -> Ins i next
  | InsList is _, [next] -> InsList is next
  | Nop _, [next] -> Nop next
  | Cmp cond _ _, [nextTrue; nextFalse] -> Cmp cond nextTrue nextFalse
  | Switch case_table case, [] -> Switch case_table case
  | Call target _, [onreturn] -> Call target onreturn
  | HighCall target args retval_store _, [onreturn] -> HighCall target args retval_store onreturn
  | Ret _, [next] -> Ret next
  | HighRet retval_load _, [next] -> HighRet retval_load next
  | _, _ -> fail_with "set_next: bad combination of operands"

val rewrite_pendings: list (loc * list loc) -> context -> Err_ context
let rec rewrite_pendings pendings ctx =
  match pendings with
  | [] -> ctx
  | (new_pc_pending_update, old_next_pcs) :: pendings ->
    if new_pc_pending_update >= AOL.length ctx.c
    then fail_with "rewrite_pendings: pending update oob"
    else (
      let mapped = map_pending old_next_pcs ctx in
      let pcode, c_op = AOL.index_and_optimize ctx.c new_pc_pending_update in
      let pcode' = set_next pcode mapped in
      let c' = AOL.update_at c_op new_pc_pending_update pcode' in
      rewrite_pendings pendings ({ctx with c = c'})
    )

val rewrite_br_tables: list aux_br_table -> context -> Err_ (list aux_br_table)
let rec rewrite_br_tables brs ctx =
  match brs with
  | [] -> []
  | br :: brs ->
    let mapped = map_pending br.br_targets ctx in
    let brs' = rewrite_br_tables brs ctx in
    {br with br_targets = mapped} :: brs'

val compile_module: Sem1.module_ -> Err_ Sem2.module_
let compile_module m =
  // Setup context and compile
  let fn_ax_empty = {fn_name = 0; fn_str = ""; fn_loc = 0; fn_end = 0;
                     fn_argtys = []; fn_rettys = None; fn_locals = [];
                     fn_isImported = false; fn_isExported = false} in
  let ctx1 = {
    m1 = m;
    fn_ax = fn_ax_empty;
    pc = 0;
    old_pc = 0;
    c = AOL.empty;
    c_all = AOL.empty;
    top_regs = 0;
    mapping = M.const None;
    pending = [];
  } in
  let fn_axs', ctx2 = compile_fns m.module_aux.fns ctx1 in
  let ctx3 = {ctx2 with c = ctx2.c_all} in
  // Rewrite pending jumps
  let ctx4 = rewrite_pendings ctx3.pending ctx3 in
  // Rewrite br tables
  let br_tables' = rewrite_br_tables ctx4.m1.module_aux.br_tables ctx4 in
  // Construct module
  let ax' = {ctx4.m1.module_aux with fns = fn_axs'; br_tables = br_tables'} in
  let m' = {module_aux = ax'; module_cfg = AOL.to_list ctx4.c} in
  m'
