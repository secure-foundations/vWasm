module Semantics.Printer

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
open Semantics.Printer.AuxiliaryRoutines

#reset-options "--ifuel 1 --fuel 0"

unfold let memory_name : string = "MEMORY"

unfold
let string_of_jump_loc (l:loc) : string =
  "_L" ^ string_of_int l

unfold
let string_of_brtable (table_id:int) : string =
  "BRTABLE" ^ string_of_int table_id

unfold
let string_of_global_ident (ident:nat) : string =
  "GBL" ^ string_of_int ident

let print_jump_if_not_fallthrough (current_label next:loc) : Printer unit =
  if next = current_label + 1 then ()
  else print Main ("  jmp " ^ string_of_jump_loc next ^ "\n")

let string_of_regi (size:nat) (r:regi) : string =
  let r64, r32, r16, r8 = match r with
    | 0 -> "rdi", "edi", "di", "dil"
    | 1 -> "rsi", "esi", "si", "sil"
    | 2 -> "rdx", "edx", "dx", "dl"
    | 3 -> "rcx", "ecx", "cx", "cl"
    | 4 -> "r8", "r8d", "r8w", "r8b"
    | 5 -> "r9", "r9d", "r9w", "r9b"
    | 6 -> "r10", "r10d", "r10w", "r10b"
    | 7 -> "r11", "r11d", "r11w", "r11b"
    | 8 -> "rax", "eax", "ax", "al"
    | 9 -> "rbx", "ebx", "bx", "bl"
    | 10 -> "rbp", "ebp", "bp", "bpl"
    | 11 -> "r12", "r12d", "r12w", "r12b"
    | 12 -> "r13", "r13d", "r13w", "r13b"
    | 13 -> "r14", "r14d", "r14w", "r14b"
    | 14 -> "r15", "r15d", "r15w", "r15b"
  in
  match size with
  | 8 -> r8
  | 16 -> r16
  | 32 -> r32
  | 64 -> r64
  | _ -> "***INVALID REGISTER SIZE***"

let string_of_regf (r:regf) : string =
  "xmm" ^ string_of_int r

let is_regi_name (s:string) : Tot bool =
  s = "rdi" || s = "rsi" || s = "rdx" || s = "rcx" || s = "r8" || s = "r9" ||
  s = "r10" || s = "r11" || s = "rax" || s = "rbx" || s = "rbp" || s = "r12" ||
  s = "r13" || s = "r14" || s = "r15"

let regi_of_string (s:string) :
  Pure regi
    (requires (is_regi_name s))
    (ensures (fun r -> string_of_regi 64 r = s)) =
  match s with
  | "rdi" -> 0
  | "rsi" -> 1
  | "rdx" -> 2
  | "rcx" -> 3
  | "r8" -> 4
  | "r9" -> 5
  | "r10" -> 6
  | "r11" -> 7
  | "rax" -> 8
  | "rbx" -> 9
  | "rbp" -> 10
  | "r12" -> 11
  | "r13" -> 12
  | "r14" -> 13
  | "r15" -> 14

type operand =
  | I32 of operandi
  | I64 of operandi
  | F32 of operandf
  | F64 of operandf

let string_of_maddr (m:maddr) : string =
  match m with
  | MIndex scale index offset ->
    "[" ^ string_of_regi 64 index ^ " * " ^ string_of_int scale ^
    " + " ^ string_of_int offset ^ " + " ^ memory_name ^ "]"

let pointer_kind (size:nat) : string =
  match size with
  | 8 -> "BYTE"
  | 16 -> "WORD"
  | 32 -> "DWORD"
  | 64 -> "QWORD"
  | _ -> "***INVALID PTR KIND***"

let string_of_operandi (size:nat) (o:operandi) : string =
  match o with
  | OConst n -> string_of_int n
  | OReg r _ -> string_of_regi size r
  | OMemRel offset -> pointer_kind size ^ " " ^ string_of_maddr offset
  | OStackRel offset -> pointer_kind size ^ " [rsp + " ^ string_of_int offset ^ "]"
  | ONamedGlobal (Ident i) -> pointer_kind size ^ " [" ^ string_of_global_ident i ^ "]"
  | ONamedGlobal MemPages -> pointer_kind size ^ " [MEM_PAGES]"

let string_of_operandf (size:nat) (o:operandf) : Printer string =
  match o with
  | OConst_f f ->
    let const_id = get_fresh FloatingConstant in
    let constant_name = "CONST_F_" ^ string_of_int const_id in
    prints Constants [
      "STATIC " ^ constant_name ^ "\n";
      constant_name ^ ":\n";
      "  ";
      (match size with
       | 32 -> "dd"
       | 64 -> "dq"
       | _ -> "***INVALID FLOATING CONSTANT SIZE: " ^ string_of_int size ^ "***");
      string_of_int f;
      "\n\n";
    ];
    pointer_kind size ^ " [" ^ constant_name ^ "]"
  | OReg_f r s -> if s `op_Multiply` 8 = size then (
      string_of_regf r
    ) else (
      "***INVALID FLOATING REGISTER SIZE: " ^ string_of_int s ^ " vs " ^ string_of_int size ^ "***"
    )
  (* Nasm, for whatever reason, doesn't want "pointerkind" specified for floating mem operands *)
  | OMemRel_f offset -> string_of_maddr offset
  (* Same for stack *)
  | OStackRel_f offset -> "[rsp + " ^ string_of_int offset ^ "]"
  (* Same for named globals *)
  | ONamedGlobal_f (Ident_f i) -> "[" ^ string_of_global_ident i ^ "]"

let string_of_operand (o:operand) : Printer string =
  match o with
  | I32 o -> string_of_operandi 32 o
  | I64 o -> string_of_operandi 64 o
  | F32 o -> string_of_operandf 32 o
  | F64 o -> string_of_operandf 64 o

let operands_of_conditional (cond:ocmp) : (operand & operand) =
  match cond with
  | OEq32 o1 o2
  | ONe32 o1 o2
  | OLe32 o1 o2
  | OGe32 o1 o2
  | OLt32 o1 o2
  | OGt32 o1 o2
  | OLeS32 o1 o2
  | OGeS32 o1 o2
  | OLtS32 o1 o2
  | OGtS32 o1 o2 ->
    (I32 o1, I32 o2)
  | OEq64 o1 o2
  | ONe64 o1 o2
  | OLe64 o1 o2
  | OGe64 o1 o2
  | OLt64 o1 o2
  | OGt64 o1 o2
  | OLeS64 o1 o2
  | OGeS64 o1 o2
  | OLtS64 o1 o2
  | OGtS64 o1 o2 ->
    (I64 o1, I64 o2)
  | OFEq32 o1 o2
  | OFNe32 o1 o2
  | OFLt32 o1 o2
  | OFGt32 o1 o2
  | OFLe32 o1 o2
  | OFGe32 o1 o2 ->
    (F32 o1, F32 o2)
  | OFEq64 o1 o2
  | OFNe64 o1 o2
  | OFLt64 o1 o2
  | OFGt64 o1 o2
  | OFLe64 o1 o2
  | OFGe64 o1 o2 ->
    (F64 o1, F64 o2)

let string_of_conditional_jmp (cond:ocmp) : string =
  match cond with
  | OEq32 o1 o2 | OEq64 o1 o2 -> "je"
  | ONe32 o1 o2 | ONe64 o1 o2 -> "jne"
  | OLe32 o1 o2 | OLe64 o1 o2 -> "jbe"
  | OGe32 o1 o2 | OGe64 o1 o2 -> "jae"
  | OLt32 o1 o2 | OLt64 o1 o2 -> "jb"
  | OGt32 o1 o2 | OGt64 o1 o2 -> "ja"
  | OLeS32 o1 o2 | OLeS64 o1 o2 -> "jle"
  | OGeS32 o1 o2 | OGeS64 o1 o2 -> "jge"
  | OLtS32 o1 o2 | OLtS64 o1 o2 -> "jl"
  | OGtS32 o1 o2 | OGtS64 o1 o2 -> "jg"
  (* floating point *)
  | OFEq32 o1 o2 | OFEq64 o1 o2 -> "je"
  | OFNe32 o1 o2 | OFNe64 o1 o2 -> "jne"
  | OFLt32 o1 o2 | OFLt64 o1 o2 -> "jb"
  | OFGt32 o1 o2 | OFGt64 o1 o2 -> "ja"
  | OFLe32 o1 o2 | OFLe64 o1 o2 -> "jbe"
  | OFGe32 o1 o2 | OFGe64 o1 o2 -> "jae"

let invert_ocmp (cond:ocmp) : Printer ocmp =
  match cond with
  | OEq32 o1 o2 -> ONe32 o1 o2
  | ONe32 o1 o2 -> OEq32 o1 o2
  | OLe32 o1 o2 -> OGt32 o1 o2
  | OGe32 o1 o2 -> OLt32 o1 o2
  | OLt32 o1 o2 -> OGe32 o1 o2
  | OGt32 o1 o2 -> OLe32 o1 o2
  | OLeS32 o1 o2 -> OGtS32 o1 o2
  | OGeS32 o1 o2 -> OLtS32 o1 o2
  | OLtS32 o1 o2 -> OGeS32 o1 o2
  | OGtS32 o1 o2 -> OLe32 o1 o2
  | OEq64 o1 o2 -> ONe64 o1 o2
  | ONe64 o1 o2 -> OEq64 o1 o2
  | OLe64 o1 o2 -> OGt64 o1 o2
  | OGe64 o1 o2 -> OLt64 o1 o2
  | OLt64 o1 o2 -> OGe64 o1 o2
  | OGt64 o1 o2 -> OLe64 o1 o2
  | OLeS64 o1 o2 -> OGtS64 o1 o2
  | OGeS64 o1 o2 -> OLtS64 o1 o2
  | OLtS64 o1 o2 -> OGeS64 o1 o2
  | OGtS64 o1 o2 -> OLe64 o1 o2
  | OFEq32 o1 o2 -> OFNe32 o1 o2
  | OFNe32 o1 o2 -> OFEq32 o1 o2
  | OFLt32 o1 o2 -> OFGe32 o1 o2
  | OFGt32 o1 o2 -> OFLe32 o1 o2
  | OFLe32 o1 o2 -> OFGt32 o1 o2
  | OFGe32 o1 o2 -> OFLt32 o1 o2
  | OFEq64 o1 o2 -> OFNe64 o1 o2
  | OFNe64 o1 o2 -> OFEq64 o1 o2
  | OFLt64 o1 o2 -> OFGe64 o1 o2
  | OFGt64 o1 o2 -> OFLe64 o1 o2
  | OFLe64 o1 o2 -> OFGt64 o1 o2
  | OFGe64 o1 o2 -> OFLt64 o1 o2

type _print_ins_t tag =
  (i:ins_t{I.tag_of_ins i = tag}) -> Printer unit

let _print_ins_Misc : _print_ins_t I.Misc = fun i ->
  match i with
  | Unreachable -> print Main "jmp internal___explicit_safe_kill ; unreachable"
  | CMov64 cond dst src ->
    let ncond = invert_ocmp cond in
    let o1, o2 = operands_of_conditional ncond in
    print Main (
      "%macro locallabel_cmov64 0\n" ^ (
        "  cmp " ^ string_of_operand o1 ^ ", " ^ string_of_operand o2 ^ "\n" ^
        "  " ^ string_of_conditional_jmp ncond ^ " short %%skip\n" ^
        "  mov " ^ string_of_operandi 64 dst ^ ", " ^ string_of_operandi 64 src ^ "\n" ^
        " %%skip:\n"
      ) ^ "  %endmacro locallabel_cmov64\n" ^
      " locallabel_cmov64\n" ^
      "  %unmacro locallabel_cmov64 0\n"
    )

let _print_ins_StackOp : _print_ins_t I.StackOp = fun i ->
  print Main (
    match i with
    | Alloc n   -> "sub rsp, " ^ string_of_int n
    | Dealloc n -> "add rsp, " ^ string_of_int n
    | Push src  -> "push " ^ string_of_operandi 64 src
    | Pop dst   -> "pop " ^ string_of_operandi 64 dst
  )

let _print_ins_Mov : _print_ins_t I.Mov = fun i ->
  let f n dst src : Printer unit = print Main (
      "mov " ^ string_of_operandi n dst ^ ", " ^ string_of_operandi n src) in
  match i with
  | Mov8  dst src -> f 8  dst src
  | Mov16 dst src -> f 16 dst src
  | Mov32 dst src -> f 32 dst src
  | Mov64 dst src -> f 64 dst src

let _print_ins_Movzx : _print_ins_t I.Movzx = fun i ->
  let f ndst dst nsrc src : Printer unit = print Main (
      "movzx " ^ string_of_operandi ndst dst ^ ", " ^ string_of_operandi nsrc src) in
  match i with
  | MovZX8to32  dst src -> f 32 dst  8 src
  | MovZX8to64  dst src -> f 64 dst  8 src
  | MovZX16to32 dst src -> f 32 dst 16 src
  | MovZX16to64 dst src -> f 64 dst 16 src
  | MovZX32to64 dst src -> (
      (* Since x64 doesn't have a movzx for 32 -> 64 *)
      match dst with
      | OConst _ -> print Main "***constant dst for movzx wat***"
      | OReg r _ ->
        (* A normal move is enough, because x64 zeros out top half of register when moving to it *)
        print Main ("mov " ^ string_of_operandi 32 dst ^ ", " ^ string_of_operandi 32 src)
      | OMemRel _ | OStackRel _ | ONamedGlobal _ ->
        (* We just expand this to 2 moves. First we move a 0 in, then
           we move the value in as a 32-bit value. This is reasonable
           since x86 is little-endian, and thus we don't need to do
           any offset-changing and can just write 4 bytes at the same
           offset. *)
        print Main ("mov " ^ string_of_operandi 64 dst ^ ", 0");
        print Main ("mov " ^ string_of_operandi 32 dst ^ ", " ^ string_of_operandi 32 src)
    )

let _print_ins_Movsx : _print_ins_t I.Movsx = fun i ->
  let f op ndst dst nsrc src : Printer unit = print Main (
      op ^ " " ^ string_of_operandi ndst dst ^ ", " ^ string_of_operandi nsrc src) in
  match i with
  | MovSX8to32  dst src -> f "movsx"  32 dst  8 src
  | MovSX8to64  dst src -> f "movsx"  64 dst  8 src
  | MovSX16to32 dst src -> f "movsx"  32 dst 16 src
  | MovSX16to64 dst src -> f "movsx"  64 dst 16 src
  | MovSX32to64 dst src -> f "movsxd" 64 dst 32 src (* Since x64 can't use the same name; smh *)

let _print_ins_FMov : _print_ins_t I.FMov = fun i ->
  let f op n dst src : Printer unit = print Main (
      op ^ " " ^ string_of_operandf n dst ^ ", " ^ string_of_operandf n src) in
  match i with
  | FMov32 dst src -> f "movss" 32 dst src
  | FMov64 dst src -> f "movsd" 64 dst src

let lines (l:list string) : string =
  fold_right (fun x r -> x ^ "\n" ^ r) l ""

let operandi_uses_register (o:operandi) (reg:string) :
  Pure bool
    (requires (is_regi_name reg))
    (ensures (fun _ -> True)) =
  match o with
  | OConst _ -> false
  | OReg r _ -> r = regi_of_string reg
  | OMemRel (MIndex _ idx _) -> idx = regi_of_string reg
  | OStackRel _ -> false (* Since rsp is reserved and can't be [reg] *)
  | ONamedGlobal (Ident _) -> false
  | ONamedGlobal MemPages -> false

(** Shift [o] due to [n] push instructions *)
let stack_shifted_operandi (n:int) (o:operandi) = match o with
  | OStackRel offset -> OStackRel (offset + (8 `op_Multiply` n))
  | _ -> o

let string_of_iunop (i:ins_t{I.tag_of_ins i = I.I32_Unop \/ I.tag_of_ins i = I.I64_Unop}) :
  Pure string
    (requires (True))
    (ensures (fun _ -> True)) =
  let n = if I.tag_of_ins i = I.I32_Unop then 32 else 64 in
  let (op, dst, src) = match i with
    | Clz32    dst src | Clz64    dst src -> ("lzcnt",  dst, src)
    | Ctz32    dst src | Ctz64    dst src -> ("tzcnt",  dst, src)
    | Popcnt32 dst src | Popcnt64 dst src -> ("popcnt", dst, src)
  in
  let direct_printing = op ^ " " ^ string_of_operandi n dst ^ ", " ^ string_of_operandi n src in
  match dst with
  | OConst _ -> "***constant dst for unop wat***"
  | OReg _ _ -> direct_printing
  | OMemRel _ | OStackRel _ | ONamedGlobal _ ->
    let temp_reg = (
      if not (operandi_uses_register dst "rcx") then "rcx"
      else (
        (* If it uses rcx, no chance it can use rax, so we can use rax as the temp *)
        assert (not (operandi_uses_register dst "rax"));
       "rax"
      )
    ) in
    let shifted_dst = stack_shifted_operandi 1 dst in
    let shifted_src = stack_shifted_operandi 1 src in
    let reg_dst = string_of_regi n (regi_of_string temp_reg) in
    lines [
      " ; " ^ direct_printing;
      " push " ^ temp_reg;
      " " ^ op ^ " " ^ reg_dst ^ ", " ^ string_of_operandi n shifted_src;
      " mov " ^ string_of_operandi n shifted_dst ^ ", " ^ reg_dst;
      " pop " ^ temp_reg;
    ]

let _print_ins_I32_Unop : _print_ins_t I.I32_Unop = fun i -> print Main (string_of_iunop i)

let _print_ins_I64_Unop : _print_ins_t I.I64_Unop = fun i -> print Main (string_of_iunop i)

let save_caller_saved_registers : string =
  "  push rdi\n" ^
  "  push rsi\n" ^
  "  push rdx\n" ^
  "  push rcx\n" ^
  "  push r8\n" ^
  "  push r9\n" ^
  "  push r10\n" ^
  "  push r11\n" ^
  "  push rax\n"

let restore_caller_saved_registers : string =
  "  pop rax\n" ^
  "  pop r11\n" ^
  "  pop r10\n" ^
  "  pop r9\n" ^
  "  pop r8\n" ^
  "  pop rcx\n" ^
  "  pop rdx\n" ^
  "  pop rsi\n" ^
  "  pop rdi\n"

let _print_ins_F32_Unop : _print_ins_t I.F32_Unop = fun i ->
  match i with
  | FNeg32 dst src -> print Main ("xorps " ^ string_of_operandf 32 dst ^ ", [CONST_NEG32]")
  | FAbs32 dst src -> print Main ("andps " ^ string_of_operandf 32 dst ^ ", [CONST_ABS32]")
  | FCeil32 dst src -> print Main ("roundss " ^ string_of_operandf 32 dst ^ ", " ^ string_of_operandf 32 src ^ ", 10")
  | FFloor32 dst src -> print Main ("roundss " ^ string_of_operandf 32 dst ^ ", " ^ string_of_operandf 32 src ^ ", 9")
  | FTrunc32 dst src -> print Main ("roundss " ^ string_of_operandf 32 dst ^ ", " ^ string_of_operandf 32 src ^ ", 11")
  | FNearest32 dst src -> print Main ("roundss " ^ string_of_operandf 32 dst ^ ", " ^ string_of_operandf 32 src ^ ", 8")
  | FSqrt32 dst src -> print Main ("sqrtss " ^ string_of_operandf 32 dst ^ ", " ^
                                   string_of_operandf 32 src)

let _print_ins_F64_Unop : _print_ins_t I.F64_Unop = fun i ->
  match i with
  | FNeg64 dst src -> print Main ("xorps " ^ string_of_operandf 64 dst ^ ", [CONST_NEG64]")
  | FAbs64 dst src -> print Main ("andps " ^ string_of_operandf 64 dst ^ ", [CONST_ABS64]")
  | FCeil64 dst src -> print Main ("roundsd " ^ string_of_operandf 64 dst ^ ", " ^ string_of_operandf 64 src ^ ", 10")
  | FFloor64 dst src -> print Main ("roundsd " ^ string_of_operandf 64 dst ^ ", " ^ string_of_operandf 64 src ^ ", 9")
  | FTrunc64 dst src -> print Main ("roundsd " ^ string_of_operandf 64 dst ^ ", " ^ string_of_operandf 64 src ^ ", 11")
  | FNearest64 dst src -> print Main ("roundsd " ^ string_of_operandf 64 dst ^ ", " ^ string_of_operandf 64 src ^ ", 8")
  | FSqrt64 dst src -> print Main ("sqrtsd " ^ string_of_operandf 64 dst ^ ", " ^
                                   string_of_operandf 64 src)

type print_divop_t = {
  div_signed: bool;
  div_64_bit: bool;
  div_quotient: bool;
  div_dst: operandi;
  div_src: operandi;
}

(* XXX This feels horrid. Is there a better thing we could do? *)
let string_of_division_operation (d:print_divop_t) : Printer string =
  let n = if d.div_64_bit then 64 else 32 in
  let debug = string_of_operandi n d.div_dst ^
              (if d.div_quotient then " /= " else " %= ") ^
              string_of_operandi n d.div_src in
  if (operandi_uses_register d.div_dst "rax" ||
      operandi_uses_register d.div_dst "rcx" ||
      operandi_uses_register d.div_dst "rdx") then (
    unimplemented_die ("string_of_division_operation | " ^ debug)
  ) else if (operandi_uses_register d.div_src "rdx") then (
    unimplemented_die ("string_of_division_operation | " ^ debug)
  ) else (
    let shifted_dst = stack_shifted_operandi 3 d.div_dst in
    let shifted_src = stack_shifted_operandi 3 d.div_src in
    let inp_dst_reg = if d.div_64_bit then "rax" else "eax" in
    let inp_src_reg = if d.div_64_bit then "rcx" else "ecx" in
    let setup_higher_src_reg = if d.div_signed then (
        if d.div_64_bit then "cqo" else "cdq"
      ) else "mov rdx, 0" in
    let rem_reg = if d.div_64_bit then "rdx" else "edx" in
    let out_reg = if d.div_quotient then inp_dst_reg else rem_reg in
    let divop = if d.div_signed then "idiv" else "div" in
    lines [
      " ; " ^ debug;
      " push rdx";
      " push rax";
      " push rcx";
      " mov " ^ inp_dst_reg ^ ", " ^ string_of_operandi n shifted_dst ^ "";
      " mov " ^ inp_src_reg ^ ", " ^ string_of_operandi n shifted_src ^ "";
      " " ^ setup_higher_src_reg;
      " " ^ divop ^ " " ^ inp_src_reg;
      " mov " ^ string_of_operandi n shifted_dst ^ ", " ^ out_reg;
      " pop rcx";
      " pop rax";
      " pop rdx";
    ]
  )

type print_shiftop_t = {
  shift_right: bool;
  shift_signed: bool; (* only applicable for right shift *)
  shift_64_bit: bool;
  shift_rotate: bool;
  shift_dst: operandi;
  shift_amt: operandi;
}

(* XXX This feels horrid. Is there a better thing we could do? *)
let string_of_shift_operation (s:print_shiftop_t) : Printer string =
  let n = if s.shift_64_bit then 64 else 32 in
  let debug = string_of_operandi n s.shift_dst ^ " = " ^ string_of_operandi n s.shift_dst ^
              (if s.shift_rotate then (if s.shift_right then "ror" else "rol")
               else if s.shift_right then (if s.shift_signed then " >>S " else " >>U ")
               else " << ") ^ string_of_operandi n s.shift_amt in
  let shiftop =
    if s.shift_rotate then (
      if s.shift_right then "ror" else "rol"
    ) else if s.shift_right then (
      if s.shift_signed then "sar" else "shr"
    ) else (
      "shl"
    ) in
  if (operandi_uses_register s.shift_dst "rcx") then (
    unimplemented_die ("string_of_shift_operation | " ^ debug)
  ) else if (operandi_uses_register s.shift_amt "rcx") then (
    unimplemented_die ("string_of_shift_operation | " ^ debug)
  ) else (
    let shifted_dst = stack_shifted_operandi 1 s.shift_dst in
    let shifted_shamt = stack_shifted_operandi 1 s.shift_amt in
    let shamt_reg = string_of_regi n (regi_of_string "rcx") in
    lines [
      " ; " ^ debug;
      " push rcx";
      " mov " ^ shamt_reg ^ ", " ^ string_of_operandi n shifted_shamt;
      " " ^ shiftop ^ " " ^ string_of_operandi n shifted_dst ^ ", cl";
      " pop rcx";
    ]
  )

let string_of_ibinop_with_dest_reg (i:ins_t) :
  Pure string
    (requires (Mul32? i \/ Mul64? i))
    (ensures (fun _ -> True)) =
  let n = match I.tag_of_ins i with
    | I.I32_Binop -> 32
    | I.I64_Binop -> 64
  in
  let (op, dst, src) = match i with
    | Mul32 dst src | Mul64 dst src -> ("imul", dst, src)
  in
  let direct_printing = op ^ " " ^ string_of_operandi n dst ^ ", " ^ string_of_operandi n src in
  match dst with
  | OConst _ -> "***constant dst for binop wat***"
  | OReg _ _ -> direct_printing
  | OMemRel _ | OStackRel _ | ONamedGlobal _ ->
    let temp_reg = (
      if not (operandi_uses_register dst "rcx") then "rcx"
      else (
        (* If it uses rcx, no chance it can use rax, so we can use rax as the temp *)
        assert (not (operandi_uses_register dst "rax"));
        "rax"
      )
    ) in
    let shifted_dst = stack_shifted_operandi 1 dst in
    let shifted_src = stack_shifted_operandi 1 src in
    let reg_dst = string_of_regi n (regi_of_string temp_reg) in
    lines [
      " ; " ^ direct_printing;
      " push " ^ temp_reg;
      " mov " ^ reg_dst ^ ", " ^ string_of_operandi n shifted_dst;
      " " ^ op ^ " " ^ reg_dst ^ ", " ^ string_of_operandi n shifted_src;
      " mov " ^ string_of_operandi n shifted_dst ^ ", " ^ reg_dst;
      " pop " ^ temp_reg;
    ]

let _print_ins_I32_Binop : _print_ins_t I.I32_Binop = fun i ->
  let f op dst src = op ^ " " ^ string_of_operandi 32 dst ^ ", " ^ string_of_operandi 32 src in
  print Main (
    match i with
    | Add32  dst src -> f "add" dst src
    | Sub32  dst src -> f "sub" dst src
    | Mul32  dst src -> string_of_ibinop_with_dest_reg i
    | DivS32 dst src ->
      string_of_division_operation ({div_signed=true; div_64_bit=false; div_quotient=true;
                                     div_dst=dst; div_src=src})
    | DivU32 dst src ->
      string_of_division_operation ({div_signed=false; div_64_bit=false; div_quotient=true;
                                     div_dst=dst; div_src=src})
    | RemS32 dst src ->
      string_of_division_operation ({div_signed=true; div_64_bit=false; div_quotient=false;
                                     div_dst=dst; div_src=src})
    | RemU32 dst src ->
      string_of_division_operation ({div_signed=false; div_64_bit=false; div_quotient=false;
                                     div_dst=dst; div_src=src})
    | And32  dst src -> f "and" dst src
    | Or32   dst src -> f "or" dst src
    | Xor32  dst src -> f "xor" dst src
    | Shl32  dst src ->
      string_of_shift_operation ({shift_right=false; shift_signed=false; shift_64_bit=false;
                                  shift_rotate=false; shift_dst=dst; shift_amt=src})
    | ShrS32 dst src ->
      string_of_shift_operation ({shift_right=true; shift_signed=true; shift_64_bit=false;
                                  shift_rotate=false; shift_dst=dst; shift_amt=src})
    | ShrU32 dst src ->
      string_of_shift_operation ({shift_right=true; shift_signed=false; shift_64_bit=false;
                                  shift_rotate=false; shift_dst=dst; shift_amt=src})
    | Rotl32 dst src ->
      string_of_shift_operation ({shift_right=false; shift_signed=false; shift_64_bit=false;
                                  shift_rotate=true; shift_dst=dst; shift_amt=src})
    | Rotr32 dst src ->
      string_of_shift_operation ({shift_right=true; shift_signed=false; shift_64_bit=false;
                                  shift_rotate=true; shift_dst=dst; shift_amt=src})
  )

let _print_ins_I64_Binop : _print_ins_t I.I64_Binop = fun i ->
  let f op dst src = op ^ " " ^ string_of_operandi 64 dst ^ ", " ^ string_of_operandi 64 src in
  print Main (
    match i with
    | Add64  dst src -> f "add" dst src
    | Sub64  dst src -> f "sub" dst src
    | Mul64  dst src -> string_of_ibinop_with_dest_reg i
    | DivS64 dst src ->
      string_of_division_operation ({div_signed=true; div_64_bit=true; div_quotient=true;
                                     div_dst=dst; div_src=src})
    | DivU64 dst src ->
      string_of_division_operation ({div_signed=false; div_64_bit=true; div_quotient=true;
                                     div_dst=dst; div_src=src})
    | RemS64 dst src ->
      string_of_division_operation ({div_signed=true; div_64_bit=true; div_quotient=false;
                                     div_dst=dst; div_src=src})
    | RemU64 dst src ->
      string_of_division_operation ({div_signed=false; div_64_bit=true; div_quotient=false;
                                     div_dst=dst; div_src=src})
    | And64  dst src -> f "and" dst src
    | Or64   dst src -> f "or" dst src
    | Xor64  dst src -> f "xor" dst src
    | Shl64  dst src ->
      string_of_shift_operation ({shift_right=false; shift_signed=false; shift_64_bit=true;
                                  shift_rotate=false; shift_dst=dst; shift_amt=src})
    | ShrS64 dst src ->
      string_of_shift_operation ({shift_right=true; shift_signed=true; shift_64_bit=true;
                                  shift_rotate=false; shift_dst=dst; shift_amt=src})
    | ShrU64 dst src ->
      string_of_shift_operation ({shift_right=true; shift_signed=false; shift_64_bit=true;
                                  shift_rotate=false; shift_dst=dst; shift_amt=src})
    | Rotl64 dst src ->
      string_of_shift_operation ({shift_right=false; shift_signed=false; shift_64_bit=true;
                                  shift_rotate=true; shift_dst=dst; shift_amt=src})
    | Rotr64 dst src ->
      string_of_shift_operation ({shift_right=true; shift_signed=false; shift_64_bit=true;
                                  shift_rotate=true; shift_dst=dst; shift_amt=src})
  )

let print_copy_sign (size:nat{size = 32 \/ size = 64}) (dst:operandf) (src:operandf) : Printer unit =
  let t0 = temporary_xmm 0 in
  let t1 = temporary_xmm 1 in
  (* Load up the arguments into temporaries *)
  prints Main [
    "movdqu " ^ t0 ^ ", " ^ string_of_operandf size dst ^ "\n";
    "movdqu " ^ t1 ^ ", " ^ string_of_operandf size src ^ "\n";
  ];
  (* Perform the actual "copy sign" *)
  prints Main [
    "andps " ^ t1 ^ ", [CONST_NEG" ^ string_of_int size ^ "]\n"; (* get the sign bit *)
    "andps " ^ t0 ^ ", [CONST_ABS" ^ string_of_int size ^ "]\n"; (* clear the sign bit *)
    "orps " ^ t0 ^ ", " ^ t1 ^ "\n"; (* set the sign bit *)
  ];
  (* Store the result *)
  prints Main [
    "movdqu " ^ string_of_operandf size dst ^ ", " ^ t0 ^ "\n";
  ]

let _print_ins_F32_Binop : _print_ins_t I.F32_Binop = fun i ->
  let f op dst src : Printer unit = print Main (
      op ^ " " ^ string_of_operandf 32 dst ^ ", " ^ string_of_operandf 32 src) in
  match i with
  | FAdd32 dst src -> f "addss" dst src
  | FSub32 dst src -> f "subss" dst src
  | FMul32 dst src -> f "mulss" dst src
  | FDiv32 dst src -> f "divss" dst src
  | FMin32 dst src -> f "minss" dst src
  | FMax32 dst src -> f "maxss" dst src
  | FCopySign32 dst src -> print_copy_sign 32 dst src

let _print_ins_F64_Binop : _print_ins_t I.F64_Binop = fun i ->
  let f op dst src : Printer unit = print Main (
      op ^ " " ^ string_of_operandf 64 dst ^ ", " ^ string_of_operandf 64 src) in
  match i with
  | FAdd64 dst src -> f "addsd" dst src
  | FSub64 dst src -> f "subsd" dst src
  | FMul64 dst src -> f "mulsd" dst src
  | FDiv64 dst src -> f "divsd" dst src
  | FMin64 dst src -> f "minsd" dst src
  | FMax64 dst src -> f "maxsd" dst src
  | FCopySign64 dst src -> print_copy_sign 64 dst src

let print_unsigned_conversion (dst:operand) (src:operand) : Printer unit =
  let t0 = temporary_xmm 0 in
  let m (o:operand) : Tot (string & string) = match o with
    | I32 _ -> "movd", "U32"
    | I64 _ -> "movq", "U64"
    | F32 _ -> "movss", "F32"
    | F64 _ -> "movsd", "F64"
  in
  let mov_dst, c_dst = m dst in
  let mov_src, c_src = m src in
  prints Main [mov_src; " "; t0; ", "; string_of_operand src; "\n"];
  prints Main ["call CONVERT_"; c_src; "_TO_"; c_dst; "\n"];
  prints Main [mov_dst; " "; string_of_operand dst; ", "; t0; "\n"]

let _print_ins_Conversion : _print_ins_t I.Conversion = fun i ->
  let f op dst src : Printer unit = print Main (
      op ^ " " ^ string_of_operand dst ^ ", " ^ string_of_operand src) in
  let f_with_mov op dst src : Printer unit = print Main (
      op ^ " " ^ string_of_operand dst ^ ", " ^ string_of_operand src) in
  match i with
  | I32TruncSF32 dst src -> f "cvttss2si" (I32 dst) (F32 src)
  | I32TruncUF32 dst src -> print_unsigned_conversion (I32 dst) (F32 src)
  | I32TruncSF64 dst src -> f "cvttsd2si" (I32 dst) (F64 src)
  | I32TruncUF64 dst src -> print_unsigned_conversion (I32 dst) (F64 src)
  | I64TruncSF32 dst src -> f "cvttss2si" (I64 dst) (F32 src)
  | I64TruncUF32 dst src -> print_unsigned_conversion (I64 dst) (F32 src)
  | I64TruncSF64 dst src -> f "cvttsd2si" (I64 dst) (F64 src)
  | I64TruncUF64 dst src -> print_unsigned_conversion (I64 dst) (F64 src)
  | F32DemoteF64 dst src -> f "cvtsd2ss" (F32 dst) (F64 src)
  | F32ConvertSI32 dst src -> f "cvtsi2ss" (F32 dst) (I32 src)
  | F32ConvertUI32 dst src -> print_unsigned_conversion (F32 dst) (I32 src)
  | F32ConvertSI64 dst src -> f "cvtsi2ss" (F32 dst) (I64 src)
  | F32ConvertUI64 dst src -> print_unsigned_conversion (F32 dst) (I64 src)
  | F64PromoteF32 dst src -> f "cvtss2sd" (F64 dst) (F32 src)
  | F64ConvertSI32 dst src -> f "cvtsi2sd" (F64 dst) (I32 src)
  | F64ConvertUI32 dst src -> print_unsigned_conversion (F64 dst) (I32 src)
  | F64ConvertSI64 dst src -> f "cvtsi2sd" (F64 dst) (I64 src)
  | F64ConvertUI64 dst src -> print_unsigned_conversion (F64 dst) (I64 src)
  | ReinterpretFloat32 dst src -> f (if OReg_f? src then "movd" else "mov") (I32 dst) (F32 src)
  | ReinterpretFloat64 dst src -> f (if OReg_f? src then "movq" else "mov") (I64 dst) (F64 src)
  | ReinterpretInt32 dst src -> f (if OReg_f? dst then "movd" else "mov") (F32 dst) (I32 src)
  | ReinterpretInt64 dst src -> f (if OReg_f? dst then "movq" else "mov") (F64 dst) (I64 src)

let print_ins (i:ins_t) : Printer unit =
  print Main " ";
  (
    match I.tag_of_ins i with
    | I.Misc -> _print_ins_Misc i
    | I.StackOp -> _print_ins_StackOp i
    | I.Mov -> _print_ins_Mov i
    | I.Movzx -> _print_ins_Movzx i
    | I.Movsx -> _print_ins_Movsx i
    | I.FMov -> _print_ins_FMov i
    | I.I32_Unop -> _print_ins_I32_Unop i
    | I.I64_Unop -> _print_ins_I64_Unop i
    | I.F32_Unop -> _print_ins_F32_Unop i
    | I.F64_Unop -> _print_ins_F64_Unop i
    | I.I32_Binop -> _print_ins_I32_Binop i
    | I.I64_Binop -> _print_ins_I64_Binop i
    | I.F32_Binop -> _print_ins_F32_Binop i
    | I.F64_Binop -> _print_ins_F64_Binop i
    | I.Conversion -> _print_ins_Conversion i
  );
  print Main "\n"

let print_inss (is:list ins_t) : Printer unit =
  printer_for_each is print_ins

let string_of_comparator_of_conditional (o1 o2:operand) : Printer string =
  match o1, o2 with
  | I32 o1, I32 o2 -> "cmp"
  | I64 o1, I64 o2 -> "cmp"
  | F32 o1, F32 o2 -> "ucomiss"
  | F64 o1, F64 o2 -> "ucomisd"
  | _ -> ("***INVALID COMPARISON: " ^
          string_of_operand o1 ^ " vs " ^
          string_of_operand o2 ^ "***")

let string_of_conditional_jump_to (cond:ocmp) (trgt:loc) : Printer string =
  let o1, o2 = operands_of_conditional cond in
  let cmp = string_of_comparator_of_conditional o1 o2 in
  "  " ^ cmp ^ " " ^ string_of_operand o1 ^ ", " ^ string_of_operand o2 ^ "\n" ^
  "  " ^ string_of_conditional_jmp cond ^ " " ^ string_of_jump_loc trgt ^ "\n"

let string_of_call (a:aux) (t:target_t) : string =
  match t with
  | CallDirect n ->
    if 0 <= n && n < length a.fns then (
      " call " ^ (index a.fns n).fn_str ^ "\n"
    ) else (
      "*** INVALID FUNCTION CALL FOUND ***"
    )
  | CallIndirect r ->
    " call [CALLTABLE + 8 * " ^ string_of_regi 64 r ^ "]\n"

let print_precode (wasi_enabled:bool) (a:aux) (p:precode) (current_label:loc) : Printer unit =
  match p with
  | FnEntry name next ->
    if 0 <= name && name < length a.fns then (
      print Main (
        "; Start of function " ^ string_of_int name ^ "\n" ^
        (if wasi_enabled && (index a.fns name).fn_str = "_start" then (
            "wasi_module_start"
          ) else if wasi_enabled && (index a.fns name).fn_str = "main" then (
           "wasi_module_main"
         ) else (
           (index a.fns name).fn_str
         )) ^ ":\n"
      );
      print_jump_if_not_fallthrough current_label next
    ) else print Main (
      "*** INVALID FUNCTION NAME FOUND ***"
    )
  | FnExit name ->
    if 0 <= name && name < length a.fns then print Main (
      "; End of function " ^ string_of_int name ^ " " ^ (index a.fns name).fn_str ^ "\n" ^
      "  hlt\n\n"
    ) else print Main (
      "*** INVALID FUNCTION NAME FOUND ***"
    )
  | Ins i next ->
    print_ins i;
    print_jump_if_not_fallthrough current_label next
  | InsList is next ->
    print_inss is;
    print_jump_if_not_fallthrough current_label next
  | Nop next ->
    print_jump_if_not_fallthrough current_label next
  | Cmp cond nextTrue nextFalse ->
    print Main (string_of_conditional_jump_to cond nextTrue);
    print_jump_if_not_fallthrough current_label nextFalse
  | Switch case_table case ->
    print Main (
      " jmp [" ^ string_of_brtable case_table ^ " + 8 * " ^ string_of_regi 64 case ^ "]\n")
  | Call target onreturn ->
    print Main (string_of_call a target);
    print_jump_if_not_fallthrough current_label onreturn
  | HighCall _ _ _ _ ->
    print Main "*** DISALLOWED HIGHCALL ***"
  | Ret next ->
    print Main "  ret\n";
    print_jump_if_not_fallthrough current_label next
  | HighRet _ _ ->
    print Main "*** DISALLOWED HIGHRET ***"

let print_lines #t (f:t -> Printer unit) (l:list t) : Printer unit =
  let f (x:t) : Printer unit = f x; print Main "\n" in
  printer_for_each l f

let enumerate_from #t (init:nat) (l:list t) : list (nat & t) =
  rev (snd (fold_left (fun (i, res) x -> i + 1, ((i <: nat), x) :: res) (init, []) l))

let print_indexed_lines #t (f:nat -> t -> Printer unit) (l:list t) (init:nat) : Printer unit =
  let fn (x:(nat & t)) : Printer unit = f (fst x) (snd x); print Main "\n" in
  printer_for_each (enumerate_from init l) fn

let print_cfg (wasi_enabled:bool) (must_label:loc->bool) (a:aux) (c:cfg) : Printer unit =
  print_indexed_lines (fun i p ->
      print Main (if must_label i then
         (* Make debugging easier by marking this label as internal to the assembly *)
         "STATIC " ^ string_of_jump_loc i ^ "\n" ^
         (* The actual label *)
         string_of_jump_loc i ^ ":"
       else
         "");
      (* The actual code *)
      print_precode wasi_enabled a p i) c 0

let rec repeat #t (v:t) (times:nat) : list t =
  match times with
  | 0 -> []
  | _ -> v :: repeat v (times - 1)

let print_global (i:nat) (g:aux_global) : Printer unit =
  let { gbl_name; gbl_init; gbl_ty; gbl_isMutable; gbl_isImported; gbl_isExported } = g in
  (* TODO: Handle imported/exported *)
  print Main (string_of_global_ident i ^ ":\n");
  print Main (gbl_name ^ ":\n");
  (
    let size = match gbl_ty with | I32_ty | F32_ty -> 4 | I64_ty | F64_ty -> 8 in
    let l : option (list nat8) = match gbl_init with
    | None -> Some (repeat 0 size)
    | Some i ->
      if length i = size then (
        Some i
      ) else (
        None
      )
    in
    match l with
    | None -> print Main "*** Invalid initialization for global ***"
    | Some l ->
      print_lines (fun (v:nat8) -> print Main ("  db " ^ string_of_int v)) l
  )

let print_br_table (br_table_index:nat) (b:aux_br_table) : Printer unit =
  let { br_name; br_targets } = b in
  print Main (string_of_brtable br_table_index ^ ": ; " ^ br_name ^ "\n");
  print_lines (fun tgt -> print Main ("  dq " ^ string_of_jump_loc tgt)) br_targets;
  print Main "\n"

let print_call_table (fn:list aux_fn) (c:aux_call_table) : Printer unit =
  let { call_name; call_init } = c in
  print Main ("; CALL TABLE - " ^ call_name ^ "\n" ^
              "CALLTABLE:\n");
  print_lines (fun (i:option nat) ->
      match i with
      | None -> print Main "  dq internal___explicit_safe_kill"
      | Some v ->
        if 0 <= v && v < length fn
        then print Main ("  dq " ^ (index fn v).fn_str)
        else print Main "*** INVALID FUNCTION NAME ***") call_init

let print_imported_functions (fn:list aux_fn) : Printer unit =
  print_lines (fun fn ->
      print Main ("extern " ^ fn.fn_str))
    (filter (fun fn -> fn.fn_isImported) fn)

(** Sort the memory initializer by base value, and make sure there are no
    overlaps in initialization. *)
let sanitize_mem_initializer (init: list (list nat8 * nat32)) (mem_size: nat) :
  option (list (list nat8 * nat32)) =
  let sorted_init = sortWith (fun (x y:(_ & nat32)) -> snd x - snd y) init in
  let allowed = fold_right (fun ((init, base):(_ & nat32)) allowed ->
      match allowed with
      | None -> None
      | Some allowed -> if base + length init <= allowed then Some base else None)
      sorted_init (Some mem_size) in
  match allowed with
  | None -> None
  | Some _ -> Some sorted_init

let is_nice_ascii_char (n:nat8) : Tot bool =
  (n >= 32 && n <= 38) ||
  (* skip single-quote *)
  (n >= 40 && n <= 91) ||
  (* skip backslash *)
  (n >= 93 && n <= 126)

let nice_char_of_int (n:nat8) : Tot (option string) =
  if is_nice_ascii_char n then (
    assert_norm (n < pow2 21);
    Some (FStar.String.string_of_list [FStar.Char.char_of_int n])
  ) else (
    None
  )

let print_data_initializer (bytes:list nat8) : Printer unit =
  print Main (
    if length bytes = 0 then "" else
      let (initializer, started_ascii_string, comma) =
        fold_right (fun (d:nat8) (initializer, started_ascii_string, comma) ->
            match nice_char_of_int d with
            | None -> (
                let initializer = if started_ascii_string then "'" ^ initializer else initializer in
                string_of_int d ^ (if comma then ", " else "") ^ initializer, false, true)
            | Some c -> (
                let initializer = if started_ascii_string then initializer else
                                  "'" ^ (if comma then ", " else "") ^ initializer in
                c ^ initializer, true, true))
         bytes ("\n", false, false)
      in
      let initializer = if started_ascii_string then "'" ^ initializer else initializer in
      "  db " ^ initializer
  )

let print_memory_initializer_data (init: list (list nat8 * nat32)) (mem_size: nat32) : Printer unit =
  match sanitize_mem_initializer init mem_size with
  | None -> print Main "*** INVALID MEMORY INITIALIZATION ***"
  | Some init ->
    let _ = printer_fold_left (fun (i:nat) ((init, base):(list nat8 & nat32)) ->
        prints Main [
          "STATIC WASM_MEM_INITIALIZER_"; string_of_int i; "\n";
          "WASM_MEM_INITIALIZER_"; string_of_int i; ":\n";
        ];
        print_data_initializer init;
        print Main "\n";
        i + 1
      ) 0 init in
    ()

let print_memory_initializer_function (init: list (list nat8 * nat32)) (mem_size: nat32) : Printer unit =
  match sanitize_mem_initializer init mem_size with
  | None -> print Main "*** INVALID MEMORY INITIALIZATION ***"
  | Some init ->
    print Main "extern memcpy\n";
    let _ = printer_fold_left (fun (i:nat) ((init, base):(list nat8 & nat32)) ->
        prints Main [
          "  lea rdi, ["; memory_name; " + "; string_of_int base ;"]\n"; (* dst *)
          "  lea rsi, [WASM_MEM_INITIALIZER_"; string_of_int i; "]\n"; (* src *)
          "  mov rdx, " ^ string_of_int (length init); "\n"; (* count *)
          "  call memcpy\n";
        ];
        i + 1
      ) 0 init in
    ()

let print_memory_sections (m:aux_memory) (mem_pages: nat32) : Printer unit =
  let { mem_name; mem_init; mem_min; mem_max; mem_isImported; mem_isExported } = m in
  let mem_size = mem_pages `op_Multiply` 65536 in
  let mem_pages_s = if mem_pages >= mem_min then (
      match mem_max with
      | None -> string_of_int mem_min
      | Some(v) -> if mem_pages = v then string_of_int mem_min else
          "*** MAX MEM PAGES DOES NOT MATCH ***"
    ) else (
      "*** TOO FEW MEM PAGES ***"
    )
  in
  if mem_size < pow2_32 then (
    prints Main [
      "SECTION .mempages NOEXEC WRITE align=16\n";
      "MEM_PAGES: dq "; mem_pages_s; "\n";
      "\n";
    ];
    prints Main [
      "SECTION .memory NOEXEC WRITE NOBITS align=16\n";
      memory_name; ": ; "; mem_name; "\n";
      "  resb "; string_of_int mem_size; "\n";
      "\n";
    ];
    prints Main [
      "SECTION .memoryinit NOEXEC NOWRITE align=16\n";
    ];
    print_memory_initializer_data mem_init mem_size;
    prints Main [
      "\n";
    ];
    prints Main [
      "SECTION .text EXEC NOWRITE\n";
      "STATIC wasm_initialize_module_memory\n";
      "wasm_initialize_module_memory:\n";
    ];
    print_memory_initializer_function mem_init mem_size;
    prints Main [
      "  ret\n";
      "\n";
    ]
  ) else (
    print Main ("***IMPOSSIBLY LARGE MEMORY SIZE: " ^ string_of_int mem_size ^ "***")
  )

let wasi_initializer : string =
  "\n" ^
  "SECTION .text EXEC NOWRITE\n" ^
  "extern wasi_initialize_context\n" ^
  "GLOBAL main\n" ^
  "main:\n" ^
  "  push rbp     ; we should always come in aligned to rsp & 16 == 0\n" ^
  "  mov rbp, rsp ; this rbp stuff is just to make sure we maintain alignment for our calls\n" ^
  "  call wasm_initialize_module_memory\n" ^
  "  lea rdi, [MEMORY]\n" ^
  "  lea rsi, [MEM_PAGES]\n" ^
  "  call wasi_initialize_context\n" ^
  "  call wasi_module_start\n" ^
  "  leave\n" ^
  "  ret\n"

let explicit_safe_kill : string =
  "\n" ^
  "SECTION .text EXEC NOWRITE\n" ^
  "internal___explicit_safe_kill:\n" ^
  "  ud2\n\n"

let print_floating_point_constants () : Printer unit =
  print_floating_constant_dds "CONST_NEG32" [0x80000000; 0x80000000; 0x80000000; 0x80000000];
  print_floating_constant_dqs "CONST_NEG64" [0x8000000000000000; 0x8000000000000000];
  print_floating_constant_dds "CONST_ABS32" [0x7fffffff; 0x7fffffff; 0x7fffffff; 0x7fffffff];
  print_floating_constant_dqs "CONST_ABS64" [0x7fffffffffffffff; 0x7fffffffffffffff];
  ()

let print_module (mod:module_) (wasi_enabled:bool) : Printer unit =
  let must_label = should_loc_be_labeled mod in
  let { module_aux ; module_cfg } = mod in
  let { fns; globals; memory; br_tables; call_table; mem_pages } = module_aux in
  print Constants "SECTION .constants NOEXEC NOWRITE align=16\n";
  print_floating_point_constants ();
  print AuxRoutines "SECTION .auxroutines EXEC NOWRITE\n";
  print AuxRWData "SECTION .auxrwdata NOEXEC WRITE align=16\n";
  print_aux_temporaries ();
  print_unsigned_conversion_routines ();
  prints Main [
    "BITS 64\n";
    "DEFAULT REL ; allow PIE\n\n";
    "SECTION .global NOEXEC WRITE align=16\n" ]; print_indexed_lines print_global globals 0; prints Main [ "\n";
    "SECTION .text EXEC NOWRITE\n" ]; print_indexed_lines print_br_table br_tables 0; prints Main [ "\n";
    "SECTION .text EXEC NOWRITE\n" ]; print_call_table fns call_table; prints Main ["\n";
    "; Imported function declarations\n"]; print_imported_functions fns; prints Main ["\n";
    "SECTION .text EXEC NOWRITE\n" ]; print_cfg wasi_enabled must_label module_aux module_cfg;
  print_memory_sections memory mem_pages;
  print Main (if wasi_enabled then wasi_initializer else "");
  print Main explicit_safe_kill

(** Produce a printable assembly listing for the module. The output is
    produced as a list that must be joined at the point of actually
    printing (with no additional newlines/whitespace necessary). This
    is done purely due to performance reasons. See
    [print_module_as_string] for a potential usage. *)
let print_module_as_list (mod:module_) (wasi_enabled:bool) : list string =
  let f = serialize_to_list (fun () -> print_module mod wasi_enabled) in
  f Constants @ f Main @ f AuxRoutines @ f AuxRWData

(** A folded-down string version of [print_module]. Not to be used
    except for debugging (due to performance reasons). See
    [Compile.All.print_all] for a convenient and fast printer
    instead. *)
let print_module_as_string (mod:module_) (wasi_enabled:bool) : string =
  fold_right (fun x r -> x ^ r) (print_module_as_list mod wasi_enabled) ""
