module Compiler.Phase.Simplify

open FStar.List.Tot

open Common.Err
open Common.Print
open Semantics.Common.FunctionInfo

open Wasm.Source
open Wasm.Types
open Wasm.I32

open Words_s

module Values = Wasm.Values
module Memory = Wasm.Memory
module Source = Wasm.Source
module I32 = Wasm.I32
module I64 = Wasm.I64
module L = Wasm.Lib.List

module IntOp = Wasm.Ast.IntOp
module FloatOp = Wasm.Ast.FloatOp

module I32Op = Wasm.Ast.IntOp
module I64Op = Wasm.Ast.IntOp
module F32Op = Wasm.Ast.FloatOp
module F64Op = Wasm.Ast.FloatOp

module Sem1 = Wasm.Ast
module Sem2 = Wasm_simple.Semantics

val errmap: ('a -> Err_ 'b) -> list 'a -> Err_ (list 'b)
let rec errmap f la =
  match la with
  | [] -> []
  | a :: la ->
    let b = f a in
    let lb = errmap f la in
    (b :: lb)

let unwrap (v:Values.value): Err_ Sem2.literal =
  match v with
  | Values.I32 i32 -> Sem2.N32 (I32.to_int_u i32)
  | Values.I64 i64 -> Sem2.N64 (I64.to_int_u i64)
  | Values.F32 f32 -> Sem2.F32 f32
  | Values.F64 f64 -> Sem2.F64 f64

let unwrapv (v:Sem1.var): nat32 = I32.to_int_u v.it

let convert_type (ty:value_type): Sem2.value_type =
  match ty with
  | I32Type -> Sem2.I32Ty
  | I64Type -> Sem2.I64Ty
  | F32Type -> Sem2.F32Ty
  | F64Type -> Sem2.F64Ty

let convert_func_type (ty:Sem1.type_): Sem2.func_type =
  let FuncType (arg, res) = ty.it in
  (map convert_type arg, map convert_type res)

let convert_loadop (op:Sem1.loadop): Err_ Sem2.loadop =
  let lty = convert_type op.Sem1.ty in
  let loffset = I32.to_int_u op.Sem1.offset in
  match op.Sem1.sz with
  | None ->
    ({Sem2.lty = lty; Sem2.loffset = loffset; Sem2.lsz = size op.Sem1.ty; Sem2.lsigned = true})
  | Some (sz, ext) ->
    ({Sem2.lty = lty; Sem2.loffset = loffset; Sem2.lsz = Memory.packed_size sz; Sem2.lsigned = Memory.SX? ext})

let convert_storeop (op:Sem1.storeop): Err_ Sem2.storeop =
  let sty = convert_type op.Sem1.ty in
  let soffset = I32.to_int_u op.Sem1.offset in
  match op.Sem1.sz with
  | None ->
    ({Sem2.sty = sty; Sem2.soffset = soffset; Sem2.ssz = size op.Sem1.ty})
  | Some sz ->
    ({Sem2.sty = sty; Sem2.soffset = soffset; Sem2.ssz = Memory.packed_size sz})

type context = {
  m2: Sem2.module_;
  f1: Sem1.func';
  targets: list bool;
  local_types: list Sem2.value_type;
  stack_types: list Sem2.value_type;
  c: Sem2.codes;
}

let rec lemma_splitAt_fst_length (n:nat) (l:list 'a{length l >= n})
  : Lemma (let l1, _ = splitAt n l in
           length l1 = n) =
  if n = 0 then () else (
    match l with
    | x :: l' -> lemma_splitAt_fst_length (n - 1) l'
  )

let prep_code instrs ctx = {ctx with c = instrs @ ctx.c}
let app_code instrs ctx = ({ctx with c = ctx.c @ instrs})
let set_code instrs ctx = {ctx with c = instrs}
let push_tys ty ctx = {ctx with stack_types = ty @ ctx.stack_types}
let pop_tys (n:nat) (s:string) (ctx:context): Err_ (ts:list Sem2.value_type{length ts == n} * context) =
  if length ctx.stack_types < n
  then fail_with ("compile_code: " ^ s ^ ": pop_tys")
  else (
    let l1, l2 = splitAt n ctx.stack_types in
    lemma_splitAt_fst_length n ctx.stack_types;
    (l1, ({ctx with stack_types = l2}))
  )
let push_tgt b ctx = {ctx with targets = b :: ctx.targets}

let arith op n ty ctx1 : Err_ _ =
  let res = pop_tys n "arith" ctx1 in
  let ctx2 = push_tys [ty] (snd res) in
  app_code [Sem2.Ins op] ctx2

val compile_code: instr1:Sem1.instr -> context -> Err_ context
val compile_codes: instrs1:list Sem1.instr -> context -> Err_ context
let rec compile_code instr1 ctx1 =
  let instr1 = instr1.it in
  let m2 = ctx1.m2 in
  match instr1 with
  | Sem1.Unreachable ->
    app_code [Sem2.Ins Sem2.Unreachable] ctx1
  | Sem1.Nop ->
    ctx1
  | Sem1.Drop ->
    let res = pop_tys 1 "Drop" ctx1 in
    let tys, ctx2 = res in
    let ty = hd tys in
    if ty = Sem2.I32Ty || ty = Sem2.I64Ty
    then app_code [Sem2.Ins Sem2.DropI] ctx2
    else app_code [Sem2.Ins Sem2.DropF] ctx2
  | Sem1.Select ->
    let res = pop_tys 3 "Select" ctx1 in
    let tys, ctx2 = res in
    let ty = index tys 1 in
    let ctx3 = push_tys [ty] ctx2 in
    if ty = Sem2.I32Ty || ty = Sem2.I64Ty then (
      app_code [Sem2.Ins Sem2.SelectI] ctx3
    ) else (
      app_code [Sem2.Ins Sem2.SelectF] ctx3
    )
  | Sem1.Block (ts, ins1) ->
    let ts' = map convert_type ts in
    let ctx2 = push_tgt false (set_code [] ctx1) in
    let ctx3 = compile_codes ins1 ctx2 in
    let ctx4 = push_tys ts' ctx1 in
    app_code [Sem2.Block ctx3.c ts'] ctx4
  | Sem1.Loop (ts, ins1) ->
    let ts' = map convert_type ts in
    let ctx2 = push_tgt true (set_code [] ctx1) in
    let ctx3 = compile_codes ins1 ctx2 in
    let ctx4 = push_tys ts' ctx1 in
    app_code [Sem2.Block ctx3.c ts'] ctx4
  | Sem1.If (ts, ctrue1, cfalse1) ->
    let ts' = map convert_type ts in
    let ctx2 = push_tgt false (set_code [] ctx1) in
    let ctx_t = compile_codes ctrue1 ctx2 in
    let ctx_f = compile_codes cfalse1 ctx2 in
    let ctx3 = push_tys ts' ctx1 in
    app_code [Sem2.IfElse ctx_t.c ctx_f.c ts'] ctx3
  | Sem1.Br x ->
    let n:nat = I32.to_int_u x.it in
    (match nth ctx1.targets n with
     | None ->
       fail_with "compile_code: Br bad branch target"
     | Some true ->
       app_code [Sem2.Continue n Sem2.Always] ctx1
     | Some false ->
       app_code [Sem2.Break n Sem2.Always] ctx1
    )
  | Sem1.BrIf x ->
    let n:nat = I32.to_int_u x.it in
    (match nth ctx1.targets n with
     | None ->
       fail_with "compile_code: BrIf bad branch target"
     | Some true ->
       app_code [Sem2.Continue n Sem2.IsNonZero] ctx1
     | Some false ->
       app_code [Sem2.Break n Sem2.IsNonZero] ctx1
    )
  | Sem1.BrTable (xs, x) ->
    let f i : Err_ _ =
      let n = I32.to_int_u i.it in
      match nth ctx1.targets n with
      | None ->
        fail_with "compile_code: BrTable bad branch target"
      | Some b ->
        (n, b)
    in
    let ns = errmap f xs in
    let n = f x in
    let br_tbl = {Sem2.cases = ns; Sem2.def = n} in
    app_code [Sem2.BrTable br_tbl] ctx1
  | Sem1.Return ->
    // Adhere to semantics
    let {Sem1.ftype; Sem1.flocals; Sem1.body} = ctx1.f1 in
    let n:nat = unwrapv ftype in
    (match nth m2.Sem2.types n with
     | None ->
       fail_with "compile_code: Return bad ftype"
     | Some (_, rettys) ->
       let res = pop_tys (length rettys) "Return" ctx1 in
       // TODO: possibly keep track of type
       // Not strictly necessary but might be useful
       // Same for calls and stuff
       app_code [Sem2.Return] (snd res)
    )
  | Sem1.Call v ->
    // NB: Imports come before regular funcs
    let v' = unwrapv v in
    let l = length m2.Sem2.fimports in
    if v' < l then (
      // Imported
      let f = index m2.Sem2.fimports v' in
      match nth m2.Sem2.types f.Sem2.idesc with
      | None -> fail_with "compile_code: Call bad imp ftype"
      | Some (argtys, rettys) ->
        let res = pop_tys (length argtys) "CallImp" ctx1 in
        let ctx2 = push_tys rettys (snd res) in
        app_code [Sem2.ExternCall v'] ctx2
    ) else (
      // Not imported
      match nth m2.Sem2.funcs (v' - l) with
      | None -> fail_with "compile_code: Call bad fidx"
      | Some f ->
        let f' = f.Sem2.ftype in
        match nth m2.Sem2.types f' with
        | None -> fail_with "compile_code: Call bad ftype"
        | Some (argtys, rettys) ->
          let res = pop_tys (length argtys) "Call" ctx1 in
          let ctx2 = push_tys rettys (snd res) in
          app_code [Sem2.Call (v' - l)] ctx2
    )
  | Sem1.CallIndirect v ->
    let v' = unwrapv v in
    (match nth m2.Sem2.types v' with
     | None -> fail_with "compile_code: CallIndirect bad ftype"
     | Some (argtys, rettys) ->
       let res = pop_tys (length argtys) "CallImp" ctx1 in
       let ctx2 = push_tys rettys (snd res) in
       app_code [Sem2.CallIndirect v'] ctx2
    )
  | Sem1.LocalGet v ->
    let v' = unwrapv v in
    (match nth ctx1.local_types v' with
     | None -> fail_with "compile_code: LocalGet bad index"
     | Some ty ->
       let ctx2 = push_tys [ty] ctx1 in
       app_code [Sem2.Ins (Sem2.LocalGet v')] ctx2
    )
  | Sem1.LocalSet v ->
    let v' = unwrapv v in
    let res = pop_tys 1 "LocalSet" ctx1 in
    app_code [Sem2.Ins (Sem2.LocalSet v')] (snd res)
  | Sem1.LocalTee v ->
    let v' = unwrapv v in
    app_code [Sem2.Ins (Sem2.LocalTee v')] ctx1
  | Sem1.GlobalGet v ->
    (* NB: See remarks on call *)
    let v' = unwrapv v in
    let l = length m2.Sem2.gimports in
    if v' < l then (
      let gi = index m2.Sem2.gimports v' in
      let ty = fst gi.Sem2.idesc in
      let ctx2 = push_tys [ty] ctx1 in
      app_code [Sem2.Ins (Sem2.ExternGlobalGet v')] ctx2
    ) else (
      match nth m2.Sem2.globals (v' - l) with
      | None -> fail_with "compile_code: GlobalGet bad index"
      | Some g ->
        let ty = fst g.Sem2.gtype in
        let ctx2 = push_tys [ty] ctx1 in
        app_code [Sem2.Ins (Sem2.GlobalGet (v' - l))] ctx2
    )
  | Sem1.GlobalSet v ->
    (* NB: See remarks on call *)
    let v' = unwrapv v in
    let l = length m2.Sem2.gimports in
    let res = pop_tys 1 "GlobalSet" ctx1 in
    if v' < l then (
      app_code [Sem2.Ins (Sem2.ExternGlobalSet v')] (snd res)
    ) else (
      app_code [Sem2.Ins (Sem2.GlobalSet (v' - l))] (snd res)
    )
  | Sem1.Load loadop ->
    let op = convert_loadop loadop in
    let res = pop_tys 1 "Load" ctx1 in
    let ctx2 = push_tys [op.Sem2.lty] (snd res) in
    app_code [Sem2.Ins (Sem2.Load op)] ctx2
  | Sem1.Store storeop ->
    let op = convert_storeop storeop in
    let res = pop_tys 2 "Store" ctx1 in
    app_code [Sem2.Ins (Sem2.Store op)] (snd res)
  | Sem1.MemorySize ->
    let ctx2 = push_tys [Sem2.I32Ty] ctx1 in
    app_code [Sem2.Ins Sem2.MemorySize] ctx2
  | Sem1.MemoryGrow ->
    let res = pop_tys 1 "MemoryGrow" ctx1 in
    let ctx2 = push_tys [Sem2.I32Ty] (snd res) in
    app_code [Sem2.Ins Sem2.MemoryGrow] ctx2
  | Sem1.Const v ->
    let v' = unwrap v.it in
    let ty =
      match v' with
      | Sem2.N32 n -> Sem2.I32Ty
      | Sem2.N64 n -> Sem2.I64Ty
      | Sem2.F32 f -> Sem2.F32Ty
      | Sem2.F64 f -> Sem2.F64Ty
    in
    let ctx2 = push_tys [ty] ctx1 in
    app_code [Sem2.Ins (Sem2.Const v')] ctx2
  | Sem1.Test op ->
    (match op with
     | Values.I32 I32Op.Eqz -> arith Sem2.I32Eqz 1 Sem2.I32Ty ctx1
     | Values.I64 I64Op.Eqz -> arith Sem2.I64Eqz 1 Sem2.I32Ty ctx1
     | _ -> fail_with "compile_code: Test unsupported op"
    )
  | Sem1.Compare relop ->
    (match relop with
     | Values.I32 op ->
       (match op with
        | I32Op.Eq  -> arith Sem2.I32Eq  2 Sem2.I32Ty ctx1
        | I32Op.Ne  -> arith Sem2.I32Ne  2 Sem2.I32Ty ctx1
        | I32Op.LtS -> arith Sem2.I32LtS 2 Sem2.I32Ty ctx1
        | I32Op.LtU -> arith Sem2.I32LtU 2 Sem2.I32Ty ctx1
        | I32Op.GtS -> arith Sem2.I32GtS 2 Sem2.I32Ty ctx1
        | I32Op.GtU -> arith Sem2.I32GtU 2 Sem2.I32Ty ctx1
        | I32Op.LeS -> arith Sem2.I32LeS 2 Sem2.I32Ty ctx1
        | I32Op.LeU -> arith Sem2.I32LeU 2 Sem2.I32Ty ctx1
        | I32Op.GeS -> arith Sem2.I32GeS 2 Sem2.I32Ty ctx1
        | I32Op.GeU -> arith Sem2.I32GeU 2 Sem2.I32Ty ctx1
       )
     | Values.I64 op ->
       (match op with
        | I64Op.Eq  -> arith Sem2.I64Eq  2 Sem2.I32Ty ctx1
        | I64Op.Ne  -> arith Sem2.I64Ne  2 Sem2.I32Ty ctx1
        | I64Op.LtS -> arith Sem2.I64LtS 2 Sem2.I32Ty ctx1
        | I64Op.LtU -> arith Sem2.I64LtU 2 Sem2.I32Ty ctx1
        | I64Op.GtS -> arith Sem2.I64GtS 2 Sem2.I32Ty ctx1
        | I64Op.GtU -> arith Sem2.I64GtU 2 Sem2.I32Ty ctx1
        | I64Op.LeS -> arith Sem2.I64LeS 2 Sem2.I32Ty ctx1
        | I64Op.LeU -> arith Sem2.I64LeU 2 Sem2.I32Ty ctx1
        | I64Op.GeS -> arith Sem2.I64GeS 2 Sem2.I32Ty ctx1
        | I64Op.GeU -> arith Sem2.I64GeU 2 Sem2.I32Ty ctx1
       )
     | Values.F32 op ->
       (match op with
        | F32Op.Eq -> arith Sem2.F32Eq 2 Sem2.I32Ty ctx1
        | F32Op.Ne -> arith Sem2.F32Ne 2 Sem2.I32Ty ctx1
        | F32Op.Lt -> arith Sem2.F32Lt 2 Sem2.I32Ty ctx1
        | F32Op.Gt -> arith Sem2.F32Gt 2 Sem2.I32Ty ctx1
        | F32Op.Le -> arith Sem2.F32Le 2 Sem2.I32Ty ctx1
        | F32Op.Ge -> arith Sem2.F32Ge 2 Sem2.I32Ty ctx1
       )
     | Values.F64 op ->
       (match op with
        | F64Op.Eq -> arith Sem2.F64Eq 2 Sem2.I32Ty ctx1
        | F64Op.Ne -> arith Sem2.F64Ne 2 Sem2.I32Ty ctx1
        | F64Op.Lt -> arith Sem2.F64Lt 2 Sem2.I32Ty ctx1
        | F64Op.Gt -> arith Sem2.F64Gt 2 Sem2.I32Ty ctx1
        | F64Op.Le -> arith Sem2.F64Le 2 Sem2.I32Ty ctx1
        | F64Op.Ge -> arith Sem2.F64Ge 2 Sem2.I32Ty ctx1
       )
    )
  | Sem1.Unary unop ->
    (match unop with
     | Values.I32 op ->
       (match op with
        | I32Op.Clz    -> arith Sem2.I32Clz    1 Sem2.I32Ty ctx1
        | I32Op.Ctz    -> arith Sem2.I32Ctz    1 Sem2.I32Ty ctx1
        | I32Op.Popcnt -> arith Sem2.I32Popcnt 1 Sem2.I32Ty ctx1
       )
     | Values.I64 op ->
       (match op with
        | I64Op.Clz    -> arith Sem2.I64Clz    1 Sem2.I32Ty ctx1
        | I64Op.Ctz    -> arith Sem2.I64Ctz    1 Sem2.I32Ty ctx1
        | I64Op.Popcnt -> arith Sem2.I64Popcnt 1 Sem2.I32Ty ctx1
       )
     | Values.F32 op ->
       (match op with
        | F32Op.Neg     -> arith Sem2.F32Neg     1 Sem2.F32Ty ctx1
        | F32Op.Abs     -> arith Sem2.F32Abs     1 Sem2.F32Ty ctx1
        | F32Op.Ceil    -> arith Sem2.F32Ceil    1 Sem2.F32Ty ctx1
        | F32Op.Floor   -> arith Sem2.F32Floor   1 Sem2.F32Ty ctx1
        | F32Op.Trunc   -> arith Sem2.F32Trunc   1 Sem2.F32Ty ctx1
        | F32Op.Nearest -> arith Sem2.F32Nearest 1 Sem2.F32Ty ctx1
        | F32Op.Sqrt    -> arith Sem2.F32Sqrt    1 Sem2.F32Ty ctx1
       )
     | Values.F64 op ->
       (match op with
        | F64Op.Neg     -> arith Sem2.F64Neg     1 Sem2.F64Ty ctx1
        | F64Op.Abs     -> arith Sem2.F64Abs     1 Sem2.F64Ty ctx1
        | F64Op.Ceil    -> arith Sem2.F64Ceil    1 Sem2.F64Ty ctx1
        | F64Op.Floor   -> arith Sem2.F64Floor   1 Sem2.F64Ty ctx1
        | F64Op.Trunc   -> arith Sem2.F64Trunc   1 Sem2.F64Ty ctx1
        | F64Op.Nearest -> arith Sem2.F64Nearest 1 Sem2.F64Ty ctx1
        | F64Op.Sqrt    -> arith Sem2.F64Sqrt    1 Sem2.F64Ty ctx1
       )
    )
  | Sem1.Binary binop ->
    (match binop with
     | Values.I32 op ->
       (match op with
        | I32Op.Add  -> arith Sem2.I32Add  2 Sem2.I32Ty ctx1
        | I32Op.Sub  -> arith Sem2.I32Sub  2 Sem2.I32Ty ctx1
        | I32Op.Mul  -> arith Sem2.I32Mul  2 Sem2.I32Ty ctx1
        | I32Op.DivS -> arith Sem2.I32DivS 2 Sem2.I32Ty ctx1
        | I32Op.DivU -> arith Sem2.I32DivU 2 Sem2.I32Ty ctx1
        | I32Op.RemS -> arith Sem2.I32RemS 2 Sem2.I32Ty ctx1
        | I32Op.RemU -> arith Sem2.I32RemU 2 Sem2.I32Ty ctx1
        | I32Op.And  -> arith Sem2.I32And  2 Sem2.I32Ty ctx1
        | I32Op.Or   -> arith Sem2.I32Or   2 Sem2.I32Ty ctx1
        | I32Op.Xor  -> arith Sem2.I32Xor  2 Sem2.I32Ty ctx1
        | I32Op.Shl  -> arith Sem2.I32Shl  2 Sem2.I32Ty ctx1
        | I32Op.ShrS -> arith Sem2.I32ShrS 2 Sem2.I32Ty ctx1
        | I32Op.ShrU -> arith Sem2.I32ShrU 2 Sem2.I32Ty ctx1
        | I32Op.Rotl -> arith Sem2.I32Rotl 2 Sem2.I32Ty ctx1
        | I32Op.Rotr -> arith Sem2.I32Rotr 2 Sem2.I32Ty ctx1
       )
     | Values.I64 op ->
       (match op with
        | I64Op.Add  -> arith Sem2.I64Add  2 Sem2.I64Ty ctx1
        | I64Op.Sub  -> arith Sem2.I64Sub  2 Sem2.I64Ty ctx1
        | I64Op.Mul  -> arith Sem2.I64Mul  2 Sem2.I64Ty ctx1
        | I64Op.DivS -> arith Sem2.I64DivS 2 Sem2.I64Ty ctx1
        | I64Op.DivU -> arith Sem2.I64DivU 2 Sem2.I64Ty ctx1
        | I64Op.RemS -> arith Sem2.I64RemS 2 Sem2.I64Ty ctx1
        | I64Op.RemU -> arith Sem2.I64RemU 2 Sem2.I64Ty ctx1
        | I64Op.And  -> arith Sem2.I64And  2 Sem2.I64Ty ctx1
        | I64Op.Or   -> arith Sem2.I64Or   2 Sem2.I64Ty ctx1
        | I64Op.Xor  -> arith Sem2.I64Xor  2 Sem2.I64Ty ctx1
        | I64Op.Shl  -> arith Sem2.I64Shl  2 Sem2.I64Ty ctx1
        | I64Op.ShrS -> arith Sem2.I64ShrS 2 Sem2.I64Ty ctx1
        | I64Op.ShrU -> arith Sem2.I64ShrU 2 Sem2.I64Ty ctx1
        | I64Op.Rotl -> arith Sem2.I64Rotl 2 Sem2.I64Ty ctx1
        | I64Op.Rotr -> arith Sem2.I64Rotr 2 Sem2.I64Ty ctx1
       )
     | Values.F32 op ->
       (match op with
        | F32Op.Add      -> arith Sem2.F32Add      2 Sem2.F32Ty ctx1
        | F32Op.Sub      -> arith Sem2.F32Sub      2 Sem2.F32Ty ctx1
        | F32Op.Mul      -> arith Sem2.F32Mul      2 Sem2.F32Ty ctx1
        | F32Op.Div      -> arith Sem2.F32Div      2 Sem2.F32Ty ctx1
        | F32Op.Min      -> arith Sem2.F32Min      2 Sem2.F32Ty ctx1
        | F32Op.Max      -> arith Sem2.F32Max      2 Sem2.F32Ty ctx1
        | F32Op.CopySign -> arith Sem2.F32CopySign 2 Sem2.F32Ty ctx1
       )
     | Values.F64 op ->
       (match op with
        | F64Op.Add      -> arith Sem2.F64Add      2 Sem2.F64Ty ctx1
        | F64Op.Sub      -> arith Sem2.F64Sub      2 Sem2.F64Ty ctx1
        | F64Op.Mul      -> arith Sem2.F64Mul      2 Sem2.F64Ty ctx1
        | F64Op.Div      -> arith Sem2.F64Div      2 Sem2.F64Ty ctx1
        | F64Op.Min      -> arith Sem2.F64Min      2 Sem2.F64Ty ctx1
        | F64Op.Max      -> arith Sem2.F64Max      2 Sem2.F64Ty ctx1
        | F64Op.CopySign -> arith Sem2.F64CopySign 2 Sem2.F64Ty ctx1
       )
    )
  | Sem1.Convert cvtop ->
    (match cvtop with
     | Values.I32 op ->
       (match op with
        | I32Op.WrapI64          -> arith Sem2.I32WrapI64          1 Sem2.I32Ty ctx1
        | I32Op.TruncSF32        -> arith Sem2.I32TruncSF32        1 Sem2.I32Ty ctx1
        | I32Op.TruncUF32        -> arith Sem2.I32TruncUF32        1 Sem2.I32Ty ctx1
        | I32Op.TruncSF64        -> arith Sem2.I32TruncSF64        1 Sem2.I32Ty ctx1
        | I32Op.TruncUF64        -> arith Sem2.I32TruncUF64        1 Sem2.I32Ty ctx1
        | I32Op.ReinterpretFloat -> arith Sem2.I32ReinterpretFloat 1 Sem2.I32Ty ctx1
        | _ -> fail_with "compile_code: I32 convert unsupported op"
       )
     | Values.I64 op ->
       (match op with
        | I64Op.ExtendSI32       -> arith Sem2.I64ExtendSI32       1 Sem2.I64Ty ctx1
        | I64Op.ExtendUI32       -> arith Sem2.I64ExtendUI32       1 Sem2.I64Ty ctx1
        | I64Op.TruncSF32        -> arith Sem2.I64TruncSF32        1 Sem2.I64Ty ctx1
        | I64Op.TruncUF32        -> arith Sem2.I64TruncUF32        1 Sem2.I64Ty ctx1
        | I64Op.TruncSF64        -> arith Sem2.I64TruncSF64        1 Sem2.I64Ty ctx1
        | I64Op.TruncUF64        -> arith Sem2.I64TruncUF64        1 Sem2.I64Ty ctx1
        | I64Op.ReinterpretFloat -> arith Sem2.I64ReinterpretFloat 1 Sem2.I64Ty ctx1
        | _ -> fail_with "compile_code: I64 convert unsupported op"
       )
     | Values.F32 op ->
       (match op with
        | F32Op.DemoteF64      -> arith Sem2.F32DemoteF64      1 Sem2.F32Ty ctx1
        | F32Op.ConvertSI32    -> arith Sem2.F32ConvertSI32    1 Sem2.F32Ty ctx1
        | F32Op.ConvertUI32    -> arith Sem2.F32ConvertUI32    1 Sem2.F32Ty ctx1
        | F32Op.ConvertSI64    -> arith Sem2.F32ConvertSI64    1 Sem2.F32Ty ctx1
        | F32Op.ConvertUI64    -> arith Sem2.F32ConvertUI64    1 Sem2.F32Ty ctx1
        | F32Op.ReinterpretInt -> arith Sem2.F32ReinterpretInt 1 Sem2.F32Ty ctx1
        | _ -> fail_with "compile_code: F32 convert unsupported op"
       )
     | Values.F64 op ->
       (match op with
        | F64Op.PromoteF32     -> arith Sem2.F64PromoteF32     1 Sem2.F64Ty ctx1
        | F64Op.ConvertSI32    -> arith Sem2.F64ConvertSI32    1 Sem2.F64Ty ctx1
        | F64Op.ConvertUI32    -> arith Sem2.F64ConvertUI32    1 Sem2.F64Ty ctx1
        | F64Op.ConvertSI64    -> arith Sem2.F64ConvertSI64    1 Sem2.F64Ty ctx1
        | F64Op.ConvertUI64    -> arith Sem2.F64ConvertUI64    1 Sem2.F64Ty ctx1
        | F64Op.ReinterpretInt -> arith Sem2.F64ReinterpretInt 1 Sem2.F64Ty ctx1
        | _ -> fail_with "compile_code: F64 convert unsupported op"
       )
    )

and compile_codes instrs1 ctx1 =
    match instrs1 with
    | [] ->
      ctx1
    | i1 :: instrs1 ->
      let ctx2 = compile_code i1 ctx1 in
      // Kill stack/processing on unreachable/return
      if Sem1.Unreachable? i1.it || Sem1.Return? i1.it then (
        ctx2
      ) else (
        compile_codes instrs1 ctx2
      )

val eval_const: Sem2.module_ -> Sem1.const -> Err_ Sem2.literal
let eval_const m2 c1 =
  let c1 = c1.it in
  if length c1 <> 1 then fail_with "eval_const: const too many instructions" else (
    match (hd c1).it with
    | Sem1.Const v ->
      unwrap v.it
    | Sem1.GlobalGet x ->
      (match nth m2.Sem2.globals (unwrapv x) with
       | Some g ->
         g.Sem2.value
       | _ ->
         fail_with "eval_const: bad global"
      )
    | _ ->
      fail_with "eval_const: Unsupported instruction"
  )

val translate_gbl_ty: global_type -> Tot Sem2.global_type
let translate_gbl_ty ty =
  let GlobalType (vty, mut) = ty in
  let vty' = convert_type vty in
  let mut = Mutable? mut in
  vty', mut

val translate_gbl: Sem2.module_ -> Sem1.global -> Err_ Sem2.global
let translate_gbl m2 gbl1 =
  let gbl1 = gbl1.it in
  let c2 = eval_const m2 gbl1.Sem1.value in
  ({Sem2.gtype = translate_gbl_ty gbl1.Sem1.gtype; Sem2.value = c2})

val translate_tbl_ty: table_type -> Tot Sem2.table_type
let translate_tbl_ty ty =
  let TableType (lim, _) = ty in
  let ({min; max}) = lim in
  {Sem2.min = I32.to_int_u min; Sem2.max = if None? max then None else Some (I32.to_int_u (Some?.v max))}

val translate_mem_ty: memory_type -> Tot Sem2.memory_type
let translate_mem_ty ty =
  let MemoryType lim = ty in
  let ({min; max}) = lim in
  {Sem2.min = I32.to_int_u min; Sem2.max = if None? max then None else Some (I32.to_int_u (Some?.v max))}

val translate_func: Sem2.module_ -> Sem1.func -> Err_ Sem2.func
let translate_func m2 f1 =
  let f1 = f1.it in
  let ft2 = unwrapv f1.Sem1.ftype in
  match nth m2.Sem2.types ft2 with
  | None -> fail_with "translate_func: bad function type"
  | Some (argtys, rettys) ->
    let floc2 = argtys @ (map convert_type f1.Sem1.flocals) in
    let ctx1 = {m2 = m2; f1 = f1; targets = [false];
                local_types = floc2; stack_types = []; c = []}
    in
    let ctx2 = compile_codes f1.Sem1.body ctx1 in
    // NB: Wrapping with return is done later in the stack elimination phase
    //let body2' = [Sem2.Block body2 rettys; Sem2.Return] in
    //return ({Sem2.ftype = ft2; Sem2.flocals = floc2; Sem2.body = body2'})
    ({Sem2.ftype = ft2; Sem2.flocals = floc2; Sem2.body = ctx2.c})

val translate_funcs: Sem2.module_ -> fs1:list Sem1.func -> Err_ (list Sem2.func) (decreases %[fs1])
let rec translate_funcs m2 fs1 =
  match fs1 with
  | [] -> []
  | f1 :: fs1 ->
    let f2 = translate_func m2 f1 in
    let fs2 = translate_funcs m2 fs1 in
    (f2 :: fs2)

val translate_elem: Sem2.module_ -> Sem1.segment (list Sem1.var) -> Err_ (Sem2.segment (list Sem2.var))
let translate_elem m2 seg1 =
  let seg1 = seg1.it in
  let idx2 = unwrapv seg1.Sem1.index in
  let seg_offset2 = eval_const m2 seg1.Sem1.seg_offset in
  let init2 = map unwrapv seg1.Sem1.init in
  ({Sem2.index = idx2; Sem2.seg_offset = seg_offset2; Sem2.init = init2})

val translate_data: Sem2.module_ -> Sem1.segment (list nat8) -> Err_ (Sem2.segment (list nat8))
let translate_data m2 seg1 =
  let seg1 = seg1.it in
  let idx2 = unwrapv seg1.Sem1.index in
  let seg_offset2 = eval_const m2 seg1.Sem1.seg_offset in
  let init2 = seg1.Sem1.init in
  ({Sem2.index = idx2; Sem2.seg_offset = seg_offset2; Sem2.init = init2})

val translate_imps: list Sem1.import ->
                   Tot ((list (Sem2.import Sem2.var)) * (list (Sem2.import Sem2.table_type)) *
                        (list (Sem2.import Sem2.memory_type)) * (list (Sem2.import Sem2.global_type)))
let rec translate_imps limp1 =
  match limp1 with
  | [] -> [], [], [], []
  | imp1 :: limp1 ->
    let imp1 = imp1.it in
    let name2 = imp1.Sem1.module_name in
    let item_name2 = imp1.Sem1.item_name in
    let lfimp2, ltimp2, lmimp2, lgimp2 = translate_imps limp1 in
    match imp1.Sem1.idesc.it with
    | Sem1.FuncImport v ->
      ({Sem2.module_name = name2; Sem2.item_name = item_name2; Sem2.idesc = unwrapv v}) :: lfimp2,
      ltimp2, lmimp2, lgimp2
    | Sem1.TableImport tb ->
      lfimp2,
      ({Sem2.module_name = name2; Sem2.item_name = item_name2; Sem2.idesc = translate_tbl_ty tb}) :: ltimp2,
      lmimp2, lgimp2
    | Sem1.MemoryImport mem ->
      lfimp2, ltimp2,
      ({Sem2.module_name = name2; Sem2.item_name = item_name2; Sem2.idesc = translate_mem_ty mem}) :: lmimp2,
      lgimp2
    | Sem1.GlobalImport gb ->
      lfimp2, ltimp2, lmimp2,
      ({Sem2.module_name = name2; Sem2.item_name = item_name2; Sem2.idesc = translate_gbl_ty gb}) :: lgimp2

val translate_exps: list Sem1.export ->
                    Tot ((list Sem2.export) * (list Sem2.export) * (list Sem2.export) * (list Sem2.export))
let rec translate_exps lexp1 =
  match lexp1 with
  | [] -> [], [], [], []
  | exp1 :: lexp1 ->
    let exp1 = exp1.it in
    let name2 = exp1.Sem1.name in
    let lfexp2, ltexp2, lmexp2, lgexp2 = translate_exps lexp1 in
    match exp1.Sem1.edesc.it with
      | Sem1.FuncExport v ->
        ({Sem2.name = name2; Sem2.edesc = unwrapv v}) :: lfexp2, ltexp2, lmexp2, lgexp2
      | Sem1.TableExport v ->
        lfexp2, ({Sem2.name = name2; Sem2.edesc = unwrapv v}) :: ltexp2, lmexp2, lgexp2
      | Sem1.MemoryExport v ->
        lfexp2, ltexp2, ({Sem2.name = name2; Sem2.edesc = unwrapv v}) :: lmexp2, lgexp2
      | Sem1.GlobalExport v ->
        lfexp2, ltexp2, lmexp2, ({Sem2.name = name2; Sem2.edesc = unwrapv v}) :: lgexp2

val compile_module: Sem1.module_ -> nat32 -> Err_ Sem2.module_
let compile_module m1 mem_pages =
  let m1 = m1.it in
  let ty2 = map convert_func_type m1.Sem1.types in
  let gb2 = errmap (translate_gbl Sem2.empty_module) m1.Sem1.globals in
  let tb2 = map (fun ty -> translate_tbl_ty ty.it.Sem1.ttype) m1.Sem1.tables in
  let mem2 = map (fun ty -> translate_mem_ty ty.it.Sem1.mtype) m1.Sem1.memories in
  let func2 = map (fun f -> {Sem2.ftype = unwrapv f.it.Sem1.ftype; Sem2.flocals = []; Sem2.body = []}) m1.Sem1.funcs in
  let start2 =
    match m1.Sem1.start with
    | Some v -> Some (unwrapv v)
    | None -> None
  in
  let fim2, tim2, mim2, gim2 = translate_imps m1.Sem1.imports in
  let fex2, tex2, mex2, gex2 = translate_exps m1.Sem1.exports in
  let stub = ({Sem2.empty_module with
               Sem2.types = ty2;
               Sem2.globals = gb2;
               Sem2.tables = tb2;
               Sem2.memories = mem2;
               Sem2.funcs = func2;
               Sem2.start = start2;
               Sem2.fimports = fim2;
               Sem2.timports = tim2;
               Sem2.mimports = mim2;
               Sem2.gimports = gim2;
               Sem2.fexports = fex2;
               Sem2.texports = tex2;
               Sem2.mexports = mex2;
               Sem2.gexports = gex2;
               Sem2.mem_pages = mem_pages})
  in
  let fs2 = translate_funcs stub m1.Sem1.funcs in
  let elems2 = errmap (translate_elem stub) m1.Sem1.elems in
  let data2 = errmap (translate_data stub) m1.Sem1.data in
  ({stub with
    Sem2.funcs = fs2;
    Sem2.elems = elems2;
    Sem2.data = data2})
