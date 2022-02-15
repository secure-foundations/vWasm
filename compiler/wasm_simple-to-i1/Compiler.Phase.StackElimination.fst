module Compiler.Phase.StackElimination

open FStar.List.Tot

open Common.Err
open Semantics.Common.CFG
open Common.Print

open Words_s

private let op_String_Access = Map.sel
private let op_String_Assignment = Map.upd

module Sem1 = Wasm_simple.Semantics
module Sem2 = I1.Semantics
module SI2 = Semantics.Common.CFG.Instructions
module AOL = Common.AppendOptimizedList

/// Generic helpers
/// TODO: Move these somewhere, stop repeating

private let rec foldr_ex (f:'a -> 'b -> Err_ 'b) (l:list 'a) (c:'b): Err_ 'b =
  match l with
  | [] -> c
  | x :: l ->
    let c' = foldr_ex f l c in
    f x c'

private let set_at l (idx:nat{idx < length l}) x =
  let l0, x0, l1 = split3 l idx in
  l0 @ (x :: l1)

/// Code generation helpers

// NB: MIndex is always 32-bit register
let ori n sz: Sem2.operandi = OReg n sz
let orf n sz: Sem2.operandf = OReg_f n sz
let oci n: Sem2.operandi = OConst n
let omi s i o: Sem2.operandi = OMemRel (MIndex s i o)
let omf s i o: Sem2.operandf = OMemRel_f (MIndex s i o)
let oni id: Sem2.operandi = ONamedGlobal (Ident id)
let onf id: Sem2.operandf = ONamedGlobal_f (Ident_f id)
let ins i next: Sem2.precode = Ins i next

/// Compilation context and helper functions

noeq type context = {
  m1: Sem1.module_;
  aux: aux;
  f: Sem1.func;
  f_aux: aux_fn;
  stack_top: option nat;             // None if hit unreachable
  last: loc;                       // index of next empty ins slot
  targets: list (loc * nat * option val_ty); // list of targets for backwards branches, previous stack_top, optional return type of block
  pending: list (list loc);        // forward branches pending resolution
  br_pending: list (list (nat * nat)); // pending forward branches in br_tables, (index of table, index of case)
  returns: list loc;               // list of returns for this function, to be fixed up at the end
  c: AOL.t Sem2.precode;
  c_all: AOL.t Sem2.precode
}

module P = Semantics.Common.CFG.Printer

private let rec string_of_list_ l p =
  match l with
  | [] -> ""
  | x :: l -> p x ++ ", " ++ string_of_list_ l p

private let string_of_list l p = "[" ++ string_of_list_ l p ++ "]"

private let string_of_pending (pending:list (list loc)) =
  string_of_list pending (fun l -> string_of_list l P.string_of_int)

private let string_of_ctx ctx =
  let c_cfg = AOL.to_list ctx.c in
  Sem2.string_of_cfg c_cfg ++ "\n" ++
  "ctx.last: " ++ P.string_of_int ctx.last ++ "\n" ++
  "ctx.pending: " ++ string_of_pending ctx.pending

private let v ctx s = "Err (" ++ ctx.f_aux.fn_str ++ "): " ++ s ++ "\nContext:\n" ++ string_of_ctx ctx ++ "\n"

val update_cond: loc -> loc -> loc -> context -> Err_ context
let update_cond pos t f ctx =
  if pos < ctx.f_aux.fn_loc then fail_with (v ctx "update_cond: bad pos 1");
  let pos_real = pos - ctx.f_aux.fn_loc in
  if pos_real >= AOL.length ctx.c then fail_with (v ctx "update_cond: bad pos 2");
  match AOL.index_and_optimize ctx.c pos_real with
  | Cmp cond _ _, c_op ->
    let ins = Cmp cond t f in
    let c' = AOL.update_at c_op pos_real ins in
    {ctx with c = c'}
  | _ ->
    fail_with (v ctx "update_cond: not a Cmp instruction")

val update_br: loc -> loc -> context -> Err_ context
let update_br pos next ctx =
  if pos < ctx.f_aux.fn_loc then fail_with (v ctx "update_br: bad pos 1");
  let pos_real = pos - ctx.f_aux.fn_loc in
  if pos_real >= AOL.length ctx.c then fail_with (v ctx "update_br: bad pos 2");
  let ins, c_op =
    match AOL.index_and_optimize ctx.c pos_real with
    | Nop _, c_op -> Nop next, c_op
    | Cmp cond _ f, c_op -> Cmp cond next f, c_op
    | _ ->
      fail_with (v ctx "update_br: not a Nop/Cmp instruction")
  in
  let c' = AOL.update_at c_op pos_real ins in
  {ctx with c = c'}

val update_ret: loc -> loc -> context -> Err_ context
let update_ret pos next ctx =
  if pos < ctx.f_aux.fn_loc then fail_with (v ctx "update_ret: bad pos 1");
  let pos_real = pos - ctx.f_aux.fn_loc in
  if pos_real >= AOL.length ctx.c then fail_with (v ctx "update_ret: bad pos 2");
  let ins, c_op =
    match AOL.index_and_optimize ctx.c pos_real with
    | HighRet retval_load _, c_op -> HighRet retval_load next, c_op
    | _ ->
      fail_with (v ctx "update_ret: not a Ret instruction")
  in
  let c' = AOL.update_at c_op pos_real ins in
  {ctx with c = c'}

val update_br_table: nat * nat -> loc -> context -> Err_ context
let update_br_table (table_idx, case_idx) next ctx =
  if table_idx >= length ctx.aux.br_tables then (
    fail_with (v ctx "update_br_table: bad table_idx")
  );
  let tbl = index ctx.aux.br_tables table_idx in
  if case_idx >= length tbl.br_targets then (
    fail_with (v ctx "update_br_table: bad case_idx")
  );
  let br_targets' = set_at tbl.br_targets case_idx next in
  let tbl' = {tbl with br_targets = br_targets'} in
  let br_tables' = set_at ctx.aux.br_tables table_idx tbl' in
  let aux' = {ctx.aux with br_tables = br_tables'} in
  {ctx with aux = aux'}

/// Compiling instructions

let stack_ok (ctx:context): Tot (v:bool{v = Some? ctx.stack_top}) =
  Some? ctx.stack_top

let stack_ok_ e (ctx:context): Err unit True (fun () -> stack_ok ctx) =
  if None? ctx.stack_top then fail_with (v ctx ("stack_ok_: " ^ e ^ ": stack_top"))

let requires_ (n:nat) e (ctx:context) : Err unit True (fun () -> Some? ctx.stack_top && Some?.v ctx.stack_top >= length ctx.f.Sem1.flocals + n) =
  stack_ok_ e ctx;
  if Some?.v ctx.stack_top < length ctx.f.Sem1.flocals + n
  then fail_with (v ctx ("compile: " ^ e ^ ": stack_top"))

let top (ctx:context{stack_ok ctx}) = Some?.v ctx.stack_top

// NB: Can make the type stricter but requires propagating a whole bunch of types
let add_ins ins (n:int) (ctx1:context{stack_ok ctx1 && top ctx1 + n >= 0}): Err_ (ctx2:context{stack_ok ctx2}) =
  let last2 = ctx1.last + 1 in
  let ins2 = Ins ins last2 in
  let ctx2 = {ctx1 with
              c = AOL.snoc (ctx1.c, ins2);
              last = last2;
              stack_top = Some (top ctx1 + n)}
  in
  ctx2

let testop (op:Sem2.operandi -> Sem2.operandi -> Sem2.ocmp) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "testop" ctx1;
  let last = ctx1.last in
  let arg = ori (top ctx1 - 1) sz in
  let cmp = Cmp (op arg (oci 0)) (last + 1) (last + 2) in
  let moveq = Ins (SI2.Mov64 arg (oci 1)) (last + 3) in
  let movneq = Ins (SI2.Mov64 arg (oci 0)) (last + 3) in
  {ctx1 with
   last = last + 3;
   c = AOL.append ctx1.c (AOL.of_list [cmp; moveq; movneq])}

let relop (op:Sem2.operandi -> Sem2.operandi -> Sem2.ocmp) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 2 "cmpop" ctx1;
  let last = ctx1.last in
  let t = top ctx1 in
  let arg1 = ori (t - 2) sz in
  let arg2 = ori (t - 1) sz in
  let cmp = Cmp (op arg1 arg2) (last + 1) (last + 2) in
  let movy = Ins (SI2.Mov32 (ori (t - 2) 4) (oci 1)) (last + 3) in
  let movn = Ins (SI2.Mov32 (ori (t - 2) 4) (oci 0)) (last + 3) in
  {ctx1 with
   last = last + 3;
   stack_top = Some (t - 1);
   c = AOL.append ctx1.c (AOL.of_list [cmp; movy; movn])}


// TODO: How do instructions like these affect reg alloc?
let frelop (op:Sem2.operandf -> Sem2.operandf -> Sem2.ocmp) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 2 "cmpop" ctx1;
  let last = ctx1.last in
  let t = top ctx1 in
  let arg1 = orf (t - 2) sz in
  let arg2 = orf (t - 1) sz in
  let cmp = Cmp (op arg1 arg2) (last + 1) (last + 2) in
  let movy = Ins (SI2.Mov32 (ori (t - 2) 4) (oci 1)) (last + 3) in
  let movn = Ins (SI2.Mov32 (ori (t - 2) 4) (oci 0)) (last + 3) in
  {ctx1 with
   last = last + 3;
   stack_top = Some (t - 1);
   c = AOL.append ctx1.c (AOL.of_list [cmp; movy; movn])}

let unop (op:Sem2.operandi -> Sem2.operandi -> Sem2.ins_t) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "unop" ctx1;
  let c = add_ins (op (ori (top ctx1 - 1) sz) (ori (top ctx1 - 1) sz)) 0 ctx1 in
  c

let funop (op:Sem2.operandf -> Sem2.operandf -> Sem2.ins_t) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "funop" ctx1;
  let c = add_ins (op (orf (top ctx1 - 1) sz) (orf (top ctx1 - 1) sz)) 0 ctx1 in
  c

let binop (op:Sem2.operandi -> Sem2.operandi -> Sem2.ins_t) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 2 "binop" ctx1;
  let c = add_ins (op (ori (top ctx1 - 2) sz) (ori (top ctx1 - 1) sz)) (-1) ctx1 in
  c

let fbinop (op:Sem2.operandf -> Sem2.operandf -> Sem2.ins_t) (sz:rsize) (ctx1:context): Err_ context =
  requires_ 2 "fbinop" ctx1;
  let c = add_ins (op (orf (top ctx1 - 2) sz) (orf (top ctx1 - 1) sz)) (-1) ctx1 in
  c

let f2iconvop (op:Sem2.operandi -> Sem2.operandf -> Sem2.ins_t) (opa_sz:rsize) (opb_sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "f2iconvop" ctx1;
  let c = add_ins (op (ori (top ctx1 - 1) opa_sz) (orf (top ctx1 - 1) opb_sz)) 0 ctx1 in
  c

let i2fconvop (op:Sem2.operandf -> Sem2.operandi -> Sem2.ins_t) (opa_sz:rsize) (opb_sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "i2fconvop" ctx1;
  let c = add_ins (op (orf (top ctx1 - 1) opa_sz) (ori (top ctx1 - 1) opb_sz)) 0 ctx1 in
  c

let i2iconvop (op:Sem2.operandi -> Sem2.operandi -> Sem2.ins_t) (opa_sz:rsize) (opb_sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "i2iconvop" ctx1;
  let c = add_ins (op (ori (top ctx1 - 1) opa_sz) (ori (top ctx1 - 1) opb_sz)) 0 ctx1 in
  c

let f2fconvop (op:Sem2.operandf -> Sem2.operandf -> Sem2.ins_t) (opa_sz:rsize) (opb_sz:rsize) (ctx1:context): Err_ context =
  requires_ 1 "f2fconvop" ctx1;
  let c = add_ins (op (orf (top ctx1 - 1) opa_sz) (orf (top ctx1 - 1) opb_sz)) 0 ctx1 in
  c

val pack_float: list nat8 -> nat
let rec pack_float l =
  match l with
  | [] -> 0
  | n :: l ->
    let v = pack_float l in
    (v `op_Multiply` 256) + n

val compile_ins: Sem1.ins -> context -> Err_ context
let compile_ins ins1 ctx1 =
  stack_ok_ "compile_ins" ctx1;
  let c1 = ctx1.c in
  let last1 = ctx1.last in
  let stack_top1 = top ctx1 in
  let nlocals = length ctx1.f.Sem1.flocals in
  match ins1 with
  | Sem1.Unreachable ->
    let ctx2 = add_ins SI2.Unreachable 0 ctx1 in
    {ctx2 with stack_top = None}
  | Sem1.DropI
  | Sem1.DropF ->
    requires_ 1 "Drop" ctx1;
    {ctx1 with stack_top = Some (stack_top1 - 1)}
  | Sem1.SelectI ->
    requires_ 3 "SelectI" ctx1;
    let cond = ONe32 (ori (stack_top1 - 1) 4) (oci 0) in
    let cmp = Cmp cond (last1 + 2) (last1 + 1) in
    // No work needed for non-0 case
    let move1 = Ins (SI2.Mov64 (ori (stack_top1 - 3) 8) (ori (stack_top1 - 2) 8)) (last1 + 2) in
    {ctx1 with
     stack_top = Some (stack_top1 - 2);
     last = last1 + 2;
     c = AOL.append c1 (AOL.of_list [cmp; move1])}
  | Sem1.SelectF ->
    requires_ 3 "SelectF" ctx1;
    let cond = ONe32 (ori (stack_top1 - 1) 4) (oci 0) in
    let cmp = Cmp cond (last1 + 2) (last1 + 1) in
    let move1 = Ins (SI2.FMov64 (orf (stack_top1 - 3) 8) (orf (stack_top1 - 2) 8)) (last1 + 2) in
    {ctx1 with
     stack_top = Some (stack_top1 - 2);
     last = last1 + 2;
     c = AOL.append c1 (AOL.of_list [cmp; move1])}
  | Sem1.LocalGet v_ ->
    let c =
      match nth ctx1.f.Sem1.flocals v_ with
      | None -> fail_with (v ctx1 "compile_ins: LocalGet: bad idx")
      | Some ty ->
        match ty with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (ori stack_top1 4) (ori v_ 4)) 1 ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (ori stack_top1 8) (ori v_ 8)) 1 ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (orf stack_top1 4) (orf v_ 4)) 1 ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (orf stack_top1 8) (orf v_ 8)) 1 ctx1
    in
    c
  | Sem1.LocalSet v_ ->
    requires_ 1 "LocalSet" ctx1;
    let c =
      match nth ctx1.f.Sem1.flocals v_ with
      | None -> fail_with (v ctx1 "compile_ins: LocalSet: bad idx")
      | Some ty ->
        match ty with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (ori v_ 4) (ori (stack_top1 - 1) 4)) (-1) ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (ori v_ 8) (ori (stack_top1 - 1) 8)) (-1) ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (orf v_ 4) (orf (stack_top1 - 1) 4)) (-1) ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (orf v_ 8) (orf (stack_top1 - 1) 8)) (-1) ctx1
    in
    c
  | Sem1.LocalTee v_ ->
    requires_ 1 "LocalTee" ctx1;
    let c =
      match nth ctx1.f.Sem1.flocals v_ with
      | None -> fail_with (v ctx1 "compile_ins: LocalTee: bad idx")
      | Some ty ->
        match ty with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (ori v_ 4) (ori (stack_top1 - 1) 4)) 0 ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (ori v_ 8) (ori (stack_top1 - 1) 8)) 0 ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (orf v_ 4) (orf (stack_top1 - 1) 4)) 0 ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (orf v_ 8) (orf (stack_top1 - 1) 8)) 0 ctx1
    in
    c
  | Sem1.GlobalGet v_ ->
    let c =
      match nth ctx1.m1.Sem1.globals v_ with
      | None -> fail_with (v ctx1 "compile_ins: GlobalGet: bad idx")
      | Some gbl ->
        let idx = length ctx1.m1.Sem1.gimports + v_ in
        match fst gbl.Sem1.gtype with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (ori stack_top1 4) (oni idx)) 1 ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (ori stack_top1 8) (oni idx)) 1 ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (orf stack_top1 4) (onf idx)) 1 ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (orf stack_top1 8) (onf idx)) 1 ctx1
    in
    c
  | Sem1.GlobalSet v_ ->
    requires_ 1 "GlobalSet" ctx1;
    let c =
      match nth ctx1.m1.Sem1.globals v_ with
      | None -> fail_with (v ctx1 "compile_ins: GlobalGet: bad idx")
      | Some gbl ->
        let idx = length ctx1.m1.Sem1.gimports + v_ in
        match fst gbl.Sem1.gtype with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (oni idx) (ori (stack_top1 - 1) 4)) (-1) ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (oni idx) (ori (stack_top1 - 1) 8)) (-1) ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (onf idx) (orf (stack_top1 - 1) 4)) (-1) ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (onf idx) (orf (stack_top1 - 1) 8)) (-1) ctx1
    in
    c
  | Sem1.ExternGlobalGet v_ ->
    let c =
      match nth ctx1.m1.Sem1.gimports v_ with
      | None -> fail_with (v ctx1 "compile_ins: ExternGlobalGet: bad idx")
      | Some gi ->
        match fst gi.Sem1.idesc with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (ori stack_top1 4) (oni v_)) 1 ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (ori stack_top1 8) (oni v_)) 1 ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (orf stack_top1 4) (onf v_)) 1 ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (orf stack_top1 8) (onf v_)) 1 ctx1
    in
    c
  | Sem1.ExternGlobalSet v_ ->
    requires_ 1 "ExternGlobalSet" ctx1;
    let c =
      match nth ctx1.m1.Sem1.gimports v_ with
      | None -> fail_with (v ctx1 "compile_ins: ExternGlobalGet: bad idx")
      | Some gi ->
        match fst gi.Sem1.idesc with
        | Sem1.I32Ty ->
          add_ins (SI2.Mov32 (oni v_) (ori (stack_top1 - 1) 4)) (-1) ctx1
        | Sem1.I64Ty ->
          add_ins (SI2.Mov64 (oni v_) (ori (stack_top1 - 1) 8)) (-1) ctx1
        | Sem1.F32Ty ->
          add_ins (SI2.FMov32 (onf v_) (orf (stack_top1 - 1) 4)) (-1) ctx1
        | Sem1.F64Ty ->
          add_ins (SI2.FMov64 (onf v_) (orf (stack_top1 - 1) 8)) (-1) ctx1
    in
    c
  | Sem1.Load loadop ->
    requires_ 1 "Load" ctx1;
    let {Sem1.lty; Sem1.loffset; Sem1.lsz; Sem1.lsigned} = loadop in
    let idx = stack_top1 - 1 in
    let di32, di64 = ori idx 4, ori idx 8 in
    let df32, df64 = orf idx 4, orf idx 8 in
    let si = omi 1 idx loffset in
    let sf = omf 1 idx loffset in
    let ins =
      match lty, lsz, lsigned with
      | Sem1.I32Ty, 1, true  -> SI2.MovSX8to32 di32 si
      | Sem1.I32Ty, 1, false -> SI2.MovZX8to32 di32 si
      | Sem1.I32Ty, 2, true  -> SI2.MovSX16to32 di32 si
      | Sem1.I32Ty, 2, false -> SI2.MovZX16to32 di32 si
      | Sem1.I32Ty, 4, _     -> SI2.Mov32 di32 si
      | Sem1.I32Ty, _, _     -> fail_with (v ctx1 "compile_ins: bad loadop")
      | Sem1.I64Ty, 1, true  -> SI2.MovSX8to64 di64 si
      | Sem1.I64Ty, 1, false -> SI2.MovZX8to64 di64 si
      | Sem1.I64Ty, 2, true  -> SI2.MovSX16to64 di64 si
      | Sem1.I64Ty, 2, false -> SI2.MovZX16to64 di64 si
      | Sem1.I64Ty, 4, true  -> SI2.MovSX32to64 di64 si
      | Sem1.I64Ty, 4, false -> SI2.MovZX32to64 di64 si
      | Sem1.I64Ty, 8, _     -> SI2.Mov64 di64 si

      | Sem1.F32Ty, 4, _     -> SI2.FMov32 df32 sf
      | Sem1.F64Ty, 8, _     -> SI2.FMov64 df64 sf
      | _, _, _              -> fail_with (v ctx1 "compile_ins: bad float loadop")
    in
    let c = add_ins ins 0 ctx1 in
    c
  | Sem1.Store storeop ->
    requires_ 2 "Store" ctx1;
    let {Sem1.sty; Sem1.soffset; Sem1.ssz} = storeop in
    let idx = stack_top1 - 2 in
    let v_ = stack_top1 - 1 in
    let si = ori v_ in
    let sf = orf v_ in
    let di = omi 1 idx soffset in
    let df = omf 1 idx soffset in
    let ins =
      match sty, ssz with
      | Sem1.I32Ty, 1 -> SI2.Mov8 di (si 1)
      | Sem1.I32Ty, 2 -> SI2.Mov16 di (si 2)
      | Sem1.I32Ty, 4 -> SI2.Mov32 di (si 4)
      | Sem1.I32Ty, _ -> fail_with (v ctx1 "compile_ins: bad storeop")
      | Sem1.I64Ty, 1 -> SI2.Mov8 di (si 1)
      | Sem1.I64Ty, 2 -> SI2.Mov16 di (si 2)
      | Sem1.I64Ty, 4 -> SI2.Mov32 di (si 4)
      | Sem1.I64Ty, 8 -> SI2.Mov64 di (si 8)
      | Sem1.F32Ty, 4 -> SI2.FMov32 df (sf 4)
      | Sem1.F64Ty, 8 -> SI2.FMov64 df (sf 8)
      | _, _          -> fail_with (v ctx1 "compile_ins: bad float storeop")
    in
    let c = add_ins ins (-2) ctx1 in
    c
  | Sem1.MemorySize ->
    let c = add_ins (SI2.Mov32 (OReg stack_top1 4) (ONamedGlobal MemPages)) 1 ctx1 in
    c
  | Sem1.MemoryGrow ->
    // We are using the fake MemPages to track memory 'size'
    requires_ 1 "MemoryGrow" ctx1;
    let delta = ori (stack_top1 - 1) 4 in
    let mp = ori stack_top1 4 in
    let ctx2 = add_ins (SI2.Mov32 mp (ONamedGlobal MemPages)) 1 ctx1 in
    let ctx3 = add_ins (SI2.Add32 delta mp) 0 ctx2 in
    let last = ctx3.last in
    let cmp1 = Cmp (OGe32 delta mp) (last + 1) (last + 5) in
    let cmp2 = Cmp (OLe32 delta (oci ctx1.m1.Sem1.mem_pages)) (last + 2) (last + 5) in
    let movs = Ins (SI2.Mov32 (ONamedGlobal MemPages) delta) (last + 3) in
    let movsz = Ins (SI2.Mov32 delta mp) (last + 4) in
    let br_end = Nop (last + 6) in
    let movf = Ins (SI2.Mov32 delta (oci (-1))) (last + 6) in
    let c4 = AOL.append ctx3.c (AOL.of_list [cmp1; cmp2; movs; movsz; br_end; movf]) in
    {ctx3 with last = last + 6; stack_top = Some stack_top1; c = c4}
  | Sem1.Const (Sem1.N32 n) ->
    let c = add_ins (SI2.Mov32 (OReg stack_top1 4) (OConst n)) 1 ctx1 in
    c
  | Sem1.Const (Sem1.N64 n) ->
    let c = add_ins (SI2.Mov64 (OReg stack_top1 8) (OConst n)) 1 ctx1 in
    c
  | Sem1.Const (Sem1.F32 f) ->
    let v = pack_float f in
    let c = add_ins (SI2.Mov32 (OReg stack_top1 4) (OConst v)) 1 ctx1 in
    c
  | Sem1.Const (Sem1.F64 f) ->
    let v = pack_float f in
    let c = add_ins (SI2.Mov64 (OReg stack_top1 8) (OConst v)) 1 ctx1 in
    c
  | Sem1.I32Eqz -> testop OEq32 4 ctx1
  | Sem1.I64Eqz -> testop OEq64 8 ctx1
  | Sem1.I32Eq  -> relop OEq32 4 ctx1
  | Sem1.I32Ne  -> relop ONe32 4 ctx1
  | Sem1.I32LtS -> relop OLtS32 4 ctx1
  | Sem1.I32LtU -> relop OLt32 4 ctx1
  | Sem1.I32GtS -> relop OGtS32 4 ctx1
  | Sem1.I32GtU -> relop OGt32 4 ctx1
  | Sem1.I32LeS -> relop OLeS32 4 ctx1
  | Sem1.I32LeU -> relop OLe32 4 ctx1
  | Sem1.I32GeS -> relop OGeS32 4 ctx1
  | Sem1.I32GeU -> relop OGe32 4 ctx1
  | Sem1.I64Eq  -> relop OEq64 8 ctx1
  | Sem1.I64Ne  -> relop ONe64 8 ctx1
  | Sem1.I64LtS -> relop OLtS64 8 ctx1
  | Sem1.I64LtU -> relop OLt64 8 ctx1
  | Sem1.I64GtS -> relop OGtS64 8 ctx1
  | Sem1.I64GtU -> relop OGt64 8 ctx1
  | Sem1.I64LeS -> relop OLeS64 8 ctx1
  | Sem1.I64LeU -> relop OLe64 8 ctx1
  | Sem1.I64GeS -> relop OGeS64 8 ctx1
  | Sem1.I64GeU -> relop OGe64 8 ctx1
  | Sem1.F32Eq  -> frelop OFEq32 4 ctx1
  | Sem1.F32Ne  -> frelop OFNe32 4 ctx1
  | Sem1.F32Lt  -> frelop OFLt32 4 ctx1
  | Sem1.F32Gt  -> frelop OFGt32 4 ctx1
  | Sem1.F32Le  -> frelop OFLe32 4 ctx1
  | Sem1.F32Ge  -> frelop OFGe32 4 ctx1
  | Sem1.F64Eq  -> frelop OFEq64 8 ctx1
  | Sem1.F64Ne  -> frelop OFNe64 8 ctx1
  | Sem1.F64Lt  -> frelop OFLt64 8 ctx1
  | Sem1.F64Gt  -> frelop OFGt64 8 ctx1
  | Sem1.F64Le  -> frelop OFLe64 8 ctx1
  | Sem1.F64Ge  -> frelop OFGe64 8 ctx1
  | Sem1.I32Clz     -> unop SI2.Clz32 4 ctx1
  | Sem1.I32Ctz     -> unop SI2.Ctz32 4 ctx1
  | Sem1.I32Popcnt  -> unop SI2.Popcnt32 4 ctx1
  | Sem1.I64Clz     -> unop SI2.Clz64 8 ctx1
  | Sem1.I64Ctz     -> unop SI2.Ctz64 8 ctx1
  | Sem1.I64Popcnt  -> unop SI2.Popcnt64 8 ctx1
  | Sem1.F32Neg     -> funop SI2.FNeg32 4 ctx1
  | Sem1.F32Abs     -> funop SI2.FAbs32 4 ctx1
  | Sem1.F32Ceil    -> funop SI2.FCeil32 4 ctx1
  | Sem1.F32Floor   -> funop SI2.FFloor32 4 ctx1
  | Sem1.F32Trunc   -> funop SI2.FTrunc32 4 ctx1
  | Sem1.F32Nearest -> funop SI2.FNearest32 4 ctx1
  | Sem1.F32Sqrt    -> funop SI2.FSqrt32 4 ctx1
  | Sem1.F64Neg     -> funop SI2.FNeg64 8 ctx1
  | Sem1.F64Abs     -> funop SI2.FAbs64 8 ctx1
  | Sem1.F64Ceil    -> funop SI2.FCeil64 8 ctx1
  | Sem1.F64Floor   -> funop SI2.FFloor64 8 ctx1
  | Sem1.F64Trunc   -> funop SI2.FTrunc64 8 ctx1
  | Sem1.F64Nearest -> funop SI2.FNearest64 8 ctx1
  | Sem1.F64Sqrt    -> funop SI2.FSqrt64 8 ctx1
  | Sem1.I32Add      -> binop SI2.Add32 4 ctx1
  | Sem1.I32Sub      -> binop SI2.Sub32 4 ctx1
  | Sem1.I32Mul      -> binop SI2.Mul32 4 ctx1
  | Sem1.I32DivS     -> binop SI2.DivS32 4 ctx1
  | Sem1.I32DivU     -> binop SI2.DivU32 4 ctx1
  | Sem1.I32RemS     -> binop SI2.RemS32 4 ctx1
  | Sem1.I32RemU     -> binop SI2.RemU32 4 ctx1
  | Sem1.I32And      -> binop SI2.And32 4 ctx1
  | Sem1.I32Or       -> binop SI2.Or32 4 ctx1
  | Sem1.I32Xor      -> binop SI2.Xor32 4 ctx1
  | Sem1.I32Shl      -> binop SI2.Shl32 4 ctx1
  | Sem1.I32ShrS     -> binop SI2.ShrS32 4 ctx1
  | Sem1.I32ShrU     -> binop SI2.ShrU32 4 ctx1
  | Sem1.I32Rotl     -> binop SI2.Rotl32 4 ctx1
  | Sem1.I32Rotr     -> binop SI2.Rotr32 4 ctx1
  | Sem1.I64Add      -> binop SI2.Add64 8 ctx1
  | Sem1.I64Sub      -> binop SI2.Sub64 8 ctx1
  | Sem1.I64Mul      -> binop SI2.Mul64 8 ctx1
  | Sem1.I64DivS     -> binop SI2.DivS64 8 ctx1
  | Sem1.I64DivU     -> binop SI2.DivU64 8 ctx1
  | Sem1.I64RemS     -> binop SI2.RemS64 8 ctx1
  | Sem1.I64RemU     -> binop SI2.RemU64 8 ctx1
  | Sem1.I64And      -> binop SI2.And64 8 ctx1
  | Sem1.I64Or       -> binop SI2.Or64 8 ctx1
  | Sem1.I64Xor      -> binop SI2.Xor64 8 ctx1
  | Sem1.I64Shl      -> binop SI2.Shl64 8 ctx1
  | Sem1.I64ShrS     -> binop SI2.ShrS64 8 ctx1
  | Sem1.I64ShrU     -> binop SI2.ShrU64 8 ctx1
  | Sem1.I64Rotl     -> binop SI2.Rotl64 8 ctx1
  | Sem1.I64Rotr     -> binop SI2.Rotr64 8 ctx1
  | Sem1.F32Add      -> fbinop SI2.FAdd32 4 ctx1
  | Sem1.F32Sub      -> fbinop SI2.FSub32 4 ctx1
  | Sem1.F32Mul      -> fbinop SI2.FMul32 4 ctx1
  | Sem1.F32Div      -> fbinop SI2.FDiv32 4 ctx1
  | Sem1.F32Min      -> fbinop SI2.FMin32 4 ctx1
  | Sem1.F32Max      -> fbinop SI2.FMax32 4 ctx1
  | Sem1.F32CopySign -> fbinop SI2.FCopySign32 4 ctx1
  | Sem1.F64Add      -> fbinop SI2.FAdd64 8 ctx1
  | Sem1.F64Sub      -> fbinop SI2.FSub64 8 ctx1
  | Sem1.F64Mul      -> fbinop SI2.FMul64 8 ctx1
  | Sem1.F64Div      -> fbinop SI2.FDiv64 8 ctx1
  | Sem1.F64Min      -> fbinop SI2.FMin64 8 ctx1
  | Sem1.F64Max      -> fbinop SI2.FMax64 8 ctx1
  | Sem1.F64CopySign -> fbinop SI2.FCopySign64 8 ctx1
  | Sem1.I32WrapI64          -> i2iconvop SI2.Mov32 4 8 ctx1
  | Sem1.I32TruncSF32        -> f2iconvop SI2.I32TruncSF32 4 4 ctx1
  | Sem1.I32TruncUF32        -> f2iconvop SI2.I32TruncUF32 4 4 ctx1
  | Sem1.I32TruncSF64        -> f2iconvop SI2.I32TruncSF64 4 8 ctx1
  | Sem1.I32TruncUF64        -> f2iconvop SI2.I32TruncUF64 4 8 ctx1
  | Sem1.I32ReinterpretFloat -> f2iconvop SI2.ReinterpretFloat32 4 4 ctx1
  | Sem1.I64ExtendSI32       -> i2iconvop SI2.MovSX32to64 8 4 ctx1
  | Sem1.I64ExtendUI32       -> i2iconvop SI2.MovZX32to64 8 4 ctx1
  | Sem1.I64TruncSF32        -> f2iconvop SI2.I64TruncSF32 8 4 ctx1
  | Sem1.I64TruncUF32        -> f2iconvop SI2.I64TruncUF32 8 4 ctx1
  | Sem1.I64TruncSF64        -> f2iconvop SI2.I64TruncSF64 8 8 ctx1
  | Sem1.I64TruncUF64        -> f2iconvop SI2.I64TruncUF64 8 8 ctx1
  | Sem1.I64ReinterpretFloat -> f2iconvop SI2.ReinterpretFloat64 8 8 ctx1
  | Sem1.F32DemoteF64        -> f2fconvop SI2.F32DemoteF64 4 8 ctx1
  | Sem1.F32ConvertSI32      -> i2fconvop SI2.F32ConvertSI32 4 4 ctx1
  | Sem1.F32ConvertUI32      -> i2fconvop SI2.F32ConvertUI32 4 4 ctx1
  | Sem1.F32ConvertSI64      -> i2fconvop SI2.F32ConvertSI64 4 8 ctx1
  | Sem1.F32ConvertUI64      -> i2fconvop SI2.F32ConvertUI64 4 8 ctx1
  | Sem1.F32ReinterpretInt   -> i2fconvop SI2.ReinterpretInt32 4 4 ctx1
  | Sem1.F64PromoteF32       -> f2fconvop SI2.F64PromoteF32 8 4 ctx1
  | Sem1.F64ConvertSI32      -> i2fconvop SI2.F64ConvertSI32 8 4 ctx1
  | Sem1.F64ConvertUI32      -> i2fconvop SI2.F64ConvertUI32 8 4 ctx1
  | Sem1.F64ConvertSI64      -> i2fconvop SI2.F64ConvertSI64 8 8 ctx1
  | Sem1.F64ConvertUI64      -> i2fconvop SI2.F64ConvertUI64 8 8 ctx1
  | Sem1.F64ReinterpretInt   -> i2fconvop SI2.ReinterpretInt64 8 8 ctx1

  | _ -> fail_with (v ctx1 "compile_ins: unimplemented")

/// Compiling precode objects

let prepend_at l (idx:nat{idx < length l}) x =
  let lx = index l idx in
  set_at l idx (x :: lx)

// Called when leaving a block context
let fixup_targets_pending dest ctx: Err_ context =
  if length ctx.targets = 0 || length ctx.pending = 0 || length ctx.br_pending = 0 then (
    fail_with (v ctx "resolve_pending: bad pending")
  );

  let pending_list = hd ctx.pending in
  let br_pending_list = hd ctx.br_pending in
  let f pos ctx_: Err_ context = update_br pos dest ctx_ in
  let g which ctx_: Err_ context = update_br_table which dest ctx_ in
  let ctx1 = foldr_ex f pending_list ctx in
  let ctx2 = foldr_ex g br_pending_list ctx1 in
  let targets3 = tl ctx.targets in
  let pending3 = tl ctx.pending in
  let br_pending3 = tl ctx.br_pending in
  {ctx2 with targets = targets3; pending = pending3; br_pending = br_pending3}

let arg_to_carg (arg:val_ty) (stack_idx:nat) =
  match arg with
  | I32_ty -> ArgInt stack_idx false
  | I64_ty -> ArgInt stack_idx true
  | F32_ty -> ArgFloat stack_idx false
  | F64_ty -> ArgFloat stack_idx true

let rec fn_args_to_call_args (args:list val_ty) (stack_idx:nat) =
  match args with
  | [] -> []
  | arg :: args' ->
    let carg = arg_to_carg arg stack_idx in
    carg :: (fn_args_to_call_args args' (stack_idx + 1))

let wsimple_arg_to_carg (arg:Sem1.value_type) (stack_idx:nat) =
  match arg with
  | Sem1.I32Ty -> ArgInt stack_idx false
  | Sem1.I64Ty -> ArgInt stack_idx true
  | Sem1.F32Ty -> ArgFloat stack_idx false
  | Sem1.F64Ty -> ArgFloat stack_idx true

let rec wsimple_args_to_call_args (args:list Sem1.value_type) (stack_idx:nat) =
  match args with
  | [] -> []
  | arg :: args' ->
    let carg = wsimple_arg_to_carg arg stack_idx in
    carg :: (wsimple_args_to_call_args args' (stack_idx + 1))

(* Convert a value type to a val_ty *)
let value_type_to_ty (ty:Sem1.value_type) =
  match ty with
  | Sem1.I32Ty -> I32_ty
  | Sem1.I64Ty -> I64_ty
  | Sem1.F32Ty -> F32_ty
  | Sem1.F64Ty -> F64_ty

let value_types_to_retty (tys:list Sem1.value_type) (ctx:context): Err_ (option val_ty) =
  match tys with
  | [] -> None
  | [ty] -> Some (value_type_to_ty ty)
  | _ -> fail_with (v ctx "compile_code: unsupported return type")

// Generates block exit shift returns, does not touch stack_top
val gen_block_exit_shift: option val_ty -> nat -> context -> Err_ context
let gen_block_exit_shift rettys dest ctx =
  if stack_ok ctx then (
    match rettys with
    | None -> ctx
    | Some ty_ ->
      requires_ 1 "compile_code: block ty" ctx;
      let t' = top ctx in
      // Optimization if already top of stack and no shift required
      if t' = dest + 1 then ctx else (
        let ins =
          match ty_ with
          | I32_ty -> SI2.Mov32 (ori dest 4) (ori (t' - 1) 4)
          | I64_ty -> SI2.Mov64 (ori dest 8) (ori (t' - 1) 8)
          | F32_ty -> SI2.FMov32 (orf dest 4) (orf (t' - 1) 4)
          | F64_ty -> SI2.FMov64 (orf dest 8) (orf (t' - 1) 8)
        in
        // NB: Do not touch stack
        let c = add_ins ins 0 ctx in
        c
      )
  ) else (
    fail_with (v ctx "gen_block_exit_shift: stack not ok")
  )

// NB: Because each different case of the brtable can result in different amounts of stack needing to be cleared up, we have compile branch statements by generating a list of cleanup + unconditional branch to target, and have the actual branch table jump to these if needed
let rec gen_br_table (cases:list (nat * bool)) (tbl_idx:nat) (case_idx:nat) (ctx:context): Err_ (aux_br_table * context) =
  match cases with
  | [] ->
    // Base case, create a new table
    let br_name = "br__" ^ (int_to_str (length ctx.aux.br_tables)) in
    let tbl = {br_name = br_name; br_targets = []} in
    tbl, ctx
  | (level, isContinue) :: cases' ->
    if level >= length ctx.targets then (
      fail_with (v ctx "gen_br_table: bad level")
    );

    // Add cleanup + branch for this case (if needed)
    // Backwards branches (Continue) never have returns because
    // they always reduce to label_0
    let br_start = ctx.last in
    let dest, t, rettys = index ctx.targets level in
    let ctx1 = if isContinue || None? rettys then ctx else (
      // TODO: Potentially check if gen_block_exit_shift produced any code and optimize out branch
      // Forward branch with return, put a branch after cleanup (if  any)
      let ctx_ = gen_block_exit_shift rettys t ctx in
      let last1 = ctx_.last + 1 in
      let c1 = AOL.snoc (ctx_.c, Nop 0) in

      // Record pending forward branch
      if level >= length ctx_.pending then fail_with (v ctx_ "gen_br_table: bad ctx_.pending");
      let pending1 = prepend_at ctx_.pending level ctx_.last in
      {ctx_ with last = last1; pending = pending1; c = c1}
    )
    in

    // Compute recursively
    let tbl2, ctx2 = gen_br_table cases' tbl_idx (case_idx + 1) ctx1 in

    // Add entry to br_table
    let tbl3 =
      if isContinue then (
        // Continue branch, backwards target is known
        {tbl2 with br_targets = dest :: tbl2.br_targets}
      ) else if None? rettys then (
        // Forward branch, no return, pending br_table fixup
        {tbl2 with br_targets = 0 :: tbl2.br_targets}
      ) else (
        // Forward branch, has return, target cleanup stub
        {tbl2 with br_targets = br_start :: tbl2.br_targets}
      )
    in

    // Update br_pending if needed
    let br_pending3 =
      if not isContinue && None? rettys then (
        if level >= length ctx2.br_pending then fail_with (v ctx2 "gen_br_table: bad br_pending");
        prepend_at ctx2.br_pending level (tbl_idx, case_idx)
      ) else (
        ctx2.br_pending
      )
    in

    let ctx3 = {ctx2 with br_pending = br_pending3} in
    tbl3, ctx3

// Generates either a Nop or a Cmp with branches pointing to the next instruction.
// Set stack_top as appropriate
val compile_cond: Sem1.jcond -> bool -> option val_ty -> nat -> context -> Err_ context
let compile_cond cond1 do_cleanup rettys dest ctx =
  match cond1 with
  | Sem1.Always ->
    // Do block cleanup if necessary
    let ctx1 =
      if do_cleanup then (
        gen_block_exit_shift rettys dest ctx
      ) else (
        ctx
      )
    in
    let last2 = ctx1.last + 1 in
    let c2 = AOL.snoc (ctx1.c, Nop last2) in
    {ctx1 with stack_top = None; last = last2; c = c2}
  | Sem1.IsNonZero ->
    stack_ok_ "compile_cond" ctx;
    requires_ 1 "compile_cond (IsNonZero)" ctx;

    // Check the condition
    let t = top ctx - 1 in
    let stack_top1 = t in
    let last1 = ctx.last + 1 in
    let cond1 = ONe32 (ori t 4) (oci 0) in
    let c1 = AOL.snoc (ctx.c, Cmp cond1 last1 last1) in
    let ctx1 = {ctx with stack_top = Some stack_top1; last = last1; c = c1} in
    // Do block cleanup in the success branch if needed
    let ctx2 =
      if do_cleanup then (
        // Note: cleanup does not touch stack_top
        let ctx_ = gen_block_exit_shift rettys dest ctx1 in
        if ctx_.last = ctx1.last then ctx_ else (
          // Add a Nop for the branch target rewrite if any cleanup code was generated
          let last2 = ctx_.last + 1 in
          let c2 = AOL.snoc (ctx_.c, Nop last2) in
          {ctx_ with last = last2; c = c2}
        )
      ) else (
        ctx1
      )
    in
    // Fix the Cmp targets
    // End result of both branches is that the last instruction is always the branch target to fix
    let cmp3 = Cmp cond1 last1 ctx2.last in
    if ctx.last < ctx.f_aux.fn_loc then fail_with (v ctx2 "compile_cond: bad ctx.last 1");
    let pos_real = ctx.last - ctx.f_aux.fn_loc in

    if pos_real >= AOL.length ctx2.c then fail_with (v ctx2 "compile_cond: bad ctx.last");

    let c3 = AOL.update_at ctx2.c pos_real cmp3 in
    {ctx2 with c = c3}

val compile_code: Sem1.code -> context -> Err_ context
val compile_codes: Sem1.codes -> context -> Err_ context
let rec compile_code c1 ctx =
  stack_ok_ "compile_code" ctx;
  match c1 with
  | Sem1.Ins ins1 ->
    // compile_ins updates last as well as stack_top
    //let _ = IO.debug_print_string "Begin: Ins\n" in
    let ret = compile_ins ins1 ctx in
    //let _ = IO.debug_print_string "End: Ins\n" in
    ret

  | Sem1.Block cs1 ts1 ->
    // Fixup targets and pending
    //let _ = IO.debug_print_string "Begin: Block\n" in
    let start = ctx.last in
    let t = top ctx in
    let tys = value_types_to_retty ts1 ctx in
    let targets1 = (start, t, tys) :: ctx.targets in
    let pending1 = [] :: ctx.pending in
    let br_pending1 = [] :: ctx.br_pending in
    let ctx1 = {ctx with targets = targets1; pending = pending1; br_pending = br_pending1} in

    // Generate body
    let ctx2 = compile_codes cs1 ctx1 in

    // No need to generate block exit shift returns, validation
    // guarantees that the block produces _exactly_ the desired number of
    // outputs if the block exits naturally (i.e. no branches out)

    // Fixup forward branches and branch lists
    let ctx3 = fixup_targets_pending ctx2.last ctx2 in

    // Fixup stack_top
    let stack_top4 = t + length ts1 in
    //let _ = IO.debug_print_string "End: Block\n" in
    {ctx3 with stack_top = Some stack_top4}

  | Sem1.IfElse ctrue1 cfalse1 ts1 ->
    // Generate conditional
    //let _ = IO.debug_print_string "Begin: IfElse\n" in
    let ctx1 = compile_cond Sem1.IsNonZero false None 0 ctx in

    stack_ok_ "compile_code: IfElse" ctx1;
    let t = top ctx1 in
    let tys = value_types_to_retty ts1 ctx1 in

    // Generate true branch
    let start_true = ctx1.last in
    let targets2 = (start_true, t, tys) :: ctx.targets in
    let pending2 = [] :: ctx.pending in
    let br_pending2 = [] :: ctx.br_pending in
    let ctx2 = {ctx1 with targets = targets2; pending = pending2; br_pending = br_pending2} in

    // Compile true branch (must generate exact returns, no shift needed)
    let ctx3 = compile_codes ctrue1 ctx2 in

    if ctx3.targets = [] || ctx3.pending = [] then (
      fail_with (v ctx3 "compile_code (IfElse ctx3): bad targets/pending")
    );

    // Add placeholder branch to after IfElse (if needed), will be fixed later
    let ctx4 =
      if stack_ok ctx3 then (
         let last4 = ctx3.last + 1 in
         let c4 = AOL.snoc (ctx3.c, Nop 0) in
         let pending4 = prepend_at ctx3.pending 0 (ctx3.last) in
         {ctx3 with last = last4; pending = pending4; c = c4}
       ) else (
        ctx3
      )
    in

    // Reset stack_top, generate false branch
    // Targets modified, pending/br_pending carries over, resolved at end of IfElse
    let stack_top5 = t in
    let start_false = ctx4.last in
    let targets5 = (start_false, t, tys) :: tl ctx4.targets in
    let ctx5 = {ctx4 with stack_top = Some stack_top5; targets = targets5} in

    // Compile false branch (must generate exact returns, no shift needed)
    let ctx6 = compile_codes cfalse1 ctx5 in

    // Update branch targets for conditional
    if ctx1.last = 0 then fail_with (v ctx6 "compile_code (IfElse ctx8): bad last");

    let ctx7 = update_cond (ctx1.last - 1) start_true start_false ctx6 in

    // Leaving if/else generated blocks, fixup forward branches and branch lists
    let ctx8 = fixup_targets_pending ctx7.last ctx7 in

    // Fixup stack_top
    let stack_top9 = t + length ts1 in
    //let _ = IO.debug_print_string "End: IfElse\n" in
    {ctx8 with stack_top = Some stack_top9}

  | Sem1.Break level cond ->
    //let _ = IO.debug_print_string "Begin: Break\n" in
    if level >= length ctx.targets then (
      fail_with (v ctx "compile_code (Break): bad targets")
    );

    // Insert a Nop/Cmp
    let _, t, rettys = index ctx.targets level in
    let ctx1 = compile_cond cond true rettys t ctx in

    if ctx1.last = 0 then fail_with (v ctx1 "compile_code (Break): bad last");
    if level >= length ctx1.pending then (
      fail_with (v ctx1 "compile_code (Break): bad pending")
    );

    // Enqueue nop/cmp, kill stack on unconditional exits
    let pending2 = prepend_at ctx1.pending level (ctx1.last - 1) in
    let stack_top2 = if Sem1.Always? cond then None else ctx1.stack_top in
    //let _ = IO.debug_print_string "End: Break\n" in
    {ctx1 with pending = pending2; stack_top = stack_top2}

  | Sem1.BrTable tbl ->
    requires_ 1 "BrTable" ctx;

    let tbl_idx = length ctx.aux.br_tables in
    let def_level, isContinue = tbl.Sem1.def in

    // Generate conditional for oob case
    let t = top ctx - 1 in
    let stack_top1 = t in
    let num_cases = length tbl.Sem1.cases in
    let cond = OGe32 (ori t 4) (oci num_cases) in

    // Create branch instruction and bound for default branch
    // Also pop off the case register off the stack
    let last1 = ctx.last + 3 in
    let c1 = AOL.append ctx.c (
      AOL.of_list [
        Cmp cond (ctx.last + 1) (ctx.last + 2);
        Ins (SI2.Mov32 (ori t 4) (oci num_cases)) (ctx.last + 2);
        Switch tbl_idx t
      ]
    )
    in
    let ctx1 = {ctx with last = last1; c = c1; stack_top = Some stack_top1} in

    // Generate table, stubs and updated pendings
    // Append default case to list of cases
    let tbl_gen, ctx2 = gen_br_table (tbl.Sem1.cases @ [tbl.Sem1.def]) tbl_idx 0 ctx1 in

    // Update list of tables and ctx
    let aux3 = {ctx2.aux with br_tables = ctx2.aux.br_tables @ [tbl_gen]} in
    {ctx2 with aux = aux3; stack_top = None}

  | Sem1.Continue level cond ->
    //let _ = IO.debug_print_string "Begin: Continue\n" in
    if level >= length ctx.targets then (
      fail_with (v ctx "compile_code (Continue): bad targets")
    );

    // Insert appropriate Nop/Cmp, rettys always None for continue (reduces to label_0)
    let dest, t, _ = index ctx.targets level in
    let ctx1 = compile_cond cond true None t ctx in

    if ctx1.last = 0 then fail_with (v ctx1 "compile_code (Continue): bad last");

    // Update br and kill stack on unconditional control flow transfer
    let ctx2 = update_br (ctx1.last - 1) dest ctx1 in
    let stack_top3 = if Sem1.Always? cond then None else ctx2.stack_top in
    //let _ = IO.debug_print_string "End: Continue\n" in
    {ctx2 with stack_top = stack_top3}

  | Sem1.Call f ->
    // Since we combine both call and externcall back here again, we need to adjust the index from the previous simplify phase.
    // TODO: Tidy up?
    let f_ = f + length ctx.m1.Sem1.fimports in
    if f_ >= length ctx.aux.fns then fail_with (v ctx "compile_code (Call): bad func index");

    let f_aux = index ctx.aux.fns f_ in
    let l = length f_aux.fn_argtys in
    requires_ l "Call" ctx;

    let base = top ctx - l in
    let call_args = fn_args_to_call_args f_aux.fn_argtys base in
    let rv_store =
      match f_aux.fn_rettys with
      | None -> None
      | Some arg -> Some (arg_to_carg arg base)
    in
    let stack_top1 = if None? rv_store then base else base + 1 in
    let last1 = ctx.last + 1 in
    // NB: Should be calling by index f_ and not f_aux.fn_name as was used previously
    let c1 = AOL.snoc (ctx.c, HighCall (CallDirect f_) call_args rv_store last1) in
    {ctx with stack_top = Some stack_top1; last = last1; c = c1}

  | Sem1.ExternCall f ->
    //let _ = IO.debug_print_string "Begin: Call/ExternCall\n" in
    if f >= length ctx.aux.fns then fail_with (v ctx "compile_code (ExternCall): bad func index");

    let f_aux = index ctx.aux.fns f in
    let l = length f_aux.fn_argtys in
    requires_ l "ExternCall" ctx;

    let base = top ctx - l in
    let call_args = fn_args_to_call_args f_aux.fn_argtys base in
    let rv_store =
      match f_aux.fn_rettys with
      | None -> None
      | Some arg -> Some (arg_to_carg arg base)
    in
    let stack_top1 = if None? rv_store then base else base + 1 in
    let last1 = ctx.last + 1 in
    // NB: Should be calling by index f and not f_aux.fn_name as was used previously
    let c1 = AOL.snoc (ctx.c, HighCall (CallDirect f) call_args rv_store last1) in
    //let _ = IO.debug_print_string "End: Call/ExternCall\n" in
    {ctx with stack_top = Some stack_top1; last = last1; c = c1}

  | Sem1.CallIndirect v_ ->
    //let _ = IO.debug_print_string "Begin: CallIndirect\n" in
    let t = top ctx in
    if v_ >= length ctx.m1.Sem1.types then fail_with (v ctx "compile_code (CallIndirect): bad type index");

    let (argtys1, rettys1) = index ctx.m1.Sem1.types v_ in
    let l = length argtys1 in
    requires_ (l + 1) "CallIndirect" ctx;

    let reg = top ctx - 1 in
    let base = reg - l in
    let call_args = wsimple_args_to_call_args argtys1 base in
    let rv_store =
      match rettys1 with
      | [] -> None
      | [arg] -> Some (wsimple_arg_to_carg arg base)
      | _ -> fail_with (v ctx "compile_code (CallIndirect): too many returns")
    in
    let stack_top1 = if None? rv_store then base else base + 1 in
    let last1 = ctx.last + 1 in
    let c1 = AOL.snoc (ctx.c, HighCall (CallIndirect reg) call_args rv_store last1) in
    //let _ = IO.debug_print_string "End: CallIndirect\n" in
    {ctx with stack_top = Some stack_top1; last = last1; c = c1}

  | Sem1.Return ->
    //let _ = IO.debug_print_string "Begin: Return\n" in
    let last1 = ctx.last + 1 in
    let returns1 = ctx.last :: ctx.returns in
    let retval_load1 =
      match ctx.f_aux.fn_rettys with
      | None -> None
      | Some ty ->
        requires_ 1 "Return" ctx;
        Some (arg_to_carg ty (top ctx - 1))
    in
    let c1 = AOL.snoc (ctx.c, HighRet retval_load1 0) in
    //let _ = IO.debug_print_string "End: Return\n" in
    {ctx with last = last1; returns = returns1; c = c1; stack_top = None}

and compile_codes cs1 ctx =
  match cs1 with
  | [] ->
    ctx
  | c1 :: cs1' ->
    // End processing of block if not stack_ok
    if not (stack_ok ctx) then ctx else (
      let ctx' = compile_code c1 ctx in
      compile_codes cs1' ctx'
    )

/// Infrastructure for compiling functions

let nil_fn = {Sem1.ftype = 0; Sem1.flocals = []; Sem1.body = []}
let nil_f_aux = {fn_name = 0; fn_str = ""; fn_loc = 0; fn_end = 0;
                 fn_argtys = []; fn_rettys = None; fn_locals = [];
                 fn_isImported = false; fn_isExported = false}

val compile_func: Sem1.func -> aux_fn -> nat -> context -> Err_ context
let compile_func f1 f_aux1 idx ctx =
  // first -> start of function, last = next code position
  let f_aux_ = {f_aux1 with fn_loc = ctx.last} in
  let last1 = ctx.last + 1 in
  let c_entry = [FnEntry f_aux_.fn_name last1] in
  let ctx1 = {ctx with f = f1; f_aux = f_aux_;
                       stack_top = Some (length f_aux_.fn_locals);
                       last = last1; targets = []; pending = [];
                       br_pending = []; returns = [];
                       c = AOL.of_list c_entry}
  in

  // Wrap body in block and insert implicit return
  let rettys =
    match f_aux_.fn_rettys with
    | None -> []
    | Some I32_ty -> [Sem1.I32Ty]
    | Some I64_ty -> [Sem1.I64Ty]
    | Some F32_ty -> [Sem1.F32Ty]
    | Some F64_ty -> [Sem1.F64Ty]
  in
  let body' = [Sem1.Block f1.Sem1.body rettys; Sem1.Return] in
  let ctx2 = compile_codes body' ctx1 in

  // Implicit ret is handled, no special exit handling
  let fnexit_loc = ctx2.last in
  let c_exit = AOL.snoc (ctx2.c, FnExit f_aux_.fn_name) in
  let ctx3 = {ctx2 with last = ctx2.last + 1; c = c_exit} in

  // Resolve returns
  let f pos ctx_: Err_ context = update_ret pos fnexit_loc ctx_ in
  let ctx4 = foldr_ex f ctx3.returns ctx3 in

  // Update loc in f_aux
  // fn_end is one after end of function
  let f_aux5 = {f_aux_ with fn_loc = ctx.last; fn_end = ctx4.last} in
  if idx >= length ctx4.aux.fns then fail_with (v ctx4 "compile_func: bad function idx");
  let fns5 = set_at ctx4.aux.fns idx f_aux5 in
  let aux5 = {ctx4.aux with fns = fns5} in
  {ctx4 with f_aux = f_aux5; aux = aux5; c_all = AOL.append ctx4.c_all ctx4.c}

val compile_funcs_: list Sem1.func -> list aux_fn -> nat -> list aux_fn -> context -> Err_ (context * list aux_fn)
let rec compile_funcs_ fs1 fs_aux idx fns ctx =
  match fs1, fs_aux with
  | [], [] -> ctx, fns
  | f1 :: fs1', f_aux :: fs_aux' ->
    if f_aux.fn_isImported then (
      // Skip imported functions, but keep a function entry in aux_fn (it still needs to be called and indexed right)
      compile_funcs_ fs1 fs_aux' (idx + 1) (fns @ [f_aux]) ctx
    ) else (
      let ctx' = compile_func f1 f_aux idx ctx in
      compile_funcs_ fs1' fs_aux' (idx + 1) (fns @ [ctx'.f_aux]) ctx'
    )
  | _, _ -> fail_with "compile_funcs_: fn/aux mismatch"

val compile_funcs: Sem1.module_ -> aux -> Err_ Sem2.module_
let compile_funcs m1 aux =
  let ctx = {m1 = m1; aux = aux; f = nil_fn; f_aux = nil_f_aux;
             stack_top = Some 0; last = 0;
             targets = []; pending = [];
             br_pending = []; returns = [];
             c = AOL.empty; c_all = AOL.empty}
  in
  let ctx', fns'' =  compile_funcs_ m1.Sem1.funcs aux.fns 0 [] ctx in
  let aux'' = {ctx'.aux with fns = fns''} in
  {module_aux = aux''; module_cfg = AOL.to_list ctx'.c_all}

/// Aux generation functions
/// TODO: Probably a good idea to refactor this code to reduce duplication

let rec nat_to_init (size:nat) n : list nat8 =
  if size = 0 then [] else (
    let rem:nat8 = n `op_Modulus` 256 in
    let quot = n `op_Division` 256 in
    rem :: nat_to_init (size - 1) quot
  )

(* TODO: Convert a literal to bytes *)
let lit_to_init_list (lit:Sem1.literal): list nat8 =
  match lit with
  | Sem1.N32 n -> nat_to_init 4 n
  | Sem1.N64 n -> nat_to_init 8 n
  | Sem1.F32 f -> admit()
  | Sem1.F64 f -> admit()

let mk_fn idx n aty rty lty im ex = {fn_name = idx; fn_str = n;
                                     fn_loc = 0; fn_end = 0;
                                     fn_argtys = aty; fn_rettys = rty; fn_locals = lty;
                                     fn_isImported = im; fn_isExported = ex}

open FStar.IO

let rec fill_fn_imports (m1:Sem1.module_) (imps:list (Sem1.import Sem1.var)) (idx:nat): Err_ (list aux_fn) =
  match imps with
  | [] -> []
  | imp :: imps ->
    let {Sem1.module_name; Sem1.item_name; Sem1.idesc} = imp in
    let l = fill_fn_imports m1 imps (idx + 1) in
    match nth m1.Sem1.types idesc with
    | None -> fail_with "fill_imports: bad function type index"
    | Some (argtys, rettys) ->
      let argtys2 = map value_type_to_ty argtys in
      let rettys2 = map value_type_to_ty rettys in
      if length rettys2 > 1 then fail_with "fill_imports: too many returns" else (
        let rty = if length rettys2 = 0 then None else Some (hd rettys2) in
        mk_fn idx (name_to_str item_name) argtys2 rty [] true false :: l
      )

let rec def_funcs (m1:Sem1.module_) (prefix:string) (fns:list Sem1.func) (idx:nat): Err_ (list aux_fn) =
  match fns with
  | [] -> []
  | fn :: fns ->
    let {Sem1.ftype; Sem1.flocals; Sem1.body} = fn in
    match nth m1.Sem1.types ftype with
    | None -> fail_with "def_names: bad function type index"
    | Some (argtys, rettys) ->
      let argtys2 = map value_type_to_ty argtys in
      let rettys2 = map value_type_to_ty rettys in
      let locals2 = map value_type_to_ty flocals in
      if length rettys2 > 1 then fail_with "def_names: too many returns" else (
        let rty = if length rettys2 = 0 then None else Some (hd rettys2) in
        let ns = def_funcs m1 prefix fns (idx + 1) in
        mk_fn idx (prefix ^ (string_of_int idx)) argtys2 rty locals2 false false :: ns
      )

let rec fix_fn_exports (exps:list Sem1.export) (ns:list aux_fn): Err_ (list aux_fn) =
  match exps with
  | [] -> ns
  | exp :: exps ->
    let {Sem1.name; Sem1.edesc} = exp in
    (* NB: Assumes that there is nothing both imported and exported *)
    if edesc >= length ns then fail_with "fix_exports: bad index " else (
      let ns0, rep, ns1 = split3 ns edesc in
      let rep' = {rep with fn_str = name_to_str name; fn_isExported = true} in
      let ns' = ns0 @ (rep' :: ns1) in
      fix_fn_exports exps ns'
    )

(* Imports go in front, according to ML spec *)
val gen_fn_info: Sem1.module_ -> string -> Err_ (list aux_fn)
let gen_fn_info m1 prefix =
  let names0 = fill_fn_imports m1 m1.Sem1.fimports 0 in
  let names1 = def_funcs m1 prefix m1.Sem1.funcs (length names0) in
  let names2 = names0 @ names1 in
  let names3 = fix_fn_exports m1.Sem1.fexports names2 in
  let _ = IO.debug_print_string ("names0: " ^ string_of_int (length names0) ^ "\n") in
  let _ = IO.debug_print_string ("names1: " ^ string_of_int (length names1) ^ "\n") in
  let _ = IO.debug_print_string ("names2: " ^ string_of_int (length names2) ^ "\n") in
  let _ = IO.debug_print_string ("names3: " ^ string_of_int (length names3) ^ "\n") in
  names3

let mk_gbl n init ty mut im ex = {gbl_name = n; gbl_init = init; gbl_ty = ty;
                                  gbl_isMutable = mut; gbl_isImported = im; gbl_isExported = ex}

let rec def_names (prefix:string) (idx:nat) (n:nat) : Tot (list (string * bool * bool)) (decreases %[n - idx]) =
  if idx >= n then [] else (prefix ^ (nat_to_hex idx), false, false) :: def_names prefix (idx + 1) n

let rec fill_gbl_imports (imps:list (Sem1.import Sem1.global_type)) =
  match imps with
  | [] -> []
  | imp :: imps ->
    let {Sem1.module_name; Sem1.item_name; Sem1.idesc} = imp in
    ((name_to_str item_name), true, false) :: fill_gbl_imports imps

let rec fix_gbl_exports (exps:list Sem1.export) (ns:list (string * bool * bool)): Err_ (list (string * bool * bool)) =
  match exps with
  | [] -> ns
  | exp :: exps ->
    let {Sem1.name; Sem1.edesc} = exp in
    (* NB: Assumes that there is nothing both imported and exported *)
    if edesc >= length ns then fail_with "fix_exports (gbl): bad index " else (
      let ns0, rep, ns1 = split3 ns edesc in
      let _, isImported, _ = rep in
      let ns' = ns0 @ ((name_to_str name, isImported, true) :: ns1) in
      fix_gbl_exports exps ns'
    )

let rec populate_gbl_import_info (ns:list (string * bool * bool)) (imps:list (Sem1.import Sem1.global_type)): Err_ (list aux_global) =
  match ns, imps with
  | [], [] -> []
  | (name, im, ex) :: ns', imp :: imps' ->
    let {Sem1.module_name; Sem1.item_name; Sem1.idesc} = imp in
    let init = None in
    let val_ty, mut = idesc in
    let ty = value_type_to_ty val_ty in
    let info' = populate_gbl_import_info ns' imps' in
    mk_gbl name init ty mut im ex :: info'
  | _, _ -> fail_with "populate_import_info (gbl): length mismatch"

let rec populate_gbl_def_info (ns:list (string * bool * bool)) (defs:list Sem1.global): Err_ (list aux_global) =
  match ns, defs with
  | [], [] -> []
  | (name, im, ex) :: ns', def :: defs' ->
    let {Sem1.gtype; Sem1.value} = def in
    let init = Some (lit_to_init_list value) in
    let val_ty, mut = gtype in
    let ty = value_type_to_ty val_ty in
    let info' = populate_gbl_def_info ns' defs' in
    mk_gbl name init ty mut im ex :: info'
  | _, _ -> fail_with "populate_def_info (gbl): length mismatch"

val gen_gbl_info: Sem1.module_ -> string -> Err_ (list aux_global)
let gen_gbl_info m1 prefix =
  let names0 = fill_gbl_imports m1.Sem1.gimports in
  let names1 = def_names prefix (length names0) (length names0 + length m1.Sem1.globals) in
  let names2 = names0 @ names1 in
  let names3 = fix_gbl_exports m1.Sem1.gexports names2 in
  let names_imp, names_def = splitAt (length names0) names3 in
  let populated_imports = populate_gbl_import_info names_imp m1.Sem1.gimports in
  let populated_defs = populate_gbl_def_info names_def m1.Sem1.globals in
  populated_imports @ populated_defs

let mk_mem n init min max im ex = {mem_name = n; mem_init = init; mem_min = min; mem_max = max;
                                   mem_isImported = im; mem_isExported = ex}

let rec segments_to_tups (segs:list (Sem1.segment (list nat8))): Err_ (list ((list nat8) * nat32)) =
  match segs with
  | [] -> []
  | seg :: segs' ->
    match seg.Sem1.seg_offset with
    | Sem1.N32 n ->
      let tups' = segments_to_tups segs' in
      (seg.Sem1.init, n) :: tups'
    | _ -> fail_with "segment_to_tup: offset not nat32"

(* TODO: Assumes unique memory, and exports line up appropriately (if they exist) *)
val gen_mem_info: Sem1.module_ -> string -> Err_ aux_memory
let gen_mem_info m1 name =
  if length m1.Sem1.mimports = 1 then (
    // Imported memory, no initializers
    let {Sem1.module_name; Sem1.item_name; Sem1.idesc} = hd m1.Sem1.mimports in
    let init = [] in
    let {Sem1.min; Sem1.max} = idesc in
    let im = true in
    let ex = length m1.Sem1.mexports = 1 in
    let name = name_to_str item_name in
    mk_mem name init min max im ex
  ) else if length m1.Sem1.memories = 1 then (
    // Non-imported memory, may be initialized
    let init = segments_to_tups m1.Sem1.data in
    let {Sem1.min; Sem1.max} = hd m1.Sem1.memories in
    let im = false in
    let ex = length m1.Sem1.mexports = 1 in
    let name =
      if length m1.Sem1.mexports = 1 then (
        let exp = hd m1.Sem1.mexports in
        name_to_str exp.Sem1.name
      ) else (
        name
      )
    in
    mk_mem name init min max im ex
  ) else if length m1.Sem1.memories = 0 then (
    mk_mem "m1" [] 0 (Some 0) false false
  ) else (
    fail_with "gen_mem_info: bad number of memories"
  )

let mk_call_tbl n init = {call_name = n; call_init = init}

let rec def_call_table (sz:nat): list (option nat) = if sz = 0 then [] else None :: def_call_table (sz - 1)

let set_range (l:list 'a) idx (l':list 'a): Err_ (list 'a) =
  if idx >= length l || idx + length l' > length l then fail_with "set: bad idx/length" else (
    let l0, l_ = splitAt idx l in
    let l1, l2 = splitAt (length l') l_ in
    l0 @ l' @ l2
  )

let rec fill_init (segs:list (Sem1.segment (list Sem1.var))) (def:list (option nat)): Err_ (list (option nat)) =
  match segs with
  | [] -> def
  | seg :: segs' ->
    let {Sem1.index; Sem1.seg_offset; Sem1.init} = seg in
    match seg_offset with
    | Sem1.N32 n ->
      let init_ = map Some init in
      let def' = set_range def n init_ in
      fill_init segs' def'
    | _ -> fail_with "fill_init: bad base"

(* TODO: Similar assumptions as mem. We do not yet support imported call tables *)
val gen_call_info: Sem1.module_ -> string -> Err_ aux_call_table
let gen_call_info m1 name =
  if length m1.Sem1.tables > 1 then (
    fail_with "gen_call_info: bad number of tables"
  ) else if length m1.Sem1.tables = 1 then (
    // Non-imported call table, may be initialized
    let {Sem1.min; Sem1.max} = hd m1.Sem1.tables in
    let def = def_call_table min in
    let init = fill_init m1.Sem1.elems def in
    let im = false in
    let ex = length m1.Sem1.mexports = 1 in
    let name =
      if length m1.Sem1.mexports = 1 then (
        let exp = hd m1.Sem1.mexports in
        name_to_str exp.Sem1.name
      ) else (
        name
      )
    in
    mk_call_tbl name init
  ) else (
    // No tables
    mk_call_tbl name []
  )

val gen_aux: Sem1.module_ -> Err_ aux
let gen_aux m1 =
  let fn_info = gen_fn_info m1 "func_" in
  let gbl_info = gen_gbl_info m1 "g__" in
  let mem_info = gen_mem_info m1 "m__0" in
  let br_tables = [] in // this gets modified during compilation
  let call_table = gen_call_info m1 "c__0" in
  let mem_pages = m1.Sem1.mem_pages in
  {fns = fn_info; globals = gbl_info; memory = mem_info; br_tables = br_tables; call_table = call_table; mem_pages = mem_pages}

/// Compile the module.

val compile_module: Sem1.module_ -> Err_ Sem2.module_
let compile_module m1 =
  let {Sem1.types; Sem1.globals; Sem1.tables; Sem1.memories; Sem1.funcs;
       Sem1.start; Sem1.elems; Sem1.data;
       Sem1.fimports; Sem1.timports; Sem1.mimports; Sem1.gimports;
       Sem1.fexports; Sem1.texports; Sem1.mexports; Sem1.gexports;
       Sem1.mem_pages} = m1 in
  if length funcs >= pow2_32
  then fail_with "compile_module: too many functions"
  else if length timports <> 0
  then fail_with "compile_module: table imports not supported yet"
  else (
    let aux = gen_aux m1 in
    compile_funcs m1 aux
  )
