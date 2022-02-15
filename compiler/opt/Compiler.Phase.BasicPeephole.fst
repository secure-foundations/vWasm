module Compiler.Phase.BasicPeephole

open Common.Err
open Semantics.Common.CFG
open Semantics.Common.CFG.Instructions
open Common.Print

open Words_s

module Sem = I2.Semantics
module L = FStar.List.Tot
module M = FStar.Map
module S = FStar.OrdSet
module AOL = Common.AppendOptimizedList

module P = Semantics.Common.CFG.Printer

private let op_String_Access = AOL.index_and_optimize
private let op_String_Assignment = AOL.update_at

/// Basic Peephole Optimizations
///
/// This module performs the following peephole optimizations:
///
/// O1. If v is a constant:
///
/// 00 mov reg, v              mov dst, v
/// 01 mov dst, reg       ->   mov reg, x
/// 02 mov reg, x
///
/// Optimization is blocked if 01 is the target of a branch instruction.
///
/// This is currently a first-pass, very naive implementation.
/// TODO: Generalize peephole pass.

/// Printing helpers
private let rec string_of_list_ l p =
  match l with
  | [] -> ""
  | x :: l -> p x ++ ", " ++ string_of_list_ l p

private let string_of_list l p = "[" ++ string_of_list_ l p ++ "]"

/// Peephole
noeq type context = {
  done: AOL.t Sem.precode; // Code that has already been processed
  wind: AOL.t (Sem.precode & bool); // Code x is_target currently in the window
  left: Sem.cfg; // Code that has not been touched yet
  is_target: list bool; // true if instruction is a possible jump target (from left onwards)
  pc: loc; // pc that is start of window
}

let len_eq w w': Prims.Tot Type0 = AOL.length w = AOL.length w'

val try_loadelim: Sem.ins_t -> Sem.ins_t -> Sem.ins_t -> Tot (option (Sem.ins_t & Sem.ins_t))
let try_loadelim i0 i1 i2 =
  match i0, i1, i2 with
  | Mov32 (OReg r0 4) (OConst v),
    Mov32 dst (OReg r1 4),
    Mov32 (OReg r2 4) _

  | Mov32 (OReg r0 4) (OConst v),
    Mov32 dst (OReg r1 4),
    Mov64 (OReg r2 8) _ ->
    if r0 = r1 && r1 = r2 then (
      Some (Mov32 dst (OConst v), i2)
    ) else (
      None
    )

  // NB: 64-bit stores to stack can't be optimized _at all_ as the whole 8 bytes must be cleared.

  | _, _, _ -> None

#push-options "--fuel 10"
val do_loadelim_simple: AOL.t Sem.precode -> (w:AOL.t (Sem.precode & bool)) -> loc -> Err (AOL.t Sem.precode & AOL.t (Sem.precode & bool)) True (fun t -> len_eq w (snd t))
let do_loadelim_simple done wind pc =
  let l = AOL.length wind in
  if l > 3 then fail_with "do_peephole: wind too large";
  if l < 3 then (done, wind) else (
    assert (l = 3);
    let (c0, is_target0), wind = wind.[0] in
    let (c1, is_target1), wind = wind.[1] in
    let (c2, is_target2), wind = wind.[2] in

    match c0, c1, c2 with
    | Ins i0 n0, Ins i1 n1, Ins i2 n2 ->
       // Check if optimization is blocked
      if n0 = pc + 1 && n1 = pc + 2 && not is_target1 then (
        match try_loadelim i0 i1 i2 with
        | None -> (done, wind)
        | Some (i0, i1) ->
          // Nop is inserted into the middle so that branches to first and last are untouched
          (done, AOL.of_list [(Ins i0 n0, is_target0); (Nop n1, false); (Ins i1 n2, is_target2)])
      ) else (
        (done, wind)
      )
    | _, _, _ -> (done, wind)
  )
#pop-options

val do_optimize: (ctx:context) -> Err context True (fun ctx' -> len_eq ctx.wind ctx'.wind /\ ctx.left == ctx'.left)
let do_optimize ctx =
  let done, wind = do_loadelim_simple ctx.done ctx.wind ctx.pc in
  {ctx with done = done; wind = wind}

val slide_window: (ctx:context) ->
  Err context True (fun ctx' ->
    match ctx.left with
    | [] -> AOL.length ctx.wind = 0 \/ (AOL.length ctx'.wind < AOL.length ctx.wind /\ ctx'.left = [])
    | _ :: left -> ctx'.left == left
  )
let slide_window ctx =
  let pc = ctx.pc + 1 in
  match AOL.length ctx.wind, ctx.left, ctx.is_target with
  | 0, [], [] -> ctx
  | n, [], [] ->
    if n > 3 then fail_with "slide_window: too many items in window";

    let _, (ins, _), wind = AOL.split3 ctx.wind 0 in
    let done = AOL.snoc (ctx.done, ins) in
    {ctx with done = done; wind = wind; pc = pc}

  | 3, c :: cs, t :: ts ->
    let _, (ins, _), wind = AOL.split3 ctx.wind 0 in
    let done = AOL.snoc (ctx.done, ins) in
    {ctx with done = done; wind = AOL.snoc(wind, (c, t)); left = cs; is_target = ts; pc = pc}

  | n, c :: cs, t :: ts ->
    if n > 3 then fail_with "slide_window: too many items in window";

    // NB: Window not full, do not update pc
    {ctx with wind = AOL.snoc (ctx.wind, (c, t)); left = cs; is_target = ts}

  | _, _, _ ->
    fail_with "slide_window: mismatched left and preds"

val optimize: (ctx:context) -> Err_ context (decreases %[ctx.left; AOL.length ctx.wind])
let rec optimize ctx =
  match AOL.length ctx.wind, ctx.left with
  | 0, [] ->
    ctx
  | _, _ ->
    let ctx = slide_window ctx in
    let ctx = do_optimize ctx in
    optimize ctx

private val fold_err: ('a -> 'b -> Err_ 'a) -> 'a -> (ls:list 'b) -> Err_ 'a (decreases ls)
private let rec fold_err f acc ls =
  match ls with
  | [] -> acc
  | l :: ls ->
    let acc = f acc l in
    fold_err f acc ls

val update_target: aux -> (AOL.t bool & loc) -> Sem.precode -> Err_ (AOL.t bool & loc)
let update_target ax (l, pc) c =
  let ns = get_next ax c in
  let l = fold_err (fun l n ->
    if n >= AOL.length l then fail_with "update_target: bad target";
    if n <> pc + 1 then l.[n] <- true else l
  ) l ns
  in
  l, pc + 1

// NB: This is an overestimation of the possible targets, since dead code may target live code.
val compute_targets: Sem.cfg -> aux -> Err_ (list bool)
let compute_targets cs ax =
  let l = AOL.repeat (L.length cs) false in
  let l, _ = fold_err (update_target ax) (l, 0) cs in
  AOL.to_list l

val compile_module: Sem.module_ -> Err_ Sem.module_
let compile_module m =
  // Setup context and compile
  let is_target = compute_targets m.module_cfg m.module_aux in
  let ctx = {
    done = AOL.empty;
    wind = AOL.empty;
    left = m.module_cfg;
    is_target = is_target;
    pc = 0;
  } in
  let ctx = optimize ctx in
  {m with module_cfg = AOL.to_list ctx.done}
