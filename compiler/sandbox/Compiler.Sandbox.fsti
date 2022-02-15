module Compiler.Sandbox

open FStar.Ghost

open FStar.List.Tot.Base
open Common.Err
open Common.Memory
open Semantics.Common.CFG
open Semantics.Common.CFG.LowLevelSemantics

open Words_s

open I2.Semantics

let is_nat64 (n:int) : Tot bool = 0 <= n && n < pow2_64

let safe_callstack (s:state) (l:nat) =
  for_all (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s.callstack

let rec eval_steps (n:nat) (c:cfg) (s:state) : (l:list state{length l = n}) =
  match n with
  | 0 -> []
  | _ ->
    let s' = eval_step c s in
    s' :: eval_steps (n-1) c (eval_step c s)

val compile (mem_sb_size:nat) (mod:module_) (s: erased state) (n:erased nat) :
  Err module_
    (requires (
        (is_nat64 mem_sb_size && mem_sb_size > 8) /\
        (s.aux = mod.module_aux) /\
        (s.ok = AllOk) /\
        (forall (addr:nat). addr <= mem_sb_size ==> valid_addr addr s.mem) /\
        (s.ip < length mod.module_cfg) /\
        (safe_callstack s (length mod.module_cfg))))
    (ensures (fun m -> (
        let ss = eval_steps n m.module_cfg s in
        for_all (fun s1 -> s1.ok = AllOk) ss)))

val init_state (mem_sb_size:nat) (mod:module_) :
  Ghost state
    (requires (length mod.module_cfg > 0))
    (ensures (fun s ->
        (s.aux = mod.module_aux) /\
        (s.ok = AllOk) /\
        (forall (addr:nat). addr <= mem_sb_size ==> valid_addr addr s.mem) /\
        (s.ip < length mod.module_cfg) /\
        (safe_callstack s (length mod.module_cfg))))
