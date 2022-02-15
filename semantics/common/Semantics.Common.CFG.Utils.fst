/// TODO: Will need to be update for each semantics respectively, when the time comes.
/// Currently this code will only be compatible with LowLevelSemantics.

(** Utilities to make it easier to define semantics *)
module Semantics.Common.CFG.Utils

open Common.Memory
open Types_s
module F = FStar.FunctionalExtensionality
module L = FStar.List.Tot

open Semantics.Common.CFG
open Semantics.Common.CFG.LowLevelSemantics

/// Define a stateful monad to simplify defining the instruction semantics

let st (a:Type) = state -> a * state

(* Convenient for defining eval_ins *)
let maintained_property (s1 s2:state) =
  s1.ip = s2.ip /\
  s1.aux = s2.aux /\
  s1.callstack = s2.callstack /\
  (forall a. {:pattern (valid_addr a s2.mem)} valid_addr a s1.mem ==> valid_addr a s2.mem)
let st_maintained (a:Type) = (f:st a{forall s. {:pattern maintained_property s} maintained_property s (snd (f s))}) (* Yes, the pattern is quite generic here unfortunately *)

unfold
let return (#a:Type) (x:a) :st_maintained a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
  fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok `ok_join` s1.ok `ok_join` s2.ok}

unfold
let get :st_maintained state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail_with (o:ok_t) :st_maintained unit =
  fun s -> (), {s with ok=o}

unfold
let check (valid: state -> ok_t) : st_maintained unit =
  s <-- get;
  match valid s with
  | AllOk -> return ()
  | x -> fail_with x

unfold
let run (f:st unit) (s:state) : state = snd (f s)

/// Useful functions for updating operands

let update_reg' #vali (r:regi #vali) (v:nat64) (s:state) : state =
  { s with reg_i = F.on_dom int (fun r' -> if r' = r then v else s.reg_i r') }
let update_regf' #valf (r:regf #valf) (v:float) (s:state) : state =
  { s with reg_f = F.on_dom int (fun r' -> if r' = r then v else s.reg_f r') }

let update_global' (n:int) (v:nat64) (s:state) : state =
  { s with global_i = F.on_dom int (fun n' -> if n' = n then v else s.global_i n') }
let update_globalf' (n:int) (v:float) (s:state) : state =
  { s with global_f = F.on_dom int (fun n' -> if n' = n then v else s.global_f n') }

let update_mem64 (ptr:int) (v:nat64) (s:state) : (s':state{maintained_property s s'}) =
  if valid_addr64 ptr s.mem then (
    Opaque_s.reveal_opaque update_heap64_def;
    { s with mem = update_heap64 ptr v s.mem }
  ) else s
let update_mem32 (ptr:int) (v:nat32) (s:state) : (s':state{maintained_property s s'}) =
  if valid_addr32 ptr s.mem then (
    Opaque_s.reveal_opaque update_heap32_def;
    { s with mem = update_heap32 ptr v s.mem }
  ) else s
let update_mem16 (ptr:int) (v:nat16) (s:state) : (s':state{maintained_property s s'}) =
  if valid_addr16 ptr s.mem then (
    Opaque_s.reveal_opaque update_heap16_def;
    { s with mem = update_heap16 ptr v s.mem }
  ) else s
let update_mem8 (ptr:int) (v:nat8) (s:state) : (s':state{maintained_property s s'}) =
  if valid_addr8 ptr s.mem then (
    Opaque_s.reveal_opaque update_heap8_def;
    { s with mem = update_heap8 ptr v s.mem }
  ) else s

let update_operand64' #vali (o:operandi #vali) (v:nat64) (s:state) : state =
  match o with
  | OConst _ -> {s with ok = AstFailure}
  | OReg r _ -> update_reg' r v s
  | OMemRel m -> update_mem64 (eval_maddr m s) v s // see valid_maddr for how eval_maddr connects to b and i
  | OStackRel m -> update_stack64 (s.stack_pointer + m) v s
  | ONamedGlobal (Ident n) -> update_global' n v s
  | ONamedGlobal MemPages -> {s with ok = AstFailure}
let update_operand32' #vali (o:operandi #vali) (v:nat32) (s:state) : state =
  match o with
  | OConst _ -> {s with ok = AstFailure}
  | OReg r _ -> update_reg' r v s
  | OMemRel m -> update_mem32 (eval_maddr m s) v s // see valid_maddr for how eval_maddr connects to b and i
  | OStackRel m -> update_stack32 (s.stack_pointer + m) v s
  | ONamedGlobal (Ident n) -> update_global' n v s
  | ONamedGlobal MemPages -> {s with global_mem_pages = v}
let update_operand16' #vali (o:operandi #vali) (v:nat16) (s:state) : state =
  match o with
  | OConst _ -> {s with ok = AstFailure}
  | OReg r _ -> update_reg' r v s
  | OMemRel m -> update_mem16 (eval_maddr m s) v s // see valid_maddr for how eval_maddr connects to b and i
  | OStackRel m -> update_stack16 (s.stack_pointer + m) v s
  | ONamedGlobal _ -> {s with ok = AstFailure}
let update_operand8' #vali (o:operandi #vali) (v:nat8) (s:state) : state =
  match o with
  | OConst _ -> {s with ok = AstFailure}
  | OReg r _ -> update_reg' r v s
  | OMemRel m -> update_mem8 (eval_maddr m s) v s // see valid_maddr for how eval_maddr connects to b and i
  | OStackRel m -> update_stack8 (s.stack_pointer + m) v s
  | ONamedGlobal _ -> {s with ok = AstFailure}

let update_operandf64' #vali #valf (o:operandf #vali #valf) (v:float) (s:state) : state =
  match o with
  | OConst_f _ -> {s with ok = AstFailure}
  | OReg_f r _ -> update_regf' r v s
  | OMemRel_f m -> update_mem64 (eval_maddr m s) (ftoi64 v) s
  | OStackRel_f m -> update_stack64 (s.stack_pointer + m) (ftoi64 v) s
  | ONamedGlobal_f (Ident_f n) -> update_globalf' n v s
let update_operandf32' #vali #valf (o:operandf #vali #valf) (v:float) (s:state) : state =
  match o with
  | OConst_f _ -> {s with ok = AstFailure}
  | OReg_f r _ -> update_regf' r v s
  | OMemRel_f m -> update_mem32 (eval_maddr m s) (ftoi32 v) s
  | OStackRel_f m -> update_stack32 (s.stack_pointer + m) (ftoi32 v) s
  | ONamedGlobal_f (Ident_f n) -> update_globalf' n v s

unfold
let valid_dst_stack64 (rsp:int) (ptr:int) (st:stack) : bool =
  // We are allowed to store anywhere between Rsp and the initial stack pointer
  ptr >= rsp && ptr + 8 <= st.init_rsp
unfold
let valid_dst_stack32 (rsp:int) (ptr:int) (st:stack) : bool =
  // We are allowed to store anywhere between Rsp and the initial stack pointer
  ptr >= rsp && ptr + 4 <= st.init_rsp
unfold
let valid_dst_stack16 (rsp:int) (ptr:int) (st:stack) : bool =
  // We are allowed to store anywhere between Rsp and the initial stack pointer
  ptr >= rsp && ptr + 2 <= st.init_rsp
unfold
let valid_dst_stack8 (rsp:int) (ptr:int) (st:stack) : bool =
  // We are allowed to store anywhere between Rsp and the initial stack pointer
  ptr >= rsp && ptr + 1 <= st.init_rsp

let valid_dst_operand64 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AstFailure
  | OReg r sz -> astcheck(sz = 8)
  | OMemRel m -> memcheck (valid_addr64 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_dst_stack64 s.stack_pointer (s.stack_pointer + m) s.stack)
  | ONamedGlobal (Ident n) -> valid_src_operand64 o s
  | ONamedGlobal MemPages -> AstFailure
let valid_dst_operand32 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AstFailure
  | OReg r sz -> astcheck(sz = 4)
  | OMemRel m -> memcheck (valid_addr32 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_dst_stack32 s.stack_pointer (s.stack_pointer + m) s.stack)
  | ONamedGlobal (Ident n) -> valid_src_operand32 o s
  | ONamedGlobal MemPages -> AllOk
let valid_dst_operand16 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AstFailure
  | OReg r sz -> astcheck(sz = 2)
  | OMemRel m -> memcheck (valid_addr16 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_dst_stack16 s.stack_pointer (s.stack_pointer + m) s.stack)
  | ONamedGlobal _ -> valid_src_operand16 o s
let valid_dst_operand8 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AstFailure
  | OReg r sz -> astcheck(sz = 1)
  | OMemRel m -> memcheck (valid_addr8 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_dst_stack8 s.stack_pointer (s.stack_pointer + m) s.stack)
  | ONamedGlobal n -> valid_src_operand8 o s

let valid_dst_operandf64 #vali #valf (o:operandf #vali #valf) (s:state) : ok_t =
  match o with
  | OConst_f n -> AstFailure
  | OReg_f r sz -> astcheck(sz = 8)
  | OMemRel_f m -> memcheck (valid_addr64 (eval_maddr m s) s.mem)
  | OStackRel_f m -> memcheck (valid_dst_stack64 s.stack_pointer (s.stack_pointer + m) s.stack)
  | ONamedGlobal_f (Ident_f n) -> valid_src_operandf64 o s
let valid_dst_operandf32 #vali #valf (o:operandf #vali #valf) (s:state) : ok_t =
  match o with
  | OConst_f n -> AstFailure
  | OReg_f r sz -> astcheck(sz = 4)
  | OMemRel_f m -> memcheck (valid_addr32 (eval_maddr m s) s.mem)
  | OStackRel_f m -> memcheck (valid_dst_stack32 s.stack_pointer (s.stack_pointer + m) s.stack)
  | ONamedGlobal_f (Ident_f n) -> valid_src_operandf32 o s

unfold
let update_operandi64 #vali (dst:operandi #vali) (v:nat64) :st_maintained unit =
  check (valid_dst_operand64 dst);;
  s <-- get;
  set (update_operand64' dst v s)
unfold
let update_operandi32 #vali (dst:operandi #vali) (v:nat32) :st_maintained unit =
  check (valid_dst_operand32 dst);;
  s <-- get;
  set (update_operand32' dst v s)
unfold
let update_operandi16 #vali (dst:operandi #vali) (v:nat16) :st_maintained unit =
  check (valid_dst_operand16 dst);;
  s <-- get;
  set (update_operand16' dst v s)
unfold
let update_operandi8 #vali (dst:operandi #vali) (v:nat8) :st_maintained unit =
  check (valid_dst_operand8 dst);;
  s <-- get;
  set (update_operand8' dst v s)

unfold
let read_operand64 #vali (src:operandi #vali) (s_orig:state) : st_maintained nat64 =
  check (valid_src_operand64 src);;
  return (eval_operand64 src s_orig)
unfold
let read_operand32 #vali (src:operandi #vali) (s_orig:state) : st_maintained nat32 =
  check (valid_src_operand32 src);;
  return (eval_operand32 src s_orig)
unfold
let read_operand16 #vali (src:operandi #vali) (s_orig:state) : st_maintained nat16 =
  check (valid_src_operand16 src);;
  return (eval_operand16 src s_orig)
unfold
let read_operand8 #vali (src:operandi #vali) (s_orig:state) : st_maintained nat8 =
  check (valid_src_operand8 src);;
  return (eval_operand8 src s_orig)

unfold
let update_operandf64 #vali #valf (dst:operandf #vali #valf) (v:float) :
  st_maintained unit =
  check (valid_dst_operandf64 dst);;
  s <-- get;
  set (update_operandf64' dst v s)
unfold
let update_operandf32 #vali #valf (dst:operandf #vali #valf) (v:float) :
  st_maintained unit =
  check (valid_dst_operandf32 dst);;
  s <-- get;
  set (update_operandf32' dst v s)

unfold
let read_operandf64 #vali #valf (src:operandf #vali #valf) (s_orig:state) :
  st_maintained float =
  check (valid_src_operandf64 src);;
  return (eval_operandf64 src s_orig)
unfold
let read_operandf32 #vali #valf (src:operandf #vali #valf) (s_orig:state) :
  st_maintained float =
  check (valid_src_operandf32 src);;
  return (eval_operandf32 src s_orig)
