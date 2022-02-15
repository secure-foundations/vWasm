module Semantics.Common.CFG.LowLevelSemantics

module L = FStar.List.Tot
open FStar.FunctionalExtensionality
open Types_s
open Common.Conversions
open Common.Memory

open Semantics.Common.CFG
open Semantics.Common.CFG.Instructions

/// Low level semantics for the CFG.
/// You will want to define
///
/// let eval_step (c:cfg) (s:state) = eval_step #_ #_ #_ #eval_ins c s
///
/// to use the semantics.

noeq
type state = {
  ok : ok_t;
  explicitly_safely_killed: bool;
  ip : loc;
  stack_pointer : int;
  reg_i : int ^-> nat64;
  reg_f : int ^-> float;
  mem : heap;
  stack : stack;
  callstack : list (loc * int * int * nat64); (* ret-location, init_rsp, stack pointer, rip-on-stack *)
  aux : aux;
  global_i : int ^-> nat64;
  global_f : int ^-> float;
  global_mem_pages : nat32;
}

unfold let trunc_64_to_32_bit (x:nat64) : nat32 = x % pow2_32
unfold let trunc_64_to_16_bit (x:nat64) : nat16 = x % pow2_16
unfold let trunc_64_to_8_bit (x:nat64) : nat8 = x % pow2_8

(* TODO: This maybe isn't quite right. Not sure if we support partial reads of floats. *)
let eval_regf64 #valf (r:regf #valf) (s:state) : float =
  s.reg_f r
let eval_regf32 #valf (r:regf #valf) (s:state) : float =
  s.reg_f r

let eval_reg64 #vali (r:regi #vali) (s:state) : nat64 =
  s.reg_i r
let eval_reg32 #vali (r:regi #vali) (s:state) : nat32 =
  trunc_64_to_32_bit (eval_reg64 r s)
let eval_reg16 #vali (r:regi #vali) (s:state) : nat16 =
  trunc_64_to_16_bit (eval_reg64 r s)
let eval_reg8 #vali (r:regi #vali) (s:state) : nat8 =
  trunc_64_to_8_bit (eval_reg64 r s)

let eval_global_i64 (n:nat) (s:state) : nat64 =
  s.global_i n
let eval_global_i32 (n:nat) (s:state) : nat64 =
  trunc_64_to_32_bit (eval_global_i64 n s)

(* TODO: Same here. *)
let eval_global_f64 (n:nat) (s:state) : float =
  s.global_f n
let eval_global_f32 (n:nat) (s:state) : float =
  s.global_f n

// TODO: Fix memory relative semantics
let eval_maddr #vali (m:maddr #vali) (s:state) : int =
  let open FStar.Mul in
  match m with
  //| MConst n -> n
  //| MReg reg offset -> (eval_reg64 reg s) + offset
  //| MIndex base scale index offset -> (eval_reg64 base s) + scale * (eval_reg64 index s) + offset
  | MIndex scale index offset -> scale * (eval_reg64 index s) + offset

unfold let eval_mem64 (ptr:int) (s:state) : nat64 = get_heap_val64 ptr s.mem
unfold let eval_mem32 (ptr:int) (s:state) : nat32 = get_heap_val32 ptr s.mem
unfold let eval_mem16 (ptr:int) (s:state) : nat16 = get_heap_val16 ptr s.mem
unfold let eval_mem8 (ptr:int) (s:state) : nat8 = get_heap_val8 ptr s.mem
unfold let eval_stack64 (ptr:int) (s:stack) : nat64 = get_heap_val64 ptr s.smem
unfold let eval_stack32 (ptr:int) (s:stack) : nat32 = get_heap_val32 ptr s.smem
unfold let eval_stack16 (ptr:int) (s:stack) : nat16 = get_heap_val16 ptr s.smem
unfold let eval_stack8 (ptr:int) (s:stack) : nat8 = get_heap_val8 ptr s.smem

let eval_operand64 #vali (o:operandi #vali) (s:state) : nat64 =
  match o with
  | OConst n -> int_to_nat64 n
  | OReg r _ -> eval_reg64 r s
  | OMemRel m -> eval_mem64 (eval_maddr m s) s
  | OStackRel m -> eval_stack64 (s.stack_pointer + m) s.stack
  | ONamedGlobal (Ident n) -> eval_global_i64 n s
  | ONamedGlobal MemPages -> s.global_mem_pages
let eval_operand32 #vali (o:operandi #vali) (s:state) : nat32 =
  match o with
  | OConst n -> int_to_nat32 n
  | OReg r _ -> eval_reg32 r s
  | OMemRel m -> eval_mem32 (eval_maddr m s) s
  | OStackRel m -> eval_stack32 (s.stack_pointer + m) s.stack
  | ONamedGlobal (Ident n) -> eval_global_i32 n s
  | ONamedGlobal MemPages -> s.global_mem_pages
let eval_operand16 #vali (o:operandi #vali) (s:state) : nat16 =
  match o with
  | OConst n -> int_to_nat16 n
  | OReg r _ -> eval_reg16 r s
  | OMemRel m -> eval_mem16 (eval_maddr m s) s
  | OStackRel m -> eval_stack16 (s.stack_pointer + m) s.stack
  | ONamedGlobal _ -> admit () (* Will never be called. Explicitly underspecified. *)
let eval_operand8 #vali (o:operandi #vali) (s:state) : nat8 =
  match o with
  | OConst n -> int_to_nat8 n
  | OReg r _ -> eval_reg8 r s
  | OMemRel m -> eval_mem8 (eval_maddr m s) s
  | OStackRel m -> eval_stack8 (s.stack_pointer + m) s.stack
  | ONamedGlobal _ -> admit () (* Will never be called. Explicitly underspecified. *)

let itof64 (n:nat64): float = admit() (* Explicitly underspecified *)
let itof32 (n:nat32): float = admit() (* Explicitly underspecified *)
let ftoi64 (f:float): nat64 = admit() (* Explicitly underspecified *)
let ftoi32 (f:float): nat32 = admit() (* Explicitly underspecified *)

let eval_operandf64 #vali #valf (o:operandf #vali #valf) (s:state) : float =
  match o with
  | OConst_f f -> f
  | OReg_f r _ -> eval_regf64 r s
  | OMemRel_f m -> itof64 (eval_mem64 (eval_maddr m s) s)
  | OStackRel_f m -> itof64 (eval_stack64 (s.stack_pointer + m) s.stack)
  | ONamedGlobal_f (Ident_f n) -> eval_global_f64 n s

let eval_operandf32 #vali #valf (o:operandf #vali #valf) (s:state) : float =
  match o with
  | OConst_f f -> f
  | OReg_f r _ -> eval_regf32 r s
  | OMemRel_f m -> itof32 (eval_mem32 (eval_maddr m s) s)
  | OStackRel_f m -> itof32 (eval_stack32 (s.stack_pointer + m) s.stack)
  | ONamedGlobal_f (Ident_f n) -> eval_global_f32 n s

let valid_src_stack64 (ptr:int) (st:stack) : bool =
  valid_addr64 ptr st.smem
let valid_src_stack32 (ptr:int) (st:stack) : bool =
  valid_addr32 ptr st.smem
let valid_src_stack16 (ptr:int) (st:stack) : bool =
  valid_addr16 ptr st.smem
let valid_src_stack8 (ptr:int) (st:stack) : bool =
  valid_addr8 ptr st.smem

(* NB: I believe you need to read/write the exact size from the appropriate global. *)
let valid_src_operand64 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AllOk
  | OReg r sz -> astcheck (vali r && sz = 8)
  | OMemRel m -> memcheck (valid_addr64 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_src_stack64 (s.stack_pointer + m) s.stack)
  | ONamedGlobal (Ident n) ->
    astcheck (0 <= n && n < L.length s.aux.globals &&
              (L.index s.aux.globals n).gbl_ty = I64_ty)
  | ONamedGlobal MemPages -> AstFailure
let valid_src_operand32 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AllOk
  | OReg r sz -> astcheck (vali r && sz = 4)
  | OMemRel m -> memcheck (valid_addr32 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_src_stack32 (s.stack_pointer + m) s.stack)
  | ONamedGlobal (Ident n) ->
    astcheck (0 <= n && n < L.length s.aux.globals &&
              (L.index s.aux.globals n).gbl_ty = I32_ty)
  | ONamedGlobal MemPages -> AllOk
let valid_src_operand16 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AllOk
  | OReg r sz -> astcheck (vali r && sz = 2)
  | OMemRel m -> memcheck (valid_addr16 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_src_stack16 (s.stack_pointer + m) s.stack)
  | ONamedGlobal _ -> AstFailure (* XXX: Is this correct *)
let valid_src_operand8 #vali (o:operandi #vali) (s:state) : ok_t =
  match o with
  | OConst n -> AllOk
  | OReg r sz -> astcheck (vali r && sz = 1)
  | OMemRel m -> memcheck (valid_addr8 (eval_maddr m s) s.mem)
  | OStackRel m -> memcheck (valid_src_stack8 (s.stack_pointer + m) s.stack)
  | ONamedGlobal _ -> AstFailure (* XXX: Is this correct *)

let valid_src_operandf64 #vali #valf (o:operandf #vali #valf) (s:state) : ok_t =
  match o with
  | OConst_f f -> AllOk
  | OReg_f r sz -> astcheck (valf r && sz = 8)
  | OMemRel_f m -> memcheck (valid_addr64 (eval_maddr m s) s.mem)
  | OStackRel_f m -> memcheck (valid_src_stack64 (s.stack_pointer + m) s.stack)
  | ONamedGlobal_f (Ident_f n) ->
    astcheck (0 <= n && n < L.length s.aux.globals &&
              (L.index s.aux.globals n).gbl_ty = F64_ty)
let valid_src_operandf32 #vali #valf (o:operandf #vali #valf) (s:state) : ok_t =
  match o with
  | OConst_f n -> AllOk
  | OReg_f r sz -> astcheck (valf r && sz = 4)
  | OMemRel_f m -> memcheck (valid_addr32 (eval_maddr m s) s.mem)
  | OStackRel_f m -> memcheck (valid_src_stack32 (s.stack_pointer + m) s.stack)
  | ONamedGlobal_f (Ident_f n) ->
    astcheck (0 <= n && n < L.length s.aux.globals &&
              (L.index s.aux.globals n).gbl_ty = F32_ty)

let valid_ocmp #vali #valf (c:ocmp #vali #valf) (s:state) : ok_t =
  match c with
  (* 32 bit comparisons *)
  | OEq32  o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | ONe32  o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OLe32  o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OGe32  o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OLt32  o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OGt32  o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s

  | OLeS32 o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OGeS32 o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OLtS32 o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  | OGtS32 o1 o2 -> valid_src_operand32 o1 s `ok_join` valid_src_operand32 o2 s
  (* 64 bit comparisons *)
  | OEq64  o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | ONe64  o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OLe64  o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OGe64  o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OLt64  o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OGt64  o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s

  | OLeS64 o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OGeS64 o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OLtS64 o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  | OGtS64 o1 o2 -> valid_src_operand64 o1 s `ok_join` valid_src_operand64 o2 s
  (* 32 bit floats *)
  | OFEq32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf32 o2 s
  | OFNe32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf32 o2 s
  | OFLt32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf32 o2 s
  | OFGt32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf32 o2 s
  | OFLe32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf32 o2 s
  | OFGe32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf32 o2 s
  (* 64 bit floats *)
  | OFEq64 o1 o2 -> valid_src_operandf64 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFNe64 o1 o2 -> valid_src_operandf64 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFLt64 o1 o2 -> valid_src_operandf64 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFGt64 o1 o2 -> valid_src_operandf64 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFLe64 o1 o2 -> valid_src_operandf64 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFGe64 o1 o2 -> valid_src_operandf64 o1 s `ok_join` valid_src_operandf64 o2 s

type comparison_result =
  | Lt
  | Gt
  | Eq
type comparison_resultf =
  | FLt
  | FGt
  | FEq
  | FNaN

let compare_float (v1 v2:float) : Tot comparison_resultf =
  admit () (* Explicitly underspecified *)
let compare_signed_i32 (v1 v2:nat32) : Tot comparison_result =
  admit () (* Explicitly underspecified *)
let compare_signed_i64 (v1 v2:nat64) : Tot comparison_result =
  admit () (* Explicitly underspecified *)

unfold
let proceed (ip:loc) (s:state) =
  { s with ip = ip }

let check_valid_ocmp #vali #valf (o:ocmp #vali #valf) (s:state) : state =
  { s with ok = valid_ocmp o s }

let eval_ocmp #vali #valf (o:ocmp #vali #valf) (s:state) : bool =
  match o with
  | OEq64 o1 o2 -> eval_operand64 o1 s = eval_operand64 o2 s
  | ONe64 o1 o2 -> eval_operand64 o1 s <> eval_operand64 o2 s
  | OLe64 o1 o2 -> eval_operand64 o1 s <= eval_operand64 o2 s
  | OGe64 o1 o2 -> eval_operand64 o1 s >= eval_operand64 o2 s
  | OLt64 o1 o2 -> eval_operand64 o1 s < eval_operand64 o2 s
  | OGt64 o1 o2 -> eval_operand64 o1 s > eval_operand64 o2 s
  | OEq32 o1 o2 -> eval_operand32 o1 s = eval_operand32 o2 s
  | ONe32 o1 o2 -> eval_operand32 o1 s <> eval_operand32 o2 s
  | OLe32 o1 o2 -> eval_operand32 o1 s <= eval_operand32 o2 s
  | OGe32 o1 o2 -> eval_operand32 o1 s >= eval_operand32 o2 s
  | OLt32 o1 o2 -> eval_operand32 o1 s < eval_operand32 o2 s
  | OGt32 o1 o2 -> eval_operand32 o1 s > eval_operand32 o2 s
  (* Explicitly underspecified *)
  | OLeS32 o1 o2 -> compare_signed_i32 (eval_operand32 o1 s) (eval_operand32 o2 s) <> Gt
  | OGeS32 o1 o2 -> compare_signed_i32 (eval_operand32 o1 s) (eval_operand32 o2 s) <> Lt
  | OLtS32 o1 o2 -> compare_signed_i32 (eval_operand32 o1 s) (eval_operand32 o2 s) = Lt
  | OGtS32 o1 o2 -> compare_signed_i32 (eval_operand32 o1 s) (eval_operand32 o2 s) = Gt
  | OLeS64 o1 o2 -> compare_signed_i64 (eval_operand64 o1 s) (eval_operand64 o2 s) <> Gt
  | OGeS64 o1 o2 -> compare_signed_i64 (eval_operand64 o1 s) (eval_operand64 o2 s) <> Lt
  | OLtS64 o1 o2 -> compare_signed_i64 (eval_operand64 o1 s) (eval_operand64 o2 s) = Lt
  | OGtS64 o1 o2 -> compare_signed_i64 (eval_operand64 o1 s) (eval_operand64 o2 s) = Gt

  | OFEq32 o1 o2
  | OFNe32 o1 o2
  | OFLt32 o1 o2
  | OFGt32 o1 o2
  | OFLe32 o1 o2
  | OFGe32 o1 o2
    -> (
        let cmp = compare_float (eval_operandf32 o1 s) (eval_operandf32 o2 s) in
        match o with
        | OFEq32 _ _ -> cmp = FEq
        | OFNe32 _ _ -> cmp = FLt || cmp = FGt
        | OFLt32 _ _ -> cmp = FLt
        | OFGt32 _ _ -> cmp = FGt
        | OFLe32 _ _ -> cmp = FEq || cmp = FLt
        | OFGe32 _ _ -> cmp = FEq || cmp = FGt
      )
  | OFEq64 o1 o2
  | OFNe64 o1 o2
  | OFLt64 o1 o2
  | OFGt64 o1 o2
  | OFLe64 o1 o2
  | OFGe64 o1 o2
    -> (
        let cmp = compare_float (eval_operandf64 o1 s) (eval_operandf64 o2 s) in
        match o with
        | OFEq64 _ _ -> cmp = FEq
        | OFNe64 _ _ -> cmp = FLt || cmp = FGt
        | OFLt64 _ _ -> cmp = FLt
        | OFGt64 _ _ -> cmp = FGt
        | OFLe64 _ _ -> cmp = FEq || cmp = FLt
        | OFGe64 _ _ -> cmp = FEq || cmp = FGt
      )

unfold
let update_stack64' (ptr:int) (v:nat64) (s:stack) : stack =
  { s with smem = update_heap64 ptr v s.smem }
unfold
let update_stack32' (ptr:int) (v:nat32) (s:stack) : stack =
  { s with smem = update_heap32 ptr v s.smem }
unfold
let update_stack16' (ptr:int) (v:nat16) (s:stack) : stack =
  { s with smem = update_heap16 ptr v s.smem }
unfold
let update_stack8' (ptr:int) (v:nat8) (s:stack) : stack =
  { s with smem = update_heap8 ptr v s.smem }

let update_stack64 (ptr:int) (v:nat64) (s:state) : state =
  // We can only write the stack between the current stack pointer and
  // the initial stack pointer. Everything above is read-only
  if (ptr >= s.stack_pointer && ptr + 8 <= s.stack.init_rsp) then (
    {s with stack = update_stack64' ptr v s.stack}
  ) else
    // If we are in this case, a previous check set the ok field to false
    s
let update_stack32 (ptr:int) (v:nat32) (s:state) : state =
  // We can only write the stack between the current stack pointer and
  // the initial stack pointer. Everything above is read-only
  if (ptr >= s.stack_pointer && ptr + 4 <= s.stack.init_rsp) then (
    {s with stack = update_stack32' ptr v s.stack}
  ) else
    // If we are in this case, a previous check set the ok field to false
    s
let update_stack16 (ptr:int) (v:nat16) (s:state) : state =
  // We can only write the stack between the current stack pointer and
  // the initial stack pointer. Everything above is read-only
  if (ptr >= s.stack_pointer && ptr + 2 <= s.stack.init_rsp) then (
    {s with stack = update_stack16' ptr v s.stack}
  ) else
    // If we are in this case, a previous check set the ok field to false
    s
let update_stack8 (ptr:int) (v:nat8) (s:state) : state =
  // We can only write the stack between the current stack pointer and
  // the initial stack pointer. Everything above is read-only
  if (ptr >= s.stack_pointer && ptr + 1 <= s.stack.init_rsp) then (
    {s with stack = update_stack8' ptr v s.stack}
  ) else
    // If we are in this case, a previous check set the ok field to false
    s

let free_stack (start finish:int) (st:stack) : stack =
  let domain = Map.domain st.smem in
  // Returns the domain, without elements between start and finish
  let restricted_domain = Vale.Set.remove_between domain start finish in
  // The new domain of the stack does not contain elements between start and finish
  let new_mem = Map.restrict restricted_domain st.smem in
  { st with smem = new_mem }

assume val havoc_ip : (#int_t:eqtype) -> (s:state) -> int_t

let same_valid_addrs (h1 h2:heap) : GTot prop =
  (forall addr. {:pattern (valid_addr addr h2)} valid_addr addr h1 = valid_addr addr h2)

let same_stack_above_rsp (s1 s2:state) : GTot prop =
  (s2.stack_pointer = s1.stack_pointer) /\
  (same_valid_addrs s1.stack.smem s2.stack.smem) /\
  (s2.stack.init_rsp = s1.stack.init_rsp) /\
  (forall addr. {:pattern (eval_stack8 addr s2.stack)}
     addr >= s1.stack_pointer ==> eval_stack8 addr s2.stack = eval_stack8 addr s1.stack)

assume val havoc_state_for_external_call (s1:state) (call_name:nat) :
  Pure state
    (requires (True))
    (ensures (fun s2 ->
         (s2.ok = s1.ok) /\
         (s2.explicitly_safely_killed = s1.explicitly_safely_killed) /\
         (s2.ip = s1.ip) /\
         (* s2.reg_i and s2.reg_f need not have any relation to s1 *)
         (same_valid_addrs s1.mem s2.mem) /\
         (same_stack_above_rsp s1 s2) /\
         (s2.callstack = s1.callstack) /\
         (s2.aux = s1.aux) /\
         (* s1.global_i and s2.global_f need not have any relation to s1 *)
         (s2.global_mem_pages = s1.global_mem_pages)
       ))

assume val axiom_external_call_ip_irrelevance (s1 s2:state) (call_name:nat) :
  Lemma
    (requires (s2 == {s1 with ip = s2.ip}))
    (ensures (
        let s1' = havoc_state_for_external_call s1 call_name in
        let s2' = havoc_state_for_external_call s2 call_name in
        s2' == {s1' with ip = s2'.ip}))

let is_imported_function (a:aux) (n:int) : Tot bool =
  Some? (FStar.List.Tot.find (fun f -> f.fn_name = n && f.fn_isImported) a.fns)

let find_call_name #vali (target:target_t #vali) (s:state) :
  Tot (option nat) =
  match target with
  | CallDirect n -> Some n
  | CallIndirect r ->
    let n = s.reg_i r in
    if n < L.length s.aux.call_table.call_init then (
      match L.index s.aux.call_table.call_init n with
      | Some idx -> Some idx
      | None -> None
    ) else (
      None
    )

let rec find_real_fn_entry #inst #vali #valf (fn_name:nat) (c:cfg #inst #vali #valf) :
  Tot (option nat) =
  match c with
  | [] -> None
  | h :: t ->
    match h with
    | FnEntry name next -> (
        if name = fn_name then (
          Some next
        ) else (
          find_real_fn_entry fn_name t
        )
      )
    | _ -> find_real_fn_entry fn_name t

let find_call_target #inst #vali #valf (target:target_t #vali) (s:state) (c:cfg #inst #vali #valf) :
  Tot (loc * ok_t) =
  let fn_name = find_call_name target s in
  match fn_name with
  | Some fn_name -> (
      match find_real_fn_entry fn_name c with
      | Some next -> next, AllOk
      | None -> s.ip, AstFailure
    )
  | None -> s.ip, AstFailure

let is_imported_function_target #vali (target:target_t #vali) (s:state) : Tot bool =
  match find_call_name target s with
  | None -> false
  | Some fn_name -> is_imported_function s.aux fn_name

let is_explicitly_safely_killed_target #vali (target:target_t #vali) (s:state) : Tot bool =
  match target with
  | CallDirect _ -> false
  | CallIndirect r ->
    let n = s.reg_i r in
    if n < L.length s.aux.call_table.call_init then (
      None? (L.index s.aux.call_table.call_init n)
    ) else (
      false
    )

let rec eval_inss (#inst:eqtype) (#f:(inst -> s:state -> (s_new:state{s.ip = s_new.ip}))) (is:list inst) (s:state) : (s_new:state{s_new.ip = s.ip}) =
  match is with
  | [] -> s
  | x :: xs -> eval_inss #_ #f xs (f x s)

(** Partially perform a single (small) step evaluation of the
    code. Does not impact ip, but mentions what it'll be next.

    NOTE: If current execution is a call, then it simply steps into
          function, and does not do a "multi-step" evaluation of the
          entire function. *)
val eval_step' :
  (#inst:eqtype) ->
  (#vali:(int -> bool)) ->
  (#valf:(int -> bool)) ->
  (#eval_ins:(inst -> s:state -> (s_new:state{s.ip = s_new.ip}))) ->
  (c:cfg #inst #vali #valf) -> (p:precode #inst #vali #valf) -> (s:state) ->
  (sip:(state & loc){(fst sip).ip = s.ip})

let eval_step' #_ #vali #valf #eval_ins c p s =
  match p with
  | FnEntry _ next -> (s, next)
  | FnExit _ ->
    (* End of function sentinel should not be executed *)
    ({ s with ok = AstFailure }, s.ip)
  | Ins i next -> (eval_ins i s, next)
  | InsList is next -> (eval_inss #_ #eval_ins is s, next)
  | Nop next -> (s, next)
  | Cmp cond nextTrue nextFalse ->
    let s = check_valid_ocmp cond s in
    if eval_ocmp cond s then
      (s, nextTrue)
    else
      (s, nextFalse)
  | Switch case_table case ->
    if case_table < L.length s.aux.br_tables then (
      let tbl = L.index s.aux.br_tables case_table in
      if vali case then (
        let target = eval_reg64 case s in
        if target < L.length tbl.br_targets then (
          (s, L.index tbl.br_targets target)
        ) else (
          (* Invalid switch *)
          ({ s with ok = AstFailure }, s.ip)
        )
      ) else (
        (* Not a valid register *)
        ({ s with ok = AstFailure }, s.ip)
      )
    ) else (
      (* Non-existent table *)
      ({ s with ok = AstFailure }, s.ip)
    )
  | Call target next -> (
      if is_imported_function_target target s then
        (havoc_state_for_external_call s (Some?.v (find_call_name target s)), next) else
      if is_explicitly_safely_killed_target target s then
        ({ s with explicitly_safely_killed = true }, next) else
      match find_call_target target s c with
      | callee_loc, AllOk ->
        let rip_on_stack = havoc_ip ({s with ip=next}) in
        let current_init_rsp = s.stack.init_rsp in
        let current_rsp = s.stack_pointer in
        let new_rsp = current_rsp - 8 in
        let new_stack = update_stack64' new_rsp rip_on_stack
            ({ s.stack with init_rsp = new_rsp }) in
        ({ s with
           stack_pointer = new_rsp ;
           stack = new_stack ;
           callstack = (next, current_init_rsp, current_rsp, rip_on_stack) :: s.callstack ;
         },
         callee_loc)
      | _, failure ->
        ({ s with ok = failure }, s.ip)
    )
  | Ret _ -> (
      match s.callstack with
      | [] -> ({ s with ok = AstFailure }, s.ip)
      | ((next, prev_init_rsp, prev_rsp, rip_on_stack) :: prev_callstack) ->
        let current_init_rsp = s.stack.init_rsp in
        let current_rsp = s.stack_pointer in
        let new_rsp = current_rsp + 8 in
        if current_init_rsp = prev_init_rsp && new_rsp = prev_rsp then (
          if eval_stack64 current_rsp s.stack = rip_on_stack then (
            ({ s with
               stack_pointer = prev_rsp ;
               stack = free_stack current_rsp prev_rsp s.stack ;
               callstack = prev_callstack ;
             },
             next)
          ) else (
            ({ s with ok = AstFailure }, s.ip)
          )
        ) else (
          ({ s with ok = AstFailure }, s.ip)
        )
    )
  | HighCall _ _ _ _
  | HighRet _ _ ->
    (* Not part of the low-level semantics *)
    ({ s with ok = AstFailure }, s.ip)

(** Perform a single (small) step evaluation of the code in the cfg. *)
val eval_step :
  (#inst:eqtype) ->
  (#vali:(int -> bool)) ->
  (#valf:(int -> bool)) ->
  (#eval_ins:(inst -> s:state -> (s_new:state{s.ip = s_new.ip}))) ->
  (c:cfg #inst #vali #valf) -> (s:state) ->
  state

let eval_step #_ #vali #valf #eval_ins c s =
  if s.ok = AllOk then (
    if s.explicitly_safely_killed then (
      s
    ) else (
      if s.ip `in_cfg` c then (
        let s1, ip = eval_step' #_ #vali #valf #eval_ins c (get_code_at s.ip c) s in
        proceed ip s1
      ) else (
        { s with ok = AstFailure }
      )
    )
  ) else (
    s
  )
