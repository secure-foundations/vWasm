module Semantics.Common.CFG.HighLevelSemantics

module L = FStar.List.Tot
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality
open Types_s
open Common.Conversions
open Common.Memory

open Semantics.Common.CFG

/// High level semantics for the CFG.
/// You will want to define
///
/// let eval_step (c:cfg) (s:state) = eval_step #_ #_ #_ #eval_ins c s
///
/// to use the semantics.

noeq
type frame = {
  frame_next: loc;
  frame_init_rsp: int;
  frame_rsp: int;
  frame_retval_store: option ins_arg;
  frame_reg_i: int ^-> nat64;
  frame_reg_f: int ^-> float;
}

noeq
type state = {
  ok : ok_t;
  ip : loc;
  stack_pointer : int;
  reg_i : int ^-> nat64;
  reg_f : int ^-> float;
  mem : heap;
  stack : stack;
  callstack : list frame;
  aux : aux;
  global_i : int ^-> nat64;
  global_f : int ^-> float;
  global_mem_pages : nat32;
}

unfold let trunc_64_to_32_bit (x:nat64) : nat32 = x % pow2_32

(* TODO: This maybe isn't quite right. Not sure if we support partial reads of floats. *)
let eval_regf64 #valf (r:regf #valf) (s:state) : float =
  s.reg_f r
let eval_regf32 #valf (r:regf #valf) (s:state) : float =
  s.reg_f r

let eval_reg64 #vali (r:regi #vali) (s:state) : nat64 =
  s.reg_i r
let eval_reg32 #vali (r:regi #vali) (s:state) : nat32 =
  trunc_64_to_32_bit (eval_reg64 r s)

let eval_global_i64 (n:nat) (s:state) : nat64 =
  s.global_i n
let eval_global_i32 (n:nat) (s:state) : nat64 =
  trunc_64_to_32_bit (eval_global_i64 n s)

(* TODO: Same here. *)
let eval_global_f64 (n:nat) (s:state) : float =
  s.global_f n
let eval_global_f32 (n:nat) (s:state) : float =
  s.global_f n

// TODO: Fix semantics here for relative memory
let eval_maddr #vali (m:maddr #vali) (s:state) : int =
  let open FStar.Mul in
  match m with
  //| MConst n -> n
  //| MReg reg offset -> (eval_reg64 reg s) + offset
  //| MIndex scale index offset -> (eval_reg64 base s) + scale * (eval_reg64 index s) + offset
  | MIndex scale index offset ->
    scale * (eval_reg32 index s) + offset

unfold let eval_mem64 (ptr:int) (s:state) : nat64 = get_heap_val64 ptr s.mem
unfold let eval_mem32 (ptr:int) (s:state) : nat32 = get_heap_val32 ptr s.mem
unfold let eval_stack64 (ptr:int) (s:stack) : nat64 = get_heap_val64 ptr s.smem
unfold let eval_stack32 (ptr:int) (s:stack) : nat32 = get_heap_val32 ptr s.smem

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
  | OFEq32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFNe32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFLt32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFGt32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFLe32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf64 o2 s
  | OFGe32 o1 o2 -> valid_src_operandf32 o1 s `ok_join` valid_src_operandf64 o2 s
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

let free_stack (start finish:int) (st:stack) : stack =
  let domain = Map.domain st.smem in
  // Returns the domain, without elements between start and finish
  let restricted_domain = Vale.Set.remove_between domain start finish in
  // The new domain of the stack does not contain elements between start and finish
  let new_mem = Map.restrict restricted_domain st.smem in
  { st with smem = new_mem }

assume
val havoc_ip :
  (#ins_t:eqtype) -> (#vali:(int -> bool)) -> (#valf:(int -> bool)) -> (#int_t:eqtype) ->
  (l:loc) -> (c:cfg #ins_t #vali #valf) -> int_t

let find_call_target #inst #vali #valf (target:target_t #vali) (s:state) (c:cfg #inst #vali #valf) :
  Tot (loc * ok_t) =
  let fn_name =
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
  in
  match fn_name with
  | Some fn_name -> (
      match L.find (fun (x:precode #inst #vali #valf) ->
          (FnEntry? x && FnEntry?.name x = fn_name)) c with
      | Some (FnEntry name next) ->
        assert (name = fn_name);
        next, AllOk
      | None -> s.ip, AstFailure
    )
  | None -> s.ip, AstFailure

assume
val havoc_nat64 (s:state) (r:int) : nat64

assume
val havoc_float (s:state) (r:int) : float

let rec args_are_valid
  (#vali:(int -> bool))
  (#valf:(int -> bool))
  (args:list ins_arg) :
  bool =
  match args with
  | [] -> true
  | arg :: args ->
    let b =
      match arg with
      | ArgInt r _ -> vali r
      | ArgFloat r _ -> valf r
    in
    b && args_are_valid #vali #valf args

// TODO: Need fix for 32/64 args?
let rec create_args
  (#vali:(int -> bool))
  (#valf:(int -> bool))
  (args:list ins_arg{args_are_valid #vali #valf args})
  (idx:nat)
  (s:state) :
  ((int ^-> nat64) * (int ^-> float)) =
  match args with
  | [] ->
    let ri = F.on_dom int (fun r -> havoc_nat64 s r) in
    let rf = F.on_dom int (fun r -> havoc_float s r) in
    ri, rf
  | arg :: args ->
    let ri, rf = create_args #vali #valf args (idx + 1) s in
    match arg with
    | ArgInt r _ ->
      let v = s.reg_i r in
      let ri' = F.on_dom int (fun r -> if r = idx then v else ri r) in
      ri', rf
    | ArgFloat r _ ->
      let v = s.reg_f r in
      let rf' = F.on_dom int (fun r -> if r = idx then v else rf r) in
      ri, rf'

let rec eval_inss (#inst:eqtype) (#f:(inst -> s:state -> (s_new:state{s.ip = s_new.ip}))) (is:list inst) (s:state) =
  match is with
  | [] -> s
  | x :: xs -> eval_inss #_ #f xs (f x s)

(** Perform a single (small) step evaluation of the code in the cfg.

    NOTE: If current execution is a call, then it simply steps into
          function, and does not do a "multi-step" evaluation of the
          entire function. *)
val eval_step :
  (#inst:eqtype) ->
  (#vali:(int -> bool)) ->
  (#valf:(int -> bool)) ->
  (#eval_ins:(inst -> s:state -> (s_new:state{s.ip = s_new.ip}))) ->
  (c:cfg #inst #vali #valf) -> (s:state) ->
  state

let eval_step #_ #vali #valf #eval_ins c s =
  if s.ok = AllOk then (
    if s.ip `in_cfg` c then (
      match get_code_at s.ip c with
      | FnEntry _ next -> proceed next s
      | FnExit _ ->
        (* End of function sentinel should not be executed *)
      	{ s with ok = AstFailure }
      | Ins i next -> proceed next (eval_ins i s)
      | InsList is next -> proceed next (eval_inss #_ #eval_ins is s)
      | Nop next -> proceed next s
      | Cmp cond nextTrue nextFalse ->
        let s = check_valid_ocmp cond s in
        if eval_ocmp cond s then
          proceed nextTrue s
        else
          proceed nextFalse s
      | Switch case_table case ->
        if case_table < L.length s.aux.br_tables then (
          let tbl = L.index s.aux.br_tables case_table in
          if vali case then (
            let target = eval_reg64 case s in
            if target < L.length tbl.br_targets then (
              proceed (L.index tbl.br_targets target) s
            ) else (
              (* Invalid switch *)
              { s with ok = AstFailure }
            )
          ) else (
            (* Not a valid register *)
            { s with ok = AstFailure }
          )
        ) else (
          (* Non-existent table *)
          { s with ok = AstFailure }
        )
      | HighCall target args retval_store next -> (
          match find_call_target target s c with
          | callee_loc, AllOk ->
            if not (args_are_valid #vali #valf args) then (
              (* Bad registers in arguments *)
              { s with ok = AstFailure }
            ) else (
              let current_init_rsp = s.stack.init_rsp in
              let current_rsp = s.stack_pointer in
              let new_rsp = current_rsp - 8 in
              let new_stack =
                update_stack64' new_rsp (havoc_ip next c)
                  ({ s.stack with init_rsp = new_rsp })
              in
              let new_reg_i, new_reg_f = create_args #vali #valf args 0 s in
              let saved_frame = {
                frame_next = next;
                frame_init_rsp = current_init_rsp;
                frame_rsp = current_rsp;
                frame_retval_store = retval_store;
                frame_reg_i = s.reg_i;
                frame_reg_f = s.reg_f;
              }
              in
              { s with
                ip = callee_loc ;
                stack_pointer = new_rsp ;
                reg_i = new_reg_i ;
                reg_f = new_reg_f ;
                stack = new_stack ;
                callstack = saved_frame :: s.callstack ; }
            )
          | _, failure ->
            { s with ok = failure }
        )
      // TODO: Need fix for 32/64 args?
      | HighRet retval_load _ -> (
          match s.callstack with
          | saved_frame :: prev_callstack ->
            let {frame_next; frame_init_rsp; frame_rsp;
                 frame_retval_store; frame_reg_i; frame_reg_f} = saved_frame
            in
            let current_init_rsp = s.stack.init_rsp in
            let current_rsp = s.stack_pointer in
            let new_rsp = current_rsp + 8 in
            let regfiles: option ((int ^-> nat64) * (int ^-> float)) =
              match retval_load, frame_retval_store with
              | None, None -> Some (frame_reg_i, frame_reg_f)
              | Some (ArgInt r_load _), Some (ArgInt r_store _) ->
                if not (vali r_load) then None else (
                  let v = s.reg_i r_load in
                  let ri: (int ^-> nat64) = frame_reg_i in // Make typechecker happy
                  let frame_reg_i' =
                    F.on_dom int (fun r -> if r = r_store then v else ri r)
                  in
                  Some (frame_reg_i', frame_reg_f)
                )
              | Some (ArgFloat r_load _), Some (ArgFloat r_store _) ->
                if not (valf r_load) then None else (
                  let v = s.reg_f r_load in
                  let rf: (int ^-> float) = frame_reg_f in // Make typechecker happy
                  let frame_reg_f' =
                    F.on_dom int (fun r -> if r = r_store then v else rf r)
                  in
                  Some (frame_reg_i, frame_reg_f')
                )
              | _, _ ->
                None
            in
            if current_init_rsp = frame_init_rsp && new_rsp = frame_rsp then (
              if eval_stack64 current_rsp s.stack = havoc_ip frame_next c && Some? regfiles then (
                let frame_reg_i', frame_reg_f' = Some?.v regfiles in
                { s with
                ip = frame_next ;
                stack_pointer = frame_rsp ;
                reg_i = frame_reg_i' ;
                reg_f = frame_reg_f' ;
                stack = free_stack current_rsp frame_rsp s.stack ;
                callstack = prev_callstack ; }
              ) else (
                { s with ok = AstFailure }
              )
            ) else (
              { s with ok = AstFailure }
            )
          | _ -> { s with ok = AstFailure }
        )
      | Call _ _
      | Ret _ ->
        // Not part of high-level semantics
        { s with ok = AstFailure }
    ) else (
      { s with ok = AstFailure }
    )
  ) else (
    s
  )
