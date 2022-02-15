module Compiler.Linearizer

open FStar.Ghost
open FStar.Tactics

open FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open Common.Err
open Common.Memory
open Semantics.Common.CFG
open Semantics.Common.CFG.Printer
open Semantics.Common.CFG.LowLevelSemantics
open Semantics.Common.CFG.Instructions

open Types_s
open Words_s
open TypesNative_s

open I2.Semantics
module U = Semantics.Common.CFG.Utils
module I = Semantics.Common.CFG.LLInstructionSemantics

#reset-options "--fuel 1 --ifuel 1"

type numbering = {
  next: nat;
  visited: list bool;
  ordering: list (option nat);
}

(** Sets the value in the list at index [n] to [v]. If values before
    it don't exist, they are set to the default value [default_v] *)
let rec update_index #t (l:list t) (default_v:t) (n:nat) (v:t) : list t =
  if n = 0 then (
    match l with
    | [] -> [v]
    | hd :: tl -> v :: tl
  ) else (
    match l with
    | [] -> default_v :: update_index [] default_v (n-1) v
    | hd :: tl -> hd :: update_index tl default_v (n-1) v
  )

let metric_numbering (c:cfg) (n:numbering) : nat =
  let l1 = length c in
  let l2 = count true n.visited in
  if l1 >= l2 then (
    l1 - l2
  ) else (
    0
  )

let rec lemma_count_less_than_length (#t:eqtype) (x:t) (l:list t) :
  Lemma
    (ensures (count x l <= length l)) =
  match l with
  | [] -> ()
  | h :: t -> lemma_count_less_than_length x t

let rec lemma_update_visited (l:list bool) (i:nat) :
  Lemma
    (ensures (
        let l2 = update_index l false i true in
        if i < length l then (
          nth l i = Some (index l i) /\
          count true l2 = count true l + (if index l i then 0 else 1) /\
          length l2 = length l
        ) else (
          count true l2 = count true l + 1 /\
          length l2 = i + 1
        ))) =
  match i with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> lemma_update_visited [] (i-1)
    | hd :: tl -> lemma_update_visited tl (i-1)

let rec lemma_update_ordering (l:list (option nat)) (i:nat) (v:nat) :
  Lemma
    (ensures (
        let l2 = update_index l None i (Some v) in
        if i < length l then (
          nth l i = Some (index l i) /\
          length l2 = length l
        ) else (
          length l2 = i + 1
        ))) =
  match i with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> lemma_update_ordering [] (i-1) v
    | hd :: tl -> lemma_update_ordering tl (i-1) v

unfold
let visit (c:cfg) (n:numbering) (i:nat) :
  Pure numbering
    (requires (
        (i < length c) /\
        (length n.visited <= length c) /\
        (match nth n.visited i with
         | None -> True
         | Some v -> not v)))
    (ensures (fun n2 ->
         metric_numbering c n2 < metric_numbering c n /\
         length n2.visited <= length c)) =
  let n2 = { n with visited = update_index n.visited false i true } in
  lemma_update_visited n.visited i;
  lemma_count_less_than_length true n.visited;
  lemma_count_less_than_length true n2.visited;
  n2

unfold
let is_visited (n:numbering) (i:nat) : Tot bool =
  match nth n.visited i with
  | None -> false
  | Some v -> v

#push-options "--z3rlimit 20"
let rec post_order_numbering (a:aux) (c:cfg) (current_idx:nat) (n:numbering) :
  Err numbering
    (requires (
        (length n.visited <= length c) /\
        (length n.ordering <= length c)))
    (ensures (fun n2 ->
         (length n2.visited <= length c) /\
         (metric_numbering c n2 <= metric_numbering c n) /\
         (length n2.ordering <= length c)))
    (decreases %[metric_numbering c n; 0]) =
  (match nth n.visited current_idx with
   | None -> ()
   | Some v -> if v then fail_with "visiting already visited location. something is horribly wrong." else ());
  if current_idx < length c then (
    let old_n = n in
    let n = visit c n current_idx in
    let n = (
      match index c current_idx with
      | FnExit _ -> n
      | FnEntry _ next
      | Ins _ next
      | InsList _ next
      | Nop next
      | Call _ next
      | Ret next -> (
          if is_visited n next then n else post_order_numbering a c next n
        )
      | Cmp _ nextTrue nextFalse -> (
          fold_left_post_order_numbering_over_list_of_loc a c n [nextTrue; nextFalse]
        )
      | Switch case_table _ -> (
          if case_table < length a.br_tables then (
            let targets = (index a.br_tables case_table).br_targets in
            (* We reverse before passing along so that the reversed post order ends up nicer :) *)
            fold_left_post_order_numbering_over_list_of_loc a c n (rev targets)
          ) else (
            fail_with "invalid case_table"
          )
        )
      | HighCall _ _ _ _ -> fail_with "unexpected highcall"
      | HighRet _ _ -> fail_with "unexpected highret"
    ) in
    lemma_update_ordering n.ordering current_idx n.next;
    let n = { n with
              ordering = update_index n.ordering None current_idx (Some n.next);
              next = n.next + 1; } in
    n
  ) else (
    fail_with "tried to go out of bounds"
  )

and fold_left_post_order_numbering_over_list_of_loc
    (a:aux) (c:cfg) (n:numbering) (l:list loc) :
  Err numbering
    (requires (
        (length n.visited <= length c) /\
        (length n.ordering <= length c)))
    (ensures (fun n2 ->
         (length n2.visited <= length c) /\
         (metric_numbering c n2 <= metric_numbering c n) /\
         (length n2.ordering <= length c)))
    (decreases %[metric_numbering c n; 1; l]) =
  match l with
  | [] -> n
  | h :: t ->
    let n1 = if is_visited n h then n else post_order_numbering a c h n in
    fold_left_post_order_numbering_over_list_of_loc a c n1 t
#pop-options

let rec perform_full_numbering_aux (fns:list aux_fn) (a:aux) (c:cfg) (n:numbering) :
  Err numbering
    (requires (
        (length n.visited <= length c) /\
        (length n.ordering <= length c)))
    (ensures (fun n2 ->
         (length n2.visited <= length c) /\
         (length n2.ordering <= length c))) =
  match fns with
  | [] -> n
  | h :: t ->
    let n = perform_full_numbering_aux t a c n in
    post_order_numbering a c h.fn_loc n

let perform_full_numbering (m:module_) :
  Err numbering
    (requires (True))
    (ensures (fun n -> length n.ordering <= length m.module_cfg)) =
  perform_full_numbering_aux m.module_aux.fns m.module_aux m.module_cfg ({
      next = 0;
      visited = [];
      ordering = [];
  })

let lemma_for_all_cons #t (f:t -> bool) (l:list t) :
  Lemma
    (requires (Cons? l ==> (f (hd l) /\ for_all f (tl l))))
    (ensures (for_all f l)) = ()

unfold type mapping (len_c:nat) = list (n:nat{n < len_c})

let rec mapping_of_numbering (len_c i:nat) (n:list (option nat)) :
  Err (mapping len_c)
    (requires (i + length n <= len_c))
    (ensures (fun r -> i + length r == len_c))
    (decreases %[n; len_c - i]) =
  match n with
  | [] -> if i = len_c then [] else (
      i :: mapping_of_numbering len_c (i+1) []
    )
  | h :: t ->
    let cur =
      match h with
      | None -> i
      | Some v -> if v < len_c then (len_c - v) - 1 else fail_with "error: out-of-bounds"
    in
    cur :: mapping_of_numbering len_c (i+1) t

let idx #t (l:list t) (i:nat) :
  Err t
    (requires True)
    (ensures (fun x ->
         (i < length l) /\
         (x == index l i))) =
  if i < length l then
    index l i
  else
    fail_with "out of bounds"

let rec map_err #t1 #t2 (f:t1 -> Err t2 (True) (fun _ -> True)) (l:list t1) : Err (list t2) (True) (fun _ -> True) =
  match l with
  | [] -> []
  | h :: t -> f h :: map_err f t

let reorder_aux #len_c (m:mapping len_c) (a:aux) :
  Err aux
    (requires True)
    (ensures (fun _ -> True)) =
  let { fns; globals; memory; br_tables; call_table; mem_pages } = a in
  {
    fns = map_err (fun f ->
        let fn_loc = idx m f.fn_loc in
        let fn_end = idx m f.fn_end in
        { f with fn_loc ; fn_end }) fns;
    globals;
    memory;
    br_tables = map_err (fun bt ->
        {bt with br_targets =
                   map_err #_ #loc (fun i -> let r = idx m i in r) bt.br_targets})
        br_tables;
    call_table;
    mem_pages;
  }

let reorder_cfg #len_c (m:mapping len_c) (c:cfg) :
  Err cfg
    (requires True)
    (ensures (fun _ -> True)) =
  let modified = map_err #_ #precode (fun p ->
      match p with
      | FnExit name ->
        FnExit name
      | FnEntry name next ->
        let l = idx m next in
        FnEntry name l
      | Ins i next ->
        let l = idx m next in
        Ins i l
      | InsList is next ->
        let l = idx m next in
        InsList is l
      | Nop next ->
        let l = idx m next in
        Nop l
      | Call target onreturn ->
        let l = idx m onreturn in
        Call target l
      | Ret next ->
        let l = idx m next in
        Ret l
      | Cmp cond nextTrue nextFalse ->
        let l1 = idx m nextTrue in
        let l2 = idx m nextFalse in
        Cmp cond l1 l2
      | Switch case_table case -> Switch case_table case
      | HighCall _ _ _ _ -> fail_with "unexpected highcall"
      | HighRet _ _ -> fail_with "unexpected highret") c in
  map_err (fun (i:nat{i < len_c}) -> let i = i in idx modified i) m

let reorder_module (m:module_) (mp:mapping (length m.module_cfg)) :
  Err module_
    (requires True)
    (ensures (fun _ -> True)) =
  let { module_aux ; module_cfg } = m in
  { module_aux = reorder_aux mp module_aux;
    module_cfg = reorder_cfg mp module_cfg; }

let compile_module (m:module_) :
  Err module_
    (requires (True))
    (ensures (fun _ -> True)) =
  let postorder = perform_full_numbering m in
  let rev_postorder = mapping_of_numbering (length m.module_cfg) 0 postorder.ordering in
  reorder_module m rev_postorder
