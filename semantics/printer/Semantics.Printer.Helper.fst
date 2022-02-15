module Semantics.Printer.Helper

open FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open Common.Err
open Common.Memory
open Common.OrdSet
open Types_s
open Common.Conversions
open Semantics.Common.CFG
open Semantics.Common.CFG.Instructions

open I2.Semantics
module I = Semantics.Common.CFG.LLInstructionSemantics

(** A set of locations *)
type locset = ordset loc (fun a b -> a <= b)

(** A convenient operator for union *)
let (++) (a b:locset) = union a b

let enumerate #t (l:list t) : Tot (list (nat & t)) =
  rev (snd (fold_left (fun (i, r) x ->
      (* The list is produced in reverse order, thus we put the elements in reverse
      here. The rev then reverses it again. *)
      let v : (nat & t) = i, x in
      i + 1, v :: r) (0, []) l))

let rec union_map_with #t (f:t -> locset) (l:list t) : Tot locset =
  match l with
  | [] -> empty
  | x :: xs -> f x ++ union_map_with f xs

let labeled_locs_of_precode (ip:loc) (p:precode) : Tot locset =
  match p with
  | FnEntry _ next
  | Ins _ next
  | InsList _ next
  | Nop next
  | Call _ next
  | Ret next
    -> if next = ip + 1 then empty else singleton next
  | Cmp _ next_t next_f ->
    (singleton next_t) ++ (* Always add for "true" case *)
    (if next_f = ip + 1 then empty else singleton next_f)
  | FnExit _ -> empty
  | Switch _ _ -> empty (* Handled by aux *)
  | HighCall _ _ _ _ | HighRet _ _ -> empty (* Irrelevant *)

let labeled_locs_of_precodes (ps:list (nat & precode)) : Tot locset =
  union_map_with (fun (ip, p) -> labeled_locs_of_precode ip p) ps

let labeled_locs_of_br_table (t:aux_br_table) : Tot locset =
  let { br_name; br_targets } = t in
  union_map_with singleton br_targets

let labeled_locs_of_aux (a:aux) : Tot locset =
  let { fns ; globals ; memory ; br_tables ; call_table ; mem_pages } = a in
  (* fns, globals, memory, call_table, mem_pages --- don't provide any forced labels *)
  union_map_with labeled_locs_of_br_table br_tables

let labeled_locs_of_module (m:module_) : Tot locset =
  let { module_aux ; module_cfg } = m in
  labeled_locs_of_aux module_aux ++
  labeled_locs_of_precodes (enumerate module_cfg)

let should_loc_be_labeled (m:module_) : (loc -> Tot bool) =
  let labeled = labeled_locs_of_module m in
  (fun l -> mem l labeled)
