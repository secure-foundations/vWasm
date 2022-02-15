module Semantics.Common.CFG

/// To build off of this common CFG framework, an (intermediate)
/// language needs to define the following:
///
/// + valid_reg_int : int -> bool
/// + valid_reg_float : int -> bool
/// + ins_t : eqtype
/// + eval_ins : ins_t -> (s:state) -> (s_new:state{s.ip = s_new.ip})
///
/// To also have access to a printer (see Semantics.Common.CFG.Printer),
/// the language needs to define the following:
///
/// + string_of_inst : ins_t -> string
///
/// The following definitions applied, once the pre-requisites are
/// defined, should make working with the CFGs much easier:
///
/// let operandi = operandi #valid_reg_int
/// let operandf = operandf #valid_reg_int #valid_reg_float
/// let cfg = cfg #ins_t #valid_reg_int #valid_reg_float
/// let eval_step (c:cfg) (s:state) = eval_step #_ #_ #_ #eval_ins c s
/// let string_of_cfg (c:cfg) = string_of_cfg #_ #_ #_ #string_of_inst c
///
/// If the above definitions are not defined, then any users of the
/// specific language will start to face a lot of implicit types that
/// it may not be able to find. If such a case shows up, it is likely
/// because the language hasn't defined the requisite definitions
/// above.

module L = FStar.List.Tot
open FStar.FunctionalExtensionality
open Types_s
open Common.Conversions
open Common.Memory

type regi (#valid_reg_int:int -> bool) : eqtype =
  (n:int{valid_reg_int n})

type regf (#valid_reg_float:int -> bool) : eqtype =
  (n:int{valid_reg_float n})

type rsize = (n:nat{n = 1 || n = 2 || n = 4 || n = 8})

type gbltype_i =
  | Ident : nat -> gbltype_i
  | MemPages

type gbltype_f =
  | Ident_f : nat -> gbltype_f

type maddr (#valid_reg_int:int -> bool) : eqtype =
  //| MReg : offset:int -> maddr #valid_reg_int // Shouldn't be needed for the time being
  | MIndex : scale:int -> index:regi #valid_reg_int -> offset:int -> maddr #valid_reg_int

type operandi (#valid_reg_int:int -> bool) : eqtype =
  | OConst : n:int -> operandi #valid_reg_int
  | OReg : r:regi #valid_reg_int -> size:rsize -> operandi #valid_reg_int
  | OMemRel : offset:maddr #valid_reg_int -> operandi #valid_reg_int // relative to mem base
  | OStackRel : offset:int -> operandi #valid_reg_int // relative to stack top
  | ONamedGlobal : gbltype_i -> operandi #valid_reg_int // index of global in globals list in aux

// NB: floats are stored as the equivalent integer
type float = nat

type operandf (#valid_reg_int:int -> bool) (#valid_reg_float:int -> bool) : eqtype =
  | OConst_f : f:float -> operandf #valid_reg_int #valid_reg_float
  | OReg_f : r:regf #valid_reg_float -> size:rsize -> operandf #valid_reg_int #valid_reg_float
  | OMemRel_f : offset:maddr #valid_reg_int -> operandf #valid_reg_int #valid_reg_float
  | OStackRel_f : offset:int -> operandf #valid_reg_int #valid_reg_float
  | ONamedGlobal_f : gbltype_f -> operandf #valid_reg_int #valid_reg_float

(* TODO: Do we need float comparisons here? *)
type ocmp (#valid_reg_int:int -> bool) (#valid_reg_float:int -> bool) : eqtype =
  (* 32 bit comparisons *)
  | OEq32 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | ONe32 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OLe32 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGe32 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OLt32 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGt32 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float

  | OLeS32: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGeS32: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OLtS32: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGtS32: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  (* 64 bit comparisons *)
  | OEq64 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | ONe64 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OLe64 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGe64 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OLt64 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGt64 : o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float

  | OLeS64: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGeS64: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OLtS64: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  | OGtS64: o1:operandi #valid_reg_int -> o2:operandi #valid_reg_int -> ocmp #valid_reg_int #valid_reg_float
  (* 32 bit floats *)
  | OFEq32: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFNe32: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFLt32: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFGt32: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFLe32: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFGe32: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  (* 64 bit floats *)
  | OFEq64: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFNe64: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFLt64: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFGt64: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFLe64: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float
  | OFGe64: o1:operandf #valid_reg_int #valid_reg_float -> o2:operandf #valid_reg_int #valid_reg_float -> ocmp #valid_reg_int #valid_reg_float

type loc = nat

type target_t #vali =
  | CallDirect : n:nat -> target_t #vali
  | CallIndirect : r:regi #vali -> target_t #vali

// r is the register, we use nats to make life a bit easier when defining the state
type ins_arg:eqtype =
  | ArgInt : r:nat -> is64:bool -> ins_arg
  | ArgFloat : r:nat -> is64:bool -> ins_arg

type precode (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool) =
  | FnEntry : name:int -> next:loc -> precode #ins_t #vali #valf
  | FnExit : name:int -> precode #ins_t #vali #valf
  | Ins : i:ins_t -> next:loc -> precode #ins_t #vali #valf
  | InsList : is:list ins_t -> next:loc -> precode #ins_t #vali #valf
  | Nop : next:loc -> precode #ins_t #vali #valf
  | Cmp : cond:ocmp #vali #valf -> nextTrue:loc -> nextFalse:loc -> precode #ins_t #vali #valf
  | Switch : case_table:nat -> case:regi #vali -> precode #ins_t #vali #valf
  | Call : target:target_t #vali -> onreturn:loc -> precode #ins_t #vali #valf
  | HighCall : target:target_t #vali -> args:list ins_arg -> retval_store:option ins_arg -> onreturn:loc -> precode #ins_t #vali #valf
  | Ret : next:loc -> precode #ins_t #vali #valf
  | HighRet : retval_load:option ins_arg -> next:loc -> precode #ins_t #vali #valf

(** The control flow graph of all the functions. We do NOT keep edges
    between functions. Thus, this is really a set of disconnected
    CFGs, all placed together in one place. *)
type cfg (#ins_t:eqtype) (#valid_reg_int:int -> bool) (#valid_reg_float:int -> bool) : eqtype =
  list (precode #ins_t #valid_reg_int #valid_reg_float)

let in_cfg (l:loc) (c:cfg #'a #'b #'c) : bool =
  l < L.length c

let get_code_at (l:loc) (c:cfg #'a #'b #'c{l `in_cfg` c}) : precode #'a #'b #'c =
  L.index c l

private
let set_at (l:list 'a) (idx:nat{idx < L.length l}) (n:'a) :
  (l':list 'a{L.length l = L.length l'}) =
  let l0, o, l1 = L.split3 l idx in
  List.Pure.Properties.lemma_split3_length l idx;
  List.Tot.Properties.append_length l0 (n :: l1);
  l0 @ (n :: l1)

let set_code_at (l:loc) (ins:precode #'a #'b #'c) (c:cfg #'a #'b #'c{l `in_cfg` c}) : cfg #'a #'b #'c =
  set_at c l ins

type ok_t =
  | AllOk
  | MemFailure
  | AstFailure
  | RuntimeError

let ok_join (o1 o2:ok_t) =
  (* NOTE: The order of matches here MATTERS.
     AstFailure is the worst failure. *)
  match o1, o2 with
  | AstFailure, _ | _, AstFailure -> AstFailure
  | MemFailure, _ | _, MemFailure -> MemFailure
  | RuntimeError, _ | _, RuntimeError -> RuntimeError
  | AllOk, AllOk -> AllOk

unfold let astcheck (b:bool) = if b then AllOk else AstFailure
unfold let memcheck (b:bool) = if b then AllOk else MemFailure
unfold let runtimecheck (b:bool) = if b then AllOk else RuntimeError

noeq
type stack = {
  init_rsp : int;
  smem : heap;
}

type val_ty: eqtype = | I32_ty | I64_ty | F32_ty | F64_ty

type aux_fn : eqtype = {
  fn_name : int;
  fn_str : string;
  fn_loc : loc;
  fn_end : loc;
  fn_argtys : list val_ty;
  fn_rettys : option val_ty;
  fn_locals : list val_ty;
  fn_isImported : bool;
  fn_isExported : bool;
}

type aux_global : eqtype = {
  gbl_name : string;
  gbl_init : option (list nat8);
  gbl_ty : val_ty;
  gbl_isMutable : bool;
  gbl_isImported : bool;
  gbl_isExported : bool;
}

type aux_memory : eqtype = {
  mem_name : string;
  mem_init : list (
      (data : list nat8) *
      (base : nat32)
    );
  mem_min : nat32;
  mem_max : option nat32;
  mem_isImported : bool;
  mem_isExported : bool;
}

type aux_br_table : eqtype = {
  br_name : string;
  br_targets : list loc;
}

type aux_call_table : eqtype = {
  call_name : string;
  call_init : list (option nat);
}

type aux : eqtype = {
  fns : list aux_fn;
  globals : list aux_global;
  memory : aux_memory;
  br_tables : list aux_br_table;
  call_table : aux_call_table;
  mem_pages: nat32;
}

type module_ (#ins_t:eqtype) (#valid_reg_int:int -> bool) (#valid_reg_float:int -> bool) : eqtype = {
  module_aux : aux;
  module_cfg : cfg #ins_t #valid_reg_int #valid_reg_float;
}

let get_next (ax:aux) (ins:precode #'a #'b #'c) =
  match ins with
  | FnEntry _ next | Ins _ next | InsList _ next | Nop next
  | Call _ next | HighCall _ _ _ next
  | Ret next | HighRet _ next ->
    [next]
  | Cmp _ nextTrue nextFalse ->
    [nextTrue; nextFalse]
  | FnExit _ ->
    []
  | Switch case_table _ ->
    match L.nth ax.br_tables case_table with
    | Some tbl -> tbl.br_targets
    | None -> []

let cfg_next_valid (c:cfg #'a #'b #'c) (ax:aux) (ins:precode #'a #'b #'c) =
  let targets = get_next ax ins in
  forall (next:loc). L.mem next targets ==> next `in_cfg` c

let cfg_ptr_valid (c:cfg #'a #'b #'c) (ax:aux) =
  forall (pc:loc). pc `in_cfg` c ==> (
    let ins = get_code_at pc c in
    cfg_next_valid c ax ins
  )

let cfg_next_valid_b (c:cfg #'a #'b #'c) (ax:aux) (ins:precode #'a #'b #'c) =
  let targets = get_next ax ins in
  L.for_all (fun next -> next `in_cfg` c) targets

let cfg_ptr_valid_b (c:cfg #'a #'b #'c) (ax:aux) =
  L.for_all (fun ins -> cfg_next_valid_b c ax ins) c

let rec lemma_for_all
  (#a:eqtype)
  (f:a -> bool)
  (l:list a)
  : Lemma (L.for_all f l ==> (forall e. (L.mem e l ==> f e))) =
  match l with
  | [] -> ()
  | e :: l -> lemma_for_all #a f l

let lemma_cfg_next_valid_b
  (c:cfg #'a #'b #'c)
  (ax:aux)
  (ins:precode #'a #'b #'c)
  : Lemma (cfg_next_valid_b c ax ins ==> cfg_next_valid c ax ins) =
  if not (cfg_next_valid_b c ax ins) then () else (
    let targets = get_next ax ins in
    lemma_for_all (fun next -> next `in_cfg` c) targets
  )

let rec lemma_index_implies_mem
  (idx:loc) (c:cfg #'a #'b #'c{idx `in_cfg` c})
  : Lemma (
    let ins = L.index c idx in
    L.mem ins c
  ) =
  match c with
  | [] -> ()
  | x :: c' ->
    if idx = 0 then () else lemma_index_implies_mem (idx - 1) c'

let lemma_cfg_b_implies_cfg
  (c:cfg #'a #'b #'c)
  (ax:aux)
  : Lemma (cfg_ptr_valid_b c ax ==> cfg_ptr_valid c ax) =
  if not (cfg_ptr_valid_b c ax) then () else (
    lemma_for_all (fun ins -> cfg_next_valid_b c ax ins) c;
    FStar.Classical.forall_intro_3 (lemma_cfg_next_valid_b #'a #'b #'c);
    FStar.Classical.forall_intro_2 (lemma_index_implies_mem #'a #'b #'c)
  )

private
let rec lemma_set_at_context (l:list 'a) (idx:nat{idx < L.length l}) (n:'a) (idx':nat{idx' <> idx /\ idx' < L.length l}):
  Lemma (
    let l' = set_at l idx n in
    L.index l idx' == L.index l' idx'
  ) =
  if idx = 0 || idx' = 0 then () else lemma_set_at_context (L.tl l) (idx - 1) n (idx' - 1)

private
let rec lemma_set_at_hole (l:list 'a) (idx:nat{idx < L.length l}) (n:'a):
  Lemma (
    let l' = set_at l idx n in
    L.index l' idx == n
  ) =
  if idx = 0 then () else lemma_set_at_hole (L.tl l) (idx - 1) n

private
let pred_valid (preds:list (list loc)) (pred:list loc) =
  forall (next:loc). L.mem next pred ==> next < L.length preds

private
let pred_ptr_valid (preds:list (list loc)) =
  (forall (pc:loc). pc < L.length preds ==> (
     let pred = L.index preds pc in
     pred_valid preds pred
  ))

let cfg_pred_ptr_valid (c:cfg #'a #'b #'c) (preds: list (list loc)) =
  pred_ptr_valid preds /\ L.length c = L.length preds

private
let rec add_preds
    (next_pcs:list loc)
    (preds:list (list loc){pred_ptr_valid preds})
    (pc:loc{pc < L.length preds}):
    (preds_:list (list loc){L.length preds_ = L.length preds /\ pred_ptr_valid preds_})=
  match next_pcs with
  | [] -> preds
  | next_pc :: next_pcs ->
    if next_pc >= L.length preds then (
      add_preds next_pcs preds pc
    ) else (
      let next_preds = L.index preds next_pc in
      if L.mem pc next_preds then (
        add_preds next_pcs preds pc
      ) else (
        let pred' = pc :: next_preds in
        let preds' = set_at preds next_pc pred' in
        lemma_set_at_hole preds next_pc pred';
        FStar.Classical.forall_intro (lemma_set_at_context preds next_pc pred');
        add_preds next_pcs preds' pc
      )
    )

let rec update_preds
    (c:cfg #'a #'b #'c)
    (ax:aux)
    (preds:list (list loc){pred_ptr_valid preds})
    (pc:loc{pc + L.length c <= L.length preds}):
    (preds_: list (list loc){L.length preds_ = L.length preds /\ pred_ptr_valid preds_}) =
  match c with
  | [] -> preds
  | ins :: c ->
    let next_pcs = get_next ax ins in
    let preds' = add_preds next_pcs preds pc in
    update_preds c ax preds' (pc + 1)

let compute_preds (c:cfg #'a #'b #'c) (ax:aux): (preds:list (list loc){cfg_pred_ptr_valid c preds}) =
  let rec f (n:nat):(ll:list (list loc){pred_ptr_valid ll /\ L.length ll = n}) =
    if n = 0 then [] else [] :: f (n - 1)
  in
  let preds = f (L.length c) in
  update_preds c ax preds 0
