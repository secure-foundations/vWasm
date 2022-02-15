module Compiler.Common.Dataflow

/// Unified Dataflow Framework
///
/// The following needs to be provided to use this framework:
/// - t: eqtype - The type of lattice element the analysis uses
/// - top: t
/// - bot: t
/// - join: t -> t -> t
/// - meet: t -> t -> t
/// - All the various lattice lemmas (see lattice structure definition)
/// This gives a lattice structure.
///
/// Then, these next things must be provided for the analysis itself:
/// - m: l.t -> nat - Metric assigning each lattice element a nat
/// - Lemmas characterising behavior of metric on joins and meets (see dataflow_pass definition)
/// - Flags specifying forward/backward and universal/existential dataflow
/// - Entry and init values for initialization
/// - Transfer function: The output of the transfer will be a list of l.t,
///   padded with a default value until the appropriate size. This allows for
///   different branches of an IfElse to have different values, for example.
///   It is up to the user to provide the correct transfer function such that the analysis makes
///   sense. The pass will not check this for you. (see dataflow_pass definition)
/// This gives a dataflow_pass structure.
///
/// Finally, you can call the function compute_dataflow: cfg -> aux -> list l.t
/// that computes the minimum/maximum fixed point for the dataflow analysis.
///
/// Note that cfg/aux needs to be a pair satisfying Semantics.Common.CFG.cfg_ptr_valid that states that
/// the 'next' pointers in the CFG do not point outside of the CFG. This has to be upheld by the compiler
/// along passes.
///
/// Currently because all the functions are lumped together it just runs the dataflow over all the functions
/// at once. Consider not doing this and instead doing each function separately, but that requires more work
/// at refactoring to split up the functions at the moment. Splitting up the functions can probably be written
/// as a dataflow pass which is cute but its probably easier to have them separate initially. Perhaps we can
/// find a way to structure this so that proofs are not difficult. KIV.

module L = FStar.List.Tot
module CS = FStar.Classical
module CFG = Semantics.Common.CFG
open Common.Err

(* Lattice axioms *)
type lat_op_t (#t:eqtype) = t -> t -> t
type lat_comm_t (#t:eqtype) (#op:lat_op_t #t) =
  (x:t) -> (y:t) -> Lemma (op x y = op y x)
type lat_assoc_t (#t:eqtype) (#op:lat_op_t #t) =
  (x:t) -> (y:t) -> (z:t) -> Lemma (op x (op y z) = op (op x y) z)
type lat_absorb_t (#t:eqtype) (#op1:lat_op_t #t) (#op2:lat_op_t #t) =
  (x:t) -> (y:t) -> Lemma (op1 x (op2 x y) = x)
type lat_ident_t (#t:eqtype) (#op:lat_op_t #t) (#i:t) =
  (x:t) -> Lemma (op x i = i)

noeq type lattice = {
  t:eqtype;
  top:t;
  bot:t;
  join:lat_op_t #t;
  meet:lat_op_t #t;
  join_comm  :lat_comm_t #t #join;
  meet_comm  :lat_comm_t #t #meet;
  join_assoc :lat_assoc_t #t #join;
  meet_assoc :lat_assoc_t #t #meet;
  join_absorb:lat_absorb_t #t #join #meet;
  meet_absorb:lat_absorb_t #t #meet #join;
  join_ident :lat_ident_t #t #join #top;
  meet_ident :lat_ident_t #t #meet #bot;
}

(* Derived axioms *)
let lemma_join_idem (#l:lattice) (x:l.t): Lemma (l.join x x = x) =
  l.meet_absorb x x;
  l.join_absorb x (l.join x x)

let lemma_meet_idem (#l:lattice) (x:l.t): Lemma (l.meet x x = x) =
  l.join_absorb x x;
  l.meet_absorb x (l.meet x x)

(* Lattice metric (for termination purposes) *)
type lat_metric_t (#l:lattice) = l.t -> nat
type lat_metric_join_t (#l:lattice) (#m:lat_metric_t #l) =
  (x:l.t) -> (y:l.t) -> Lemma (
    let z = l.join x y in
    z <> x ==> m z > m x
  )
type lat_metric_meet_t (#l:lattice) (#m:lat_metric_t #l) =
  (x:l.t) -> (y:l.t) -> Lemma (
    let z = l.meet x y in
    z <> x ==> m z < m x
  )

(* Dataflow functions *)
/// NOTE: The output of the transfer will be cases, padded with def until the appropriate size.
/// It is up to the user to provide the correct transfer function such that the analysis makes sense.
/// The pass will not check this for you.
type trans_t (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool) =
  CFG.loc -> l.t -> ins:CFG.precode #ins_t #vali #valf -> Err_ (cases:(list l.t) * def:l.t)

noeq type dataflow_pass (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool) = {
  m:lat_metric_t #l;
  existential_dataflow:bool;
  backwards_dataflow:bool;
  m_join:lat_metric_join_t #l #m;
  m_meet:lat_metric_meet_t #l #m;
  entry:l.t;
  init:l.t;
  trans: trans_t #l #ins_t #vali #valf;
}

type fp_t (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool) (dp:dataflow_pass #l #ins_t #vali #valf) =
  list l.t

(* TEST CODE, TO REMOVE *)
/// This file contains various analyses implemented with the unified dataflow framework

/// 'Basic Block' lattice and lattice metric
/// This lattice keeps track of sets of basic block indices, and is meant to be used in SSA transformation.
module S = Common.OrdSet
module M = FStar.Map
module Sem = I1.Semantics

let pc_ (#c:Sem.cfg): eqtype = (n:nat{n < L.length c})
let t (#c:Sem.cfg): eqtype = S.ordset (n:pc_ #c) op_LessThanOrEqual

let rec of_list (#ty:eqtype) #cmp (l:list ty): S.ordset ty cmp =
  match l with
  | [] -> S.empty
  | [x] -> S.singleton x
  | x :: l -> S.union (S.singleton x) (of_list l)

let to_list (#ty:eqtype) #cmp (s:S.ordset ty cmp): list ty =
  S.fold (fun acc a -> a :: acc) [] s


let rec f_ (#c:Sem.cfg) (n:nat{n <= L.length c}) : (s:t #c{forall (k:nat{k < n}). S.mem k s}) =
  if n = 0 then S.empty else S.union (S.singleton (n - 1)) (f_ (n - 1))

let top (#c:Sem.cfg): (s:t{forall (n:nat). n < L.length c ==> S.mem n s}) = f_ #c (L.length c)
let bot #c: t #c = S.empty

let join #c: lat_op_t #(t #c) = S.union
let meet #c: lat_op_t #(t #c) = S.intersect

let join_comm #c: lat_comm_t #(t #c) #join = fun x -> fun y -> ()
let meet_comm #c: lat_comm_t #(t #c) #meet = fun x -> fun y -> ()

val join_assoc (#c:Sem.cfg): lat_assoc_t #(t #c) #(join #c)
let join_assoc #c x y z =
  let lhs = join x (join y z) in
  let rhs = join (join x y) z in
  assert (S.equal lhs rhs)
val meet_assoc (#c:Sem.cfg) : lat_assoc_t #(t #c) #(meet #c)
let meet_assoc #c x y z =
  let lhs = meet x (meet y z) in
  let rhs = meet (meet x y) z in
  assert (S.equal lhs rhs)

val join_absorb (#c:Sem.cfg) : lat_absorb_t #(t #c) #(join #c) #(meet #c)
let join_absorb #c x y =
  let lhs = join x (meet x y) in
  let rhs = x in
  assert (S.equal lhs rhs)
val meet_absorb (#c:Sem.cfg) : lat_absorb_t #(t #c) #(meet #c) #(join #c)
let meet_absorb #c x y =
  let lhs = meet x (join x y) in
  let rhs = x in
  assert (S.equal lhs rhs)

val join_ident (#c:Sem.cfg): lat_ident_t #(t #c) #(join #c) #(top #c)
let join_ident #c x =
  let lhs = join x (top #c) in
  let rhs = top #c in
  assert (S.equal lhs rhs)
val meet_ident (#c:Sem.cfg): lat_ident_t #(t #c) #(meet #c) #(bot #c)
let meet_ident #c x =
  let lhs = meet x bot in
  let rhs = bot in
  assert (S.equal lhs rhs)

let l (#c:Sem.cfg): lattice = {
  t = t #c;
  top = top #c;
  bot = bot #c;
  join = join #c;
  meet = meet #c;
  join_comm = join_comm #c;
  meet_comm = meet_comm #c;
  join_assoc = join_assoc #c;
  meet_assoc = meet_assoc #c;
  join_absorb = join_absorb #c;
  meet_absorb = meet_absorb #c;
  join_ident = join_ident #c;
  meet_ident = meet_ident #c;
}

let size_ #c x = S.size #(pc_ #c) #(op_LessThanOrEqual) x
let mem_ #c e x = S.mem #(pc_ #c) #(op_LessThanOrEqual) e x
let singleton_ #c x = S.singleton #(pc_ #c) #(op_LessThanOrEqual) x
let empty_ #c = S.empty #(pc_ #c) #(op_LessThanOrEqual)

let m #c (x:(l #c).t) = size_ x

val m_join (#c:Sem.cfg): lat_metric_join_t #(l #c) #(m #c)
let m_join #c x y =
  let z = join x y in
  if z = x then () else (
    assert (~(S.equal z x));
    assert (exists e. S.mem e z /\ not (mem_ e x) /\
                 (let s = S.remove e z in
                  S.size z = S.size s + 1 /\
                  S.subset x s /\
                  S.size s >= size_ x))
  )

val m_meet (#c:Sem.cfg): lat_metric_meet_t #(l #c) #(m #c)
let m_meet #c x y =
  let z = meet x y in
  if z = x then () else (
    assert (~(S.equal z x));
    assert (exists e. mem_ e x /\ not (S.mem e z) /\
            (let s = S.remove e x in
             size_ x = S.size s + 1 /\
             S.subset z s /\
             S.size s >= S.size z))
  )

/// Dominator dataflow pass
/// This calculates the blocks that dominate a given block.

val trans_dom (#c:Sem.cfg): trans_t #(l #c) #Sem.ins_t #Sem.valid_reg_int #Sem.valid_reg_float
let trans_dom #c pc dom_in ins =
  if pc >= L.length c then fail_with "reaching_defs: bad pc" else (
    match ins with
    | CFG.Call _ _ -> fail_with "trans_dom: unexpected Call" // Should not occur in high level
    | CFG.Ret _ -> fail_with "trans_dom: unexpected Ret" // Should not occur in high level
    | _ -> ([], S.union (singleton_ pc) dom_in)
  )

let dominator_pass (#c:Sem.cfg): dataflow_pass #(l #c) #Sem.ins_t #Sem.valid_reg_int #Sem.valid_reg_float = {
  m = m #c;
  existential_dataflow = false;
  backwards_dataflow = false;
  m_join = m_join #c;
  m_meet = m_meet #c;
  entry = empty_;
  init = l.top;
  trans = trans_dom #c;
}

(** Small test cases for dominator pass **)
private let _c0: Sem.cfg = [
    CFG.FnEntry 1 1;
    CFG.FnExit 1;
]

private let _f0 = {
    CFG.fn_name = 1;
    CFG.fn_str = "f0";
    CFG.fn_loc = 0;
    CFG.fn_end = 1;
    CFG.fn_argtys = [];
    CFG.fn_rettys = None;
    CFG.fn_locals = [];
    CFG.fn_isImported = false;
    CFG.fn_isExported = false;
}

private let _mem0 = {
  CFG.mem_name = "mem0";
  CFG.mem_init = [];
  CFG.mem_min = 0;
  CFG.mem_max = None;
  CFG.mem_isImported = false;
  CFG.mem_isExported = false;
}

private let _ctable0 = {
  CFG.call_name = "ctable0";
  CFG.call_init = [];
}


private let _aux0 = {
  CFG.fns = [_f0];
  CFG.globals = [];
  CFG.memory = _mem0;
  CFG.br_tables = [];
  CFG.call_table = _ctable0;
  CFG.mem_pages = 10;
}

let l_c0: lattice = l #_c0
let dp_c0 = dominator_pass #_c0
let pc_c0 = pc_ #_c0
let t_c0 = t #_c0
let of_list_c0 = of_list #(pc_c0) #(op_LessThanOrEqual)

(* Helper lemmas *)
private
let lemma_metric_top (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (x:l.t): Lemma (dp.m x <= dp.m l.top) =
  l.join_ident x;
  dp.m_join x l.top

private
let lemma_metric_bot (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (x:l.t): Lemma (dp.m x >= dp.m l.bot) =
  l.meet_ident x;
  dp.m_meet x l.bot

private
let set_at (l:list 'a) (idx:nat{idx < L.length l}) (n:'a) :
  (l':list 'a{L.length l = L.length l'}) =
  let l0, o, l1 = L.split3 l idx in
  List.Pure.Properties.lemma_split3_length l idx;
  List.Tot.Properties.append_length l0 (n :: l1);
  l0 @ (n :: l1)

#push-options "--fuel 4"
/// @Test
private let test_set_at _ : GTot (list nat) =
  let a = [1; 2; 3; 4; 5] in
  set_at a 3 20
#pop-options

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
let add_uniq (#ty:eqtype) (l:list ty) (x:ty) = if L.mem x l then l else x :: l

/// @Test
private let test_add_uniq () : GTot (list nat) =
  let x = [1; 2; 3] in
  add_uniq x 4

/// @Test
private let test_add_uniq2 () : GTot (list nat) =
  let x = [1; 2; 3] in
  add_uniq x 3

(* mfp -> Minimum/maximum fixed point, depending on type of dataflow *)
private
let mfp_diff (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (mfp:fp_t dp): nat =
  let f (x:l.t): nat =
    if not dp.existential_dataflow then (
      lemma_metric_bot dp x;
      dp.m x - dp.m l.bot
    ) else (
      lemma_metric_top dp x;
      dp.m l.top - dp.m x
    )
  in
  let (diff:list nat) = L.map f mfp in
  let plus (x:nat) (y:nat):nat = x + y in
  L.fold_right plus diff 0

/// @Test
let test_mfp_diff () : GTot nat =
  let mfp: fp_t dp_c0 = [of_list_c0 []; of_list_c0 [0]] in
  mfp_diff #l_c0 #Sem.ins_t #Sem.valid_reg_int #Sem.valid_reg_float
    (dominator_pass #_c0)
    mfp

private
let rec lemma_mfp_decreases (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (mfp:fp_t dp)
  (pc:nat{pc < L.length mfp})
  (n:l.t):
  Lemma (
    let o = L.index mfp pc in
    let mfp' = set_at mfp pc n in
    let diff = mfp_diff dp mfp in
    let diff' = mfp_diff dp mfp' in
    ((not dp.existential_dataflow) /\ dp.m n < dp.m o ==> diff' < diff) /\
    (dp.existential_dataflow /\ dp.m n > dp.m o ==> diff' < diff) /\
    (n = o ==> diff' = diff)
  ) =
  CS.forall_intro (lemma_set_at_context mfp pc n);
  lemma_set_at_hole mfp pc n;
  if pc = 0 then () else lemma_mfp_decreases dp (L.tl mfp) (pc - 1) n

/// - Pop pc and v' from pc and lv'
/// - Grab mfp[pc]
/// - Try to update mfp[pc] with v' using appropriate meet/join
/// - If mfp[pc] was updated, add to working set
/// - Recurse
private
let rec update_fp (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (mfp:fp_t dp)
  (lv':list l.t)
  (pcs:list CFG.loc{L.length pcs = L.length lv' /\ (forall (pc:CFG.loc). L.mem pc pcs ==> pc < L.length mfp)})
  (ws:list CFG.loc{forall (ws_pc:CFG.loc). L.mem ws_pc ws ==> ws_pc < L.length mfp}):
  Tot (res:(fp_t dp * (list CFG.loc)){
         let mfp_ = fst res in
         let ws_ = snd res in
         let diff = mfp_diff dp mfp in
         let diff' = mfp_diff dp mfp_ in
         (forall (ws_pc_:CFG.loc). L.mem ws_pc_ ws_ ==> ws_pc_ < L.length mfp) /\
         L.length mfp = L.length mfp_ /\
         diff' <= diff /\
         (diff' = diff ==> ws_ = ws)
       })
      (decreases pcs) =
  match pcs, lv' with
  | [], [] -> mfp, ws
  | pc :: pcs, v' :: lv' ->
    let v_old = L.index mfp pc in
    let op = if dp.existential_dataflow then l.join else l.meet in
    let v_new = op v_old v' in
    if v_old = v_new then (
      update_fp dp mfp lv' pcs ws
    ) else (
      let mfp' = set_at mfp pc v_new in
      let ws' = add_uniq ws pc in
      dp.m_join v_old v';
      dp.m_meet v_old v';
      lemma_mfp_decreases dp mfp pc v_new;
      update_fp dp mfp' lv' pcs ws'
    )

#push-options "--fuel 3 --ifuel 0"
/// @Test
private let test_update_fp (): GTot (fp_t dp_c0 * (list CFG.loc)) =
  let mfp: fp_t dp_c0 = [of_list_c0 [0;1]; of_list_c0 [1]] in
  let lv': list l_c0.t = [of_list_c0 [0]; of_list_c0 [0]] in
  let pcs: (pcs:list CFG.loc{L.length pcs = L.length lv' /\ (forall (pc:CFG.loc). L.mem pc pcs ==> pc < L.length mfp)}) =
    [0; 1] in
  let ws: (ws:list CFG.loc{forall (ws_pc:CFG.loc). L.mem ws_pc ws ==> ws_pc < L.length mfp}) = [] in
  update_fp #l_c0 #Sem.ins_t #Sem.valid_reg_int #Sem.valid_reg_float
    dp_c0 mfp lv' pcs ws
#pop-options

private
let pad_or_take (l:list 'a) (len:nat) (def:'a): (ll:list 'a{L.length ll = len}) =
  let rec rep (n:nat) (x:'a): (lx:list 'a{L.length lx = n}) = if n = 0 then [] else x :: (rep (n - 1) x) in
  let llen = L.length l in
  if llen = len then l else
  if llen < len then (
    FStar.List.Tot.Properties.append_length l (rep (len - llen) def);
    l @ (rep (len - llen) def)
  ) else (
    let l1, l2 = L.splitAt len l in
    FStar.List.Pure.Properties.lemma_splitAt l l1 l2 len;
    l1
  )

/// @Test
private let test_pad_or_take (): GTot (list nat) =
  let l = [0; 1; 2; 3; 4; 5] in
  let len = 3 in
  let def = 6 in
  pad_or_take l len def

/// @Test
private let test_pad_or_take2 (): GTot (list nat) =
  let l = [0; 1; 2; 3; 4; 5] in
  let len = 8 in
  let def = 6 in
  pad_or_take l len def

#push-options "--z3rlimit 50"

/// - Pop pc from working set
/// - Grab current mfp for that pc, apply transfer function
/// - Form list of updates to pcs (preds or succs)
/// - Update those pcs + ws
/// - Recurse
private
let rec compute_dataflow_ (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (cfg:CFG.cfg #ins_t #vali #valf)
  (aux:CFG.aux{CFG.cfg_ptr_valid cfg aux})
  (opreds:option (list (list CFG.loc)){dp.backwards_dataflow ==> (Some? opreds /\ CFG.cfg_pred_ptr_valid cfg (Some?.v opreds))})
  (mfp:fp_t dp{L.length cfg = L.length mfp})
  (ws:list CFG.loc{forall (ws_pc:CFG.loc). L.mem ws_pc ws ==> ws_pc < L.length cfg}):
  Err (mfp_:(fp_t dp))
    (requires (True))
    (ensures (fun mfp_ -> (L.length cfg = L.length mfp_)))
    (decreases %[mfp_diff dp mfp; ws]) =
  match ws with
  | [] -> mfp
  | pc :: pcs ->
    let ins = CFG.get_code_at pc cfg in
    if CFG.FnExit? ins && not dp.backwards_dataflow then (
      compute_dataflow_ dp cfg aux opreds mfp pcs
    ) else if CFG.FnEntry? ins && dp.backwards_dataflow then (
      compute_dataflow_ dp cfg aux opreds mfp pcs
    ) else (
      let lc = L.length cfg in
      let v = L.index mfp pc in
      let tup = dp.trans pc v ins in
      let lv0', def = tup in
      let propagate_pcs = if dp.backwards_dataflow then L.index (Some?.v opreds) pc else CFG.get_next aux ins in
      let lv1' = pad_or_take lv0' (L.length propagate_pcs) def in
      let mfp', ws' = update_fp dp mfp lv1' propagate_pcs pcs in
      assert (L.length mfp' = L.length mfp);
      let mfp'' = compute_dataflow_ dp cfg aux opreds mfp' ws' in
      assert (L.length cfg = L.length mfp');
      mfp'
    )

#pop-options

#push-options "--fuel 3"
/// @Test
private let test_compute_dataflow_helper () : Err_ (fp_t dp_c0) =
  let mfp: (mfp: fp_t dp_c0{L.length _c0 = L.length mfp}) = [of_list_c0 []; of_list_c0 [0;1]] in
  compute_dataflow_ #l_c0 #Sem.ins_t #Sem.valid_reg_int #Sem.valid_reg_float
    dp_c0 _c0 _aux0 None mfp [0; 1]
#pop-options

(* Dataflow calculation *)

let rec aux_compute_dataflow_e lc (n:nat{n <= lc}):
  Tot (ls:list CFG.loc{forall (pc:CFG.loc). L.mem pc ls ==> pc < lc})
    (decreases (lc - n)) =
  if n = lc then [] else n :: aux_compute_dataflow_e lc (n + 1)

(** [compute_dataflow dp cfg aux] computes the fixed point corresponding to the dataflow pass dp, and produces
    a dataflow analysis result, which is a list of lattice elements, one for each instruction in the CFG.
    The result may be indexed into using the [loc]s of the instructions.
    The i^th index corresponds to the dataflow result before the instruction for forward passes and to the
    dataflow result after the instruction for backward passes. The functions [dataflow_result_before dp loc fp]
    and [dataflow_result_after dp loc fp] may be used to do the correct indexing for you.
*)
let compute_dataflow (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (cfg:CFG.cfg #ins_t #vali #valf)
  (aux:CFG.aux{CFG.cfg_ptr_valid cfg aux}):
  Err (fp_t dp)
    (requires (True))
    (ensures (fun fp -> L.length fp = L.length cfg)) =
  let lc = L.length cfg in
  let f (ins:CFG.precode #'a #'b #'c): l.t =
    match ins with
    | CFG.FnEntry name _ -> if not dp.backwards_dataflow then dp.entry else dp.init
    | CFG.FnExit name -> if dp.backwards_dataflow then dp.entry else dp.init
    | _ -> dp.init
  in
  let mfp = L.map f cfg in
  let ws = aux_compute_dataflow_e lc 0 in
  let opreds = if dp.backwards_dataflow then Some (CFG.compute_preds cfg aux) else None in
  compute_dataflow_ dp cfg aux opreds mfp ws

/// TODO (jarsp): How to handle cases? Or remove cases entirely, shouldn't matter?
let dataflow_result_before (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (loc:CFG.loc)
  (ins:CFG.precode #ins_t #vali #valf)
  (fp:fp_t dp) : option l.t =
  if not dp.backwards_dataflow then (
    L.nth fp loc
  ) else (
    match L.nth fp loc with
    | None -> None
    | Some v ->
      match reify (dp.trans loc v ins) () with
      | Error' _ -> None
      | Ok' (cases, def) -> Some def
  )

let dataflow_result_after (#l:lattice) (#ins_t:eqtype) (#vali:int -> bool) (#valf:int -> bool)
  (dp:dataflow_pass #l #ins_t #vali #valf)
  (loc:CFG.loc)
  (ins: CFG.precode #ins_t #vali #valf)
  (fp:fp_t dp) : option l.t =
  if dp.backwards_dataflow then (
    L.nth fp loc
  ) else (
    match L.nth fp loc with
    | None -> None
    | Some v ->
      match reify (dp.trans loc v ins) () with
      | Error' _ -> None
      | Ok' (case, def) -> Some def
  )
