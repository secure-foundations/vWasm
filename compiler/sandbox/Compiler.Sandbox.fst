module Compiler.Sandbox

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

open Compiler.Sandbox.Helpers

open Types_s
open Words_s
open TypesNative_s

open I2.Semantics
module U = Semantics.Common.CFG.Utils
module I = Semantics.Common.CFG.LLInstructionSemantics
module A = Common.AppendOptimizedList

#reset-options "--fuel 0 --ifuel 0"

noeq
type aux_info = {
  m_aux : aux;
  add_loc : loc;
  mem_sb_size : nat;
  modified_code: erased cfg;
  orig_code: cfg;
}

(** Represents a range of addresses from lower to upper (both
    inclusive). *)
type range = {
  lower: int;
  upper: int;
}

let valid_range (rng:range) : Tot bool =
  (-pow2_64) < rng.lower &&
  is_nat64 (rng.upper - rng.lower) &&
  rng.upper < pow2_64

let is_in_range (n:nat64) (r:range) : Tot bool =
  if r.lower >= 0 then (
    r.lower <= n && n <= r.upper
  ) else (
    if r.upper >= 0 then (
      r.lower % pow2_64 <= n || n <= r.upper
    ) else (
      r.lower % pow2_64 <= n && n <= r.upper % pow2_64
    )
  )

let range_add (r:range) (n:int) : Tot range = {
  lower = r.lower + n;
  upper = r.upper + n;
}

let range_sub (r:range) (n:int) : Tot range = range_add r (-n)

let range_mul (r:range) (n:int) : Tot range = {
  lower = r.lower `op_Multiply` n;
  upper = r.upper `op_Multiply` n;
}

let range_div (r:range) (n:pos) : Tot range = {
  lower = r.lower `op_Division` n;
  upper = r.upper `op_Division` n;
}

let rec is_pow2 (n:int) : Tot bool =
  if n < 0 then false else
  match n with
  | 0 -> false
  | 1 -> true
  | _ -> n % 2 = 0 && is_pow2 (n / 2)

let restrict_regi_to_max (r:regi) (c:int): ins_t =
  (* We use the faster "and" based version when possible, and
     fall-back to a conditional move otherwise *)
  if is_pow2 (c + 1) then (
    And64 (OReg r 8) (OConst c)
  ) else (
    CMov64 (OGt64 (OReg r 8) (OConst c)) (OReg r 8) (OConst 0)
  )

(** Restrict range of a single register *)
let restrict_regi (r:regi) (rng:range) : list ins_t =
  (* TODO: It _is_ possible to optimize this, but for now, I'm keeping it mostly generic *)
  let { lower ; upper } = rng in
  if lower = 0 then ([
      restrict_regi_to_max r upper;
  ]) else if lower > 0 then ([
      Sub64 (OReg r 8) (OConst lower);
      restrict_regi_to_max r (upper - lower);
      Add64 (OReg r 8) (OConst lower);
  ]) else ([
      Add64 (OReg r 8) (OConst (-lower));
      restrict_regi_to_max r (upper - lower);
      Sub64 (OReg r 8) (OConst (-lower));
  ])

let lemma_and64 (a b:nat64) :
  Lemma
    (iand a b <= a /\ iand a b <= b) =
  reveal_iand 64 a b;
  FStar.UInt.logand_le #64 a b

let lemma_and64_regi_const (r:regi) (c:int) (s:state) :
  Lemma
    (requires (is_nat64 c))
    (ensures (
        let i = And64 (OReg r 8) (OConst c) in
        let s' = eval_ins i s in
        eval_reg64 r s' == iand (eval_reg64 r s) c)) =
  let i = And64 (OReg r 8) (OConst c) in
  let s' = eval_ins i s in
  assert (eval_reg64 r s' == iand (eval_reg64 r s) c) by (
    norm [delta_fully [`%eval_ins; `%I.eval_ins; `%I.tag_of_ins; `%U.run;]];
    norm [delta_only [`%I._eval_ins_I64_Binop; `%I.op_I64_Binop]; nbe];
    norm [delta_fully [`%I.args_I64_Binop]];
    norm [delta_only [`%U.bind; `%I.bind_maintained]; nbe]
  )

let lemma_add64_regi_const (r:regi) (c:int) (s:state) :
  Lemma
    (requires (is_nat64 c))
    (ensures (
        let i = Add64 (OReg r 8) (OConst c) in
        let s' = eval_ins i s in
        eval_reg64 r s' == ((eval_reg64 r s) + c) % pow2_64)) =
  let i = Add64 (OReg r 8) (OConst c) in
  let s' = eval_ins i s in
  assert (eval_reg64 r s' == ((eval_reg64 r s) + c) % pow2_64) by (
    norm [delta_fully [`%eval_ins; `%I.eval_ins; `%I.tag_of_ins; `%U.run;]];
    norm [delta_only [`%I._eval_ins_I64_Binop; `%I.op_I64_Binop]; nbe];
    norm [delta_fully [`%I.args_I64_Binop]];
    norm [delta_only [`%U.bind; `%I.bind_maintained]; nbe]
  )

let lemma_sub64_regi_const (r:regi) (c:int) (s:state) :
  Lemma
    (requires (is_nat64 c))
    (ensures (
        let i = Sub64 (OReg r 8) (OConst c) in
        let s' = eval_ins i s in
        eval_reg64 r s' == ((eval_reg64 r s) - c) % pow2_64)) =
  let i = Sub64 (OReg r 8) (OConst c) in
  let s' = eval_ins i s in
  assert (eval_reg64 r s' == ((eval_reg64 r s) - c) % pow2_64) by (
    norm [delta_fully [`%eval_ins; `%I.eval_ins; `%I.tag_of_ins; `%U.run;]];
    norm [delta_only [`%I._eval_ins_I64_Binop; `%I.op_I64_Binop]; nbe];
    norm [delta_fully [`%I.args_I64_Binop]];
    norm [delta_only [`%U.bind; `%I.bind_maintained]; nbe]
  )

(* This is stupid. Why do I need to spin this off as a lemma?! *)
let lemma_eval_3_instructions (i1 i2 i3:ins_t) (s:state) :
  Lemma
    (requires (s.ok == AllOk))
    (ensures (
        let s1 = eval_ins i1 s in
         let s2 = eval_ins i2 s1 in
         let s3 = eval_ins i3 s2 in
         (eval_inss [i1;i2;i3] s == s3))) =
  assert_norm (let s1 = eval_ins i1 s in
     let s2 = eval_ins i2 s1 in
     let s3 = eval_ins i3 s2 in
     eval_inss [i1;i2;i3] s == s3)

let lemma_i64_binop_regi_const_ok (i:ins_t) (r:regi) (c:int) (s:state) :
  Lemma
    (requires (
        (s.ok == AllOk) /\
        (I.tag_of_ins i == I.I64_Binop) /\
        (I.args_I64_Binop i == (OReg r 8, OConst c))))
    (ensures ((eval_ins i s).ok == AllOk)) =
  assert ((eval_ins i s).ok == AllOk) by (
    norm [delta_only [`%eval_ins; `%I.eval_ins]];
    grewrite (`I.tag_of_ins (`@i)) (`I.I64_Binop); flip(); smt();
    norm [delta_only [`%I._eval_ins_I64_Binop; `%I.op_I64_Binop]; nbe];
    norm [delta_only [`%U.bind; `%I.bind_maintained]; nbe];
    norm [delta];
    smt ()
  )

let lemma_cmov64_regi_const_ok (r:regi) (c:int) (s:state) :
  Lemma
    (requires (s.ok == AllOk))
    (ensures (
        let i = CMov64 (OGt64 (OReg r 8) (OConst c)) (OReg r 8) (OConst 0) in
        (eval_ins i s).ok == AllOk)) =
  let i = CMov64 (OGt64 (OReg r 8) (OConst c)) (OReg r 8) (OConst 0) in
  assert ((eval_ins i s).ok == AllOk) by (
    norm [delta_only [`%eval_ins; `%I.eval_ins]];
    grewrite (`I.tag_of_ins (`@i)) (`I.Misc); flip(); smt();
    norm [delta_only [`%I._eval_ins_Misc]; nbe];
    norm [delta_only [`%U.bind; `%I.bind_maintained]; nbe];
    norm [delta];
    smt ()
  )

let lemma_restrict_regi_to_max_ok (r:regi) (c:int) (s:state) :
  Lemma
    (requires (s.ok == AllOk))
    (ensures (
        let i = restrict_regi_to_max r c in
        (eval_ins i s).ok == AllOk)) =
  let i = restrict_regi_to_max r c in
  if is_pow2 (c + 1) then (
    lemma_i64_binop_regi_const_ok i r c s
  ) else (
    lemma_cmov64_regi_const_ok r c s
  )

let is_in_sandbox (n:int) (a:aux_info) : Tot bool =
  0 <= n && n <= a.mem_sb_size

let valid_sb_state (a:aux_info) (s:state) : GTot Type0 =
  (s.aux = a.m_aux) /\
  (s.ok = AllOk) /\
  (forall (addr:int). {:pattern (valid_addr addr s.mem)}
     addr `is_in_sandbox` a ==> valid_addr addr s.mem)

let lemma_i64_binop_regi_const_aux_maintained (i:ins_t) (r:regi) (c:int) (a:aux_info) (s:state) :
  Lemma
    (requires (
        (valid_sb_state a s) /\
        (I.tag_of_ins i == I.I64_Binop) /\
        (I.args_I64_Binop i == (OReg r 8, OConst c))))
    (ensures (valid_sb_state a (eval_ins i s))) =
  assert ((s.ok == (eval_ins i s).ok) /\
          (s.mem == (eval_ins i s).mem) /\
          (s.aux == (eval_ins i s).aux)) by (
    norm [delta_only [`%eval_ins; `%I.eval_ins]];
    grewrite (`I.tag_of_ins (`@i)) (`I.I64_Binop); flip(); smt();
    norm [delta_only [`%I._eval_ins_I64_Binop; `%I.op_I64_Binop]; nbe];
    norm [delta_only [`%U.bind; `%I.bind_maintained]; nbe];
    norm [delta];
    smt ()
  )

let lemma_restrict_regi_to_max_aux_maintained (r:regi) (c:int) (a:aux_info) (s:state) :
  Lemma
    (requires (valid_sb_state a s))
    (ensures (
        let i = restrict_regi_to_max r c in
        (valid_sb_state a (eval_ins i s)))) = ()

#push-options "--z3rlimit 30 --fuel 2 --ifuel 0"
let lemma_restrict_regi_ok (r:regi) (rng:range) (s:state) :
  Lemma
    (requires (s.ok == AllOk))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        s'.ok == AllOk)) =
  let { lower ; upper } = rng in
  if lower = 0 then (
    let i = restrict_regi_to_max r upper in
    lemma_restrict_regi_to_max_ok r upper s
  ) else if lower > 0 then (
    let i1 = Sub64 (OReg r 8) (OConst lower) in
    let i2 = restrict_regi_to_max r (upper - lower) in
    let i3 = Add64 (OReg r 8) (OConst lower) in
    let s1 = eval_ins i1 s in
    let s2 = eval_ins i2 s1 in
    let s3 = eval_ins i3 s2 in
    lemma_eval_3_instructions i1 i2 i3 s;
    lemma_i64_binop_regi_const_ok i1 r lower s;
    lemma_restrict_regi_to_max_ok r (upper - lower) s1;
    lemma_i64_binop_regi_const_ok i3 r lower s2
  ) else (
    let i1 = Add64 (OReg r 8) (OConst (-lower)) in
    let i2 = restrict_regi_to_max r (upper - lower) in
    let i3 = Sub64 (OReg r 8) (OConst (-lower)) in
    let s1 = eval_ins i1 s in
    let s2 = eval_ins i2 s1 in
    let s3 = eval_ins i3 s2 in
    lemma_eval_3_instructions i1 i2 i3 s;
    lemma_i64_binop_regi_const_ok i1 r (-lower) s;
    lemma_restrict_regi_to_max_ok r (upper - lower) s1;
    lemma_i64_binop_regi_const_ok i3 r (-lower) s2
  )
#pop-options

(* Note: [lemma_restrict_regi_value] needed to be refactored into 3
         auxiliaries, because for some reason, F* doesn't like them
         together. *)
#push-options "--fuel 2 --ifuel 0"
let lemma_restrict_regi_value_aux1 (r:regi) (rng:range) (s:state) :
  Lemma
    (requires ((s.ok == AllOk) /\ valid_range rng /\ rng.lower = 0))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        let v' = eval_reg64 r s' in
        v' `is_in_range` rng)) =
  let { lower ; upper } = rng in
  let s' = eval_inss (restrict_regi r rng) s in
  let v = eval_reg64 r s in
  let v' = eval_reg64 r s' in
  assert_spinoff (s' == eval_ins (restrict_regi_to_max r upper) s);
  lemma_and64_regi_const r upper s;
  lemma_and64 v upper
#pop-options

#restart-solver
#push-options "--z3rlimit 40"
let lemma_restrict_regi_value_aux2 (r:regi) (rng:range) (s:state) :
  Lemma
    (requires ((s.ok == AllOk) /\ valid_range rng /\ rng.lower > 0))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        let v' = eval_reg64 r s' in
        v' `is_in_range` rng)) =
  let { lower ; upper } = rng in
  let s' = eval_inss (restrict_regi r rng) s in
  let v = eval_reg64 r s in
  let v' = eval_reg64 r s' in
  let i1 = Sub64 (OReg r 8) (OConst lower) in
  let i2 = restrict_regi_to_max r (upper - lower) in
  let i3 = Add64 (OReg r 8) (OConst lower) in
  assert_spinoff ([i1;i2;i3] == restrict_regi r rng);
  let s1 = eval_ins i1 s in
  let s2 = eval_ins i2 s1 in
  let s3 = eval_ins i3 s2 in
  lemma_eval_3_instructions i1 i2 i3 s;
  assert_spinoff (s' == s3);
  lemma_and64_regi_const r (upper - lower) s1;
  lemma_and64 (eval_reg64 r s1) (upper - lower);
  lemma_add64_regi_const r lower s2;
  let v1 = eval_reg64 r s2 in
  assert_spinoff (0 <= v1 /\ v1 <= upper - lower);
  // assert_spinoff (lower <= v1 + lower /\ v1 + lower <= upper);
  // assert_spinoff (lower <= (v1 + lower) % pow2_64 /\ (v1 + lower) % pow2_64 <= upper);
  assert_spinoff (lower <= v' /\ v' <= upper);
  ()
#pop-options

#restart-solver
#push-options "--z3rlimit 50"
let lemma_restrict_regi_value_aux3 (r:regi) (rng:range) (s:state) :
  Lemma
    (requires ((s.ok == AllOk) /\ valid_range rng /\ rng.lower < 0))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        let v' = eval_reg64 r s' in
        v' `is_in_range` rng)) =
  let { lower ; upper } = rng in
  let s' = eval_inss (restrict_regi r rng) s in
  let v = eval_reg64 r s in
  let v' = eval_reg64 r s' in
  let i1 = Add64 (OReg r 8) (OConst (-lower)) in
  let i2 = restrict_regi_to_max r (upper - lower) in
  let i3 = Sub64 (OReg r 8) (OConst (-lower)) in
  assert_spinoff ([i1;i2;i3] == restrict_regi r rng);
  let s1 = eval_ins i1 s in
  let s2 = eval_ins i2 s1 in
  let s3 = eval_ins i3 s2 in
  lemma_eval_3_instructions i1 i2 i3 s;
  assert_spinoff (s' == s3);
  lemma_and64_regi_const r (upper - lower) s1;
  lemma_and64 (eval_reg64 r s1) (upper - lower);
  lemma_sub64_regi_const r (-lower) s2;
  let v1 = eval_reg64 r s2 in
  assert_spinoff (0 <= v1 /\ v1 <= upper - lower);
  assert_spinoff (lower <= v1 + lower /\ v1 + lower <= upper);
  ()
#pop-options

let lemma_restrict_regi_value (r:regi) (rng:range) (s:state) :
  Lemma
    (requires ((s.ok == AllOk) /\ valid_range rng))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        let v' = eval_reg64 r s' in
        v' `is_in_range` rng)) =
  let { lower ; upper } = rng in
  if lower = 0 then (
    lemma_restrict_regi_value_aux1 r rng s
  ) else if lower > 0 then (
    lemma_restrict_regi_value_aux2 r rng s
  ) else (
    lemma_restrict_regi_value_aux3 r rng s
  )

#push-options "--z3rlimit 10 --fuel 2 --ifuel 0"
let lemma_restrict_regi_aux_maintenance (r:regi) (rng:range) (a:aux_info) (s:state) :
  Lemma
    (requires (valid_range rng /\ valid_sb_state a s))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        valid_sb_state a s')) =
  let s' = eval_inss (restrict_regi r rng) s in
  let { lower ; upper } = rng in
  if lower = 0 then (
    let i = restrict_regi_to_max r upper in
    lemma_restrict_regi_to_max_aux_maintained r upper a s
  ) else if lower > 0 then (
    let i1 = Sub64 (OReg r 8) (OConst lower) in
    let i2 = restrict_regi_to_max r (upper - lower) in
    let i3 = Add64 (OReg r 8) (OConst lower) in
    let s1 = eval_ins i1 s in
    let s2 = eval_ins i2 s1 in
    let s3 = eval_ins i3 s2 in
    lemma_eval_3_instructions i1 i2 i3 s;
    lemma_i64_binop_regi_const_aux_maintained i1 r lower a s;
    lemma_restrict_regi_to_max_aux_maintained r (upper - lower) a s1;
    lemma_i64_binop_regi_const_aux_maintained i3 r lower a s2
  ) else (
    let i1 = Add64 (OReg r 8) (OConst (-lower)) in
    let i2 = restrict_regi_to_max r (upper - lower) in
    let i3 = Sub64 (OReg r 8) (OConst (-lower)) in
    let s1 = eval_ins i1 s in
    let s2 = eval_ins i2 s1 in
    let s3 = eval_ins i3 s2 in
    lemma_eval_3_instructions i1 i2 i3 s;
    lemma_i64_binop_regi_const_aux_maintained i1 r (-lower) a s;
    lemma_restrict_regi_to_max_aux_maintained r (upper - lower) a s1;
    lemma_i64_binop_regi_const_aux_maintained i3 r (-lower) a s2
  )
#pop-options

let lemma_restrict_regi (r:regi) (rng:range) (a:aux_info) (s:state) :
  Lemma
    (requires (valid_range rng /\ valid_sb_state a s))
    (ensures (
        let s' = eval_inss (restrict_regi r rng) s in
        let v' = eval_reg64 r s' in
        v' `is_in_range` rng /\ valid_sb_state a s')) =
  lemma_restrict_regi_ok r rng s;
  lemma_restrict_regi_value r rng s;
  lemma_restrict_regi_aux_maintenance r rng a s

let valid_sb_size (a:aux_info) : Tot bool =
  0 <= a.mem_sb_size && is_nat64 a.mem_sb_size && a.mem_sb_size > 8

type access_size = (n:nat{n = 1 \/ n = 2 \/ n = 4 \/ n = 8})

let sandboxed_address (v:int) (as:access_size) (a:aux_info) : Tot bool =
  match as with
  | 1 ->
    (v+0) `is_in_sandbox` a
  | 2 ->
    (v+0) `is_in_sandbox` a &&
    (v+1) `is_in_sandbox` a
  | 4 ->
    (v+0) `is_in_sandbox` a &&
    (v+1) `is_in_sandbox` a &&
    (v+2) `is_in_sandbox` a &&
    (v+3) `is_in_sandbox` a
  | 8 ->
    (v+0) `is_in_sandbox` a &&
    (v+1) `is_in_sandbox` a &&
    (v+2) `is_in_sandbox` a &&
    (v+3) `is_in_sandbox` a &&
    (v+4) `is_in_sandbox` a &&
    (v+5) `is_in_sandbox` a &&
    (v+6) `is_in_sandbox` a &&
    (v+7) `is_in_sandbox` a

#push-options "--z3rlimit 10 --z3cliopt smt.arith.nl=true"
(** Sandbox a single memory address *)
let sandbox_maddr (a:aux_info) (as:access_size) (rel_m:maddr) (s: erased state) :
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         let s' = eval_inss r s in
         let v = eval_maddr rel_m s' in
         valid_sb_state a s' /\
         sandboxed_address v as a)) =
  match rel_m with
  | MIndex scale index offset ->
    if scale <= 0 then (
      fail_with ("Received a memory referrence with scale: " ^ string_of_int scale)
    ) else if (offset < 0 || offset >= pow2_64) then (
      fail_with ("Received invalid maddr offset: " ^ string_of_int offset)
    ) else if (a.mem_sb_size - as < offset) then (
      fail_with ("Sandbox size is too small! Trying to use an offset " ^ string_of_int offset)
    ) else (
      // XXX: Deliberate oversimplification here. Technically we
      // _should_ be using a change in the `lower` value too, but
      // based on the current model of the semantics, it seems like we
      // only treat it as an unsigned number for the value of the
      // register, which means that we cannot really get negative
      // values anyways.
      let rng = { lower = 0 ; upper = ((a.mem_sb_size - as) - offset) / scale } in
      lemma_restrict_regi index rng a s;
      let r = restrict_regi index rng in
      let s' : erased _ = eval_inss r s in
      let v : erased _ = eval_maddr rel_m s' in
      // assert (valid_sb_state a s');
      // assert (v `is_in_sandbox` a);
      // assert ((v + as - 1) `is_in_sandbox` a);
      // assert (sandboxed_address v as a);
      r
    )
#pop-options

type operand =
  | IntOp: o:operandi -> operand
  | FloatOp: o:operandf -> operand

unfold
inline_for_extraction
let generic_operand_lift (#t:Type) (f:operandi -> t) (g:operandf -> t) : Tot (operand -> t) =
  allow_inversion operand;
  fun o -> match o with
    | IntOp o -> f o
    | FloatOp o -> g o

let string_of_operand = generic_operand_lift string_of_operandi string_of_operandf

type usage_t : eqtype =
  | Src
  | Dst
  | Both

let valid_src_operandi (as:access_size) (o:operandi) (s:state) : Tot bool =
  match as with
  | 1 -> valid_src_operand8 o s = AllOk
  | 2 -> valid_src_operand16 o s = AllOk
  | 4 -> valid_src_operand32 o s = AllOk
  | 8 -> valid_src_operand64 o s = AllOk

let valid_src_operandf (as:access_size) (o:operandf) (s:state) : Tot bool =
  match as with
  | 1 -> false
  | 2 -> false
  | 4 -> valid_src_operandf32 o s = AllOk
  | 8 -> valid_src_operandf64 o s = AllOk

let valid_dst_operandi (as:access_size) (o:operandi) (s:state) : Tot bool =
  match as with
  | 1 -> U.valid_dst_operand8 o s = AllOk
  | 2 -> U.valid_dst_operand16 o s = AllOk
  | 4 -> U.valid_dst_operand32 o s = AllOk
  | 8 -> U.valid_dst_operand64 o s = AllOk

let valid_dst_operandf (as:access_size) (o:operandf) (s:state) : Tot bool =
  match as with
  | 1 -> false
  | 2 -> false
  | 4 -> U.valid_dst_operandf32 o s = AllOk
  | 8 -> U.valid_dst_operandf64 o s = AllOk

let valid_operandi (u:usage_t) (as:access_size) (o:operandi) (s:state) : Tot bool =
  allow_inversion usage_t;
  match u with
  | Src -> valid_src_operandi as o s
  | Dst -> valid_dst_operandi as o s
  | Both -> valid_src_operandi as o s && valid_dst_operandi as o s

let valid_operandf (u:usage_t) (as:access_size) (o:operandf) (s:state) : Tot bool =
  allow_inversion usage_t;
  match u with
  | Src -> valid_src_operandf as o s
  | Dst -> valid_dst_operandf as o s
  | Both -> valid_src_operandf as o s && valid_dst_operandf as o s

let is_memory_ref_i (o:operandi) : Tot bool =
  allow_inversion operandi;
  match o with
  | OConst _ | OReg _ _ | ONamedGlobal _ -> false
  | OMemRel _ | OStackRel _ -> true

let is_memory_ref_f (o:operandf) : Tot bool =
  allow_inversion operandf;
  match o with
  | OConst_f _ | OReg_f _ _ | ONamedGlobal_f _ -> false
  | OMemRel_f _ | OStackRel_f _ -> true

let is_memory_ref (o:operand) : Tot bool =
  generic_operand_lift is_memory_ref_i is_memory_ref_f o

#push-options "--fuel 1 --ifuel 1"
(** Sandbox a single operandi *)
let sandbox_operandi (usage:usage_t) (a:aux_info) (o:operandi) (as:access_size) (s:erased state) :
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (not (is_memory_ref_i o) ==> Nil? r /\ eval_inss r s == reveal s) /\
         valid_sb_state a (eval_inss r s) /\
         valid_operandi usage as o (eval_inss r s))) =
  match o with
  | OMemRel offset ->
    let r = sandbox_maddr a as offset s in
    let s' : erased state = eval_inss r s in
    let m : erased int = eval_maddr offset s' in
    // assert (valid_sb_state a s');
    // assert (as = 1 ==> valid_addr m s'.mem);
    // assert (as = 2 ==> valid_addr16 m s'.mem);
    // assert (as = 4 ==> valid_addr32 m s'.mem);
    // assert (as = 8 ==> valid_addr64 m s'.mem);
    // assert (as = 1 ==> U.valid_dst_operand8 o s' == AllOk);
    // assert (as = 2 ==> U.valid_dst_operand16 o s' == AllOk);
    // assert (as = 4 ==> U.valid_dst_operand32 o s' == AllOk);
    // assert (as = 8 ==> U.valid_dst_operand64 o s' == AllOk);
    // assert (as = 1 ==> valid_src_operand8 o s' == AllOk);
    // assert (as = 2 ==> valid_src_operand16 o s' == AllOk);
    // assert (as = 4 ==> valid_src_operand32 o s' == AllOk);
    // assert (as = 8 ==> valid_src_operand64 o s' == AllOk);
    // assert (valid_dst_operandi as o s');
    // assert (valid_src_operandi as o s');
    // assert (valid_operandi usage as o s');
    r
  | OStackRel _ ->
    (* NOTE: We decided that stack-relative stuff would be handled via
     guard-pages, and not via an explicitly added SFI check. I _still_
     believe we should have a static guard to prevent it from skipping
     past the guard pages, but I am not entirely sure how that may be
     done, without incurring the full overhead. In any case, if we do
     need to / plan to use this, we can simply switch it out from an
     Ok[] to match the same as OMemRel. *)
     admit (); (* Property of register allocator. Cannot be affected adversarially. *)
     []
  | OConst _ -> if usage = Src then [] else fail_with "Cannot use constant as destination"
  | OReg reg sz ->
    if valid_reg_int reg then (
      if sz = as then (
        []
      ) else (
        fail_with ("Impossible! Bad register access size reg=" ^ string_of_int reg ^
                   " sz=" ^ string_of_int sz ^ " as=" ^ string_of_int as)
      )
    ) else (
      fail_with ("Impossible! Got a bad register " ^ string_of_int reg)
    )
  | ONamedGlobal (Ident ident)
    ->
    if (ident < 0 ||
        ident >= length a.m_aux.globals) then (
      fail_with ("Invalid global: " ^ string_of_int ident)
    ) else (
      let t = (index a.m_aux.globals ident).gbl_ty in
      if (as = 8 && t = I64_ty) || (as = 4 && t = I32_ty) then (
        []
      ) else (
        fail_with ("Invalid global type: " ^ string_of_int ident)
      )
    )
  | ONamedGlobal MemPages ->
    if as = 4 then [] else fail_with ("MemPages accessed with non-4: " ^ string_of_int as)
#pop-options

#push-options "--fuel 1 --ifuel 1"
(** Sandbox a single operandf *)
let sandbox_operandf (usage:usage_t) (a:aux_info) (o:operandf) (as:access_size) (s:erased state) :
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (not (is_memory_ref_f o) ==> Nil? r /\ eval_inss r s == reveal s) /\
         valid_sb_state a (eval_inss r s) /\
         valid_operandf usage as o (eval_inss r s))) =
  if as = 1 || as = 2 then
    fail_with ("Invalid access size " ^ string_of_int as ^
               " for floating operand " ^ string_of_operandf o) else
  match o with
  | OMemRel_f offset ->
    let r = sandbox_maddr a as offset s in
    let s' : erased state = eval_inss r s in
    let m : erased int = eval_maddr offset s' in
    // assert (valid_sb_state a s');
    // assert (as = 1 ==> valid_addr m s'.mem);
    // assert (as = 2 ==> valid_addr16 m s'.mem);
    // assert (as = 4 ==> valid_addr32 m s'.mem);
    // assert (as = 8 ==> valid_addr64 m s'.mem);
    // assert (as = 4 ==> U.valid_dst_operandf32 o s' == AllOk);
    // assert (as = 8 ==> U.valid_dst_operandf64 o s' == AllOk);
    // assert (as = 4 ==> valid_src_operandf32 o s' == AllOk);
    // assert (as = 8 ==> valid_src_operandf64 o s' == AllOk);
    // assert (valid_dst_operandf as o s');
    // assert (valid_src_operandf as o s');
    // assert (valid_operandf usage as o s');
    r
  | OStackRel_f _ ->
    (* NOTE: We decided that stack-relative stuff would be handled via
     guard-pages, and not via an explicitly added SFI check. I _still_
     believe we should have a static guard to prevent it from skipping
     past the guard pages, but I am not entirely sure how that may be
     done, without incurring the full overhead. In any case, if we do
     need to / plan to use this, we can simply switch it out from an
     Ok[] to match the same as OMemRel. *)
     admit (); (* Property of register allocator. Cannot be affected adversarially. *)
     []
  | OConst_f _ -> if usage = Src then [] else fail_with "Cannot use constant as destination"
  | OReg_f reg sz ->
    if valid_reg_float reg then (
      if sz = as then (
        []
      ) else (
        fail_with ("Impossible! Bad floating register access size reg=" ^ string_of_int reg ^
                   " sz=" ^ string_of_int sz ^ " as=" ^ string_of_int as)
      )
    ) else (
      fail_with ("Impossible! Got a bad register " ^ string_of_int reg)
    )
  | ONamedGlobal_f (Ident_f ident)
    ->
    if (ident < 0 ||
        ident >= length a.m_aux.globals) then (
      fail_with ("Invalid floating global: " ^ string_of_int ident)
    ) else (
      let t = (index a.m_aux.globals ident).gbl_ty in
      if (as = 8 && t = F64_ty) || (as = 4 && t = F32_ty) then (
        []
      ) else (
        fail_with ("Invalid floating global type: " ^ string_of_int ident)
      )
    )
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_eval_inss_append (is1 is2:list ins_t) (s:state) :
  Lemma
    (requires (True))
    (ensures (
        let s1 = eval_inss is1 s in
        let s2 = eval_inss is2 s1 in
        eval_inss (is1 @ is2) s == s2)) =
  match is1 with
  | [] -> ()
  | h :: t ->
    lemma_eval_inss_append t is2 (eval_ins h s)
#pop-options

let lemma_eval_inss_ins_append (is:list ins_t) (i:ins_t) (s:state) :
  Lemma
    (requires (True))
    (ensures (
        let s1 = eval_inss is s in
        let s2 = eval_ins i s1 in
        eval_inss (is @ [i]) s == s2)) =
  let s1 = eval_inss is s in
  let s2 = eval_ins i s1 in
  assert_norm (eval_inss [i] s1 == s2); // OBSERVE
  lemma_eval_inss_append is [i] s

let upto_one_mem_ref (o1 o2:operand) :
  Err unit
    (requires True)
    (ensures (fun () -> ~(is_memory_ref o1 /\ is_memory_ref o2))) =
  if is_memory_ref o1 && is_memory_ref o2 then (
    fail_with ("Cannot have two memory references: " ^
               string_of_operand o1 ^ " and " ^ string_of_operand o2)
  ) else ()

let lemma_eval_ins_maintains_aux (i:ins_t) (s:state) :
  Lemma
    (ensures ((eval_ins i s).aux = s.aux)) = ()

#push-options "--fuel 1"
let rec lemma_eval_inss_maintains_aux (is:list ins_t) (s:state) :
  Lemma
    (ensures ((eval_inss is s).aux = s.aux)) =
  allow_inversion (list ins_t);
  match is with
  | [] -> ()
  | h :: t ->
    lemma_eval_ins_maintains_aux h s;
    lemma_eval_inss_maintains_aux t (eval_ins h s)
#pop-options

let lemma_eval_step'_maintains_aux (c:list precode) (p:precode) (s:state) :
  Lemma
    (ensures ((fst (eval_step' c p s)).aux = s.aux)) =
  allow_inversion precode;
  match p with
  | FnEntry _ _ -> ()
  | FnExit _ -> ()
  | Ins i _ -> lemma_eval_ins_maintains_aux i s
  | InsList is _ -> lemma_eval_inss_maintains_aux is s
  | Nop _ -> ()
  | Cmp _ _ _ -> ()
  | Switch _ _ -> ()
  | Call target next -> ()
  | HighCall _ _ _ _ -> ()
  | Ret _ -> ()
  | HighRet _ _ -> ()

let lemma_eval_step_maintains_aux (c:list precode) (s:state) :
  Lemma
    (ensures ((eval_step c s).aux = s.aux)) =
  if s.ip < length c then (
    lemma_eval_step'_maintains_aux c (index c s.ip) s
  )

let lemma_eval_ins_monotonic_heap (i:ins_t) (s:state) :
  Lemma
    (ensures (
        let s' = eval_ins i s in
        forall a. valid_addr a s.mem ==> valid_addr a s'.mem)) = ()

#push-options "--fuel 1"
let rec lemma_eval_inss_monotonic_heap (is:list ins_t) (s:state) :
  Lemma
    (ensures (
        let s' = eval_inss is s in
        forall a. valid_addr a s.mem ==> valid_addr a s'.mem)) =
  allow_inversion (list ins_t);
  match is with
  | [] -> ()
  | h :: t ->
    lemma_eval_ins_monotonic_heap h s;
    lemma_eval_inss_monotonic_heap t (eval_ins h s)
#pop-options

let lemma_eval_step'_monotonic_heap (c:cfg) (p:precode) (s:state) :
  Lemma
    (ensures (
        let s', _ = eval_step' c p s in
        forall a. valid_addr a s.mem ==> valid_addr a s'.mem)) =
  allow_inversion precode;
  match p with
  | FnEntry _ _ -> ()
  | FnExit _ -> ()
  | Ins i _ -> lemma_eval_ins_monotonic_heap i s
  | InsList is _ -> lemma_eval_inss_monotonic_heap is s
  | Nop _ -> ()
  | Cmp _ _ _ -> ()
  | Switch _ _ -> ()
  | Call target next -> ()
  | HighCall _ _ _ _ -> ()
  | Ret _ -> ()
  | HighRet _ _ -> ()

let lemma_eval_step_monotonic_heap (c:cfg) (s:state) :
  Lemma
    (ensures (
        let s' = eval_step c s in
        forall a. valid_addr a s.mem ==> valid_addr a s'.mem)) =
  if s.ip < length c then (
    lemma_eval_step'_monotonic_heap c (index c s.ip) s
  )

let lemma_eval_ins_maintains_validity (a:aux_info) (i:ins_t) (s:state) :
  Lemma
    (requires (valid_sb_state a s /\ (eval_ins i s).ok == AllOk))
    (ensures (valid_sb_state a (eval_ins i s))) =
  lemma_eval_ins_maintains_aux i s;
  lemma_eval_ins_monotonic_heap i s

let lemma_eval_ins_maintains_callstack (i:ins_t) (s:state) :
  Lemma
    (requires (True))
    (ensures (s.callstack == (eval_ins i s).callstack)) = ()

#push-options "--fuel 1 --ifuel 1"
let rec lemma_eval_inss_maintains_callstack (is:list ins_t) (s:state) :
  Lemma
    (requires (True))
    (ensures (s.callstack == (eval_inss is s).callstack)) =
  match is with
  | [] -> ()
  | h :: t ->
    lemma_eval_ins_maintains_callstack h s;
    lemma_eval_inss_maintains_callstack t (eval_ins h s)
#pop-options

type _compile_ins_t tag =
  (a:aux_info) ->
  (i:ins_t{I.tag_of_ins i = tag}) ->
  (s:erased state) ->
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (valid_sb_state a (eval_inss r s)) /\
         (Cons? r)))

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let _compile_ins_StackOp : _compile_ins_t I.StackOp =
  fun a i s ->
    match i with
    | Alloc _ | Dealloc _ ->
      assert_norm (eval_ins i s == eval_inss [i] s);
      lemma_eval_ins_maintains_validity a i s;
      [i]
    | Push o ->
      let sb = sandbox_operandi Src a o 8 s in
      let r = sb @ [i] in
      // assert ((eval_ins i (eval_inss sb s)).ok == AllOk);
      // assert (valid_sb_state a (eval_inss sb s));
      // assert (valid_sb_state a (eval_ins i (eval_inss sb s)));
      lemma_eval_inss_ins_append sb i s;
      // assert (valid_sb_state a (eval_inss r s));
      // assert (Cons? r);
      r
    | Pop o ->
      let sb = sandbox_operandi Dst a o 8 s in
      let r = sb @ [i] in
      lemma_eval_inss_ins_append sb i s;
      // assert (valid_sb_state a (eval_inss sb s));
      // assert (U.valid_dst_operand64 o (eval_inss sb s) == AllOk);
      assume (valid_src_operand64 (OStackRel 0 <: operandi) (eval_inss sb s) == AllOk); (* Property of register allocator. Cannot be affected adversarially. *)
      // assert ((eval_ins i (eval_inss sb s)).ok == AllOk);
      r
#pop-options

#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let _compile_ins_Mov : _compile_ins_t I.Mov =
  fun a i s ->
  let o1, o2 = match i with | Mov8 o1 o2 | Mov16 o1 o2 | Mov32 o1 o2 | Mov64 o1 o2 -> o1, o2 in
  let bytecount = match i with | Mov8 _ _ -> 1 | Mov16 _ _ -> 2 | Mov32 _ _ -> 4 | Mov64 _ _ -> 8 in
  upto_one_mem_ref (IntOp o1) (IntOp o2);
  let sb1 = sandbox_operandi Dst a o1 bytecount s in
  let sb2 = sandbox_operandi Src a o2 bytecount (eval_inss sb1 s) in
  let r = sb1 @ sb2 @ [i] in
  // assert (r == sb1 @ (sb2 @ [i]));
  // assert (valid_sb_state a (eval_inss sb1 s));
  // assert (valid_sb_state a (eval_inss sb2 (eval_inss sb1 s)));
  // assert (U.valid_dst_operand8 o1 (eval_inss sb2 (eval_inss sb1 s)) == AllOk);
  // assert ((eval_ins i (eval_inss sb2 (eval_inss sb1 s))).ok == AllOk);
  // assert ((eval_ins i (eval_inss sb2 (eval_inss sb1 s))).aux = a.m_aux);
  // assert ((eval_ins i (eval_inss sb2 (eval_inss sb1 s))).ok = AllOk);
  lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
  lemma_eval_inss_append sb1 (sb2 @ [i]) s;
  let s' : erased state = eval_inss r s in
  assert (s'.aux = a.m_aux); (* OBSERVE *)
  (
    match i with
    | Mov8 _ _ -> assert_spinoff (s'.ok = AllOk)
    | Mov16 _ _ -> assert_spinoff (s'.ok = AllOk)
    | Mov32 _ _ -> assert_spinoff (s'.ok = AllOk)
    | Mov64 _ _ -> assert_spinoff (s'.ok = AllOk)
  ); (* OBSERVE: Makes the proof obligation much more tractable *)
  assert (s'.ok = AllOk);
  lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
  // assert ((forall (addr:int). {:pattern (valid_addr addr s'.mem)}
  //            addr `is_in_sandbox` a ==> valid_addr addr s'.mem));
  // assert (valid_sb_state a (eval_ins i (eval_inss sb2 (eval_inss sb1 s))));
  r
#pop-options

#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let _compile_ins_I32_Binop : _compile_ins_t I.I32_Binop =
  fun a i s ->
    let o1, o2 = I.args_I32_Binop i in
    upto_one_mem_ref (IntOp o1) (IntOp o2);
    let sb1 = sandbox_operandi Both a o1 4 s in
    let sb2 = sandbox_operandi Src a o2 4 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

#restart-solver
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let _compile_ins_I64_Binop : _compile_ins_t I.I64_Binop =
  fun a i s ->
    let o1, o2 = I.args_I64_Binop i in
    upto_one_mem_ref (IntOp o1) (IntOp o2);
    let sb1 = sandbox_operandi Both a o1 8 s in
    let sb2 = sandbox_operandi Src a o2 8 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

#restart-solver
#push-options "--fuel 2 --ifuel 0"
let _compile_ins_Misc : _compile_ins_t I.Misc =
  fun a i s ->
    match i with
    | Unreachable ->
      assert_norm ((eval_ins i s).ok == AllOk); (* OBSERVE *)
      lemma_eval_ins_maintains_validity a i s;
      [i]
    | CMov64 cond dst src ->
      fail_with "Received CMov64 as input at _compile_ins_Misc. Should not happen."
#pop-options

let dst_op_size_movx (i:ins_t{I.tag_of_ins i = I.Movzx \/ I.tag_of_ins i = I.Movsx}) : access_size =
  match i with
  | MovZX8to32 _ _ | MovSX8to32 _ _ -> 4
  | MovZX8to64 _ _ | MovSX8to64 _ _ -> 8
  | MovZX16to32 _ _ | MovSX16to32 _ _ -> 4
  | MovZX16to64 _ _ | MovSX16to64 _ _ -> 8
  | MovZX32to64 _ _ | MovSX32to64 _ _ -> 8

let src_op_size_movx (i:ins_t{I.tag_of_ins i = I.Movzx \/ I.tag_of_ins i = I.Movsx}) : access_size =
  match i with
  | MovZX8to32 _ _ | MovSX8to32 _ _ -> 1
  | MovZX8to64 _ _ | MovSX8to64 _ _ -> 1
  | MovZX16to32 _ _ | MovSX16to32 _ _ -> 2
  | MovZX16to64 _ _ | MovSX16to64 _ _ -> 2
  | MovZX32to64 _ _ | MovSX32to64 _ _ -> 4

#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let _compile_ins_Movzx : _compile_ins_t I.Movzx =
  fun a i s ->
    match i with
    | MovZX8to32 o1 o2
    | MovZX8to64 o1 o2
    | MovZX16to32 o1 o2
    | MovZX16to64 o1 o2
    | MovZX32to64 o1 o2 ->
      upto_one_mem_ref (IntOp o1) (IntOp o2);
      let sb1 = sandbox_operandi Dst a o1 (dst_op_size_movx i) s in
      let sb2 = sandbox_operandi Src a o2 (src_op_size_movx i) (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased state = eval_inss r s in
      (
        match i with
        | MovZX8to32 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovZX8to64 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovZX16to32 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovZX16to64 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovZX32to64 _ _ -> assert_spinoff (s'.ok = AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#restart-solver
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let _compile_ins_Movsx : _compile_ins_t I.Movsx =
  fun a i s ->
    match i with
    | MovSX8to32 o1 o2
    | MovSX8to64 o1 o2
    | MovSX16to32 o1 o2
    | MovSX16to64 o1 o2
    | MovSX32to64 o1 o2 ->
      upto_one_mem_ref (IntOp o1) (IntOp o2);
      let sb1 = sandbox_operandi Dst a o1 (dst_op_size_movx i) s in
      let sb2 = sandbox_operandi Src a o2 (src_op_size_movx i) (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased state = eval_inss r s in
      (
        match i with
        | MovSX8to32 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovSX8to64 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovSX16to32 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovSX16to64 _ _ -> assert_spinoff (s'.ok = AllOk)
        | MovSX32to64 _ _ -> assert_spinoff (s'.ok = AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--fuel 0 --ifuel 0"
let lemma_valid_operands_means_ok_I32_Unop (i:ins_t) (s:state) :
  Lemma
    (requires (
        (s.ok = AllOk) /\
        (I.tag_of_ins i == I.I32_Unop) /\ (
          let o1, o2 = I.args_I32_Unop i in
          (valid_operandi Dst 4 o1 s) /\
          (valid_operandi Src 4 o2 s))))
    (ensures (
        (eval_ins i s).ok = AllOk)) =
  // assert ((eval_ins i s).ok = AllOk) by (
  //   norm [delta_fully [`%eval_ins; `%I.eval_ins; `%U.run;]];
  //   grewrite (`I.tag_of_ins (`@i)) (`I.I32_Unop); flip (); smt ();
  //   norm [iota];
  //   norm [delta_fully [`%I._eval_ins_I32_Unop]];
  //   norm [zeta_full; delta_fully [`%I.bind_maintained; `%U.bind; `%U.get]];
  //   norm [zeta_full; delta_fully [`%U.st; `%U.st_maintained]];
  //   smt ()
  // );
  ()
#pop-options

#push-options "--fuel 1 --ifuel 0"
let _compile_ins_I32_Unop : _compile_ins_t I.I32_Unop =
  fun a i s ->
    let o1, o2 = I.args_I32_Unop i in
    upto_one_mem_ref (IntOp o1) (IntOp o2);
    let sb1 = sandbox_operandi Dst a o1 4 s in
    let sb2 = sandbox_operandi Src a o2 4 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_valid_operands_means_ok_I32_Unop i (eval_inss sb2 (eval_inss sb1 s));
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    let s' : erased state = eval_inss r s in
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

#push-options "--fuel 0 --ifuel 0"
let lemma_valid_operands_means_ok_I64_Unop (i:ins_t) (s:state) :
  Lemma
    (requires (
        (s.ok = AllOk) /\
        (I.tag_of_ins i == I.I64_Unop) /\ (
          let o1, o2 = I.args_I64_Unop i in
          (valid_operandi Dst 8 o1 s) /\
          (valid_operandi Src 8 o2 s))))
    (ensures (
        (eval_ins i s).ok = AllOk)) =
  // assert ((eval_ins i s).ok = AllOk) by (
  //   norm [delta_fully [`%eval_ins; `%I.eval_ins; `%U.run;]];
  //   grewrite (`I.tag_of_ins (`@i)) (`I.I64_Unop); flip (); smt ();
  //   norm [iota];
  //   norm [delta_fully [`%I._eval_ins_I64_Unop]];
  //   norm [zeta_full; delta_fully [`%I.bind_maintained; `%U.bind; `%U.get]];
  //   norm [zeta_full; delta_fully [`%U.st; `%U.st_maintained]];
  //   smt ()
  // );
  ()
#pop-options

#push-options "--fuel 1 --ifuel 0"
let _compile_ins_I64_Unop : _compile_ins_t I.I64_Unop =
  fun a i s ->
    let o1, o2 = I.args_I64_Unop i in
    upto_one_mem_ref (IntOp o1) (IntOp o2);
    let sb1 = sandbox_operandi Dst a o1 8 s in
    let sb2 = sandbox_operandi Src a o2 8 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_valid_operands_means_ok_I64_Unop i (eval_inss sb2 (eval_inss sb1 s));
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    let s' : erased state = eval_inss r s in
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_FMov : _compile_ins_t I.FMov =
  fun a i s ->
    match i with
    | FMov32 o1 o2 ->
      upto_one_mem_ref (FloatOp o1) (FloatOp o2);
      let sb1 = sandbox_operandf Dst a o1 4 s in
      let sb2 = sandbox_operandf Src a o2 4 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
    | FMov64 o1 o2 ->
      upto_one_mem_ref (FloatOp o1) (FloatOp o2);
      let sb1 = sandbox_operandf Dst a o1 8 s in
      let sb2 = sandbox_operandf Src a o2 8 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

let lemma_valid_operands_means_ok_F32_Unop (i:ins_t) (s:state) :
  Lemma
    (requires (
        (s.ok = AllOk) /\
        (I.tag_of_ins i == I.F32_Unop) /\ (
          let o1, o2 = I.args_F32_Unop i in
          (valid_operandf Dst 4 o1 s) /\
          (valid_operandf Src 4 o2 s))))
    (ensures (
        (eval_ins i s).ok = AllOk)) = ()

#push-options "--fuel 1 --ifuel 0"
let _compile_ins_F32_Unop : _compile_ins_t I.F32_Unop =
  fun a i s ->
    let o1, o2 = I.args_F32_Unop i in
    upto_one_mem_ref (FloatOp o1) (FloatOp o2);
    let sb1 = sandbox_operandf Dst a o1 4 s in
    let sb2 = sandbox_operandf Src a o2 4 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_valid_operands_means_ok_F32_Unop i (eval_inss sb2 (eval_inss sb1 s));
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    let s' : erased state = eval_inss r s in
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

let lemma_valid_operands_means_ok_F64_Unop (i:ins_t) (s:state) :
  Lemma
    (requires (
        (s.ok = AllOk) /\
        (I.tag_of_ins i == I.F64_Unop) /\ (
          let o1, o2 = I.args_F64_Unop i in
          (valid_operandf Dst 8 o1 s) /\
          (valid_operandf Src 8 o2 s))))
    (ensures (
        (eval_ins i s).ok = AllOk)) = ()

#push-options "--fuel 1 --ifuel 0"
let _compile_ins_F64_Unop : _compile_ins_t I.F64_Unop =
  fun a i s ->
    let o1, o2 = I.args_F64_Unop i in
    upto_one_mem_ref (FloatOp o1) (FloatOp o2);
    let sb1 = sandbox_operandf Dst a o1 8 s in
    let sb2 = sandbox_operandf Src a o2 8 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_valid_operands_means_ok_F64_Unop i (eval_inss sb2 (eval_inss sb1 s));
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    let s' : erased state = eval_inss r s in
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

#push-options "--z3rlimit 50"
let lemma_valid_operands_means_ok_F32_Binop (i:ins_t) (s:state) :
  Lemma
    (requires (
        (s.ok = AllOk) /\
        (I.tag_of_ins i == I.F32_Binop) /\ (
          let o1, o2 = I.args_F32_Binop i in
          (valid_operandf Both 4 o1 s) /\
          (valid_operandf Src 4 o2 s))))
    (ensures (
        (eval_ins i s).ok = AllOk)) = ()
#pop-options

#push-options "--fuel 1 --ifuel 0"
let _compile_ins_F32_Binop : _compile_ins_t I.F32_Binop =
  fun a i s ->
    let o1, o2 = I.args_F32_Binop i in
    upto_one_mem_ref (FloatOp o1) (FloatOp o2);
    let sb1 = sandbox_operandf Both a o1 4 s in
    let sb2 = sandbox_operandf Src a o2 4 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_valid_operands_means_ok_F32_Binop i (eval_inss sb2 (eval_inss sb1 s));
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    let s' : erased state = eval_inss r s in
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

#push-options "--z3rlimit 50"
let lemma_valid_operands_means_ok_F64_Binop (i:ins_t) (s:state) :
  Lemma
    (requires (
        (s.ok = AllOk) /\
        (I.tag_of_ins i == I.F64_Binop) /\ (
          let o1, o2 = I.args_F64_Binop i in
          (valid_operandf Both 8 o1 s) /\
          (valid_operandf Src 8 o2 s))))
    (ensures (
        (eval_ins i s).ok = AllOk)) = ()
#pop-options

#push-options "--fuel 1 --ifuel 0"
let _compile_ins_F64_Binop : _compile_ins_t I.F64_Binop =
  fun a i s ->
    let o1, o2 = I.args_F64_Binop i in
    upto_one_mem_ref (FloatOp o1) (FloatOp o2);
    let sb1 = sandbox_operandf Both a o1 8 s in
    let sb2 = sandbox_operandf Src a o2 8 (eval_inss sb1 s) in
    let r = sb1 @ sb2 @ [i] in
    lemma_valid_operands_means_ok_F64_Binop i (eval_inss sb2 (eval_inss sb1 s));
    lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
    lemma_eval_inss_append sb1 (sb2 @ [i]) s;
    let s' : erased state = eval_inss r s in
    lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
    r
#pop-options

type _compile_ins_t_Conversion (pred:ins_t -> bool) =
  (a:aux_info) ->
  (i:ins_t{I.tag_of_ins i = I.Conversion /\ pred i}) ->
  (s:erased state) ->
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (valid_sb_state a (eval_inss r s)) /\
         (Cons? r)))

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_i32_f32 : _compile_ins_t_Conversion (fun i -> I32TruncSF32? i || I32TruncUF32? i || ReinterpretFloat32? i) =
  fun a i s ->
    match i with
    | I32TruncSF32 dst src | I32TruncUF32 dst src | ReinterpretFloat32 dst src ->
      upto_one_mem_ref (IntOp dst) (FloatOp src);
      let sb1 = sandbox_operandi Dst a dst 4 s in
      let sb2 = sandbox_operandf Src a src 4 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | I32TruncSF32 dst src -> assert_spinoff (s'.ok == AllOk)
        | I32TruncUF32 dst src -> assert_spinoff (s'.ok == AllOk)
        | ReinterpretFloat32 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_i32_f64 : _compile_ins_t_Conversion (fun i -> I32TruncSF64? i || I32TruncUF64? i) =
  fun a i s ->
    match i with
    | I32TruncSF64 dst src | I32TruncUF64 dst src ->
      upto_one_mem_ref (IntOp dst) (FloatOp src);
      let sb1 = sandbox_operandi Dst a dst 4 s in
      let sb2 = sandbox_operandf Src a src 8 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | I32TruncSF64 dst src -> assert_spinoff (s'.ok == AllOk)
        | I32TruncUF64 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_i64_f32 : _compile_ins_t_Conversion (fun i -> I64TruncSF32? i || I64TruncUF32? i) =
  fun a i s ->
    match i with
    | I64TruncSF32 dst src | I64TruncUF32 dst src ->
      upto_one_mem_ref (IntOp dst) (FloatOp src);
      let sb1 = sandbox_operandi Dst a dst 8 s in
      let sb2 = sandbox_operandf Src a src 4 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | I64TruncSF32 dst src -> assert_spinoff (s'.ok == AllOk)
        | I64TruncUF32 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_i64_f64 : _compile_ins_t_Conversion (fun i -> I64TruncSF64? i || I64TruncUF64? i || ReinterpretFloat64? i) =
  fun a i s ->
    match i with
    | I64TruncSF64 dst src | I64TruncUF64 dst src | ReinterpretFloat64 dst src ->
      upto_one_mem_ref (IntOp dst) (FloatOp src);
      let sb1 = sandbox_operandi Dst a dst 8 s in
      let sb2 = sandbox_operandf Src a src 8 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | I64TruncSF64 dst src -> assert_spinoff (s'.ok == AllOk)
        | I64TruncUF64 dst src -> assert_spinoff (s'.ok == AllOk)
        | ReinterpretFloat64 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_f_f : _compile_ins_t_Conversion (fun i -> F32DemoteF64? i || F64PromoteF32? i) =
  fun a i s ->
    match i with
    | F32DemoteF64 dst src ->
      upto_one_mem_ref (FloatOp dst) (FloatOp src);
      let sb1 = sandbox_operandf Dst a dst 4 s in
      let sb2 = sandbox_operandf Src a src 8 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      assert_spinoff (s'.ok == AllOk); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
    | F64PromoteF32 dst src ->
      upto_one_mem_ref (FloatOp dst) (FloatOp src);
      let sb1 = sandbox_operandf Dst a dst 8 s in
      let sb2 = sandbox_operandf Src a src 4 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      assert_spinoff (s'.ok == AllOk); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_f32_i32 : _compile_ins_t_Conversion (fun i -> F32ConvertSI32? i || F32ConvertUI32? i || ReinterpretInt32? i) =
  fun a i s ->
    match i with
    | F32ConvertSI32 dst src | F32ConvertUI32 dst src | ReinterpretInt32 dst src ->
      upto_one_mem_ref (FloatOp dst) (IntOp src);
      let sb1 = sandbox_operandf Dst a dst 4 s in
      let sb2 = sandbox_operandi Src a src 4 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | F32ConvertSI32 dst src -> assert_spinoff (s'.ok == AllOk)
        | F32ConvertUI32 dst src -> assert_spinoff (s'.ok == AllOk)
        | ReinterpretInt32 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_f64_i32 : _compile_ins_t_Conversion (fun i -> F64ConvertSI32? i || F64ConvertUI32? i) =
  fun a i s ->
    match i with
    | F64ConvertSI32 dst src | F64ConvertUI32 dst src ->
      upto_one_mem_ref (FloatOp dst) (IntOp src);
      let sb1 = sandbox_operandf Dst a dst 8 s in
      let sb2 = sandbox_operandi Src a src 4 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | F64ConvertSI32 dst src -> assert_spinoff (s'.ok == AllOk)
        | F64ConvertUI32 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_f32_i64 : _compile_ins_t_Conversion (fun i -> F32ConvertSI64? i || F32ConvertUI64? i) =
  fun a i s ->
    match i with
    | F32ConvertSI64 dst src | F32ConvertUI64 dst src ->
      upto_one_mem_ref (FloatOp dst) (IntOp src);
      let sb1 = sandbox_operandf Dst a dst 4 s in
      let sb2 = sandbox_operandi Src a src 8 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | F32ConvertSI64 dst src -> assert_spinoff (s'.ok == AllOk)
        | F32ConvertUI64 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
let _compile_ins_Conversion_f64_i64 : _compile_ins_t_Conversion (fun i -> F64ConvertSI64? i || F64ConvertUI64? i || ReinterpretInt64? i) =
  fun a i s ->
    match i with
    | F64ConvertSI64 dst src | F64ConvertUI64 dst src | ReinterpretInt64 dst src ->
      upto_one_mem_ref (FloatOp dst) (IntOp src);
      let sb1 = sandbox_operandf Dst a dst 8 s in
      let sb2 = sandbox_operandi Src a src 8 (eval_inss sb1 s) in
      let r = sb1 @ sb2 @ [i] in
      lemma_eval_inss_ins_append sb2 i (eval_inss sb1 s);
      lemma_eval_inss_append sb1 (sb2 @ [i]) s;
      let s' : erased _ = eval_inss r s in
      (
        match i with
        | F64ConvertSI64 dst src -> assert_spinoff (s'.ok == AllOk)
        | F64ConvertUI64 dst src -> assert_spinoff (s'.ok == AllOk)
        | ReinterpretInt64 dst src -> assert_spinoff (s'.ok == AllOk)
      ); (* OBSERVE: Makes the proof obligation much more tractable *)
      lemma_eval_ins_maintains_validity a i (eval_inss sb2 (eval_inss sb1 s));
      r
#pop-options

let _compile_ins_Conversion : _compile_ins_t I.Conversion =
  fun a i s ->
    allow_inversion ins_t;
    match i with
    | I32TruncSF32 _ _ | I32TruncUF32 _ _ | ReinterpretFloat32 _ _ -> _compile_ins_Conversion_i32_f32 a i s
    | I32TruncSF64 _ _ | I32TruncUF64 _ _ -> _compile_ins_Conversion_i32_f64 a i s
    | I64TruncSF32 _ _ | I64TruncUF32 _ _ -> _compile_ins_Conversion_i64_f32 a i s
    | I64TruncSF64 _ _ | I64TruncUF64 _ _ | ReinterpretFloat64 _ _ -> _compile_ins_Conversion_i64_f64 a i s
    | F32DemoteF64 _ _ | F64PromoteF32 _ _ -> _compile_ins_Conversion_f_f a i s
    | F32ConvertSI32 _ _ | F32ConvertUI32 _ _ | ReinterpretInt32 _ _ -> _compile_ins_Conversion_f32_i32 a i s
    | F64ConvertSI32 _ _ | F64ConvertUI32 _ _ -> _compile_ins_Conversion_f64_i32 a i s
    | F32ConvertSI64 _ _ | F32ConvertUI64 _ _ -> _compile_ins_Conversion_f32_i64 a i s
    | F64ConvertSI64 _ _ | F64ConvertUI64 _ _ | ReinterpretInt64 _ _ -> _compile_ins_Conversion_f64_i64 a i s

(** Compile a single instruction *)
let compile_ins (a:aux_info) (i:ins_t) (s:erased state) :
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (valid_sb_state a (eval_inss r s)) /\
         (Cons? r))) =
  wrap_err_with
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (valid_sb_state a (eval_inss r s)) /\
         (Cons? r)))
    (fun e -> "Error in [compile_ins] at instruction " ^ string_of_inst i ^ ": " ^ e)
    (fun () ->
       let open I in
       match tag_of_ins i with
       | StackOp -> _compile_ins_StackOp a i s
       | Mov -> _compile_ins_Mov a i s
       | I32_Binop -> _compile_ins_I32_Binop a i s
       | I64_Binop -> _compile_ins_I64_Binop a i s
       | Misc -> _compile_ins_Misc a i s
       | Movzx -> _compile_ins_Movzx a i s
       | Movsx -> _compile_ins_Movsx a i s
       | I32_Unop -> _compile_ins_I32_Unop a i s
       | I64_Unop -> _compile_ins_I64_Unop a i s
       | FMov -> _compile_ins_FMov a i s
       | F32_Unop -> _compile_ins_F32_Unop a i s
       | F64_Unop -> _compile_ins_F64_Unop a i s
       | F32_Binop -> _compile_ins_F32_Binop a i s
       | F64_Binop -> _compile_ins_F64_Binop a i s
       | Conversion -> _compile_ins_Conversion a i s
    )

(** Compile a list of instructions *)
let rec compile_inss (a:aux_info) (is:list ins_t) (s:erased state) :
  Err (A.t ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (valid_sb_state a (eval_inss (A.to_list r) s)))) =
  allow_inversion (list ins_t);
  match is with
  | [] ->
    assert_norm (eval_inss [] s == reveal s); (* OBSERVE *)
    A.empty
  | x :: xs ->
    let r1 = compile_ins a x s in
    let r2 = compile_inss a xs (eval_inss r1 s) in
    let r = A.of_list r1 `A.append` r2 in
    // assert (valid_sb_state a (eval_inss r1 s));
    // assert (valid_sb_state a (eval_inss r2 (eval_inss r1 s)));
    lemma_eval_inss_append r1 (A.to_list r2) s;
    r

#push-options "--z3rlimit 100"
(** Sandbox a comparison *)
let sandbox_cmp (a:aux_info) (c:ocmp) (t f:loc) (s:erased state) :
  Err (list ins_t)
    (requires (
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun r ->
         (valid_ocmp c (eval_inss r s) == AllOk) /\
         (valid_sb_state a (eval_inss r s)))) =
  allow_inversion ocmp;
  match c with
  | OEq32 o1 o2
  | ONe32 o1 o2
  | OLe32 o1 o2
  | OGe32 o1 o2
  | OLt32 o1 o2
  | OGt32 o1 o2
  | OLeS32 o1 o2
  | OGeS32 o1 o2
  | OLtS32 o1 o2
  | OGtS32 o1 o2
    ->
    upto_one_mem_ref (IntOp o1) (IntOp o2);
    let sb1 = sandbox_operandi Src a o1 4 s in
    let sb2 = sandbox_operandi Src a o2 4 (eval_inss sb1 s) in
    let r = sb1 @ sb2 in
    lemma_eval_inss_append sb1 sb2 s;
    r
  | OEq64 o1 o2
  | ONe64 o1 o2
  | OLe64 o1 o2
  | OGe64 o1 o2
  | OLt64 o1 o2
  | OGt64 o1 o2
  | OLeS64 o1 o2
  | OGeS64 o1 o2
  | OLtS64 o1 o2
  | OGtS64 o1 o2
    ->
    upto_one_mem_ref (IntOp o1) (IntOp o2);
    let sb1 = sandbox_operandi Src a o1 8 s in
    let sb2 = sandbox_operandi Src a o2 8 (eval_inss sb1 s) in
    let r = sb1 @ sb2 in
    lemma_eval_inss_append sb1 sb2 s;
    r
  | OFEq32 o1 o2
  | OFNe32 o1 o2
  | OFLt32 o1 o2
  | OFGt32 o1 o2
  | OFLe32 o1 o2
  | OFGe32 o1 o2
    ->
    upto_one_mem_ref (FloatOp o1) (FloatOp o2);
    let sb1 = sandbox_operandf Src a o1 4 s in
    let sb2 = sandbox_operandf Src a o2 4 (eval_inss sb1 s) in
    let r = sb1 @ sb2 in
    lemma_eval_inss_append sb1 sb2 s;
    r
  | OFEq64 o1 o2
  | OFNe64 o1 o2
  | OFLt64 o1 o2
  | OFGt64 o1 o2
  | OFLe64 o1 o2
  | OFGe64 o1 o2
    ->
    upto_one_mem_ref (FloatOp o1) (FloatOp o2);
    let sb1 = sandbox_operandf Src a o1 8 s in
    let sb2 = sandbox_operandf Src a o2 8 (eval_inss sb1 s) in
    let r = sb1 @ sb2 in
    lemma_eval_inss_append sb1 sb2 s;
    r
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec lemma_for_all_index #t (f:t -> bool) (l:list t) (i:nat) :
  Lemma
    (requires (for_all f l /\ i < length l))
    (ensures (f (index l i))) =
  if i = 0 then () else (
    lemma_for_all_index f (tl l) (i - 1)
  )
#pop-options

let sane_call_tables' (a:aux_info) : GTot Type0 =
  let tbl = a.m_aux.call_table.call_init in
  (forall (i:nat). {:pattern (index tbl i)} i < length tbl ==> (
      let n = index tbl i in
      Some? n ==> Some? (find_real_fn_entry (Some?.v n) a.orig_code)))

let sane_call_tables'_modified (a:aux_info) : GTot Type0 =
  let tbl = a.m_aux.call_table.call_init in
  (forall (i:nat). {:pattern (index tbl i)} i < length tbl ==> (
      let n = index tbl i in
      Some? n ==> Some? (find_real_fn_entry (Some?.v n) a.modified_code)))

let same_fn_entry_point_code (a b:precode) : Type0 =
  match a, b with
  | FnEntry _ _, FnEntry _ _ -> a = b
  | FnEntry _ _, _ -> False
  | _, FnEntry _ _ -> False
  | _, _ -> True

let rec same_fn_entry_points (a b:list precode) : Type0 =
  allow_inversion (list precode);
  match a, b with
  | [], [] -> True
  | FnEntry _ _ :: _, [] -> False
  | _ :: t1, [] -> same_fn_entry_points t1 []
  | [], FnEntry _ _ :: _ -> False
  | [], _ :: t2 -> same_fn_entry_points [] t2
  | (h1 :: t1), (h2 :: t2) ->
    same_fn_entry_point_code h1 h2 /\ same_fn_entry_points t1 t2

#push-options "--fuel 1 --ifuel 0"
let rec lemma_same_fn_entry_points (a b:list precode) (fn_name:nat) :
  Lemma
    (requires (same_fn_entry_points a b))
    (ensures (find_real_fn_entry fn_name a == find_real_fn_entry fn_name b)) =
  allow_inversion (list precode);
  match a with
  | [] -> (
      match b with
      | [] -> ()
      | h2 :: t2 ->
        // assert_norm (~(FnEntry? h2));
        lemma_same_fn_entry_points [] t2 fn_name
    )
  | h1 :: t1 -> (
      match b with
      | [] -> (
          // assert_norm (~(FnEntry? h1));
          lemma_same_fn_entry_points t1 [] fn_name
        )
      | h2 :: t2 -> (
          match h1, h2 with
          | FnEntry f1 _, FnEntry f2 _ ->
            // assert_norm (f1 = f2);
            if f1 = fn_name then () else (
              lemma_same_fn_entry_points t1 t2 fn_name
            )
          | _, _ ->
            lemma_same_fn_entry_points t1 t2 fn_name
        )
    )
#pop-options

let sane_call_tables (a:aux_info) : GTot Type0 =
  sane_call_tables' a /\ same_fn_entry_points a.orig_code a.modified_code

let auto_lemma_sane_call_tables (a:aux_info) (n:nat) :
  Lemma
    (requires (sane_call_tables a))
    (ensures (find_real_fn_entry n a.modified_code == find_real_fn_entry n a.orig_code))
    [SMTPat (find_real_fn_entry n a.modified_code)] =
  lemma_same_fn_entry_points a.orig_code a.modified_code n

let sanity_check_call_tables (a:aux_info) :
  Err unit
    (requires True)
    (ensures (fun () -> sane_call_tables' a)) =
  let tbl = a.m_aux.call_table.call_init in
  let f (n:option nat) = match n with
    | None -> true
    | Some x -> Some? (find_real_fn_entry x a.orig_code) in
  if for_all f tbl then (
    let aux (i:nat) : Lemma
        (requires (i < length tbl))
        (ensures (let n = index tbl i in
                  Some? n ==> Some? (find_real_fn_entry (Some?.v n) a.orig_code)))
        [SMTPat (index tbl i)] =
      lemma_for_all_index f tbl i
    in
    ()
  ) else (
    fail_with "[sanity_check_call_tables] AST Failure"
  )

(** Sandbox a single Call instruction *)
let sandbox_call (a:aux_info) (p:precode) (s:erased state) :
  Err (list ins_t)
    (requires (
        (sane_call_tables a) /\
        (valid_sb_state a s) /\
        (valid_sb_size a) /\
        (Call? p)))
    (ensures (fun r ->
         Call? p /\ (
           let Call target next = p in
           (
             (snd (find_call_target target (eval_inss r s) a.orig_code) == AllOk)
             \/
             (is_explicitly_safely_killed_target target (eval_inss r s))
             \/
             (is_imported_function_target (Call?.target p) s /\ r == [])
           ) /\
           (valid_sb_state a (eval_inss r s))))) =
  allow_inversion target_t;
  let Call target onreturn = p in
  match target with
  | CallDirect n -> (
      match find_real_fn_entry n a.orig_code with
      | Some next ->
        let r = [] in
        assert_norm (eval_inss r s == reveal s); (* OBSERVE *)
        r
      | None ->
        if is_imported_function a.m_aux n then (
          let r = [] in
          assert_norm (eval_inss r s == reveal s); (* OBSERVE *)
          r
        ) else (
          fail_with ("AST Failure for (CallDirect " ^ string_of_int n ^ ")")
        )
    )
  | CallIndirect reg -> (
      let tbl = a.m_aux.call_table.call_init in
      if length tbl > 0 && length tbl - 1 < pow2_64 then (
        let rng = {lower = 0; upper = length tbl - 1} in
        let r = restrict_regi reg rng in
        let s1 : erased state = eval_inss r s in
        lemma_restrict_regi reg rng a s;
        r
      ) else (
        fail_with "Impossible call table size"
      )
    )

#push-options "--fuel 1"
let lemma_for_all_cons #t (f:t -> bool) (l:list t) :
  Lemma
    (requires (Cons? l ==> (f (hd l) /\ for_all f (tl l))))
    (ensures (for_all f l)) = ()
#pop-options

#push-options "--fuel 1"
let lemma_for_all_uncons #t (f:t -> bool) (l:list t) :
  Lemma
    (requires (for_all f l))
    (ensures (Cons? l ==> (f (hd l) /\ for_all f (tl l)))) = ()
#pop-options

let ensure_call_maintains_callstack (a:aux_info) (p:precode) (cfi_loc:loc) (s:erased state) :
  Err unit
    (requires (
        (sane_call_tables a) /\
        (Call? p) /\
        (s.aux = a.m_aux) /\
        (safe_callstack s cfi_loc)))
    (ensures (fun () ->
         let s1, ip = eval_step' a.modified_code p s in
         safe_callstack s1 cfi_loc)) =
  allow_inversion precode;
  allow_inversion target_t;
  let Call target next = p in
  if next < cfi_loc then (
    match target with
    | CallDirect n -> (
        if is_imported_function a.m_aux n then () else
        match find_real_fn_entry n a.orig_code with
        | None -> fail_with ("[ensure_call_maintains_callstack] Call target doesn't have valid function[" ^ string_of_int n ^ "] " ^
                             string_of_precode p)
        | Some next -> (
            if next < cfi_loc then (
              let s1 : erased state = fst (eval_step' a.modified_code p s) in
              lemma_for_all_cons (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < cfi_loc) s1.callstack
            ) else (
              fail_with ("[ensure_call_maintains_callstack] Function trying to jump out of bounds in " ^ string_of_precode p)
            )
          )
      )
    | CallIndirect r -> (
        let tbl = a.m_aux.call_table.call_init in
        let f (fn_name:option nat) =
          match fn_name with
          | None -> true
          | Some fn_name ->
            if is_imported_function a.m_aux fn_name then true else
            match find_real_fn_entry fn_name a.orig_code with
            | None -> false
            | Some next -> next < cfi_loc in
        if for_all f tbl then (
          let n : erased nat64 = s.reg_i r in
          if n < length tbl then (
            lemma_for_all_index f tbl n
          ) else ();
          let s1 : erased state = fst (eval_step' a.modified_code p s) in
          if s1.callstack = s.callstack then () else
            lemma_for_all_cons (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < cfi_loc) s1.callstack
        ) else (
          fail_with ("[ensure_call_maintains_callstack] Invalid table referenced in " ^ string_of_precode p)
        )
      )
  ) else (
    fail_with ("[ensure_call_maintains_callstack] Returning back into a bad location for " ^ string_of_precode p)
  )

#push-options "--fuel 0 --ifuel 1"
(** Compile a single precode instruction *)
let compile_precode (a:aux_info) (p:precode) (cfi_loc:loc) (s:erased state) :
  Err (A.t ins_t & precode)
    (requires (
        (sane_call_tables a) /\
        (safe_callstack s cfi_loc) /\
        (valid_sb_state a s) /\
        (valid_sb_size a)))
    (ensures (fun (r, p') ->
         let s1 = eval_inss (A.to_list r) s in
         let s2, ip = eval_step' a.modified_code p' s1 in
         valid_sb_state a s1 /\
         valid_sb_state a s2 /\
         (safe_callstack s2 cfi_loc) /\
         (FnEntry? p \/ FnEntry? p' ==> p == p') /\
         (FnEntry? p ==> A.to_list r == []))) =
  allow_inversion precode;
  assert_norm (eval_inss [] s == reveal s); (* OBSERVE *)
  match p with
  | HighCall _ _ _ _ -> fail_with "Disallowed HighCall instruction in sandboxing phase"
  | HighRet _ _ -> fail_with "Disallowed HighRet instruction in sandboxing phase"
  | FnEntry name _ ->
    if name < 0 then
      fail_with ("Got negative function name: " ^ string_of_int name)
    else if name >= length a.m_aux.fns then (* XXX: Should this be fns or calltable? *)
      fail_with ("Invalid function name: " ^ string_of_int name)
    else (A.empty, p)
  | FnExit name ->
    fail_with ("Not allowed: " ^ string_of_precode p)
  | Cmp c t f ->
    let sbx = sandbox_cmp a c t f s in
    lemma_eval_inss_maintains_callstack sbx s;
    (A.of_list sbx, p)
  | Switch case_table case ->
    if case_table < 0 || case_table >= length a.m_aux.br_tables then
      fail_with ("Invalid case table: " ^ string_of_int case_table)
    else if not (valid_reg_int case) then
      fail_with ("Invalid register " ^ string_of_int case)
    else (
      let br_tbl = index a.m_aux.br_tables case_table in
      let tbl = br_tbl.br_targets in
      let rng = ({lower = 0;
                  upper = length tbl - 1}) in
      if length tbl > 0 && rng.upper < pow2_64 then (
        lemma_restrict_regi case rng a s;
        let sbx = restrict_regi case rng in
        lemma_eval_inss_maintains_callstack sbx s;
        (A.of_list sbx, p)
      ) else (
        fail_with ("Impossibly sized case table " ^ string_of_int case_table)
      )
    )
  | Call _ _ ->
    let sbx = sandbox_call a p s in
    lemma_eval_inss_maintains_callstack sbx s;
    let _ = ensure_call_maintains_callstack a p cfi_loc (eval_inss sbx s) in
    (A.of_list sbx, p)
  | Nop _ ->
    (A.empty, p)
  | Ret _ ->
    lemma_for_all_uncons (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < cfi_loc) s.callstack;
    assert (safe_callstack (fst (eval_step' a.modified_code p s)) cfi_loc);
    assume ((Cons? s.callstack) /\ (
        let next, prev_init_rsp, prev_rsp, rip_on_stack = hd s.callstack in
        (s.stack.init_rsp = prev_init_rsp) /\
        (s.stack_pointer + 8 = prev_rsp) /\
        (eval_stack64 s.stack_pointer s.stack = rip_on_stack))); (* Property of register allocator. Cannot be affected adversarially. *)
    (A.empty, p)
  | Ins i next ->
    let compiled = compile_ins a i s in
    lemma_eval_inss_maintains_callstack compiled s;
    (A.empty, InsList compiled next)
  | InsList is next ->
    let compiled = compile_inss a is s in
    lemma_eval_inss_maintains_callstack (A.to_list compiled) s;
    (A.empty, InsList (A.to_list compiled) next)
#pop-options

#push-options "--fuel 1 --ifuel 0"
let lemma_length_tl #t (hd:t) (tl:list t) :
  Lemma
    (ensures (length (hd :: tl) = 1 + length tl)) = ()
#pop-options

#push-options "--fuel 1 --ifuel 0"
let rec lemma_index_append_length #t (l1 l2:list t) :
  Lemma
    (requires (Cons? l2))
    (ensures (
        length l1 < length (l1 @ l2) /\
        index (l1 @ l2) (length l1) == hd l2)) =
  allow_inversion (list t);
  LP.append_length l1 l2;
  match l1 with
  | [] -> ()
  | hd :: tl ->
    lemma_index_append_length tl l2
#pop-options

(** A pre-processing step that guarantees that no execution escapes
    the confines of the initial CFG. This step is used in the main
    processing step to show basic CFI promises which ensure that none
    of the SFI guarantees can be subverted.

    The way this works is that the [pre_process_cfg] defines a core
    set of expected control flow guarantees (at the moment, that all
    executions stay within the confines of the initial CFG, even under
    failure). The main [process_precode] works by adding code in such
    a way that it either stays within the confines of the existing
    CFG, or only temporarily exits the CFG but then in forced to
    re-enter the CFG. With these two properties combined, we can
    obtain the fact that the SFI guarantees aren't subverted. *)
#restart-solver
#push-options "--z3rlimit 10 --fuel 1"
let rec pre_process_cfg (a:aux_info) (c_finished:A.t precode) (c_processing:cfg) (l:nat) (s:erased state) :
  Err unit
    (requires (
        let c = A.to_list c_finished @ c_processing in
        sane_call_tables a /\
        reveal a.modified_code == c /\
        valid_sb_state a s /\
        (l == length c) /\
        (s.ip < length c) /\
        (forall i. i < A.length c_finished ==> (
             let s1, ip1 = eval_step' c (index c i) s in
             (ip1 < l) /\
             (safe_callstack s1 l))) /\
        (safe_callstack s l)))
    (ensures (fun () ->
        let c = A.to_list c_finished @ c_processing in
        (forall i. i < l ==> (
             let s1, ip1 = eval_step' c (index c i) s in
             (ip1 < l) /\
             (safe_callstack s1 l)))))
    (decreases %[c_processing]) =
  allow_inversion cfg;
  allow_inversion precode;
  match c_processing with
  | [] -> ()
  | hd :: tl -> (
      lemma_length_tl hd tl;
      LP.lemma_snoc_length ((A.to_list c_finished), hd);
      LP.append_l_cons hd tl (A.to_list c_finished);
      // assert (snoc (c_finished, hd) @ tl == c_finished @ c_processing);
      lemma_index_append_length (A.to_list c_finished) c_processing;
      // assert (index (c_finished @ c_processing) (length c_finished) == hd);
      match hd with
      | FnEntry _ next
      | Nop next ->
        if next < l then (
          pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
        ) else (
          fail_with ("[pre_process_cfg] Trying to jump out of bounds in " ^ string_of_precode hd)
        )
      | Ins i next ->
        lemma_eval_ins_maintains_callstack i s;
        if next < l then (
          pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
        ) else (
          fail_with ("[pre_process_cfg] Trying to jump out of bounds in " ^ string_of_precode hd)
        )
      | InsList is next ->
        lemma_eval_inss_maintains_callstack is s;
        if next < l then (
          pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
        ) else (
          fail_with ("[pre_process_cfg] Trying to jump out of bounds in " ^ string_of_precode hd)
        )
      | Cmp _ nextTrue nextFalse ->
        if nextTrue < l && nextFalse < l then (
          pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
        ) else (
          fail_with ("[pre_process_cfg] Trying to jump out of bounds in " ^ string_of_precode hd)
        )
      | Switch case_table case ->
        if case_table < length a.m_aux.br_tables then (
          let tbl = index a.m_aux.br_tables case_table in
          let f (next:loc) = next < l in
          if for_all f tbl.br_targets then (
            let target: erased nat64 = eval_reg64 case s in
            if target < length tbl.br_targets then (
              lemma_for_all_index f tbl.br_targets target
            ) else ();
            pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
          ) else (
            fail_with ("[pre_process_cfg] Invalid table referenced in " ^
                       string_of_precode hd ^ "; table " ^ tbl.br_name)
          )
        ) else (
          fail_with ("[pre_process_cfg] Trying to access invalid table in " ^ string_of_precode hd)
        )
      | Call target next ->
        allow_inversion target_t;
        if next < l then (
          match target with
          | CallDirect n -> (
              if is_imported_function a.m_aux n then
                pre_process_cfg a (A.snoc (c_finished, hd)) tl l s else
              match find_real_fn_entry n a.orig_code with
              | None -> fail_with ("[pre_process_cfg] Direct call target doesn't have valid function[" ^
                                   string_of_int n ^ "]: " ^ string_of_precode hd)
              | Some next -> (
                  if next < l then (
                    // assert (
                    //   let c = c_finished @ c_processing in
                    //   let s1, ip1 = eval_step' c hd s in
                    //   let h :: t = s1.callstack in
                    //   let (next, _, _) = h in
                    //   next < l
                    //   );
                    let s1 : erased state = fst (eval_step' a.modified_code hd s) in
                    assert (List.Tot.tl s1.callstack == s.callstack);
                    assert (squash (safe_callstack s l)); (* OBSERVE *)
                    assert (for_all (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s.callstack) by (
                      revert ();
                      norm [delta_only [`%safe_callstack]];
                      exact (`(fun x -> x))
                    ); (* No idea why F* does not automatically unfold this for us *)
                    lemma_for_all_cons (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s1.callstack;
                    // assert (
                    //   let c = c_finished @ c_processing in
                    //   let s1, ip1 = eval_step' c hd s in
                    //   safe_callstack s1 l);
                    pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
                  ) else (
                    fail_with ("[pre_process_cfg] Function trying to jump out of bounds in " ^ string_of_precode hd)
                  )
                )
            )
          | CallIndirect r -> (
              let tbl = a.m_aux.call_table.call_init in
              let f (fn_name:option nat) =
                match fn_name with
                | None -> true
                | Some fn_name ->
                  if is_imported_function a.m_aux fn_name then true else
                  match find_real_fn_entry fn_name a.orig_code with
                  | None -> false
                  | Some next -> next < l in
              if for_all f tbl then (
                let n : erased nat64 = s.reg_i r in
                if n < length tbl then (
                  lemma_for_all_index f tbl n
                ) else ();
                let c = a.orig_code in
                let s1 : erased state = fst (eval_step' c hd s) in
                // assert (
                //   s1.callstack == s.callstack \/
                //   (Cons? s1.callstack /\ (
                //      let (next, _, _) :: t = s1.callstack in
                //      next < l /\
                //      t == s.callstack))
                // );
                if s1.callstack = s.callstack then () else (
                  assert (List.Tot.tl s1.callstack == s.callstack);
                  assert (squash (safe_callstack s l)); (* OBSERVE *)
                  assert (for_all (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s.callstack) by (
                    revert ();
                    norm [delta_only [`%safe_callstack]];
                    exact (`(fun x -> x))
                  ); (* No idea why F* does not automatically unfold this for us *)
                  lemma_for_all_cons (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s1.callstack
                );
                pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
              ) else (
                fail_with ("[pre_process_cfg] Invalid table referenced in " ^ string_of_precode hd)
              )
            )
        ) else (
          fail_with ("[pre_process_cfg] Returning back into a bad location for " ^ string_of_precode hd)
        )
      | Ret _ -> (
          // assert (
          //   let c = c_finished @ c_processing in
          //   let s1, ip1 = eval_step' c hd s in
          //   s1.callstack = s.callstack \/ (
          //       let (next, _, _) :: prev_callstack = s.callstack in
          //       s1.callstack = prev_callstack /\ next = ip1
          //     )
          // );
          assert (squash (safe_callstack s l)); (* OBSERVE *)
          assert (for_all (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s.callstack) by (
            revert ();
            norm [delta_only [`%safe_callstack]];
            exact (`(fun x -> x))
          ); (* No idea why F* does not automatically unfold this for us *)
          lemma_for_all_uncons (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l) s.callstack;
          // assert (
          //   let c = c_finished @ c_processing in
          //   let s1, ip1 = eval_step' c hd s in
          //   (ip1 < l) /\
          //   (safe_callstack s1 l)
          // );
          pre_process_cfg a (A.snoc (c_finished, hd)) tl l s
        )
      | FnExit _
      | HighCall _ _ _ _
      | HighRet _ _ -> fail_with ("[pre_process_cfg] Found disallowed: " ^ string_of_precode hd)
    )
#pop-options

#push-options "--fuel 2 --ifuel 0"
let rec lemma_index_snoc #t (a:list t) (b:t) (i:nat{i < length a}) :
  Lemma
    (i < length (snoc (a, b)) /\ index a i == index (snoc (a, b)) i) =
  allow_inversion (list t);
  match a with
  | [_] -> ()
  | _ -> if i = 0 then () else lemma_index_snoc (tl a) b (i - 1)

let rec lemma_unzip_snoc #t1 #t2 (a:list (t1 & t2)) (b1:t1) (b2:t2) :
  Lemma
    (ensures (
        (fst (unzip (snoc (a, (b1, b2)))) == snoc (fst (unzip a), b1)) /\
        (snd (unzip (snoc (a, (b1, b2)))) == snoc (snd (unzip a), b2)))) =
  allow_inversion (list (t1 & t2));
  match a with
  | [] -> ()
  | _ -> lemma_unzip_snoc (tl a) b1 b2

let rec lemma_unzip_length #t1 #t2 (a:list (t1 & t2)) :
  Lemma
    (ensures (
        length (fst (unzip a)) == length a /\
        length (snd (unzip a)) == length a)) =
  allow_inversion (list (t1 & t2));
  match a with
  | [] -> ()
  | _ -> lemma_unzip_length (tl a)
#pop-options

let lemma_move_left #t (left:list t) (hd:t) (tl:list t) (right:list t) :
  Lemma
    (ensures (
        (snoc (left, hd) @ tl @ right) ==
        (left @ (hd :: tl) @ right))) =
  LP.append_assoc (snoc (left, hd)) tl right;
  LP.append_l_cons hd tl left;
  LP.append_assoc left (hd :: tl) right

#push-options "--fuel 1"
let rec lemma_same_fn_entry_points_reflexive (a:list precode) :
  Lemma
    (ensures (same_fn_entry_points a a)) =
  allow_inversion (list precode);
  match a with
  | [] -> ()
  | h :: t -> lemma_same_fn_entry_points_reflexive t
#pop-options

#push-options "--fuel 1"
let rec lemma_same_fn_entry_points_transitive (a b c:list precode) :
  Lemma
    (requires (same_fn_entry_points a b /\ same_fn_entry_points b c))
    (ensures (same_fn_entry_points a c)) =
  allow_inversion (list precode);
  let possible_tl (x:list precode) = match x with
    | [] -> []
    | _ :: t -> t
  in
  match a, b, c with
  | [], [], [] -> ()
  | _, _, _ -> lemma_same_fn_entry_points_transitive (possible_tl a) (possible_tl b) (possible_tl c)
#pop-options

#push-options "--fuel 1"
let rec lemma_same_fn_entry_points_append_left (left a b:list precode) :
  Lemma
    (requires (same_fn_entry_points a b))
    (ensures (same_fn_entry_points (left @ a) (left @ b))) =
  allow_inversion (list precode);
  match left with
  | [] -> ()
  | h :: t -> lemma_same_fn_entry_points_append_left t a b
#pop-options

#push-options "--fuel 1"
let rec lemma_same_fn_entry_points_append_left2 (left1 left2 right1 right2:list precode) :
  Lemma
    (requires (length left1 == length left2 /\ same_fn_entry_points left1 left2 /\ same_fn_entry_points right1 right2))
    (ensures (same_fn_entry_points (left1 @ right1) (left2 @ right2))) =
  allow_inversion (list precode);
  let possible_tl (x:list precode) = match x with
    | [] -> []
    | _ :: t -> t
  in
  match left1, left2 with
  | [], [] -> ()
  | _, _ ->
    lemma_same_fn_entry_points_append_left2 (possible_tl left1) (possible_tl left2) right1 right2
#pop-options

#push-options "--fuel 1"
let lemma_same_fn_entry_points_maintained1 (orig left:list precode) (hd1 hd2:precode) (tl right:list precode) :
  Lemma
    (requires (
        (same_fn_entry_points orig (left @ (hd1 :: tl) @ right)) /\
        (FnEntry? hd1 \/ FnEntry? hd2 ==> hd1 == hd2)))
    (ensures (
        (same_fn_entry_points orig (snoc (left, hd2) @ tl @ right)))) =
  lemma_same_fn_entry_points_reflexive right;
  lemma_same_fn_entry_points_append_left tl right right;
  lemma_same_fn_entry_points_append_left left ((hd1 :: tl) @ right) ((hd2 :: tl) @ right);
  lemma_same_fn_entry_points_transitive orig (left @ (hd1 :: tl) @ right) (left @ (hd2 :: tl) @ right);
  lemma_move_left left hd2 tl right
#pop-options

#push-options "--fuel 2"
let lemma_same_fn_entry_points_maintained2 (orig left:list precode) (hd1 hd2:precode) (tl right:list precode) (addn:precode) :
  Lemma
    (requires (
        (same_fn_entry_points orig (left @ (hd1 :: tl) @ right)) /\
        (same_fn_entry_point_code hd1 hd2) /\
        (~(FnEntry? addn))))
    (ensures (
        (same_fn_entry_points orig (snoc (left, hd2) @ tl @ snoc (right, addn))))) =
  lemma_same_fn_entry_points_append_left right [] [addn];
  lemma_same_fn_entry_points_append_left tl right (snoc (right, addn));
  lemma_same_fn_entry_points_append_left left (hd1 :: tl @ right) (hd2 :: tl @ snoc (right, addn));
  lemma_same_fn_entry_points_transitive orig (left @ (hd1 :: tl) @ right) (left @ (hd2 :: tl) @ snoc (right, addn));
  lemma_move_left left hd2 tl (snoc (right, addn))
#pop-options

(** In essence, a non-interference property on the evaluation of the
    code. This property explicitly says that the "middle" part of the
    code does not interfere with the evaluation whatsoever, as long as
    its length remains the same. *)
let eval_steps_irrelevant_mid (n:nat) (left mid right: list precode) (s:state) : Type0 =
  (forall (mid':list precode{length mid == length mid' /\ same_fn_entry_points mid mid'}).
     {:pattern (eval_steps n (left @ mid' @ right) s)}
     eval_steps n (left @ mid' @ right) s == eval_steps n (left @ mid @ right) s)

#push-options "--fuel 1"
let lemma_eval_steps_irrelevant_mid_move_left' (n:nat) (left:list precode) (hd1 hd2:precode) (mid right: list precode) (s:state) :
  Lemma
    (requires (
        (same_fn_entry_point_code hd1 hd2) /\
        (eval_steps_irrelevant_mid n left (hd1 :: mid) right s)))
    (ensures (
        eval_steps n (left @ (hd1 :: mid) @ right) s ==
        eval_steps n (left @ (hd2 :: mid) @ right) s)) =
  lemma_same_fn_entry_points_reflexive mid
#pop-options

(** When you change a code from irrelevance to relevance, the
    non-interference property still holds. *)
#push-options "--fuel 1"
let lemma_eval_steps_irrelevant_mid_move_left
    (n:nat) (left:list precode) (hd1 hd2:precode) (mid right:list precode) (s:state) :
  Lemma
    (requires (
        (same_fn_entry_point_code hd1 hd2) /\
        (eval_steps_irrelevant_mid n left (hd1 :: mid) right s)))
    (ensures (eval_steps_irrelevant_mid n (snoc (left, hd2)) mid right s)) =
  lemma_same_fn_entry_points_reflexive mid;
  assert (same_fn_entry_points (hd1 :: mid) (hd2 :: mid));
  let aux mid' : Lemma
    (requires (
       (eval_steps_irrelevant_mid n left (hd1 :: mid) right s) /\
       (length mid' == length mid) /\
       (same_fn_entry_points mid mid')))
    (ensures (eval_steps n (snoc (left, hd2) @ mid @ right) s ==
              eval_steps n (snoc (left, hd2) @ mid' @ right) s))
    [SMTPat (eval_steps n (snoc (left, hd2) @ mid' @ right) s)] =
    lemma_same_fn_entry_points_reflexive mid;
    assert (eval_steps n (left @ (hd1 :: mid) @ right) s ==
            eval_steps n (left @ (hd2 :: mid) @ right) s);
    assert (eval_steps n (left @ (hd1 :: mid') @ right) s ==
            eval_steps n (left @ (hd2 :: mid') @ right) s);
    lemma_move_left left hd2 mid right;
    assert (snoc (left, hd2) @ mid @ right == left @ (hd2 :: mid) @ right);
    assert (eval_steps n (snoc (left, hd2) @ mid @ right) s ==
            eval_steps n (left @ (hd1 :: mid) @ right) s);
    assert (eval_steps n (snoc (left, hd2) @ mid @ right) s ==
            eval_steps n (left @ (hd1 :: mid') @ right) s);
    assert (eval_steps n (snoc (left, hd2) @ mid @ right) s ==
            eval_steps n (left @ (hd2 :: mid') @ right) s);
    lemma_move_left left hd2 mid' right;
    assert (snoc (left, hd2) @ mid' @ right == left @ (hd2 :: mid') @ right);
    assert (eval_steps n (snoc (left, hd2) @ mid @ right) s ==
            eval_steps n (snoc (left, hd2) @ mid' @ right) s)
  in
  ()
#pop-options

#push-options "--fuel 1"
let lemma_eval_step'_changed_mid (left mid mid' right:list precode) (p:precode) (s:state) :
  Lemma
    (requires (length mid == length mid' /\ same_fn_entry_points mid mid'))
    (ensures (eval_step' (left @ mid @ right) p s == eval_step' (left @ mid' @ right) p s)) =
  let c1 = left @ mid @ right in
  let c2 = left @ mid' @ right in
  allow_inversion precode;
  allow_inversion (list (loc * int * int * nat64));
  match p with
  | FnEntry _ _ -> ()
  | FnExit _ -> ()
  | Ins _ _ -> ()
  | InsList _ _ -> ()
  | Nop _ -> ()
  | Cmp _ _ _ -> ()
  | Switch _ _ -> ()
  | Call target next -> (
      (
        assert (length c1 = length c2);
        lemma_same_fn_entry_points_reflexive right;
        lemma_same_fn_entry_points_append_left2 mid mid' right right;
        lemma_same_fn_entry_points_append_left left (mid @ right) (mid' @ right);
        assert (same_fn_entry_points c1 c2);
        match find_call_name target s with
        | Some fn_name ->
          lemma_same_fn_entry_points c1 c2 fn_name
        | None -> ()
      )
    )
  | HighCall _ _ _ _ -> ()
  | Ret _ -> (
      match s.callstack with
      | [] -> ()
      | (next, _, _, _) :: _ ->
        assert (length c1 = length c2);
        lemma_same_fn_entry_points_reflexive right;
        lemma_same_fn_entry_points_append_left2 mid mid' right right;
        lemma_same_fn_entry_points_append_left left (mid @ right) (mid' @ right);
        assert (same_fn_entry_points c1 c2)
    )
  | HighRet _ _ -> ()
#pop-options

#push-options "--fuel 1"
let rec lemma_index_append1 #t (l1 l2:list t) (n:nat) :
  Lemma
    (requires (n < length l1))
    (ensures (
        (n < length (l1 @ l2)) /\
        (index (l1 @ l2) n == index l1 n))) =
  allow_inversion (list t);
  match n with
  | 0 -> ()
  | _ -> lemma_index_append1 (tl l1) l2 (n - 1)

let rec lemma_index_append2 #t (l1 l2:list t) (n:nat) :
  Lemma
    (requires (n >= length l1 /\ n < length l1 + length l2))
    (ensures (
        (n < length (l1 @ l2)) /\
        (index (l1 @ l2) n == index l2 (n - length l1)))) =
  allow_inversion (list t);
  match l1 with
  | [] -> ()
  | h :: t -> lemma_index_append2 t l2 (n - 1)
#pop-options

#push-options "--fuel 1"
let lemma_eval_step'_unchanged_replacement
    (c1 c2:list precode) (p:precode) (s:state) :
  Lemma
    (requires (same_fn_entry_points c1 c2))
    (ensures (eval_step' c1 p s == eval_step' c2 p s)) =
  allow_inversion precode;
  allow_inversion (list (loc * int * int * nat64));
  match p with
  | FnEntry _ _ -> ()
  | FnExit _ -> ()
  | Ins _ _ -> ()
  | InsList _ _ -> ()
  | Nop _ -> ()
  | Cmp _ _ _ -> ()
  | Switch _ _ -> ()
  | Call target next -> (
      (
        match find_call_name target s with
        | Some fn_name ->
          lemma_same_fn_entry_points c1 c2 fn_name
        | None -> ()
      )
    )
  | HighCall _ _ _ _ -> ()
  | Ret _ -> ()
  | HighRet _ _ -> ()
#pop-options

#push-options "--fuel 1"
let lemma_eval_step'_unchanged_add_right
    (c:list precode) (a:precode) (p:precode) (s:state) :
  Lemma
    (requires (~(FnEntry? a)))
    (ensures (eval_step' c p s == eval_step' (snoc (c, a)) p s)) =
  lemma_same_fn_entry_points_reflexive [];
  lemma_same_fn_entry_points_append_left c [] [a];
  lemma_eval_step'_unchanged_replacement c (snoc (c, a)) p s
#pop-options

#push-options "--fuel 1"
let rec lemma_eval_step'_unchanged_add_right_xtra
    (c xtra:list precode) (p:precode) (s:state) :
  Lemma
    (requires (same_fn_entry_points [] xtra))
    (ensures (eval_step' c p s == eval_step' (c @ xtra) p s))
    (decreases %[xtra]) =
  allow_inversion (list precode);
  match xtra with
  | [] -> ()
  | hd :: tl ->
    calc (==) {
      (eval_step' c p s); =={ lemma_eval_step'_unchanged_add_right c hd p s }
      (eval_step' (c @ [hd]) p s); =={ lemma_eval_step'_unchanged_add_right_xtra (c @ [hd]) tl p s }
      (eval_step' ((c @ [hd]) @ tl) p s); =={ LP.append_assoc c [hd] tl }
      (eval_step' (c @ [hd] @ tl) p s); =={ assert_norm ([hd] @ tl == hd :: tl) } (* OBSERVE *)
      (eval_step' (c @ xtra) p s);
    }
#pop-options

#push-options "--fuel 1"
let lemma_single_step_irrelevant_mid (i:nat) (left:list precode) (modf:precode) (tl right:list precode) (s:state) :
  Lemma
    (requires (
        (s.ok == AllOk) /\
        (s.ip == length left)))
    (ensures (
        eval_steps_irrelevant_mid 1 (snoc (left, modf)) tl right s)) =
  let aux mid : Lemma
    (requires (length tl == length mid /\ same_fn_entry_points tl mid))
    (ensures (eval_steps 1 (snoc (left, modf) @ mid @ right) s == eval_steps 1 (snoc (left, modf) @ tl @ right) s))
    [SMTPat (snoc (left, modf) @ mid @ right)] =
    if s.explicitly_safely_killed then (
      assert_norm (eval_steps 1 (snoc (left, modf) @ mid @ right) s == [s]);
      assert_norm (eval_steps 1 (snoc (left, modf) @ tl @ right) s == [s])
    ) else
    let c1 = snoc (left, modf) @ tl @ right in
    let c2 = snoc (left, modf) @ mid @ right in
    lemma_move_left left modf tl right;
    lemma_move_left left modf mid right;
    LP.append_length left (modf :: tl @ right);
    LP.append_length left (modf :: mid @ right);
    LP.lemma_unsnoc_snoc (snoc (left, modf));
    LP.lemma_unsnoc_is_last (snoc (left, modf));
    LP.lemma_snoc_length (left, modf);
    assert (index (snoc (left, modf)) s.ip == modf);
    lemma_index_append_length left (modf :: tl @ right);
    lemma_index_append_length left (modf :: mid @ right);
    assert (index c1 s.ip == modf);
    assert (index c2 s.ip == modf);
    let s1, ip1 = eval_step' c1 (index c1 s.ip) s in
    let s2, ip2 = eval_step' c2 (index c2 s.ip) s in
    assert_norm (eval_steps 1 c1 s == [{s1 with ip = ip1}]);
    assert_norm (eval_steps 1 c2 s == [{s2 with ip = ip2}]);
    lemma_eval_step'_changed_mid (snoc (left, modf)) tl mid right modf s;
    assert ({s1 with ip = ip1} == {s2 with ip = ip2});
    assert (eval_steps 1 c1 s == eval_steps 1 c2 s);
    assert (eval_steps 1 (snoc (left, modf) @ mid @ right) s == eval_steps 1 (snoc (left, modf) @ tl @ right) s)
  in
  ()
#pop-options

#push-options "--fuel 1"
let lemma_eval_step_unchanged_add_right_xtra
    (a b xtra:list precode) (s:state) :
  Lemma
    (requires (
        (length a = length b) /\
        (same_fn_entry_points a b) /\
        (same_fn_entry_points [] xtra) /\
        (eval_step a s == eval_step b s)))
    (ensures (
        (eval_step (a @ xtra) s == eval_step (b @ xtra) s))) =
  if s.ok = AllOk then (
    if s.explicitly_safely_killed then (
      assert_norm (eval_step (a @ xtra) s == eval_step (b @ xtra) s)
    ) else if s.ip < length a then (
      calc (==) {
        (eval_step' (a @ xtra) (get_code_at s.ip (a @ xtra)) s); == { lemma_index_append1 a xtra s.ip }
        (eval_step' (a @ xtra) (get_code_at s.ip a) s); =={ lemma_eval_step'_unchanged_add_right_xtra a xtra (get_code_at s.ip a) s }
        (eval_step' a (get_code_at s.ip a) s); =={}
        (eval_step' b (get_code_at s.ip b) s); == { lemma_eval_step'_unchanged_add_right_xtra b xtra (get_code_at s.ip b) s }
        (eval_step' (b @ xtra) (get_code_at s.ip b) s); == { lemma_index_append1 b xtra s.ip }
        (eval_step' (b @ xtra) (get_code_at s.ip (b @ xtra)) s);
      }
    ) else if s.ip < length a + length xtra then (
      let i = s.ip - length a in
      calc (==) {
        (eval_step' (a @ xtra) (get_code_at s.ip (a @ xtra)) s); == { lemma_index_append2 a xtra s.ip }
        (eval_step' (a @ xtra) (get_code_at i xtra) s); == { lemma_eval_step'_unchanged_add_right_xtra a xtra (get_code_at i xtra) s }
        (eval_step' a (get_code_at i xtra) s); =={ lemma_eval_step'_unchanged_replacement a b (get_code_at i xtra) s }
        (eval_step' b (get_code_at i xtra) s); == { lemma_eval_step'_unchanged_add_right_xtra b xtra (get_code_at i xtra) s }
        (eval_step' (b @ xtra) (get_code_at i xtra) s); == { lemma_index_append2 b xtra s.ip }
        (eval_step' (b @ xtra) (get_code_at s.ip (b @ xtra)) s);
      }
    )
  )
#pop-options

let lemma_eval_step_ok_unchanged_add_right_xtra
    (a xtra:list precode) (s:state) :
  Lemma
    (requires (
        (same_fn_entry_points [] xtra) /\
        ((eval_step a s).ok == AllOk)))
    (ensures (
        (eval_step (a @ xtra) s == eval_step a s))) =
  // assert (s.ok = AllOk);
  if s.explicitly_safely_killed then () else (
    // assert (s.ip < length a);
    lemma_index_append1 a xtra s.ip;
    // assert (index a s.ip == index (a @ xtra) s.ip);
    lemma_eval_step'_unchanged_add_right_xtra a xtra (index a s.ip) s
  )

#push-options "--fuel 1"
let rec lemma_eval_steps_last_ok_means_idx_ok
    (n:nat) (c:list precode) (s:state) (i:nat) :
  Lemma
    (requires (
        (i < n) /\
        ((last (eval_steps n c s)).ok == AllOk)))
    (ensures (
        ((index (eval_steps n c s) i).ok == AllOk))) =
  match n with
  | 1 -> assert_norm (eval_steps n c s == [eval_step c s]) (* OBSERVE *)
  | _ ->
    match i with
    | 0 -> lemma_eval_steps_last_ok_means_idx_ok (n-1) c (eval_step c s) i
    | _ -> lemma_eval_steps_last_ok_means_idx_ok (n-1) c (eval_step c s) (i-1)
#pop-options

#push-options "--fuel 2"
let rec lemma_eval_steps_ok_unchanged_add_right_xtra
    (n:nat) (a xtra:list precode) (s:state) :
  Lemma
    (requires (
        (n > 0) /\
        (same_fn_entry_points [] xtra) /\
        ((last (eval_steps n a s)).ok = AllOk)))
    (ensures (
        (eval_steps n (a @ xtra) s == eval_steps n a s))) =
  match n with
  | 1 -> lemma_eval_step_ok_unchanged_add_right_xtra a xtra s
  | _ ->
    lemma_eval_steps_last_ok_means_idx_ok n a s 0;
    lemma_eval_step_ok_unchanged_add_right_xtra a xtra s;
    lemma_eval_steps_ok_unchanged_add_right_xtra (n-1) a xtra (eval_step a s)
#pop-options

#push-options "--fuel 1"
let rec lemma_eval_steps_unchanged_add_right_xtra
    (n:nat) (a b xtra:list precode) (s:state) :
  Lemma
    (requires (
        (length a = length b) /\
        (same_fn_entry_points a b) /\
        (same_fn_entry_points [] xtra) /\
        (eval_steps n a s == eval_steps n b s) /\
        (n > 0 ==> (last (eval_steps n a s)).ok = AllOk)))
    (ensures (
        (eval_steps n (a @ xtra) s == eval_steps n (b @ xtra) s))) =
  match n with
  | 0 -> ()
  | _ ->
    // assert (eval_step a s == eval_step b s);
    lemma_eval_step_unchanged_add_right_xtra a b xtra s;
    // assert (eval_step (a @ xtra) s == eval_step (b @ xtra) s);
    lemma_eval_steps_last_ok_means_idx_ok n a s (n-1);
    lemma_eval_steps_last_ok_means_idx_ok n a s 0;
    lemma_eval_step_ok_unchanged_add_right_xtra a xtra s;
    // assert (eval_step (a @ xtra) s == eval_step a s);
    // assert (eval_steps (n-1) a (eval_step (a @ xtra) s) == eval_steps (n-1) b (eval_step (b @ xtra) s));
    // assert (n > 1 ==> (last (eval_steps (n-1) a (eval_step (a @ xtra) s))).ok = AllOk);
    lemma_eval_steps_unchanged_add_right_xtra (n-1) a b xtra (eval_step (a @ xtra) s)
#pop-options

let lemma_list_reorg (a b c d:list precode) :
  Lemma
    (ensures ((a @ b @ c) @ d == a @ b @ c @ d)) =
  LP.append_assoc a b (c @ d);
  LP.append_assoc (a @ b) c d;
  LP.append_assoc a b c

#push-options "--fuel 1"
let lemma_eval_steps_irrelevant_mid_add_xtra
    (n:nat) (left mid right xtra:list precode) (s:state) :
  Lemma
    (requires (
        (n > 0) /\
        (same_fn_entry_points [] xtra) /\
        (eval_steps_irrelevant_mid n left mid right s) /\
        ((last (eval_steps n (left @ mid @ right) s)).ok = AllOk)))
    (ensures (
       (eval_steps_irrelevant_mid n left mid (right @ xtra) s))) =
  let aux mid' : Lemma
    (requires (
       (length mid == length mid') /\
       (same_fn_entry_points mid mid')))
    (ensures (
        (eval_steps n (left @ mid' @ (right @ xtra)) s == eval_steps n (left @ mid @ (right @ xtra)) s)))
    [SMTPat (eval_steps n (left @ mid' @ (right @ xtra)) s)] =
    calc (==) {
      (eval_steps n (left @ mid @ (right @ xtra)) s); =={ lemma_list_reorg left mid right xtra }
      (eval_steps n ((left @ mid @ right) @ xtra) s); =={
        lemma_same_fn_entry_points_reflexive right;
        lemma_same_fn_entry_points_append_left2 mid mid' right right;
        lemma_same_fn_entry_points_append_left left (mid @ right) (mid' @ right);
        lemma_eval_steps_unchanged_add_right_xtra n (left @ mid @ right) (left @ mid' @ right) xtra s }
      (eval_steps n ((left @ mid' @ right) @ xtra) s); =={ lemma_list_reorg left mid' right xtra }
      (eval_steps n (left @ mid' @ (right @ xtra)) s);
    }
  in
  ()
#pop-options

#push-options "--fuel 1"
let rec max_val #t (l:list t) (f:t -> nat) :
  Pure nat
    (requires (True))
    (ensures (fun r ->
         (forall i. {:pattern (index l i)}
            ((i < length l) ==> (f (index l i) <= r))))) =
  allow_inversion (list t);
  match l with
  | [] -> 0
  | h :: t ->
    let v1 = f h in
    let v2 = max_val t f in
    if v1 >= v2 then v1 else v2
#pop-options

#push-options "--fuel 1 --ifuel 1"
let lemma_safe_callstack_monotone (s:state) (l1 l2:loc) :
  Lemma
    (requires (l1 <= l2 /\ safe_callstack s l1))
    (ensures (safe_callstack s l2)) =
  let rec aux cs :
    Lemma
      (requires (l1 <= l2 /\ for_all (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l1) cs))
      (ensures (for_all (fun ((next, _, _, _) : (loc * int * int * nat64)) -> next < l2) cs)) =
    match cs with
    | [] -> ()
    | h :: t -> aux t
  in
  aux s.callstack
#pop-options

#push-options "--fuel 1 --ifuel 1"
let max_possible_next_ip (a:aux_info) (c:erased cfg) (p:precode) (s:erased state) (limit:nat) :
  Pure bool
    (requires (s.aux = a.m_aux /\ same_fn_entry_points a.orig_code c))
    (ensures (fun b ->
         let s1, ip = eval_step' c p s in
         (b /\ safe_callstack s limit) ==> (
           (s1.ok = AllOk ==> ip < limit) /\
           (safe_callstack s1 limit)
           ))) =
  allow_inversion precode;
  allow_inversion target_t;
  match p with
  | FnEntry _ next -> next < limit
  | Ins i next ->
    lemma_eval_ins_maintains_callstack i s;
    next < limit
  | InsList is next ->
    lemma_eval_inss_maintains_callstack is s;
    next < limit
  | Nop next -> next < limit
  | FnExit _ -> true
  | Cmp _ nextTrue nextFalse -> nextTrue < limit && nextFalse < limit
  | Switch case_table case -> (
      if case_table < length a.m_aux.br_tables then (
        max_val (index a.m_aux.br_tables case_table).br_targets id < limit
      ) else (
        true
      )
    )
  | Call target onreturn ->
    FStar.Classical.forall_intro (FStar.Classical.move_requires (lemma_same_fn_entry_points a.orig_code c));
    onreturn < limit &&
    (match target with
     | CallDirect n -> (
         match find_real_fn_entry n a.orig_code with
         | None -> true
         | Some m -> m < limit
       )
     | CallIndirect r -> max_val a.m_aux.call_table.call_init (fun v ->
         match v with
         | None -> 0
         | Some n ->
           match find_real_fn_entry n a.orig_code with
           | None -> 0
           | Some m -> m) < limit
    )
  | HighCall _ _ _ _ -> true
  | Ret _ -> true
  | HighRet _ _ -> true
#pop-options

(** Perform a validation check to make sure that the next instruction
    pointer after execution is placed exactly within the region we
    expect it to be placed. This should not be directly necessary, if
    we carefully weave the CFI proof from [pre_process_cfg] through
    the entire proof, however, it is much more convenient to simply
    perform a quick validation and get the proof done with instead. *)
let restrict_possible_next_ip_below (m:loc) (a:aux_info) (c:erased cfg) (p:precode) (s:erased state) :
  Err unit
    (requires (s.aux = a.m_aux /\ same_fn_entry_points a.orig_code c))
    (ensures (fun () ->
         let s1, ip = eval_step' c p s in
         ((safe_callstack s m)) ==> (s1.ok = AllOk ==> ip < m))) =
  if max_possible_next_ip a c p s m then () else (
    fail_with ("Impossible break out of CFI guarantees for " ^ string_of_precode p)
  )

#push-options "--fuel 2"
let lemma_non_fn_entry_point (p:precode) :
  Lemma
    (requires (~(FnEntry? p)))
    (ensures (same_fn_entry_points [] [p])) = ()
#pop-options

#push-options "--fuel 1"
let rec lemma_unzip_append #t1 #t2 (l1 l2:list (t1 & t2)) :
  Lemma
    (ensures (
        (fst (unzip (l1 @ l2)) == fst (unzip l1) @ fst (unzip l2)) /\
        (snd (unzip (l1 @ l2)) == snd (unzip l1) @ snd (unzip l2)))) =
  allow_inversion (list (t1 & t2));
  match l1 with
  | [] -> ()
  | h :: t -> lemma_unzip_append t l2
#pop-options

#push-options "--fuel 3"
let lemma_eval_steps_2_expand (c:list precode) (s:state) :
  Lemma
    (eval_steps 2 c s == [eval_step c s; eval_step c (eval_step c s)]) = ()
#pop-options

unfold
let equiv_except_ip (s1 s2:state) : GTot Type0 =
  s2 == {s1 with ip = s2.ip}

let lemma_eval_ins_ip_irrelevance (i:ins_t) (s1 s2:state) :
  Lemma
    (requires (equiv_except_ip s1 s2))
    (ensures (equiv_except_ip (eval_ins i s1) (eval_ins i s2))) =
  admit () (* TODO: Prove this once instruction semantics are completed *)

#push-options "--fuel 1"
let rec lemma_eval_inss_ip_irrelevance (is:list ins_t) (s1 s2:state) :
  Lemma
    (requires (equiv_except_ip s1 s2))
    (ensures (equiv_except_ip (eval_inss is s1) (eval_inss is s2))) =
  allow_inversion (list ins_t);
  match is with
  | [] -> ()
  | h :: t ->
    lemma_eval_ins_ip_irrelevance h s1 s2;
    lemma_eval_inss_ip_irrelevance t (eval_ins h s1) (eval_ins h s2)
#pop-options

let lemma_check_valid_ocmp_ip_irrelevance (cond:ocmp) (s1 s2:state) :
  Lemma
    (requires (equiv_except_ip s1 s2))
    (ensures (equiv_except_ip (check_valid_ocmp cond s1) (check_valid_ocmp cond s2))) =
  assert (valid_ocmp cond s1 = valid_ocmp cond s2) by (
    norm [delta_only [`%valid_ocmp]];
    seq (fun () -> destruct (`(`@cond))) (fun () ->
        let breq = last_binder_after_intros () in
        rewrite breq;
        norm [iota];
        rewrite_all_equalities ();
        norm [delta_fully [`%valid_src_operand32; `%valid_src_operand64]];
        smt ())
  )

let lemma_eval_ocmp_ip_irrelevance (cond:ocmp) (s1 s2:state) :
  Lemma
    (requires (equiv_except_ip s1 s2))
    (ensures ((eval_ocmp cond s1) = (eval_ocmp cond s2))) = ()

let lemma_eval_step'_ip_irrelevance (c:list precode) (p:precode) (s1 s2:state) :
  Lemma
    (requires (equiv_except_ip s1 s2))
    (ensures (
        let s1', ip1 = eval_step' c p s1 in
        let s2', ip2 = eval_step' c p s2 in
        (equiv_except_ip s1' s2') /\
        (s1'.ok = AllOk ==> ip1 = ip2))) =
  allow_inversion precode;
  match p with
  | FnEntry _ _ -> ()
  | FnExit _ -> ()
  | Ins i _ -> lemma_eval_ins_ip_irrelevance i s1 s2
  | InsList is _ -> lemma_eval_inss_ip_irrelevance is s1 s2
  | Nop _ -> ()
  | Cmp cond _ _ ->
    lemma_check_valid_ocmp_ip_irrelevance cond s1 s2;
    lemma_eval_ocmp_ip_irrelevance cond (check_valid_ocmp cond s1) (check_valid_ocmp cond s2)
  | Switch case_table case -> ()
  | Call target next ->
    if is_imported_function_target target s1 then
      axiom_external_call_ip_irrelevance s1 s2 (Some?.v (find_call_name target s1))
  | HighCall _ _ _ _ -> ()
  | Ret _ -> ()
  | HighRet _ _ -> ()

#push-options "--fuel 1"
let lemma_double_step_irrelevant_mid (i:nat) (add_loc:loc) (left:list precode) (addn:list ins_t) (tl right:list precode) (modf:precode) (s:state) :
  Lemma
    (requires (
        (add_loc = length left + 1 + length tl + length right) /\
        ((eval_step ((snoc (left, InsList addn add_loc)) @ tl @ (snoc (right, modf))) s).ok == AllOk) /\
        (s.ip == length left)))
    (ensures (
        eval_steps_irrelevant_mid 2 (snoc (left, InsList addn add_loc)) tl (snoc (right, modf)) s)) =
  let aux mid : Lemma
    (requires (length tl == length mid /\ same_fn_entry_points tl mid))
    (ensures (eval_steps 2 (snoc (left, InsList addn add_loc) @ mid @ snoc (right, modf)) s == eval_steps 2 (snoc (left, InsList addn add_loc) @ tl @ snoc (right, modf)) s))
    [SMTPat (snoc (left, InsList addn add_loc) @ mid @ snoc (right, modf))] =
    let c1 = snoc (left, InsList addn add_loc) @ tl @ snoc (right, modf) in
    let c2 = snoc (left, InsList addn add_loc) @ mid @ snoc (right, modf) in
    lemma_same_fn_entry_points_reflexive (snoc (right, modf));
    lemma_same_fn_entry_points_append_left2 tl mid (snoc (right, modf)) (snoc (right, modf));
    lemma_move_left left (InsList addn add_loc) tl (snoc (right, modf));
    lemma_move_left left (InsList addn add_loc) mid (snoc (right, modf));
    lemma_same_fn_entry_points_append_left left (InsList addn add_loc :: tl @ snoc (right, modf)) (InsList addn add_loc :: mid @ snoc (right, modf));
    // assert (same_fn_entry_points c1 c2);
    lemma_eval_step'_unchanged_replacement c1 c2 (InsList addn add_loc) s;
    LP.lemma_snoc_length (right, modf);
    LP.append_length tl (snoc (right, modf));
    LP.append_length mid (snoc (right, modf));
    LP.lemma_snoc_length (left, InsList addn add_loc);
    LP.append_length (snoc (left, InsList addn add_loc)) (tl @ snoc (right, modf));
    LP.append_length (snoc (left, InsList addn add_loc)) (mid @ snoc (right, modf));
    // assert (length c1 = length left + 1 + length tl + length right + 1);
    // assert (length c2 = length left + 1 + length tl + length right + 1);
    // assert (s.ip < length c1);
    // assert (s.ip < length c2);
    lemma_index_append_length left (InsList addn add_loc :: tl @ snoc (right, modf));
    lemma_index_append_length left (InsList addn add_loc :: mid @ snoc (right, modf));
    // assert (index c1 s.ip = InsList addn add_loc);
    // assert (index c2 s.ip = InsList addn add_loc);
    let s1, ip1 = eval_step' c1 (InsList addn add_loc) s in
    let s2, ip2 = eval_step' c2 (InsList addn add_loc) s in
    // assert_norm (eval_step c1 s == {s1 with ip = ip1});
    // assert_norm (eval_step c2 s == {s2 with ip = ip2});
    // assert (eval_step c1 s == eval_step c2 s);
    let s' = eval_step c1 s in
    lemma_eval_step'_unchanged_replacement c1 c2 modf s';
    // assert (s'.ip < length c1);
    // assert (s'.ip < length c2);
    // assert (s'.ip = length left + 1 + length tl + length right);
    LP.lemma_append_last (snoc (left, InsList addn add_loc)) (tl @ snoc (right, modf));
    LP.lemma_append_last (snoc (left, InsList addn add_loc)) (mid @ snoc (right, modf));
    LP.lemma_append_last tl (snoc (right, modf));
    LP.lemma_append_last mid (snoc (right, modf));
    LP.lemma_append_last right [modf];
    // assert (last [modf] == modf);
    // assert (last c1 = modf);
    // assert (last c2 = modf);
    LP.lemma_unsnoc_is_last c1;
    LP.lemma_unsnoc_is_last c2;
    // assert (index c1 s'.ip = modf);
    // assert (index c2 s'.ip = modf);
    let s1, ip1 = eval_step' c1 modf s' in
    let s2, ip2 = eval_step' c2 modf s' in
    // assert (s'.ok = AllOk);
    // assert_norm (eval_step c1 s' == {s1 with ip = ip1});
    // assert_norm (eval_step c2 s' == {s2 with ip = ip2});
    // assert (eval_step c1 s' == eval_step c2 s');
    // let s'' = eval_step c1 s' in
    lemma_eval_steps_2_expand c1 s;
    lemma_eval_steps_2_expand c2 s;
    // assert (eval_steps 2 c1 s == [s'; s'']);
    // assert (eval_steps 2 c2 s == [s'; s'']);
    ()
  in
  ()
#pop-options

(* An aux one-time-use lemma to reduce context bloat *)
#push-options "--fuel 1"
let lemma_index_last_loc left addn mid right xtra :
  Lemma
    (ensures (
        let l = fst (unzip (snoc (left, addn))) @ mid @ snoc (right, xtra) in
        let i = length left + 1 + length mid + length right in
        (i < length l) /\
        (index l i == xtra))) =
  let i = length left + 1 + length mid + length right in
  let l = fst (unzip (snoc (left, addn))) @ mid @ snoc (right, xtra) in
  let lft = fst (unzip left) in
  let adn, adn2 = addn in
  lemma_unzip_snoc left adn adn2;
  lemma_unzip_length (snoc (left, addn));
  lemma_unzip_length left;
  lemma_move_left lft adn mid (snoc (right, xtra));
  assert (l == lft @ adn :: mid @ snoc (right, xtra));
  LP.lemma_snoc_length (right, xtra);
  assert (length (snoc (right, xtra)) = length right + 1);
  LP.append_length mid (snoc (right, xtra));
  assert (length (mid @ snoc (right, xtra)) = length mid + length right + 1);
  LP.append_length lft (adn :: mid @ snoc (right, xtra));
  assert (length l = length left + 1 + length mid + length right + 1);
  assert (i < length l);
  LP.lemma_unsnoc_is_last l;
  LP.lemma_append_last right [xtra];
  LP.lemma_append_last mid (snoc (right, xtra));
  LP.lemma_append_last (fst (unzip (snoc (left, addn)))) (mid @ snoc (right, xtra));
  assert (last l == xtra)
#pop-options

let rec safe_callstacks (ss:list state) (l:loc) : Tot bool =
  allow_inversion (list state);
  match ss with
  | [] -> true
  | h :: t -> safe_callstack h l && safe_callstacks t l

#push-options "--fuel 1"
unfold
let precond_process_precode (a:aux_info) (len_finished_and_processing:nat) (l_finished: A.t (precode & nat)) (l_processing: list precode) (l_added:A.t precode) (s:state) : GTot Type0 =
  (len_finished_and_processing = A.length l_finished + length l_processing) /\
  (sane_call_tables a) /\
  (safe_callstack s (length (A.to_list l_finished) + length l_processing)) /\
  (same_fn_entry_points a.orig_code (fst (unzip (A.to_list l_finished)) @ l_processing @ (A.to_list l_added))) /\
  ((s.ip < A.length l_finished) ==> (
      let n = snd (index (A.to_list l_finished) s.ip) in
      let finished' = fst (unzip (A.to_list l_finished)) in
      let ss = eval_steps n (finished' @ l_processing @ (A.to_list l_added)) s in
      (n == 1 \/ n == 2) /\
      (eval_steps_irrelevant_mid n finished' l_processing (A.to_list l_added) s) /\
      (safe_callstacks ss (A.length l_finished + length l_processing)) /\
      (not (last ss).explicitly_safely_killed ==> (last ss).ip < A.length l_finished + length l_processing) /\
      (valid_sb_state a (last ss)))) /\
  (valid_sb_state a s) /\
  (valid_sb_size a)

unfold
let postcond_process_precode (a:aux_info) (len_finished_and_processing:nat) (l_finished: A.t (precode & nat)) (l_processing: list precode) (l_added:A.t precode) (s:state) (r:A.t (precode & nat)) : GTot Type0 =
  (A.length r >= A.length l_finished + length l_processing) /\
  ((s.ip < A.length l_finished + length l_processing) ==> (
      let n = snd (index (A.to_list r) s.ip) in
      let ss = eval_steps n (fst (unzip (A.to_list r))) s in
      (n == 1 \/ n == 2) /\
      (safe_callstacks ss (A.length l_finished + length l_processing)) /\
      (not (last ss).explicitly_safely_killed ==> (last ss).ip < A.length l_finished + length l_processing) /\
      (valid_sb_state a (last ss))))
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
(** Perform across all instructions.  Expected to be called with
    `process_precode a [] l []`. *)
let rec process_precode
    (a:aux_info)
    (len_finished_and_processing:nat)
    (l_finished: A.t (precode & nat)) (l_processing: list precode) (l_added:A.t precode)
    (s: erased state) :
  Err (A.t (precode & nat))
    (requires (precond_process_precode a len_finished_and_processing l_finished l_processing l_added s))
    (ensures (postcond_process_precode a len_finished_and_processing l_finished l_processing l_added s))
    (decreases %[l_processing]) =
  allow_inversion (list precode);
  allow_inversion (list ins_t);
  match l_processing with
  | [] ->
    let right = A.zip l_added (A.repeat (A.length l_added) 0) in
    let r = l_finished `A.append` right in
    // assert_norm (length l_processing = 0);
    LP.append_length (A.to_list l_finished) (A.to_list right);
    // assert (length r >= length l_finished + length l_processing);
    // assert (s.ip < length l_finished + length l_processing ==> s.ip < length l_finished);
    if s.ip < A.length l_finished then lemma_index_append1 (A.to_list l_finished) (A.to_list right) s.ip;
    // assert (s.ip < length l_finished ==> index r s.ip == index l_finished s.ip);
    lemma_unzip_append (A.to_list l_finished) (A.to_list right);
    // assert (fst (unzip r) == fst (unzip l_finished) @ l_added);
    // assert ((s.ip < length l_finished + length l_processing) ==> (
    //          let n = snd (index r s.ip) in
    //          let s1 = eval_steps n (fst (unzip r)) s in
    //          (s1.ip < length l_finished + length l_processing) /\
    //          (valid_sb_state a s1)));
    r
  | hd :: tl ->
    lemma_length_tl hd tl;
    let add_loc = len_finished_and_processing +
                  A.length l_added in
    let modified_code : erased _ = fst (unzip (A.to_list l_finished)) @ l_processing @ (A.to_list l_added) in
    let addn, modf = compile_precode ({ a with add_loc; modified_code }) hd len_finished_and_processing s in
    let addn = A.to_list addn in
    match addn with
    | [] -> (
        let finished = A.snoc (l_finished, (modf, 1)) in
        let added = l_added in
        lemma_unzip_snoc (A.to_list l_finished) modf 1;
        lemma_same_fn_entry_points_maintained1 a.orig_code (fst (unzip (A.to_list l_finished))) hd modf tl (A.to_list l_added);
        restrict_possible_next_ip_below len_finished_and_processing a (fst (unzip (A.to_list finished)) @ tl @ (A.to_list added)) modf s;
        LP.lemma_snoc_length ((A.to_list l_finished), (modf, 1));
        FStar.Classical.forall_intro (lemma_index_snoc (A.to_list l_finished) (modf, 1));
        let aux i :
          Lemma
            (requires (
                (i < A.length finished /\ s.ip = i) /\
                (forall i. {:pattern (index (A.to_list l_finished) i)}
                   (i < A.length l_finished /\ s.ip = i) ==> (
                   let n = snd (index (A.to_list l_finished) i) in
                   let finished' = fst (unzip (A.to_list l_finished)) in
                   let ss = eval_steps n (finished' @ l_processing @ (A.to_list l_added)) s in
                   (n == 1 \/ n == 2) /\
                   (eval_steps_irrelevant_mid n finished' l_processing (A.to_list l_added) s) /\
                   (safe_callstacks ss len_finished_and_processing) /\
                   (not (last ss).explicitly_safely_killed ==> (last ss).ip < len_finished_and_processing) /\
                   (valid_sb_state a (last ss))))))
            (ensures (
                (let n = snd (index (A.to_list finished) i) in
                 let finished' = fst (unzip (A.to_list finished)) in
                 let ss = eval_steps n (finished' @ tl @ (A.to_list added)) s in
                 (n == 1 \/ n == 2) /\
                 (eval_steps_irrelevant_mid n finished' tl (A.to_list added) s) /\
                 (safe_callstacks ss (A.length finished + length tl)) /\
                 (not (last ss).explicitly_safely_killed ==> (last ss).ip < A.length finished + length tl) /\
                 (valid_sb_state a (last ss))))) =
          let n = snd (index (A.to_list finished) i) in
          let finished' = fst (unzip (A.to_list finished)) in
          if i = A.length l_finished then (
            LP.lemma_unsnoc_snoc (A.to_list finished);
            LP.lemma_unsnoc_is_last (A.to_list finished);
            // assert (i == length (snoc (l_finished, (modf, 1))) - 1);
            // assert (index finished i == (modf, 1));
            // assert (n == 1);
            let s1 = last (eval_steps n (finished' @ tl @ (A.to_list added)) s) in
            assert_norm (s1 == eval_step (finished' @ tl @ (A.to_list added)) s); (* OBSERVE *)
            // assert (addn = []);
            // assert_norm (eval_inss [] s == reveal s);
            lemma_unzip_length (A.to_list l_finished);
            // assert (length (fst (unzip l_finished)) == length l_finished);
            lemma_single_step_irrelevant_mid i (fst (unzip (A.to_list l_finished))) modf tl (A.to_list added) s;
            lemma_unzip_snoc (A.to_list l_finished) modf 1;
            // assert (finished' == snoc (fst (unzip l_finished), modf));
            // assert (eval_steps_irrelevant_mid n finished' tl added s);
            lemma_move_left (fst (unzip (A.to_list l_finished))) modf tl (A.to_list added);
            LP.lemma_snoc_length (fst (unzip (A.to_list l_finished)), modf);
            lemma_index_append_length (fst (unzip (A.to_list l_finished))) (modf :: (tl @ (A.to_list added)));
            // assert (s.ip `in_cfg` (finished' @ tl @ added));
            // assert (get_code_at s.ip (finished' @ tl @ added) == modf);
            let s2, ip2 = eval_step' (finished' @ tl @ (A.to_list added)) modf s in
            // assert_norm (s1 == {s2 with ip = ip2});
            lemma_same_fn_entry_points_reflexive tl;
            lemma_eval_step'_changed_mid (fst (unzip (A.to_list l_finished))) (hd :: tl) (modf :: tl) (A.to_list added) modf s;
            let s3, ip3 = eval_step' (fst (unzip (A.to_list l_finished)) @ (hd :: tl) @ (A.to_list added)) modf s in
            // assert (fst (unzip l_finished) @ (modf :: tl) @ added == finished' @ tl @ added);
            // assert (s2 == s3);
            // assert (valid_sb_state a s3);
            calc (==>) {
              (True /\ safe_callstack s1 (A.length finished + length tl)); (==>) {
                assert_norm (safe_callstacks [] (A.length finished + length tl)) (* OBSERVE *)
              }
              (True /\ safe_callstacks [s1] (A.length finished + length tl));
              (==>) {
                assert_norm (eval_steps n (finished' @ tl @ (A.to_list added)) s == [s1]) (* OBSERVE *)
              }
              (True /\ safe_callstacks (eval_steps n (finished' @ tl @ (A.to_list added)) s) (A.length finished + length tl));
            };
            // assert (safe_callstacks (eval_steps n (finished' @ tl @ added) s) (length finished + length tl));
            // assert (s1.ip < length l_finished + length l_processing);
            // assert (s1.ip < length finished + length tl);
            // assert (valid_sb_state a s1);
            ()
          ) else (
            // assert (n > 0);
            let s1 = last (eval_steps n (finished' @ tl @ (A.to_list added)) s) in
            // assert (length l_finished + 1 == length finished);
            // assert (i < length finished);
            // assert (i < length l_finished);
            // assert (n == snd (index l_finished i));
            // assert (eval_steps_irrelevant_mid n (fst (unzip l_finished)) (length l_processing) l_added s);
            lemma_eval_steps_irrelevant_mid_move_left n (fst (unzip (A.to_list l_finished))) hd modf tl (A.to_list added) s;
            lemma_unzip_snoc (A.to_list l_finished) modf 1;
            // assert (finished' == snoc (fst (unzip l_finished), modf));
            // assert (eval_steps_irrelevant_mid n finished' (length tl) added s);
            lemma_eval_steps_irrelevant_mid_move_left' n (fst (unzip (A.to_list l_finished))) hd modf tl (A.to_list l_added) s;
            lemma_move_left (fst (unzip (A.to_list l_finished))) modf tl (A.to_list l_added);
            // assert (finished' @ tl @ l_added == fst (unzip l_finished) @ (modf :: tl) @ l_added);
            // assert (s1.ip < length finished + length tl);
            // assert (valid_sb_state a s1);
            ()
          )
        in
        if s.ip < A.length finished then aux s.ip else ();
        // assert (FnEntry? hd \/ FnEntry? modf ==> hd == modf);
        process_precode a len_finished_and_processing finished tl added s
      )
    | _ -> (
        let finished = A.snoc (l_finished, (InsList addn add_loc, 2)) in
        let added = A.snoc (l_added, modf) in
        let finished' : erased _ = fst (unzip (A.to_list finished)) in
        let s11 : erased _ = eval_step (finished' @ tl @ (A.to_list added)) s in
        let s12 : erased _ = eval_step (finished' @ tl @ (A.to_list added)) s11 in
        LP.lemma_snoc_length ((A.to_list l_finished), (InsList addn add_loc, 2));
        lemma_eval_step_maintains_aux (fst (unzip (A.to_list finished)) @ tl @ (A.to_list added)) s;
        // assert (a.m_aux = (eval_step (fst (unzip finished) @ tl @ added) s).aux);
        LP.lemma_snoc_length ((A.to_list l_finished), (InsList addn add_loc, 2));
        LP.lemma_snoc_length ((A.to_list l_added), modf);
        lemma_index_last_loc (A.to_list l_finished) (InsList addn add_loc, 2) tl (A.to_list l_added) modf;
        // assert (add_loc < length (fst (unzip finished) @ tl @ added));
        // assert (index (fst (unzip finished) @ tl @ added) add_loc == modf);
        // FStar.Classical.forall_intro (lemma_index_snoc l_finished (InsList addn add_loc, 2));
        lemma_unzip_snoc (A.to_list l_finished) (InsList addn add_loc) 2;
        lemma_move_left (fst (unzip (A.to_list l_finished))) (InsList addn add_loc) tl (A.to_list added);
        lemma_index_append_length (fst (unzip (A.to_list l_finished))) ((InsList addn add_loc) :: tl @ (A.to_list added));
        lemma_unzip_length (A.to_list l_finished);
        // assert (length l_finished == length (fst (unzip l_finished)));
        // assert (index (fst (unzip finished) @ tl @ added) (length l_finished) == InsList addn add_loc);
        // assert (length finished == length l_finished + 1);
        // assert (safe_callstack s (length finished + length tl));
        lemma_same_fn_entry_points_reflexive modified_code;
        lemma_same_fn_entry_points_maintained2 modified_code (fst (unzip (A.to_list l_finished))) hd (InsList addn add_loc) tl (A.to_list l_added) modf;
        lemma_same_fn_entry_points_maintained2 a.orig_code (fst (unzip (A.to_list l_finished))) hd (InsList addn add_loc) tl (A.to_list l_added) modf;
        lemma_non_fn_entry_point modf;
        restrict_possible_next_ip_below (A.length finished + length tl) a (fst (unzip (A.to_list finished)) @ tl @ (A.to_list added)) modf s11;
        if s.ip < A.length finished then (
          let i = s.ip in
          let n = snd (index (A.to_list finished) s.ip) in
          if s.ip = A.length l_finished then (
            LP.lemma_unsnoc_snoc (A.to_list finished);
            LP.lemma_unsnoc_is_last (A.to_list finished);
            // assert (n == 2);
            let s1 = last (eval_steps n (finished' @ tl @ (A.to_list added)) s) in
            lemma_eval_steps_2_expand (finished' @ tl @ (A.to_list added)) s;
            // assert (eval_steps n (finished' @ tl @ added) s == [s11; s12]);
            assert_norm (s1 == reveal s12); (* OBSERVE *)
            if s.explicitly_safely_killed then (
              assert_norm (s1 == reveal s);
              lemma_double_step_irrelevant_mid i add_loc (fst (unzip (A.to_list l_finished))) addn tl (A.to_list l_added) modf s;
              // assert (eval_steps_irrelevant_mid n finished' tl added s);
              let cfi_loc = A.length finished + length tl in
              calc (==>) {
                (True /\ safe_callstack s1 cfi_loc); (==>) {}
                (True /\ safe_callstack (reveal s11) cfi_loc /\ safe_callstack s1 cfi_loc); (==>) {
                  assert_norm (safe_callstacks [] cfi_loc); (* OBSERVE *)
                  assert_spinoff (safe_callstacks [s1] cfi_loc) (* OBSERVE *)
                }
                (True /\ safe_callstacks [reveal s11; s1] (A.length finished + length tl));
              };
              // assert (safe_callstacks [reveal s11; s1] (length finished + length tl));
              ()
            ) else (
              // assert_norm (s11 == ({eval_inss addn s with ip = add_loc}));
              // assert (valid_sb_state a (fst (eval_step' modified_code modf (eval_inss addn s))));
              lemma_eval_step'_ip_irrelevance modified_code modf (eval_inss addn s) s11;
              // assert (valid_sb_state a (fst (eval_step' modified_code modf s11)));
              // assert (same_fn_entry_points modified_code (finished' @ tl @ added));
              lemma_eval_step'_unchanged_replacement modified_code (finished' @ tl @ (A.to_list added)) modf s11;
              lemma_double_step_irrelevant_mid i add_loc (fst (unzip (A.to_list l_finished))) addn tl (A.to_list l_added) modf s;
              // assert (eval_steps_irrelevant_mid n finished' tl added s);
              lemma_eval_inss_maintains_callstack addn s;
              // assert (safe_callstack s11 (length finished + length tl));
              let cfi_loc = A.length finished + length tl in
              calc (==>) {
                (True /\ safe_callstack s1 cfi_loc); (==>) {
                  lemma_eval_inss_maintains_callstack addn s
                }
                (True /\ safe_callstack (reveal s11) cfi_loc /\ safe_callstack s1 cfi_loc); (==>) {
                  assert_norm (safe_callstacks [] cfi_loc) (* OBSERVE *)
                }
                (True /\ safe_callstack (reveal s11) cfi_loc /\ safe_callstacks [s1] cfi_loc); (==>) {
                  // assert_norm (safe_callstacks [] cfi_loc) (* OBSERVE *)
                }
                (True /\ safe_callstacks [reveal s11; s1] (A.length finished + length tl));
              };
              // assert_norm (s1.ip = snd (eval_step' (finished' @ tl @ added) modf s11));
              // assert (s1.ip < length finished + length tl);
              // assert (valid_sb_state a s1);
              ()
            )
          ) else (
            // assert (s.ip < length l_finished);
            // assert (length l_finished + 1 == length finished);
            // assert (i < length l_finished);
            lemma_index_append1 (A.to_list l_finished) [(InsList addn add_loc, 2)] i;
            // assert (n == snd (index l_finished i));
            // assert (n == 1 \/ n == 2);
            let s1 = last (eval_steps n (finished' @ tl @ (A.to_list added)) s) in
            lemma_eval_steps_irrelevant_mid_move_left n (fst (unzip (A.to_list l_finished))) hd (InsList addn add_loc) tl (A.to_list l_added) s;
            // assert (eval_steps_irrelevant_mid n finished' tl l_added s);
            lemma_eval_steps_irrelevant_mid_move_left' n (fst (unzip (A.to_list l_finished))) hd (InsList addn add_loc) tl (A.to_list l_added) s;
            lemma_move_left (fst (unzip (A.to_list l_finished))) (InsList addn add_loc) tl (A.to_list l_added);
            // assert ((last (eval_steps n (finished' @ tl @ l_added) s)).ok = AllOk);
            lemma_eval_steps_irrelevant_mid_add_xtra n finished' tl (A.to_list l_added) [modf] s;
            // assert (eval_steps_irrelevant_mid n finished' tl added s);
            // assert (eval_steps n (fst (unzip (l_finished)) @ l_processing @ l_added) s == eval_steps n (finished' @ tl @ l_added) s);
            lemma_eval_steps_ok_unchanged_add_right_xtra n (finished' @ tl @ (A.to_list l_added)) [modf] s;
            lemma_list_reorg finished' tl (A.to_list l_added) [modf];
            // assert (eval_steps n (finished' @ tl @ l_added) s == eval_steps n (finished' @ tl @ added) s);
            // assert (s1.ip < length finished + length tl);
            // assert (valid_sb_state a s1);
            ()
          )
        );
        // assert (valid_sb_state a s);
        // assert (valid_sb_size a);
        process_precode a len_finished_and_processing finished tl added s
      )
#pop-options

let lemma_process_precode_state_irrelevance
    (a:aux_info) (len_finished_and_processing:nat) (l_finished: A.t (precode & nat)) (l_processing:list precode) (l_added:A.t precode)
    (s1 s2: erased state) :
  Lemma
    (requires (
        (precond_process_precode a len_finished_and_processing l_finished l_processing l_added s1) /\
        (precond_process_precode a len_finished_and_processing l_finished l_processing l_added s2)))
    (ensures (
        reify (process_precode a len_finished_and_processing l_finished l_processing l_added s1) () ==
        reify (process_precode a len_finished_and_processing l_finished l_processing l_added s2) ())) =
  admit () (* This is true because of computational irrelevance of erased code *)

#push-options "--fuel 1"
[@"opaque_to_smt"]
let aux_stepped_ok_and_cfi_maintenance (a:aux_info) (cn:list (precode & nat)) (cfi_loc:loc) : GTot Type0 =
  (cfi_loc <= length cn) /\
  (forall s'. (
       (valid_sb_state a s') /\
       (safe_callstack s' cfi_loc) /\
       (s'.ip < cfi_loc)
     ) ==> ((
      let n' = snd (index cn s'.ip) in
      let ss' = eval_steps n' (fst (unzip cn)) s' in
      (n' == 1 \/ n' == 2) /\
      (not (last ss').explicitly_safely_killed ==> (last ss').ip < cfi_loc) /\
      ((last ss').ok = AllOk) /\
      (safe_callstacks ss' cfi_loc)
    )))
#pop-options

let lemma_aux_stepped_ok_and_cfi_maintenance' (a:aux_info) (cn:list (precode & nat)) (cfi_loc:loc) (s':state) : Lemma
    (requires (
        (aux_stepped_ok_and_cfi_maintenance a cn cfi_loc) /\
        (cfi_loc <= length cn) /\
        (valid_sb_state a s') /\
        (safe_callstack s' cfi_loc) /\
        (s'.ip < cfi_loc)))
    (ensures (
        let n' = snd (index cn s'.ip) in
        (n' == 1 \/ n' == 2))) =
  reveal_opaque (`%aux_stepped_ok_and_cfi_maintenance) aux_stepped_ok_and_cfi_maintenance

let lemma_aux_stepped_ok_and_cfi_maintenance (a:aux_info) (cn:list (precode & nat)) (cfi_loc:loc) (s':state) (n':nat) (ss':list state{Cons? ss'}) (s1:state) : Lemma
    (requires (
        (aux_stepped_ok_and_cfi_maintenance a cn cfi_loc) /\
        (cfi_loc <= length cn) /\
        (valid_sb_state a s') /\
        (safe_callstack s' cfi_loc) /\
        (s'.ip < cfi_loc) /\
        (n' = snd (index cn s'.ip)) /\
        (ss' == eval_steps n' (fst (unzip cn)) s') /\
        (s1 == last ss')))
    (ensures (
        (n' == 1 \/ n' == 2) /\
        (not s1.explicitly_safely_killed ==> s1.ip < cfi_loc) /\
        (s1.ok = AllOk) /\
        (safe_callstacks ss' cfi_loc))) =
  reveal_opaque (`%aux_stepped_ok_and_cfi_maintenance) aux_stepped_ok_and_cfi_maintenance

#push-options "--fuel 1"
let lemma_process_precode_state_irrelevance'
    (a:aux_info) (len_finished_and_processing:nat) (l_finished: A.t (precode & nat)) (l_processing:list precode) (l_added:A.t precode) (s:state) :
  Lemma
    (requires (
        (Nil? (A.to_list l_finished)) /\
        (precond_process_precode a len_finished_and_processing l_finished l_processing l_added s) /\
        (Ok'? (reify (process_precode a len_finished_and_processing l_finished l_processing l_added s) ()))))
    (ensures (
        let cfi_loc = A.length l_finished + length l_processing in
        let Ok' cn = reify (process_precode a len_finished_and_processing l_finished l_processing l_added s) () in
        aux_stepped_ok_and_cfi_maintenance a (A.to_list cn) cfi_loc)) =
  let cfi_loc = A.length l_finished + length l_processing in
  let Ok' cn = reify (process_precode a len_finished_and_processing l_finished l_processing l_added s) () in
  assert (cfi_loc <= A.length cn);
  let aux s' : Lemma
    (requires (
       (valid_sb_state a s') /\
       (safe_callstack s' cfi_loc) /\
       (s'.ip < cfi_loc)))
    (ensures (
        let n' = snd (index (A.to_list cn) s'.ip) in
        let ss' = eval_steps n' (fst (unzip (A.to_list cn))) s' in
        (n' == 1 \/ n' == 2) /\
        (not (last ss').explicitly_safely_killed ==> (last ss').ip < cfi_loc) /\
        ((last ss').ok = AllOk) /\
        (safe_callstacks ss' cfi_loc)))
    [SMTPat (s'.ok)] =
    lemma_process_precode_state_irrelevance a len_finished_and_processing l_finished l_processing l_added s s';
    assert (Ok' cn == reify (process_precode a len_finished_and_processing l_finished l_processing l_added s') ());
    let n' = snd (index (A.to_list cn) s'.ip) in
    let ss' = eval_steps n' (fst (unzip (A.to_list cn))) s' in
    assert (n' == 1 \/ n' == 2);
    assert (not (last ss').explicitly_safely_killed ==> (last ss').ip < cfi_loc);
    assert ((last ss').ok = AllOk);
    assert (safe_callstacks ss' cfi_loc)
  in
  reveal_opaque (`%aux_stepped_ok_and_cfi_maintenance) aux_stepped_ok_and_cfi_maintenance
#pop-options

#push-options "--fuel 2 --z3rlimit 20"
let rec lemma_invariant_extends_to_all_n (a:aux_info) (s:state) (n:nat) (cn:list (precode & nat)) (cfi_loc:nat) :
  Lemma
    (requires (
        (valid_sb_state a s) /\
        (not s.explicitly_safely_killed ==> s.ip < cfi_loc) /\
        (safe_callstack s cfi_loc) /\
        (cfi_loc <= length cn) /\
        (aux_stepped_ok_and_cfi_maintenance a cn cfi_loc)))
    (ensures (
        let ss = eval_steps n (fst (unzip cn)) s in
        for_all (fun s1 -> s1.ok = AllOk && safe_callstack s1 cfi_loc) ss))
    (decreases %[n]) =
  let ss = eval_steps n (fst (unzip cn)) s in
  match n with
  | 0 -> ()
  | _ ->
    let f s1 = s1.ok = AllOk && safe_callstack s1 cfi_loc in
    if s.explicitly_safely_killed then (
      lemma_invariant_extends_to_all_n a s (n-1) cn cfi_loc
    ) else (
      let c = (fst (unzip cn)) in
      let n1 = snd (index cn s.ip) in
      if n1 = 1 then (
        let s1 = eval_step c s in
        assert_norm (eval_steps 1 c s == [s1]);
        lemma_aux_stepped_ok_and_cfi_maintenance a cn cfi_loc s n1 (eval_steps 1 c s) s1;
        assert (s1.ok = AllOk);
        assert (not s1.explicitly_safely_killed ==> s1.ip < cfi_loc);
        assert (safe_callstack s1 cfi_loc);
        lemma_eval_step_maintains_aux c s;
        lemma_eval_step_monotonic_heap c s;
        assert (valid_sb_state a s1);
        lemma_invariant_extends_to_all_n a s1 (n-1) cn cfi_loc
      ) else (
        lemma_aux_stepped_ok_and_cfi_maintenance' a cn cfi_loc s;
        let s1 = eval_step c s in
        let s2 = eval_step c s1 in
        assert_norm (eval_steps 2 c s == [s1; s2]);
        assert_norm (last [s1; s2] == s2);
        lemma_aux_stepped_ok_and_cfi_maintenance a cn cfi_loc s n1 (eval_steps n1 c s) s2;
        lemma_eval_steps_last_ok_means_idx_ok 2 c s 0;
        assert (s1.ok = AllOk);
        assert (safe_callstacks [s1; s2] cfi_loc);
        assert (safe_callstack s1 cfi_loc);
        assert (s2.ok = AllOk);
        assert (not s2.explicitly_safely_killed ==> s2.ip < cfi_loc);
        assert (safe_callstacks [s2] cfi_loc);
        assert (safe_callstack s2 cfi_loc);
        if n = 1 then (
          assert_norm (ss == [s1]);
          lemma_for_all_cons f ss
        ) else (
          lemma_eval_step_maintains_aux c s;
          lemma_eval_step_maintains_aux c s1;
          lemma_eval_step_monotonic_heap c s;
          lemma_eval_step_monotonic_heap c s1;
          assert (valid_sb_state a s2);
          lemma_invariant_extends_to_all_n a s2 (n-2) cn cfi_loc;
          lemma_for_all_cons f (tl ss);
          lemma_for_all_cons f ss
        )
      )
    )
#pop-options

#push-options "--fuel 1"
let rec lemma_weaken_for_all #t (f1 f2:t -> Tot bool) (l:list t) :
  Lemma
    (requires (
        (forall x. f1 x ==> f2 x) /\
        (for_all f1 l)))
    (ensures (
        (for_all f2 l))) =
  allow_inversion (list t);
  match l with
  | [] -> ()
  | h :: t ->
    lemma_weaken_for_all f1 f2 t
#pop-options

#push-options "--fuel 1"
let rec remove_fn_exits (c_finished:A.t precode) (c_processing:cfg) (i:nat) :
  Err (A.t precode)
    (requires (
        (i == A.length c_finished)))
    (ensures (fun c -> A.length c == A.length c_finished + length c_processing))
    (decreases %[c_processing]) =
  allow_inversion cfg;
  // allow_inversion precode;
  match c_processing with
  | [] -> c_finished
  | hd :: tl ->
    lemma_length_tl hd tl;
    match hd with
    | FnExit _ ->
      let hlt = Ins Unreachable i in
      LP.lemma_snoc_length ((A.to_list c_finished), hlt);
      remove_fn_exits (A.snoc (c_finished, hlt)) tl (i + 1)
    | _ ->
      LP.lemma_snoc_length ((A.to_list c_finished), hd);
      remove_fn_exits (A.snoc (c_finished, hd)) tl (i + 1)
#pop-options

#push-options "--fuel 1 --ifuel 0"
(** Compiles an entire module *)
let compile (mem_sb_size:nat) (mod:module_) (s: erased state) (n:erased nat) :
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
        for_all (fun s1 -> s1.ok = AllOk) ss))) =
  let { module_aux ; module_cfg } = mod in
  let module_cfg = A.to_list (remove_fn_exits A.empty module_cfg 0) in
  let a: aux_info = {
    m_aux = module_aux;
    add_loc = 0;
    mem_sb_size;
    orig_code = module_cfg;
    modified_code = module_cfg;
  } in
  sanity_check_call_tables a; lemma_same_fn_entry_points_reflexive module_cfg;
  pre_process_cfg a A.empty module_cfg (length module_cfg) s;
  lemma_same_fn_entry_points_reflexive module_cfg;
  (* We explicitly [reify] here, rather than let it be handled by the
     [bind] of the [Err] effect, because that does it quite late, and
     we want to be able to split out some of the properties and talk
     about them via lemmas right here instead. This requires forcing
     it into the [PURE] effect, which is done via the reification. *)
  let len_module_cfg = length module_cfg in
  match reify (process_precode a len_module_cfg A.empty module_cfg A.empty s) () with
  | Error' e -> fail_with e
  | Ok' processed_code ->
    let processed_code = A.to_list processed_code in
    lemma_process_precode_state_irrelevance' a len_module_cfg A.empty module_cfg A.empty s;
    lemma_invariant_extends_to_all_n a s n processed_code (length module_cfg);
    lemma_weaken_for_all (fun s1 -> s1.ok = AllOk && safe_callstack s1 (length module_cfg)) (fun s1 -> s1.ok = AllOk) (eval_steps n (fst (unzip processed_code)) s);
    let module_cfg = fst (unzip (processed_code)) in
    ({ module_aux ; module_cfg })
#pop-options

(** An arbitrarily picked initial state that satisfies the required
    interface. Can be made more precise if a stronger interface is
    desired. Since it is arbitrarily picked and no other information
    about the actual state (other than the interface) must be
    visible/accessible, we mark it [irreducible] which instantly makes
    the body inaccessible, even within the same module. *)
irreducible
let init_state_ (mem_sb_size:nat) (mod:module_) :
  Ghost state
    (requires (length mod.module_cfg > 0))
    (ensures (fun s ->
        (s.aux = mod.module_aux) /\
        (s.ok = AllOk) /\
        (forall (addr:nat). addr <= mem_sb_size ==> valid_addr addr s.mem) /\
        (s.ip < length mod.module_cfg) /\
        (safe_callstack s (length mod.module_cfg)))) =
  let open FStar.FunctionalExtensionality in
  let s = {
    ok = AllOk;
    explicitly_safely_killed = false;
    ip = 0;
    stack_pointer = 0;
    reg_i = on _ #nat64 (fun _ -> 0);
    reg_f = on _ #float (fun _ -> 0);
    mem = FStar.Map.const 0;
    stack = { init_rsp = 0; smem = FStar.Map.const 0 };
    callstack = [];
    aux = mod.module_aux;
    global_i = on _ #nat64 (fun _ -> 0);
    global_f = on _ #float (fun _ -> 0);
    global_mem_pages = mod.module_aux.mem_pages;
  } in
  assert_norm (safe_callstack s (length mod.module_cfg));
  s

(* We cannot use [irreducible] in combination with an interface
   directly, which is why we are forced to do this single-level
   indirection. *)
let init_state = init_state_
