module Wasm.Parse.Exportdesc

(* This file has been automatically generated by EverParse. *)
open FStar.Bytes
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module LP = LowParse.Spec
module LS = LowParse.SLow
module LPI = LowParse.Spec.AllIntegers
module L = FStar.List.Tot
module BY = FStar.Bytes

#reset-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --z3rlimit 16 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 2"

friend Wasm.Parse.Aux_exportdesc_label

// Need high Z3 limits for large sum types
#set-options "--z3rlimit 240"

inline_for_extraction unfold let aux_exportdesc_label_as_enum_key (x:aux_exportdesc_label) : Pure (LP.enum_key aux_exportdesc_label_enum)
  (requires norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst aux_exportdesc_label_enum)) == true) (ensures fun _ -> True) =
  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst aux_exportdesc_label_enum)) in x

inline_for_extraction let key_of_exportdesc (x:exportdesc) : LP.enum_key aux_exportdesc_label_enum =
  match x with
  | X_func _ -> aux_exportdesc_label_as_enum_key Func
  | X_table _ -> aux_exportdesc_label_as_enum_key Table
  | X_mem _ -> aux_exportdesc_label_as_enum_key Mem
  | X_global _ -> aux_exportdesc_label_as_enum_key Global

inline_for_extraction let exportdesc_case_of_aux_exportdesc_label (x:aux_exportdesc_label) : Type0 =
  match x with
  | Func -> funcidx
  | Table -> tableidx
  | Mem -> memidx
  | Global -> globalidx

unfold inline_for_extraction let to_exportdesc_case_of_aux_exportdesc_label (x:aux_exportdesc_label) (#x':aux_exportdesc_label) (y:exportdesc_case_of_aux_exportdesc_label x')  : Pure (norm [delta_only [(`%exportdesc_case_of_aux_exportdesc_label)]; iota] (exportdesc_case_of_aux_exportdesc_label x))
  (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%exportdesc_case_of_aux_exportdesc_label)] ; iota] (exportdesc_case_of_aux_exportdesc_label x) in y

unfold inline_for_extraction let exportdesc_refine (k:LP.enum_key aux_exportdesc_label_enum) (x:exportdesc)
  : Pure (LP.refine_with_tag key_of_exportdesc k)  (requires norm [delta; iota; zeta] (key_of_exportdesc x) == k) (ensures (fun y -> y == x)) =
  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_exportdesc x) in x

inline_for_extraction let synth_exportdesc_cases (x:LP.enum_key aux_exportdesc_label_enum) (y:exportdesc_case_of_aux_exportdesc_label x)
  : LP.refine_with_tag key_of_exportdesc x =
  match x with
  | Func -> exportdesc_refine x (X_func (to_exportdesc_case_of_aux_exportdesc_label Func y))
  | Table -> exportdesc_refine x (X_table (to_exportdesc_case_of_aux_exportdesc_label Table y))
  | Mem -> exportdesc_refine x (X_mem (to_exportdesc_case_of_aux_exportdesc_label Mem y))
  | Global -> exportdesc_refine x (X_global (to_exportdesc_case_of_aux_exportdesc_label Global y))

unfold inline_for_extraction let from_exportdesc_case_of_aux_exportdesc_label (#x':aux_exportdesc_label) (x:aux_exportdesc_label)
  (y: norm [delta_only [(`%exportdesc_case_of_aux_exportdesc_label)]; iota] (exportdesc_case_of_aux_exportdesc_label x))
  : Pure (exportdesc_case_of_aux_exportdesc_label x') (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%exportdesc_case_of_aux_exportdesc_label)] ; iota] (exportdesc_case_of_aux_exportdesc_label x) in y

let synth_exportdesc_cases_recip_pre (k:LP.enum_key aux_exportdesc_label_enum)
  (x:LP.refine_with_tag key_of_exportdesc k) : GTot bool =
  match k with
  | Func -> X_func? x
  | Table -> X_table? x
  | Mem -> X_mem? x
  | Global -> X_global? x

let synth_exportdesc_cases_recip_pre_intro (k:LP.enum_key aux_exportdesc_label_enum) (x:LP.refine_with_tag key_of_exportdesc k)
  : Lemma (synth_exportdesc_cases_recip_pre k x == true) =
  norm_spec [delta; iota] (synth_exportdesc_cases_recip_pre k x)

inline_for_extraction let synth_exportdesc_cases_recip (k:LP.enum_key aux_exportdesc_label_enum)
  (x:LP.refine_with_tag key_of_exportdesc k) : (exportdesc_case_of_aux_exportdesc_label k) =
  match k with
  | Func -> [@inline_let] let _ = synth_exportdesc_cases_recip_pre_intro Func x in
    (match x with X_func y -> (from_exportdesc_case_of_aux_exportdesc_label Func y))
  | Table -> [@inline_let] let _ = synth_exportdesc_cases_recip_pre_intro Table x in
    (match x with X_table y -> (from_exportdesc_case_of_aux_exportdesc_label Table y))
  | Mem -> [@inline_let] let _ = synth_exportdesc_cases_recip_pre_intro Mem x in
    (match x with X_mem y -> (from_exportdesc_case_of_aux_exportdesc_label Mem y))
  | Global -> [@inline_let] let _ = synth_exportdesc_cases_recip_pre_intro Global x in
    (match x with X_global y -> (from_exportdesc_case_of_aux_exportdesc_label Global y))

inline_for_extraction let exportdesc_sum = LP.make_sum' aux_exportdesc_label_enum key_of_exportdesc
  exportdesc_case_of_aux_exportdesc_label synth_exportdesc_cases synth_exportdesc_cases_recip
  (_ by (LP.make_sum_synth_case_recip_synth_case_tac ()))
  (_ by (LP.synth_case_synth_case_recip_tac ()))

noextract let parse_exportdesc_cases (x:LP.sum_key exportdesc_sum)
  : k:LP.parser_kind & LP.parser k (exportdesc_case_of_aux_exportdesc_label x) =
  match x with
  | Func -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (exportdesc_case_of_aux_exportdesc_label Func)) = (| _, funcidx_parser |) in u
  | Table -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (exportdesc_case_of_aux_exportdesc_label Table)) = (| _, tableidx_parser |) in u
  | Mem -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (exportdesc_case_of_aux_exportdesc_label Mem)) = (| _, memidx_parser |) in u
  | Global -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (exportdesc_case_of_aux_exportdesc_label Global)) = (| _, globalidx_parser |) in u
  | _ -> (| _, LP.parse_false |)

noextract let serialize_exportdesc_cases (x:LP.sum_key exportdesc_sum)
  : LP.serializer (dsnd (parse_exportdesc_cases x)) =
  match x with
  | Func -> [@inline_let] let u : LP.serializer (dsnd (parse_exportdesc_cases Func)) = funcidx_serializer in u
  | Table -> [@inline_let] let u : LP.serializer (dsnd (parse_exportdesc_cases Table)) = tableidx_serializer in u
  | Mem -> [@inline_let] let u : LP.serializer (dsnd (parse_exportdesc_cases Mem)) = memidx_serializer in u
  | Global -> [@inline_let] let u : LP.serializer (dsnd (parse_exportdesc_cases Global)) = globalidx_serializer in u
  | _ -> LP.serialize_false

inline_for_extraction noextract let parse32_exportdesc_cases (x:LP.sum_key exportdesc_sum)
  : LS.parser32 (dsnd (parse_exportdesc_cases x)) =
  match x with
  | Func -> [@inline_let] let u : LS.parser32 (dsnd (parse_exportdesc_cases Func)) = funcidx_parser32 in u
  | Table -> [@inline_let] let u : LS.parser32 (dsnd (parse_exportdesc_cases Table)) = tableidx_parser32 in u
  | Mem -> [@inline_let] let u : LS.parser32 (dsnd (parse_exportdesc_cases Mem)) = memidx_parser32 in u
  | Global -> [@inline_let] let u : LS.parser32 (dsnd (parse_exportdesc_cases Global)) = globalidx_parser32 in u
  | _ -> LS.parse32_false

inline_for_extraction noextract let serialize32_exportdesc_cases (x:LP.sum_key exportdesc_sum)
  : LS.serializer32 (serialize_exportdesc_cases x) =
  match x with
  | Func -> [@inline_let] let u : LS.serializer32 (serialize_exportdesc_cases Func) = funcidx_serializer32 in u
  | Table -> [@inline_let] let u : LS.serializer32 (serialize_exportdesc_cases Table) = tableidx_serializer32 in u
  | Mem -> [@inline_let] let u : LS.serializer32 (serialize_exportdesc_cases Mem) = memidx_serializer32 in u
  | Global -> [@inline_let] let u : LS.serializer32 (serialize_exportdesc_cases Global) = globalidx_serializer32 in u
  | _ -> LS.serialize32_false

inline_for_extraction noextract let size32_exportdesc_cases (x:LP.sum_key exportdesc_sum)
  : LS.size32 (serialize_exportdesc_cases x) =
  match x with
  | Func -> [@inline_let] let u : LS.size32 (serialize_exportdesc_cases Func) = funcidx_size32 in u
  | Table -> [@inline_let] let u : LS.size32 (serialize_exportdesc_cases Table) = tableidx_size32 in u
  | Mem -> [@inline_let] let u : LS.size32 (serialize_exportdesc_cases Mem) = memidx_size32 in u
  | Global -> [@inline_let] let u : LS.size32 (serialize_exportdesc_cases Global) = globalidx_size32 in u
  | _ -> LS.size32_false

let exportdesc_parser =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);
  LP.parse_sum exportdesc_sum aux_exportdesc_label_repr_parser parse_exportdesc_cases

let exportdesc_serializer =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);
  LP.serialize_sum exportdesc_sum aux_exportdesc_label_repr_serializer serialize_exportdesc_cases

let exportdesc_bytesize (x:exportdesc) : GTot nat = Seq.length (exportdesc_serializer x)

let exportdesc_bytesize_eq x = ()

let exportdesc_parser32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);
  LS.parse32_sum2 exportdesc_sum aux_exportdesc_label_repr_parser aux_exportdesc_label_repr_parser32 parse_exportdesc_cases parse32_exportdesc_cases (_ by (LP.enum_destr_tac aux_exportdesc_label_enum)) (_ by (LP.maybe_enum_key_of_repr_tac aux_exportdesc_label_enum))

let exportdesc_serializer32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);
  assert_norm (LS.serializer32_sum_gen_precond (LP.get_parser_kind aux_exportdesc_label_repr_parser) (LP.weaken_parse_cases_kind exportdesc_sum parse_exportdesc_cases));
  LS.serialize32_sum2 exportdesc_sum aux_exportdesc_label_repr_serializer aux_exportdesc_label_repr_serializer32 serialize_exportdesc_cases serialize32_exportdesc_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac aux_exportdesc_label_enum)) ()

let exportdesc_size32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);
  assert_norm (LS.size32_sum_gen_precond (LP.get_parser_kind aux_exportdesc_label_repr_parser) (LP.weaken_parse_cases_kind exportdesc_sum parse_exportdesc_cases));
  LS.size32_sum2 exportdesc_sum aux_exportdesc_label_repr_serializer aux_exportdesc_label_repr_size32 serialize_exportdesc_cases size32_exportdesc_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac aux_exportdesc_label_enum)) ()

let exportdesc_bytesize_eqn_func x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);

  LP.serialize_sum_eq exportdesc_sum aux_exportdesc_label_repr_serializer serialize_exportdesc_cases (X_func x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_exportdesc_label_repr_serializer (LP.sum_enum exportdesc_sum)) (key_of_exportdesc (X_func x))) in assert (1 <= ln /\ ln <= 1));
  (funcidx_bytesize_eq (x))

let exportdesc_bytesize_eqn_table x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);

  LP.serialize_sum_eq exportdesc_sum aux_exportdesc_label_repr_serializer serialize_exportdesc_cases (X_table x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_exportdesc_label_repr_serializer (LP.sum_enum exportdesc_sum)) (key_of_exportdesc (X_table x))) in assert (1 <= ln /\ ln <= 1));
  (tableidx_bytesize_eq (x))

let exportdesc_bytesize_eqn_mem x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);

  LP.serialize_sum_eq exportdesc_sum aux_exportdesc_label_repr_serializer serialize_exportdesc_cases (X_mem x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_exportdesc_label_repr_serializer (LP.sum_enum exportdesc_sum)) (key_of_exportdesc (X_mem x))) in assert (1 <= ln /\ ln <= 1));
  (memidx_bytesize_eq (x))

let exportdesc_bytesize_eqn_global x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_exportdesc_label_repr_parser) exportdesc_sum parse_exportdesc_cases == exportdesc_parser_kind);

  LP.serialize_sum_eq exportdesc_sum aux_exportdesc_label_repr_serializer serialize_exportdesc_cases (X_global x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_exportdesc_label_repr_serializer (LP.sum_enum exportdesc_sum)) (key_of_exportdesc (X_global x))) in assert (1 <= ln /\ ln <= 1));
  (globalidx_bytesize_eq (x))

