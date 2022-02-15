module Wasm.Parse.Importdesc

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

friend Wasm.Parse.Aux_importdesc_label

// Need high Z3 limits for large sum types
#set-options "--z3rlimit 240"

inline_for_extraction unfold let aux_importdesc_label_as_enum_key (x:aux_importdesc_label) : Pure (LP.enum_key aux_importdesc_label_enum)
  (requires norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst aux_importdesc_label_enum)) == true) (ensures fun _ -> True) =
  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst aux_importdesc_label_enum)) in x

inline_for_extraction let key_of_importdesc (x:importdesc) : LP.enum_key aux_importdesc_label_enum =
  match x with
  | T_func _ -> aux_importdesc_label_as_enum_key Func
  | T_table _ -> aux_importdesc_label_as_enum_key Table
  | T_mem _ -> aux_importdesc_label_as_enum_key Mem
  | T_global _ -> aux_importdesc_label_as_enum_key Global

inline_for_extraction let importdesc_case_of_aux_importdesc_label (x:aux_importdesc_label) : Type0 =
  match x with
  | Func -> typeidx
  | Table -> tabletype
  | Mem -> memtype
  | Global -> globaltype

unfold inline_for_extraction let to_importdesc_case_of_aux_importdesc_label (x:aux_importdesc_label) (#x':aux_importdesc_label) (y:importdesc_case_of_aux_importdesc_label x')  : Pure (norm [delta_only [(`%importdesc_case_of_aux_importdesc_label)]; iota] (importdesc_case_of_aux_importdesc_label x))
  (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%importdesc_case_of_aux_importdesc_label)] ; iota] (importdesc_case_of_aux_importdesc_label x) in y

unfold inline_for_extraction let importdesc_refine (k:LP.enum_key aux_importdesc_label_enum) (x:importdesc)
  : Pure (LP.refine_with_tag key_of_importdesc k)  (requires norm [delta; iota; zeta] (key_of_importdesc x) == k) (ensures (fun y -> y == x)) =
  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_importdesc x) in x

inline_for_extraction let synth_importdesc_cases (x:LP.enum_key aux_importdesc_label_enum) (y:importdesc_case_of_aux_importdesc_label x)
  : LP.refine_with_tag key_of_importdesc x =
  match x with
  | Func -> importdesc_refine x (T_func (to_importdesc_case_of_aux_importdesc_label Func y))
  | Table -> importdesc_refine x (T_table (to_importdesc_case_of_aux_importdesc_label Table y))
  | Mem -> importdesc_refine x (T_mem (to_importdesc_case_of_aux_importdesc_label Mem y))
  | Global -> importdesc_refine x (T_global (to_importdesc_case_of_aux_importdesc_label Global y))

unfold inline_for_extraction let from_importdesc_case_of_aux_importdesc_label (#x':aux_importdesc_label) (x:aux_importdesc_label)
  (y: norm [delta_only [(`%importdesc_case_of_aux_importdesc_label)]; iota] (importdesc_case_of_aux_importdesc_label x))
  : Pure (importdesc_case_of_aux_importdesc_label x') (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%importdesc_case_of_aux_importdesc_label)] ; iota] (importdesc_case_of_aux_importdesc_label x) in y

let synth_importdesc_cases_recip_pre (k:LP.enum_key aux_importdesc_label_enum)
  (x:LP.refine_with_tag key_of_importdesc k) : GTot bool =
  match k with
  | Func -> T_func? x
  | Table -> T_table? x
  | Mem -> T_mem? x
  | Global -> T_global? x

let synth_importdesc_cases_recip_pre_intro (k:LP.enum_key aux_importdesc_label_enum) (x:LP.refine_with_tag key_of_importdesc k)
  : Lemma (synth_importdesc_cases_recip_pre k x == true) =
  norm_spec [delta; iota] (synth_importdesc_cases_recip_pre k x)

inline_for_extraction let synth_importdesc_cases_recip (k:LP.enum_key aux_importdesc_label_enum)
  (x:LP.refine_with_tag key_of_importdesc k) : (importdesc_case_of_aux_importdesc_label k) =
  match k with
  | Func -> [@inline_let] let _ = synth_importdesc_cases_recip_pre_intro Func x in
    (match x with T_func y -> (from_importdesc_case_of_aux_importdesc_label Func y))
  | Table -> [@inline_let] let _ = synth_importdesc_cases_recip_pre_intro Table x in
    (match x with T_table y -> (from_importdesc_case_of_aux_importdesc_label Table y))
  | Mem -> [@inline_let] let _ = synth_importdesc_cases_recip_pre_intro Mem x in
    (match x with T_mem y -> (from_importdesc_case_of_aux_importdesc_label Mem y))
  | Global -> [@inline_let] let _ = synth_importdesc_cases_recip_pre_intro Global x in
    (match x with T_global y -> (from_importdesc_case_of_aux_importdesc_label Global y))

inline_for_extraction let importdesc_sum = LP.make_sum' aux_importdesc_label_enum key_of_importdesc
  importdesc_case_of_aux_importdesc_label synth_importdesc_cases synth_importdesc_cases_recip
  (_ by (LP.make_sum_synth_case_recip_synth_case_tac ()))
  (_ by (LP.synth_case_synth_case_recip_tac ()))

noextract let parse_importdesc_cases (x:LP.sum_key importdesc_sum)
  : k:LP.parser_kind & LP.parser k (importdesc_case_of_aux_importdesc_label x) =
  match x with
  | Func -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (importdesc_case_of_aux_importdesc_label Func)) = (| _, typeidx_parser |) in u
  | Table -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (importdesc_case_of_aux_importdesc_label Table)) = (| _, tabletype_parser |) in u
  | Mem -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (importdesc_case_of_aux_importdesc_label Mem)) = (| _, memtype_parser |) in u
  | Global -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (importdesc_case_of_aux_importdesc_label Global)) = (| _, globaltype_parser |) in u
  | _ -> (| _, LP.parse_false |)

noextract let serialize_importdesc_cases (x:LP.sum_key importdesc_sum)
  : LP.serializer (dsnd (parse_importdesc_cases x)) =
  match x with
  | Func -> [@inline_let] let u : LP.serializer (dsnd (parse_importdesc_cases Func)) = typeidx_serializer in u
  | Table -> [@inline_let] let u : LP.serializer (dsnd (parse_importdesc_cases Table)) = tabletype_serializer in u
  | Mem -> [@inline_let] let u : LP.serializer (dsnd (parse_importdesc_cases Mem)) = memtype_serializer in u
  | Global -> [@inline_let] let u : LP.serializer (dsnd (parse_importdesc_cases Global)) = globaltype_serializer in u
  | _ -> LP.serialize_false

inline_for_extraction noextract let parse32_importdesc_cases (x:LP.sum_key importdesc_sum)
  : LS.parser32 (dsnd (parse_importdesc_cases x)) =
  match x with
  | Func -> [@inline_let] let u : LS.parser32 (dsnd (parse_importdesc_cases Func)) = typeidx_parser32 in u
  | Table -> [@inline_let] let u : LS.parser32 (dsnd (parse_importdesc_cases Table)) = tabletype_parser32 in u
  | Mem -> [@inline_let] let u : LS.parser32 (dsnd (parse_importdesc_cases Mem)) = memtype_parser32 in u
  | Global -> [@inline_let] let u : LS.parser32 (dsnd (parse_importdesc_cases Global)) = globaltype_parser32 in u
  | _ -> LS.parse32_false

inline_for_extraction noextract let serialize32_importdesc_cases (x:LP.sum_key importdesc_sum)
  : LS.serializer32 (serialize_importdesc_cases x) =
  match x with
  | Func -> [@inline_let] let u : LS.serializer32 (serialize_importdesc_cases Func) = typeidx_serializer32 in u
  | Table -> [@inline_let] let u : LS.serializer32 (serialize_importdesc_cases Table) = tabletype_serializer32 in u
  | Mem -> [@inline_let] let u : LS.serializer32 (serialize_importdesc_cases Mem) = memtype_serializer32 in u
  | Global -> [@inline_let] let u : LS.serializer32 (serialize_importdesc_cases Global) = globaltype_serializer32 in u
  | _ -> LS.serialize32_false

inline_for_extraction noextract let size32_importdesc_cases (x:LP.sum_key importdesc_sum)
  : LS.size32 (serialize_importdesc_cases x) =
  match x with
  | Func -> [@inline_let] let u : LS.size32 (serialize_importdesc_cases Func) = typeidx_size32 in u
  | Table -> [@inline_let] let u : LS.size32 (serialize_importdesc_cases Table) = tabletype_size32 in u
  | Mem -> [@inline_let] let u : LS.size32 (serialize_importdesc_cases Mem) = memtype_size32 in u
  | Global -> [@inline_let] let u : LS.size32 (serialize_importdesc_cases Global) = globaltype_size32 in u
  | _ -> LS.size32_false

let importdesc_parser =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);
  LP.parse_sum importdesc_sum aux_importdesc_label_repr_parser parse_importdesc_cases

let importdesc_serializer =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);
  LP.serialize_sum importdesc_sum aux_importdesc_label_repr_serializer serialize_importdesc_cases

let importdesc_bytesize (x:importdesc) : GTot nat = Seq.length (importdesc_serializer x)

let importdesc_bytesize_eq x = ()

let importdesc_parser32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);
  LS.parse32_sum2 importdesc_sum aux_importdesc_label_repr_parser aux_importdesc_label_repr_parser32 parse_importdesc_cases parse32_importdesc_cases (_ by (LP.enum_destr_tac aux_importdesc_label_enum)) (_ by (LP.maybe_enum_key_of_repr_tac aux_importdesc_label_enum))

let importdesc_serializer32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);
  assert_norm (LS.serializer32_sum_gen_precond (LP.get_parser_kind aux_importdesc_label_repr_parser) (LP.weaken_parse_cases_kind importdesc_sum parse_importdesc_cases));
  LS.serialize32_sum2 importdesc_sum aux_importdesc_label_repr_serializer aux_importdesc_label_repr_serializer32 serialize_importdesc_cases serialize32_importdesc_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac aux_importdesc_label_enum)) ()

let importdesc_size32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);
  assert_norm (LS.size32_sum_gen_precond (LP.get_parser_kind aux_importdesc_label_repr_parser) (LP.weaken_parse_cases_kind importdesc_sum parse_importdesc_cases));
  LS.size32_sum2 importdesc_sum aux_importdesc_label_repr_serializer aux_importdesc_label_repr_size32 serialize_importdesc_cases size32_importdesc_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac aux_importdesc_label_enum)) ()

let importdesc_bytesize_eqn_func x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);

  LP.serialize_sum_eq importdesc_sum aux_importdesc_label_repr_serializer serialize_importdesc_cases (T_func x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_importdesc_label_repr_serializer (LP.sum_enum importdesc_sum)) (key_of_importdesc (T_func x))) in assert (1 <= ln /\ ln <= 1));
  (typeidx_bytesize_eq (x))

let importdesc_bytesize_eqn_table x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);

  LP.serialize_sum_eq importdesc_sum aux_importdesc_label_repr_serializer serialize_importdesc_cases (T_table x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_importdesc_label_repr_serializer (LP.sum_enum importdesc_sum)) (key_of_importdesc (T_table x))) in assert (1 <= ln /\ ln <= 1));
  (tabletype_bytesize_eq (x))

let importdesc_bytesize_eqn_mem x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);

  LP.serialize_sum_eq importdesc_sum aux_importdesc_label_repr_serializer serialize_importdesc_cases (T_mem x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_importdesc_label_repr_serializer (LP.sum_enum importdesc_sum)) (key_of_importdesc (T_mem x))) in assert (1 <= ln /\ ln <= 1));
  (memtype_bytesize_eq (x))

let importdesc_bytesize_eqn_global x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind aux_importdesc_label_repr_parser) importdesc_sum parse_importdesc_cases == importdesc_parser_kind);

  LP.serialize_sum_eq importdesc_sum aux_importdesc_label_repr_serializer serialize_importdesc_cases (T_global x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ aux_importdesc_label_repr_serializer (LP.sum_enum importdesc_sum)) (key_of_importdesc (T_global x))) in assert (1 <= ln /\ ln <= 1));
  (globaltype_bytesize_eq (x))
