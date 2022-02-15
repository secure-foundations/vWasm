module Wasm.Parse.Opt_funcsec

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

friend Wasm.Parse.Optional_tag

// Need high Z3 limits for large sum types
#set-options "--z3rlimit 120"

inline_for_extraction unfold let optional_tag_as_enum_key (x:optional_tag) : Pure (LP.enum_key optional_tag_enum)
  (requires norm [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst optional_tag_enum)) == true) (ensures fun _ -> True) =
  [@inline_let] let _ = norm_spec [delta; zeta; iota; primops] (LP.list_mem x (LP.list_map fst optional_tag_enum)) in x

inline_for_extraction let key_of_opt_funcsec (x:opt_funcsec) : LP.enum_key optional_tag_enum =
  match x with
  | X_absent _ -> optional_tag_as_enum_key Absent
  | X_present _ -> optional_tag_as_enum_key Present

inline_for_extraction let opt_funcsec_case_of_optional_tag (x:optional_tag) : Type0 =
  match x with
  | Absent -> unit
  | Present -> funcsec

unfold inline_for_extraction let to_opt_funcsec_case_of_optional_tag (x:optional_tag) (#x':optional_tag) (y:opt_funcsec_case_of_optional_tag x')  : Pure (norm [delta_only [(`%opt_funcsec_case_of_optional_tag)]; iota] (opt_funcsec_case_of_optional_tag x))
  (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%opt_funcsec_case_of_optional_tag)] ; iota] (opt_funcsec_case_of_optional_tag x) in y

unfold inline_for_extraction let opt_funcsec_refine (k:LP.enum_key optional_tag_enum) (x:opt_funcsec)
  : Pure (LP.refine_with_tag key_of_opt_funcsec k)  (requires norm [delta; iota; zeta] (key_of_opt_funcsec x) == k) (ensures (fun y -> y == x)) =
  [@inline_let] let _ = norm_spec [delta; iota; zeta] (key_of_opt_funcsec x) in x

inline_for_extraction let synth_opt_funcsec_cases (x:LP.enum_key optional_tag_enum) (y:opt_funcsec_case_of_optional_tag x)
  : LP.refine_with_tag key_of_opt_funcsec x =
  match x with
  | Absent -> opt_funcsec_refine x (X_absent (to_opt_funcsec_case_of_optional_tag Absent y))
  | Present -> opt_funcsec_refine x (X_present (to_opt_funcsec_case_of_optional_tag Present y))

unfold inline_for_extraction let from_opt_funcsec_case_of_optional_tag (#x':optional_tag) (x:optional_tag)
  (y: norm [delta_only [(`%opt_funcsec_case_of_optional_tag)]; iota] (opt_funcsec_case_of_optional_tag x))
  : Pure (opt_funcsec_case_of_optional_tag x') (requires (x == x')) (ensures (fun y' -> y' == y)) =
  [@inline_let] let _ = norm_spec [delta_only [(`%opt_funcsec_case_of_optional_tag)] ; iota] (opt_funcsec_case_of_optional_tag x) in y

let synth_opt_funcsec_cases_recip_pre (k:LP.enum_key optional_tag_enum)
  (x:LP.refine_with_tag key_of_opt_funcsec k) : GTot bool =
  match k with
  | Absent -> X_absent? x
  | Present -> X_present? x

let synth_opt_funcsec_cases_recip_pre_intro (k:LP.enum_key optional_tag_enum) (x:LP.refine_with_tag key_of_opt_funcsec k)
  : Lemma (synth_opt_funcsec_cases_recip_pre k x == true) =
  norm_spec [delta; iota] (synth_opt_funcsec_cases_recip_pre k x)

inline_for_extraction let synth_opt_funcsec_cases_recip (k:LP.enum_key optional_tag_enum)
  (x:LP.refine_with_tag key_of_opt_funcsec k) : (opt_funcsec_case_of_optional_tag k) =
  match k with
  | Absent -> [@inline_let] let _ = synth_opt_funcsec_cases_recip_pre_intro Absent x in
    (match x with X_absent y -> (from_opt_funcsec_case_of_optional_tag Absent y))
  | Present -> [@inline_let] let _ = synth_opt_funcsec_cases_recip_pre_intro Present x in
    (match x with X_present y -> (from_opt_funcsec_case_of_optional_tag Present y))

inline_for_extraction let opt_funcsec_sum = LP.make_sum' optional_tag_enum key_of_opt_funcsec
  opt_funcsec_case_of_optional_tag synth_opt_funcsec_cases synth_opt_funcsec_cases_recip
  (_ by (LP.make_sum_synth_case_recip_synth_case_tac ()))
  (_ by (LP.synth_case_synth_case_recip_tac ()))

noextract let parse_opt_funcsec_cases (x:LP.sum_key opt_funcsec_sum)
  : k:LP.parser_kind & LP.parser k (opt_funcsec_case_of_optional_tag x) =
  match x with
  | Absent -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (opt_funcsec_case_of_optional_tag Absent)) = (| _, LP.parse_empty |) in u
  | Present -> [@inline_let] let u : (k: LP.parser_kind & LP.parser k (opt_funcsec_case_of_optional_tag Present)) = (| _, funcsec_parser |) in u
  | _ -> (| _, LP.parse_false |)

noextract let serialize_opt_funcsec_cases (x:LP.sum_key opt_funcsec_sum)
  : LP.serializer (dsnd (parse_opt_funcsec_cases x)) =
  match x with
  | Absent -> [@inline_let] let u : LP.serializer (dsnd (parse_opt_funcsec_cases Absent)) = LP.serialize_empty in u
  | Present -> [@inline_let] let u : LP.serializer (dsnd (parse_opt_funcsec_cases Present)) = funcsec_serializer in u
  | _ -> LP.serialize_false

inline_for_extraction noextract let parse32_opt_funcsec_cases (x:LP.sum_key opt_funcsec_sum)
  : LS.parser32 (dsnd (parse_opt_funcsec_cases x)) =
  match x with
  | Absent -> [@inline_let] let u : LS.parser32 (dsnd (parse_opt_funcsec_cases Absent)) = LS.parse32_empty in u
  | Present -> [@inline_let] let u : LS.parser32 (dsnd (parse_opt_funcsec_cases Present)) = funcsec_parser32 in u
  | _ -> LS.parse32_false

inline_for_extraction noextract let serialize32_opt_funcsec_cases (x:LP.sum_key opt_funcsec_sum)
  : LS.serializer32 (serialize_opt_funcsec_cases x) =
  match x with
  | Absent -> [@inline_let] let u : LS.serializer32 (serialize_opt_funcsec_cases Absent) = LS.serialize32_empty in u
  | Present -> [@inline_let] let u : LS.serializer32 (serialize_opt_funcsec_cases Present) = funcsec_serializer32 in u
  | _ -> LS.serialize32_false

inline_for_extraction noextract let size32_opt_funcsec_cases (x:LP.sum_key opt_funcsec_sum)
  : LS.size32 (serialize_opt_funcsec_cases x) =
  match x with
  | Absent -> [@inline_let] let u : LS.size32 (serialize_opt_funcsec_cases Absent) = LS.size32_empty in u
  | Present -> [@inline_let] let u : LS.size32 (serialize_opt_funcsec_cases Present) = funcsec_size32 in u
  | _ -> LS.size32_false

let opt_funcsec_parser =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);
  LP.parse_sum opt_funcsec_sum optional_tag_repr_parser parse_opt_funcsec_cases

let opt_funcsec_serializer =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);
  LP.serialize_sum opt_funcsec_sum optional_tag_repr_serializer serialize_opt_funcsec_cases

let opt_funcsec_bytesize (x:opt_funcsec) : GTot nat = Seq.length (opt_funcsec_serializer x)

let opt_funcsec_bytesize_eq x = ()

let opt_funcsec_parser32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);
  LS.parse32_sum2 opt_funcsec_sum optional_tag_repr_parser optional_tag_repr_parser32 parse_opt_funcsec_cases parse32_opt_funcsec_cases (_ by (LP.enum_destr_tac optional_tag_enum)) (_ by (LP.maybe_enum_key_of_repr_tac optional_tag_enum))

let opt_funcsec_serializer32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);
  assert_norm (LS.serializer32_sum_gen_precond (LP.get_parser_kind optional_tag_repr_parser) (LP.weaken_parse_cases_kind opt_funcsec_sum parse_opt_funcsec_cases));
  LS.serialize32_sum2 opt_funcsec_sum optional_tag_repr_serializer optional_tag_repr_serializer32 serialize_opt_funcsec_cases serialize32_opt_funcsec_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac optional_tag_enum)) ()

let opt_funcsec_size32 =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);
  assert_norm (LS.size32_sum_gen_precond (LP.get_parser_kind optional_tag_repr_parser) (LP.weaken_parse_cases_kind opt_funcsec_sum parse_opt_funcsec_cases));
  LS.size32_sum2 opt_funcsec_sum optional_tag_repr_serializer optional_tag_repr_size32 serialize_opt_funcsec_cases size32_opt_funcsec_cases (_ by (LP.dep_enum_destr_tac ())) (_ by (LP.enum_repr_of_key_tac optional_tag_enum)) ()

let opt_funcsec_bytesize_eqn_absent x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);

  LP.serialize_sum_eq opt_funcsec_sum optional_tag_repr_serializer serialize_opt_funcsec_cases (X_absent x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ optional_tag_repr_serializer (LP.sum_enum opt_funcsec_sum)) (key_of_opt_funcsec (X_absent x))) in assert (1 <= ln /\ ln <= 1));
  (assert (FStar.Seq.length (LP.serialize LP.serialize_empty (x)) == 0))

let opt_funcsec_bytesize_eqn_present x =
    assert_norm (LP.parse_sum_kind (LP.get_parser_kind optional_tag_repr_parser) opt_funcsec_sum parse_opt_funcsec_cases == opt_funcsec_parser_kind);

  LP.serialize_sum_eq opt_funcsec_sum optional_tag_repr_serializer serialize_opt_funcsec_cases (X_present x);
  (let ln = FStar.Seq.length (LP.serialize (LP.serialize_enum_key _ optional_tag_repr_serializer (LP.sum_enum opt_funcsec_sum)) (key_of_opt_funcsec (X_present x))) in assert (1 <= ln /\ ln <= 1));
  (funcsec_bytesize_eq (x))

