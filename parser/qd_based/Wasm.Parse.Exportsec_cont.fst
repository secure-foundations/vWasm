module Wasm.Parse.Exportsec_cont

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

let check_exportsec_cont_bytesize x =
  [@inline_let] let _ = (aux_vecexport_bytesize_eq (x)) in
  let l = aux_vecexport_size32 x in
  0ul `U32.lte` l && l `U32.lte` 16777215ul

type exportsec_cont' = LP.parse_bounded_vldata_strong_t 0 16777215 aux_vecexport_serializer

inline_for_extraction let synth_exportsec_cont (x: exportsec_cont') : Tot exportsec_cont =
  [@inline_let] let _ = (aux_vecexport_bytesize_eq (x)) in x

inline_for_extraction let synth_exportsec_cont_recip (x: exportsec_cont) : Tot exportsec_cont' =
  [@inline_let] let _ = (aux_vecexport_bytesize_eq (x)) in x

noextract let exportsec_cont'_parser : LP.parser _ exportsec_cont' =
  LP.parse_bounded_vldata_strong 0 16777215 aux_vecexport_serializer

let exportsec_cont_parser = LP.parse_synth exportsec_cont'_parser synth_exportsec_cont

noextract let exportsec_cont'_serializer : LP.serializer exportsec_cont'_parser =
  LP.serialize_bounded_vldata_strong 0 16777215 aux_vecexport_serializer

let exportsec_cont_serializer = LP.serialize_synth _ synth_exportsec_cont exportsec_cont'_serializer synth_exportsec_cont_recip ()

let exportsec_cont_bytesize (x:exportsec_cont) : GTot nat = Seq.length (exportsec_cont_serializer x)

let exportsec_cont_bytesize_eq x = ()

inline_for_extraction let exportsec_cont'_parser32 : LS.parser32 exportsec_cont'_parser =
  LS.parse32_bounded_vldata_strong 0 0ul 16777215 16777215ul aux_vecexport_serializer aux_vecexport_parser32

let exportsec_cont_parser32 = LS.parse32_synth' _ synth_exportsec_cont exportsec_cont'_parser32 ()

inline_for_extraction noextract let exportsec_cont'_serializer32 : LS.serializer32 exportsec_cont'_serializer =
  LS.serialize32_bounded_vldata_strong 0 16777215 aux_vecexport_serializer32

let exportsec_cont_serializer32 = LS.serialize32_synth' _ synth_exportsec_cont _ exportsec_cont'_serializer32 synth_exportsec_cont_recip ()

inline_for_extraction noextract let exportsec_cont'_size32 : LS.size32 exportsec_cont'_serializer =
  LS.size32_bounded_vldata_strong 0 16777215 aux_vecexport_size32 3ul

let exportsec_cont_size32 = LS.size32_synth' _ synth_exportsec_cont _ exportsec_cont'_size32 synth_exportsec_cont_recip ()

let exportsec_cont_bytesize_eqn x =
  LP.serialize_synth_eq _ synth_exportsec_cont exportsec_cont'_serializer synth_exportsec_cont_recip () x;
  (aux_vecexport_bytesize_eq (x))

