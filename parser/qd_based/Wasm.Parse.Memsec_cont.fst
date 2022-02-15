module Wasm.Parse.Memsec_cont

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

let check_memsec_cont_bytesize x =
  [@inline_let] let _ = (aux_vecmem_bytesize_eq (x)) in
  let l = aux_vecmem_size32 x in
  0ul `U32.lte` l && l `U32.lte` 16777215ul

type memsec_cont' = LP.parse_bounded_vldata_strong_t 0 16777215 aux_vecmem_serializer

inline_for_extraction let synth_memsec_cont (x: memsec_cont') : Tot memsec_cont =
  [@inline_let] let _ = (aux_vecmem_bytesize_eq (x)) in x

inline_for_extraction let synth_memsec_cont_recip (x: memsec_cont) : Tot memsec_cont' =
  [@inline_let] let _ = (aux_vecmem_bytesize_eq (x)) in x

noextract let memsec_cont'_parser : LP.parser _ memsec_cont' =
  LP.parse_bounded_vldata_strong 0 16777215 aux_vecmem_serializer

let memsec_cont_parser = LP.parse_synth memsec_cont'_parser synth_memsec_cont

noextract let memsec_cont'_serializer : LP.serializer memsec_cont'_parser =
  LP.serialize_bounded_vldata_strong 0 16777215 aux_vecmem_serializer

let memsec_cont_serializer = LP.serialize_synth _ synth_memsec_cont memsec_cont'_serializer synth_memsec_cont_recip ()

let memsec_cont_bytesize (x:memsec_cont) : GTot nat = Seq.length (memsec_cont_serializer x)

let memsec_cont_bytesize_eq x = ()

inline_for_extraction let memsec_cont'_parser32 : LS.parser32 memsec_cont'_parser =
  LS.parse32_bounded_vldata_strong 0 0ul 16777215 16777215ul aux_vecmem_serializer aux_vecmem_parser32

let memsec_cont_parser32 = LS.parse32_synth' _ synth_memsec_cont memsec_cont'_parser32 ()

inline_for_extraction noextract let memsec_cont'_serializer32 : LS.serializer32 memsec_cont'_serializer =
  LS.serialize32_bounded_vldata_strong 0 16777215 aux_vecmem_serializer32

let memsec_cont_serializer32 = LS.serialize32_synth' _ synth_memsec_cont _ memsec_cont'_serializer32 synth_memsec_cont_recip ()

inline_for_extraction noextract let memsec_cont'_size32 : LS.size32 memsec_cont'_serializer =
  LS.size32_bounded_vldata_strong 0 16777215 aux_vecmem_size32 3ul

let memsec_cont_size32 = LS.size32_synth' _ synth_memsec_cont _ memsec_cont'_size32 synth_memsec_cont_recip ()

let memsec_cont_bytesize_eqn x =
  LP.serialize_synth_eq _ synth_memsec_cont memsec_cont'_serializer synth_memsec_cont_recip () x;
  (aux_vecmem_bytesize_eq (x))
