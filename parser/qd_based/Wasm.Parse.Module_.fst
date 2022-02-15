module Wasm.Parse.Module_

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

type module_' = ((((magic_ & version) & (opt_typesec & opt_importsec)) & ((opt_funcsec & opt_tablesec) & (opt_memsec & opt_globalsec))) & (((opt_exportsec & opt_startsec) & (opt_elemsec & opt_codesec)) & opt_datasec))

inline_for_extraction let synth_module_ (x: module_') : module_ =
  match x with ((((_m,_v),(functype,import)),((typeidx,table),(mem,global))),(((export,start),(elem,code)),data)) -> {
    _m = _m;
    _v = _v;
    functype = functype;
    import = import;
    typeidx = typeidx;
    table = table;
    mem = mem;
    global = global;
    export = export;
    start = start;
    elem = elem;
    code = code;
    data = data;
  }

inline_for_extraction let synth_module__recip (x: module_) : module_' = ((((x._m,x._v),(x.functype,x.import)),((x.typeidx,x.table),(x.mem,x.global))),(((x.export,x.start),(x.elem,x.code)),x.data))

#push-options "--ifuel 3"
let synth_module__recip_inverse () : Lemma (LP.synth_inverse synth_module__recip synth_module_) = ()
#pop-options

let synth_module__injective () : Lemma (LP.synth_injective synth_module_) =
  LP.synth_inverse_synth_injective synth_module__recip synth_module_;
  synth_module__recip_inverse ()

let synth_module__inverse () : Lemma (LP.synth_inverse synth_module_ synth_module__recip) =
  assert_norm (LP.synth_inverse synth_module_ synth_module__recip)

let synth_module__recip_injective () : Lemma (LP.synth_injective synth_module__recip) =
  synth_module__recip_inverse ();
  LP.synth_inverse_synth_injective synth_module_ synth_module__recip

noextract let module_'_parser : LP.parser _ module_' = ((((magic__parser `LP.nondep_then` version_parser) `LP.nondep_then` (opt_typesec_parser `LP.nondep_then` opt_importsec_parser)) `LP.nondep_then` ((opt_funcsec_parser `LP.nondep_then` opt_tablesec_parser) `LP.nondep_then` (opt_memsec_parser `LP.nondep_then` opt_globalsec_parser))) `LP.nondep_then` (((opt_exportsec_parser `LP.nondep_then` opt_startsec_parser) `LP.nondep_then` (opt_elemsec_parser `LP.nondep_then` opt_codesec_parser)) `LP.nondep_then` opt_datasec_parser))

noextract let module_'_parser_kind = LP.get_parser_kind module_'_parser

let module__parser =
  synth_module__injective ();
  assert_norm (module__parser_kind == module_'_parser_kind);
  module_'_parser `LP.parse_synth` synth_module_

noextract let module_'_serializer : LP.serializer module_'_parser = ((((magic__serializer `LP.serialize_nondep_then` version_serializer) `LP.serialize_nondep_then` (opt_typesec_serializer `LP.serialize_nondep_then` opt_importsec_serializer)) `LP.serialize_nondep_then` ((opt_funcsec_serializer `LP.serialize_nondep_then` opt_tablesec_serializer) `LP.serialize_nondep_then` (opt_memsec_serializer `LP.serialize_nondep_then` opt_globalsec_serializer))) `LP.serialize_nondep_then` (((opt_exportsec_serializer `LP.serialize_nondep_then` opt_startsec_serializer) `LP.serialize_nondep_then` (opt_elemsec_serializer `LP.serialize_nondep_then` opt_codesec_serializer)) `LP.serialize_nondep_then` opt_datasec_serializer))

let module__serializer =
  [@inline_let] let _ = synth_module__injective () in
  [@inline_let] let _ = synth_module__inverse () in
  [@inline_let] let _ = assert_norm (module__parser_kind == module_'_parser_kind) in
  LP.serialize_synth _ synth_module_ module_'_serializer synth_module__recip ()

let module__bytesize (x:module_) : GTot nat = Seq.length (module__serializer x)

let module__bytesize_eq x = ()

inline_for_extraction let module_'_parser32 : LS.parser32 module_'_parser = ((((magic__parser32 `LS.parse32_nondep_then` version_parser32) `LS.parse32_nondep_then` (opt_typesec_parser32 `LS.parse32_nondep_then` opt_importsec_parser32)) `LS.parse32_nondep_then` ((opt_funcsec_parser32 `LS.parse32_nondep_then` opt_tablesec_parser32) `LS.parse32_nondep_then` (opt_memsec_parser32 `LS.parse32_nondep_then` opt_globalsec_parser32))) `LS.parse32_nondep_then` (((opt_exportsec_parser32 `LS.parse32_nondep_then` opt_startsec_parser32) `LS.parse32_nondep_then` (opt_elemsec_parser32 `LS.parse32_nondep_then` opt_codesec_parser32)) `LS.parse32_nondep_then` opt_datasec_parser32))

let module__parser32 =
  [@inline_let] let _ = synth_module__injective () in
  [@inline_let] let _ = assert_norm (module__parser_kind == module_'_parser_kind) in
  LS.parse32_synth _ synth_module_ (fun x -> synth_module_ x) module_'_parser32 ()

inline_for_extraction let module_'_serializer32 : LS.serializer32 module_'_serializer = ((((magic__serializer32 `LS.serialize32_nondep_then` version_serializer32) `LS.serialize32_nondep_then` (opt_typesec_serializer32 `LS.serialize32_nondep_then` opt_importsec_serializer32)) `LS.serialize32_nondep_then` ((opt_funcsec_serializer32 `LS.serialize32_nondep_then` opt_tablesec_serializer32) `LS.serialize32_nondep_then` (opt_memsec_serializer32 `LS.serialize32_nondep_then` opt_globalsec_serializer32))) `LS.serialize32_nondep_then` (((opt_exportsec_serializer32 `LS.serialize32_nondep_then` opt_startsec_serializer32) `LS.serialize32_nondep_then` (opt_elemsec_serializer32 `LS.serialize32_nondep_then` opt_codesec_serializer32)) `LS.serialize32_nondep_then` opt_datasec_serializer32))

let module__serializer32 =
  [@inline_let] let _ = synth_module__injective () in
  [@inline_let] let _ = synth_module__inverse () in
  [@inline_let] let _ = assert_norm (module__parser_kind == module_'_parser_kind) in
  LS.serialize32_synth _ synth_module_ _ module_'_serializer32 synth_module__recip (fun x -> synth_module__recip x) ()

inline_for_extraction let module_'_size32 : LS.size32 module_'_serializer = ((((magic__size32 `LS.size32_nondep_then` version_size32) `LS.size32_nondep_then` (opt_typesec_size32 `LS.size32_nondep_then` opt_importsec_size32)) `LS.size32_nondep_then` ((opt_funcsec_size32 `LS.size32_nondep_then` opt_tablesec_size32) `LS.size32_nondep_then` (opt_memsec_size32 `LS.size32_nondep_then` opt_globalsec_size32))) `LS.size32_nondep_then` (((opt_exportsec_size32 `LS.size32_nondep_then` opt_startsec_size32) `LS.size32_nondep_then` (opt_elemsec_size32 `LS.size32_nondep_then` opt_codesec_size32)) `LS.size32_nondep_then` opt_datasec_size32))

let module__size32 =
  [@inline_let] let _ = synth_module__injective () in
  [@inline_let] let _ = synth_module__inverse () in
  [@inline_let] let _ = assert_norm (module__parser_kind == module_'_parser_kind) in
  LS.size32_synth _ synth_module_ _ module_'_size32 synth_module__recip (fun x -> synth_module__recip x) ()

let module__bytesize_eqn x =
  [@inline_let] let _ = synth_module__injective () in
  [@inline_let] let _ = synth_module__inverse () in
  [@inline_let] let _ = assert_norm (module__parser_kind == module_'_parser_kind) in
  LP.serialize_synth_eq _ synth_module_ module_'_serializer synth_module__recip () x;
LP.length_serialize_nondep_then magic__serializer version_serializer x._m x._v;
LP.length_serialize_nondep_then opt_typesec_serializer opt_importsec_serializer x.functype x.import;
LP.length_serialize_nondep_then (magic__serializer `LP.serialize_nondep_then` version_serializer) (opt_typesec_serializer `LP.serialize_nondep_then` opt_importsec_serializer) (x._m, x._v) (x.functype, x.import);
LP.length_serialize_nondep_then opt_funcsec_serializer opt_tablesec_serializer x.typeidx x.table;
LP.length_serialize_nondep_then opt_memsec_serializer opt_globalsec_serializer x.mem x.global;
LP.length_serialize_nondep_then (opt_funcsec_serializer `LP.serialize_nondep_then` opt_tablesec_serializer) (opt_memsec_serializer `LP.serialize_nondep_then` opt_globalsec_serializer) (x.typeidx, x.table) (x.mem, x.global);
LP.length_serialize_nondep_then ((magic__serializer `LP.serialize_nondep_then` version_serializer) `LP.serialize_nondep_then` (opt_typesec_serializer `LP.serialize_nondep_then` opt_importsec_serializer)) ((opt_funcsec_serializer `LP.serialize_nondep_then` opt_tablesec_serializer) `LP.serialize_nondep_then` (opt_memsec_serializer `LP.serialize_nondep_then` opt_globalsec_serializer)) ((x._m, x._v), (x.functype, x.import)) ((x.typeidx, x.table), (x.mem, x.global));
LP.length_serialize_nondep_then opt_exportsec_serializer opt_startsec_serializer x.export x.start;
LP.length_serialize_nondep_then opt_elemsec_serializer opt_codesec_serializer x.elem x.code;
LP.length_serialize_nondep_then (opt_exportsec_serializer `LP.serialize_nondep_then` opt_startsec_serializer) (opt_elemsec_serializer `LP.serialize_nondep_then` opt_codesec_serializer) (x.export, x.start) (x.elem, x.code);
LP.length_serialize_nondep_then ((opt_exportsec_serializer `LP.serialize_nondep_then` opt_startsec_serializer) `LP.serialize_nondep_then` (opt_elemsec_serializer `LP.serialize_nondep_then` opt_codesec_serializer)) opt_datasec_serializer ((x.export, x.start), (x.elem, x.code)) x.data;
LP.length_serialize_nondep_then (((magic__serializer `LP.serialize_nondep_then` version_serializer) `LP.serialize_nondep_then` (opt_typesec_serializer `LP.serialize_nondep_then` opt_importsec_serializer)) `LP.serialize_nondep_then` ((opt_funcsec_serializer `LP.serialize_nondep_then` opt_tablesec_serializer) `LP.serialize_nondep_then` (opt_memsec_serializer `LP.serialize_nondep_then` opt_globalsec_serializer))) (((opt_exportsec_serializer `LP.serialize_nondep_then` opt_startsec_serializer) `LP.serialize_nondep_then` (opt_elemsec_serializer `LP.serialize_nondep_then` opt_codesec_serializer)) `LP.serialize_nondep_then` opt_datasec_serializer) (((x._m, x._v), (x.functype, x.import)), ((x.typeidx, x.table), (x.mem, x.global))) (((x.export, x.start), (x.elem, x.code)), x.data);
  (magic__bytesize_eq (x._m));
  (version_bytesize_eq (x._v));
  (opt_typesec_bytesize_eq (x.functype));
  (opt_importsec_bytesize_eq (x.import));
  (opt_funcsec_bytesize_eq (x.typeidx));
  (opt_tablesec_bytesize_eq (x.table));
  (opt_memsec_bytesize_eq (x.mem));
  (opt_globalsec_bytesize_eq (x.global));
  (opt_exportsec_bytesize_eq (x.export));
  (opt_startsec_bytesize_eq (x.start));
  (opt_elemsec_bytesize_eq (x.elem));
  (opt_codesec_bytesize_eq (x.code));
  (opt_datasec_bytesize_eq (x.data));
  assert(module__bytesize x == Seq.length (LP.serialize magic__serializer x._m) + Seq.length (LP.serialize version_serializer x._v) + Seq.length (LP.serialize opt_typesec_serializer x.functype) + Seq.length (LP.serialize opt_importsec_serializer x.import) + Seq.length (LP.serialize opt_funcsec_serializer x.typeidx) + Seq.length (LP.serialize opt_tablesec_serializer x.table) + Seq.length (LP.serialize opt_memsec_serializer x.mem) + Seq.length (LP.serialize opt_globalsec_serializer x.global) + Seq.length (LP.serialize opt_exportsec_serializer x.export) + Seq.length (LP.serialize opt_startsec_serializer x.start) + Seq.length (LP.serialize opt_elemsec_serializer x.elem) + Seq.length (LP.serialize opt_codesec_serializer x.code) + Seq.length (LP.serialize opt_datasec_serializer x.data))
