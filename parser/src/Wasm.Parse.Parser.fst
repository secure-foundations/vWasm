module Wasm.Parse.Parser

module Ast = Wasm.Ast
module AT = Wasm.Types
module AM = Wasm.Memory
module AV = Wasm.Values
module AI = Wasm.Ast.IntOp
module AF = Wasm.Ast.FloatOp
module AO = Wasm.Operators
module ASource = Wasm.Source

open FStar.Bytes
open FStar.IO
open FStar.List.Tot

open Wasm.Parse.Aux_br_table
open Wasm.Parse.Aux_call_indirect
open Wasm.Parse.Aux_constbyte0
open Wasm.Parse.Aux_exportdesc_label
open Wasm.Parse.Aux_functype_magic
open Wasm.Parse.Aux_importdesc_label
open Wasm.Parse.Aux_insn_label
open Wasm.Parse.Aux_magic_0
open Wasm.Parse.Aux_magic_1
open Wasm.Parse.Aux_magic_2
open Wasm.Parse.Aux_magic_3
open Wasm.Parse.Aux_max_present
open Wasm.Parse.Aux_min_max
open Wasm.Parse.Aux_only_min
open Wasm.Parse.Aux_vecbyte
open Wasm.Parse.Aux_veccode
open Wasm.Parse.Aux_vecdata
open Wasm.Parse.Aux_vecelem
open Wasm.Parse.Aux_vecexport
open Wasm.Parse.Aux_vecfuncidx
open Wasm.Parse.Aux_vecfunctype
open Wasm.Parse.Aux_vecglobal
open Wasm.Parse.Aux_veclabelidx
open Wasm.Parse.Aux_veclocals
open Wasm.Parse.Aux_vecmem
open Wasm.Parse.Aux_vectable
open Wasm.Parse.Aux_vectypeidx
open Wasm.Parse.Aux_vecvaltype
open Wasm.Parse.Aux_version_0
open Wasm.Parse.Aux_version_1
open Wasm.Parse.Blocktype
open Wasm.Parse.Code
open Wasm.Parse.Codesec
open Wasm.Parse.Data
open Wasm.Parse.Datasec
open Wasm.Parse.Elem
open Wasm.Parse.Elemsec
open Wasm.Parse.Elemtype
open Wasm.Parse.Export
open Wasm.Parse.Exportdesc
open Wasm.Parse.Exportsec
open Wasm.Parse.Expr
open Wasm.Parse.F32
open Wasm.Parse.F64
open Wasm.Parse.Func
open Wasm.Parse.Funcidx
open Wasm.Parse.Funcsec
open Wasm.Parse.Functype
open Wasm.Parse.Global
open Wasm.Parse.Globalidx
open Wasm.Parse.Globalsec
open Wasm.Parse.Globaltype
open Wasm.Parse.I32
open Wasm.Parse.I64
open Wasm.Parse.Import
open Wasm.Parse.Importdesc
open Wasm.Parse.Importsec
open Wasm.Parse.Instr
open Wasm.Parse.Labelidx
open Wasm.Parse.Limits
open Wasm.Parse.Localidx
open Wasm.Parse.Locals
open Wasm.Parse.Magic_
open Wasm.Parse.Mem
open Wasm.Parse.Memarg
open Wasm.Parse.Memidx
open Wasm.Parse.Memsec
open Wasm.Parse.Memtype
open Wasm.Parse.Module_
open Wasm.Parse.Mut
open Wasm.Parse.Name
open Wasm.Parse.Opt_codesec
open Wasm.Parse.Opt_datasec
open Wasm.Parse.Opt_elemsec
open Wasm.Parse.Opt_exportsec
open Wasm.Parse.Opt_funcsec
open Wasm.Parse.Opt_globalsec
open Wasm.Parse.Opt_importsec
open Wasm.Parse.Opt_memsec
open Wasm.Parse.Opt_startsec
open Wasm.Parse.Opt_tablesec
open Wasm.Parse.Opt_typesec
open Wasm.Parse.Optional_tag
open Wasm.Parse.Start
open Wasm.Parse.Startsec
open Wasm.Parse.Table
open Wasm.Parse.Tableidx
open Wasm.Parse.Tablesec
open Wasm.Parse.Tabletype
open Wasm.Parse.Typeidx
open Wasm.Parse.Typesec
open Wasm.Parse.Uint64
open Wasm.Parse.Valtype
open Wasm.Parse.Version

unfold let pow2_32 = 0x100000000
let _ = assert_norm (pow2_32 == pow2 32)

let anon (#a) (x:a) = { ASource.at = ASource.no_region; ASource.it = x }
let convert_value_type (v:valtype) : AT.value_type =
  match v with
  | I32 -> AT.I32Type
  | I64 -> AT.I64Type
  | F32 -> AT.F32Type
  | F64 -> AT.F64Type

let convert_mut_type (m:mut) : AT.mutability =
  match m with
  | Cnst -> AT.Immutable
  | Var ->  AT.Mutable

let convert_global_type (gt:globaltype) : AT.global_type =
  let Mkglobaltype t m = gt in
  let t' = convert_value_type t in
  let m' = convert_mut_type m in
  let gt' = AT.GlobalType (t', m') in
  gt'

let convert_limits32 (l:limits) : AT.limits Wasm.I32.t =
  match l with
  | L_absent min -> { AT.min = min; AT.max = None }
  | L_present m -> { AT.min = m.min; AT.max = Some m.max }

let convert_name (n:name) : Ast.name =
  map (fun (i:FStar.UInt8.t) -> let v:int = FStar.UInt8.v i in v) n

let convert_table_type (t:tabletype) : AT.table_type =
  AT.TableType ((convert_limits32 t.lim), (match t.et with | Funcref -> AT.FuncRefType))

let convert_memory_type (m:memtype) : AT.memory_type =
  AT.MemoryType (convert_limits32 m)

let convert_tables (x:opt_tablesec) : list Ast.table =
  match x with
  | Opt_tablesec.X_absent _ -> []
  | Opt_tablesec.X_present x ->
  map (fun (t:table) -> anon ({Ast.ttype = convert_table_type t})) x.Tablesec.cont

let convert_mem (x:opt_memsec) : list Ast.memory =
  match x with
  | Opt_memsec.X_absent _ -> []
  | Opt_memsec.X_present x ->
  map (fun (m:mem) -> anon ({ Ast.mtype = convert_memory_type m })) x.Memsec.cont

let convert_f32 (f:lbytes 4) : Pure Wasm.F32.t (requires True) (ensures fun _ -> True) =
    let f0:Words_s.nat8 = FStar.UInt8.v (get f 0ul) in
    let f1:Words_s.nat8 = FStar.UInt8.v (get f 1ul) in
    let f2:Words_s.nat8 = FStar.UInt8.v (get f 2ul) in
    let f3:Words_s.nat8 = FStar.UInt8.v (get f 3ul) in
    Wasm.F32.of_bytes [f0; f1; f2; f3]

let convert_f64 (f:lbytes 8) : Pure Wasm.F64.t (requires True) (ensures fun _ -> True) =
    let f0:Words_s.nat8 = FStar.UInt8.v (get f 0ul) in
    let f1:Words_s.nat8 = FStar.UInt8.v (get f 1ul) in
    let f2:Words_s.nat8 = FStar.UInt8.v (get f 2ul) in
    let f3:Words_s.nat8 = FStar.UInt8.v (get f 3ul) in
    let f4:Words_s.nat8 = FStar.UInt8.v (get f 4ul) in
    let f5:Words_s.nat8 = FStar.UInt8.v (get f 5ul) in
    let f6:Words_s.nat8 = FStar.UInt8.v (get f 6ul) in
    let f7:Words_s.nat8 = FStar.UInt8.v (get f 7ul) in
    Wasm.F64.of_bytes [f0; f1; f2; f3; f4; f5; f6; f7]

let convert_block_type (b:blocktype) : AT.stack_type =
  match b with
  | R_none -> []
  | R_i32 -> [AT.I32Type]
  | R_i64 -> [AT.I64Type]
  | R_f32 -> [AT.F32Type]
  | R_f64 -> [AT.F64Type]

let is_ctrl_flow (i:instr) =
  Rest_end_of_contiguous_instructions? i ||
  Rest_block? i ||
  Rest_loop? i ||
  Rest_if_? i

let is_instr_basic (i:instr) = ~(is_ctrl_flow i)

let convert_instr_basic (i:instr{is_instr_basic i}) : Ast.instr' =
  match i with
  | Rest_br i -> Ast.Br (anon i)
  | Rest_br_if i -> Ast.BrIf (anon i)
  | Rest_br_table t -> Ast.BrTable ((map (fun s -> anon s) t.ls), (anon t.ln))
  | Rest_call i -> Ast.Call (anon i)
  | Rest_call_indirect i -> Ast.CallIndirect (anon i.Aux_call_indirect.x)  // TODO: Check x.z is 0?

  | Rest_local_get i -> Ast.LocalGet (anon i)
  | Rest_local_set i -> Ast.LocalSet (anon i)
  | Rest_local_tee i -> Ast.LocalTee (anon i)
  | Rest_global_get i -> Ast.GlobalGet (anon i)
  | Rest_global_set i -> Ast.GlobalSet (anon i)
  | Rest_i32_load m -> AO.i32_load (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load m -> AO.i64_load (FStar.UInt32.v m.align) m.offset
  | Rest_f32_load m -> AO.f32_load (FStar.UInt32.v m.align) m.offset
  | Rest_f64_load m -> AO.f64_load (FStar.UInt32.v m.align) m.offset
  | Rest_i32_load8_s m -> AO.i32_load8_s (FStar.UInt32.v m.align) m.offset
  | Rest_i32_load8_u m -> AO.i32_load8_u (FStar.UInt32.v m.align) m.offset
  | Rest_i32_load16_s m -> AO.i32_load16_s (FStar.UInt32.v m.align) m.offset
  | Rest_i32_load16_u m -> AO.i32_load16_u (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load8_s m -> AO.i64_load8_s (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load8_u m -> AO.i64_load8_u (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load16_s m -> AO.i64_load16_s (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load16_u m -> AO.i64_load16_u (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load32_s m -> AO.i64_load32_s (FStar.UInt32.v m.align) m.offset
  | Rest_i64_load32_u m -> AO.i64_load32_u (FStar.UInt32.v m.align) m.offset
  | Rest_i32_store m -> AO.i32_store (FStar.UInt32.v m.align) m.offset
  | Rest_i64_store m -> AO.i64_store (FStar.UInt32.v m.align) m.offset
  | Rest_f32_store m -> AO.f32_store (FStar.UInt32.v m.align) m.offset
  | Rest_f64_store m -> AO.f64_store (FStar.UInt32.v m.align) m.offset

  | Rest_i32_store8 m -> AO.i32_store8 (FStar.UInt32.v m.align) m.offset
  | Rest_i32_store16 m -> AO.i32_store16 (FStar.UInt32.v m.align) m.offset
  | Rest_i64_store8 m -> AO.i64_store8 (FStar.UInt32.v m.align) m.offset
  | Rest_i64_store16 m -> AO.i64_store16 (FStar.UInt32.v m.align) m.offset

  | Rest_i64_store32 m -> AO.i64_store32 (FStar.UInt32.v m.align) m.offset
  | Rest_memory_size cb0 -> (match cb0 with | Zero -> Ast.MemorySize)
  | Rest_memory_grow cb0 -> (match cb0 with | Zero -> Ast.MemoryGrow)

  | Rest_i32_const i -> Ast.Const (anon (AV.I32 i))
  | Rest_i64_const i -> Ast.Const (anon (AV.I64 i))

  | Rest_f32_const f -> Ast.Const (anon (AV.F32 (convert_f32 f)))
  | Rest_f64_const f -> Ast.Const (anon (AV.F64 (convert_f64 f)))


  | Rest_f64_reinterpret_i64 _ -> Ast.Convert (AV.F64 AF.ReinterpretInt)
  | Rest_f32_reinterpret_i32 _ -> Ast.Convert (AV.F32 AF.ReinterpretInt)
  | Rest_i64_reinterpret_f64 _ -> Ast.Convert (AV.I64 AI.ReinterpretFloat)
  | Rest_i32_reinterpret_f32 _ -> Ast.Convert (AV.I32 AI.ReinterpretFloat)
  | Rest_f64_promote_f32 _ -> Ast.Convert (AV.F64 AF.PromoteF32)
  | Rest_f64_convert_i64_u _ -> Ast.Convert (AV.F64 AF.ConvertUI64)
  | Rest_f64_convert_i64_s _ -> Ast.Convert (AV.F64 AF.ConvertSI64)
  | Rest_f64_convert_i32_u _ -> Ast.Convert (AV.F64 AF.ConvertUI32)
  | Rest_f64_convert_i32_s _ -> Ast.Convert (AV.F64 AF.ConvertSI32)
  | Rest_f32_demote_f64 _ -> Ast.Convert (AV.F32 AF.DemoteF64)
  | Rest_f32_convert_i64_u _ -> Ast.Convert (AV.F32 AF.ConvertUI64)
  | Rest_f32_convert_i64_s _ -> Ast.Convert (AV.F32 AF.ConvertSI64)
  | Rest_f32_convert_i32_u _ -> Ast.Convert (AV.F32 AF.ConvertUI32)
  | Rest_f32_convert_i32_s _ -> Ast.Convert (AV.F32 AF.ConvertSI32)
  | Rest_i64_trunc_f64_u _ -> Ast.Convert (AV.I64 AI.TruncUF64)
  | Rest_i64_trunc_f64_s _ -> Ast.Convert (AV.I64 AI.TruncSF64)
  | Rest_i64_trunc_f32_u _ -> Ast.Convert (AV.I64 AI.TruncUF32)
  | Rest_i64_trunc_f32_s _ -> Ast.Convert (AV.I64 AI.TruncSF32)
  | Rest_i64_extend_i32_u _ -> Ast.Convert (AV.I64 AI.ExtendUI32)
  | Rest_i64_extend_i32_s _ -> Ast.Convert (AV.I64 AI.ExtendSI32)
  | Rest_i32_trunc_f64_u _ -> Ast.Convert (AV.I32 AI.TruncUF64)
  | Rest_i32_trunc_f64_s _ -> Ast.Convert (AV.I32 AI.TruncSF64)
  | Rest_i32_trunc_f32_u _ -> Ast.Convert (AV.I32 AI.TruncUF32)
  | Rest_i32_trunc_f32_s _ -> Ast.Convert (AV.I32 AI.TruncSF32)
  | Rest_i32_wrap_i64 _ -> Ast.Convert (AV.I32 AI.WrapI64)

  | Rest_f64_copysign _ -> Ast.Binary (AV.F64 AF.CopySign)
  | Rest_f64_max _ -> Ast.Binary (AV.F64 AF.Max)
  | Rest_f64_min _ -> Ast.Binary (AV.F64 AF.Min)
  | Rest_f64_div _ -> Ast.Binary (AV.F64 AF.Div)
  | Rest_f64_mul _ -> Ast.Binary (AV.F64 AF.Mul)
  | Rest_f64_sub _ -> Ast.Binary (AV.F64 AF.Sub)
  | Rest_f64_add _ -> Ast.Binary (AV.F64 AF.Add)
  | Rest_f64_sqrt _ -> Ast.Unary (AV.F64 AF.Sqrt)
  | Rest_f64_nearest _ -> Ast.Unary (AV.F64 AF.Nearest)
  | Rest_f64_trunc _ -> Ast.Unary (AV.F64 AF.Trunc)
  | Rest_f64_floor _ -> Ast.Unary (AV.F64 AF.Floor)
  | Rest_f64_ceil _ -> Ast.Unary (AV.F64 AF.Ceil)
  | Rest_f64_neg _ -> Ast.Unary (AV.F64 AF.Neg)
  | Rest_f64_abs _ -> Ast.Unary (AV.F64 AF.Abs)
  | Rest_f32_copysign _ -> Ast.Binary (AV.F32 AF.CopySign)
  | Rest_f32_max _ -> Ast.Binary (AV.F32 AF.Max)
  | Rest_f32_min _ -> Ast.Binary (AV.F32 AF.Min)
  | Rest_f32_div _ -> Ast.Binary (AV.F32 AF.Div)
  | Rest_f32_mul _ -> Ast.Binary (AV.F32 AF.Mul)
  | Rest_f32_sub _ -> Ast.Binary (AV.F32 AF.Sub)
  | Rest_f32_add _ -> Ast.Binary (AV.F32 AF.Add)
  | Rest_f32_sqrt _ -> Ast.Unary (AV.F32 AF.Sqrt)
  | Rest_f32_nearest _ -> Ast.Unary (AV.F32 AF.Nearest)
  | Rest_f32_trunc _ -> Ast.Unary (AV.F32 AF.Trunc)
  | Rest_f32_floor _ -> Ast.Unary (AV.F32 AF.Floor)
  | Rest_f32_ceil _ -> Ast.Unary (AV.F32 AF.Ceil)
  | Rest_f32_neg _ -> Ast.Unary (AV.F32 AF.Neg)
  | Rest_f32_abs _ -> Ast.Unary (AV.F32 AF.Abs)
  | Rest_i64_rotr _ -> Ast.Binary (AV.I64 AI.Rotr)
  | Rest_i64_rotl _ -> Ast.Binary (AV.I64 AI.Rotl)
  | Rest_i64_shr_u _ -> Ast.Binary (AV.I64 AI.ShrU)
  | Rest_i64_shr_s _ -> Ast.Binary (AV.I64 AI.ShrS)
  | Rest_i64_shl _ -> Ast.Binary (AV.I64 AI.Shl)
  | Rest_i64_xor _ -> Ast.Binary (AV.I64 AI.Xor)
  | Rest_i64_or _ -> Ast.Binary (AV.I64 AI.Or)
  | Rest_i64_and _ -> Ast.Binary (AV.I64 AI.And)
  | Rest_i64_rem_u _ -> Ast.Binary (AV.I64 AI.RemU)
  | Rest_i64_rem_s _ -> Ast.Binary (AV.I64 AI.RemS)
  | Rest_i64_div_u _ -> Ast.Binary (AV.I64 AI.DivU)
  | Rest_i64_div_s _ -> Ast.Binary (AV.I64 AI.DivS)
  | Rest_i64_mul _ -> Ast.Binary (AV.I64 AI.Mul)
  | Rest_i64_sub _ -> Ast.Binary (AV.I64 AI.Sub)
  | Rest_i64_add _ -> Ast.Binary (AV.I64 AI.Add)
  | Rest_i64_popcnt _ -> Ast.Unary (AV.I64 AI.Popcnt)
  | Rest_i64_ctz _ -> Ast.Unary (AV.I64 AI.Ctz)
  | Rest_i64_clz _ -> Ast.Unary (AV.I64 AI.Clz)
  | Rest_i32_rotr _ -> Ast.Binary (AV.I32 AI.Rotr)
  | Rest_i32_rotl _ -> Ast.Binary (AV.I32 AI.Rotl)
  | Rest_i32_shr_u _ -> Ast.Binary (AV.I32 AI.ShrU)
  | Rest_i32_shr_s _ -> Ast.Binary (AV.I32 AI.ShrS)
  | Rest_i32_shl _ -> Ast.Binary (AV.I32 AI.Shl)
  | Rest_i32_xor _ -> Ast.Binary (AV.I32 AI.Xor)
  | Rest_i32_or _ -> Ast.Binary (AV.I32 AI.Or)
  | Rest_i32_and _ -> Ast.Binary (AV.I32 AI.And)
  | Rest_i32_rem_u _ -> Ast.Binary (AV.I32 AI.RemU)
  | Rest_i32_rem_s _ -> Ast.Binary (AV.I32 AI.RemS)
  | Rest_i32_div_u _ -> Ast.Binary (AV.I32 AI.DivU)
  | Rest_i32_div_s _ -> Ast.Binary (AV.I32 AI.DivS)
  | Rest_i32_mul _ -> Ast.Binary (AV.I32 AI.Mul)
  | Rest_i32_sub _ -> Ast.Binary (AV.I32 AI.Sub)
  | Rest_i32_add _ -> Ast.Binary (AV.I32 AI.Add)
  | Rest_i32_popcnt _ -> Ast.Unary (AV.I32 AI.Popcnt)
  | Rest_i32_ctz _ -> Ast.Unary (AV.I32 AI.Ctz)
  | Rest_i32_clz _ -> Ast.Unary (AV.I32 AI.Clz)
  | Rest_f64_ge _ -> Ast.Compare (AV.F64 AF.Ge)
  | Rest_f64_le _ -> Ast.Compare (AV.F64 AF.Le)
  | Rest_f64_gt _ -> Ast.Compare (AV.F64 AF.Gt)
  | Rest_f64_lt _ -> Ast.Compare (AV.F64 AF.Lt)
  | Rest_f64_ne _ -> Ast.Compare (AV.F64 AF.Ne)
  | Rest_f64_eq _ -> Ast.Compare (AV.F64 AF.Eq)
  | Rest_f32_ge _ -> Ast.Compare (AV.F32 AF.Ge)
  | Rest_f32_le _ -> Ast.Compare (AV.F32 AF.Le)
  | Rest_f32_gt _ -> Ast.Compare (AV.F32 AF.Gt)
  | Rest_f32_lt _ -> Ast.Compare (AV.F32 AF.Lt)
  | Rest_f32_ne _ -> Ast.Compare (AV.F32 AF.Ne)
  | Rest_f32_eq _ -> Ast.Compare (AV.F32 AF.Eq)
  | Rest_i64_ge_u _ -> Ast.Compare (AV.I64 AI.GeU)
  | Rest_i64_ge_s _ -> Ast.Compare (AV.I64 AI.GeS)
  | Rest_i64_le_u _ -> Ast.Compare (AV.I64 AI.LeU)
  | Rest_i64_le_s _ -> Ast.Compare (AV.I64 AI.LeS)
  | Rest_i64_gt_u _ -> Ast.Compare (AV.I64 AI.GtU)
  | Rest_i64_gt_s _ -> Ast.Compare (AV.I64 AI.GtS)
  | Rest_i64_lt_u _ -> Ast.Compare (AV.I64 AI.LtU)
  | Rest_i64_lt_s _ -> Ast.Compare (AV.I64 AI.LtS)
  | Rest_i64_ne _ -> Ast.Compare (AV.I64 AI.Ne)
  | Rest_i64_eq _ -> Ast.Compare (AV.I64 AI.Eq)
  | Rest_i64_eqz _ -> Ast.Test (AV.I64 AI.Eqz)
  | Rest_i32_ge_u _ -> Ast.Compare (AV.I32 AI.GeU)
  | Rest_i32_ge_s _ -> Ast.Compare (AV.I32 AI.GeS)
  | Rest_i32_le_u _ -> Ast.Compare (AV.I32 AI.LeU)
  | Rest_i32_le_s _ -> Ast.Compare (AV.I32 AI.LeS)
  | Rest_i32_gt_u _ -> Ast.Compare (AV.I32 AI.GtU)
  | Rest_i32_gt_s _ -> Ast.Compare (AV.I32 AI.GtS)
  | Rest_i32_lt_u _ -> Ast.Compare (AV.I32 AI.LtU)
  | Rest_i32_lt_s _ -> Ast.Compare (AV.I32 AI.LtS)
  | Rest_i32_ne _ -> Ast.Compare (AV.I32 AI.Ne)
  | Rest_i32_eq _ -> Ast.Compare (AV.I32 AI.Eq)
  | Rest_i32_eqz _ -> Ast.Test (AV.I32 AI.Eqz)
  | Rest_select_ _ -> Ast.Select
  | Rest_drop _ -> Ast.Drop
  | Rest_ret _ -> Ast.Return
  | Rest_nop _ -> Ast.Nop
  | Rest_unreachable _ -> Ast.Unreachable

type end_block =
  | Delimited of list Ast.instr
  | Empty of list Ast.instr
  | Err

let rec convert_instrs' (accum:list Ast.instr) (instrs:list instr)
  : Tot (end_block *
         r:(list instr){ length r <= length instrs })
        (decreases %[length instrs]) =
  match instrs with
  | [] -> Empty accum, []
  | i :: tl ->
    match i with
    | Rest_end_of_contiguous_instructions _ -> Delimited accum, tl
    | _ ->
      let i',rest =
      match i with
      | Rest_block bt ->
        let t = convert_block_type bt in
        let (block_instrs, rest) = convert_instrs' [] tl in
        (match block_instrs with
         | Delimited b -> Some (anon (Ast.Block (t, b))), rest
         | _ -> None, rest)
      | Rest_loop bt ->
        let t = convert_block_type bt in
        let (block_instrs, rest) = convert_instrs' [] tl in
        (match block_instrs with
         | Delimited b -> Some (anon (Ast.Loop (t, b))), rest
         | _ -> None, rest)
      | Rest_if_ bt ->
        let if_t = convert_block_type bt in
        let block_instrs_true, rest = convert_instrs' [] tl in
        let block_instrs_false, rest = convert_instrs' [] rest in
        (match block_instrs_true, block_instrs_false with
         | Delimited t, Delimited f ->
           Some (anon (Ast.If (if_t, t, f))), rest
         | _ -> None, rest)
      | _ ->
        let i_basic = convert_instr_basic i in
        Some (anon i_basic), tl
      in
      match i' with
      | Some v ->
        let a'', r'' = convert_instrs' (append accum [v]) rest in
        a'', r''
      | None -> Err, rest

open FStar.All
let convert_instructions (x:list instr) : ML (list Ast.instr) =
  let a, r = convert_instrs' [] x in
  match a with
  | Empty instrs -> instrs
  | _ -> print_string "The instructions were not properly delimited!";
        FStar.All.exit 1

let convert_global (g:Wasm.Parse.Global.global) : ML Ast.global =
  let Mkglobal gt e = g in
  let Mkglobaltype t m = gt in
  let gt' = convert_global_type gt in
  let e' = anon (convert_instructions e) in
  let g' = { Ast.gtype = gt'; Ast.value = e' } in
  anon g'

let convert_globals (x: opt_globalsec) : ML (list Ast.global) =
  match x with
  | Opt_globalsec.X_absent _ -> []
  | Opt_globalsec.X_present x ->
  FStar.List.map convert_global x.Globalsec.cont

let convert_exports (x:opt_exportsec) : list Ast.export =
  match x with
  | Opt_exportsec.X_absent _ -> []
  | Opt_exportsec.X_present x ->
  map (fun (e:export) ->
       let d = match e.Export.d with
               | X_func i ->   Ast.FuncExport (anon i)
               | X_table i ->  Ast.TableExport (anon i)
               | X_mem i ->    Ast.MemoryExport (anon i)
               | X_global i -> Ast.GlobalExport (anon i)
       in
       anon ({ Ast.name = convert_name e.Export.nm; Ast.edesc = anon d }))
      x.Exportsec.cont

let convert_import (i:import) : Ast.import =
    anon (let d:Ast.import_desc' = match i.d with
                  | T_func i   -> Ast.FuncImport (anon i)
                  | T_table t  -> Ast.TableImport (convert_table_type t)
                  | T_mem m    -> Ast.MemoryImport (convert_memory_type m)
                  | T_global g -> Ast.GlobalImport (convert_global_type g)
          in
          {Ast.module_name = convert_name i.modu;
           Ast.item_name = convert_name i.nm;
           Ast.idesc = anon d})

let convert_imports (x:opt_importsec) : list Ast.import =
  match x with
  | Opt_importsec.X_absent _ -> []
  | Opt_importsec.X_present x ->
  map convert_import x.Importsec.cont

let convert_start (x:opt_startsec) : option Ast.var =
  match x with
  | Opt_startsec.X_absent _ -> None
  | Opt_startsec.X_present x ->
    Some (anon x.Startsec.cont)

let convert_elem (e:elem) : ML (Ast.segment (list Ast.var)) =
  anon ({ Ast.index = anon e.x;
          Ast.seg_offset = anon (convert_instructions e.Elem.e);
          Ast.init = map (fun fi -> anon fi) e.y})

let convert_elems (x:opt_elemsec) : ML (list (Ast.segment (list Ast.var))) =
  match x with
  | Opt_elemsec.X_absent _ -> []
  | Opt_elemsec.X_present x ->
  FStar.List.map convert_elem x.Elemsec.cont

let convert_datum (d:data) : ML (Ast.segment (list Words_s.nat8)) =
  anon ({ Ast.index = anon d.Data.x;
          Ast.seg_offset = anon (convert_instructions d.Data.e);
          Ast.init = map (fun i -> let v:Words_s.nat8 = FStar.UInt8.v i in v) d.b})

let convert_data (x:opt_datasec) : ML (list (Ast.segment (list Words_s.nat8))) =
  match x with
  | Opt_datasec.X_absent _ -> []
  | Opt_datasec.X_present x ->
  FStar.List.map convert_datum x.Datasec.cont

let convert_types (x:opt_typesec) : list Ast.type_  =
  match x with
  | X_absent _ -> []
  | X_present x ->
  map (fun (f:functype) ->
         anon (AT.FuncType (map convert_value_type f.params, map convert_value_type f.results))
      ) x.Typesec.cont

let rec repeat (#a) (v:a) (n:nat) : list a =
  if n = 0 then []
  else v :: repeat v (n-1)

let rec convert_locals (l:list locals) : list AT.value_type =
  match l with
  | [] -> []
  | hd :: tl -> append (repeat (convert_value_type hd.t) (FStar.UInt32.v hd.Locals.n)) (convert_locals tl)

let convert_code (c:typeidx * code) : ML (Ast.func) =
  let f, c = c in
  anon ({ Ast.ftype = (anon f);
          Ast.flocals = convert_locals c.Code.code_.Func.t;
          Ast.body = convert_instructions c.Code.code_.Func.e})

let convert_codes (fs:opt_funcsec) (cs:opt_codesec) : ML (list (Ast.func)) =
  match fs,cs with
  | Opt_funcsec.X_absent _,   Opt_codesec.X_absent _ -> []
  | Opt_funcsec.X_present fs, Opt_codesec.X_present cs ->
    let fs = fs.Funcsec.cont in
    let cs = cs.Codesec.cont in
    if length fs = length cs then (
       let fcs = FStar.List.zip fs cs in
       FStar.List.map convert_code fcs
    ) else (
      print_string "Expected funcsec and codesec to have the same length!";
      exit 2
    )
  | _ ->
    print_string "Expected funcsec and codesec to both be present or both be absent!";
    exit 4

let convert_module (m:module_) : ML Ast.module_ =
  anon ({
    Ast.types    = convert_types   m.functype;
    Ast.globals  = convert_globals m.global;
    Ast.tables   = convert_tables  m.table;
    Ast.memories = convert_mem     m.mem;
    Ast.funcs    = convert_codes   m.typeidx m.code;
    Ast.start    = convert_start   m.start;
    Ast.elems    = convert_elems   m.elem;
    Ast.data     = convert_data    m.data;
    Ast.imports  = convert_imports m.import;
    Ast.exports  = convert_exports m.export
    })

let parse (b:bytes) =
  match module__parser32 b with
  | Some (m, n) -> convert_module m
  | None -> print_string "Failed to parse the bytes!";
           exit 3
