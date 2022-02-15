/// WARNING:
/// - See top comment in Wasm.Func.fst
/// - Tables are arrays in the OCaml implementation, but here they are just Maps and do
///   functional update.
/// - We don't care about modelling running out memory to allocate tables.

(**
Representation of an instantiation of a table and of a module.

@summary Table and Module instances.
*)
module Wasm.Instance

open Wasm.Optr
open Wasm.Types

module Ast = Wasm.Ast
module Func = Wasm.Func
module Global = Wasm.Global
module I32 = Wasm.I32
module Memory = Wasm.Memory

private let op_String_Access = Map.sel
private let op_String_Assignment = Map.upd

/// ####################
/// DECLARATIONS
/// ####################
type func_inst = Func.t nat (* Reference to a module_inst by index *)
type memory_inst = Memory.t
type global_inst = Global.t

type tb_size_ = I32.t
type tb_index = I32.t

noeq type module_inst =
{
  types_: list func_type;
  funcs_: list func_inst;
  tables_: list table_inst;
  memories_: list memory_inst;
  globals_: list global_inst;
  exports_: list export_inst;
}

and table_inst = tb_t
and export_inst = Ast.name * extern

and extern =
  | ExternFunc of func_inst
  | ExternTable of table_inst
  | ExternMemory of memory_inst
  | ExternGlobal of global_inst

and tb_elem =
  | Uninitialized
  | FuncElem of func_inst
and tb_table' = Map.t nat tb_elem
and tb_table  =
  {table_content: tb_table'; table_sz: tb_size_; table_max: option tb_size_; elem_type: elem_type}
and tb_t = tb_table

(* Functions from table.ml *)

let e_Bounds = Left "Bounds"
let e_SizeOverflow = Left "SizeOverflow"
let e_SizeLimit = Left "SizeLimit"
let e_Out_of_memory = Left "Out_of_memory"
let __errfail = Left "error"

val tb_alloc: table_type -> Tot (optr tb_table)
val tb_size: tb_table -> Tot tb_size_
val tb_type_of: tb_table -> Tot table_type
val tb_grow: tb_table -> tb_size_ -> Tot (optr tb_table)

val tb_load: tb_table -> tb_index -> Tot (optr tb_elem)
val tb_store: tb_table -> tb_index -> tb_elem -> Tot (optr tb_table)
val tb_blit: tb_table -> tb_index -> list tb_elem -> Tot (optr tb_table)

/// ####################
/// DEFINITIONS
/// ####################
(* Using a map, I could have used a list as well I suppose *)
let within_limits size mx =
  match mx with
  | None -> true
  | Some max -> I32.le_u size max

let create size: tb_table' * tb_size_ = (Map.const Uninitialized), size

let tb_alloc (TableType ({min; max}, elem_type)) =
  if within_limits min max then (
    let tb, sz = create min in
    Right ({table_content = tb; table_sz = sz; table_max = max; elem_type = elem_type})
  ) else
    e_SizeLimit

let tb_size tab = tab.table_sz

let tb_type_of tab =
  let lim = {min = tb_size tab; max = tab.table_max} in
  TableType (lim, tab.elem_type)

let tb_grow tab delta =
  let old_size = tb_size tab in
  let new_size = I32.add old_size delta in
  if I32.gt_u old_size new_size then e_SizeOverflow else (
    if not (within_limits new_size tab.table_max) then e_SizeLimit else (
      Right ({tab with table_sz = new_size})
    )
  )

let tb_load tab i =
  if I32.lt_u i (tb_size tab) then
    Right (tab.table_content.[I32.to_int_u i])
  else
    e_Bounds

let tb_store tab i v =
  if I32.lt_u i (tb_size tab) then
    Right ({tab with table_content = (tab.table_content.[I32.to_int_u i] <- v)})
  else
    e_Bounds

let tb_blit tab offset elems =
  let st = tab.table_content in
  let sz = tb_size tab in
  let l = List.Tot.length elems in
  let rec loop elems (st: tb_table') ptr =
    match elems with
    | [] -> st
    | e :: es -> loop es (st.[ptr] <- e) (ptr + 1)
  in
  if I32.lt_u offset sz && I32.gt_u (I32.sub sz offset) (I32.of_int_u l) then (
    Right ({tab with table_content = loop elems tab.table_content (I32.to_int_u offset)})
  ) else
    e_Bounds

(* Functions from instance.ml *)

let empty_module_inst =
  { types_ = []; funcs_ = []; tables_ = []; memories_ = []; globals_ = []; exports_ = [] }

let extern_type_of ext =
  match ext with
  | ExternFunc func -> ExternFuncType (Func.type_of func)
  | ExternTable tab -> ExternTableType (tb_type_of tab)
  | ExternMemory mem -> ExternMemoryType (Memory.type_of mem)
  | ExternGlobal glob -> ExternGlobalType (Global.type_of glob)

let export (inst:module_inst) (name:list int) : option extern =
  List.assoc name inst.exports_
