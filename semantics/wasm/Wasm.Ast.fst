(**
Defines the core structures of the wasm AST, and some helper functions
for getting types.

@summary AST
*)
module Wasm.Ast

(*
 * Throughout the implementation we use consistent naming conventions for
 * syntactic elements, associated with the types defined here and in a few
 * other places:
 *
 *   x : var
 *   v : value
 *   e : instrr
 *   f : func
 *   m : module_
 *
 *   t : value_type
 *   s : func_type
 *   c : context / config
 *
 * These conventions mostly follow standard practice in language semantics.
 *)

open Wasm.Optr

open Wasm.Source
open Wasm.Types
open Wasm.I32

open Words_s

module Values = Wasm.Values
module Memory = Wasm.Memory
module Source = Wasm.Source
module L = Wasm.Lib.List

(* Operators *)

module IntOp = Wasm.Ast.IntOp
module FloatOp = Wasm.Ast.FloatOp

module I32Op = Wasm.Ast.IntOp
module I64Op = Wasm.Ast.IntOp
module F32Op = Wasm.Ast.FloatOp
module F64Op = Wasm.Ast.FloatOp

type unop = Values.op I32Op.unop I64Op.unop F32Op.unop F64Op.unop
type binop = Values.op I32Op.binop I64Op.binop F32Op.binop F64Op.binop
type testop = Values.op I32Op.testop I64Op.testop F32Op.testop F64Op.testop
type relop = Values.op I32Op.relop I64Op.relop F32Op.relop F64Op.relop
type cvtop = Values.op I32Op.cvtop I64Op.cvtop F32Op.cvtop F64Op.cvtop

type memop 'a =
  {ty : value_type; align : nat; offset : Memory.offset; sz: option 'a}
type loadop = memop (Memory.pack_size * Memory.extension)
type storeop = memop Memory.pack_size

(* Expressions *)

type var = Source.phrase I32.t
type literal = Source.phrase Values.value
type name = list int

type instr = Source.phrase instr'
and instr' =
  | Unreachable                       (* trap unconditionally *)
  | Nop                               (* do nothing *)
  | Drop                              (* forget a value *)
  | Select                            (* branchless conditional *)
  | Block of stack_type * list instr  (* execute in sequence *)
  | Loop of stack_type * list instr   (* loop header *)
  | If of stack_type * list instr * list instr  (* conditional *)
  | Br of var                         (* break to n-th surrounding label *)
  | BrIf of var                       (* conditional break *)
  | BrTable of list var * var         (* indexed break *)
  | Return                            (* break from function body *)
  | Call of var                       (* call function *)
  | CallIndirect of var               (* call function through table *)
  | LocalGet of var                   (* read local variable *)
  | LocalSet of var                   (* write local variable *)
  | LocalTee of var                   (* write local variable and keep value *)
  | GlobalGet of var                  (* read global variable *)
  | GlobalSet of var                  (* write global variable *)
  | Load of loadop                    (* read memory at address *)
  | Store of storeop                  (* write memory at address *)
  | MemorySize                        (* size of linear memory *)
  | MemoryGrow                        (* grow linear memory *)
  | Const of literal                  (* constant *)
  | Test of testop                    (* numeric test *)
  | Compare of relop                  (* numeric comparison *)
  | Unary of unop                     (* unary numeric operator *)
  | Binary of binop                   (* binary numeric operator *)
  | Convert of cvtop                  (* conversion *)

(* Globals & Functions *)

type const = Source.phrase (list instr)

type global' =
{
  gtype: global_type;
  value: const;
}
type global = Source.phrase global'

type func' =
{
  ftype : var;
  flocals : list value_type;
  body : list instr;
}
type func = Source.phrase func'

(* Tables & Memories *)

type table' =
{
  ttype : table_type;
}
type table = Source.phrase table'

type memory' =
{
  mtype : memory_type;
}
type memory = Source.phrase memory'

type segment' data =
{
  index : var;
  seg_offset : const;
  init : data;
}
type segment data = Source.phrase (segment' data)

type table_segment = segment (list var)
type memory_segment = segment (list nat8)

(* Modules *)
type type_ = Source.phrase func_type

type export_desc' =
  | FuncExport of var
  | TableExport of var
  | MemoryExport of var
  | GlobalExport of var
type export_desc = Source.phrase export_desc'

type export' =
{
  name : name;
  edesc : export_desc;
}
type export = Source.phrase export'

type import_desc' =
  | FuncImport of var
  | TableImport of table_type
  | MemoryImport of memory_type
  | GlobalImport of global_type
type import_desc = Source.phrase import_desc'

type import' =
{
  module_name : name;
  item_name : name;
  idesc : import_desc;
}
type import = Source.phrase import'

type module_' =
{
  types : list type_;
  globals : list global;
  tables : list table;
  memories : list memory;
  funcs : list func;
  start : option var;
  elems : list (segment (list var));
  data : list (segment (list nat8));
  imports : list import;
  exports : list export;
}
type module_ = Source.phrase module_'

(* Auxiliary functions *)

let empty_module =
{
  types = [];
  globals = [];
  tables = [];
  memories = [];
  funcs = [];
  start = None;
  elems = [];
  data = [];
  imports = [];
  exports = [];
}

let __errfail = Left "error"

let func_type_for (m:module_) (x:var) : optr func_type =
  let opt = List.Tot.nth m.it.types (to_int_u x.it) in
  match opt with
  | Some ty_ -> Right ty_.it
  | None -> __errfail

let import_type (m:module_) (im:import) : optr extern_type =
  let idesc = im.it.idesc in
  match idesc.it with
  | FuncImport x ->
    let opt = func_type_for m x in
    o_fmap ExternFuncType opt
  | TableImport t -> Right (ExternTableType t)
  | MemoryImport t -> Right (ExternMemoryType t)
  | GlobalImport t -> Right (ExternGlobalType t)

let export_type (m:module_) (ex:export) : optr extern_type =
  let edesc = ex.it.edesc in
  let its_ = L.map_ex (import_type m) m.it.imports in
  let fts__ = L.map_ex (fun f -> func_type_for m f.it.ftype) m.it.funcs in
  let tts_ = List.Tot.map (fun t -> t.it.ttype) m.it.tables in
  let mts_ = List.Tot.map (fun m -> m.it.mtype) m.it.memories in
  let gts_ = List.Tot.map (fun g -> g.it.gtype) m.it.globals in
  match its_ with
  | Left err -> Left err
  | Right its -> (
    match edesc.it with
    | FuncExport x -> (
      match fts__ with
      | Left err -> Left err
      | Right fts_ -> (
        let fts = funcs its @ fts_ in
        let opt = List.Tot.nth fts (to_int_u x.it) in
        (match opt with
        | Some y -> Right (ExternFuncType y)
        | None -> __errfail)
      )
    )
    | TableExport x ->
      let tts = tables its @ tts_ in
      let opt = List.Tot.nth tts (to_int_u x.it) in
      (match opt with
      | Some y -> Right (ExternTableType y)
      | None -> __errfail)
    | MemoryExport x ->
      let mts = memories its @ mts_ in
      let opt = List.Tot.nth mts (to_int_u x.it) in
      (match opt with
      | Some y -> Right (ExternMemoryType y)
      | None -> __errfail)
    | GlobalExport x ->
      let gts = globals its @ gts_ in
      let opt = List.Tot.nth gts (to_int_u x.it) in
      (match opt with
      | Some y -> Right (ExternGlobalType y)
      | None -> __errfail)
  )

let string_of_name (n:int) : string = admit()
