module Wasm_simple.Semantics

open Words_s

(* Expressions *)

(* TODO: Using list nat8 as type of float *)
type var = nat32
type literal =
  | N32: nat32 -> literal
  | N64: nat64 -> literal
  | F32: list nat8 -> literal
  | F64: list nat8 -> literal
type name = list int

type value_type =
  | I32Ty
  | I64Ty
  | F32Ty
  | F64Ty

type func_type = (list value_type) * (list value_type)

type pack_size = (n:nat{n = 1 \/ n = 2 \/ n = 4 \/ n = 8})
type loadop =
  {lty: (v:value_type);
   loffset: nat32;
   lsz: pack_size;
   lsigned: bool
  }
type storeop =
  {sty: (v:value_type);
   soffset: nat32;
   ssz: pack_size;
  }

type brtable_type =
{
  cases: list (nat * bool);
  def: nat * bool;
}

type jcond =
  | Always
  | IsNonZero

type precode (t_ins:eqtype) =
  | Ins: ins:t_ins -> precode t_ins
  | Block: block:list (precode t_ins) -> ts:list value_type -> precode t_ins
  | IfElse: ifTrue:list (precode t_ins) -> ifFalse:list (precode t_ins) -> ts: list value_type -> precode t_ins // implicit isNonZero
  | Break: level:nat -> cond:jcond -> precode t_ins
  | BrTable: tbl:brtable_type -> precode t_ins
  | Continue: level:nat -> cond:jcond -> precode t_ins
  | Call: f:var -> precode t_ins
  | ExternCall: f:var -> precode t_ins
  | CallIndirect: fn_ty:var -> precode t_ins
  | Return: precode t_ins

type ins =
  | Unreachable: ins
  | DropI: ins
  | DropF: ins
  | SelectI: ins
  | SelectF: ins
  | LocalGet: var -> ins
  | LocalSet: var -> ins
  | LocalTee: var -> ins
  | GlobalGet: var -> ins
  | GlobalSet: var -> ins
  | ExternGlobalGet: var -> ins
  | ExternGlobalSet: var -> ins
  | Load: loadop -> ins
  | Store: storeop -> ins
  | MemorySize: ins
  | MemoryGrow: ins
  | Const: literal -> ins

  | I32Eqz: ins

  | I64Eqz: ins

  | I32Eq: ins
  | I32Ne: ins
  | I32LtS: ins
  | I32LtU: ins
  | I32GtS: ins
  | I32GtU: ins
  | I32LeS: ins
  | I32LeU: ins
  | I32GeS: ins
  | I32GeU: ins

  | I64Eq: ins
  | I64Ne: ins
  | I64LtS: ins
  | I64LtU: ins
  | I64GtS: ins
  | I64GtU: ins
  | I64LeS: ins
  | I64LeU: ins
  | I64GeS: ins
  | I64GeU: ins

  | F32Eq: ins
  | F32Ne: ins
  | F32Lt: ins
  | F32Gt: ins
  | F32Le: ins
  | F32Ge: ins

  | F64Eq: ins
  | F64Ne: ins
  | F64Lt: ins
  | F64Gt: ins
  | F64Le: ins
  | F64Ge: ins

  | I32Clz: ins
  | I32Ctz: ins
  | I32Popcnt: ins

  | I64Clz: ins
  | I64Ctz: ins
  | I64Popcnt: ins

  | F32Neg: ins
  | F32Abs: ins
  | F32Ceil: ins
  | F32Floor: ins
  | F32Trunc: ins
  | F32Nearest: ins
  | F32Sqrt: ins

  | F64Neg: ins
  | F64Abs: ins
  | F64Ceil: ins
  | F64Floor: ins
  | F64Trunc: ins
  | F64Nearest: ins
  | F64Sqrt: ins

  | I32Add: ins
  | I32Sub: ins
  | I32Mul: ins
  | I32DivS: ins
  | I32DivU: ins
  | I32RemS: ins
  | I32RemU: ins
  | I32And: ins
  | I32Or: ins
  | I32Xor: ins
  | I32Shl: ins
  | I32ShrS: ins
  | I32ShrU: ins
  | I32Rotl: ins
  | I32Rotr: ins

  | I64Add: ins
  | I64Sub: ins
  | I64Mul: ins
  | I64DivS: ins
  | I64DivU: ins
  | I64RemS: ins
  | I64RemU: ins
  | I64And: ins
  | I64Or: ins
  | I64Xor: ins
  | I64Shl: ins
  | I64ShrS: ins
  | I64ShrU: ins
  | I64Rotl: ins
  | I64Rotr: ins

  | F32Add: ins
  | F32Sub: ins
  | F32Mul: ins
  | F32Div: ins
  | F32Min: ins
  | F32Max: ins
  | F32CopySign: ins

  | F64Add: ins
  | F64Sub: ins
  | F64Mul: ins
  | F64Div: ins
  | F64Min: ins
  | F64Max: ins
  | F64CopySign: ins

  | I32WrapI64: ins
  | I32TruncSF32: ins
  | I32TruncUF32: ins
  | I32TruncSF64: ins
  | I32TruncUF64: ins
  | I32ReinterpretFloat: ins

  | I64ExtendSI32: ins
  | I64ExtendUI32: ins
  | I64TruncSF32: ins
  | I64TruncUF32: ins
  | I64TruncSF64: ins
  | I64TruncUF64: ins
  | I64ReinterpretFloat: ins

  | F32DemoteF64: ins
  | F32ConvertSI32: ins
  | F32ConvertUI32: ins
  | F32ConvertSI64: ins
  | F32ConvertUI64: ins
  | F32ReinterpretInt: ins

  | F64PromoteF32: ins
  | F64ConvertSI32: ins
  | F64ConvertUI32: ins
  | F64ConvertSI64: ins
  | F64ConvertUI64: ins
  | F64ReinterpretInt: ins

type code = precode ins
type codes = list code

type limits 'a = {min: 'a; max: option 'a}

// TODO: At the moment, only FuncRefType, so type is ignored
type table_type = limits nat32
type memory_type = limits nat32
type global_type = value_type * bool (* True if mutable *)

type global =
{
  gtype: global_type;
  value: literal;
}

type func =
{
  ftype: var;
  flocals: list value_type; // includes args
  body: codes;
}

type segment data =
{
  index: var;
  seg_offset: literal;
  init: data;
}
type export =
{
  name: name;
  edesc: var;
}

type import desc =
{
  module_name: name;
  item_name: name;
  idesc: desc;
}

type module_ =
{
  types: list func_type;
  globals: list global;
  tables: list table_type;
  memories: list memory_type;
  funcs: list func;
  start: option var;
  elems: list (segment (list var));
  data: list (segment (list nat8));
  fimports: list (import var);
  timports: list (import table_type);
  mimports: list (import memory_type);
  gimports: list (import global_type);
  fexports: list export;
  texports: list export;
  mexports: list export;
  gexports: list export;
  mem_pages: nat32;
}

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
  fimports = [];
  timports = [];
  mimports = [];
  gimports = [];
  fexports = [];
  texports = [];
  mexports = [];
  gexports = [];
  mem_pages = 0;
}
