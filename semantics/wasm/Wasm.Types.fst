(**
Various types of wasm constructs.

@summary Wasm types.
*)
module Wasm.Types

open FStar.Option

module I32 = Wasm.I32
module L = Wasm.Lib.List

(* Types *)

type value_type =
  | I32Type
  | I64Type
  | F32Type
  | F64Type

type stack_type = list value_type

type func_type =
  | FuncType of stack_type * stack_type

type limits 'a = {min: 'a; max: option 'a}

type elem_type =
  | FuncRefType
type table_type =
  | TableType of (limits I32.t) * elem_type

type memory_type =
  | MemoryType of limits I32.t

type mutability =
  | Immutable
  | Mutable
type global_type =
  | GlobalType of value_type * mutability

type extern_type =
  | ExternFuncType of func_type
  | ExternTableType of table_type
  | ExternMemoryType of memory_type
  | ExternGlobalType of global_type

(* Attributes *)

let size ty =
  match ty with
  | I32Type | F32Type -> 4
  | I64Type | F64Type -> 8

(* Subtyping *)

val match_limits: limits I32.t -> limits I32.t -> Tot bool
let match_limits lim1 lim2 =
  I32.ge_u lim1.min lim2.min &&
  ( match lim1.max, lim2.max with
  | _, None -> true
  | None, Some _ -> false
  | Some i, Some j -> I32.le_u i j )

val match_func_type: func_type -> func_type -> Tot bool
let match_func_type ft1 ft2 =
  ft1 = ft2

val match_table_type: table_type -> table_type -> Tot bool
let match_table_type (TableType (lim1, et1)) (TableType (lim2, et2)) =
  et1 = et2 && match_limits lim1 lim2

val match_memory_type: memory_type -> memory_type -> Tot bool
let match_memory_type (MemoryType lim1) (MemoryType lim2) =
  match_limits lim1 lim2

val match_global_type: global_type -> global_type -> Tot bool
let match_global_type gt1 gt2 =
  gt1 = gt2

val match_extern_type: extern_type -> extern_type -> Tot bool
let match_extern_type et1 et2 =
  match et1, et2 with
  | ExternFuncType ft1, ExternFuncType ft2 -> match_func_type ft1 ft2
  | ExternTableType tt1, ExternTableType tt2 -> match_table_type tt1 tt2
  | ExternMemoryType mt1, ExternMemoryType mt2 -> match_memory_type mt1 mt2
  | ExternGlobalType gt1, ExternGlobalType gt2 -> match_global_type gt1 gt2
  | _, _ -> false

(* Filters *)
let funcs exts =
  L.map_filter (fun ext -> match ext with | ExternFuncType t -> Some t | _ -> None) exts
let tables exts =
  L.map_filter (fun ext -> match ext with | ExternTableType t -> Some t | _ -> None) exts
let memories exts =
  L.map_filter (fun ext -> match ext with | ExternMemoryType t -> Some t | _ -> None) exts
let globals exts =
  L.map_filter (fun ext -> match ext with | ExternGlobalType t -> Some t | _ -> None) exts

(* String conversion *)

let string_of_value_type ty =
  match ty with
  | I32Type -> "i32"
  | I64Type -> "i64"
  | F32Type -> "f32"
  | F64Type -> "f64"

let string_of_value_types tys =
  match tys with
  | [t] -> string_of_value_type t
  | ts -> "[" ^ String.concat " " (List.Tot.map string_of_value_type ts) ^ "]"

let string_of_elem_type ty =
  match ty with
  | FuncRefType -> "funcref"

let string_of_limits {min; max} =
  I32.to_string_u min ^
  (match max with None -> "" | Some n -> " " ^ I32.to_string_u n)

let string_of_memory_type ty =
  match ty with
  | MemoryType lim -> string_of_limits lim

let string_of_table_type ty =
  match ty with
  | TableType (lim, t) -> string_of_limits lim ^ " " ^ string_of_elem_type t

let string_of_global_type ty =
  match ty with
  | GlobalType (t, Immutable) -> string_of_value_type t
  | GlobalType (t, Mutable) -> "(mut " ^ string_of_value_type t ^ ")"

let string_of_stack_type ts =
  "[" ^ String.concat " " (List.Tot.map string_of_value_type ts) ^ "]"

let string_of_func_type (FuncType (ins, out)) =
  string_of_stack_type ins ^ " -> " ^ string_of_stack_type out

let string_of_extern_type ext =
  match ext with
  | ExternFuncType ft -> "func " ^ string_of_func_type ft
  | ExternTableType tt -> "table " ^ string_of_table_type tt
  | ExternMemoryType mt -> "memory " ^ string_of_memory_type mt
  | ExternGlobalType gt -> "global " ^ string_of_global_type gt
