module Wasm_simple.Print

open Words_s

open Common.Print
open Wasm_simple.Semantics
open FStar.String
open FStar.List.Tot

let lit_to_str (v:literal) =
  match v with
  | N32 n -> nat_to_str n
  | N64 n -> nat_to_str n
  | F32 f -> "[" ++ (concat " " (map nat_to_str f)) ++ "]"
  | F64 f -> "[" ++ (concat " " (map nat_to_str f)) ++ "]"

let type_to_str ty =
  match ty with
  | I32Ty -> "i32"
  | I64Ty -> "i64"
  | F32Ty -> "f32"
  | F64Ty -> "f64"

let func_type_to_str fty =
  let argtys, rettys = fty in
  let argtys_s = concat " " (map type_to_str argtys) in
  let rettys_s = concat " " (map type_to_str rettys) in
  "([Args: " ++ argtys_s ++ "]; [Ret: " ++ rettys_s ++ "])"

let global_to_str gbl =
  let {gtype; value} = gbl in
  let ty, mut = gtype in
  let mut_s = if mut then " mut" else "" in
  "(" ++ (type_to_str ty) ++ mut_s ++ " " ++ (lit_to_str value) ++ ")"

let limits_to_str (lim:limits nat32) =
  let {min; max} = lim in
  let min_s = nat_to_str min in
  let max_s =
    match max with
    | None -> "None"
    | Some v -> nat_to_str v
  in
  "(" ++ min_s ++ " " ++ max_s ++ ")"

let brtable_to_str brt =
  let {cases; def} = brt in
  let f (n, b) = "(" ++ (if b then "Cont " else "Br ") ++ nat_to_str n ++ ")" in
  let cases_s = concat " " (map f cases) in
  let def_s = f def in
  "[" ++ cases_s ++ "], " ++ def_s

let ocmp_to_str ocmp =
  match ocmp with
  | IsNonZero -> "IsNonZero"
  | Always -> "Always"

let ins_to_str ins =
  match ins with
  | Unreachable -> "Unreachable"
  | DropI -> "DropI"
  | SelectI -> "SelectI"
  | DropF -> "DropF"
  | SelectF -> "SelectF"
  | LocalGet v -> "LocalGet " ++ (nat_to_str v)
  | LocalSet v -> "LocalSet " ++ (nat_to_str v)
  | LocalTee v -> "LocalTee " ++ (nat_to_str v)
  | GlobalGet v -> "GlobalGet " ++ (nat_to_str v)
  | GlobalSet v -> "GlobalSet " ++ (nat_to_str v)
  | ExternGlobalGet v -> "ExternGlobalGet " ++ (nat_to_str v)
  | ExternGlobalSet v -> "ExternGlobalSet " ++ (nat_to_str v)
  | Load op ->
    let {lty; loffset; lsz; lsigned} = op in
    let lty_s = type_to_str lty in
    let loffset_s = nat_to_hex loffset in
    let lsz_s = nat_to_hex lsz in
    let lsigned_s = if lsigned then "SX" else "ZX" in
    "Load" ++ lsz_s ++ lsigned_s ++ "_TO_" ++ lty_s ++ " @ " ++ loffset_s
  | Store op ->
    let {sty; soffset; ssz} = op in
    let sty_s = type_to_str sty in
    let soffset_s = nat_to_hex soffset in
    let ssz_s = nat_to_hex ssz in
    "Store" ++ ssz_s ++ "_OF_" ++ sty_s ++ " @ " ++ soffset_s
  | MemoryGrow -> "MemoryGrow"
  | MemorySize -> "MemorySize"
  | Const lit ->
    (match lit with
     | N32 n -> "Const I32 " ++ (nat_to_str n)
     | N64 n -> "Const I64 " ++ (nat_to_str n)
     | F32 f -> "Const F32 " ++ (lit_to_str lit)
     | F64 f -> "Const F64 " ++ (lit_to_str lit)
    )

  | I32Eqz -> "I32Eqz"

  | I64Eqz -> "I64Eqz"

  | I32Eq -> "I32Eq"
  | I32Ne -> "I32Ne"
  | I32LtS -> "I32LtS"
  | I32LtU -> "I32LtU"
  | I32GtS -> "I32GtS"
  | I32GtU -> "I32GtU"
  | I32LeS -> "I32LeS"
  | I32LeU -> "I32LeU"
  | I32GeS -> "I32GeS"
  | I32GeU -> "I32GeU"

  | I64Eq -> "I64Eq"
  | I64Ne -> "I64Ne"
  | I64LtS -> "I64LtS"
  | I64LtU -> "I64LtU"
  | I64GtS -> "I64GtS"
  | I64GtU -> "I64GtU"
  | I64LeS -> "I64LeS"
  | I64LeU -> "I64LeU"
  | I64GeS -> "I64GeS"
  | I64GeU -> "I64GeU"

  | F32Eq -> "F32Eq"
  | F32Ne -> "F32Ne"
  | F32Lt -> "F32Lt"
  | F32Gt -> "F32Gt"
  | F32Le -> "F32Le"
  | F32Ge -> "F32Ge"

  | F64Eq -> "F64Eq"
  | F64Ne -> "F64Ne"
  | F64Lt -> "F64Lt"
  | F64Gt -> "F64Gt"
  | F64Le -> "F64Le"
  | F64Ge -> "F64Ge"

  | I32Clz -> "I32Clz"
  | I32Ctz -> "I32Ctz"
  | I32Popcnt -> "I32Popcnt"

  | I64Clz -> "I64Clz"
  | I64Ctz -> "I64Ctz"
  | I64Popcnt -> "I64Popcnt"

  | F32Neg -> "F32Neg"
  | F32Abs -> "F32Abs"
  | F32Ceil -> "F32Ceil"
  | F32Floor -> "F32Floor"
  | F32Trunc -> "F32Trunc"
  | F32Nearest -> "F32Nearest"
  | F32Sqrt -> "F32Sqrt"

  | F64Neg -> "F64Neg"
  | F64Abs -> "F64Abs"
  | F64Ceil -> "F64Ceil"
  | F64Floor -> "F64Floor"
  | F64Trunc -> "F64Trunc"
  | F64Nearest -> "F64Nearest"
  | F64Sqrt -> "F64Sqrt"

  | I32Add -> "I32Add"
  | I32Sub -> "I32Sub"
  | I32Mul -> "I32Mul"
  | I32DivS -> "I32DivS"
  | I32DivU -> "I32DivU"
  | I32RemS -> "I32RemS"
  | I32RemU -> "I32RemU"
  | I32And -> "I32And"
  | I32Or -> "I32Or"
  | I32Xor -> "I32Xor"
  | I32Shl -> "I32Shl"
  | I32ShrS -> "I32ShrS"
  | I32ShrU -> "I32ShrU"
  | I32Rotl -> "I32Rotl"
  | I32Rotr -> "I32Rotr"

  | I64Add -> "I64Add"
  | I64Sub -> "I64Sub"
  | I64Mul -> "I64Mul"
  | I64DivS -> "I64DivS"
  | I64DivU -> "I64DivU"
  | I64RemS -> "I64RemS"
  | I64RemU -> "I64RemU"
  | I64And -> "I64And"
  | I64Or -> "I64Or"
  | I64Xor -> "I64Xor"
  | I64Shl -> "I64Shl"
  | I64ShrS -> "I64ShrS"
  | I64ShrU -> "I64ShrU"
  | I64Rotl -> "I64Rotl"
  | I64Rotr -> "I64Rotr"

  | F32Add -> "F32Add"
  | F32Sub -> "F32Sub"
  | F32Mul -> "F32Mul"
  | F32Div -> "F32Div"
  | F32Min -> "F32Min"
  | F32Max -> "F32Max"
  | F32CopySign -> "F32CopySign"

  | F64Add -> "F64Add"
  | F64Sub -> "F64Sub"
  | F64Mul -> "F64Mul"
  | F64Div -> "F64Div"
  | F64Min -> "F64Min"
  | F64Max -> "F64Max"
  | F64CopySign -> "F64CopySign"

  | I32WrapI64 -> "I32WrapI64"
  | I32TruncSF32 -> "I32TruncSF32"
  | I32TruncUF32 -> "I32TruncUF32"
  | I32TruncSF64 -> "I32TruncSF64"
  | I32TruncUF64 -> "I32TruncUF64"
  | I32ReinterpretFloat -> "I32ReinterpretFloat"

  | I64ExtendSI32 -> "I64ExtendSI32"
  | I64ExtendUI32 -> "I64ExtendUI32"
  | I64TruncSF32 -> "I64TruncSF32"
  | I64TruncUF32 -> "I64TruncUF32"
  | I64TruncSF64 -> "I64TruncSF64"
  | I64TruncUF64 -> "I64TruncUF64"
  | I64ReinterpretFloat -> "I64ReinterpretFloat"

  | F32DemoteF64 -> "F32DemoteF64"
  | F32ConvertSI32 -> "F32ConvertSI32"
  | F32ConvertUI32 -> "F32ConvertUI32"
  | F32ConvertSI64 -> "F32ConvertSI64"
  | F32ConvertUI64 -> "F32ConvertUI64"
  | F32ReinterpretInt -> "F32ReinterpretInt"

  | F64PromoteF32 -> "F64PromoteF32"
  | F64ConvertSI32 -> "F64ConvertSI32"
  | F64ConvertUI32 -> "F64ConvertUI32"
  | F64ConvertSI64 -> "F64ConvertSI64"
  | F64ConvertUI64 -> "F64ConvertUI64"
  | F64ReinterpretInt -> "F64ReinterpretInt"

let rec code_to_str (c:code) (ind_s:string):string =
  let ind_s' = ind_s ++ "  " in
  match c with
  | Ins ins -> ind_s ++ "(" ++ (ins_to_str ins) ++ ")"
  | Block cs ts ->
    ind_s ++ "{\n" ++ (codes_to_str cs ind_s') ++ ind_s ++ "}"
  | IfElse ctrue cfalse ts ->
    ind_s ++ "(If IsNonZero" ++ "\n" ++
    (codes_to_str ctrue ind_s') ++ "\n\n" ++
    (codes_to_str cfalse ind_s') ++ "\n" ++
    ind_s ++ ")"
  | Break level Always ->
    ind_s ++ "(Break " ++ (nat_to_str level) ++ ")"
  | Break level IsNonZero ->
    ind_s ++ "(BreakNZ " ++ (nat_to_str level) ++ ")"
  | BrTable tbl ->
    ind_s ++ "(BrTable " ++ (brtable_to_str tbl) ++ ")"
  | Continue level Always ->
    ind_s ++ "(Continue " ++ (nat_to_str level) ++ ")"
  | Continue level IsNonZero ->
    ind_s ++ "(ContinueNZ " ++ (nat_to_str level) ++ ")"
  | Call f ->
    ind_s ++ "(Call " ++ (nat_to_str f) ++ ")"
  | ExternCall f ->
    ind_s ++ "(ExternCall " ++ (nat_to_str f) ++ ")"
  | CallIndirect fn_ty ->
    ind_s ++ "(CallIndirect (type " ++ (nat_to_str fn_ty) ++ "))"
  | Return ->
    ind_s ++ "(Return)"

and codes_to_str (cs:codes) (ind_s:string):string =
  match cs with
  | [] -> ""
  | c :: cs ->
    let c_s = code_to_str c ind_s in
    let cs_s = codes_to_str cs ind_s in
    c_s ++ "\n" ++ cs_s

let func_to_str func =
  let {ftype; flocals; body} = func in
  let sep = "**********************************************************************" in
  let ftype_s = "Type: " ++ (nat_to_str ftype) in
  let flocals_s = "Locals:\n" ++ (enummap type_to_str flocals) in
  let body_s = codes_to_str body "" in
  "\n" ++ sep ++ "\n" ++ ftype_s ++ "\n" ++ flocals_s ++ "\n" ++ body_s

let elems_to_str (seg:segment (list var)) =
  let {index; seg_offset; init} = seg in
  let index_s = "Index: " ++ (nat_to_str index) in
  let seg_offset_s = "Offset: " ++ (lit_to_str seg_offset) in
  let init_s = "Init: [" ++ (concat " " (map nat_to_hex init)) ++ "]" in
  "\n" ++ index_s ++ "\n" ++ seg_offset_s ++ "\n" ++ init_s

let data_to_str (seg:segment (list nat8)) =
  let {index; seg_offset; init} = seg in
  let index_s = "Index: " ++ (nat_to_str index) in
  let seg_offset_s = "Offset: " ++ (lit_to_str seg_offset) in
  let init_s = "Init: [" ++ (concat " " (map nat_to_hex init)) ++ "]" in
  "\n" ++ index_s ++ "\n" ++ seg_offset_s ++ "\n" ++ init_s

let import_to_str import f =
  let {module_name; item_name; idesc} = import in
  let module_name_s = "[" ++ (concat " " (map int_to_str module_name)) ++ "]" in
  let item_name_s = "[" ++ (concat " " (map int_to_str item_name)) ++ "]" in
  let idesc_s = f idesc in
  "(" ++ module_name_s ++ " " ++ item_name_s ++ " " ++ idesc_s ++ ")"

let fimport_to_str import =
  let f (v:var) = "FuncImport " ++ (nat_to_str v) in
  import_to_str import f

let timport_to_str import =
  let f v = "TableImport " ++ (limits_to_str v) in
  import_to_str import f

let mimport_to_str import =
  let f v = "MemoryImport " ++ (limits_to_str v) in
  import_to_str import f

let gimport_to_str import =
  let f (ty, mut) = "GlobalImport " ++ "(" ++ (type_to_str ty) ++ (if mut then " mut" else "") ++ ")" in
  import_to_str import f

let export_to_str export f =
  let {name; edesc} = export in
  let name_s = "[" ++ (concat " " (map int_to_str name)) ++ "]" in
  let edesc_s = f edesc in
  "(" ++ name_s ++ " " ++ edesc_s ++ ")"

let fexport_to_str export =
  let f (v:var) = "FuncExport " ++ (nat_to_str v) in
  export_to_str export f

let texport_to_str export =
  let f (v:var) = "TableExport " ++ (nat_to_str v) in
  export_to_str export f

let mexport_to_str export =
  let f (v:var) = "MemoryExport " ++ (nat_to_str v) in
  export_to_str export f

let gexport_to_str export =
  let f (v:var) = "GlobalExport " ++ (nat_to_str v) in
  export_to_str export f

let enummap_section heading sep f xs =
  sep ++ "\n" ++ heading ++ "\n" ++ sep ++ "\n" ++ (enummap f xs)

let module_to_str m1 =
  let {types; globals; tables; memories; funcs; start; elems; data; fimports; timports; mimports; gimports; fexports; texports; mexports; gexports} = m1 in
  let sep = "======================================================================" in
  let types_s = enummap_section "Types:" sep func_type_to_str types in
  let gbls_s = enummap_section "Globals:" sep global_to_str globals in
  let tables_s = enummap_section "Tables:" sep limits_to_str tables in
  let memories_s = enummap_section "Memories:" sep limits_to_str memories in
  let funcs_s = enummap_section "Funcs:" sep func_to_str funcs in
  let start_s =
    match start with
    | None -> "Start: None\n"
    | Some v -> "Start: " ++ (nat_to_str v) ++ "\n"
  in
  let elems_s = enummap_section "Elems:" sep elems_to_str elems in
  let data_s = enummap_section "Data:" sep data_to_str data in
  let fimports_s = enummap_section "Func Imports:" sep fimport_to_str fimports in
  let timports_s = enummap_section "Table Imports:" sep timport_to_str timports in
  let mimports_s = enummap_section "Memory Imports:" sep
mimport_to_str mimports in
  let gimports_s = enummap_section "Global Imports:" sep gimport_to_str gimports in
  let fexports_s = enummap_section "Func Exports:" sep fexport_to_str fexports in
  let texports_s = enummap_section "Table Exports:" sep texport_to_str texports in
  let mexports_s = enummap_section "Memory Exports:" sep mexport_to_str mexports in
  let gexports_s = enummap_section "Global Exports:" sep gexport_to_str gexports in
  types_s ++ "\n" ++
  gbls_s ++ "\n" ++
  tables_s ++ "\n" ++
  elems_s ++ "\n" ++
  memories_s ++ "\n" ++
  fimports_s ++ "\n" ++
  timports_s ++ "\n" ++
  mimports_s ++ "\n" ++
  gimports_s ++ "\n" ++
  fexports_s ++ "\n" ++
  texports_s ++ "\n" ++
  mexports_s ++ "\n" ++
  gexports_s ++ "\n" ++
  funcs_s ++ "\n" ++
  sep ++ "\n" ++
  start_s ++ "\n"
