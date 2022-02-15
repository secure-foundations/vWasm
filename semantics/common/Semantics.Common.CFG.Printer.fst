(** Generic printer for CFGs *)
module Semantics.Common.CFG.Printer

open Semantics.Common.CFG

let string_of_int (i:int) =
  if i < 0 then (
    "(" ^ Prims.string_of_int i ^ ")"
  ) else (
    Prims.string_of_int i
  )

let string_of_loc (l:loc) : string =
  string_of_int l

let string_of_regi #vali (r:regi #vali) =
  string_of_int r

let string_of_regf #valf (r:regf #valf) =
  string_of_int r

let string_of_maddr #vali (m:maddr #vali) =
  "(" ^ (
    match m with
    //| MConst n -> "MConst " ^ string_of_int n
    //| MReg r offset -> "MReg " ^ string_of_regi r ^ " " ^ string_of_int offset
    | MIndex scale index offset ->
      "MIndex " ^
      string_of_int scale ^ " " ^
      string_of_regi index ^ "_" ^
      string_of_int offset
  ) ^ ")"

let string_of_operandi #vali (o:operandi #vali) =
  "(" ^ (
    match o with
    | OConst n -> "OConst " ^ string_of_int n
    | OReg r sz -> "OReg_" ^ string_of_int sz ^ " " ^ string_of_regi r
    | OMemRel m -> "OMemRel " ^ string_of_maddr m
    | OStackRel m -> "OStack " ^ string_of_int m
    | ONamedGlobal (Ident n) -> "ONamedGlobal " ^ string_of_int n
    | ONamedGlobal MemPages -> "ONamedGlobal MemPages"
  ) ^ ")"

let string_of_operandf #vali #valf (o:operandf #vali #valf) =
  "(" ^ (
    match o with
    | OConst_f n -> "OConst_f UNK"
    | OReg_f r sz -> "OReg_f_" ^ string_of_int sz ^ " " ^ string_of_regf r
    | OMemRel_f m -> "OMemRel_f " ^ string_of_maddr m
    | OStackRel_f m -> "OStack_f " ^ string_of_int m
    | ONamedGlobal_f (Ident_f n) -> "ONamedGlobal_f " ^ string_of_int n
  ) ^ ")"

let string_of_ocmp #vali #valf (o:ocmp #vali #valf) =
  "(" ^ (
    match o with
    | OEq64 o1 o2 -> "OEq64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | ONe64 o1 o2 -> "ONe64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLe64 o1 o2 -> "OLe64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGe64 o1 o2 -> "OGe64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLt64 o1 o2 -> "OLt64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGt64 o1 o2 -> "OGt64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OEq32 o1 o2 -> "OEq32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | ONe32 o1 o2 -> "ONe32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLe32 o1 o2 -> "OLe32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGe32 o1 o2 -> "OGe32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLt32 o1 o2 -> "OLt32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGt32 o1 o2 -> "OGt32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2

    (* 32 bit comparisons *)
    | OEq32  o1 o2 -> "OEq32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | ONe32  o1 o2 -> "ONe32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLe32  o1 o2 -> "OLe32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGe32  o1 o2 -> "OGe32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLt32  o1 o2 -> "OLt32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGt32  o1 o2 -> "OGt32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2

    | OLeS32 o1 o2 -> "OLeS32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGeS32 o1 o2 -> "OGeS32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLtS32 o1 o2 -> "OLtS32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGtS32 o1 o2 -> "OGtS32 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    (* 64 bit comparisons *)
    | OEq64  o1 o2 -> "OEq64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | ONe64  o1 o2 -> "ONe64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLe64  o1 o2 -> "OLe64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGe64  o1 o2 -> "OGe64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLt64  o1 o2 -> "OLt64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGt64  o1 o2 -> "OGt64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2

    | OLeS64 o1 o2 -> "OLeS64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGeS64 o1 o2 -> "OGeS64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OLtS64 o1 o2 -> "OLtS64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    | OGtS64 o1 o2 -> "OGtS64 " ^ string_of_operandi o1 ^ " " ^ string_of_operandi o2
    (* 32 bit floats *)
    | OFEq32 o1 o2 -> "OFEq32 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFNe32 o1 o2 -> "OFNe32 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFLt32 o1 o2 -> "OFLt32 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFGt32 o1 o2 -> "OFGt32 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFLe32 o1 o2 -> "OFLe32 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFGe32 o1 o2 -> "OFGe32 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    (* 64 bit floats *)
    | OFEq64 o1 o2 -> "OFEq64 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFNe64 o1 o2 -> "OFNe64 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFLt64 o1 o2 -> "OFLt64 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFGt64 o1 o2 -> "OFGt64 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFLe64 o1 o2 -> "OFLe64 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
    | OFGe64 o1 o2 -> "OFGe64 " ^ string_of_operandf o1 ^ " " ^ string_of_operandf o2
  ) ^ ")"

let string_of_target #vali (t:target_t #vali) =
  "(" ^ (
    match t with
    | CallDirect n -> "CallDirect " ^ string_of_int n
    | CallIndirect r -> "CallIndirect " ^ string_of_int r
  ) ^ ")"

let string_of_arg (arg:ins_arg) =
  "(" ^ (
    match arg with
    | ArgInt r false -> "ArgInt32 " ^ string_of_int r
    | ArgInt r true -> "ArgInt64 " ^ string_of_int r
    | ArgFloat r false -> "ArgFloat32 " ^ string_of_int r
    | ArgFloat r true -> "ArgFloat64 " ^ string_of_int r
  ) ^ ")"

let string_of_args (args:list ins_arg) =
  let rec f (l:list ins_arg) =
    match l with
    | [] -> ""
    | [x] -> string_of_arg x
    | x :: l -> string_of_arg x ^ ";" ^ f l
  in
  "[" ^ f args ^ "]"

let string_of_oparg (retval:option ins_arg) =
  "(" ^ (
    match retval with
    | None -> "None"
    | Some v -> "Some " ^ string_of_arg v
  ) ^ ")"

let string_of_precode #inst #vali #valf #string_of_inst (p:precode #inst #vali #valf) : string =
  let rec string_of_insts (is:list inst) : string =
    match is with
    | [] -> ""
    | x :: xs -> string_of_inst x ^ " " ^ string_of_insts xs
  in
  match p with
  | FnEntry name next ->
    "FnEntry " ^ string_of_int name ^ " " ^ string_of_loc next
  | FnExit name ->
    "FnExit " ^ string_of_int name
  | Ins i next ->
    "Ins (" ^ string_of_inst i ^ ") " ^ string_of_loc next
  | InsList is next ->
    "Ins (" ^ string_of_insts is ^ ") " ^ string_of_loc next
  | Nop next ->
    "Nop " ^ string_of_loc next
  | Cmp cond nextTrue nextFalse ->
    "Cmp " ^ string_of_ocmp cond ^ " " ^ string_of_loc nextTrue ^ " " ^ string_of_loc nextFalse
  | Switch case_table case ->
    "Switch " ^ string_of_int case_table ^ " " ^ string_of_regi case
  | Call target next ->
    "Call " ^ string_of_target target ^ " " ^ string_of_loc next
  | HighCall target args retval_loc next ->
    "HighCall " ^ string_of_target target ^ " " ^ string_of_args args ^ " " ^ string_of_oparg retval_loc ^ " " ^ string_of_loc next
  | Ret next ->
    "Ret " ^ string_of_int next
  | HighRet retval next ->
    "HighRet " ^ string_of_oparg retval ^ " " ^ string_of_loc next

(* Note: If the passed in [string_of_inst] parameter is such that its
         result can be directly dropped into F* to get type checked
         into an [inst], then the results of [string_of_cfg] can
         instantly be dropped into F* to get a type-checkable
         string. This should be _super_ useful for debugging, thus it
         is strongly recommend that the style shown above is used when
         implementing [string_of_inst] for all languages, if
         possible. *)
let string_of_cfg (#inst:eqtype) #vali #valf
    (#string_of_inst : (inst -> string))
    (c:cfg #inst #vali #valf) : string =
  let rec aux xs n s =
    match xs with
    | [] -> s
    | x :: xs ->
      let ins_line = string_of_int n ^ "\t" ^ string_of_precode #_ #_ #_ #string_of_inst x ^ ";\n" in
      aux xs (n + 1) (s ^ ins_line) in
  "[\n" ^ aux c 0 "" ^ "]"

let print_strings_of_cfg (#inst:eqtype) #vali #valf
    (#string_of_inst : (inst -> string))
    (c:cfg #inst #vali #valf) : list string =
  "[\n" :: List.Tot.Base.rev ("]" :: snd (List.Tot.Base.fold_left (fun (n, l) x ->
      (n + 1,
       (string_of_int n ^ "\t" ^
        string_of_precode #_ #_ #_ #string_of_inst x ^ ";\n") ::
       l)) (0, []) c))

let string_of_opt #a (p:a -> string) (o:option a) : string =
  match o with
  | None -> "None"
  | Some x -> "(Some " ^ (p x) ^ ")"

let rec string_of_list_ #a (p:a -> string) (l:list a) : string =
  match l with
  | [] -> ""
  | [x] -> p x
  | x :: l -> (p x) ^ "; " ^ (string_of_list_ p l)

let string_of_list #a (p:a -> string) (l:list a) : string =
  "[" ^ (string_of_list_ p l) ^ "]"

let string_of_pair #a #b (pa:a -> string) (pb:b -> string) (t:(a * b)) : string =
  let x1, x2 = t in
  "(" ^ (pa x1) ^ ", " ^ (pb x2) ^ ")"

let string_of_val_ty (val_ty:val_ty) : string =
  match val_ty with
  | I32_ty -> "I32_ty"
  | I64_ty -> "I64_ty"
  | F32_ty -> "F32_ty"
  | F64_ty -> "F64_ty"

let string_of_aux_fn (aux_fn:aux_fn) : string =
  let {fn_name; fn_str; fn_loc; fn_end;
       fn_argtys; fn_rettys; fn_isImported; fn_isExported}
       = aux_fn
  in
  let name_s = string_of_int fn_name in
  let str_s = fn_str in
  let loc_s = string_of_int fn_loc in
  let end_s = string_of_int fn_end in
  let argtys_s = string_of_list (string_of_val_ty) (fn_argtys) in
  let rettys_s = string_of_opt (string_of_val_ty) (fn_rettys) in
  let isImported_s = string_of_bool fn_isImported in
  let isExported_s = string_of_bool fn_isExported in
  "({ " ^ "name: " ^ name_s ^ "; "
        ^ "str: " ^ str_s ^ "; "
        ^ "loc: " ^ loc_s ^ "; "
        ^ "end: " ^ end_s ^ "; "
        ^ "argtys: " ^ argtys_s ^ "; "
        ^ "rettys: " ^ rettys_s ^ "; "
        ^ "isImported: " ^ isImported_s ^ "; "
        ^ "isExported: " ^ isExported_s ^ "})"

let string_of_aux_global (aux_global:aux_global) : string =
  let {gbl_name; gbl_init; gbl_ty; gbl_isMutable;
       gbl_isImported; gbl_isExported} = aux_global
  in
  let name_s = gbl_name in
  let s_of_nat8: Types_s.nat8 -> string = string_of_int in
  let init_s = string_of_opt (string_of_list s_of_nat8) gbl_init in
  let ty_s = string_of_val_ty gbl_ty in
  let isMutable_s = string_of_bool gbl_isMutable in
  let isImported_s = string_of_bool gbl_isImported in
  let isExported_s = string_of_bool gbl_isExported in
  "({ " ^ name_s ^ "; "
        ^ init_s ^ "; "
        ^ ty_s ^ "; "
        ^ isMutable_s ^ "; "
        ^ isImported_s ^ "; "
        ^ isExported_s ^ "})"

let string_of_aux_memory (aux_memory:aux_memory) : string =
  let {mem_name; mem_init; mem_min; mem_max;
       mem_isImported; mem_isExported} = aux_memory
  in
  let name_s = mem_name in
  let s_of_nat8: Types_s.nat8 -> string = string_of_int in
  let s_of_nat32: Types_s.nat32 -> string = string_of_int in
  let init_s = string_of_list (string_of_pair (string_of_list s_of_nat8) s_of_nat32) mem_init in
  let min_s = s_of_nat32 mem_min in
  let max_s = string_of_opt s_of_nat32 mem_max in
  let isImported_s = string_of_bool mem_isImported in
  let isExported_s = string_of_bool mem_isExported in
  "({ " ^ name_s ^ "; "
        ^ init_s ^ "; "
        ^ min_s ^ "; "
        ^ max_s ^ "; "
        ^ isImported_s ^ "; "
        ^ isExported_s ^ ")}"

let string_of_aux_br_table (aux_br_table:aux_br_table) : string =
  let {br_name; br_targets} = aux_br_table in
  let name_s = br_name in
  let targets_s = string_of_list string_of_int br_targets in
  "({ " ^ name_s ^ "; " ^ targets_s ^ "})"

let string_of_aux_call_table (aux_call_table:aux_call_table) : string =
  let {call_name; call_init} = aux_call_table in
  let name_s = call_name in
  let s_of_nat: nat -> string = string_of_int in
  let init_s = string_of_list (string_of_opt s_of_nat) call_init in
  "({ " ^ name_s ^ "; " ^ init_s ^ "})"

let string_of_aux (aux:aux) : string =
  let {fns; globals; memory; br_tables; call_table} = aux in
  let fns_s = string_of_list string_of_aux_fn fns in
  let globals_s = string_of_list string_of_aux_global globals in
  let memory_s = string_of_aux_memory memory in
  let br_tables_s = string_of_list string_of_aux_br_table br_tables in
  let call_table_s = string_of_aux_call_table call_table in
  "({\n   "
  ^ fns_s ^ ";\n\n   "
  ^ globals_s ^ ";\n\n   "
  ^ memory_s ^ ";\n\n   "
  ^ br_tables_s ^ ";\n\n   "
  ^ call_table_s ^ ";\n})"
