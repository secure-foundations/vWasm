/// WARNING:
/// - Frame locals are no longer refs.
/// - Keeps a list of module instances around in context to refer to. Modules instances
///   are placed in a way that doesn't mess up the refs.
/// - eval_const was rewritten to not use eval, instead looking up the appropriate global
///   or finding the value of the constant (if necessary). Currently this is ok as if my
///   interpretation of the spec is correct, consts are just lists of 1 instruction which
///   specifies an explicit constant or a global. This is probably a future-looking thing
///   in the spec.
/// - There is no need to fix func references in ExternFunc import. See note in add_import.
/// - We fold over the tables and then the memories during initialization in add_import,
///   but I don't think that this makes in a differences from the original which does all
///   simultaneously, as the only relevant shared information is eval_const, which should
///   not be affected by memory/table init. Be aware if spec is updated though. Can be fixed
///   to be simultaneous.

(**
Evaluation semantics of the F* wasm interpreter.

@summary Eval routines
*)
module Wasm.Eval

open Wasm.Optr
open Wasm.Values
open Wasm.Types
open Wasm.Instance
open Wasm.Ast
open Wasm.Source

module Eval_numeric = Wasm.Eval_numeric
module Func = Wasm.Func
module Global = Wasm.Global
module I32 = Wasm.I32
module I64 = Wasm.I64
module I64_convert = Wasm.I64_convert
module Instance = Wasm.Instance
module L = Wasm.Lib.List
module Memory = Wasm.Memory

(* Errors *)
let s_Link = "Link"
let s_Trap = "Trap"
let s_Crash = "Crash"
let s_Exhaustion = "Exhaustion"

let e_Link = Left s_Link
let e_Trap = Left s_Trap
let e_Crash = Left s_Crash
let e_Exhaustion = Left s_Exhaustion

(* Administrative Expressions and Configurations *)
type stack 'a = list 'a

type frame =
{
  (* We need a reference to the current module instance. All the fields
     in module_inst are essentially meant to be mutable fields (which
     makes sense, really) *)
  inst: nat;
  (* Locals are only referenced from the current frame, no ref needed *)
  locals: list value;
}

noeq type code = stack value * list admin_instr

and admin_instr = phrase admin_instr'
and admin_instr' =
  | Plain of instr'
  | Invoke of func_inst
  | Trapping of string
  | Returning of stack value
  | Breaking of I32.t * stack value
  | Label of nat * list instr * code
  | Frame of nat * frame * code

noeq type context =
{
  instances: list module_inst          (* for functions/frames to ref back to *)
}

noeq type config =
{
  frame: frame;
  code: code;
  budget: nat;                           (* to model stack overflow *)
}

noeq type state =
{
  ctx: context;
  cfg: config;
  ok: bool;                            (* to model exceptions *)
  err: string;                         (* error message/type *)
  e_at: region;                        (* error location in source *)
}

let mk_frame inst locals = {inst; locals}
let mk_config inst vs es = {frame = mk_frame inst [];
                            code = vs, es;
                            budget = 300;}

let plain e = Plain e.it @@ e.at

let lookup category l (x:var) =
  let i = I32.to_int_u x.it in
  if i >= List.Tot.length l then
    e_Crash
  else
    Right (List.Tot.index l i)

let l_inst (ctx: context) (i:nat) =
  if i >= List.Tot.length ctx.instances then
    e_Crash
  else
    Right (List.Tot.index ctx.instances i)

let l_type_ (inst: module_inst) x = lookup "type" inst.types_ x
let l_func (inst: module_inst) x = lookup "function" inst.funcs_ x
let l_table (inst: module_inst) x = lookup "table" inst.tables_ x
let l_memory (inst: module_inst) x = lookup "memory" inst.memories_ x
let l_global (inst: module_inst) x = lookup "global" inst.globals_ x
let l_local (frame: frame) x = lookup "local" frame.locals x

(* TODO: Most code does not distinguish between trap and crash here *)
let l_elem inst x i at =
  match l_table inst x with
  | Right tbl ->
    (match Instance.tb_load tbl i with
     | Right Instance.Uninitialized -> e_Trap
     | Right f -> Right f
     | _ -> e_Trap)
  | Left e -> Left e

let l_func_elem inst x i at =
  match l_elem inst x i at with
  | Right (FuncElem f) -> Right f
  | Left e -> e_Crash

let take n (vs: stack 'a) at =
  match L.take n vs with
  | Right vs' -> Right vs'
  | Left _ -> e_Crash

let drop n (vs: stack 'a) at =
  match L.drop n vs with
  | Right vs' -> Right vs'
  | Left _ -> e_Crash

let replace_elem (n:nat) (xs: list 'a) e' at =
  if n < List.Tot.length xs then (
    let l, e, r = List.Tot.split3 xs n in
    Right (l @ [e'] @ r)
  ) else (
    e_Crash
  )

(* Evaluation *)

(* Define a stateful monad to simplify defining the instruction semantics *)
let st (a:Type) = state -> a * state

unfold
let return (#a:Type) (x:a): st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b): st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok = s0.ok && s1.ok && s2.ok}

(* Getters *)
let get: st state =
  fun s -> s, s

let status: st bool =
 fun s -> s.ok, s

let get_cfg: st config =
  fun s -> s.cfg, s

let get_ctx: st context =
  fun s -> s.ctx, s

let get_inst_list: st (list module_inst) =
  fun s -> s.ctx.instances, s

let get_frame: st frame =
  fun s -> s.cfg.frame, s

let get_frame_inst: st (optr module_inst) =
  ctx <-- get_ctx;
  fr <-- get_frame;
  return (l_inst ctx fr.inst)

let get_code: st code =
  fun s -> s.cfg.code, s

let get_budget: st int =
  fun s -> s.cfg.budget, s


(* Setters *)
let set (s:state): st unit =
  fun _ -> (), s

let failwith (err: string) (at: region): st unit =
  s <-- get;
  if s.ok = true then
    set ({s with ok = false; err = err; e_at = at})
  else
    return ()

let set_ctx (ctx: context): st unit =
  fun s -> (), {s with ctx = ctx}

let set_inst_list (instances': list module_inst) =
  ctx <-- get_ctx;
  set_ctx ({ctx with instances = instances'})

let set_frame_inst (m: module_inst) (at: region): st unit =
  fr <-- get_frame;
  insts <-- get_inst_list;
  match replace_elem fr.inst insts m at with
  | Right insts' ->
    set_inst_list insts'
  | Left _ ->
    failwith s_Crash at

let set_cfg (cfg: config): st unit =
  fun s -> (), {s with cfg = cfg}

let set_frame (f:frame): st unit =
  cfg <-- get_cfg;
  set_cfg ({cfg with frame = f})

let set_code (c:code): st unit =
  cfg <-- get_cfg;
  set_cfg ({cfg with code = c})

let set_prep_code (vs':stack value) (es':list admin_instr): st unit =
  c <-- get_code;
  set_code (vs', es' @ snd c)

let set_budget (b: nat): st unit =
  cfg <-- get_cfg;
  set_cfg ({cfg with budget = b})


(*
 * Conventions:
 *   e   : instr
 *   v   : value
 *   es  : list instr
 *   vs  : stack value
 *   cfg : config
 *   ctx : context
 *   c   : code
 *   s   : state
 *)

(* Executing 'plain' instructions
 * We require the instruction being executed
 * to have been removed from the instruction list *)

let step_ins (e: instr): st unit =
  s <-- get;
  c <-- get_code;
  cfg <-- get_cfg;
  fr <-- get_frame;
  oinst <-- get_frame_inst;
  vs <-- return (fst c);

  if s.ok = false then return () else (
  match e.it, vs with
  | Unreachable, vs ->
    set_prep_code vs [Trapping "unreachable executed" @@ e.at]

  | Nop, vs ->
    set_prep_code vs []

  | Block (ts, es'), vs ->
    set_prep_code vs [Label (List.length ts, [], ([], List.Tot.map plain es')) @@ e.at]

  | Loop (ts, es'), vs ->
    set_prep_code vs [Label (0, [e.it @@ e.at], ([], List.Tot.map plain es')) @@ e.at]

  | If (ts, es1, es2), I32 i :: vs' ->
    if i = I32.zero then
      set_prep_code vs' [Plain (Block (ts, es2)) @@ e.at]
    else
      set_prep_code vs' [Plain (Block (ts, es1)) @@ e.at]

  | If (ts, es1, es2), vs ->
    failwith s_Crash e.at

  | Br x, vs ->
    set_prep_code [] [Breaking (x.it, vs) @@ e.at]

  | BrIf x, I32 i :: vs' ->
    if i = I32.zero then
      set_prep_code vs' []
    else
      set_prep_code vs' [Plain (Br x) @@ e.at]

  | BrIf x, vs ->
    failwith s_Crash e.at

  | BrTable (xs, x), I32 i :: vs' ->
    (match List.Tot.nth xs (I32.to_int_u i) with
     | Some v ->
       set_prep_code vs' [Plain (Br v) @@ e.at]
     | None ->
       set_prep_code vs' [Plain (Br x) @@ e.at]
    )

  | BrTable (xs, x), vs ->
    failwith s_Crash e.at

  | Return, vs ->
    set_prep_code vs [Returning vs @@ e.at]

  | Call x, vs ->
    if Left? oinst then failwith s_Crash e.at else
    (match l_func (Right?.v oinst) x with
     | Right f ->
       set_prep_code vs [Invoke f @@ e.at]
     | Left _ ->
       failwith s_Crash e.at
    )

  | CallIndirect x, I32 i :: vs ->
    if Left? oinst then failwith s_Crash e.at else (
    let inst = Right?.v oinst in
    let func = l_func_elem inst (I32.zero @@ e.at) i e.at in
    let ty = l_type_ inst x in
    match ty, func with
    | Right t, Right f ->
      if t <> Func.type_of f then
        set_prep_code vs [Trapping "indirect call type mismatch" @@ e.at]
      else
        set_prep_code vs [Invoke f @@ e.at]
    | _ ->
      failwith s_Crash e.at
    )

  | CallIndirect x, vs ->
    failwith s_Crash e.at

  | Drop, v :: vs' ->
    set_prep_code vs' []

  | Drop, [] ->
    failwith s_Crash e.at

  | Select, I32 i :: v2 :: v1 :: vs' ->
    if i = I32.zero then
      set_prep_code (v2 :: vs') []
    else
      set_prep_code (v1 :: vs') []

  | Select, vs ->
    failwith s_Crash e.at

  | LocalGet x, vs ->
    let l = l_local fr x in
    (match l with
     | Right l' ->
       set_prep_code (l' :: vs) []
     | Left _ ->
       failwith s_Crash e.at
    )

  | LocalSet x, v :: vs' ->
    if Left? oinst then failwith s_Crash e.at else (
    let inst = Right?.v oinst in
    let replaced = replace_elem (I32.to_int_u x.it) fr.locals v e.at in
    match replaced with
    | Right locals' ->
      set_frame ({fr with locals = locals'});;
      set_prep_code vs' []
    | _ ->
      failwith s_Crash e.at
    )

  | LocalSet x, [] ->
    failwith s_Crash e.at

  | LocalTee x, v :: vs' ->
    if Left? oinst then failwith s_Crash e.at else (
    let inst = Right?.v oinst in
    let replaced = replace_elem (I32.to_int_u x.it) fr.locals v e.at in
    match replaced with
    | Right locals' ->
      set_frame ({fr with locals = locals'});;
      set_prep_code (v :: vs') []
    | _ ->
      failwith s_Crash e.at
    )

  | LocalTee x, [] ->
    failwith s_Crash e.at

  | GlobalGet x, vs ->
    if Left? oinst then failwith s_Crash e.at else (
    let inst = Right?.v oinst in
    let g = l_global inst x in
    match g with
    | Right g' ->
      set_prep_code ((Global.load g') :: vs) []
    | _ ->
      failwith s_Crash e.at
    )

  | GlobalSet x, v :: vs' ->
    if Left? oinst then failwith s_Crash e.at else (
    let inst = Right?.v oinst in
    let og = l_global inst x in
    match og with
    | Left _ ->
      failwith s_Crash e.at
    | Right g ->
      let og' = Global.store g v in (
      match og' with
      | Right g' ->
        let globals' = Right?.v (replace_elem (I32.to_int_u x.it) inst.globals_ g' e.at) in
        let inst' = {inst with globals_ = globals'} in
        set_frame_inst inst' e.at;;
        set_prep_code vs' []
      | _ ->
        failwith s_Crash e.at
      )
    )

  | GlobalSet x, [] ->
    failwith s_Crash e.at

  (* Recall we only have one linear memory per instance atm *)
  | Load ({offset; ty; sz; align}), I32 i :: vs' ->
    if Left? oinst then failwith s_Crash e.at else (
    let idx = I32.zero in
    let inst = Right?.v oinst in
    let omem = l_memory inst (idx @@ e.at) in
      if Left? omem then failwith s_Crash e.at else (
        let mem = Right?.v omem in
        let addr = I64_convert.extend_i32_u i in
        let ov =
          (match sz with
           | None ->
             Memory.load_value mem addr offset ty
           | Some (sz, ext) ->
             Memory.load_packed sz ext mem addr offset ty
          )
        in
        match ov with
        | Right v ->
          set_prep_code (v :: vs') []
        | Left err ->
          set_prep_code vs' [Trapping "memory error" @@ e.at]
      )
    )

  | Load _, vs ->
    failwith s_Crash e.at

  | Store ({offset; sz; ty; align}), v :: I32 i :: vs' ->
    if Left? oinst then failwith s_Crash e.at else (
    let idx = I32.zero in
    let inst = Right?.v oinst in
    let omem = l_memory inst (idx @@ e.at) in
      if Left? omem then failwith s_Crash e.at else (
        let mem = Right?.v omem in
        let addr = I64_convert.extend_i32_u i in
        let omem' =
          (match sz with
           | None ->
             Memory.store_value mem addr offset v
           | Some sz ->
             Memory.store_packed sz mem addr offset v
          )
        in
        match omem' with
        | Right mem' ->
          let memories' = Right?.v (replace_elem (I32.to_int_u idx) inst.memories_ mem' e.at) in
          let inst' = {inst with memories_ = memories'} in
          set_frame_inst inst' e.at;;
          set_prep_code vs' []
        | _ ->
          set_prep_code vs' [Trapping "memory error" @@ e.at]
      )
    )

  | Store _, vs ->
    failwith s_Crash e.at

  | MemorySize, vs ->
    if Left? oinst then failwith s_Crash e.at else (
    let idx = I32.zero in
    let inst = Right?.v oinst in
    let omem = l_memory inst (idx @@ e.at) in
    match omem with
    | Right mem ->
      set_prep_code (I32 (Memory.size mem) :: vs) []
    | _ ->
      failwith s_Crash e.at
    )

  | MemoryGrow, I32 delt :: vs' ->
    if Left? oinst then failwith s_Crash e.at else (
    let idx = I32.zero in
    let inst = Right?.v oinst in
    let omem = l_memory inst (idx @@ e.at) in
    match omem with
    | Right mem ->
      let omem' = Memory.grow mem delt in
      (match omem' with
       | Right mem' ->
         let memories' = Right?.v (replace_elem (I32.to_int_u idx) inst.memories_ mem' e.at) in
         let inst' = {inst with memories_ = memories'} in
         set_frame_inst inst' e.at;;
         set_prep_code (I32 (Memory.size mem) :: vs') []
       | _ ->
         set_prep_code (I32 (I32.of_int_s (-1)) :: vs') []
      )
    | _ ->
      failwith s_Crash e.at
    )

  | MemoryGrow, vs ->
    failwith s_Crash e.at

  | Const v, vs ->
    set_prep_code (v.it :: vs) []

  | Test testop, v :: vs' ->
    (match (Eval_numeric.eval_testop testop v) with
     | Right b ->
       set_prep_code (value_of_bool b :: vs') []
     | _ ->
       set_prep_code vs' [Trapping "numeric error" @@ e.at]
    )

  | Test testop, [] ->
    failwith s_Crash e.at

  | Compare relop, v2 :: v1 :: vs' ->
    (match (Eval_numeric.eval_relop relop v1 v2) with
     | Right b ->
       set_prep_code (value_of_bool b :: vs') []
     | _ ->
       set_prep_code vs' [Trapping "numeric error" @@ e.at]
    )

  | Compare relop, v1 :: [] ->
    failwith s_Crash e.at

  | Compare relop, [] ->
    failwith s_Crash e.at

  | Unary unop, v :: vs' ->
    (match (Eval_numeric.eval_unop unop v) with
     | Right v' ->
       set_prep_code (v' :: vs') []
     | _ ->
       set_prep_code vs' [Trapping "numeric error" @@ e.at]
    )

  | Unary unop, [] ->
    failwith s_Crash e.at

  | Binary binop, v2 :: v1 :: vs' ->
    (match (Eval_numeric.eval_binop binop v1 v2) with
     | Right v' ->
       set_prep_code (v' :: vs') []
     | _ ->
       set_prep_code vs' [Trapping "numeric error" @@ e.at]
    )

  | Binary binop, v1 :: [] ->
    failwith s_Crash e.at

  | Binary binop, [] ->
    failwith s_Crash e.at

  | Convert cvtop, v :: vs' ->
    (match (Eval_numeric.eval_cvtop cvtop v) with
     | Right v' ->
       set_prep_code (v' :: vs') []
     | _ ->
       set_prep_code vs' [Trapping "numeric error" @@ e.at]
    )

  | Convert cvtop, [] ->
    failwith s_Crash e.at
  )

(* Executing admin instructions.
 * Also requires e to have been removed from
 * the instruction list *)

let rec step (e: admin_instr): st unit =
  s <-- get;
  c <-- get_code;
  cfg <-- get_cfg;
  ctx <-- get_ctx;
  fr <-- get_frame;
  oinst <-- get_frame_inst;
  vs <-- return (fst c);

  if s.ok = false then return () else (
  match e.it, vs with
  | Plain ee, vs ->
    step_ins (ee @@ e.at)

  | Trapping msg, vs ->
    failwith s_Crash e.at

  | Returning vs', vs ->
    failwith s_Crash e.at

  | Breaking (k, vs'), vs ->
    failwith s_Crash e.at

  | Label (n, es0, (vs', [])), vs ->
    set_prep_code (vs' @ vs) []

  | Label (n, es0, (vs', ({it = Trapping msg; at}) :: es')), vs ->
    set_prep_code vs [Trapping msg @@ at]

  | Label (n, es0, (vs', ({it = Returning vs0; at}) :: es')), vs ->
    set_prep_code vs [Returning vs0 @@ at]

  | Label (n, es0, (vs', ({it = Breaking (i, vs0); at}) :: es')), vs ->
    if i = I32.zero then (
      match take n vs0 at with
      | Right vv ->
        set_prep_code (vv @ vs) (List.Tot.map plain es0)
      | Left _ ->
        failwith s_Crash e.at
    ) else (
      set_prep_code vs [Breaking (I32.sub i I32.one, vs0) @@ at]
    )

  (* Any changes to frame's module_inst should remain,
     any changes to frame's locals should remain,
     any changes to ctx's module instances list should remain,
     any changes to cfg's frame gets undone,
     any changes to cfg's code gets overwritten,
     any changes to cfg's budget gets undone,
     any changes to ctx/cfg fields gets undone,
     any changes to state's ok/err fields should remain.
     See Frame and Invoke as well *)
  | Label (n, es0, code'), vs ->
    if Nil? (snd code') then (
      failwith s_Crash e.at
    ) else (
      set_code (fst code', List.Tot.tl (snd code'));;
      step (List.Tot.hd (snd code'));;
      code'' <-- get_code;
      set_code (vs, [Label (n, es0, code'') @@ e.at] @ snd c)
    )

  | Frame (n, frame', (vs', [])), vs ->
    set_prep_code (vs' @ vs) []

  | Frame (n, frame', (vs', ({it = Trapping msg; at}) :: es')), vs ->
    set_prep_code vs [Trapping msg @@ at]

  | Frame (n, frame', (vs', ({it = Returning vs0; at}) :: es')), vs ->
    (match take n vs0 at with
     | Right vv ->
       set_prep_code (vv @ vs) []
     | Left _ ->
       failwith s_Crash e.at
    )

  (* Host functions can't modify locals, so the initial frame remains
     the same, so we can just write it back after stepping *)
  (* Check budget semantics *)
  | Frame (n, frame', code'), vs ->
    if Nil? (snd code') then (
      failwith s_Crash e.at
    ) else if cfg.budget = 0 then (
      failwith s_Exhaustion e.at
    ) else (
      set_frame frame';;
      set_code (fst code', List.Tot.tl (snd code'));;
      set_budget (cfg.budget - 1);;
      step (List.Tot.hd (snd code'));;
      fr' <-- get_frame;
      code'' <-- get_code;
      set_frame fr;;
      set_code (vs, [Frame (n, fr', code'') @@ e.at] @ snd c)
    )

  (* TODO: Cannot invoke HostFuncs yet *)
  | Invoke func, vs ->
    if cfg.budget = 0 then (
      failwith s_Crash e.at
    ) else (
      let FuncType (ins, out) = Func.type_of func in
      let n = List.Tot.length ins in
      if n > List.Tot.length vs then failwith s_Crash e.at else (
        let args, vs' = List.Tot.splitAt n vs in
        match func with
        | Func.AstFunc (t, inst', f) ->
          (* inst' is a nat *)
          let locals' = (List.Tot.rev args) @ (List.Tot.map default_value f.it.flocals) in
          let code' = ([], [Plain (Block (out, f.it.body)) @@ f.at]) in
          if inst' >= List.Tot.length ctx.instances then failwith s_Crash e.at else (
            let frame' = {inst = inst'; locals = locals'} in
            set_prep_code vs' [Frame (List.length out, frame', code') @@ e.at]
          )
        | Func.HostFunc (t, f) ->
          failwith "Unimplemented" e.at
      )
    )
  )

let rec eval (fuel: nat): st unit =
  s <-- get;
  c <-- get_code;

  if s.ok = false then return () else (
  match fuel, c with
  | 0, _ ->
    return ()
  | n, (vs, []) ->
    return ()
  | n, (vs, (e :: es)) ->
    set_code (fst c, List.Tot.tl (snd c));;
    step e;;
    eval (fuel - 1)
  )


(* Initialization Routines *)

(* Functions & Constants *)

let invoke (fuel: nat) (func: func_inst) (vs: list value): st unit =
  let at =
    (match func with
     | Func.AstFunc (_, _, f) -> f.at
     | _ -> no_region
    )
  in
  let FuncType (ins, out) = Func.type_of func in
  if List.Tot.length vs <> List.Tot.length ins then
    failwith s_Crash at
  else (
    inst_list <-- get_inst_list;
    set_inst_list (inst_list @ [empty_module_inst]);;
    let idx = List.Tot.length inst_list in
    let cfg = mk_config idx (List.Tot.rev vs) [Invoke func @@ at] in
    set_cfg cfg;;
    eval fuel
  )

(* TODO: Rewritten to not use evals *)
let eval_const (inst: module_inst) (const: const): optr value =
  if List.Tot.length const.it <> 1 then e_Crash else (
  match (List.Tot.hd const.it).it with
  | Const v ->
    Right v.it
  | GlobalGet x ->
    let og = l_global inst x in
    (match og with
     | Right g ->
       Right (Global.load g)
     | _ ->
       e_Crash
    )
  | _ ->
    e_Crash
  )


(* Modules *)

let create_func (inst_ref: nat) (inst: module_inst) (f: func): optr func_inst =
  let oty = l_type_ inst f.it.ftype in
  match oty with
  | Right ty ->
    Right (Func.alloc ty (inst_ref) f)
  | _ ->
    e_Crash

let create_table (inst: module_inst) (tab: table): optr table_inst =
  let {ttype} = tab.it in
  Instance.tb_alloc ttype

let create_memory (inst: module_inst) (mem: memory): optr memory_inst =
  let {mtype} = mem.it in
  Memory.alloc mtype

let create_global (inst: module_inst) (glob: global): optr global_inst =
  let {gtype; value} = glob.it in
  let ov = eval_const inst value in
  match ov with
  | Right v ->
    Global.alloc gtype v
  | _ ->
    e_Crash

let create_export (inst: module_inst) (ex: export): optr export_inst =
  let {name; edesc} = ex.it in
  let oext =
    match edesc.it with
    | FuncExport x -> o_fmap ExternFunc (l_func inst x)
    | TableExport x -> o_fmap ExternTable (l_table inst x)
    | MemoryExport x -> o_fmap ExternMemory (l_memory inst x)
    | GlobalExport x -> o_fmap ExternGlobal (l_global inst x)
  in
  match oext with
  | Right ext ->
    Right (name, ext)
  | _ ->
    e_Crash

(* NB: Not needed, see later comment in init_module *)
(*
let init_func (inst_ref: nat) (inst: module_inst) (func: func_inst) =
  match func with
  | Func.AstFunc (ft, r, fn) ->
    Right (Func.AstFunc (ft, inst_ref, fn))
  | _ ->
    e_Crash
*)

let init_table (seg: table_segment) (inst: module_inst) =
  let {index; seg_offset = econst; init} = seg.it in
  let otab = l_table inst index in
  let oconst = eval_const inst econst in
  if (Left? otab) || (Left? oconst) then e_Crash else (
    let tab = Right?.v otab in
    let const = Right?.v oconst in
    match const with
    | I32 offset ->
      let end_  = I32.add offset (I32.of_int_u (List.Tot.length init)) in
      let bound = Instance.tb_size tab in
      if (I32.lt_u bound end_) || (I32.lt_u end_ offset) then
        e_Link
      else (
        let ofuncelems = L.map_ex (fun x -> o_fmap FuncElem (l_func inst x)) init in
        match ofuncelems with
        | Right funcelems ->
          (match Instance.tb_blit tab offset funcelems with
           | Right tb_new ->
             let tbs = Right?.v (replace_elem (I32.to_int_u index.it) inst.tables_ tb_new no_region) in
             Right ({inst with tables_ = tbs})
           | _ ->
             e_Crash
          )
        | _ ->
          e_Crash
      )
    | _ ->
      e_Crash
  )

let init_memory (seg: memory_segment) (inst: module_inst) =
  let {index; seg_offset = econst; init} = seg.it in
  let omem = l_memory inst index in
  let oconst = eval_const inst econst in
  if (Left? omem) || (Left? oconst) then e_Crash else (
    let mem = Right?.v omem in
    let const = Right?.v oconst in
    match const with
    | I32 offset' ->
      (* TODO: Why not I64 offset? Check spec. *)
      let offset = I64_convert.extend_i32_u offset' in
      let end_ = I64.add offset (I64.of_int_u (List.Tot.length init)) in
      let bound = Memory.bound mem in
      if (I64.lt_u bound end_) || (I64.lt_u end_ offset) then
        e_Link
      else (
        match Memory.store_bytes mem offset init with
        | Right mem_new ->
          let mems = Right?.v (replace_elem (I32.to_int_u index.it) inst.memories_ mem_new no_region) in
          Right ({inst with memories_ = mems})
        | _ ->
          e_Crash
      )
    | _ ->
      e_Crash
  )

let add_import (m: module_) (ext: extern) (im: import) (oinst: optr module_inst): optr module_inst =
  if Left? oinst then e_Crash else (
    let inst = Right?.v oinst in
    match import_type m im with
    | Right ity ->
      if not (match_extern_type (extern_type_of ext) ity) then
        e_Link
      else (
        (* NB: There is no need to fix the func instance ref, because for such a func instance
         * to exist, the instance it refers to is already in existence, so as long as we only
         * append to the instance list, the ref numbering never changes.
         *)
        match ext with
        | ExternFunc func ->
          Right ({inst with funcs_ = func :: inst.funcs_})
        | ExternTable tab ->
          Right ({inst with tables_ = tab :: inst.tables_})
        | ExternMemory mem ->
          Right ({inst with memories_ = mem :: inst.memories_})
        | ExternGlobal glob ->
          Right ({inst with globals_ = glob :: inst.globals_})
      )
    | _ ->
      e_Crash
  )

let init_module (m: module_) (exts: list extern): st unit =
  inst_list <-- get_inst_list;

  let {imports; tables; memories; globals; funcs; types;
       exports; elems; data; start} = m.it
  in
  if List.Tot.length exts <> List.Tot.length imports then
    failwith s_Link no_region
  else (
    (* NB: Have to fold_right to maintain the ordering of the imports so that the
     * indexing is correctly preserved in the original implementation, we have no
     * fold_right2 so here we just append to the list in add_import.
     *)
    let oinst0 = L.fold_right2 (add_import m) exts imports (Right empty_module_inst) in
    match oinst0 with
    | Right inst0 ->
      let tys = List.Tot.map (fun type_ -> type_.it) types in
      let inst0 = {inst0 with types_ = tys} in
      let idx = List.Tot.length inst_list in
      let ofs' = L.map_ex (create_func idx inst0) funcs in
      let otbs' = L.map_ex (create_table inst0) tables in
      let omems' = L.map_ex (create_memory inst0) memories in
      let ogbls' = L.map_ex (create_global inst0) globals in
      (match ofs', otbs', omems', ogbls' with
       | Right fs', Right tbs', Right mems', Right gbls' ->
         let inst1 = {inst0 with
                      funcs_ = inst0.funcs_ @ fs';
                      tables_ = inst0.tables_ @ tbs';
                      memories_ = inst0.memories_ @ mems';
                      globals_ = inst0.globals_ @ gbls';
                     }
         in
         let oexps = L.map_ex (create_export inst1) exports in
         if Left? oexps then failwith (Left?.v oexps) no_region else (
           (* NB: No need to initialize funcs, the ref idx will already be right
            * Also, just folding over table initializers then memory initializers
            * I don't think this makes a difference because the only shared
            * information is in eval_const, which is not affected by the
            * global/memory initialization routines.
            *)
           let inst2 = {inst1 with exports_ = Right?.v oexps} in
           let oinst3 = List.Tot.fold_left (fun oinst seg -> o_bind (init_table seg) oinst) (Right inst2) elems in
           let oinst4 = List.Tot.fold_left (fun oinst seg -> o_bind (init_memory seg) oinst) oinst3 data in
           match oinst4 with
           | Right inst ->
             set_inst_list (inst_list @ [inst])
           | Left err ->
             failwith err no_region
         )

       | Left err, _, _, _ ->
         failwith err no_region
       | _, Left err, _, _ ->
         failwith err no_region
       | _, _, Left err, _ ->
         failwith err no_region
       | _, _, _, Left err ->
         failwith err no_region
      )
    | _ ->
      failwith s_Crash no_region
  )

let run_instance (fuel: nat) (inst_ref: nat) (start: option var): st unit =
  inst_list <-- get_inst_list;
  if inst_ref >= List.Tot.length inst_list then
    failwith s_Crash no_region
  else (
    let inst = List.Tot.index inst_list inst_ref in
    match start with
    | Some v ->
      (match l_func inst v with
       | Right f_inst ->
         invoke fuel f_inst []
       | _ ->
         failwith s_Crash no_region
      )
    | None ->
      return ()
  )
