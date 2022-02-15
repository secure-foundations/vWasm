/// WARNING:
/// - Memory is now a Map with functional update instead of an array (in the original
///   implementation).
/// - We assume that a memory may always be allocated (enough space).

(**
Representation of an instantiation of a memory.

@summary Memory instances.
*)
module Wasm.Memory

open Wasm.Optr

open Wasm.Types
open Wasm.Values

open Words_s
open Opaque_s

module I32 = Wasm.I32
module I32_convert = Wasm.I32_convert
module I64 = Wasm.I64
module I64_convert = Wasm.I64_convert
module Types = Wasm.Types
module Values = Wasm.Values

private let op_String_Access = Map.sel
private let op_String_Assignment = Map.upd

/// ####################
/// DECLARATIONS
/// ####################
type size_ = I32.t
type address = I64.t
type offset = I32.t

type pack_size =
  | Pack8
  | Pack16
  | Pack32
type extension =
  | SX
  | ZX

type t_byte = nat8
type memory' = Map.t nat t_byte
noeq type memory = {content: memory'; mem_sz: address; mem_max : option size_}
type t = memory

let e_Type = Left "Type"
let e_Bounds = Left "Bounds"
let e_SizeOverflow = Left "SizeOverflow"
let e_SizeLimit = Left "SizeLimit"
let e_OutOfMemory = Left "OutOfMemory"

val page_size : I64.t
val packed_size : pack_size -> Tot int

val alloc : memory_type -> Tot (optr memory)
val type_of : memory -> Tot memory_type
val size : memory -> Tot size_
val bound : memory -> Tot address
val grow : memory -> size_ -> Tot (optr memory)

val load_byte : memory -> address -> Tot (optr t_byte)
val store_byte : memory -> address -> t_byte -> Tot (optr memory)
val load_bytes : memory -> address -> (n: nat) -> Tot (l: optr (list t_byte){Right? l ==> List.Tot.length (Right?.v l) = n})
val store_bytes : memory -> address -> list t_byte -> Tot (optr memory)

val load_value :
  memory -> address -> offset -> value_type -> Tot (optr value)
val store_value :
  memory -> address -> offset -> value -> Tot (optr memory)
val load_packed :
  pack_size -> extension -> memory -> address -> offset -> value_type -> Tot (optr value)
val store_packed :
  pack_size -> memory -> address -> offset -> value -> Tot (optr memory)

/// ####################
/// DEFINITIONS
/// ####################
let page_size = I64.of_int_u 0x10000

let packed_size packed =
  match packed with
  | Pack8 -> 1
  | Pack16 -> 2
  | Pack32 -> 4

let within_limits n mx =
  match mx with
  | None -> true
  | Some max -> I32.le_u n max

(* NB: No OOM option *)
let create n: optr (memory' * address) =
  if I32.gt_u n (I32.of_int_u 0x10000) then e_SizeOverflow else (
    let size = I64.mul (I64_convert.extend_i32_u n) page_size in
    Right (Map.const 0, size)
  )

(* NB: Gives e_SizeLimit error if not within_limits, instead of
 * throwing an assert failure as in the original
 *)
let alloc (MemoryType {min; max}) =
  if within_limits min max then (
    match create min with
    | Right (mem', size) ->
      Right ({content = mem'; mem_sz = size; mem_max = max})
    | Left err ->
      Left err
  ) else e_SizeLimit

let content mem = mem.content

let bound mem = mem.mem_sz

#push-options "--z3cliopt smt.arith.nl=true"
let size mem = I32_convert.wrap_i64 (Right?.v (I64.div_u (bound mem) page_size))
#pop-options

let type_of mem =
  MemoryType ({min = size mem; max = mem.mem_max})

let grow mem delta =
  let old_size = size mem in
  let new_size = I32.add old_size delta in
  if I32.gt_u old_size new_size then e_SizeOverflow else (
    if not (within_limits new_size mem.mem_max) then e_SizeLimit else (
      let new_size' = I64.mul (I64_convert.extend_i32_u new_size) page_size in
      Right ({mem with mem_sz = new_size'})
    )
  )

let load_byte mem a =
  let ct = content mem in
  let ptr = I64.to_int_u a in
  if I64.lt_u a (bound mem) then
    Right (ct.[ptr])
  else
    e_Bounds

let store_byte mem a b =
  let ct = content mem in
  let ptr = I64.to_int_u a in
  if I64.lt_u a (bound mem) then
    Right ({mem with content = (ct.[ptr] <- b)})
  else
    e_Bounds

let rec load_bytes_loop__ (ct: memory') (ptr: nat) (n: nat) acc
  :(l: (list nat8){List.Tot.length l = n + List.Tot.length acc}) =
  if n = 0 then
    acc
  else
    load_bytes_loop__ ct ptr (n - 1) (ct.[ptr + n - 1] :: acc)

let load_bytes mem a n =
  let ct = content mem in
  let ptr = I64.to_int_u a in
  let bnd = bound mem in
  if I64.lt_u a bnd && I64.gt_u (I64.sub bnd a) (I64.of_int_u n) then (
    Right (load_bytes_loop__ ct ptr n [])
  ) else
    e_Bounds

let rec store_bytes_loop__ (bs: list t_byte) (ct:memory') (ptr: nat) =
  match bs with
  | [] -> ct
  | b :: bs -> store_bytes_loop__ bs (ct.[ptr] <- b) (ptr + 1)

let store_bytes mem a bs =
  let ct = content mem in
  let ptr = I64.to_int_u a in
  let bnd = bound mem in
  let n = List.Tot.length bs in
  if I64.lt_u a bnd && I64.gt_u (I64.sub bnd a) (I64.of_int_u n) then (
    Right ({mem with content = store_bytes_loop__ bs ct ptr})
  ) else
    e_Bounds

let effective_address a o =
  let ea = I64.add a (I64_convert.extend_i32_u o) in
  if I64.lt_u ea a then
    e_Bounds
  else
    Right ea

let load_value mem a o t =
  match effective_address a o with
  | Right ea ->
    let obs = load_bytes mem ea (Types.size t) in
    if Left? obs then Left (Left?.v obs) else (
      (* NB: We unfold obs here else FStar couldn't seem to prove it *)
      let bs = Right?.v obs in
      (match t with
       | I32Type -> Right (I32 (I32.of_bytes bs))
       | I64Type -> Right (I64 (I64.of_bytes bs))
       | F32Type -> Right (F32 (F32.of_bytes bs))
       | F64Type -> Right (F64 (F64.of_bytes bs))
      )
    )
  | Left err ->
    Left err

let store_value mem a o v =
  let bs =
    match v with
    | I32 x -> I32.to_bytes x
    | I64 x -> I64.to_bytes x
    | F32 x -> F32.to_bytes x
    | F64 x -> F64.to_bytes x
  in
  match effective_address a o with
  | Right ea ->
    store_bytes mem ea bs
  | Left err ->
    Left err

let extend ext n x =
  match ext with
  | ZX -> x
  | SX ->
    let sh = I64.of_int_u (64 - 8 `op_Multiply` n) in
    I64.shr_s (I64.shl x sh) sh

let rec pad_zeros__ (n: nat) (ls: list t_byte)
  : (l: (list t_byte){List.Tot.length l = n + List.Tot.length ls}) =
  if n = 0 then ls else pad_zeros__ (n - 1) (0 :: ls)

let load_packed sz ext mem a o t =
  let n = packed_size sz in
  if n > Types.size t then e_Type else (
    match effective_address a o with
    | Right ea ->
      assert (0 <= n && n <= 8);
      let obs = load_bytes mem ea n in
      if Left? obs then Left (Left?.v obs) else (
        let bs = Right?.v obs in
        let pbs = pad_zeros__ (8 - n) bs in
        let x = extend ext n (I64.of_bytes pbs) in
        (match t with
         | I32Type -> Right (I32 (I32_convert.wrap_i64 x))
         | I64Type -> Right (I64 x)
         | _ -> e_Type
        )
      )
    | Left err ->
      Left err
  )

let store_packed sz mem a o v =
  let n = packed_size sz in
  let csz = Types.size (Values.type_of v) in
  if n > csz then e_Type else (
    match effective_address a o with
    | Right ea ->
      (match v with
       | I32 x ->
         let bs = snd (List.Tot.splitAt (csz - n) (I32.to_bytes x)) in
         store_bytes mem ea bs
       | I64 x ->
         let bs = snd (List.Tot.splitAt (csz - n) (I64.to_bytes x)) in
         store_bytes mem ea bs
       | _ -> e_Type
      )
    | Left err ->
      Left err
  )
