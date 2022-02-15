open Prims
type 's zero_free = unit
type 's well_formed = unit
type t =
  | S of C.char FStar_Seq_Base.seq 
let uu___is_S uu___ = match uu___ with | S _ -> true | _ -> false


let (get : t -> FStar_UInt32.t -> C.char) =
  fun s ->
    fun l -> FStar_Seq_Base.index (__proj__S__item__s s) (FStar_UInt32.v l)

let (of_literal : Prims.string -> t) = fun uu___ -> Prims.admit ()
let (op_Bang_Dollar : Prims.string -> t) = of_literal
let (print : t -> unit) = fun uu___ -> ()
let (strlen : t -> FStar_UInt32.t) = fun uu___ -> Prims.admit ()
let (memcpy :
  FStar_UInt8.t LowStar_Buffer.buffer -> t -> FStar_UInt32.t -> unit) =
  fun uu___ -> fun uu___1 -> fun uu___2 -> ()