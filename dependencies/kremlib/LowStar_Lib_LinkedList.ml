open Prims
type 'a cell = {
  next: 'a cell LowStar_Buffer.buffer ;
  data: 'a }
let __proj__Mkcell__item__next :
  'a . 'a cell -> 'a cell LowStar_Buffer.buffer =
  fun projectee -> match projectee with | { next; data;_} -> next
let __proj__Mkcell__item__data : 'a . 'a cell -> 'a =
  fun projectee -> match projectee with | { next; data;_} -> data
type 'a t = 'a cell LowStar_Buffer.buffer
type ('a, 'h, 'c, 'l) well_formed = Obj.t



type ('a, 'h, 'l, 'n) cells_pairwise_disjoint = Obj.t
type ('a, 'h, 'l, 'n) cells_live_freeable = Obj.t
type ('a, 'h, 'l, 'n) invariant = unit








let push : 'a . unit -> unit -> 'a t LowStar_Buffer.buffer -> 'a -> unit =
  fun r ->
    fun n ->
      fun pl ->
        fun x ->
          let h0 = FStar_HyperStack_ST.get () in
          let l = LowStar_BufferOps.op_Bang_Star pl in
          let c = { next = l; data = x } in
          let pc =
            LowStar_Monotonic_Buffer.mmalloc () c
              (FStar_UInt32.uint_to_t Prims.int_one) in
          let h1 = FStar_HyperStack_ST.get () in
          LowStar_BufferOps.op_Star_Equals pl pc;
          (let h2 = FStar_HyperStack_ST.get () in ())
let pop : 'a . unit -> unit -> 'a t LowStar_Buffer.buffer -> 'a =
  fun r ->
    fun n ->
      fun pl ->
        let l = LowStar_BufferOps.op_Bang_Star pl in
        let r1 = let uu___ = LowStar_BufferOps.op_Bang_Star l in uu___.data in
        let next = let uu___ = LowStar_BufferOps.op_Bang_Star l in uu___.next in
        let h1 = FStar_HyperStack_ST.get () in
        LowStar_BufferOps.op_Star_Equals pl next;
        LowStar_Monotonic_Buffer.free l;
        r1
let rec free_ : 'a . unit -> 'a t -> unit =
  fun n ->
    fun l ->
      let uu___ = LowStar_Monotonic_Buffer.is_null l in
      if uu___
      then ()
      else
        ((let uu___3 =
            let uu___4 = LowStar_BufferOps.op_Bang_Star l in uu___4.next in
          free_ () uu___3);
         LowStar_Monotonic_Buffer.free l)
let free : 'a . unit -> 'a t LowStar_Buffer.buffer -> unit =
  fun n ->
    fun pl ->
      (let uu___1 = LowStar_BufferOps.op_Bang_Star pl in free_ () uu___1);
      LowStar_BufferOps.op_Star_Equals pl (LowStar_Monotonic_Buffer.mnull ())
let rec length : 'a . unit -> 'a t -> FStar_UInt32.t =
  fun gn ->
    fun l ->
      let uu___ = LowStar_Monotonic_Buffer.is_null l in
      if uu___
      then FStar_UInt32.uint_to_t Prims.int_zero
      else
        (let c = LowStar_BufferOps.op_Bang_Star l in
         let next = c.next in
         let n = length () next in
         if n = (FStar_UInt32.uint_to_t (Prims.parse_int "0xffffffff"))
         then
           LowStar_Failure.failwith
             "Integer overflow in LowStar.LinkedList.length"
         else FStar_UInt32.add n (FStar_UInt32.uint_to_t Prims.int_one))
let (test : unit -> FStar_Int32.t) =
  fun uu___ ->
    let l =
      LowStar_Monotonic_Buffer.mmalloc () (LowStar_Monotonic_Buffer.mnull ())
        (FStar_UInt32.uint_to_t Prims.int_one) in
    FStar_HyperStack_ST.new_region ();
    push () () l (FStar_Int32.int_to_t Prims.int_one);
    push () () l (FStar_Int32.int_to_t Prims.int_zero);
    (let r = pop () () l in
     (let uu___4 =
        let uu___5 = LowStar_BufferOps.op_Bang_Star l in length () uu___5 in
      TestLib.checku32 uu___4 (FStar_UInt32.uint_to_t Prims.int_one));
     r)