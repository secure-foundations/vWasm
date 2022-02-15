open Prims
type 'a t =
  {
  ptr: 'a LowStar_Lib_LinkedList.t LowStar_Buffer.buffer ;
  v: unit LowStar_Buffer.buffer ;
  r: unit ;
  spine_rid: unit ;
  ptr_v_rid: unit }
let __proj__Mkt__item__ptr :
  'a . 'a t -> 'a LowStar_Lib_LinkedList.t LowStar_Buffer.buffer =
  fun projectee ->
    match projectee with | { ptr; v; r; spine_rid; ptr_v_rid;_} -> ptr
let __proj__Mkt__item__v : 'a . 'a t -> unit LowStar_Buffer.buffer =
  fun projectee ->
    match projectee with | { ptr; v; r; spine_rid; ptr_v_rid;_} -> v



type ('a, 'h, 'll) invariant = unit







let create_in : 'a . unit -> 'a t =
  fun r ->
    FStar_HyperStack_ST.new_region ();
    FStar_HyperStack_ST.new_region ();
    (let ptr =
       LowStar_Monotonic_Buffer.mmalloc ()
         (LowStar_Monotonic_Buffer.mnull ())
         (FStar_UInt32.uint_to_t Prims.int_one) in
     let v =
       LowStar_Monotonic_Buffer.mmalloc () ()
         (FStar_UInt32.uint_to_t Prims.int_one) in
     { ptr; v; r = (); spine_rid = (); ptr_v_rid = () })
let push : 'a . 'a t -> 'a -> unit =
  fun ll ->
    fun x ->
      LowStar_BufferOps.op_Bang_Star ll.v;
      LowStar_Lib_LinkedList.push () () ll.ptr x;
      LowStar_BufferOps.op_Bang_Star ll.v;
      LowStar_BufferOps.op_Star_Equals ll.v ()
let pop : 'a . 'a t -> 'a =
  fun ll ->
    let r =
      LowStar_BufferOps.op_Bang_Star ll.v;
      LowStar_Lib_LinkedList.pop () () ll.ptr in
    LowStar_BufferOps.op_Bang_Star ll.v;
    LowStar_BufferOps.op_Star_Equals ll.v ();
    r
let maybe_pop : 'a . 'a t -> 'a FStar_Pervasives_Native.option =
  fun ll ->
    let uu___ =
      let uu___1 =
        let uu___2 = LowStar_BufferOps.op_Bang_Star ll.ptr in
        LowStar_Monotonic_Buffer.is_null uu___2 in
      Prims.op_Negation uu___1 in
    if uu___
    then
      (LowStar_BufferOps.op_Bang_Star ll.v;
       (let r =
          LowStar_BufferOps.op_Bang_Star ll.v;
          LowStar_Lib_LinkedList.pop () () ll.ptr in
        LowStar_BufferOps.op_Star_Equals ll.v ();
        FStar_Pervasives_Native.Some r))
    else FStar_Pervasives_Native.None
let clear : 'a . 'a t -> unit =
  fun ll ->
    LowStar_BufferOps.op_Bang_Star ll.v;
    LowStar_Lib_LinkedList.free () ll.ptr;
    LowStar_BufferOps.op_Star_Equals ll.v ()
let free : 'uuuuu . 'uuuuu t -> unit =
  fun ll ->
    LowStar_BufferOps.op_Bang_Star ll.v;
    LowStar_Lib_LinkedList.free () ll.ptr;
    LowStar_Monotonic_Buffer.free ll.ptr;
    LowStar_Monotonic_Buffer.free ll.v
let (test : unit -> unit) =
  fun uu___ ->
    FStar_HyperStack_ST.new_region ();
    (let b =
       LowStar_Monotonic_Buffer.mmalloc ()
         (FStar_UInt32.uint_to_t Prims.int_zero)
         (FStar_UInt32.uint_to_t Prims.int_one) in
     let l = create_in () in
     push l (FStar_UInt32.uint_to_t Prims.int_zero);
     push l (FStar_UInt32.uint_to_t Prims.int_one);
     push l (FStar_UInt32.uint_to_t (Prims.of_int (2)));
     (let h = FStar_HyperStack_ST.get () in
      LowStar_Monotonic_Buffer.upd' b (FStar_UInt32.uint_to_t Prims.int_zero)
        (FStar_UInt32.uint_to_t Prims.int_one));
     (let h0 = FStar_HyperStack_ST.get () in
      (let uu___6 = pop l in ());
      (let h1 = FStar_HyperStack_ST.get () in
       clear l; (let h2 = FStar_HyperStack_ST.get () in free l))))