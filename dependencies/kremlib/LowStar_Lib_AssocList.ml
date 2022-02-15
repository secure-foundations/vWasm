open Prims
type ('k, 'v) t = ('k * 'v) LowStar_Lib_LinkedList2.t
type ('k, 'v) map = ('k, 'v FStar_Pervasives_Native.option) FStar_Map.t
let v_ : 'uuuuu 'tuv . ('uuuuu * 'tuv) Prims.list -> ('uuuuu, 'tuv) map =
  fun l ->
    FStar_List_Tot_Base.fold_right
      (fun uu___ ->
         fun m ->
           match uu___ with
           | (k, v) -> FStar_Map.upd m k (FStar_Pervasives_Native.Some v)) l
      (FStar_Map.const FStar_Pervasives_Native.None)

type ('uuuuu, 'uuuuu1, 'h, 'll) invariant = unit




let create_in : 'uuuuu 'uuuuu1 . unit -> ('uuuuu, 'uuuuu1) t =
  fun r -> LowStar_Lib_LinkedList2.create_in ()
let rec find_ :
  'uuuuu 'uuuuu1 .
    ('uuuuu * 'uuuuu1) LowStar_Lib_LinkedList.t ->
      unit -> 'uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option
  =
  fun hd ->
    fun l ->
      fun k ->
        let uu___ = LowStar_Monotonic_Buffer.is_null hd in
        if uu___
        then FStar_Pervasives_Native.None
        else
          (let cell = LowStar_BufferOps.op_Bang_Star hd in
           if
             (FStar_Pervasives_Native.fst cell.LowStar_Lib_LinkedList.data) =
               k
           then
             FStar_Pervasives_Native.Some
               (FStar_Pervasives_Native.snd cell.LowStar_Lib_LinkedList.data)
           else find_ cell.LowStar_Lib_LinkedList.next () k)
let find :
  'uuuuu 'uuuuu1 .
    ('uuuuu, 'uuuuu1) t -> 'uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option
  =
  fun ll ->
    fun k ->
      let uu___ =
        LowStar_BufferOps.op_Bang_Star ll.LowStar_Lib_LinkedList2.ptr in
      LowStar_BufferOps.op_Bang_Star ll.LowStar_Lib_LinkedList2.v;
      find_ uu___ () k
let add : 'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) t -> 'uuuuu -> 'uuuuu1 -> unit =
  fun ll -> fun k -> fun x -> LowStar_Lib_LinkedList2.push ll (k, x)
let rec remove_all_ :
  'tuk 'tuv .
    ('tuk * 'tuv) LowStar_Lib_LinkedList.t ->
      unit -> 'tuk -> (('tuk * 'tuv) LowStar_Lib_LinkedList.t * unit)
  =
  fun hd ->
    fun l ->
      fun k ->
        let h0 = FStar_HyperStack_ST.get () in
        let uu___ = LowStar_Monotonic_Buffer.is_null hd in
        if uu___
        then (hd, ())
        else
          (let cell = LowStar_BufferOps.op_Bang_Star hd in
           let uu___2 = cell in
           match uu___2 with
           | { LowStar_Lib_LinkedList.next = next;
               LowStar_Lib_LinkedList.data = data;_} ->
               let uu___3 = data in
               (match uu___3 with
                | (k', v) ->
                    if k = k'
                    then
                      (LowStar_Monotonic_Buffer.free hd;
                       (let h1 = FStar_HyperStack_ST.get () in
                        let uu___5 = remove_all_ next () k in
                        match uu___5 with | (hd', l') -> (hd', ())))
                    else
                      (let uu___5 = remove_all_ next () k in
                       match uu___5 with
                       | (hd', l') ->
                           let h1 = FStar_HyperStack_ST.get () in
                           (LowStar_BufferOps.op_Star_Equals hd
                              {
                                LowStar_Lib_LinkedList.next = hd';
                                LowStar_Lib_LinkedList.data = data
                              };
                            (let h2 = FStar_HyperStack_ST.get () in (hd, ()))))))
let remove_all : 'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) t -> 'uuuuu -> unit =
  fun ll ->
    fun k ->
      let uu___ =
        let uu___1 =
          LowStar_BufferOps.op_Bang_Star ll.LowStar_Lib_LinkedList2.ptr in
        LowStar_BufferOps.op_Bang_Star ll.LowStar_Lib_LinkedList2.v;
        remove_all_ uu___1 () k in
      match uu___ with
      | (hd, v) ->
          (LowStar_BufferOps.op_Star_Equals ll.LowStar_Lib_LinkedList2.ptr hd;
           LowStar_BufferOps.op_Star_Equals ll.LowStar_Lib_LinkedList2.v ())
let clear : 'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) t -> unit =
  fun ll -> LowStar_Lib_LinkedList2.clear ll
let free : 'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) t -> unit =
  fun ll -> LowStar_Lib_LinkedList2.free ll