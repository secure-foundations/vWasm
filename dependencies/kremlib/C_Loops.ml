open Prims
let rec (for1 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> unit -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun start ->
    fun finish ->
      fun inv ->
        fun f ->
          if start = finish
          then ()
          else
            (f start;
             for1
               (FStar_UInt32.add start (FStar_UInt32.uint_to_t Prims.int_one))
               finish () f)
let rec (for64 :
  FStar_UInt64.t ->
    FStar_UInt64.t -> unit -> (FStar_UInt64.t -> unit) -> unit)
  =
  fun start ->
    fun finish ->
      fun inv ->
        fun f ->
          if start = finish
          then ()
          else
            (f start;
             for64
               (FStar_UInt64.add start (FStar_UInt64.uint_to_t Prims.int_one))
               finish () f)
let rec (reverse_for :
  FStar_UInt32.t ->
    FStar_UInt32.t -> unit -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun start ->
    fun finish ->
      fun inv ->
        fun f ->
          if start = finish
          then ()
          else
            (f start;
             reverse_for
               (FStar_UInt32.sub start (FStar_UInt32.uint_to_t Prims.int_one))
               finish () f)
let rec (interruptible_for :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit -> (FStar_UInt32.t -> Prims.bool) -> (FStar_UInt32.t * Prims.bool))
  =
  fun start ->
    fun finish ->
      fun inv ->
        fun f ->
          if start = finish
          then (finish, false)
          else
            (let start' =
               FStar_UInt32.add start (FStar_UInt32.uint_to_t Prims.int_one) in
             let uu___1 = f start in
             if uu___1
             then (start', true)
             else interruptible_for start' finish () f)
let rec do_while : 'inv . (unit -> Prims.bool) -> unit =
  fun f ->
    let uu___ = let uu___1 = f () in Prims.op_Negation uu___1 in
    if uu___ then do_while f else ()
let rec while1 :
  'testupre 'testupost . (unit -> Prims.bool) -> (unit -> unit) -> unit =
  fun test ->
    fun body ->
      let uu___ = test () in
      if uu___ then (body (); while1 test body) else ()
let rec (interruptible_reverse_for :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      unit -> (FStar_UInt32.t -> Prims.bool) -> (FStar_UInt32.t * Prims.bool))
  =
  fun start ->
    fun finish ->
      fun inv ->
        fun f ->
          if start = finish
          then (finish, false)
          else
            (let start' =
               FStar_UInt32.sub start (FStar_UInt32.uint_to_t Prims.int_one) in
             let uu___1 = f start in
             if uu___1
             then (start', true)
             else interruptible_reverse_for start' finish () f)
let map :
  'a 'b .
    'b LowStar_Buffer.buffer ->
      'a LowStar_Buffer.buffer -> FStar_UInt32.t -> ('a -> 'b) -> unit
  =
  fun output ->
    fun input ->
      fun l ->
        fun f ->
          let h0 = FStar_HyperStack_ST.get () in
          Obj.magic (fun h1 -> fun i -> ());
          (let f' i =
             let xi = LowStar_Monotonic_Buffer.index input i in
             let h = FStar_HyperStack_ST.get () in
             LowStar_Monotonic_Buffer.upd' output i (f xi) in
           for1 (FStar_UInt32.uint_to_t Prims.int_zero) l () f';
           (let h1 = FStar_HyperStack_ST.get () in ()))
let map2 :
  'a 'b 'c .
    'c LowStar_Buffer.buffer ->
      'a LowStar_Buffer.buffer ->
        'b LowStar_Buffer.buffer ->
          FStar_UInt32.t -> ('a -> 'b -> 'c) -> unit
  =
  fun output ->
    fun in1 ->
      fun in2 ->
        fun l ->
          fun f ->
            let h0 = FStar_HyperStack_ST.get () in
            Obj.magic (fun h1 -> fun i -> ());
            (let f' i =
               let xi = LowStar_Monotonic_Buffer.index in1 i in
               let yi = LowStar_Monotonic_Buffer.index in2 i in
               let h = FStar_HyperStack_ST.get () in
               LowStar_Monotonic_Buffer.upd' output i (f xi yi) in
             for1 (FStar_UInt32.uint_to_t Prims.int_zero) l () f';
             (let h1 = FStar_HyperStack_ST.get () in ()))
let in_place_map :
  'a . 'a LowStar_Buffer.buffer -> FStar_UInt32.t -> ('a -> 'a) -> unit =
  fun b ->
    fun l ->
      fun f ->
        let h0 = FStar_HyperStack_ST.get () in
        Obj.magic (fun h1 -> fun i -> ());
        (let f' i =
           let xi = LowStar_Monotonic_Buffer.index b i in
           let h = FStar_HyperStack_ST.get () in
           LowStar_Monotonic_Buffer.upd' b i (f xi) in
         for1 (FStar_UInt32.uint_to_t Prims.int_zero) l () f';
         (let h1 = FStar_HyperStack_ST.get () in ()))
let in_place_map2 :
  'a 'b .
    'a LowStar_Buffer.buffer ->
      'b LowStar_Buffer.buffer -> FStar_UInt32.t -> ('a -> 'b -> 'a) -> unit
  =
  fun in1 ->
    fun in2 ->
      fun l ->
        fun f ->
          let h0 = FStar_HyperStack_ST.get () in
          Obj.magic (fun h1 -> fun i -> ());
          (let f' i =
             let xi = LowStar_Monotonic_Buffer.index in1 i in
             let yi = LowStar_Monotonic_Buffer.index in2 i in
             let h = FStar_HyperStack_ST.get () in
             LowStar_Monotonic_Buffer.upd' in1 i (f xi yi) in
           for1 (FStar_UInt32.uint_to_t Prims.int_zero) l () f';
           (let h1 = FStar_HyperStack_ST.get () in ()))
let repeat :
  'a .
    FStar_UInt32.t ->
      ('a FStar_Seq_Base.seq -> 'a FStar_Seq_Base.seq) ->
        'a LowStar_Buffer.buffer ->
          FStar_UInt32.t -> ('a LowStar_Buffer.buffer -> unit) -> unit
  =
  fun l ->
    fun f ->
      fun b ->
        fun max ->
          fun fc ->
            let h0 = FStar_HyperStack_ST.get () in
            Obj.magic (fun h1 -> fun i -> ());
            (let f' i = fc b in
             for1 (FStar_UInt32.uint_to_t Prims.int_zero) max () f')
type ('a, 'max) repeat_range_body_spec = 'a -> Prims.nat -> 'a
type ('a, 'inv) repeat_range_body_interp = unit
type ('a, 'min, 'max, 'f, 'inv, 'interp) repeat_range_body_impl =
  FStar_UInt32.t -> unit
let repeat_range :
  'a .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        unit -> unit -> unit -> (FStar_UInt32.t -> unit) -> unit
  =
  fun min ->
    fun max ->
      fun f ->
        fun inv ->
          fun interp ->
            fun fc ->
              let h0 = FStar_HyperStack_ST.get () in
              Obj.magic (fun h1 -> fun i -> ());
              (let f' i = fc i in for1 min max () f')
let rec total_while_gen :
  't 'a . unit -> unit -> ('t -> Prims.bool) -> ('t -> 't) -> 't -> 't =
  fun tmes ->
    fun tinv ->
      fun tcontinue ->
        fun body ->
          fun x ->
            let y = body x in
            let continue = tcontinue y in
            if continue then total_while_gen () () tcontinue body y else y
let total_while : 't . unit -> unit -> ('t -> (Prims.bool * 't)) -> 't -> 't
  =
  fun tmes ->
    fun tinv ->
      fun body ->
        fun x ->
          let uu___ =
            total_while_gen () ()
              (fun uu___1 -> match uu___1 with | (x1, uu___2) -> x1)
              (fun uu___1 -> match uu___1 with | (uu___2, x1) -> body x1)
              (true, x) in
          match uu___ with | (uu___1, res) -> res