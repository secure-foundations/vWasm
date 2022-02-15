open Prims


type ('ol, 'ne) memory_invariant_includes = unit

type ('a, 'wp) pure_wp_mono = unit
type 'a result =
  | Correct of 'a 
  | Error of Prims.string 
let uu___is_Correct : 'a . 'a result -> Prims.bool =
  fun projectee -> match projectee with | Correct _0 -> true | uu___ -> false
let __proj__Correct__item___0 : 'a . 'a result -> 'a =
  fun projectee -> match projectee with | Correct _0 -> _0
let uu___is_Error : 'a . 'a result -> Prims.bool =
  fun projectee -> match projectee with | Error _0 -> true | uu___ -> false
let __proj__Error__item___0 : 'a . 'a result -> Prims.string =
  fun projectee -> match projectee with | Error _0 -> _0
type 'pre pure_post_err = unit
type ('a, 'pre) pure_post' = unit
type ('a, 'pre, 'post, 'postuerr) read_repr_spec = unit
type ('a, 'pre, 'post, 'postuerr, 'l, 'spec) read_repr_impl =
  unit -> 'a result
let mk_read_repr_impl :
  'a 'pre 'post 'postuerr .
    unit -> unit -> (unit -> 'a result) -> unit -> 'a result
  = fun l -> fun spec -> fun impl -> impl
let extract_read_repr_impl :
  'a 'pre 'post 'postuerr . unit -> unit -> (unit -> 'a result) -> 'a result
  = fun l -> fun spec -> fun impl -> impl ()
type ('a, 'pre, 'post, 'postuerr, 'l) read_repr =
  | ReadRepr of unit * (unit -> 'a result) 
let uu___is_ReadRepr :
  'a 'pre 'post 'postuerr .
    unit -> ('a, 'pre, 'post, 'postuerr, unit) read_repr -> Prims.bool
  = fun l -> fun projectee -> true

let __proj__ReadRepr__item__impl :
  'a 'pre 'post 'postuerr .
    unit -> ('a, 'pre, 'post, 'postuerr, unit) read_repr -> unit -> 'a result
  =
  fun l ->
    fun projectee -> match projectee with | ReadRepr (spec, impl) -> impl

let read_return_impl : 'a . 'a -> unit -> unit -> 'a result =
  fun x -> fun inv -> fun uu___ -> Correct x
let read_return :
  'a . 'a -> unit -> ('a, Prims.l_True, unit, Prims.l_False, unit) read_repr
  = fun x -> fun inv -> ReadRepr ((), (fun uu___ -> Correct x))

let read_bind_impl :
  'a 'b 'preuf 'postuf 'postuerruf 'preug 'postug 'postuerrug .
    unit ->
      unit ->
        unit ->
          (unit -> 'a result) ->
            ('a -> unit -> 'b result) -> unit -> 'b result
  =
  fun f_bind_impl ->
    fun g ->
      fun l ->
        fun f' ->
          fun g' ->
            fun uu___ ->
              let uu___1 = f' () in
              match uu___1 with | Correct x -> g' x () | Error e -> Error e
let read_bind :
  'a 'b 'preuf 'postuf 'postuerruf 'preug 'postug 'postuerrug .
    unit ->
      ('a, 'preuf, 'postuf, 'postuerruf, unit) read_repr ->
        ('a -> ('b, 'preug, 'postug, 'postuerrug, unit) read_repr) ->
          ('b, unit, unit, unit, unit) read_repr
  =
  fun l ->
    fun f_bind ->
      fun g ->
        ReadRepr
          ((),
            (fun uu___ ->
               let uu___1 =
                 match f_bind with | ReadRepr (spec, impl) -> impl () in
               match uu___1 with
               | Correct x ->
                   (match g x with | ReadRepr (spec, impl) -> impl ())
               | Error e -> Error e))
type ('a, 'pre, 'post, 'postuerr, 'preu, 'postu,
  'postuerru) read_subcomp_spec_cond = unit
type ('a, 'pre, 'post, 'postuerr, 'preu, 'postu, 'postuerru, 'l,
  'lu) read_subcomp_cond = unit

let read_subcomp_impl :
  'a 'pre 'post 'postuerr 'preu 'postu 'postuerru .
    unit -> unit -> unit -> (unit -> 'a result) -> unit -> unit -> 'a result
  =
  fun l ->
    fun l' ->
      fun f_subcomp_spec ->
        fun f_subcomp -> fun sq -> fun uu___ -> f_subcomp ()
let read_subcomp :
  'a 'pre 'post 'postuerr 'preu 'postu 'postuerru .
    unit ->
      unit ->
        ('a, 'pre, 'post, 'postuerr, unit) read_repr ->
          ('a, 'preu, 'postu, 'postuerru, unit) read_repr
  =
  fun l ->
    fun l' ->
      fun f_subcomp ->
        ReadRepr
          ((),
            (fun uu___ ->
               match f_subcomp with | ReadRepr (spec, impl) -> impl ()))
type ('a, 'preuf, 'preug, 'postuf, 'postug, 'postuerruf, 'postuerrug, 
  'l, 'fuifthenelse, 'g, 'p) read_if_then_else =
  ('a, unit, unit, unit, unit) read_repr
let __proj__ERead__item__return = read_return
let __proj__ERead__item__bind = read_bind

let lift_pure_read_impl : 'a 'wp . (unit -> 'a) -> unit -> unit -> 'a result
  =
  fun f_pure_spec_for_impl ->
    fun l -> fun uu___ -> Correct (f_pure_spec_for_impl ())
let lift_pure_read :
  'a 'wp .
    unit -> (unit -> 'a) -> ('a, 'wp, unit, Prims.l_False, unit) read_repr
  = fun l -> fun f_pure -> ReadRepr ((), (fun uu___ -> Correct (f_pure ())))

let destr_read_repr_impl :
  'a 'pre 'post 'postuerr .
    unit ->
      (unit -> ('a, unit, unit, unit, unit) read_repr) -> unit -> 'a result
  =
  fun l ->
    fun r -> match Obj.magic (r ()) with | ReadRepr (spec, impl) -> impl
let reify_read :
  'a 'pre 'post 'postuerr .
    unit -> (unit -> ('a, unit, unit, unit, unit) read_repr) -> 'a result
  =
  fun l ->
    fun r -> match Obj.magic (r ()) with | ReadRepr (spec, impl) -> impl ()
let (test_read_if :
  unit ->
    (unit -> (Prims.bool, unit, unit, Prims.l_False, unit) read_repr) ->
      (Prims.bool, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun inv ->
    fun f ->
      ReadRepr
        ((),
          (fun uu___ ->
             let uu___1 =
               match Obj.magic (f ()) with | ReadRepr (spec, impl) -> impl () in
             match uu___1 with
             | Correct x -> Correct (if x then false else false)
             | Error e -> Error e))
let (test_read1 :
  unit ->
    (unit -> (Prims.bool, unit, unit, Prims.l_False, unit) read_repr) ->
      (Prims.bool, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun inv ->
    fun f ->
      ReadRepr
        ((),
          (fun uu___ ->
             let uu___1 =
               match Obj.magic (f ()) with | ReadRepr (spec, impl) -> impl () in
             match uu___1 with
             | Correct x -> Correct false
             | Error e -> Error e))
let (test_read2 :
  unit ->
    (unit -> (Prims.bool, unit, unit, Prims.l_False, unit) read_repr) ->
      (Prims.bool, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun inv ->
    fun f ->
      ReadRepr
        ((),
          (fun uu___ ->
             let uu___1 =
               match Obj.magic (f ()) with | ReadRepr (spec, impl) -> impl () in
             match uu___1 with
             | Correct x ->
                 let uu___2 =
                   match Obj.magic (f ()) with
                   | ReadRepr (spec, impl) -> impl () in
                 (match uu___2 with
                  | Correct x1 -> Correct false
                  | Error e -> Error e)
             | Error e -> Error e))
let (test_read3 :
  unit ->
    (unit -> (Prims.bool, unit, unit, Prims.l_False, unit) read_repr) ->
      (Prims.bool, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun inv ->
    fun f ->
      ReadRepr
        ((),
          (fun uu___ ->
             let uu___1 =
               match Obj.magic (f ()) with | ReadRepr (spec, impl) -> impl () in
             match uu___1 with
             | Correct x ->
                 let uu___2 =
                   match Obj.magic (f ()) with
                   | ReadRepr (spec, impl) -> impl () in
                 (match uu___2 with
                  | Correct x1 ->
                      let uu___3 =
                        match Obj.magic (f ()) with
                        | ReadRepr (spec, impl) -> impl () in
                      (match uu___3 with
                       | Correct x2 -> Correct false
                       | Error e -> Error e)
                  | Error e -> Error e)
             | Error e -> Error e))

let failwith_impl : 'a . unit -> Prims.string -> unit -> 'a result =
  fun inv -> fun s -> fun uu___ -> Error s
let failwith_repr :
  'a .
    unit ->
      Prims.string ->
        ('a, Prims.l_True, Prims.l_False, Prims.l_True, unit) read_repr
  = fun inv -> fun s -> ReadRepr ((), (fun uu___ -> Error s))
let failwith :
  'a . unit -> Prims.string -> ('a, unit, unit, unit, unit) read_repr =
  fun inv -> fun s -> ReadRepr ((), (fun uu___ -> Error s))

let buffer_index_impl :
  't .
    unit -> 't LowStar_Buffer.buffer -> FStar_UInt32.t -> unit -> 't result
  =
  fun inv ->
    fun b ->
      fun i ->
        fun uu___ ->
          let uu___1 = LowStar_Monotonic_Buffer.index b i in Correct uu___1
let buffer_index :
  't .
    unit ->
      't LowStar_Buffer.buffer ->
        FStar_UInt32.t -> ('t, unit, unit, Prims.l_False, unit) read_repr
  =
  fun inv ->
    fun b ->
      fun i ->
        ReadRepr
          ((),
            (fun uu___ ->
               let uu___1 = LowStar_Monotonic_Buffer.index b i in
               Correct uu___1))

let buffer_sub_impl :
  't .
    unit ->
      't LowStar_Buffer.buffer ->
        FStar_UInt32.t -> unit -> unit -> 't LowStar_Buffer.buffer result
  =
  fun inv ->
    fun b ->
      fun i ->
        fun len ->
          fun uu___ ->
            let uu___1 = LowStar_Monotonic_Buffer.msub b i () in
            Correct uu___1
let buffer_sub :
  't .
    unit ->
      't LowStar_Buffer.buffer ->
        FStar_UInt32.t ->
          unit ->
            ('t LowStar_Buffer.buffer, unit, unit, Prims.l_False, unit)
              read_repr
  =
  fun inv ->
    fun b ->
      fun i ->
        fun len ->
          ReadRepr
            ((),
              (fun uu___ ->
                 let uu___1 = LowStar_Monotonic_Buffer.msub b i () in
                 Correct uu___1))
type rptr =
  {
  rptr_base: FStar_UInt8.t LowStar_Buffer.buffer ;
  rptr_len: FStar_UInt32.t }
let (__proj__Mkrptr__item__rptr_base :
  rptr -> FStar_UInt8.t LowStar_Buffer.buffer) =
  fun projectee ->
    match projectee with | { rptr_base; rptr_len;_} -> rptr_base
let (__proj__Mkrptr__item__rptr_len : rptr -> FStar_UInt32.t) =
  fun projectee ->
    match projectee with | { rptr_base; rptr_len;_} -> rptr_len
type ('p, 'inv, 'x) valid_rptr = unit
type ('p, 'inv) ptr = rptr

let (mk_ptr :
  LowParse_Writers_Parser.parser ->
    unit ->
      LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
        FStar_UInt32.t -> rptr)
  = fun p -> fun inv -> fun b -> fun len -> { rptr_base = b; rptr_len = len }
let (buffer_of_ptr :
  LowParse_Writers_Parser.parser ->
    unit ->
      rptr ->
        (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer * FStar_UInt32.t))
  = fun p -> fun inv -> fun x -> ((x.rptr_base), (x.rptr_len))

let (deref_impl :
  LowParse_Writers_Parser.parser ->
    unit ->
      (FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> Obj.t) ->
        rptr -> unit -> Obj.t result)
  =
  fun p ->
    fun inv ->
      fun r ->
        fun x ->
          fun uu___ ->
            let h = FStar_HyperStack_ST.get () in
            let uu___1 = r x.rptr_base x.rptr_len in Correct uu___1
let (deref_repr :
  LowParse_Writers_Parser.parser ->
    unit ->
      (FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> Obj.t) ->
        rptr -> (Obj.t, Prims.l_True, unit, Prims.l_False, unit) read_repr)
  =
  fun p ->
    fun inv ->
      fun r ->
        fun x ->
          ReadRepr
            ((),
              (fun uu___ ->
                 let h = FStar_HyperStack_ST.get () in
                 let uu___1 = r x.rptr_base x.rptr_len in Correct uu___1))
let (deref :
  LowParse_Writers_Parser.parser ->
    unit ->
      (FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> Obj.t) ->
        rptr -> (Obj.t, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun p ->
    fun inv ->
      fun r ->
        fun x ->
          ReadRepr
            ((),
              (fun uu___ ->
                 let h = FStar_HyperStack_ST.get () in
                 let uu___1 = r x.rptr_base x.rptr_len in Correct uu___1))

let (access_impl :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      (Obj.t, Obj.t) LowParse_Writers_Parser.clens ->
        unit ->
          (unit, unit, unit) LowParse_Writers_Parser.gaccessor ->
            (unit, unit, unit, unit) LowParse_Writers_Parser.accessor ->
              rptr -> unit -> rptr result)
  =
  fun p1 ->
    fun p2 ->
      fun lens ->
        fun inv ->
          fun g ->
            fun a ->
              fun x ->
                fun uu___ ->
                  let h = FStar_HyperStack_ST.get () in
                  let uu___1 =
                    LowParse_Writers_Parser.baccess p1 p2 lens g a
                      x.rptr_base x.rptr_len in
                  match uu___1 with
                  | (base', len') ->
                      let h' = FStar_HyperStack_ST.get () in
                      Correct { rptr_base = base'; rptr_len = len' }
let (access_repr :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      (Obj.t, Obj.t) LowParse_Writers_Parser.clens ->
        unit ->
          (unit, unit, unit) LowParse_Writers_Parser.gaccessor ->
            (unit, unit, unit, unit) LowParse_Writers_Parser.accessor ->
              rptr -> (rptr, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun p1 ->
                   fun p2 ->
                     fun lens ->
                       fun inv ->
                         fun g ->
                           fun a ->
                             fun x ->
                               Obj.magic
                                 (ReadRepr
                                    ((),
                                      (fun uu___ ->
                                         let h = FStar_HyperStack_ST.get () in
                                         let uu___1 =
                                           LowParse_Writers_Parser.baccess p1
                                             p2 lens g a x.rptr_base
                                             x.rptr_len in
                                         match uu___1 with
                                         | (base', len') ->
                                             let h' =
                                               FStar_HyperStack_ST.get () in
                                             Correct
                                               {
                                                 rptr_base = base';
                                                 rptr_len = len'
                                               })))) uu___6 uu___5 uu___4
                  uu___3 uu___2 uu___1 uu___
let (access :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      (Obj.t, Obj.t) LowParse_Writers_Parser.clens ->
        unit ->
          (unit, unit, unit) LowParse_Writers_Parser.gaccessor ->
            (unit, unit, unit, unit) LowParse_Writers_Parser.accessor ->
              rptr -> (rptr, unit, unit, Prims.l_False, unit) read_repr)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun p1 ->
                   fun p2 ->
                     fun lens ->
                       fun inv ->
                         fun g ->
                           fun a ->
                             fun x ->
                               Obj.magic
                                 (ReadRepr
                                    ((),
                                      (fun uu___ ->
                                         let h = FStar_HyperStack_ST.get () in
                                         let uu___1 =
                                           LowParse_Writers_Parser.baccess p1
                                             p2 lens g a x.rptr_base
                                             x.rptr_len in
                                         match uu___1 with
                                         | (base', len') ->
                                             let h' =
                                               FStar_HyperStack_ST.get () in
                                             Correct
                                               {
                                                 rptr_base = base';
                                                 rptr_len = len'
                                               })))) uu___6 uu___5 uu___4
                  uu___3 uu___2 uu___1 uu___
type ('inv, 'b) validate_pre = unit
type ('p, 'inv, 'b) validate_post = Obj.t
type ('p, 'inv, 'b) validate_post_err = unit


let (validate_impl :
  LowParse_Writers_Parser.parser ->
    unit LowParse_Writers_Parser.validator ->
      unit ->
        FStar_UInt8.t LowStar_Buffer.buffer ->
          FStar_UInt32.t -> unit -> (rptr * FStar_UInt32.t) result)
  =
  fun p ->
    fun v ->
      fun inv ->
        fun b ->
          fun len ->
            fun uu___ ->
              let h1 = FStar_HyperStack_ST.get () in
              let res = LowParse_Writers_Parser.bvalidate p v b len in
              let h2 = FStar_HyperStack_ST.get () in
              match res with
              | FStar_Pervasives_Native.None -> Error "validation failed"
              | FStar_Pervasives_Native.Some pos ->
                  let b' =
                    LowStar_Monotonic_Buffer.msub b
                      (FStar_UInt32.uint_to_t Prims.int_zero) () in
                  let x = { rptr_base = b'; rptr_len = pos } in
                  Correct (x, pos)
let (validate_repr :
  LowParse_Writers_Parser.parser ->
    unit LowParse_Writers_Parser.validator ->
      unit ->
        FStar_UInt8.t LowStar_Buffer.buffer ->
          FStar_UInt32.t ->
            ((rptr * FStar_UInt32.t), unit, Obj.t,
              (unit, unit, unit) validate_post_err, unit) read_repr)
  =
  fun p ->
    fun v ->
      fun inv ->
        fun b ->
          fun len ->
            ReadRepr
              ((),
                (fun uu___ ->
                   let h1 = FStar_HyperStack_ST.get () in
                   let res = LowParse_Writers_Parser.bvalidate p v b len in
                   let h2 = FStar_HyperStack_ST.get () in
                   match res with
                   | FStar_Pervasives_Native.None ->
                       Error "validation failed"
                   | FStar_Pervasives_Native.Some pos ->
                       let b' =
                         LowStar_Monotonic_Buffer.msub b
                           (FStar_UInt32.uint_to_t Prims.int_zero) () in
                       let x = { rptr_base = b'; rptr_len = pos } in
                       Correct (x, pos)))
let (validate :
  LowParse_Writers_Parser.parser ->
    unit LowParse_Writers_Parser.validator ->
      unit ->
        FStar_UInt8.t LowStar_Buffer.buffer ->
          FStar_UInt32.t ->
            ((rptr * FStar_UInt32.t), unit, unit, unit, unit) read_repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun p ->
               fun v ->
                 fun inv ->
                   fun b ->
                     fun len ->
                       Obj.magic
                         (ReadRepr
                            ((),
                              (fun uu___ ->
                                 let h1 = FStar_HyperStack_ST.get () in
                                 let res =
                                   LowParse_Writers_Parser.bvalidate p v b
                                     len in
                                 let h2 = FStar_HyperStack_ST.get () in
                                 match res with
                                 | FStar_Pervasives_Native.None ->
                                     Error "validation failed"
                                 | FStar_Pervasives_Native.Some pos ->
                                     let b' =
                                       LowStar_Monotonic_Buffer.msub b
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_zero) () in
                                     Correct
                                       ({ rptr_base = b'; rptr_len = pos },
                                         pos))))) uu___4 uu___3 uu___2 uu___1
              uu___
type 'rin pre_t = unit
type ('a, 'rin, 'rout, 'pre) post_t = unit
type ('rin, 'pre) post_err_t = unit
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr) repr_spec = unit
type 'a iresult =
  | ICorrect of 'a * FStar_UInt32.t 
  | IError of Prims.string 
  | IOverflow 
let uu___is_ICorrect : 'a . 'a iresult -> Prims.bool =
  fun projectee ->
    match projectee with | ICorrect (res, new_pos) -> true | uu___ -> false
let __proj__ICorrect__item__res : 'a . 'a iresult -> 'a =
  fun projectee -> match projectee with | ICorrect (res, new_pos) -> res
let __proj__ICorrect__item__new_pos : 'a . 'a iresult -> FStar_UInt32.t =
  fun projectee -> match projectee with | ICorrect (res, new_pos) -> new_pos
let uu___is_IError : 'a . 'a iresult -> Prims.bool =
  fun projectee -> match projectee with | IError _0 -> true | uu___ -> false
let __proj__IError__item___0 : 'a . 'a iresult -> Prims.string =
  fun projectee -> match projectee with | IError _0 -> _0
let uu___is_IOverflow : 'a . 'a iresult -> Prims.bool =
  fun projectee -> match projectee with | IOverflow -> true | uu___ -> false
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'l, 'spec, 'b, 'pos1, 
  'h, 'res, 'hu) repr_impl_post = unit
type ('t, 'b) buffer_offset = FStar_UInt32.t
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'l, 'spec) repr_impl =
  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
    FStar_UInt32.t ->
      (LowParse_Writers_Parser.u8, unit) buffer_offset -> 'a iresult
let mk_repr_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                     FStar_UInt32.t ->
                       (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                         'a iresult)
                    ->
                    LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                      FStar_UInt32.t ->
                        (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                          'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post -> fun post_err -> fun l -> fun spec -> fun impl -> impl
let extract_repr_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                     FStar_UInt32.t ->
                       (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                         'a iresult)
                    ->
                    LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                      FStar_UInt32.t ->
                        (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                          'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post -> fun post_err -> fun l -> fun spec -> fun impl -> impl
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'l) repr =
  | Repr of unit *
  (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
     FStar_UInt32.t ->
       (LowParse_Writers_Parser.u8, unit) buffer_offset -> 'a iresult)
  
let uu___is_Repr :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                ('a, unit, unit, Obj.t, Obj.t, Obj.t, unit) repr ->
                  Prims.bool
  =
  fun r_in ->
    fun r_out ->
      fun pre -> fun post -> fun post_err -> fun l -> fun projectee -> true

let __proj__Repr__item__impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                ('a, unit, unit, Obj.t, Obj.t, Obj.t, unit) repr ->
                  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                    FStar_UInt32.t ->
                      (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                        'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post ->
          fun post_err ->
            fun l ->
              fun projectee ->
                match projectee with | Repr (spec, impl) -> impl

let return_impl :
  'a .
    'a ->
      LowParse_Writers_Parser.parser ->
        unit ->
          LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
            FStar_UInt32.t ->
              (LowParse_Writers_Parser.u8, unit) buffer_offset -> 'a iresult
  =
  fun x ->
    fun r -> fun l -> fun b -> fun len -> fun pos1 -> ICorrect (x, pos1)
let returnc :
  'a .
    'a ->
      LowParse_Writers_Parser.parser ->
        unit ->
          ('a, unit, unit, Prims.l_True, unit, Prims.l_False, unit) repr
  =
  fun x ->
    fun r ->
      fun l ->
        Repr ((), (fun b -> fun len -> fun pos1 -> ICorrect (x, pos1)))

let bind_impl :
  'a 'b .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              LowParse_Writers_Parser.parser ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          unit ->
                            (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer
                               ->
                               FStar_UInt32.t ->
                                 (LowParse_Writers_Parser.u8, unit)
                                   buffer_offset -> 'a iresult)
                              ->
                              ('a ->
                                 LowParse_Writers_Parser.u8
                                   LowStar_Buffer.buffer ->
                                   FStar_UInt32.t ->
                                     (LowParse_Writers_Parser.u8, unit)
                                       buffer_offset -> 'b iresult)
                                ->
                                LowParse_Writers_Parser.u8
                                  LowStar_Buffer.buffer ->
                                  FStar_UInt32.t ->
                                    (LowParse_Writers_Parser.u8, unit)
                                      buffer_offset -> 'b iresult
  =
  fun r_in_f ->
    fun r_out_f ->
      fun pre_f ->
        fun post_f ->
          fun post_err_f ->
            fun r_out_g ->
              fun pre_g ->
                fun post_g ->
                  fun post_err_g ->
                    fun f_bind_impl ->
                      fun g ->
                        fun l ->
                          fun f' ->
                            fun g' ->
                              fun buf ->
                                fun len ->
                                  fun pos ->
                                    let uu___ = f' buf len pos in
                                    match uu___ with
                                    | IError e -> IError e
                                    | IOverflow -> IOverflow
                                    | ICorrect (x, posf) -> g' x buf len posf
let bind :
  'a 'b .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              LowParse_Writers_Parser.parser ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        ('a, unit, unit, Obj.t, Obj.t, Obj.t, unit) repr ->
                          ('a ->
                             ('b, unit, unit, Obj.t, Obj.t, Obj.t, unit) repr)
                            -> ('b, unit, unit, unit, unit, unit, unit) repr
  =
  fun r_in_f ->
    fun r_out_f ->
      fun pre_f ->
        fun post_f ->
          fun post_err_f ->
            fun r_out_g ->
              fun pre_g ->
                fun post_g ->
                  fun post_err_g ->
                    fun l ->
                      fun f_bind ->
                        fun g ->
                          Repr
                            ((),
                              (fun buf ->
                                 fun len ->
                                   fun pos ->
                                     let uu___ =
                                       match f_bind with
                                       | Repr (spec, impl) ->
                                           impl buf len pos in
                                     match uu___ with
                                     | IError e -> IError e
                                     | IOverflow -> IOverflow
                                     | ICorrect (x, posf) ->
                                         (match g x with
                                          | Repr (spec, impl) ->
                                              impl buf len posf)))
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'preu, 'postu,
  'postuerru) subcomp_spec_cond = unit
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'preu, 'postu, 'postuerru,
  'l, 'lu) subcomp_cond = unit

let subcomp_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer
                             ->
                             FStar_UInt32.t ->
                               (LowParse_Writers_Parser.u8, unit)
                                 buffer_offset -> 'a iresult)
                            ->
                            unit ->
                              LowParse_Writers_Parser.u8
                                LowStar_Buffer.buffer ->
                                FStar_UInt32.t ->
                                  (LowParse_Writers_Parser.u8, unit)
                                    buffer_offset -> 'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post ->
          fun post_err ->
            fun pre' ->
              fun post' ->
                fun post_err' ->
                  fun l ->
                    fun l' ->
                      fun f_subcomp_spec ->
                        fun f_subcomp ->
                          fun sq ->
                            fun b ->
                              fun len -> fun pos -> f_subcomp b len pos
let subcomp :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        ('a, unit, unit, Obj.t, Obj.t, Obj.t, unit) repr ->
                          ('a, unit, unit, Obj.t, Obj.t, Obj.t, unit) repr
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post ->
          fun post_err ->
            fun pre' ->
              fun post' ->
                fun post_err' ->
                  fun l ->
                    fun l' ->
                      fun f_subcomp ->
                        Repr
                          ((),
                            (fun b ->
                               fun len ->
                                 fun pos ->
                                   match f_subcomp with
                                   | Repr (spec, impl) -> impl b len pos))
type ('a, 'ruin, 'ruout, 'preuf, 'preug, 'postuf, 'postug, 'postuerruf,
  'postuerrug, 'l, 'fuifthenelse, 'g, 'p) if_then_else =
  ('a, unit, unit, unit, unit, unit, unit) repr
let __proj__EWrite__item__return = returnc
let __proj__EWrite__item__bind = bind

let lift_read_impl :
  'a 'pre 'post 'postuerr .
    unit ->
      LowParse_Writers_Parser.parser ->
        ('a, 'pre, 'post, 'postuerr, unit) read_repr ->
          LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
            FStar_UInt32.t ->
              (LowParse_Writers_Parser.u8, unit) buffer_offset -> 'a iresult
  =
  fun inv ->
    fun r ->
      fun f_read_spec ->
        fun b ->
          fun len ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let uu___ =
                match f_read_spec with | ReadRepr (spec, impl) -> impl () in
              match uu___ with
              | Correct res ->
                  let h' = FStar_HyperStack_ST.get () in ICorrect (res, pos)
              | Error e -> IError e
let lift_read :
  'a 'pre 'post 'postuerr .
    unit ->
      LowParse_Writers_Parser.parser ->
        ('a, 'pre, 'post, 'postuerr, unit) read_repr ->
          ('a, unit, unit, 'pre, unit, 'postuerr, unit) repr
  =
  fun inv ->
    fun r ->
      fun f_read_spec ->
        Repr
          ((),
            (fun b ->
               fun len ->
                 fun pos ->
                   let h = FStar_HyperStack_ST.get () in
                   let uu___ =
                     match f_read_spec with
                     | ReadRepr (spec, impl) -> impl () in
                   match uu___ with
                   | Correct res ->
                       let h' = FStar_HyperStack_ST.get () in
                       ICorrect (res, pos)
                   | Error e -> IError e))

let wfailwith_impl :
  'a .
    unit ->
      LowParse_Writers_Parser.parser ->
        LowParse_Writers_Parser.parser ->
          Prims.string ->
            LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
              FStar_UInt32.t ->
                (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                  'a iresult
  =
  fun inv ->
    fun rin -> fun rout -> fun s -> fun b -> fun len -> fun pos -> IError s
let wfailwith :
  'a .
    unit ->
      LowParse_Writers_Parser.parser ->
        LowParse_Writers_Parser.parser ->
          Prims.string -> ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun inv ->
    fun rin ->
      fun rout ->
        fun s -> Repr ((), (fun b -> fun len -> fun pos -> IError s))

let destr_repr_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                    FStar_UInt32.t ->
                      (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                        'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post ->
          fun post_err ->
            fun l ->
              fun f_destr_spec ->
                match Obj.magic (f_destr_spec ()) with
                | Repr (spec, impl) -> impl
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'l,
  'fudestruspec) extract_t =
  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
    FStar_UInt32.t ->
      (LowParse_Writers_Parser.u8, unit) buffer_offset -> 'a iresult
let extract :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                    FStar_UInt32.t ->
                      (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                        'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post ->
          fun post_err ->
            fun l ->
              fun f_destr_spec ->
                match Obj.magic (f_destr_spec ()) with
                | Repr (spec, impl) -> impl
let wrap_extracted_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                     FStar_UInt32.t ->
                       (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                         'a iresult)
                    -> ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun r_in ->
                     fun r_out ->
                       fun pre ->
                         fun post ->
                           fun post_err ->
                             fun l ->
                               fun f_destr_spec ->
                                 fun e ->
                                   Obj.magic
                                     (Repr
                                        ((),
                                          (fun b ->
                                             fun len ->
                                               fun pos1 -> e b len pos1))))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk_repr :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                     FStar_UInt32.t ->
                       (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                         'a iresult)
                    -> unit -> ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___8 ->
    fun uu___7 ->
      fun uu___6 ->
        fun uu___5 ->
          fun uu___4 ->
            fun uu___3 ->
              fun uu___2 ->
                fun uu___1 ->
                  fun uu___ ->
                    (fun r_in ->
                       fun r_out ->
                         fun pre ->
                           fun post ->
                             fun post_err ->
                               fun l ->
                                 fun spec ->
                                   fun impl ->
                                     fun uu___ -> Obj.magic (Repr ((), impl)))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___

let (get_state_impl :
  unit ->
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
        FStar_UInt32.t ->
          (LowParse_Writers_Parser.u8, unit) buffer_offset -> unit iresult)
  =
  fun inv ->
    fun p ->
      fun b ->
        fun len ->
          fun pos -> let h = FStar_HyperStack_ST.get () in ICorrect ((), pos)
let (get_state :
  unit ->
    LowParse_Writers_Parser.parser ->
      unit -> (unit, unit, unit, unit, unit, Prims.l_False, unit) repr)
  =
  fun inv ->
    fun p ->
      fun uu___ ->
        Repr
          ((),
            (fun b ->
               fun len ->
                 fun pos ->
                   let h = FStar_HyperStack_ST.get () in ICorrect ((), pos)))
let frame_out :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser -> LowParse_Writers_Parser.parser
  =
  fun frame ->
    fun p ->
      LowParse_Writers_Parser.Parser
        ((),
          (Obj.magic
             (LowParse_Writers_Parser.parse_pair'
                (match frame with
                 | LowParse_Writers_Parser.Parser (t, p1) -> p1)
                (match p with | LowParse_Writers_Parser.Parser (t, p1) -> p1))))
type ('frame, 'pre) frame_pre = 'pre
type ('a, 'frame, 'pre, 'p, 'post) frame_post = Obj.t
type ('frame, 'pre, 'postuerr) frame_post_err = 'postuerr

let frame_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      unit ->
        LowParse_Writers_Parser.parser ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                    FStar_UInt32.t ->
                      (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                        'a iresult
  =
  fun frame ->
    fun pre ->
      fun p ->
        fun post ->
          fun post_err ->
            fun l ->
              fun inner ->
                fun buf ->
                  fun len ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      let buf' = LowStar_Monotonic_Buffer.moffset buf pos in
                      let uu___ =
                        (match Obj.magic (inner ()) with
                         | Repr (spec, impl) -> impl) buf'
                          (FStar_UInt32.sub len pos)
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      match uu___ with
                      | IError e -> IError e
                      | IOverflow -> IOverflow
                      | ICorrect (x, wlen) ->
                          let h' = FStar_HyperStack_ST.get () in
                          let pos' = FStar_UInt32.add pos wlen in
                          ICorrect (x, pos')
let frame_repr :
  'a .
    LowParse_Writers_Parser.parser ->
      unit ->
        LowParse_Writers_Parser.parser ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  unit -> ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun frame ->
                     fun pre ->
                       fun p ->
                         fun post ->
                           fun post_err ->
                             fun l ->
                               fun inner ->
                                 fun uu___ ->
                                   Obj.magic
                                     (Repr
                                        ((),
                                          (fun buf ->
                                             fun len ->
                                               fun pos ->
                                                 let h =
                                                   FStar_HyperStack_ST.get () in
                                                 let buf' =
                                                   LowStar_Monotonic_Buffer.moffset
                                                     buf pos in
                                                 let uu___1 =
                                                   (match Obj.magic
                                                            (inner ())
                                                    with
                                                    | Repr (spec, impl) ->
                                                        impl) buf'
                                                     (FStar_UInt32.sub len
                                                        pos)
                                                     (FStar_UInt32.uint_to_t
                                                        Prims.int_zero) in
                                                 match uu___1 with
                                                 | IError e -> IError e
                                                 | IOverflow -> IOverflow
                                                 | ICorrect (x, wlen) ->
                                                     let h' =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     ICorrect
                                                       (x,
                                                         (FStar_UInt32.add
                                                            pos wlen))))))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let frame :
  'a .
    LowParse_Writers_Parser.parser ->
      unit ->
        LowParse_Writers_Parser.parser ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun frame1 ->
                   fun pre ->
                     fun p ->
                       fun post ->
                         fun post_err ->
                           fun l ->
                             fun inner ->
                               Obj.magic
                                 (Repr
                                    ((),
                                      (fun buf ->
                                         fun len ->
                                           fun pos ->
                                             let h =
                                               FStar_HyperStack_ST.get () in
                                             let buf' =
                                               LowStar_Monotonic_Buffer.moffset
                                                 buf pos in
                                             let uu___ =
                                               (match Obj.magic (inner ())
                                                with
                                                | Repr (spec, impl) -> impl)
                                                 buf'
                                                 (FStar_UInt32.sub len pos)
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero) in
                                             match uu___ with
                                             | IError e -> IError e
                                             | IOverflow -> IOverflow
                                             | ICorrect (x, wlen) ->
                                                 let h' =
                                                   FStar_HyperStack_ST.get () in
                                                 ICorrect
                                                   (x,
                                                     (FStar_UInt32.add pos
                                                        wlen)))))) uu___6
                  uu___5 uu___4 uu___3 uu___2 uu___1 uu___

let (elem_writer_impl :
  LowParse_Writers_Parser.parser ->
    (FStar_UInt8.t LowStar_Buffer.buffer ->
       FStar_UInt32.t ->
         Obj.t -> FStar_UInt32.t FStar_Pervasives_Native.option)
      ->
      unit ->
        Obj.t ->
          LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
            FStar_UInt32.t ->
              (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                unit iresult)
  =
  fun p ->
    fun w ->
      fun l ->
        fun x ->
          fun b ->
            fun len ->
              fun pos ->
                let b' = LowStar_Monotonic_Buffer.moffset b pos in
                let uu___ = w b' (FStar_UInt32.sub len pos) x in
                match uu___ with
                | FStar_Pervasives_Native.None -> IOverflow
                | FStar_Pervasives_Native.Some xlen ->
                    ICorrect ((), (FStar_UInt32.add pos xlen))
let (start :
  LowParse_Writers_Parser.parser ->
    (FStar_UInt8.t LowStar_Buffer.buffer ->
       FStar_UInt32.t ->
         Obj.t -> FStar_UInt32.t FStar_Pervasives_Native.option)
      ->
      unit ->
        Obj.t -> (unit, unit, unit, unit, unit, Prims.l_False, unit) repr)
  =
  fun p ->
    fun w ->
      fun l ->
        fun x ->
          Repr
            ((),
              (fun b ->
                 fun len ->
                   fun pos ->
                     let b' = LowStar_Monotonic_Buffer.moffset b pos in
                     let uu___ = w b' (FStar_UInt32.sub len pos) x in
                     match uu___ with
                     | FStar_Pervasives_Native.None -> IOverflow
                     | FStar_Pervasives_Native.Some xlen ->
                         ICorrect ((), (FStar_UInt32.add pos xlen))))
let (append :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      (FStar_UInt8.t LowStar_Buffer.buffer ->
         FStar_UInt32.t ->
           Obj.t -> FStar_UInt32.t FStar_Pervasives_Native.option)
        ->
        unit ->
          Obj.t -> (unit, unit, unit, unit, unit, Prims.l_False, unit) repr)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun fr ->
               fun p ->
                 fun w ->
                   fun l ->
                     fun x ->
                       Obj.magic
                         (Repr
                            ((),
                              (fun buf ->
                                 fun len ->
                                   fun pos ->
                                     let h = FStar_HyperStack_ST.get () in
                                     let buf' =
                                       LowStar_Monotonic_Buffer.moffset buf
                                         pos in
                                     let uu___ =
                                       let b' =
                                         LowStar_Monotonic_Buffer.moffset
                                           buf'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero) in
                                       let uu___1 =
                                         w b'
                                           (FStar_UInt32.sub
                                              (FStar_UInt32.sub len pos)
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero)) x in
                                       match uu___1 with
                                       | FStar_Pervasives_Native.None ->
                                           IOverflow
                                       | FStar_Pervasives_Native.Some xlen ->
                                           ICorrect
                                             ((),
                                               (FStar_UInt32.add
                                                  (FStar_UInt32.uint_to_t
                                                     Prims.int_zero) xlen)) in
                                     match uu___ with
                                     | IError e -> IError e
                                     | IOverflow -> IOverflow
                                     | ICorrect (x1, wlen) ->
                                         let h' = FStar_HyperStack_ST.get () in
                                         ICorrect
                                           ((), (FStar_UInt32.add pos wlen))))))
              uu___4 uu___3 uu___2 uu___1 uu___
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'l, 'f) recast_writer_post =
  unit
type ('a, 'ruin, 'ruout, 'pre, 'post, 'postuerr, 'l,
  'f) recast_writer_post_err = unit

let recast_writer_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                    FStar_UInt32.t ->
                      (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                        'a iresult
  =
  fun r_in ->
    fun r_out ->
      fun pre ->
        fun post ->
          fun post_err ->
            fun l ->
              fun f ->
                fun b ->
                  fun len ->
                    fun pos ->
                      match Obj.magic (f ()) with
                      | Repr (spec, impl) -> impl b len pos
let recast_writer_repr :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  unit -> ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun r_in ->
                     fun r_out ->
                       fun pre ->
                         fun post ->
                           fun post_err ->
                             fun l ->
                               fun f ->
                                 fun uu___ ->
                                   Obj.magic
                                     (Repr
                                        ((),
                                          (fun b ->
                                             fun len ->
                                               fun pos ->
                                                 match Obj.magic (f ()) with
                                                 | Repr (spec, impl) ->
                                                     impl b len pos))))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let recast_writer :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          unit ->
            unit ->
              unit ->
                (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                  ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun r_in ->
                   fun r_out ->
                     fun pre ->
                       fun post ->
                         fun post_err ->
                           fun l ->
                             fun f ->
                               Obj.magic
                                 (Repr
                                    ((),
                                      (fun b ->
                                         fun len ->
                                           fun pos ->
                                             match Obj.magic (f ()) with
                                             | Repr (spec, impl) ->
                                                 impl b len pos)))) uu___6
                  uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let frame' :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
            ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun fr ->
             fun p ->
               fun l ->
                 fun f ->
                   Obj.magic
                     (Repr
                        ((),
                          (fun buf ->
                             fun len ->
                               fun pos ->
                                 let h = FStar_HyperStack_ST.get () in
                                 let buf' =
                                   LowStar_Monotonic_Buffer.moffset buf pos in
                                 let uu___ =
                                   (match f () with
                                    | Repr (spec, impl) -> impl) buf'
                                     (FStar_UInt32.sub len pos)
                                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                                 match uu___ with
                                 | IError e -> IError e
                                 | IOverflow -> IOverflow
                                 | ICorrect (x, wlen) ->
                                     let h' = FStar_HyperStack_ST.get () in
                                     ICorrect
                                       (x, (FStar_UInt32.add pos wlen))))))
            uu___3 uu___2 uu___1 uu___
type ('frame1, 'ppre, 'pre) frame2_pre = Obj.t
type ('a, 'frame1, 'ppre, 'pre, 'p, 'post) frame2_post = Obj.t
type ('frame1, 'ppre, 'pre, 'postuerr) frame2_post_err = Obj.t

let frame2_impl :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          LowParse_Writers_Parser.parser ->
            unit ->
              unit ->
                unit ->
                  (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                    LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                      FStar_UInt32.t ->
                        (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                          'a iresult
  =
  fun frame1 ->
    fun ppre ->
      fun pre ->
        fun p ->
          fun post ->
            fun post_err ->
              fun l ->
                fun inner ->
                  fun buf ->
                    fun len ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let pos2 =
                          LowParse_Writers_Parser.valid_parse_pair_inv frame1
                            ppre buf len
                            (FStar_UInt32.uint_to_t Prims.int_zero) pos in
                        let buf' = LowStar_Monotonic_Buffer.moffset buf pos2 in
                        let h1 = FStar_HyperStack_ST.get () in
                        let uu___ =
                          (match Obj.magic (inner ()) with
                           | Repr (spec, impl) -> impl) buf'
                            (FStar_UInt32.sub len pos2)
                            (FStar_UInt32.sub pos pos2) in
                        match uu___ with
                        | IOverflow -> IOverflow
                        | IError e -> IError e
                        | ICorrect (x, wlen) ->
                            let h' = FStar_HyperStack_ST.get () in
                            let pos' = FStar_UInt32.add pos2 wlen in
                            ICorrect (x, pos')
let frame2_repr :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          LowParse_Writers_Parser.parser ->
            unit ->
              unit ->
                unit ->
                  (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                    unit -> ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___8 ->
    fun uu___7 ->
      fun uu___6 ->
        fun uu___5 ->
          fun uu___4 ->
            fun uu___3 ->
              fun uu___2 ->
                fun uu___1 ->
                  fun uu___ ->
                    (fun frame1 ->
                       fun ppre ->
                         fun pre ->
                           fun p ->
                             fun post ->
                               fun post_err ->
                                 fun l ->
                                   fun inner ->
                                     fun uu___ ->
                                       Obj.magic
                                         (Repr
                                            ((),
                                              (fun buf ->
                                                 fun len ->
                                                   fun pos ->
                                                     let h =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     let pos2 =
                                                       LowParse_Writers_Parser.valid_parse_pair_inv
                                                         frame1 ppre buf len
                                                         (FStar_UInt32.uint_to_t
                                                            Prims.int_zero)
                                                         pos in
                                                     let buf' =
                                                       LowStar_Monotonic_Buffer.moffset
                                                         buf pos2 in
                                                     let h1 =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     let uu___1 =
                                                       (match Obj.magic
                                                                (inner ())
                                                        with
                                                        | Repr (spec, impl)
                                                            -> impl) buf'
                                                         (FStar_UInt32.sub
                                                            len pos2)
                                                         (FStar_UInt32.sub
                                                            pos pos2) in
                                                     match uu___1 with
                                                     | IOverflow -> IOverflow
                                                     | IError e -> IError e
                                                     | ICorrect (x, wlen) ->
                                                         let h' =
                                                           FStar_HyperStack_ST.get
                                                             () in
                                                         ICorrect
                                                           (x,
                                                             (FStar_UInt32.add
                                                                pos2 wlen))))))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let frame2 :
  'a .
    LowParse_Writers_Parser.parser ->
      LowParse_Writers_Parser.parser ->
        unit ->
          LowParse_Writers_Parser.parser ->
            unit ->
              unit ->
                unit ->
                  (unit -> ('a, unit, unit, unit, unit, unit, unit) repr) ->
                    ('a, unit, unit, unit, unit, unit, unit) repr
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun frame1 ->
                     fun ppre ->
                       fun pre ->
                         fun p ->
                           fun post ->
                             fun post_err ->
                               fun l ->
                                 fun inner ->
                                   Obj.magic
                                     (Repr
                                        ((),
                                          (fun buf ->
                                             fun len ->
                                               fun pos ->
                                                 let h =
                                                   FStar_HyperStack_ST.get () in
                                                 let pos2 =
                                                   LowParse_Writers_Parser.valid_parse_pair_inv
                                                     frame1 ppre buf len
                                                     (FStar_UInt32.uint_to_t
                                                        Prims.int_zero) pos in
                                                 let buf' =
                                                   LowStar_Monotonic_Buffer.moffset
                                                     buf pos2 in
                                                 let h1 =
                                                   FStar_HyperStack_ST.get () in
                                                 let uu___ =
                                                   (match Obj.magic
                                                            (inner ())
                                                    with
                                                    | Repr (spec, impl) ->
                                                        impl) buf'
                                                     (FStar_UInt32.sub len
                                                        pos2)
                                                     (FStar_UInt32.sub pos
                                                        pos2) in
                                                 match uu___ with
                                                 | IOverflow -> IOverflow
                                                 | IError e -> IError e
                                                 | ICorrect (x, wlen) ->
                                                     let h' =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     ICorrect
                                                       (x,
                                                         (FStar_UInt32.add
                                                            pos2 wlen))))))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___





let (valid_rewrite_impl :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      unit ->
        unit ->
          unit ->
            unit ->
              LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
                FStar_UInt32.t ->
                  (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                    unit iresult)
  =
  fun p1 ->
    fun p2 ->
      fun precond ->
        fun f ->
          fun v ->
            fun inv ->
              fun buf ->
                fun len ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in ICorrect ((), pos)
let (valid_rewrite_repr :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      unit ->
        unit ->
          unit ->
            unit -> (unit, unit, unit, Obj.t, unit, Prims.l_False, unit) repr)
  =
  fun p1 ->
    fun p2 ->
      fun precond ->
        fun f ->
          fun v ->
            fun inv ->
              Repr
                ((),
                  (fun buf ->
                     fun len ->
                       fun pos ->
                         let h = FStar_HyperStack_ST.get () in
                         ICorrect ((), pos)))
let (valid_rewrite :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      unit ->
        unit ->
          unit ->
            unit -> (unit, unit, unit, unit, unit, Prims.l_False, unit) repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun p1 ->
                 fun p2 ->
                   fun precond ->
                     fun f ->
                       fun inv ->
                         fun v ->
                           Obj.magic
                             (Repr
                                ((),
                                  (fun buf ->
                                     fun len ->
                                       fun pos ->
                                         let h = FStar_HyperStack_ST.get () in
                                         ICorrect ((), pos))))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
let (cast :
  LowParse_Writers_Parser.parser ->
    LowParse_Writers_Parser.parser ->
      unit -> unit -> unit -> unit -> rptr -> rptr)
  =
  fun p1 ->
    fun p2 -> fun precond -> fun f -> fun v -> fun inv -> fun x1 -> x1




type ('p1, 'precond) check_precond_t =
  FStar_UInt8.t LowStar_Buffer.buffer ->
    FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t -> Prims.bool

let (check_precond_impl :
  LowParse_Writers_Parser.parser ->
    unit ->
      (unit, Obj.t) check_precond_t ->
        unit ->
          LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
            FStar_UInt32.t ->
              (LowParse_Writers_Parser.u8, unit) buffer_offset ->
                unit iresult)
  =
  fun p1 ->
    fun precond ->
      fun c ->
        fun inv ->
          fun b ->
            fun len ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let uu___ =
                  c b len (FStar_UInt32.uint_to_t Prims.int_zero) pos in
                if uu___
                then
                  let h' = FStar_HyperStack_ST.get () in ICorrect ((), pos)
                else IError "check_precond failed"
let (check_precond_repr :
  LowParse_Writers_Parser.parser ->
    unit ->
      (unit, Obj.t) check_precond_t ->
        unit -> (unit, unit, unit, Obj.t, unit, unit, unit) repr)
  =
  fun p1 ->
    fun precond ->
      fun c ->
        fun inv ->
          Repr
            ((),
              (fun b ->
                 fun len ->
                   fun pos ->
                     let h = FStar_HyperStack_ST.get () in
                     let uu___ =
                       c b len (FStar_UInt32.uint_to_t Prims.int_zero) pos in
                     if uu___
                     then
                       let h' = FStar_HyperStack_ST.get () in
                       ICorrect ((), pos)
                     else IError "check_precond failed"))
let (check_precond :
  LowParse_Writers_Parser.parser ->
    unit ->
      (unit, Obj.t) check_precond_t ->
        unit -> (unit, unit, unit, unit, unit, unit, unit) repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun p1 ->
             fun precond ->
               fun c ->
                 fun inv ->
                   Obj.magic
                     (Repr
                        ((),
                          (fun b ->
                             fun len ->
                               fun pos ->
                                 let h = FStar_HyperStack_ST.get () in
                                 let uu___ =
                                   c b len
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     pos in
                                 if uu___
                                 then
                                   let h' = FStar_HyperStack_ST.get () in
                                   ICorrect ((), pos)
                                 else IError "check_precond failed"))))
            uu___3 uu___2 uu___1 uu___

let (cat_impl :
  unit ->
    LowParse_Writers_Parser.parser ->
      rptr ->
        LowParse_Writers_Parser.u8 LowStar_Buffer.buffer ->
          FStar_UInt32.t ->
            (LowParse_Writers_Parser.u8, unit) buffer_offset -> unit iresult)
  =
  fun inv ->
    fun p ->
      fun x ->
        fun b ->
          fun len ->
            fun uu___ ->
              if FStar_UInt32.lt len x.rptr_len
              then IOverflow
              else
                (LowStar_Monotonic_Buffer.blit x.rptr_base
                   (FStar_UInt32.uint_to_t Prims.int_zero) b
                   (FStar_UInt32.uint_to_t Prims.int_zero) x.rptr_len;
                 (let h' = FStar_HyperStack_ST.get () in
                  ICorrect ((), (x.rptr_len))))
let (cat :
  unit ->
    LowParse_Writers_Parser.parser ->
      rptr -> (unit, unit, unit, unit, unit, Prims.l_False, unit) repr)
  =
  fun inv ->
    fun p ->
      fun x ->
        Repr
          ((),
            (fun b ->
               fun len ->
                 fun uu___ ->
                   if FStar_UInt32.lt len x.rptr_len
                   then IOverflow
                   else
                     (LowStar_Monotonic_Buffer.blit x.rptr_base
                        (FStar_UInt32.uint_to_t Prims.int_zero) b
                        (FStar_UInt32.uint_to_t Prims.int_zero) x.rptr_len;
                      (let h' = FStar_HyperStack_ST.get () in
                       ICorrect ((), (x.rptr_len))))))