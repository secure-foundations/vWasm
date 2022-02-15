open Prims
type strong_parser_kind = LowParse_Spec_Base.parser_kind
type ('c, 'uuuuu, 'uuuuu1) preorder = Obj.t
type ('uuuuu, 'uuuuu1) mut_p = unit
type const_slice =
  | MkSlice of LowParse_Bytes.byte LowStar_ConstBuffer.const_buffer *
  FStar_UInt32.t 
let (uu___is_MkSlice : const_slice -> Prims.bool) = fun projectee -> true
let (__proj__MkSlice__item__base :
  const_slice -> LowParse_Bytes.byte LowStar_ConstBuffer.const_buffer) =
  fun projectee -> match projectee with | MkSlice (base, slice_len) -> base
let (__proj__MkSlice__item__slice_len : const_slice -> FStar_UInt32.t) =
  fun projectee ->
    match projectee with | MkSlice (base, slice_len) -> slice_len
let (to_slice : const_slice -> (Obj.t, Obj.t) LowParse_Slice.slice) =
  fun x ->
    {
      LowParse_Slice.base =
        (LowStar_ConstBuffer.cast (__proj__MkSlice__item__base x));
      LowParse_Slice.len = (__proj__MkSlice__item__slice_len x)
    }
let (of_slice :
  ((unit, unit) mut_p, (unit, unit) mut_p) LowParse_Slice.slice ->
    const_slice)
  =
  fun x ->
    let b =
      LowStar_ConstBuffer.of_buffer
        (match x with
         | { LowParse_Slice.base = base; LowParse_Slice.len = len;_} -> base) in
    let len =
      match x with
      | { LowParse_Slice.base = base; LowParse_Slice.len = len1;_} -> len1 in
    MkSlice (b, len)
type ('h, 'c) live_slice =
  (LowParse_Bytes.byte, unit, unit) LowStar_ConstBuffer.live








type 't repr_ptr =
  | Ptr of LowParse_Bytes.byte LowStar_ConstBuffer.const_buffer * unit * 't *
  FStar_UInt32.t 
let uu___is_Ptr : 't . 't repr_ptr -> Prims.bool = fun projectee -> true
let __proj__Ptr__item__b :
  't . 't repr_ptr -> LowParse_Bytes.byte LowStar_ConstBuffer.const_buffer =
  fun projectee -> match projectee with | Ptr (b, meta, vv, length) -> b

let __proj__Ptr__item__vv : 't . 't repr_ptr -> 't =
  fun projectee -> match projectee with | Ptr (b, meta, vv, length) -> vv
let __proj__Ptr__item__length : 't . 't repr_ptr -> FStar_UInt32.t =
  fun projectee -> match projectee with | Ptr (b, meta, vv, length) -> length


type ('t, 'k, 'parser) repr_ptr_p = 't repr_ptr

type ('a, 'b, 'p2, 'p1) sub_ptr = unit

type ('t, 'r, 's, 'slice, 'meta, 'h) valid_slice = unit
type ('t, 'p, 'h) valid' = unit
type ('t, 'p, 'h) valid = unit



let length :
  't .
    't repr_ptr ->
      (unit ->
         unit ->
           (Obj.t, Obj.t) LowParse_Slice.slice ->
             FStar_UInt32.t -> FStar_UInt32.t)
        -> FStar_UInt32.t
  =
  fun p ->
    fun j ->
      let s =
        {
          LowParse_Slice.base =
            (LowStar_ConstBuffer.cast (__proj__Ptr__item__b p));
          LowParse_Slice.len = (__proj__Ptr__item__length p)
        } in
      j () () s (FStar_UInt32.uint_to_t Prims.int_zero)
let to_bytes : 't . 't repr_ptr -> FStar_UInt32.t -> FStar_Bytes.bytes =
  fun p ->
    fun len ->
      FStar_Bytes.of_buffer len () ()
        (LowStar_ConstBuffer.cast (__proj__Ptr__item__b p))
type ('t, 'p) valid_if_live = unit
type 't stable_repr_ptr = 't repr_ptr


let recall_stable_repr_ptr : 't . 't stable_repr_ptr -> unit =
  fun r ->
    let h1 = FStar_HyperStack_ST.get () in
    let i = LowStar_ConstBuffer.to_ibuffer (__proj__Ptr__item__b r) in
    Obj.magic (fun h -> ()); LowStar_ImmutableBuffer.recall_value i ()
type ('t, 'p) is_stable_in_region = unit
type ('r, 't) stable_region_repr_ptr = 't repr_ptr
let recall_stable_region_repr_ptr :
  't . FStar_HyperStack_ST.drgn -> (unit, 't) stable_region_repr_ptr -> unit
  =
  fun r ->
    fun p ->
      LowStar_Monotonic_Buffer.recall
        (LowStar_ConstBuffer.cast (__proj__Ptr__item__b p));
      recall_stable_repr_ptr p
let (ralloc_and_blit :
  FStar_HyperStack_ST.drgn ->
    LowParse_Bytes.byte LowStar_ConstBuffer.const_buffer ->
      FStar_UInt32.t -> LowParse_Bytes.byte LowStar_ConstBuffer.const_buffer)
  =
  fun r ->
    fun src ->
      fun len ->
        let src_buf = LowStar_ConstBuffer.cast src in
        let b =
          LowStar_Monotonic_Buffer.mmalloc_drgn_and_blit r src_buf
            (FStar_UInt32.uint_to_t Prims.int_zero) len in
        let h0 = FStar_HyperStack_ST.get () in
        LowStar_Monotonic_Buffer.witness_p b ();
        LowStar_ConstBuffer.of_ibuffer b
let (stash :
  FStar_HyperStack_ST.drgn ->
    unit ->
      Obj.t repr_ptr ->
        FStar_UInt32.t -> (unit, Obj.t) stable_region_repr_ptr)
  =
  fun rgn ->
    fun t ->
      fun r ->
        fun len ->
          let buf' = ralloc_and_blit rgn (__proj__Ptr__item__b r) len in
          let s = MkSlice (buf', len) in
          let h = FStar_HyperStack_ST.get () in
          let p =
            Ptr
              (buf', (), (__proj__Ptr__item__vv r),
                (__proj__Ptr__item__length r)) in
          p
type ('k1, 'k2, 't1, 't2, 'p1, 'p2) field_accessor =
  | FieldAccessor of ('t1, 't2) LowParse_Low_Base_Spec.clens * unit *
  (unit ->
     unit ->
       (Obj.t, Obj.t) LowParse_Slice.slice ->
         FStar_UInt32.t -> FStar_UInt32.t)
  *
  (unit ->
     unit ->
       (Obj.t, Obj.t) LowParse_Slice.slice ->
         FStar_UInt32.t -> FStar_UInt32.t)
  *
  (LowParse_SLow_Base.bytes32 ->
     ('t2 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  
let (uu___is_FieldAccessor :
  strong_parser_kind ->
    strong_parser_kind ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                Prims.bool)
  =
  fun k1 ->
    fun k2 -> fun t1 -> fun t2 -> fun p1 -> fun p2 -> fun projectee -> true
let (__proj__FieldAccessor__item__cl :
  strong_parser_kind ->
    strong_parser_kind ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun k1 ->
    fun k2 ->
      fun t1 ->
        fun t2 ->
          fun p1 ->
            fun p2 ->
              fun projectee ->
                match projectee with
                | FieldAccessor (cl, g, acc, jump, p2') -> cl

let (__proj__FieldAccessor__item__acc :
  strong_parser_kind ->
    strong_parser_kind ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun k2 ->
      fun t1 ->
        fun t2 ->
          fun p1 ->
            fun p2 ->
              fun projectee ->
                match projectee with
                | FieldAccessor (cl, g, acc, jump, p2') -> acc
let (__proj__FieldAccessor__item__jump :
  strong_parser_kind ->
    strong_parser_kind ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun k2 ->
      fun t1 ->
        fun t2 ->
          fun p1 ->
            fun p2 ->
              fun projectee ->
                match projectee with
                | FieldAccessor (cl, g, acc, jump, p2') -> jump
let (__proj__FieldAccessor__item__p2' :
  strong_parser_kind ->
    strong_parser_kind ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k1 ->
    fun k2 ->
      fun t1 ->
        fun t2 ->
          fun p1 ->
            fun p2 ->
              fun projectee ->
                match projectee with
                | FieldAccessor (cl, g, acc, jump, p2') -> p2'
let (get_field :
  strong_parser_kind ->
    unit ->
      unit ->
        strong_parser_kind ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                (Obj.t, unit, unit) repr_ptr_p ->
                  (Obj.t, unit, unit) repr_ptr_p)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun k2 ->
          fun t2 ->
            fun p2 ->
              fun f ->
                fun p ->
                  match f with
                  | FieldAccessor (uu___, uu___1, acc, jump, p2') ->
                      let b =
                        {
                          LowParse_Slice.base =
                            (LowStar_ConstBuffer.cast
                               (__proj__Ptr__item__b p));
                          LowParse_Slice.len = (__proj__Ptr__item__length p)
                        } in
                      let pos =
                        acc () () b (FStar_UInt32.uint_to_t Prims.int_zero) in
                      let pos_to = jump () () b pos in
                      let q =
                        let c =
                          MkSlice
                            ((LowStar_ConstBuffer.of_qbuf ()
                                (match b with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len;_} -> base)),
                              (match b with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len;_} -> len)) in
                        let h = FStar_HyperStack_ST.get () in
                        let slice = to_slice c in
                        let sub_b =
                          LowStar_ConstBuffer.sub
                            (__proj__MkSlice__item__base c) pos () in
                        let value =
                          let sub_b_bytes =
                            FStar_Bytes.of_buffer
                              (FStar_UInt32.sub pos_to pos) () ()
                              (LowStar_ConstBuffer.cast sub_b) in
                          let uu___2 = p2' sub_b_bytes in
                          match uu___2 with
                          | FStar_Pervasives_Native.Some (v, uu___3) -> v in
                        let p3 =
                          Ptr
                            (sub_b, (), value, (FStar_UInt32.sub pos_to pos)) in
                        let h1 = FStar_HyperStack_ST.get () in
                        let slice' =
                          {
                            LowParse_Slice.base =
                              (LowStar_ConstBuffer.cast sub_b);
                            LowParse_Slice.len =
                              (FStar_UInt32.sub pos_to pos)
                          } in
                        p3 in
                      let h = FStar_HyperStack_ST.get () in q
type ('k1, 't1, 'p1, 't2) field_reader =
  | FieldReader of strong_parser_kind * unit * ('t1, 't2)
  LowParse_Low_Base_Spec.clens * unit *
  (unit ->
     unit ->
       (Obj.t, Obj.t) LowParse_Slice.slice ->
         FStar_UInt32.t -> FStar_UInt32.t)
  *
  (unit ->
     unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 't2)
  
let (uu___is_FieldReader :
  strong_parser_kind ->
    unit ->
      unit -> unit -> (unit, Obj.t, unit, Obj.t) field_reader -> Prims.bool)
  = fun k1 -> fun t1 -> fun p1 -> fun t2 -> fun projectee -> true
let (__proj__FieldReader__item__k2 :
  strong_parser_kind ->
    unit ->
      unit ->
        unit -> (unit, Obj.t, unit, Obj.t) field_reader -> strong_parser_kind)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun t2 ->
          fun projectee ->
            match projectee with
            | FieldReader (k2, p2, cl, g, acc, reader) -> k2

let (__proj__FieldReader__item__cl :
  strong_parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit, Obj.t, unit, Obj.t) field_reader ->
            (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun t2 ->
          fun projectee ->
            match projectee with
            | FieldReader (k2, p2, cl, g, acc, reader) -> cl

let (__proj__FieldReader__item__acc :
  strong_parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit, Obj.t, unit, Obj.t) field_reader ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun t2 ->
          fun projectee ->
            match projectee with
            | FieldReader (k2, p2, cl, g, acc, reader) -> acc
let (__proj__FieldReader__item__reader :
  strong_parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit, Obj.t, unit, Obj.t) field_reader ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> Obj.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun t2 ->
          fun projectee ->
            match projectee with
            | FieldReader (k2, p2, cl, g, acc, reader) -> reader
type ('k1, 't1, 'p1, 't2, 'f) field_reader_t =
  ('t1, unit, unit) repr_ptr_p -> 't2
let (read_field :
  strong_parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit, Obj.t, unit, Obj.t) field_reader ->
            (Obj.t, unit, unit) repr_ptr_p -> Obj.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun t2 ->
          fun f ->
            fun p ->
              match f with
              | FieldReader (uu___, uu___1, uu___2, uu___3, acc, reader) ->
                  let b =
                    {
                      LowParse_Slice.base =
                        (LowStar_ConstBuffer.cast (__proj__Ptr__item__b p));
                      LowParse_Slice.len = (__proj__Ptr__item__length p)
                    } in
                  let pos =
                    acc () () b (FStar_UInt32.uint_to_t Prims.int_zero) in
                  reader () () b pos
type 'b index = FStar_UInt32.t
type ('t, 'b) repr_pos =
  | Pos of unit index * unit * 't * FStar_UInt32.t 
let uu___is_Pos : 't . const_slice -> ('t, unit) repr_pos -> Prims.bool =
  fun b -> fun projectee -> true
let __proj__Pos__item__start_pos :
  't . const_slice -> ('t, unit) repr_pos -> unit index =
  fun b ->
    fun projectee ->
      match projectee with
      | Pos (start_pos, meta, vv_pos, length1) -> start_pos

let __proj__Pos__item__vv_pos : 't . const_slice -> ('t, unit) repr_pos -> 't
  =
  fun b ->
    fun projectee ->
      match projectee with | Pos (start_pos, meta, vv_pos, length1) -> vv_pos
let __proj__Pos__item__length :
  't . const_slice -> ('t, unit) repr_pos -> FStar_UInt32.t =
  fun b ->
    fun projectee ->
      match projectee with
      | Pos (start_pos, meta, vv_pos, length1) -> length1



type ('t, 'b, 'k, 'parser) repr_pos_p = ('t, unit) repr_pos
type ('t, 'b, 'r, 'h) valid_repr_pos = unit


let end_pos : 't . const_slice -> ('t, unit) repr_pos -> unit index =
  fun b ->
    fun r ->
      FStar_UInt32.add (__proj__Pos__item__start_pos b r)
        (__proj__Pos__item__length b r)

let as_ptr : 't . const_slice -> ('t, unit) repr_pos -> 't repr_ptr =
  fun b ->
    fun r ->
      let b1 =
        LowStar_ConstBuffer.sub (__proj__MkSlice__item__base b)
          (__proj__Pos__item__start_pos b r) () in
      let v = __proj__Pos__item__vv_pos b r in
      let l = __proj__Pos__item__length b r in Ptr (b1, (), v, l)
let as_repr_pos :
  't .
    const_slice ->
      unit index -> unit index -> 't repr_ptr -> ('t, unit) repr_pos
  =
  fun b ->
    fun from ->
      fun to1 ->
        fun p ->
          Pos
            (from, (), (__proj__Ptr__item__vv p),
              (FStar_UInt32.sub to1 from))
let (mk_repr_pos :
  strong_parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          ((unit, unit) mut_p, (unit, unit) mut_p) LowParse_Slice.slice ->
            unit index -> unit index -> (Obj.t, unit, unit, unit) repr_pos_p)
  =
  fun k ->
    fun t ->
      fun parser ->
        fun parser32 ->
          fun b ->
            fun from ->
              fun to1 ->
                let uu___ =
                  let c =
                    MkSlice
                      ((LowStar_ConstBuffer.of_qbuf ()
                          (match b with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len;_} -> Obj.magic base)),
                        (match b with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len;_} -> len)) in
                  let h = FStar_HyperStack_ST.get () in
                  let slice = to_slice c in
                  let sub_b =
                    LowStar_ConstBuffer.sub (__proj__MkSlice__item__base c)
                      from () in
                  let value =
                    let sub_b_bytes =
                      FStar_Bytes.of_buffer (FStar_UInt32.sub to1 from) () ()
                        (LowStar_ConstBuffer.cast sub_b) in
                    let uu___1 = parser32 sub_b_bytes in
                    match uu___1 with
                    | FStar_Pervasives_Native.Some (v, uu___2) -> v in
                  let p = Ptr (sub_b, (), value, (FStar_UInt32.sub to1 from)) in
                  let h1 = FStar_HyperStack_ST.get () in
                  let slice' =
                    {
                      LowParse_Slice.base = (LowStar_ConstBuffer.cast sub_b);
                      LowParse_Slice.len = (FStar_UInt32.sub to1 from)
                    } in
                  p in
                as_repr_pos (of_slice b) from to1 uu___
let (mk_repr_pos_from_const_slice :
  strong_parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          const_slice ->
            unit index -> unit index -> (Obj.t, unit, unit, unit) repr_pos_p)
  =
  fun k ->
    fun t ->
      fun parser ->
        fun parser32 ->
          fun b ->
            fun from ->
              fun to1 ->
                let uu___ =
                  let h = FStar_HyperStack_ST.get () in
                  let slice = to_slice b in
                  let sub_b =
                    LowStar_ConstBuffer.sub (__proj__MkSlice__item__base b)
                      from () in
                  let value =
                    let sub_b_bytes =
                      FStar_Bytes.of_buffer (FStar_UInt32.sub to1 from) () ()
                        (LowStar_ConstBuffer.cast sub_b) in
                    let uu___1 = parser32 sub_b_bytes in
                    match uu___1 with
                    | FStar_Pervasives_Native.Some (v, uu___2) -> v in
                  let p = Ptr (sub_b, (), value, (FStar_UInt32.sub to1 from)) in
                  let h1 = FStar_HyperStack_ST.get () in
                  let slice' =
                    {
                      LowParse_Slice.base = (LowStar_ConstBuffer.cast sub_b);
                      LowParse_Slice.len = (FStar_UInt32.sub to1 from)
                    } in
                  p in
                as_repr_pos b from to1 uu___
type ('b, 't1, 'p, 'k2, 't2, 'p2, 'f, 'h0, 'q, 'h1) field_accessor_pos_post =
  unit
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'f) get_field_pos_t =
  const_slice ->
    ('t1, unit, unit, unit) repr_pos_p -> ('t2, unit, unit, unit) repr_pos_p
let (get_field_pos :
  strong_parser_kind ->
    unit ->
      unit ->
        strong_parser_kind ->
          unit ->
            unit ->
              (unit, unit, Obj.t, Obj.t, unit, unit) field_accessor ->
                const_slice ->
                  (Obj.t, unit, unit, unit) repr_pos_p ->
                    (Obj.t, unit, unit, unit) repr_pos_p)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun k2 ->
          fun t2 ->
            fun p2 ->
              fun f ->
                fun b ->
                  fun pp ->
                    match f with
                    | FieldAccessor (uu___, uu___1, acc, jump, p2') ->
                        let p = as_ptr b pp in
                        let bb =
                          {
                            LowParse_Slice.base =
                              (LowStar_ConstBuffer.cast
                                 (__proj__Ptr__item__b p));
                            LowParse_Slice.len =
                              (__proj__Ptr__item__length p)
                          } in
                        let pos =
                          acc () () bb
                            (FStar_UInt32.uint_to_t Prims.int_zero) in
                        let pos_to = jump () () bb pos in
                        let q =
                          let c =
                            MkSlice
                              ((LowStar_ConstBuffer.of_qbuf ()
                                  (match bb with
                                   | { LowParse_Slice.base = base;
                                       LowParse_Slice.len = len;_} -> base)),
                                (match bb with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len;_} -> len)) in
                          let h = FStar_HyperStack_ST.get () in
                          let slice = to_slice c in
                          let sub_b =
                            LowStar_ConstBuffer.sub
                              (__proj__MkSlice__item__base c) pos () in
                          let value =
                            let sub_b_bytes =
                              FStar_Bytes.of_buffer
                                (FStar_UInt32.sub pos_to pos) () ()
                                (LowStar_ConstBuffer.cast sub_b) in
                            let uu___2 = p2' sub_b_bytes in
                            match uu___2 with
                            | FStar_Pervasives_Native.Some (v, uu___3) -> v in
                          let p3 =
                            Ptr
                              (sub_b, (), value,
                                (FStar_UInt32.sub pos_to pos)) in
                          let h1 = FStar_HyperStack_ST.get () in
                          let slice' =
                            {
                              LowParse_Slice.base =
                                (LowStar_ConstBuffer.cast sub_b);
                              LowParse_Slice.len =
                                (FStar_UInt32.sub pos_to pos)
                            } in
                          p3 in
                        let len = FStar_UInt32.sub pos_to pos in
                        as_repr_pos b
                          (FStar_UInt32.add
                             (__proj__Pos__item__start_pos b pp) pos)
                          (FStar_UInt32.add
                             (FStar_UInt32.add
                                (__proj__Pos__item__start_pos b pp) pos) len)
                          q
type ('k1, 't1, 'p1, 't2, 'f) read_field_pos_t =
  const_slice -> ('t1, unit, unit, unit) repr_pos_p -> 't2
let (read_field_pos :
  strong_parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit, Obj.t, unit, Obj.t) field_reader ->
            const_slice -> (Obj.t, unit, unit, unit) repr_pos_p -> Obj.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun t2 ->
          fun f ->
            fun b ->
              fun p ->
                let uu___ = as_ptr b p in
                match f with
                | FieldReader (uu___1, uu___2, uu___3, uu___4, acc, reader)
                    ->
                    let b1 =
                      {
                        LowParse_Slice.base =
                          (LowStar_ConstBuffer.cast
                             (__proj__Ptr__item__b uu___));
                        LowParse_Slice.len =
                          (__proj__Ptr__item__length uu___)
                      } in
                    let pos =
                      acc () () b1 (FStar_UInt32.uint_to_t Prims.int_zero) in
                    reader () () b1 pos