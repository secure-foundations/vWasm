open Prims
type ('tot, 't, 'cl, 'bitsumuusize) bitsum' =
  | BitStop of unit 
  | BitField of Prims.nat * (unit, 't, unit, unit) bitsum' 
  | BitSum' of unit * Prims.nat * (Obj.t, 't) LowParse_Spec_Enum.enum *
  (Obj.t -> (unit, 't, unit, unit) bitsum') 
let (uu___is_BitStop :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee ->
            match projectee with | BitStop _0 -> true | uu___ -> false

let (uu___is_BitField :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee ->
            match projectee with
            | BitField (sz, rest) -> true
            | uu___ -> false
let (__proj__BitField__item__sz :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Prims.nat)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee -> match projectee with | BitField (sz, rest) -> sz
let (__proj__BitField__item__rest :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            (unit, Obj.t, unit, unit) bitsum')
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee -> match projectee with | BitField (sz, rest) -> rest
let (uu___is_BitSum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee ->
            match projectee with
            | BitSum' (key, key_size, e, payload) -> true
            | uu___ -> false
let (__proj__BitSum'__item__key_size :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Prims.nat)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee ->
            match projectee with
            | BitSum' (key, key_size, e, payload) -> key_size
let (__proj__BitSum'__item__e :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            (unit, Obj.t) LowParse_Spec_Enum.enum)
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun tot ->
               fun t ->
                 fun cl ->
                   fun bitsum'_size ->
                     fun projectee ->
                       match projectee with
                       | BitSum' (key, key_size, e, payload) -> Obj.magic e)
              uu___4 uu___3 uu___2 uu___1 uu___
let (__proj__BitSum'__item__payload :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            Obj.t -> (unit, Obj.t, unit, unit) bitsum')
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun projectee ->
            match projectee with
            | BitSum' (key, key_size, e, payload) -> payload
type ('tot, 't, 'cl, 'bitsumuusize, 'b) bitsum'_type' = Obj.t
type ('tot, 't, 'cl, 'bitsumuusize, 'b) bitsum'_type = Obj.t
type ('tot, 't, 'cl, 'bitsumuusize, 'sz, 'rest) bitsum'_type_bitfield =
  ('t * Obj.t)
type ('tot, 't, 'cl, 'bitsumuusize, 'key, 'keyusize, 'e,
  'payload) bitsum'_type_bitsum' = ('key, Obj.t) Prims.dtuple2
type filter_bitsum'_t_attr
let (bitsum'_type_elim_BitSum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  Obj.t ->
                    (unit, Obj.t, unit, unit, Obj.t, unit, unit, unit)
                      bitsum'_type_bitsum')
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
                    (fun tot ->
                       fun t ->
                         fun cl ->
                           fun bitsum'_size ->
                             fun key ->
                               fun key_size ->
                                 fun e -> fun payload -> fun x -> Obj.magic x)
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let (bitsum'_type_intro_BitSum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (unit, Obj.t, unit, unit, Obj.t, unit, unit, unit)
                    bitsum'_type_bitsum' -> Obj.t)
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
                    (fun tot ->
                       fun t ->
                         fun cl ->
                           fun bitsum'_size ->
                             fun key ->
                               fun key_size ->
                                 fun e -> fun payload -> fun x -> Obj.magic x)
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let (bitsum'_type_elim_BitField :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat ->
            (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> (Obj.t * Obj.t))
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun tot ->
                   fun t ->
                     fun cl ->
                       fun bitsum'_size ->
                         fun sz -> fun rest -> fun x -> Obj.magic x) uu___6
                  uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (bitsum'_type_intro_BitField :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat ->
            (unit, Obj.t, unit, unit) bitsum' -> (Obj.t * Obj.t) -> Obj.t)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun tot ->
                   fun t ->
                     fun cl ->
                       fun bitsum'_size ->
                         fun sz -> fun rest -> fun x -> Obj.magic x) uu___6
                  uu___5 uu___4 uu___3 uu___2 uu___1 uu___
type ('tot, 't, 'cl, 'bitsumuusize, 'b) bitsum'_key_type = Obj.t
let (bitsum'_key_type_elim_BitSum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  Obj.t -> (Obj.t, Obj.t) Prims.dtuple2)
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
                    (fun tot ->
                       fun t ->
                         fun cl ->
                           fun bitsum'_size ->
                             fun key ->
                               fun key_size ->
                                 fun e -> fun payload -> fun x -> Obj.magic x)
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let (bitsum'_key_type_intro_BitSum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t, Obj.t) Prims.dtuple2 -> Obj.t)
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
                    (fun tot ->
                       fun t ->
                         fun cl ->
                           fun bitsum'_size ->
                             fun key ->
                               fun key_size ->
                                 fun e -> fun payload -> fun x -> Obj.magic x)
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let coerce : 't2 't1 . 't1 -> 't2 = fun uu___ -> (fun x -> Obj.magic x) uu___
let (bitsum'_key_type_intro_BitField :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t -> fun cl -> fun bitsum'_size -> fun sz -> fun rest -> fun x -> x
let (bitsum'_key_type_elim_BitField :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t -> fun cl -> fun bitsum'_size -> fun sz -> fun rest -> fun x -> x
let rec (filter_bitsum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun x ->
              match b with
              | BitStop uu___ -> true
              | BitField (uu___, rest) ->
                  filter_bitsum' tot () cl (bitsum'_size - uu___) rest x
              | BitSum' (key, key_size, e, payload) ->
                  let f =
                    (match cl with
                     | { LowParse_BitFields.v = v;
                         LowParse_BitFields.uint_to_t = uint_to_t;
                         LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                         LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                         LowParse_BitFields.get_bitfield_gen =
                           get_bitfield_gen;
                         LowParse_BitFields.set_bitfield_gen =
                           set_bitfield_gen;
                         LowParse_BitFields.get_bitfield = get_bitfield;
                         LowParse_BitFields.set_bitfield = set_bitfield;
                         LowParse_BitFields.logor = logor;
                         LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
                         LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_}
                         -> get_bitfield) x (bitsum'_size - key_size)
                      bitsum'_size in
                  if
                    LowParse_Spec_Enum.list_mem f
                      (LowParse_Spec_Enum.list_map
                         FStar_Pervasives_Native.snd e)
                  then
                    let k = LowParse_Spec_Enum.enum_key_of_repr e f in
                    filter_bitsum' tot () cl (bitsum'_size - key_size)
                      (payload k) x
                  else false
let rec (synth_bitsum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun x ->
              match b with
              | BitStop uu___ -> Obj.repr ()
              | BitField (sz, rest) ->
                  Obj.repr
                    (((match cl with
                       | { LowParse_BitFields.v = v;
                           LowParse_BitFields.uint_to_t = uint_to_t;
                           LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                           LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                           LowParse_BitFields.get_bitfield_gen =
                             get_bitfield_gen;
                           LowParse_BitFields.set_bitfield_gen =
                             set_bitfield_gen;
                           LowParse_BitFields.get_bitfield = get_bitfield;
                           LowParse_BitFields.set_bitfield = set_bitfield;
                           LowParse_BitFields.logor = logor;
                           LowParse_BitFields.bitfield_eq_lhs =
                             bitfield_eq_lhs;
                           LowParse_BitFields.bitfield_eq_rhs =
                             bitfield_eq_rhs;_}
                           -> get_bitfield) x (bitsum'_size - sz)
                        bitsum'_size),
                      (synth_bitsum' tot () cl (bitsum'_size - sz) rest x))
              | BitSum' (key, key_size, e, payload) ->
                  Obj.repr
                    (let f =
                       (match cl with
                        | { LowParse_BitFields.v = v;
                            LowParse_BitFields.uint_to_t = uint_to_t;
                            LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                            LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                            LowParse_BitFields.get_bitfield_gen =
                              get_bitfield_gen;
                            LowParse_BitFields.set_bitfield_gen =
                              set_bitfield_gen;
                            LowParse_BitFields.get_bitfield = get_bitfield;
                            LowParse_BitFields.set_bitfield = set_bitfield;
                            LowParse_BitFields.logor = logor;
                            LowParse_BitFields.bitfield_eq_lhs =
                              bitfield_eq_lhs;
                            LowParse_BitFields.bitfield_eq_rhs =
                              bitfield_eq_rhs;_}
                            -> get_bitfield) x (bitsum'_size - key_size)
                         bitsum'_size in
                     let k = LowParse_Spec_Enum.enum_key_of_repr e f in
                     let z =
                       synth_bitsum' tot () cl (bitsum'_size - key_size)
                         (payload k) x in
                     let p = Prims.Mkdtuple2 (k, z) in p)




let rec (synth_bitsum'_recip' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun x ->
              match b with
              | BitStop uu___ ->
                  (match cl with
                   | { LowParse_BitFields.v = v;
                       LowParse_BitFields.uint_to_t = uint_to_t;
                       LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                       LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                       LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
                       LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
                       LowParse_BitFields.get_bitfield = get_bitfield;
                       LowParse_BitFields.set_bitfield = set_bitfield;
                       LowParse_BitFields.logor = logor;
                       LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
                       LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_}
                       -> uint_to_t Prims.int_zero)
              | BitField (sz, rest) ->
                  let uu___ = Obj.magic x in
                  (match uu___ with
                   | (hd, tl) ->
                       ((match cl with
                         | { LowParse_BitFields.v = v;
                             LowParse_BitFields.uint_to_t = uint_to_t;
                             LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                             LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                             LowParse_BitFields.get_bitfield_gen =
                               get_bitfield_gen;
                             LowParse_BitFields.set_bitfield_gen =
                               set_bitfield_gen;
                             LowParse_BitFields.get_bitfield = get_bitfield;
                             LowParse_BitFields.set_bitfield = set_bitfield;
                             LowParse_BitFields.logor = logor;
                             LowParse_BitFields.bitfield_eq_lhs =
                               bitfield_eq_lhs;
                             LowParse_BitFields.bitfield_eq_rhs =
                               bitfield_eq_rhs;_}
                             -> set_bitfield))
                         (synth_bitsum'_recip' tot () cl (bitsum'_size - sz)
                            rest tl) (bitsum'_size - sz) bitsum'_size hd)
              | BitSum' (key, key_size, e, payload) ->
                  let uu___ = Obj.magic x in
                  (match uu___ with
                   | Prims.Mkdtuple2 (k, tl) ->
                       let y1 =
                         synth_bitsum'_recip' tot () cl
                           (bitsum'_size - key_size) (payload k) tl in
                       let y2 =
                         (match cl with
                          | { LowParse_BitFields.v = v;
                              LowParse_BitFields.uint_to_t = uint_to_t;
                              LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                              LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                              LowParse_BitFields.get_bitfield_gen =
                                get_bitfield_gen;
                              LowParse_BitFields.set_bitfield_gen =
                                set_bitfield_gen;
                              LowParse_BitFields.get_bitfield = get_bitfield;
                              LowParse_BitFields.set_bitfield = set_bitfield;
                              LowParse_BitFields.logor = logor;
                              LowParse_BitFields.bitfield_eq_lhs =
                                bitfield_eq_lhs;
                              LowParse_BitFields.bitfield_eq_rhs =
                                bitfield_eq_rhs;_}
                              -> set_bitfield) y1 (bitsum'_size - key_size)
                           bitsum'_size
                           (LowParse_Spec_Enum.enum_repr_of_key e k) in
                       y2)



let (synth_bitsum'_recip :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b -> fun x -> synth_bitsum'_recip' tot () cl bitsum'_size b x




let rec (bitsum'_key_of_t :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun x ->
              match b with
              | BitStop uu___ -> Obj.repr ()
              | BitField (sz, rest) ->
                  Obj.repr
                    (match Obj.magic x with
                     | (uu___, tl) ->
                         bitsum'_key_of_t tot () cl (bitsum'_size - sz) rest
                           tl)
              | BitSum' (key, key_size, e, payload) ->
                  Obj.repr
                    (match Obj.magic x with
                     | Prims.Mkdtuple2 (k, pl) ->
                         Prims.Mkdtuple2
                           (k,
                             (bitsum'_key_of_t tot () cl
                                (bitsum'_size - key_size) (payload k) pl)))
let id : 't . 't -> 't = fun x -> x
type ('tot, 't, 'cl, 'b, 'data, 'taguofudata, 'typeuofutag) synth_case_t =
  | SynthCase of (Obj.t -> 'typeuofutag -> 'data) * unit *
  (Obj.t -> 'data -> 'typeuofutag) * unit 
let (uu___is_SynthCase :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        (unit, Obj.t, unit, unit) bitsum' ->
          unit ->
            (Obj.t -> Obj.t) ->
              unit ->
                (unit, Obj.t, unit, unit, Obj.t, unit, Obj.t) synth_case_t ->
                  Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun b ->
          fun data ->
            fun tag_of_data -> fun type_of_tag -> fun projectee -> true
let (__proj__SynthCase__item__f :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        (unit, Obj.t, unit, unit) bitsum' ->
          unit ->
            (Obj.t -> Obj.t) ->
              unit ->
                (unit, Obj.t, unit, unit, Obj.t, unit, Obj.t) synth_case_t ->
                  Obj.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun b ->
          fun data ->
            fun tag_of_data ->
              fun type_of_tag ->
                fun projectee ->
                  match projectee with | SynthCase (f, f_inj, g, f_g_eq) -> f

let (__proj__SynthCase__item__g :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        (unit, Obj.t, unit, unit) bitsum' ->
          unit ->
            (Obj.t -> Obj.t) ->
              unit ->
                (unit, Obj.t, unit, unit, Obj.t, unit, Obj.t) synth_case_t ->
                  Obj.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun b ->
          fun data ->
            fun tag_of_data ->
              fun type_of_tag ->
                fun projectee ->
                  match projectee with | SynthCase (f, f_inj, g, f_g_eq) -> g


let rec (weaken_parse_bitsum_cases_kind' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            (Obj.t -> LowParse_Spec_Base.parser_kind) ->
              (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun f ->
              match b with
              | BitStop uu___ -> Prims.Mkdtuple2 ((f (Obj.repr ())), ())
              | BitField (sz, rest) ->
                  let uu___ =
                    weaken_parse_bitsum_cases_kind' tot () cl
                      (bitsum'_size - sz) rest (fun x -> f x) in
                  (match uu___ with
                   | Prims.Mkdtuple2 (g, phi) -> Prims.Mkdtuple2 (g, ()))
              | BitSum' (key, key_size, e, payload) ->
                  let keys =
                    FStar_List_Tot_Base.map FStar_Pervasives_Native.fst e in
                  let phi x =
                    if FStar_List_Tot_Base.mem x keys
                    then
                      let uu___ =
                        weaken_parse_bitsum_cases_kind' tot () cl
                          (bitsum'_size - key_size) (payload x)
                          (fun z -> f (Obj.magic (Prims.Mkdtuple2 (x, z)))) in
                      match uu___ with
                      | Prims.Mkdtuple2 (k, g) -> Prims.Mkdtuple2 (k, ())
                    else
                      Prims.Mkdtuple2
                        (LowParse_Spec_Base.default_parser_kind, ()) in
                  let k =
                    LowParse_Spec_Base.glb_list_of
                      (fun x -> FStar_Pervasives.dfst (phi x)) keys in
                  Prims.Mkdtuple2 (k, ())
let (weaken_parse_bitsum_cases_kind :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        (unit, Obj.t, unit, unit) bitsum' ->
          unit ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              -> LowParse_Spec_Base.parser_kind)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun b ->
          fun type_of_tag ->
            fun f ->
              let uu___ =
                weaken_parse_bitsum_cases_kind' tot () cl tot b
                  (fun k -> FStar_Pervasives.dfst (f k)) in
              match uu___ with | Prims.Mkdtuple2 (k, phi) -> k


let (parse_bitsum_kind :
  LowParse_Spec_Base.parser_kind ->
    Prims.pos ->
      unit ->
        (unit, Obj.t) LowParse_BitFields.uint_t ->
          (unit, Obj.t, unit, unit) bitsum' ->
            unit ->
              (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                -> LowParse_Spec_Base.parser_kind)
  =
  fun kt ->
    fun tot ->
      fun t ->
        fun cl ->
          fun b ->
            fun type_of_tag ->
              fun f ->
                {
                  LowParse_Spec_Base.parser_kind_low =
                    ((match kt with
                      | {
                          LowParse_Spec_Base.parser_kind_low =
                            parser_kind_low;
                          LowParse_Spec_Base.parser_kind_high =
                            parser_kind_high;
                          LowParse_Spec_Base.parser_kind_subkind =
                            parser_kind_subkind;
                          LowParse_Spec_Base.parser_kind_metadata =
                            parser_kind_metadata;_}
                          -> parser_kind_low)
                       +
                       (match weaken_parse_bitsum_cases_kind tot () cl b () f
                        with
                        | {
                            LowParse_Spec_Base.parser_kind_low =
                              parser_kind_low;
                            LowParse_Spec_Base.parser_kind_high =
                              parser_kind_high;
                            LowParse_Spec_Base.parser_kind_subkind =
                              parser_kind_subkind;
                            LowParse_Spec_Base.parser_kind_metadata =
                              parser_kind_metadata;_}
                            -> parser_kind_low));
                  LowParse_Spec_Base.parser_kind_high =
                    (if
                       (if
                          match match kt with
                                | {
                                    LowParse_Spec_Base.parser_kind_low =
                                      parser_kind_low;
                                    LowParse_Spec_Base.parser_kind_high =
                                      parser_kind_high;
                                    LowParse_Spec_Base.parser_kind_subkind =
                                      parser_kind_subkind;
                                    LowParse_Spec_Base.parser_kind_metadata =
                                      parser_kind_metadata;_}
                                    -> parser_kind_high
                          with
                          | FStar_Pervasives_Native.Some uu___ -> true
                          | uu___ -> false
                        then
                          match match weaken_parse_bitsum_cases_kind tot ()
                                        cl b () f
                                with
                                | {
                                    LowParse_Spec_Base.parser_kind_low =
                                      parser_kind_low;
                                    LowParse_Spec_Base.parser_kind_high =
                                      parser_kind_high;
                                    LowParse_Spec_Base.parser_kind_subkind =
                                      parser_kind_subkind;
                                    LowParse_Spec_Base.parser_kind_metadata =
                                      parser_kind_metadata;_}
                                    -> parser_kind_high
                          with
                          | FStar_Pervasives_Native.Some uu___ -> true
                          | uu___ -> false
                        else false)
                     then
                       FStar_Pervasives_Native.Some
                         ((match match kt with
                                 | {
                                     LowParse_Spec_Base.parser_kind_low =
                                       parser_kind_low;
                                     LowParse_Spec_Base.parser_kind_high =
                                       parser_kind_high;
                                     LowParse_Spec_Base.parser_kind_subkind =
                                       parser_kind_subkind;
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
                                     -> parser_kind_high
                           with
                           | FStar_Pervasives_Native.Some y -> y) +
                            (match match weaken_parse_bitsum_cases_kind tot
                                           () cl b () f
                                   with
                                   | {
                                       LowParse_Spec_Base.parser_kind_low =
                                         parser_kind_low;
                                       LowParse_Spec_Base.parser_kind_high =
                                         parser_kind_high;
                                       LowParse_Spec_Base.parser_kind_subkind
                                         = parser_kind_subkind;
                                       LowParse_Spec_Base.parser_kind_metadata
                                         = parser_kind_metadata;_}
                                       -> parser_kind_high
                             with
                             | FStar_Pervasives_Native.Some y -> y))
                     else FStar_Pervasives_Native.None);
                  LowParse_Spec_Base.parser_kind_subkind =
                    (if
                       (match weaken_parse_bitsum_cases_kind tot () cl b () f
                        with
                        | {
                            LowParse_Spec_Base.parser_kind_low =
                              parser_kind_low;
                            LowParse_Spec_Base.parser_kind_high =
                              parser_kind_high;
                            LowParse_Spec_Base.parser_kind_subkind =
                              parser_kind_subkind;
                            LowParse_Spec_Base.parser_kind_metadata =
                              parser_kind_metadata;_}
                            -> parser_kind_subkind)
                         =
                         (FStar_Pervasives_Native.Some
                            LowParse_Spec_Base.ParserConsumesAll)
                     then
                       FStar_Pervasives_Native.Some
                         LowParse_Spec_Base.ParserConsumesAll
                     else
                       if
                         (if
                            (match kt with
                             | {
                                 LowParse_Spec_Base.parser_kind_low =
                                   parser_kind_low;
                                 LowParse_Spec_Base.parser_kind_high =
                                   parser_kind_high;
                                 LowParse_Spec_Base.parser_kind_subkind =
                                   parser_kind_subkind;
                                 LowParse_Spec_Base.parser_kind_metadata =
                                   parser_kind_metadata;_}
                                 -> parser_kind_subkind)
                              =
                              (FStar_Pervasives_Native.Some
                                 LowParse_Spec_Base.ParserStrong)
                          then
                            (match weaken_parse_bitsum_cases_kind tot () cl b
                                     () f
                             with
                             | {
                                 LowParse_Spec_Base.parser_kind_low =
                                   parser_kind_low;
                                 LowParse_Spec_Base.parser_kind_high =
                                   parser_kind_high;
                                 LowParse_Spec_Base.parser_kind_subkind =
                                   parser_kind_subkind;
                                 LowParse_Spec_Base.parser_kind_metadata =
                                   parser_kind_metadata;_}
                                 -> parser_kind_subkind)
                              =
                              (FStar_Pervasives_Native.Some
                                 LowParse_Spec_Base.ParserStrong)
                          else false)
                       then
                         FStar_Pervasives_Native.Some
                           LowParse_Spec_Base.ParserStrong
                       else
                         if
                           (if
                              (match weaken_parse_bitsum_cases_kind tot () cl
                                       b () f
                               with
                               | {
                                   LowParse_Spec_Base.parser_kind_low =
                                     parser_kind_low;
                                   LowParse_Spec_Base.parser_kind_high =
                                     parser_kind_high;
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     parser_kind_subkind;
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     parser_kind_metadata;_}
                                   -> parser_kind_high)
                                =
                                (FStar_Pervasives_Native.Some Prims.int_zero)
                            then
                              (match weaken_parse_bitsum_cases_kind tot () cl
                                       b () f
                               with
                               | {
                                   LowParse_Spec_Base.parser_kind_low =
                                     parser_kind_low;
                                   LowParse_Spec_Base.parser_kind_high =
                                     parser_kind_high;
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     parser_kind_subkind;
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     parser_kind_metadata;_}
                                   -> parser_kind_subkind)
                                =
                                (FStar_Pervasives_Native.Some
                                   LowParse_Spec_Base.ParserStrong)
                            else false)
                         then
                           (match kt with
                            | {
                                LowParse_Spec_Base.parser_kind_low =
                                  parser_kind_low;
                                LowParse_Spec_Base.parser_kind_high =
                                  parser_kind_high;
                                LowParse_Spec_Base.parser_kind_subkind =
                                  parser_kind_subkind;
                                LowParse_Spec_Base.parser_kind_metadata =
                                  parser_kind_metadata;_}
                                -> parser_kind_subkind)
                         else FStar_Pervasives_Native.None);
                  LowParse_Spec_Base.parser_kind_metadata =
                    (match ((match match kt with
                                   | {
                                       LowParse_Spec_Base.parser_kind_low =
                                         parser_kind_low;
                                       LowParse_Spec_Base.parser_kind_high =
                                         parser_kind_high;
                                       LowParse_Spec_Base.parser_kind_subkind
                                         = parser_kind_subkind;
                                       LowParse_Spec_Base.parser_kind_metadata
                                         = parser_kind_metadata;_}
                                       -> parser_kind_metadata
                             with
                             | FStar_Pervasives_Native.Some
                                 (LowParse_Spec_Base.ParserKindMetadataFail)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   LowParse_Spec_Base.ParserKindMetadataFail
                             | uu___ -> FStar_Pervasives_Native.None),
                             (match weaken_parse_bitsum_cases_kind tot () cl
                                      b () f
                              with
                              | {
                                  LowParse_Spec_Base.parser_kind_low =
                                    parser_kind_low;
                                  LowParse_Spec_Base.parser_kind_high =
                                    parser_kind_high;
                                  LowParse_Spec_Base.parser_kind_subkind =
                                    parser_kind_subkind;
                                  LowParse_Spec_Base.parser_kind_metadata =
                                    parser_kind_metadata;_}
                                  -> parser_kind_metadata))
                     with
                     | (FStar_Pervasives_Native.Some
                        (LowParse_Spec_Base.ParserKindMetadataFail), uu___)
                         ->
                         (match match kt with
                                | {
                                    LowParse_Spec_Base.parser_kind_low =
                                      parser_kind_low;
                                    LowParse_Spec_Base.parser_kind_high =
                                      parser_kind_high;
                                    LowParse_Spec_Base.parser_kind_subkind =
                                      parser_kind_subkind;
                                    LowParse_Spec_Base.parser_kind_metadata =
                                      parser_kind_metadata;_}
                                    -> parser_kind_metadata
                          with
                          | FStar_Pervasives_Native.Some
                              (LowParse_Spec_Base.ParserKindMetadataFail) ->
                              FStar_Pervasives_Native.Some
                                LowParse_Spec_Base.ParserKindMetadataFail
                          | uu___1 -> FStar_Pervasives_Native.None)
                     | (uu___, FStar_Pervasives_Native.Some
                        (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                         (match weaken_parse_bitsum_cases_kind tot () cl b ()
                                  f
                          with
                          | {
                              LowParse_Spec_Base.parser_kind_low =
                                parser_kind_low;
                              LowParse_Spec_Base.parser_kind_high =
                                parser_kind_high;
                              LowParse_Spec_Base.parser_kind_subkind =
                                parser_kind_subkind;
                              LowParse_Spec_Base.parser_kind_metadata =
                                parser_kind_metadata;_}
                              -> parser_kind_metadata)
                     | (FStar_Pervasives_Native.Some
                        (LowParse_Spec_Base.ParserKindMetadataTotal),
                        FStar_Pervasives_Native.Some
                        (LowParse_Spec_Base.ParserKindMetadataTotal)) ->
                         (match match kt with
                                | {
                                    LowParse_Spec_Base.parser_kind_low =
                                      parser_kind_low;
                                    LowParse_Spec_Base.parser_kind_high =
                                      parser_kind_high;
                                    LowParse_Spec_Base.parser_kind_subkind =
                                      parser_kind_subkind;
                                    LowParse_Spec_Base.parser_kind_metadata =
                                      parser_kind_metadata;_}
                                    -> parser_kind_metadata
                          with
                          | FStar_Pervasives_Native.Some
                              (LowParse_Spec_Base.ParserKindMetadataFail) ->
                              FStar_Pervasives_Native.Some
                                LowParse_Spec_Base.ParserKindMetadataFail
                          | uu___ -> FStar_Pervasives_Native.None)
                     | uu___ -> FStar_Pervasives_Native.None)
                }











type ('tot, 't, 'cl, 'bitsumuusize, 'b) filter_bitsum'_t = 't -> Prims.bool
let (filter_bitsum'_bitstop :
  Prims.pos ->
    unit -> (unit, Obj.t) LowParse_BitFields.uint_t -> Obj.t -> Prims.bool)
  = fun tot -> fun t -> fun cl -> fun uu___ -> true
let (filter_bitsum'_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat ->
            (unit, Obj.t, unit, unit) bitsum' ->
              (Obj.t -> Prims.bool) -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size -> fun sz -> fun rest -> fun phi -> fun x -> phi x
let (filter_bitsum'_bitsum_gen :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t -> Prims.bool) ->
                    (Obj.t -> Obj.t) ->
                      (Obj.t -> Obj.t -> Prims.bool) -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun is_valid_repr ->
                    fun key_of ->
                      fun destr_payload ->
                        fun x ->
                          let r =
                            (match cl with
                             | { LowParse_BitFields.v = v;
                                 LowParse_BitFields.uint_to_t = uint_to_t;
                                 LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                                 LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                                 LowParse_BitFields.get_bitfield_gen =
                                   get_bitfield_gen;
                                 LowParse_BitFields.set_bitfield_gen =
                                   set_bitfield_gen;
                                 LowParse_BitFields.get_bitfield =
                                   get_bitfield;
                                 LowParse_BitFields.set_bitfield =
                                   set_bitfield;
                                 LowParse_BitFields.logor = logor;
                                 LowParse_BitFields.bitfield_eq_lhs =
                                   bitfield_eq_lhs;
                                 LowParse_BitFields.bitfield_eq_rhs =
                                   bitfield_eq_rhs;_}
                                 -> get_bitfield) x (bitsum'_size - key_size)
                              bitsum'_size in
                          if Prims.op_Negation (is_valid_repr r)
                          then false
                          else destr_payload (key_of r) x
type ('tot, 't, 'cl, 'bitsumuusize, 'key, 'keyusize, 'e, 'payload, 'l1,
  'l2) filter_bitsum'_bitsum'_t = 't -> 't -> Prims.bool
let (filter_bitsum'_bitsum'_intro :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t -> Obj.t -> Prims.bool) -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun phi ->
                    fun x ->
                      let xr =
                        (match cl with
                         | { LowParse_BitFields.v = v;
                             LowParse_BitFields.uint_to_t = uint_to_t;
                             LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                             LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                             LowParse_BitFields.get_bitfield_gen =
                               get_bitfield_gen;
                             LowParse_BitFields.set_bitfield_gen =
                               set_bitfield_gen;
                             LowParse_BitFields.get_bitfield = get_bitfield;
                             LowParse_BitFields.set_bitfield = set_bitfield;
                             LowParse_BitFields.logor = logor;
                             LowParse_BitFields.bitfield_eq_lhs =
                               bitfield_eq_lhs;
                             LowParse_BitFields.bitfield_eq_rhs =
                               bitfield_eq_rhs;_}
                             -> bitfield_eq_lhs) x (bitsum'_size - key_size)
                          bitsum'_size in
                      phi x xr
let (filter_bitsum'_bitsum'_nil :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  unit -> Obj.t -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e -> fun payload -> fun h -> fun x -> fun xr -> false
let (filter_bitsum'_bitsum'_cons :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    Obj.t ->
                      Obj.t ->
                        (Obj.t * Obj.t) Prims.list ->
                          (Obj.t -> Prims.bool) ->
                            (Obj.t -> Obj.t -> Prims.bool) ->
                              Obj.t -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun k ->
                      fun r ->
                        fun l2 ->
                          fun destr_payload ->
                            fun destr_tail ->
                              fun x ->
                                fun xr ->
                                  if
                                    xr =
                                      ((match cl with
                                        | { LowParse_BitFields.v = v;
                                            LowParse_BitFields.uint_to_t =
                                              uint_to_t;
                                            LowParse_BitFields.v_uint_to_t =
                                              v_uint_to_t;
                                            LowParse_BitFields.uint_to_t_v =
                                              uint_to_t_v;
                                            LowParse_BitFields.get_bitfield_gen
                                              = get_bitfield_gen;
                                            LowParse_BitFields.set_bitfield_gen
                                              = set_bitfield_gen;
                                            LowParse_BitFields.get_bitfield =
                                              get_bitfield;
                                            LowParse_BitFields.set_bitfield =
                                              set_bitfield;
                                            LowParse_BitFields.logor = logor;
                                            LowParse_BitFields.bitfield_eq_lhs
                                              = bitfield_eq_lhs;
                                            LowParse_BitFields.bitfield_eq_rhs
                                              = bitfield_eq_rhs;_}
                                            -> bitfield_eq_rhs) x
                                         (bitsum'_size - key_size)
                                         bitsum'_size r)
                                  then destr_payload x
                                  else destr_tail x xr

let rec (mk_filter_bitsum'_t' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            match b with
            | BitStop uu___ -> (fun uu___1 -> true)
            | BitField (sz, rest) ->
                (fun x ->
                   mk_filter_bitsum'_t' tot () cl (bitsum'_size - sz) rest x)
            | BitSum' (key, key_size, e, payload) ->
                (fun x ->
                   let xr =
                     (match cl with
                      | { LowParse_BitFields.v = v;
                          LowParse_BitFields.uint_to_t = uint_to_t;
                          LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                          LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                          LowParse_BitFields.get_bitfield_gen =
                            get_bitfield_gen;
                          LowParse_BitFields.set_bitfield_gen =
                            set_bitfield_gen;
                          LowParse_BitFields.get_bitfield = get_bitfield;
                          LowParse_BitFields.set_bitfield = set_bitfield;
                          LowParse_BitFields.logor = logor;
                          LowParse_BitFields.bitfield_eq_lhs =
                            bitfield_eq_lhs;
                          LowParse_BitFields.bitfield_eq_rhs =
                            bitfield_eq_rhs;_}
                          -> bitfield_eq_lhs) x (bitsum'_size - key_size)
                       bitsum'_size in
                   mk_filter_bitsum'_bitsum'_t' tot () cl bitsum'_size ()
                     key_size e payload [] e x xr)
and (mk_filter_bitsum'_bitsum'_t' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    (Obj.t * Obj.t) Prims.list ->
                      Obj.t -> Obj.t -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun l2 ->
                      match l2 with
                      | [] -> (fun x -> fun xr -> false)
                      | (k, r)::q ->
                          (fun x ->
                             fun xr ->
                               if
                                 xr =
                                   ((match cl with
                                     | { LowParse_BitFields.v = v;
                                         LowParse_BitFields.uint_to_t =
                                           uint_to_t;
                                         LowParse_BitFields.v_uint_to_t =
                                           v_uint_to_t;
                                         LowParse_BitFields.uint_to_t_v =
                                           uint_to_t_v;
                                         LowParse_BitFields.get_bitfield_gen
                                           = get_bitfield_gen;
                                         LowParse_BitFields.set_bitfield_gen
                                           = set_bitfield_gen;
                                         LowParse_BitFields.get_bitfield =
                                           get_bitfield;
                                         LowParse_BitFields.set_bitfield =
                                           set_bitfield;
                                         LowParse_BitFields.logor = logor;
                                         LowParse_BitFields.bitfield_eq_lhs =
                                           bitfield_eq_lhs;
                                         LowParse_BitFields.bitfield_eq_rhs =
                                           bitfield_eq_rhs;_}
                                         -> bitfield_eq_rhs) x
                                      (bitsum'_size - key_size) bitsum'_size
                                      r)
                               then
                                 mk_filter_bitsum'_t' tot () cl
                                   (bitsum'_size - key_size) (payload k) x
                               else
                                 mk_filter_bitsum'_bitsum'_t' tot () cl
                                   bitsum'_size () key_size e payload
                                   (FStar_List_Tot_Base.append l1 [(k, r)]) q
                                   x xr)
type 't if_combinator_weak = Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't
type ('tot, 't, 'cl, 'from, 'b) destr_bitsum'_t =
  unit ->
    (unit -> Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t) ->
      (Obj.t -> Obj.t) ->
        ('t, unit) LowParse_Spec_Combinators.parse_filter_refine -> Obj.t
let (destr_bitsum'_bitstop :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        unit ->
          (unit -> Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
            -> (unit -> Obj.t) -> Obj.t -> Obj.t)
  = fun tot -> fun t -> fun cl -> fun u -> fun u_if -> fun f -> fun x -> f ()
let (destr_bitsum'_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat ->
            (unit, Obj.t, unit, unit) bitsum' ->
              (unit ->
                 (unit ->
                    Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                   -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
                ->
                unit ->
                  (unit ->
                     Prims.bool ->
                       (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                    -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun sz ->
            fun rest ->
              fun phi ->
                fun u ->
                  fun u_if ->
                    fun f ->
                      fun x ->
                        phi () (fun z -> u_if ())
                          (fun z ->
                             f
                               (Obj.magic
                                  (((match cl with
                                     | { LowParse_BitFields.v = v;
                                         LowParse_BitFields.uint_to_t =
                                           uint_to_t;
                                         LowParse_BitFields.v_uint_to_t =
                                           v_uint_to_t;
                                         LowParse_BitFields.uint_to_t_v =
                                           uint_to_t_v;
                                         LowParse_BitFields.get_bitfield_gen
                                           = get_bitfield_gen;
                                         LowParse_BitFields.set_bitfield_gen
                                           = set_bitfield_gen;
                                         LowParse_BitFields.get_bitfield =
                                           get_bitfield;
                                         LowParse_BitFields.set_bitfield =
                                           set_bitfield;
                                         LowParse_BitFields.logor = logor;
                                         LowParse_BitFields.bitfield_eq_lhs =
                                           bitfield_eq_lhs;
                                         LowParse_BitFields.bitfield_eq_rhs =
                                           bitfield_eq_rhs;_}
                                         -> get_bitfield) x
                                      (bitsum'_size - sz) bitsum'_size), z)))
                          x
let (destr_bitsum'_bitsum_gen :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> Obj.t) ->
                  (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                    (Obj.t ->
                       unit ->
                         (unit ->
                            Prims.bool ->
                              (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                           -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
                      ->
                      unit ->
                        (unit ->
                           Prims.bool ->
                             (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                          -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun key_of ->
                  fun payload ->
                    fun destr_payload ->
                      fun u ->
                        fun u_if ->
                          fun f ->
                            fun x ->
                              destr_payload
                                (key_of
                                   ((match cl with
                                     | { LowParse_BitFields.v = v;
                                         LowParse_BitFields.uint_to_t =
                                           uint_to_t;
                                         LowParse_BitFields.v_uint_to_t =
                                           v_uint_to_t;
                                         LowParse_BitFields.uint_to_t_v =
                                           uint_to_t_v;
                                         LowParse_BitFields.get_bitfield_gen
                                           = get_bitfield_gen;
                                         LowParse_BitFields.set_bitfield_gen
                                           = set_bitfield_gen;
                                         LowParse_BitFields.get_bitfield =
                                           get_bitfield;
                                         LowParse_BitFields.set_bitfield =
                                           set_bitfield;
                                         LowParse_BitFields.logor = logor;
                                         LowParse_BitFields.bitfield_eq_lhs =
                                           bitfield_eq_lhs;
                                         LowParse_BitFields.bitfield_eq_rhs =
                                           bitfield_eq_rhs;_}
                                         -> get_bitfield) x
                                      (bitsum'_size - key_size) bitsum'_size))
                                () (fun z -> u_if ())
                                (fun z ->
                                   f
                                     (Obj.magic
                                        (Prims.Mkdtuple2
                                           ((key_of
                                               ((match cl with
                                                 | {
                                                     LowParse_BitFields.v = v;
                                                     LowParse_BitFields.uint_to_t
                                                       = uint_to_t;
                                                     LowParse_BitFields.v_uint_to_t
                                                       = v_uint_to_t;
                                                     LowParse_BitFields.uint_to_t_v
                                                       = uint_to_t_v;
                                                     LowParse_BitFields.get_bitfield_gen
                                                       = get_bitfield_gen;
                                                     LowParse_BitFields.set_bitfield_gen
                                                       = set_bitfield_gen;
                                                     LowParse_BitFields.get_bitfield
                                                       = get_bitfield;
                                                     LowParse_BitFields.set_bitfield
                                                       = set_bitfield;
                                                     LowParse_BitFields.logor
                                                       = logor;
                                                     LowParse_BitFields.bitfield_eq_lhs
                                                       = bitfield_eq_lhs;
                                                     LowParse_BitFields.bitfield_eq_rhs
                                                       = bitfield_eq_rhs;_}
                                                     -> get_bitfield) x
                                                  (bitsum'_size - key_size)
                                                  bitsum'_size)), z)))) x
type ('tot, 't, 'cl, 'bitsumuusize, 'key, 'keyusize, 'e, 'payload, 'l1,
  'l2) destr_bitsum'_bitsum_t =
  unit ->
    (unit -> Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t) ->
      (Obj.t -> Obj.t) ->
        ('t, unit) LowParse_Spec_Combinators.parse_filter_refine -> Obj.t
let (destr_bitsum'_bitsum_intro :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (unit ->
                     (unit ->
                        Prims.bool ->
                          (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                       -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
                    ->
                    unit ->
                      (unit ->
                         Prims.bool ->
                           (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                        -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun phi ->
                    fun u -> fun u_if -> fun f -> fun x -> phi () u_if f x
let (destr_bitsum'_bitsum_nil :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  unit ->
                    unit ->
                      (unit ->
                         Prims.bool ->
                           (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                        -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun h ->
                    fun u ->
                      fun u_if ->
                        fun f -> fun x -> FStar_Pervasives.false_elim ()
let (destr_bitsum'_bitsum_cons :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    Obj.t ->
                      Obj.t ->
                        (Obj.t * Obj.t) Prims.list ->
                          (unit ->
                             (unit ->
                                Prims.bool ->
                                  (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                               -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
                            ->
                            (unit ->
                               (unit ->
                                  Prims.bool ->
                                    (unit -> Obj.t) ->
                                      (unit -> Obj.t) -> Obj.t)
                                 -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
                              ->
                              unit ->
                                (unit ->
                                   Prims.bool ->
                                     (unit -> Obj.t) ->
                                       (unit -> Obj.t) -> Obj.t)
                                  -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun k ->
                      fun r ->
                        fun l2 ->
                          fun destr_payload ->
                            fun destr_tail ->
                              fun u ->
                                fun u_if ->
                                  fun f ->
                                    fun x ->
                                      u_if ()
                                        (((match cl with
                                           | { LowParse_BitFields.v = v;
                                               LowParse_BitFields.uint_to_t =
                                                 uint_to_t;
                                               LowParse_BitFields.v_uint_to_t
                                                 = v_uint_to_t;
                                               LowParse_BitFields.uint_to_t_v
                                                 = uint_to_t_v;
                                               LowParse_BitFields.get_bitfield_gen
                                                 = get_bitfield_gen;
                                               LowParse_BitFields.set_bitfield_gen
                                                 = set_bitfield_gen;
                                               LowParse_BitFields.get_bitfield
                                                 = get_bitfield;
                                               LowParse_BitFields.set_bitfield
                                                 = set_bitfield;
                                               LowParse_BitFields.logor =
                                                 logor;
                                               LowParse_BitFields.bitfield_eq_lhs
                                                 = bitfield_eq_lhs;
                                               LowParse_BitFields.bitfield_eq_rhs
                                                 = bitfield_eq_rhs;_}
                                               -> get_bitfield) x
                                            (bitsum'_size - key_size)
                                            bitsum'_size)
                                           = r)
                                        (fun cond_true ->
                                           destr_payload ()
                                             (fun x1 -> u_if ())
                                             (fun x1 ->
                                                f
                                                  (Obj.magic
                                                     (Prims.Mkdtuple2 (k, x1))))
                                             x)
                                        (fun cond_false ->
                                           destr_tail () u_if f x)
let (destr_bitsum'_bitsum_cons_nil :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    Obj.t ->
                      Obj.t ->
                        (unit ->
                           (unit ->
                              Prims.bool ->
                                (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                             -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
                          ->
                          unit ->
                            (unit ->
                               Prims.bool ->
                                 (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                              -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun k ->
                      fun r ->
                        fun destr_payload ->
                          fun u ->
                            fun u_if ->
                              fun f ->
                                fun x ->
                                  destr_payload () (fun x1 -> u_if ())
                                    (fun x1 ->
                                       f
                                         (Obj.magic (Prims.Mkdtuple2 (k, x1))))
                                    x
let rec (mk_destr_bitsum'_t :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            unit ->
              (unit ->
                 Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
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
                    (fun tot ->
                       fun t ->
                         fun cl ->
                           fun bitsum'_size ->
                             fun b ->
                               match b with
                               | BitStop uu___ ->
                                   Obj.magic
                                     (Obj.repr
                                        (fun u ->
                                           fun u_if -> fun f -> fun x -> f ()))
                               | BitField (sz, rest) ->
                                   Obj.magic
                                     (Obj.repr
                                        (fun u ->
                                           fun u_if ->
                                             fun f ->
                                               fun x ->
                                                 mk_destr_bitsum'_t tot () cl
                                                   (bitsum'_size - sz) rest
                                                   () (fun z -> u_if ())
                                                   (fun z ->
                                                      f
                                                        (Obj.magic
                                                           (((match cl with
                                                              | {
                                                                  LowParse_BitFields.v
                                                                    = v;
                                                                  LowParse_BitFields.uint_to_t
                                                                    =
                                                                    uint_to_t;
                                                                  LowParse_BitFields.v_uint_to_t
                                                                    =
                                                                    v_uint_to_t;
                                                                  LowParse_BitFields.uint_to_t_v
                                                                    =
                                                                    uint_to_t_v;
                                                                  LowParse_BitFields.get_bitfield_gen
                                                                    =
                                                                    get_bitfield_gen;
                                                                  LowParse_BitFields.set_bitfield_gen
                                                                    =
                                                                    set_bitfield_gen;
                                                                  LowParse_BitFields.get_bitfield
                                                                    =
                                                                    get_bitfield;
                                                                  LowParse_BitFields.set_bitfield
                                                                    =
                                                                    set_bitfield;
                                                                  LowParse_BitFields.logor
                                                                    = logor;
                                                                  LowParse_BitFields.bitfield_eq_lhs
                                                                    =
                                                                    bitfield_eq_lhs;
                                                                  LowParse_BitFields.bitfield_eq_rhs
                                                                    =
                                                                    bitfield_eq_rhs;_}
                                                                  ->
                                                                  get_bitfield)
                                                               x
                                                               (bitsum'_size
                                                                  - sz)
                                                               bitsum'_size),
                                                             z))) x))
                               | BitSum' (key, key_size, e, payload) ->
                                   Obj.magic
                                     (Obj.repr
                                        (fun u ->
                                           fun u_if ->
                                             fun f ->
                                               fun x ->
                                                 mk_destr_bitsum'_bitsum_t
                                                   tot () cl bitsum'_size ()
                                                   key_size e payload [] e ()
                                                   u_if f x))) uu___8 uu___7
                      uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
and (mk_destr_bitsum'_bitsum_t :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    (Obj.t * Obj.t) Prims.list ->
                      unit ->
                        (unit ->
                           Prims.bool ->
                             (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                          -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun l2 ->
                      match l2 with
                      | [] ->
                          (fun u ->
                             fun u_if ->
                               fun f ->
                                 fun x -> FStar_Pervasives.false_elim ())
                      | (k, r)::[] ->
                          (fun u ->
                             fun u_if ->
                               fun f ->
                                 fun x ->
                                   mk_destr_bitsum'_t tot () cl
                                     (bitsum'_size - key_size) (payload k) ()
                                     (fun x1 -> u_if ())
                                     (fun x1 ->
                                        f
                                          (Obj.magic
                                             (Prims.Mkdtuple2 (k, x1)))) x)
                      | (k, r)::q ->
                          (fun u ->
                             fun u_if ->
                               fun f ->
                                 fun x ->
                                   u_if ()
                                     (((match cl with
                                        | { LowParse_BitFields.v = v;
                                            LowParse_BitFields.uint_to_t =
                                              uint_to_t;
                                            LowParse_BitFields.v_uint_to_t =
                                              v_uint_to_t;
                                            LowParse_BitFields.uint_to_t_v =
                                              uint_to_t_v;
                                            LowParse_BitFields.get_bitfield_gen
                                              = get_bitfield_gen;
                                            LowParse_BitFields.set_bitfield_gen
                                              = set_bitfield_gen;
                                            LowParse_BitFields.get_bitfield =
                                              get_bitfield;
                                            LowParse_BitFields.set_bitfield =
                                              set_bitfield;
                                            LowParse_BitFields.logor = logor;
                                            LowParse_BitFields.bitfield_eq_lhs
                                              = bitfield_eq_lhs;
                                            LowParse_BitFields.bitfield_eq_rhs
                                              = bitfield_eq_rhs;_}
                                            -> get_bitfield) x
                                         (bitsum'_size - key_size)
                                         bitsum'_size)
                                        = r)
                                     (fun cond_true ->
                                        mk_destr_bitsum'_t tot () cl
                                          (bitsum'_size - key_size)
                                          (payload k) () (fun x1 -> u_if ())
                                          (fun x1 ->
                                             f
                                               (Obj.magic
                                                  (Prims.Mkdtuple2 (k, x1))))
                                          x)
                                     (fun cond_false ->
                                        mk_destr_bitsum'_bitsum_t tot () cl
                                          bitsum'_size () key_size e payload
                                          (FStar_List_Tot_Base.append l1
                                             [(k, r)]) q () u_if f x))
type ('tot, 't, 'cl, 'bitsumuusize, 'b) synth_bitsum'_recip_t = Obj.t -> 't
let (synth_bitsum'_recip_BitStop :
  Prims.pos ->
    unit -> (unit, Obj.t) LowParse_BitFields.uint_t -> unit -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun uu___ ->
          match cl with
          | { LowParse_BitFields.v = v;
              LowParse_BitFields.uint_to_t = uint_to_t;
              LowParse_BitFields.v_uint_to_t = v_uint_to_t;
              LowParse_BitFields.uint_to_t_v = uint_to_t_v;
              LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
              LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
              LowParse_BitFields.get_bitfield = get_bitfield;
              LowParse_BitFields.set_bitfield = set_bitfield;
              LowParse_BitFields.logor = logor;
              LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
              LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
              uint_to_t Prims.int_zero
let (synth_bitsum'_recip_BitField :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat ->
            (unit, Obj.t, unit, unit) bitsum' ->
              (Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun sz ->
            fun rest ->
              fun ih ->
                fun x ->
                  match Obj.magic x with
                  | (hd, tl) ->
                      ((match cl with
                        | { LowParse_BitFields.v = v;
                            LowParse_BitFields.uint_to_t = uint_to_t;
                            LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                            LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                            LowParse_BitFields.get_bitfield_gen =
                              get_bitfield_gen;
                            LowParse_BitFields.set_bitfield_gen =
                              set_bitfield_gen;
                            LowParse_BitFields.get_bitfield = get_bitfield;
                            LowParse_BitFields.set_bitfield = set_bitfield;
                            LowParse_BitFields.logor = logor;
                            LowParse_BitFields.bitfield_eq_lhs =
                              bitfield_eq_lhs;
                            LowParse_BitFields.bitfield_eq_rhs =
                              bitfield_eq_rhs;_}
                            -> set_bitfield)) (ih tl) (bitsum'_size - sz)
                        bitsum'_size hd
let (synth_bitsum'_recip_BitSum_gen :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> Obj.t) ->
                  (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                    (Obj.t -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun repr_of ->
                  fun payload ->
                    fun synth_payload ->
                      fun x ->
                        match Obj.magic x with
                        | Prims.Mkdtuple2 (k, pl) ->
                            ((match cl with
                              | { LowParse_BitFields.v = v;
                                  LowParse_BitFields.uint_to_t = uint_to_t;
                                  LowParse_BitFields.v_uint_to_t =
                                    v_uint_to_t;
                                  LowParse_BitFields.uint_to_t_v =
                                    uint_to_t_v;
                                  LowParse_BitFields.get_bitfield_gen =
                                    get_bitfield_gen;
                                  LowParse_BitFields.set_bitfield_gen =
                                    set_bitfield_gen;
                                  LowParse_BitFields.get_bitfield =
                                    get_bitfield;
                                  LowParse_BitFields.set_bitfield =
                                    set_bitfield;
                                  LowParse_BitFields.logor = logor;
                                  LowParse_BitFields.bitfield_eq_lhs =
                                    bitfield_eq_lhs;
                                  LowParse_BitFields.bitfield_eq_rhs =
                                    bitfield_eq_rhs;_}
                                  -> set_bitfield)) (synth_payload k pl)
                              (bitsum'_size - key_size) bitsum'_size
                              (repr_of k)
type ('tot, 't, 'cl, 'bitsumuusize, 'key, 'keyusize, 'e, 'payload, 'l1,
  'l2) synth_bitsum'_recip_BitSum_t = 'key -> Obj.t -> 't
let (synth_bitsum'_recip_BitSum_intro :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t -> Obj.t -> Obj.t) -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun phi ->
                    fun x ->
                      match Obj.magic x with
                      | Prims.Mkdtuple2 (k, pl) -> phi k pl
let (synth_bitsum'_recip_BitSum_nil :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list -> Obj.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun k -> fun uu___ -> FStar_Pervasives.false_elim ()
let (synth_bitsum'_recip_BitSum_cons :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    Obj.t ->
                      Obj.t ->
                        (Obj.t * Obj.t) Prims.list ->
                          (Obj.t -> Obj.t) ->
                            (Obj.t -> Obj.t -> Obj.t) ->
                              Obj.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun k ->
                      fun r ->
                        fun l2 ->
                          fun destr_payload ->
                            fun destr_tail ->
                              fun k' ->
                                fun rest ->
                                  if k' = k
                                  then
                                    (match cl with
                                     | { LowParse_BitFields.v = v;
                                         LowParse_BitFields.uint_to_t =
                                           uint_to_t;
                                         LowParse_BitFields.v_uint_to_t =
                                           v_uint_to_t;
                                         LowParse_BitFields.uint_to_t_v =
                                           uint_to_t_v;
                                         LowParse_BitFields.get_bitfield_gen
                                           = get_bitfield_gen;
                                         LowParse_BitFields.set_bitfield_gen
                                           = set_bitfield_gen;
                                         LowParse_BitFields.get_bitfield =
                                           get_bitfield;
                                         LowParse_BitFields.set_bitfield =
                                           set_bitfield;
                                         LowParse_BitFields.logor = logor;
                                         LowParse_BitFields.bitfield_eq_lhs =
                                           bitfield_eq_lhs;
                                         LowParse_BitFields.bitfield_eq_rhs =
                                           bitfield_eq_rhs;_}
                                         -> set_bitfield)
                                      (destr_payload rest)
                                      (bitsum'_size - key_size) bitsum'_size
                                      r
                                  else destr_tail k' rest
let (synth_bitsum'_recip_BitSum_cons_nil :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    Obj.t ->
                      Obj.t -> (Obj.t -> Obj.t) -> Obj.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun k ->
                      fun r ->
                        fun destr_payload ->
                          fun k' ->
                            fun rest ->
                              (match cl with
                               | { LowParse_BitFields.v = v;
                                   LowParse_BitFields.uint_to_t = uint_to_t;
                                   LowParse_BitFields.v_uint_to_t =
                                     v_uint_to_t;
                                   LowParse_BitFields.uint_to_t_v =
                                     uint_to_t_v;
                                   LowParse_BitFields.get_bitfield_gen =
                                     get_bitfield_gen;
                                   LowParse_BitFields.set_bitfield_gen =
                                     set_bitfield_gen;
                                   LowParse_BitFields.get_bitfield =
                                     get_bitfield;
                                   LowParse_BitFields.set_bitfield =
                                     set_bitfield;
                                   LowParse_BitFields.logor = logor;
                                   LowParse_BitFields.bitfield_eq_lhs =
                                     bitfield_eq_lhs;
                                   LowParse_BitFields.bitfield_eq_rhs =
                                     bitfield_eq_rhs;_}
                                   -> set_bitfield) (destr_payload rest)
                                (bitsum'_size - key_size) bitsum'_size r
let rec (mk_synth_bitsum'_recip :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> (unit, Obj.t, unit, unit) bitsum' -> Obj.t -> Obj.t)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun tot ->
                 fun t ->
                   fun cl ->
                     fun bitsum'_size ->
                       fun b ->
                         match b with
                         | BitStop uu___ ->
                             Obj.magic
                               (Obj.repr
                                  (fun uu___1 ->
                                     match cl with
                                     | { LowParse_BitFields.v = v;
                                         LowParse_BitFields.uint_to_t =
                                           uint_to_t;
                                         LowParse_BitFields.v_uint_to_t =
                                           v_uint_to_t;
                                         LowParse_BitFields.uint_to_t_v =
                                           uint_to_t_v;
                                         LowParse_BitFields.get_bitfield_gen
                                           = get_bitfield_gen;
                                         LowParse_BitFields.set_bitfield_gen
                                           = set_bitfield_gen;
                                         LowParse_BitFields.get_bitfield =
                                           get_bitfield;
                                         LowParse_BitFields.set_bitfield =
                                           set_bitfield;
                                         LowParse_BitFields.logor = logor;
                                         LowParse_BitFields.bitfield_eq_lhs =
                                           bitfield_eq_lhs;
                                         LowParse_BitFields.bitfield_eq_rhs =
                                           bitfield_eq_rhs;_}
                                         -> uint_to_t Prims.int_zero))
                         | BitField (sz, rest) ->
                             Obj.magic
                               (Obj.repr
                                  (fun x ->
                                     match Obj.magic x with
                                     | (hd, tl) ->
                                         ((match cl with
                                           | { LowParse_BitFields.v = v;
                                               LowParse_BitFields.uint_to_t =
                                                 uint_to_t;
                                               LowParse_BitFields.v_uint_to_t
                                                 = v_uint_to_t;
                                               LowParse_BitFields.uint_to_t_v
                                                 = uint_to_t_v;
                                               LowParse_BitFields.get_bitfield_gen
                                                 = get_bitfield_gen;
                                               LowParse_BitFields.set_bitfield_gen
                                                 = set_bitfield_gen;
                                               LowParse_BitFields.get_bitfield
                                                 = get_bitfield;
                                               LowParse_BitFields.set_bitfield
                                                 = set_bitfield;
                                               LowParse_BitFields.logor =
                                                 logor;
                                               LowParse_BitFields.bitfield_eq_lhs
                                                 = bitfield_eq_lhs;
                                               LowParse_BitFields.bitfield_eq_rhs
                                                 = bitfield_eq_rhs;_}
                                               -> set_bitfield))
                                           (mk_synth_bitsum'_recip tot () cl
                                              (bitsum'_size - sz) rest tl)
                                           (bitsum'_size - sz) bitsum'_size
                                           hd))
                         | BitSum' (key, key_size, e, payload) ->
                             Obj.magic
                               (Obj.repr
                                  (fun x ->
                                     match Obj.magic x with
                                     | Prims.Mkdtuple2 (k, pl) ->
                                         mk_synth_bitsum'_recip_BitSum tot ()
                                           cl bitsum'_size () key_size e
                                           payload [] e k pl))) uu___5 uu___4
                uu___3 uu___2 uu___1 uu___
and (mk_synth_bitsum'_recip_BitSum :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> (unit, Obj.t, unit, unit) bitsum') ->
                  (Obj.t * Obj.t) Prims.list ->
                    (Obj.t * Obj.t) Prims.list -> Obj.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun l1 ->
                    fun l2 ->
                      match l2 with
                      | [] ->
                          (fun k ->
                             fun uu___ -> FStar_Pervasives.false_elim ())
                      | (k, r)::[] ->
                          (fun k' ->
                             fun rest ->
                               (match cl with
                                | { LowParse_BitFields.v = v;
                                    LowParse_BitFields.uint_to_t = uint_to_t;
                                    LowParse_BitFields.v_uint_to_t =
                                      v_uint_to_t;
                                    LowParse_BitFields.uint_to_t_v =
                                      uint_to_t_v;
                                    LowParse_BitFields.get_bitfield_gen =
                                      get_bitfield_gen;
                                    LowParse_BitFields.set_bitfield_gen =
                                      set_bitfield_gen;
                                    LowParse_BitFields.get_bitfield =
                                      get_bitfield;
                                    LowParse_BitFields.set_bitfield =
                                      set_bitfield;
                                    LowParse_BitFields.logor = logor;
                                    LowParse_BitFields.bitfield_eq_lhs =
                                      bitfield_eq_lhs;
                                    LowParse_BitFields.bitfield_eq_rhs =
                                      bitfield_eq_rhs;_}
                                    -> set_bitfield)
                                 (mk_synth_bitsum'_recip tot () cl
                                    (bitsum'_size - key_size) (payload k)
                                    rest) (bitsum'_size - key_size)
                                 bitsum'_size r)
                      | (k, r)::q ->
                          (fun k' ->
                             fun rest ->
                               if k' = k
                               then
                                 (match cl with
                                  | { LowParse_BitFields.v = v;
                                      LowParse_BitFields.uint_to_t =
                                        uint_to_t;
                                      LowParse_BitFields.v_uint_to_t =
                                        v_uint_to_t;
                                      LowParse_BitFields.uint_to_t_v =
                                        uint_to_t_v;
                                      LowParse_BitFields.get_bitfield_gen =
                                        get_bitfield_gen;
                                      LowParse_BitFields.set_bitfield_gen =
                                        set_bitfield_gen;
                                      LowParse_BitFields.get_bitfield =
                                        get_bitfield;
                                      LowParse_BitFields.set_bitfield =
                                        set_bitfield;
                                      LowParse_BitFields.logor = logor;
                                      LowParse_BitFields.bitfield_eq_lhs =
                                        bitfield_eq_lhs;
                                      LowParse_BitFields.bitfield_eq_rhs =
                                        bitfield_eq_rhs;_}
                                      -> set_bitfield)
                                   (mk_synth_bitsum'_recip tot () cl
                                      (bitsum'_size - key_size) (payload k)
                                      rest) (bitsum'_size - key_size)
                                   bitsum'_size r
                               else
                                 mk_synth_bitsum'_recip_BitSum tot () cl
                                   bitsum'_size () key_size e payload
                                   (FStar_List_Tot_Base.append l1 [(k, r)]) q
                                   k' rest)


let rec (get_valid_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            Obj.t -> Prims.nat -> Prims.nat -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun k ->
              fun low ->
                fun high ->
                  match b with
                  | BitField (sz, rest) ->
                      let uu___ = Obj.magic k in
                      (match uu___ with
                       | (hd, tl) ->
                           if ((low + sz) = high) && (high = bitsum'_size)
                           then hd
                           else
                             get_valid_bitfield tot () cl (bitsum'_size - sz)
                               rest tl low high)
                  | BitSum' (key, key_size, e, payload) ->
                      let uu___ = Obj.magic k in
                      (match uu___ with
                       | Prims.Mkdtuple2 (k', r') ->
                           get_valid_bitfield tot () cl
                             (bitsum'_size - key_size) (payload k') r' low
                             high)

let rec (set_valid_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          (unit, Obj.t, unit, unit) bitsum' ->
            Obj.t -> Prims.nat -> Prims.nat -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun b ->
            fun k ->
              fun low ->
                fun high ->
                  fun v ->
                    match b with
                    | BitField (sz, rest) ->
                        Obj.repr
                          (let uu___ = Obj.magic k in
                           match uu___ with
                           | (hd, tl) ->
                               if
                                 ((low + sz) = high) && (high = bitsum'_size)
                               then (v, tl)
                               else
                                 (hd,
                                   (set_valid_bitfield tot () cl
                                      (bitsum'_size - sz) rest tl low high v)))
                    | BitSum' (key, key_size, e, payload) ->
                        Obj.repr
                          (let uu___ = Obj.magic k in
                           match uu___ with
                           | Prims.Mkdtuple2 (k', r') ->
                               Prims.Mkdtuple2
                                 (k',
                                   (set_valid_bitfield tot () cl
                                      (bitsum'_size - key_size) (payload k')
                                      r' low high v)))



