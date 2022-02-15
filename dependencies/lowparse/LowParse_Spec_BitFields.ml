open Prims
let rec (valid_bitfield_bounds :
  Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Prims.bool) =
  fun lo ->
    fun hi ->
      fun l ->
        match l with
        | [] -> true
        | mi::q ->
            ((lo <= mi) && (mi <= hi)) && (valid_bitfield_bounds mi hi q)
let rec (valid_bitfield_widths :
  Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Prims.bool) =
  fun lo ->
    fun hi ->
      fun l ->
        match l with
        | [] -> lo = hi
        | sz::q ->
            ((lo + sz) <= hi) && (valid_bitfield_widths (lo + sz) hi q)
let rec (bounds_of_widths :
  Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Prims.nat Prims.list) =
  fun lo ->
    fun hi ->
      fun l ->
        match l with
        | [] -> []
        | uu___::[] -> []
        | sz::q -> (lo + sz) :: (bounds_of_widths (lo + sz) hi q)
let rec (synth_bitfield' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun lo ->
          fun hi ->
            fun l ->
              fun x ->
                match l with
                | [] -> Obj.repr ()
                | uu___::[] ->
                    Obj.repr
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
                           -> get_bitfield x lo hi)
                | sz::q ->
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
                             -> get_bitfield) x lo (lo + sz)),
                        (synth_bitfield' tot () cl (lo + sz) hi q x))
let (synth_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun lo ->
          fun hi -> fun l -> fun x -> synth_bitfield' tot () cl lo hi l x




let rec (synth_bitfield_recip' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun lo ->
          fun hi ->
            fun l ->
              fun x ->
                match l with
                | [] ->
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
                         -> uint_to_t Prims.int_zero)
                | uu___::[] ->
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
                           -> uint_to_t Prims.int_zero) lo hi x
                | sz::q ->
                    let uu___ = Obj.magic x in
                    (match Obj.magic uu___ with
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
                           (synth_bitfield_recip' tot () cl (lo + sz) hi q tl)
                           lo (lo + sz) hd)
let (synth_bitfield_recip :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun lo ->
          fun hi ->
            fun l -> fun x -> synth_bitfield_recip' tot () cl lo hi l x












let rec (valid_bitfield_widths_prefix :
  Prims.nat ->
    Prims.nat -> Prims.nat Prims.list -> Prims.nat Prims.list -> Prims.nat)
  =
  fun lo ->
    fun hi ->
      fun prefix ->
        fun suffix ->
          match prefix with
          | [] -> lo
          | sz::q -> valid_bitfield_widths_prefix (lo + sz) hi q suffix
