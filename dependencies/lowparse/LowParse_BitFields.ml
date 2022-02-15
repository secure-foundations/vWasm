open Prims
type ('tot, 'sz) ubitfield = unit FStar_UInt.uint_t
let (bitfield_mask :
  Prims.pos -> Prims.nat -> Prims.nat -> unit FStar_UInt.uint_t) =
  fun tot ->
    fun lo ->
      fun hi ->
        ((match hi - lo with
          | uu___ when uu___ = Prims.int_zero -> Prims.int_one
          | uu___ ->
              (Prims.of_int (2)) * (Prims.pow2 ((hi - lo) - Prims.int_one)))
           - Prims.int_one)
          *
          (match lo with
           | uu___ when uu___ = Prims.int_zero -> Prims.int_one
           | uu___ -> (Prims.of_int (2)) * (Prims.pow2 (lo - Prims.int_one)))


let (nth : Prims.pos -> unit FStar_UInt.uint_t -> Prims.nat -> Prims.bool) =
  fun n -> fun a -> fun i -> FStar_UInt.nth n a ((n - Prims.int_one) - i)





let (get_bitfield_raw :
  Prims.pos ->
    unit FStar_UInt.uint_t ->
      Prims.nat -> Prims.nat -> unit FStar_UInt.uint_t)
  =
  fun tot ->
    fun x ->
      fun lo ->
        fun hi ->
          FStar_UInt.shift_right tot
            (FStar_UInt.logand tot x
               (((match hi - lo with
                  | uu___ when uu___ = Prims.int_zero -> Prims.int_one
                  | uu___ ->
                      (Prims.of_int (2)) *
                        (Prims.pow2 ((hi - lo) - Prims.int_one)))
                   - Prims.int_one)
                  *
                  (match lo with
                   | uu___ when uu___ = Prims.int_zero -> Prims.int_one
                   | uu___ ->
                       (Prims.of_int (2)) * (Prims.pow2 (lo - Prims.int_one)))))
            lo








let (get_bitfield :
  Prims.pos ->
    unit FStar_UInt.uint_t ->
      Prims.nat -> Prims.nat -> (unit, unit) ubitfield)
  = fun tot -> fun x -> fun lo -> fun hi -> get_bitfield_raw tot x lo hi






let (not_bitfield_mask :
  Prims.pos -> Prims.nat -> Prims.nat -> unit FStar_UInt.uint_t) =
  fun tot ->
    fun lo ->
      fun hi ->
        (((match tot - hi with
           | uu___ when uu___ = Prims.int_zero -> Prims.int_one
           | uu___ ->
               (Prims.of_int (2)) * (Prims.pow2 ((tot - hi) - Prims.int_one)))
            - Prims.int_one)
           *
           (match hi with
            | uu___ when uu___ = Prims.int_zero -> Prims.int_one
            | uu___ -> (Prims.of_int (2)) * (Prims.pow2 (hi - Prims.int_one))))
          +
          (((match lo - Prims.int_zero with
             | uu___ when uu___ = Prims.int_zero -> Prims.int_one
             | uu___ ->
                 (Prims.of_int (2)) *
                   (Prims.pow2 ((lo - Prims.int_zero) - Prims.int_one)))
              - Prims.int_one)
             * Prims.int_one)

let (set_bitfield :
  Prims.pos ->
    unit FStar_UInt.uint_t ->
      Prims.nat ->
        Prims.nat -> (unit, unit) ubitfield -> unit FStar_UInt.uint_t)
  =
  fun tot ->
    fun x ->
      fun lo ->
        fun hi ->
          fun v ->
            FStar_UInt.logor tot
              (FStar_UInt.logand tot x
                 ((((match tot - hi with
                     | uu___ when uu___ = Prims.int_zero -> Prims.int_one
                     | uu___ ->
                         (Prims.of_int (2)) *
                           (Prims.pow2 ((tot - hi) - Prims.int_one)))
                      - Prims.int_one)
                     *
                     (match hi with
                      | uu___ when uu___ = Prims.int_zero -> Prims.int_one
                      | uu___ ->
                          (Prims.of_int (2)) *
                            (Prims.pow2 (hi - Prims.int_one))))
                    +
                    (((match lo - Prims.int_zero with
                       | uu___ when uu___ = Prims.int_zero -> Prims.int_one
                       | uu___ ->
                           (Prims.of_int (2)) *
                             (Prims.pow2
                                ((lo - Prims.int_zero) - Prims.int_one)))
                        - Prims.int_one)
                       * Prims.int_one))) (FStar_UInt.shift_left tot v lo)





















let rec (get_bitfield_partition_prop :
  Prims.pos ->
    unit FStar_UInt.uint_t ->
      unit FStar_UInt.uint_t ->
        Prims.nat -> Prims.nat -> Prims.nat Prims.list -> Prims.bool)
  =
  fun tot ->
    fun x ->
      fun y ->
        fun lo ->
          fun hi ->
            fun l ->
              match l with
              | [] -> (get_bitfield tot x lo hi) = (get_bitfield tot y lo hi)
              | mi::q ->
                  (((lo <= mi) && (mi <= hi)) &&
                     (get_bitfield_partition_prop tot x y mi hi q))
                    &&
                    ((get_bitfield tot x lo mi) = (get_bitfield tot y lo mi))















type ('tot, 't) uint_t =
  {
  v: 't -> unit FStar_UInt.uint_t ;
  uint_to_t: unit FStar_UInt.uint_t -> 't ;
  v_uint_to_t: unit ;
  uint_to_t_v: unit ;
  get_bitfield_gen: 't -> FStar_UInt32.t -> FStar_UInt32.t -> 't ;
  set_bitfield_gen: 't -> FStar_UInt32.t -> FStar_UInt32.t -> 't -> 't ;
  get_bitfield: 't -> Prims.nat -> Prims.nat -> 't ;
  set_bitfield: 't -> Prims.nat -> Prims.nat -> 't -> 't ;
  logor: 't -> 't -> 't ;
  bitfield_eq_lhs: 't -> Prims.nat -> Prims.nat -> 't ;
  bitfield_eq_rhs: 't -> Prims.nat -> Prims.nat -> 't -> 't }
let (__proj__Mkuint_t__item__v :
  Prims.pos ->
    unit -> (unit, Obj.t) uint_t -> Obj.t -> unit FStar_UInt.uint_t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> v
let (__proj__Mkuint_t__item__uint_to_t :
  Prims.pos ->
    unit -> (unit, Obj.t) uint_t -> unit FStar_UInt.uint_t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> uint_to_t


let (__proj__Mkuint_t__item__get_bitfield_gen :
  Prims.pos ->
    unit ->
      (unit, Obj.t) uint_t ->
        Obj.t -> FStar_UInt32.t -> FStar_UInt32.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> get_bitfield_gen
let (__proj__Mkuint_t__item__set_bitfield_gen :
  Prims.pos ->
    unit ->
      (unit, Obj.t) uint_t ->
        Obj.t -> FStar_UInt32.t -> FStar_UInt32.t -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> set_bitfield_gen
let (__proj__Mkuint_t__item__get_bitfield :
  Prims.pos ->
    unit -> (unit, Obj.t) uint_t -> Obj.t -> Prims.nat -> Prims.nat -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> get_bitfield1
let (__proj__Mkuint_t__item__set_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) uint_t ->
        Obj.t -> Prims.nat -> Prims.nat -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> set_bitfield1
let (__proj__Mkuint_t__item__logor :
  Prims.pos -> unit -> (unit, Obj.t) uint_t -> Obj.t -> Obj.t -> Obj.t) =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> logor
let (__proj__Mkuint_t__item__bitfield_eq_lhs :
  Prims.pos ->
    unit -> (unit, Obj.t) uint_t -> Obj.t -> Prims.nat -> Prims.nat -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> bitfield_eq_lhs
let (__proj__Mkuint_t__item__bitfield_eq_rhs :
  Prims.pos ->
    unit ->
      (unit, Obj.t) uint_t ->
        Obj.t -> Prims.nat -> Prims.nat -> Obj.t -> Obj.t)
  =
  fun tot ->
    fun t ->
      fun projectee ->
        match projectee with
        | { v; uint_to_t; v_uint_to_t; uint_to_t_v; get_bitfield_gen;
            set_bitfield_gen; get_bitfield = get_bitfield1;
            set_bitfield = set_bitfield1; logor; bitfield_eq_lhs;
            bitfield_eq_rhs;_} -> bitfield_eq_rhs
type ('tot, 't, 'cl, 'sz) bitfield = 't







let (bitfield_mask64 : Prims.nat -> Prims.nat -> FStar_UInt64.t) =
  fun lo ->
    fun hi ->
      if lo = hi
      then FStar_UInt64.uint_to_t Prims.int_zero
      else
        FStar_UInt64.shift_left
          (FStar_UInt64.shift_right
             (FStar_UInt64.uint_to_t (Prims.parse_int "18446744073709551615"))
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                (FStar_UInt32.uint_to_t (hi - lo))))
          (FStar_UInt32.uint_to_t lo)
let (u64_shift_right : FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun x ->
    fun amount ->
      if amount = (FStar_UInt32.uint_to_t (Prims.of_int (64)))
      then FStar_UInt64.uint_to_t Prims.int_zero
      else FStar_UInt64.shift_right x amount
let (get_bitfield64 :
  FStar_UInt64.t -> Prims.nat -> Prims.nat -> FStar_UInt64.t) =
  fun x ->
    fun lo ->
      fun hi ->
        if
          (FStar_UInt32.uint_to_t lo) =
            (FStar_UInt32.uint_to_t (Prims.of_int (64)))
        then FStar_UInt64.uint_to_t Prims.int_zero
        else
          FStar_UInt64.shift_right
            (FStar_UInt64.logand x
               (if lo = hi
                then FStar_UInt64.uint_to_t Prims.int_zero
                else
                  FStar_UInt64.shift_left
                    (FStar_UInt64.shift_right
                       (FStar_UInt64.uint_to_t
                          (Prims.parse_int "18446744073709551615"))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo))) (FStar_UInt32.uint_to_t lo)
let (not_bitfield_mask64 : Prims.nat -> Prims.nat -> FStar_UInt64.t) =
  fun lo ->
    fun hi ->
      FStar_UInt64.lognot
        (if lo = hi
         then FStar_UInt64.uint_to_t Prims.int_zero
         else
           FStar_UInt64.shift_left
             (FStar_UInt64.shift_right
                (FStar_UInt64.uint_to_t
                   (Prims.parse_int "18446744073709551615"))
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                   (FStar_UInt32.uint_to_t (hi - lo))))
             (FStar_UInt32.uint_to_t lo))
let (u64_shift_left : FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun x ->
    fun amount ->
      if amount = (FStar_UInt32.uint_to_t (Prims.of_int (64)))
      then FStar_UInt64.uint_to_t Prims.int_zero
      else FStar_UInt64.shift_left x amount
let (set_bitfield64 :
  FStar_UInt64.t ->
    Prims.nat -> Prims.nat -> FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          FStar_UInt64.logor
            (FStar_UInt64.logand x
               (FStar_UInt64.lognot
                  (if lo = hi
                   then FStar_UInt64.uint_to_t Prims.int_zero
                   else
                     FStar_UInt64.shift_left
                       (FStar_UInt64.shift_right
                          (FStar_UInt64.uint_to_t
                             (Prims.parse_int "18446744073709551615"))
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                             (FStar_UInt32.uint_to_t (hi - lo))))
                       (FStar_UInt32.uint_to_t lo))))
            (if
               (FStar_UInt32.uint_to_t lo) =
                 (FStar_UInt32.uint_to_t (Prims.of_int (64)))
             then FStar_UInt64.uint_to_t Prims.int_zero
             else FStar_UInt64.shift_left v (FStar_UInt32.uint_to_t lo))
let (bitfield_eq64_lhs :
  FStar_UInt64.t -> Prims.nat -> Prims.nat -> FStar_UInt64.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt64.logand x
          (if lo = hi
           then FStar_UInt64.uint_to_t Prims.int_zero
           else
             FStar_UInt64.shift_left
               (FStar_UInt64.shift_right
                  (FStar_UInt64.uint_to_t
                     (Prims.parse_int "18446744073709551615"))
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                     (FStar_UInt32.uint_to_t (hi - lo))))
               (FStar_UInt32.uint_to_t lo))
let (bitfield_eq64_rhs :
  FStar_UInt64.t ->
    Prims.nat -> Prims.nat -> FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          if
            (FStar_UInt32.uint_to_t lo) =
              (FStar_UInt32.uint_to_t (Prims.of_int (64)))
          then FStar_UInt64.uint_to_t Prims.int_zero
          else FStar_UInt64.shift_left v (FStar_UInt32.uint_to_t lo)
let (get_bitfield_gen64 :
  FStar_UInt64.t -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt64.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt64.shift_right
          (FStar_UInt64.shift_left x
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                hi))
          (FStar_UInt32.add
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                hi) lo)
let (set_bitfield_gen64 :
  FStar_UInt64.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          FStar_UInt64.logor
            (FStar_UInt64.logand x
               (FStar_UInt64.lognot
                  (FStar_UInt64.shift_left
                     (FStar_UInt64.shift_right
                        (FStar_UInt64.uint_to_t
                           (Prims.parse_int "18446744073709551615"))
                        (FStar_UInt32.sub
                           (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                           (FStar_UInt32.sub hi lo))) lo)))
            (FStar_UInt64.shift_left v lo)
let (bitfield_mask32 : Prims.nat -> Prims.nat -> FStar_UInt32.t) =
  fun lo ->
    fun hi ->
      if lo = hi
      then FStar_UInt32.uint_to_t Prims.int_zero
      else
        FStar_UInt32.shift_left
          (FStar_UInt32.shift_right
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                (FStar_UInt32.uint_to_t (hi - lo))))
          (FStar_UInt32.uint_to_t lo)
let (u32_shift_right : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x ->
    fun amount ->
      if amount = (FStar_UInt32.uint_to_t (Prims.of_int (32)))
      then FStar_UInt32.uint_to_t Prims.int_zero
      else FStar_UInt32.shift_right x amount
let (get_bitfield32 :
  FStar_UInt32.t -> Prims.nat -> Prims.nat -> FStar_UInt32.t) =
  fun x ->
    fun lo ->
      fun hi ->
        if
          (FStar_UInt32.uint_to_t lo) =
            (FStar_UInt32.uint_to_t (Prims.of_int (32)))
        then FStar_UInt32.uint_to_t Prims.int_zero
        else
          FStar_UInt32.shift_right
            (FStar_UInt32.logand x
               (if lo = hi
                then FStar_UInt32.uint_to_t Prims.int_zero
                else
                  FStar_UInt32.shift_left
                    (FStar_UInt32.shift_right
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo))) (FStar_UInt32.uint_to_t lo)
let (not_bitfield_mask32 : Prims.nat -> Prims.nat -> FStar_UInt32.t) =
  fun lo ->
    fun hi ->
      FStar_UInt32.lognot
        (if lo = hi
         then FStar_UInt32.uint_to_t Prims.int_zero
         else
           FStar_UInt32.shift_left
             (FStar_UInt32.shift_right
                (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                   (FStar_UInt32.uint_to_t (hi - lo))))
             (FStar_UInt32.uint_to_t lo))
let (u32_shift_left : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x ->
    fun amount ->
      if amount = (FStar_UInt32.uint_to_t (Prims.of_int (32)))
      then FStar_UInt32.uint_to_t Prims.int_zero
      else FStar_UInt32.shift_left x amount
let (set_bitfield32 :
  FStar_UInt32.t ->
    Prims.nat -> Prims.nat -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          FStar_UInt32.logor
            (FStar_UInt32.logand x
               (FStar_UInt32.lognot
                  (if lo = hi
                   then FStar_UInt32.uint_to_t Prims.int_zero
                   else
                     FStar_UInt32.shift_left
                       (FStar_UInt32.shift_right
                          (FStar_UInt32.uint_to_t
                             (Prims.parse_int "4294967295"))
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                             (FStar_UInt32.uint_to_t (hi - lo))))
                       (FStar_UInt32.uint_to_t lo))))
            (if
               (FStar_UInt32.uint_to_t lo) =
                 (FStar_UInt32.uint_to_t (Prims.of_int (32)))
             then FStar_UInt32.uint_to_t Prims.int_zero
             else FStar_UInt32.shift_left v (FStar_UInt32.uint_to_t lo))
let (bitfield_eq32_lhs :
  FStar_UInt32.t -> Prims.nat -> Prims.nat -> FStar_UInt32.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt32.logand x
          (if lo = hi
           then FStar_UInt32.uint_to_t Prims.int_zero
           else
             FStar_UInt32.shift_left
               (FStar_UInt32.shift_right
                  (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                     (FStar_UInt32.uint_to_t (hi - lo))))
               (FStar_UInt32.uint_to_t lo))
let (bitfield_eq32_rhs :
  FStar_UInt32.t ->
    Prims.nat -> Prims.nat -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          if
            (FStar_UInt32.uint_to_t lo) =
              (FStar_UInt32.uint_to_t (Prims.of_int (32)))
          then FStar_UInt32.uint_to_t Prims.int_zero
          else FStar_UInt32.shift_left v (FStar_UInt32.uint_to_t lo)
let (get_bitfield_gen32 :
  FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt32.shift_right
          (FStar_UInt32.shift_left x
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                hi))
          (FStar_UInt32.add
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                hi) lo)
let (set_bitfield_gen32 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          FStar_UInt32.logor
            (FStar_UInt32.logand x
               (FStar_UInt32.lognot
                  (FStar_UInt32.shift_left
                     (FStar_UInt32.shift_right
                        (FStar_UInt32.uint_to_t
                           (Prims.parse_int "4294967295"))
                        (FStar_UInt32.sub
                           (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                           (FStar_UInt32.sub hi lo))) lo)))
            (FStar_UInt32.shift_left v lo)
let (bitfield_mask16 : Prims.nat -> Prims.nat -> FStar_UInt16.t) =
  fun lo ->
    fun hi ->
      if lo = hi
      then FStar_UInt16.uint_to_t Prims.int_zero
      else
        FStar_UInt16.shift_left
          (FStar_UInt16.shift_right
             (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                (FStar_UInt32.uint_to_t (hi - lo))))
          (FStar_UInt32.uint_to_t lo)
let (u16_shift_right : FStar_UInt16.t -> FStar_UInt32.t -> FStar_UInt16.t) =
  fun x ->
    fun amount ->
      if amount = (FStar_UInt32.uint_to_t (Prims.of_int (16)))
      then FStar_UInt16.uint_to_t Prims.int_zero
      else FStar_UInt16.shift_right x amount
let (get_bitfield16 :
  FStar_UInt16.t -> Prims.nat -> Prims.nat -> FStar_UInt16.t) =
  fun x ->
    fun lo ->
      fun hi ->
        if
          (FStar_UInt32.uint_to_t lo) =
            (FStar_UInt32.uint_to_t (Prims.of_int (16)))
        then FStar_UInt16.uint_to_t Prims.int_zero
        else
          FStar_UInt16.shift_right
            (FStar_UInt16.logand x
               (if lo = hi
                then FStar_UInt16.uint_to_t Prims.int_zero
                else
                  FStar_UInt16.shift_left
                    (FStar_UInt16.shift_right
                       (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo))) (FStar_UInt32.uint_to_t lo)
let (not_bitfield_mask16 : Prims.nat -> Prims.nat -> FStar_UInt16.t) =
  fun lo ->
    fun hi ->
      FStar_UInt16.lognot
        (if lo = hi
         then FStar_UInt16.uint_to_t Prims.int_zero
         else
           FStar_UInt16.shift_left
             (FStar_UInt16.shift_right
                (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                   (FStar_UInt32.uint_to_t (hi - lo))))
             (FStar_UInt32.uint_to_t lo))
let (u16_shift_left : FStar_UInt16.t -> FStar_UInt32.t -> FStar_UInt16.t) =
  fun x ->
    fun amount ->
      if amount = (FStar_UInt32.uint_to_t (Prims.of_int (16)))
      then FStar_UInt16.uint_to_t Prims.int_zero
      else FStar_UInt16.shift_left x amount
let (set_bitfield16 :
  FStar_UInt16.t ->
    Prims.nat -> Prims.nat -> FStar_UInt16.t -> FStar_UInt16.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          FStar_UInt16.logor
            (FStar_UInt16.logand x
               (FStar_UInt16.lognot
                  (if lo = hi
                   then FStar_UInt16.uint_to_t Prims.int_zero
                   else
                     FStar_UInt16.shift_left
                       (FStar_UInt16.shift_right
                          (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                             (FStar_UInt32.uint_to_t (hi - lo))))
                       (FStar_UInt32.uint_to_t lo))))
            (if
               (FStar_UInt32.uint_to_t lo) =
                 (FStar_UInt32.uint_to_t (Prims.of_int (16)))
             then FStar_UInt16.uint_to_t Prims.int_zero
             else FStar_UInt16.shift_left v (FStar_UInt32.uint_to_t lo))
let (bitfield_eq16_lhs :
  FStar_UInt16.t -> Prims.nat -> Prims.nat -> FStar_UInt16.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt16.logand x
          (if lo = hi
           then FStar_UInt16.uint_to_t Prims.int_zero
           else
             FStar_UInt16.shift_left
               (FStar_UInt16.shift_right
                  (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                     (FStar_UInt32.uint_to_t (hi - lo))))
               (FStar_UInt32.uint_to_t lo))
let (bitfield_eq16_rhs :
  FStar_UInt16.t ->
    Prims.nat -> Prims.nat -> FStar_UInt16.t -> FStar_UInt16.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          if
            (FStar_UInt32.uint_to_t lo) =
              (FStar_UInt32.uint_to_t (Prims.of_int (16)))
          then FStar_UInt16.uint_to_t Prims.int_zero
          else FStar_UInt16.shift_left v (FStar_UInt32.uint_to_t lo)
let (get_bitfield_gen16 :
  FStar_UInt16.t -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt16.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt16.shift_right
          (FStar_UInt16.shift_left x
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                hi))
          (FStar_UInt32.add
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                hi) lo)
let (set_bitfield_gen16 :
  FStar_UInt16.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt16.t -> FStar_UInt16.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          FStar_UInt16.logor
            (FStar_UInt16.logand x
               (FStar_UInt16.lognot
                  (FStar_UInt16.shift_left
                     (FStar_UInt16.shift_right
                        (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                        (FStar_UInt32.sub
                           (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                           (FStar_UInt32.sub hi lo))) lo)))
            (FStar_UInt16.shift_left v lo)
let (bitfield_mask8 : Prims.nat -> Prims.nat -> FStar_UInt8.t) =
  fun lo ->
    fun hi ->
      if lo = hi
      then FStar_UInt8.uint_to_t Prims.int_zero
      else
        FStar_UInt8.shift_left
          (FStar_UInt8.shift_right
             (FStar_UInt8.uint_to_t (Prims.of_int (255)))
             (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                (FStar_UInt32.uint_to_t (hi - lo))))
          (FStar_UInt32.uint_to_t lo)
let (u8_shift_right : FStar_UInt8.t -> FStar_UInt32.t -> FStar_UInt8.t) =
  fun x ->
    fun amount ->
      let y =
        if amount = (FStar_UInt32.uint_to_t (Prims.of_int (8)))
        then FStar_UInt8.uint_to_t Prims.int_zero
        else FStar_UInt8.shift_right x amount in
      y
let (get_bitfield_gen8 :
  FStar_UInt8.t -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt8.t) =
  fun x ->
    fun lo ->
      fun hi ->
        let op1 =
          FStar_UInt8.shift_left x
            (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (8))) hi) in
        let op2 =
          FStar_UInt8.shift_right op1
            (FStar_UInt32.add
               (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                  hi) lo) in
        op2
let (set_bitfield_gen8 :
  FStar_UInt8.t ->
    FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt8.t -> FStar_UInt8.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          let op0 = FStar_UInt8.uint_to_t (Prims.of_int (255)) in
          let op1 =
            FStar_UInt8.shift_right op0
              (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                 (FStar_UInt32.sub hi lo)) in
          let op2 = FStar_UInt8.shift_left op1 lo in
          let op3 = FStar_UInt8.lognot op2 in
          let op4 = FStar_UInt8.logand x op3 in
          let op5 = FStar_UInt8.shift_left v lo in
          let op6 = FStar_UInt8.logor op4 op5 in op6
let (get_bitfield8 :
  FStar_UInt8.t -> Prims.nat -> Prims.nat -> FStar_UInt8.t) =
  fun x ->
    fun lo ->
      fun hi ->
        if lo = hi
        then FStar_UInt8.uint_to_t Prims.int_zero
        else
          get_bitfield_gen8 x (FStar_UInt32.uint_to_t lo)
            (FStar_UInt32.uint_to_t hi)
let (not_bitfield_mask8 : Prims.nat -> Prims.nat -> FStar_UInt8.t) =
  fun lo ->
    fun hi ->
      FStar_UInt8.lognot
        (if lo = hi
         then FStar_UInt8.uint_to_t Prims.int_zero
         else
           FStar_UInt8.shift_left
             (FStar_UInt8.shift_right
                (FStar_UInt8.uint_to_t (Prims.of_int (255)))
                (FStar_UInt32.sub (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                   (FStar_UInt32.uint_to_t (hi - lo))))
             (FStar_UInt32.uint_to_t lo))
let (u8_shift_left : FStar_UInt8.t -> FStar_UInt32.t -> FStar_UInt8.t) =
  fun x ->
    fun amount ->
      let y =
        if amount = (FStar_UInt32.uint_to_t (Prims.of_int (8)))
        then FStar_UInt8.uint_to_t Prims.int_zero
        else FStar_UInt8.shift_left x amount in
      y
let (set_bitfield8 :
  FStar_UInt8.t -> Prims.nat -> Prims.nat -> FStar_UInt8.t -> FStar_UInt8.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          if lo = hi
          then x
          else
            set_bitfield_gen8 x (FStar_UInt32.uint_to_t lo)
              (FStar_UInt32.uint_to_t hi) v
let (bitfield_eq8_lhs :
  FStar_UInt8.t -> Prims.nat -> Prims.nat -> FStar_UInt8.t) =
  fun x ->
    fun lo ->
      fun hi ->
        FStar_UInt8.logand x
          (if lo = hi
           then FStar_UInt8.uint_to_t Prims.int_zero
           else
             FStar_UInt8.shift_left
               (FStar_UInt8.shift_right
                  (FStar_UInt8.uint_to_t (Prims.of_int (255)))
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                     (FStar_UInt32.uint_to_t (hi - lo))))
               (FStar_UInt32.uint_to_t lo))
let (bitfield_eq8_rhs :
  FStar_UInt8.t -> Prims.nat -> Prims.nat -> FStar_UInt8.t -> FStar_UInt8.t)
  =
  fun x ->
    fun lo ->
      fun hi ->
        fun v ->
          let y =
            if
              (FStar_UInt32.uint_to_t lo) =
                (FStar_UInt32.uint_to_t (Prims.of_int (8)))
            then FStar_UInt8.uint_to_t Prims.int_zero
            else FStar_UInt8.shift_left v (FStar_UInt32.uint_to_t lo) in
          y
let (uint64 : (unit, FStar_UInt64.t) uint_t) =
  {
    v = FStar_UInt64.v;
    uint_to_t = FStar_UInt64.uint_to_t;
    v_uint_to_t = ();
    uint_to_t_v = ();
    get_bitfield_gen =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt64.shift_right
               (FStar_UInt64.shift_left x
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (64))) hi))
               (FStar_UInt32.add
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (64))) hi) lo));
    set_bitfield_gen =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               FStar_UInt64.logor
                 (FStar_UInt64.logand x
                    (FStar_UInt64.lognot
                       (FStar_UInt64.shift_left
                          (FStar_UInt64.shift_right
                             (FStar_UInt64.uint_to_t
                                (Prims.parse_int "18446744073709551615"))
                             (FStar_UInt32.sub
                                (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                                (FStar_UInt32.sub hi lo))) lo)))
                 (FStar_UInt64.shift_left z lo));
    get_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             if
               (FStar_UInt32.uint_to_t lo) =
                 (FStar_UInt32.uint_to_t (Prims.of_int (64)))
             then FStar_UInt64.uint_to_t Prims.int_zero
             else
               FStar_UInt64.shift_right
                 (FStar_UInt64.logand x
                    (if lo = hi
                     then FStar_UInt64.uint_to_t Prims.int_zero
                     else
                       FStar_UInt64.shift_left
                         (FStar_UInt64.shift_right
                            (FStar_UInt64.uint_to_t
                               (Prims.parse_int "18446744073709551615"))
                            (FStar_UInt32.sub
                               (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                               (FStar_UInt32.uint_to_t (hi - lo))))
                         (FStar_UInt32.uint_to_t lo)))
                 (FStar_UInt32.uint_to_t lo));
    set_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               FStar_UInt64.logor
                 (FStar_UInt64.logand x
                    (FStar_UInt64.lognot
                       (if lo = hi
                        then FStar_UInt64.uint_to_t Prims.int_zero
                        else
                          FStar_UInt64.shift_left
                            (FStar_UInt64.shift_right
                               (FStar_UInt64.uint_to_t
                                  (Prims.parse_int "18446744073709551615"))
                               (FStar_UInt32.sub
                                  (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                                  (FStar_UInt32.uint_to_t (hi - lo))))
                            (FStar_UInt32.uint_to_t lo))))
                 (if
                    (FStar_UInt32.uint_to_t lo) =
                      (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                  then FStar_UInt64.uint_to_t Prims.int_zero
                  else FStar_UInt64.shift_left z (FStar_UInt32.uint_to_t lo)));
    logor = (fun x -> fun y -> FStar_UInt64.logor x y);
    bitfield_eq_lhs =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt64.logand x
               (if lo = hi
                then FStar_UInt64.uint_to_t Prims.int_zero
                else
                  FStar_UInt64.shift_left
                    (FStar_UInt64.shift_right
                       (FStar_UInt64.uint_to_t
                          (Prims.parse_int "18446744073709551615"))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (64)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo)));
    bitfield_eq_rhs =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               if
                 (FStar_UInt32.uint_to_t lo) =
                   (FStar_UInt32.uint_to_t (Prims.of_int (64)))
               then FStar_UInt64.uint_to_t Prims.int_zero
               else FStar_UInt64.shift_left z (FStar_UInt32.uint_to_t lo))
  }


let (uint32 : (unit, FStar_UInt32.t) uint_t) =
  {
    v = FStar_UInt32.v;
    uint_to_t = FStar_UInt32.uint_to_t;
    v_uint_to_t = ();
    uint_to_t_v = ();
    get_bitfield_gen =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt32.shift_right
               (FStar_UInt32.shift_left x
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (32))) hi))
               (FStar_UInt32.add
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (32))) hi) lo));
    set_bitfield_gen =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               FStar_UInt32.logor
                 (FStar_UInt32.logand x
                    (FStar_UInt32.lognot
                       (FStar_UInt32.shift_left
                          (FStar_UInt32.shift_right
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295"))
                             (FStar_UInt32.sub
                                (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                                (FStar_UInt32.sub hi lo))) lo)))
                 (FStar_UInt32.shift_left z lo));
    get_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             if
               (FStar_UInt32.uint_to_t lo) =
                 (FStar_UInt32.uint_to_t (Prims.of_int (32)))
             then FStar_UInt32.uint_to_t Prims.int_zero
             else
               FStar_UInt32.shift_right
                 (FStar_UInt32.logand x
                    (if lo = hi
                     then FStar_UInt32.uint_to_t Prims.int_zero
                     else
                       FStar_UInt32.shift_left
                         (FStar_UInt32.shift_right
                            (FStar_UInt32.uint_to_t
                               (Prims.parse_int "4294967295"))
                            (FStar_UInt32.sub
                               (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                               (FStar_UInt32.uint_to_t (hi - lo))))
                         (FStar_UInt32.uint_to_t lo)))
                 (FStar_UInt32.uint_to_t lo));
    set_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               FStar_UInt32.logor
                 (FStar_UInt32.logand x
                    (FStar_UInt32.lognot
                       (if lo = hi
                        then FStar_UInt32.uint_to_t Prims.int_zero
                        else
                          FStar_UInt32.shift_left
                            (FStar_UInt32.shift_right
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "4294967295"))
                               (FStar_UInt32.sub
                                  (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                                  (FStar_UInt32.uint_to_t (hi - lo))))
                            (FStar_UInt32.uint_to_t lo))))
                 (if
                    (FStar_UInt32.uint_to_t lo) =
                      (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                  then FStar_UInt32.uint_to_t Prims.int_zero
                  else FStar_UInt32.shift_left z (FStar_UInt32.uint_to_t lo)));
    logor = (fun x -> fun y -> FStar_UInt32.logor x y);
    bitfield_eq_lhs =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt32.logand x
               (if lo = hi
                then FStar_UInt32.uint_to_t Prims.int_zero
                else
                  FStar_UInt32.shift_left
                    (FStar_UInt32.shift_right
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (32)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo)));
    bitfield_eq_rhs =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               if
                 (FStar_UInt32.uint_to_t lo) =
                   (FStar_UInt32.uint_to_t (Prims.of_int (32)))
               then FStar_UInt32.uint_to_t Prims.int_zero
               else FStar_UInt32.shift_left z (FStar_UInt32.uint_to_t lo))
  }


let (uint16 : (unit, FStar_UInt16.t) uint_t) =
  {
    v = FStar_UInt16.v;
    uint_to_t = FStar_UInt16.uint_to_t;
    v_uint_to_t = ();
    uint_to_t_v = ();
    get_bitfield_gen =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt16.shift_right
               (FStar_UInt16.shift_left x
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (16))) hi))
               (FStar_UInt32.add
                  (FStar_UInt32.sub
                     (FStar_UInt32.uint_to_t (Prims.of_int (16))) hi) lo));
    set_bitfield_gen =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               FStar_UInt16.logor
                 (FStar_UInt16.logand x
                    (FStar_UInt16.lognot
                       (FStar_UInt16.shift_left
                          (FStar_UInt16.shift_right
                             (FStar_UInt16.uint_to_t
                                (Prims.parse_int "65535"))
                             (FStar_UInt32.sub
                                (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                                (FStar_UInt32.sub hi lo))) lo)))
                 (FStar_UInt16.shift_left z lo));
    get_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             if
               (FStar_UInt32.uint_to_t lo) =
                 (FStar_UInt32.uint_to_t (Prims.of_int (16)))
             then FStar_UInt16.uint_to_t Prims.int_zero
             else
               FStar_UInt16.shift_right
                 (FStar_UInt16.logand x
                    (if lo = hi
                     then FStar_UInt16.uint_to_t Prims.int_zero
                     else
                       FStar_UInt16.shift_left
                         (FStar_UInt16.shift_right
                            (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                            (FStar_UInt32.sub
                               (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                               (FStar_UInt32.uint_to_t (hi - lo))))
                         (FStar_UInt32.uint_to_t lo)))
                 (FStar_UInt32.uint_to_t lo));
    set_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               FStar_UInt16.logor
                 (FStar_UInt16.logand x
                    (FStar_UInt16.lognot
                       (if lo = hi
                        then FStar_UInt16.uint_to_t Prims.int_zero
                        else
                          FStar_UInt16.shift_left
                            (FStar_UInt16.shift_right
                               (FStar_UInt16.uint_to_t
                                  (Prims.parse_int "65535"))
                               (FStar_UInt32.sub
                                  (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                                  (FStar_UInt32.uint_to_t (hi - lo))))
                            (FStar_UInt32.uint_to_t lo))))
                 (if
                    (FStar_UInt32.uint_to_t lo) =
                      (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                  then FStar_UInt16.uint_to_t Prims.int_zero
                  else FStar_UInt16.shift_left z (FStar_UInt32.uint_to_t lo)));
    logor = (fun x -> fun y -> FStar_UInt16.logor x y);
    bitfield_eq_lhs =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt16.logand x
               (if lo = hi
                then FStar_UInt16.uint_to_t Prims.int_zero
                else
                  FStar_UInt16.shift_left
                    (FStar_UInt16.shift_right
                       (FStar_UInt16.uint_to_t (Prims.parse_int "65535"))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (16)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo)));
    bitfield_eq_rhs =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               if
                 (FStar_UInt32.uint_to_t lo) =
                   (FStar_UInt32.uint_to_t (Prims.of_int (16)))
               then FStar_UInt16.uint_to_t Prims.int_zero
               else FStar_UInt16.shift_left z (FStar_UInt32.uint_to_t lo))
  }


let (uint8 : (unit, FStar_UInt8.t) uint_t) =
  {
    v = FStar_UInt8.v;
    uint_to_t = FStar_UInt8.uint_to_t;
    v_uint_to_t = ();
    uint_to_t_v = ();
    get_bitfield_gen =
      (fun x -> fun lo -> fun hi -> get_bitfield_gen8 x lo hi);
    set_bitfield_gen =
      (fun x -> fun lo -> fun hi -> fun z -> set_bitfield_gen8 x lo hi z);
    get_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             if lo = hi
             then FStar_UInt8.uint_to_t Prims.int_zero
             else
               get_bitfield_gen8 x (FStar_UInt32.uint_to_t lo)
                 (FStar_UInt32.uint_to_t hi));
    set_bitfield =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               if lo = hi
               then x
               else
                 set_bitfield_gen8 x (FStar_UInt32.uint_to_t lo)
                   (FStar_UInt32.uint_to_t hi) z);
    logor = (fun x -> fun y -> FStar_UInt8.logor x y);
    bitfield_eq_lhs =
      (fun x ->
         fun lo ->
           fun hi ->
             FStar_UInt8.logand x
               (if lo = hi
                then FStar_UInt8.uint_to_t Prims.int_zero
                else
                  FStar_UInt8.shift_left
                    (FStar_UInt8.shift_right
                       (FStar_UInt8.uint_to_t (Prims.of_int (255)))
                       (FStar_UInt32.sub
                          (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                          (FStar_UInt32.uint_to_t (hi - lo))))
                    (FStar_UInt32.uint_to_t lo)));
    bitfield_eq_rhs =
      (fun x ->
         fun lo ->
           fun hi ->
             fun z ->
               let y =
                 if
                   (FStar_UInt32.uint_to_t lo) =
                     (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                 then FStar_UInt8.uint_to_t Prims.int_zero
                 else FStar_UInt8.shift_left z (FStar_UInt32.uint_to_t lo) in
               y)
  }

