open Prims
type norm_t =
  | Norm 
let (uu___is_Norm : norm_t -> Prims.bool) = fun projectee -> true
let rec list_map : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f ->
    fun l -> match l with | [] -> [] | a1::q -> (f a1) :: (list_map f q)
type ('key, 'repr) enum = ('key * 'repr) Prims.list
let rec list_mem : 't . 't -> 't Prims.list -> Prims.bool =
  fun x ->
    fun l -> match l with | [] -> false | a::q -> (x = a) || (list_mem x q)

type ('key, 'repr, 'e) enum_key = 'key
let make_enum_key : 'key 'repr . ('key, 'repr) enum -> 'key -> 'key =
  fun e -> fun k -> k
type ('key, 'repr, 'e) enum_repr = 'repr
let flip : 'a 'b . ('a * 'b) -> ('b * 'a) =
  fun c -> let uu___ = c in match uu___ with | (ca, cb) -> (cb, ca)






let enum_key_of_repr : 'key 'repr . ('key, 'repr) enum -> 'repr -> 'key =
  fun e ->
    fun r ->
      let e' = list_map flip e in
      let k =
        FStar_Pervasives_Native.__proj__Some__item__v
          (FStar_List_Tot_Base.assoc r e') in
      k



let enum_repr_of_key : 'key 'repr . ('key, 'repr) enum -> 'key -> 'repr =
  fun e ->
    fun k ->
      let r =
        FStar_Pervasives_Native.__proj__Some__item__v
          (FStar_List_Tot_Base.assoc k e) in
      r






type ('key, 'repr, 'e) unknown_enum_repr = 'repr
type ('key, 'repr, 'e) maybe_enum_key =
  | Known of 'key 
  | Unknown of 'repr 
let uu___is_Known :
  'key 'repr .
    ('key, 'repr) enum -> ('key, 'repr, unit) maybe_enum_key -> Prims.bool
  =
  fun e ->
    fun projectee -> match projectee with | Known _0 -> true | uu___ -> false
let __proj__Known__item___0 :
  'key 'repr .
    ('key, 'repr) enum -> ('key, 'repr, unit) maybe_enum_key -> 'key
  = fun e -> fun projectee -> match projectee with | Known _0 -> _0
let uu___is_Unknown :
  'key 'repr .
    ('key, 'repr) enum -> ('key, 'repr, unit) maybe_enum_key -> Prims.bool
  =
  fun e ->
    fun projectee ->
      match projectee with | Unknown _0 -> true | uu___ -> false
let __proj__Unknown__item___0 :
  'key 'repr .
    ('key, 'repr) enum -> ('key, 'repr, unit) maybe_enum_key -> 'repr
  = fun e -> fun projectee -> match projectee with | Unknown _0 -> _0
let maybe_enum_key_of_repr :
  'key 'repr .
    ('key, 'repr) enum -> 'repr -> ('key, 'repr, unit) maybe_enum_key
  =
  fun e ->
    fun r ->
      if list_mem r (list_map FStar_Pervasives_Native.snd e)
      then Known (enum_key_of_repr e r)
      else Unknown r



let repr_of_maybe_enum_key :
  'key 'repr .
    ('key, 'repr) enum -> ('key, 'repr, unit) maybe_enum_key -> 'repr
  =
  fun e ->
    fun x ->
      match x with | Known k' -> enum_repr_of_key e k' | Unknown r -> r


type ('key, 'repr, 'l) is_total_enum = unit
type ('key, 'repr) total_enum = ('key, 'repr) enum
let synth_total_enum_key :
  'key 'repr . ('key, 'repr) total_enum -> 'key -> 'key =
  fun l -> fun k -> let k' = k in k'

let synth_total_enum_key_recip :
  'key 'repr . ('key, 'repr) total_enum -> 'key -> 'key = fun l -> fun k -> k

type ('key, 'repr, 'e) maybe_total_enum_key =
  | TotalKnown of 'key 
  | TotalUnknown of 'repr 
let uu___is_TotalKnown :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_total_enum_key -> Prims.bool
  =
  fun e ->
    fun projectee ->
      match projectee with | TotalKnown _0 -> true | uu___ -> false
let __proj__TotalKnown__item___0 :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_total_enum_key -> 'key
  = fun e -> fun projectee -> match projectee with | TotalKnown _0 -> _0
let uu___is_TotalUnknown :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_total_enum_key -> Prims.bool
  =
  fun e ->
    fun projectee ->
      match projectee with | TotalUnknown _0 -> true | uu___ -> false
let __proj__TotalUnknown__item___0 :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_total_enum_key -> 'repr
  = fun e -> fun projectee -> match projectee with | TotalUnknown _0 -> _0
let maybe_total_enum_key_of_repr :
  'key 'repr .
    ('key, 'repr) total_enum ->
      'repr -> ('key, 'repr, unit) maybe_total_enum_key
  =
  fun e ->
    fun r ->
      if list_mem r (list_map FStar_Pervasives_Native.snd e)
      then TotalKnown (enum_key_of_repr e r)
      else TotalUnknown r

let repr_of_maybe_total_enum_key :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_total_enum_key -> 'repr
  =
  fun e ->
    fun k ->
      match k with
      | TotalKnown k' -> enum_repr_of_key e k'
      | TotalUnknown r -> r

let maybe_enum_key_of_total :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_total_enum_key ->
        ('key, 'repr, unit) maybe_enum_key
  =
  fun e ->
    fun k ->
      match k with | TotalKnown ek -> Known ek | TotalUnknown r -> Unknown r
let total_of_maybe_enum_key :
  'key 'repr .
    ('key, 'repr) total_enum ->
      ('key, 'repr, unit) maybe_enum_key ->
        ('key, 'repr, unit) maybe_total_enum_key
  =
  fun e ->
    fun k ->
      match k with | Known ek -> TotalKnown ek | Unknown r -> TotalUnknown r


type ('t, 'r) r_reflexive_prop = unit
type ('t, 'r) r_reflexive_t = unit

type ('t, 'r) r_transitive_prop = unit
type ('t, 'r) r_transitive_t = unit

type ('t, 'eq) if_combinator =
  Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't
let default_if : 't . Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't =
  fun cond ->
    fun s_true -> fun s_false -> if cond then s_true () else s_false ()
type ('u, 'v, 'eq, 'f1, 'f2) feq = unit



let fif :
  'u 'v 'eq .
    (Prims.bool -> (unit -> 'v) -> (unit -> 'v) -> 'v) ->
      Prims.bool -> (unit -> 'u -> 'v) -> (unit -> 'u -> 'v) -> 'u -> 'v
  =
  fun ifc ->
    fun cond ->
      fun s_true ->
        fun s_false ->
          fun x -> ifc cond (fun h -> s_true () x) (fun h -> s_false () x)
type ('t, 'key, 'repr, 'e) enum_destr_t =
  unit ->
    (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
      unit -> unit -> ('key -> 't) -> 'key -> 't
let enum_tail' : 'key 'repr . ('key, 'repr) enum -> ('key, 'repr) enum =
  fun e -> match e with | uu___::y -> y | uu___ -> []
let enum_tail : 'key 'repr . ('key, 'repr) enum -> ('key, 'repr) enum =
  fun e -> match e with | uu___::y -> y | uu___ -> []
let enum_destr_cons :
  't 'key 'repr .
    ('key, 'repr) enum ->
      (unit ->
         (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
           unit -> unit -> ('key -> 't) -> 'key -> 't)
        ->
        unit ->
          (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
            unit -> unit -> ('key -> 't) -> 'key -> 't
  =
  fun e ->
    fun g ->
      fun eq ->
        fun ift ->
          fun eq_refl ->
            fun eq_trans ->
              match e with
              | (k, uu___)::uu___1 ->
                  (fun f ->
                     fun x ->
                       ift (k = x) (fun h -> f k)
                         (fun h -> g () ift () () (fun x' -> f x') x))
let enum_destr_cons' :
  't 'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        (unit ->
           (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
             unit -> unit -> ('key -> 't) -> 'key -> 't)
          ->
          unit ->
            (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
              unit -> unit -> ('key -> 't) -> 'key -> 't
  =
  fun e ->
    fun u ->
      fun g ->
        fun eq ->
          fun ift ->
            fun eq_refl ->
              fun eq_trans ->
                match e with
                | (k, uu___)::uu___1 ->
                    (fun f ->
                       fun x ->
                         ift (k = x) (fun h -> f k)
                           (fun h -> g () ift () () (fun x' -> f x') x))
let enum_destr_cons_nil :
  't 'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
          unit -> unit -> ('key -> 't) -> 'key -> 't
  =
  fun e ->
    fun eq ->
      fun ift ->
        fun eq_refl ->
          fun eq_trans ->
            match e with | (k, uu___)::uu___1 -> (fun f -> fun x -> f k)
let enum_destr_cons_nil' :
  't 'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        unit ->
          unit ->
            (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
              unit -> unit -> ('key -> 't) -> 'key -> 't
  =
  fun e ->
    fun u1 ->
      fun u2 ->
        fun eq ->
          fun ift ->
            fun eq_refl ->
              fun eq_trans ->
                match e with | (k, uu___)::uu___1 -> (fun f -> fun x -> f k)
type ('key, 'repr, 'e, 'v) dep_enum_destr =
  unit ->
    ('key -> Prims.bool -> (unit -> 'v) -> (unit -> 'v) -> 'v) ->
      unit -> unit -> ('key -> 'v) -> 'key -> 'v
let dep_enum_destr_cons :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        unit ->
          (unit ->
             ('key ->
                Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
               -> unit -> unit -> ('key -> Obj.t) -> 'key -> Obj.t)
            ->
            unit ->
              ('key ->
                 Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                -> unit -> unit -> ('key -> Obj.t) -> 'key -> Obj.t
  =
  fun e ->
    fun u ->
      fun v ->
        fun destr ->
          match e with
          | (k, uu___)::uu___1 ->
              (fun v_eq ->
                 fun v_if ->
                   fun v_eq_refl ->
                     fun v_eq_trans ->
                       fun f ->
                         fun k' ->
                           v_if k' (k = k') (fun uu___2 -> f k)
                             (fun uu___2 ->
                                destr () (fun k1 -> v_if k1) () ()
                                  (fun k1 -> f k1) k'))
let dep_enum_destr_cons_nil :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        unit ->
          unit ->
            ('key ->
               Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
              -> unit -> unit -> ('key -> Obj.t) -> 'key -> Obj.t
  =
  fun e ->
    fun u ->
      fun v ->
        match e with
        | (k, uu___)::uu___1 ->
            (fun v_eq ->
               fun v_if ->
                 fun v_eq_refl -> fun v_eq_trans -> fun f -> fun k' -> f k)
type ('key, 'repr, 'e, 'l, 'x) maybe_enum_key_of_repr_not_in = unit



type ('t, 'key, 'repr, 'e, 'l1, 'l2, 'u1) maybe_enum_destr_t' =
  unit ->
    (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
      unit ->
        unit -> (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't
type ('t, 'key, 'repr, 'e) maybe_enum_destr_t =
  unit ->
    (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
      unit ->
        unit -> (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't
let destr_maybe_total_enum_repr :
  't 'key 'repr .
    ('key, 'repr) total_enum ->
      (unit ->
         (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
           unit ->
             unit ->
               (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't)
        ->
        unit ->
          (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
            unit ->
              unit ->
                (('key, 'repr, unit) maybe_total_enum_key -> 't) ->
                  'repr -> 't
  =
  fun e ->
    fun destr ->
      fun eq ->
        fun ift ->
          fun eq_refl ->
            fun eq_trans ->
              fun f ->
                fun x ->
                  destr () ift () ()
                    (fun y ->
                       f
                         (match y with
                          | Known ek -> TotalKnown ek
                          | Unknown r -> TotalUnknown r)) x
let maybe_enum_destr_t_intro :
  't 'key 'repr .
    ('key, 'repr) enum ->
      (unit ->
         (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
           unit ->
             unit ->
               (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't)
        ->
        unit ->
          (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
            unit ->
              unit ->
                (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't
  = fun e -> fun f -> f

let list_hd : 't . 't Prims.list -> 't =
  fun l -> match l with | a::uu___ -> a
let list_tl : 't . 't Prims.list -> 't Prims.list =
  fun l -> match l with | uu___::q -> q
let maybe_enum_destr_cons :
  't 'key 'repr .
    ('key, 'repr) enum ->
      ('key * 'repr) Prims.list ->
        ('key * 'repr) Prims.list ->
          unit ->
            (unit ->
               (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
                 unit ->
                   unit ->
                     (('key, 'repr, unit) maybe_enum_key -> 't) ->
                       'repr -> 't)
              ->
              unit ->
                (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
                  unit ->
                    unit ->
                      (('key, 'repr, unit) maybe_enum_key -> 't) ->
                        'repr -> 't
  =
  fun e ->
    fun l1 ->
      fun l2 ->
        fun u1 ->
          fun g ->
            fun eq ->
              fun ift ->
                fun eq_refl ->
                  fun eq_trans ->
                    fun f ->
                      match match l2 with | a::uu___ -> a with
                      | (k, r) ->
                          (fun x ->
                             ift (x = r) (fun h -> f (Known k))
                               (fun h -> g () ift () () f x))

let maybe_enum_destr_nil :
  't 'key 'repr .
    ('key, 'repr) enum ->
      ('key * 'repr) Prims.list ->
        ('key * 'repr) Prims.list ->
          unit ->
            unit ->
              (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
                unit ->
                  unit ->
                    (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't
  =
  fun e ->
    fun l1 ->
      fun l2 ->
        fun u1 ->
          fun eq ->
            fun ift ->
              fun eq_refl -> fun eq_trans -> fun f -> fun x -> f (Unknown x)
let rec mk_maybe_enum_destr' :
  't 'key 'repr .
    ('key, 'repr) enum ->
      ('key * 'repr) Prims.list ->
        ('key * 'repr) Prims.list ->
          unit ->
            unit ->
              (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
                unit ->
                  unit ->
                    (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't
  =
  fun e ->
    fun l1 ->
      fun l2 ->
        fun u ->
          match l2 with
          | [] ->
              (fun eq ->
                 fun ift ->
                   fun eq_refl ->
                     fun eq_trans -> fun f -> fun x -> f (Unknown x))
          | uu___ ->
              (fun eq ->
                 fun ift ->
                   fun eq_refl ->
                     fun eq_trans ->
                       fun f ->
                         match match l2 with | a::uu___1 -> a with
                         | (k, r) ->
                             (fun x ->
                                ift (x = r) (fun h -> f (Known k))
                                  (fun h ->
                                     mk_maybe_enum_destr' e
                                       ((match l2 with | a::uu___1 -> a) ::
                                       l1) (match l2 with | uu___1::q -> q)
                                       () () ift () () f x)))
let mk_maybe_enum_destr :
  't 'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        (Prims.bool -> (unit -> 't) -> (unit -> 't) -> 't) ->
          unit ->
            unit -> (('key, 'repr, unit) maybe_enum_key -> 't) -> 'repr -> 't
  = fun e -> mk_maybe_enum_destr' e [] e ()
type ('key, 'repr, 'e, 'v) dep_maybe_enum_destr_t =
  unit ->
    (('key, 'repr, unit) maybe_enum_key ->
       Prims.bool -> (unit -> 'v) -> (unit -> 'v) -> 'v)
      ->
      unit ->
        unit -> (('key, 'repr, unit) maybe_enum_key -> 'v) -> 'repr -> 'v
type ('key, 'repr, 'e, 'v, 'l1, 'l2, 'u1) dep_maybe_enum_destr_t' =
  unit ->
    (('key, 'repr, unit) maybe_enum_key ->
       Prims.bool -> (unit -> 'v) -> (unit -> 'v) -> 'v)
      ->
      unit ->
        unit -> (('key, 'repr, unit) maybe_enum_key -> 'v) -> 'repr -> 'v
let dep_maybe_enum_destr_t_intro :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        (unit ->
           (('key, 'repr, unit) maybe_enum_key ->
              Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
             ->
             unit ->
               unit ->
                 (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                   'repr -> Obj.t)
          ->
          unit ->
            (('key, 'repr, unit) maybe_enum_key ->
               Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
              ->
              unit ->
                unit ->
                  (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                    'repr -> Obj.t
  = fun e -> fun v -> fun d -> d
let dep_maybe_enum_destr_cons :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        ('key * 'repr) Prims.list ->
          ('key * 'repr) Prims.list ->
            unit ->
              (unit ->
                 (('key, 'repr, unit) maybe_enum_key ->
                    Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                   ->
                   unit ->
                     unit ->
                       (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                         'repr -> Obj.t)
                ->
                unit ->
                  (('key, 'repr, unit) maybe_enum_key ->
                     Prims.bool ->
                       (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                    ->
                    unit ->
                      unit ->
                        (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                          'repr -> Obj.t
  =
  fun e ->
    fun v ->
      fun l1 ->
        fun l2 ->
          fun u1 ->
            fun g ->
              fun v_eq ->
                fun v_if ->
                  fun v_eq_refl ->
                    fun v_eq_trans ->
                      fun f ->
                        match match l2 with | a::uu___ -> a with
                        | (k, r) ->
                            (fun x ->
                               v_if (maybe_enum_key_of_repr e x) (x = r)
                                 (fun h -> f (Known k))
                                 (fun h -> g () v_if () () f x))
let dep_maybe_enum_destr_nil :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        ('key * 'repr) Prims.list ->
          ('key * 'repr) Prims.list ->
            unit ->
              unit ->
                (('key, 'repr, unit) maybe_enum_key ->
                   Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                  ->
                  unit ->
                    unit ->
                      (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                        'repr -> Obj.t
  =
  fun e ->
    fun v ->
      fun l1 ->
        fun l2 ->
          fun u1 ->
            fun v_eq ->
              fun v_if ->
                fun v_eq_refl ->
                  fun v_eq_trans -> fun f -> fun x -> f (Unknown x)
let rec mk_dep_maybe_enum_destr' :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        ('key * 'repr) Prims.list ->
          ('key * 'repr) Prims.list ->
            unit ->
              unit ->
                (('key, 'repr, unit) maybe_enum_key ->
                   Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
                  ->
                  unit ->
                    unit ->
                      (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                        'repr -> Obj.t
  =
  fun e ->
    fun v ->
      fun l1 ->
        fun l2 ->
          fun u1 ->
            match l2 with
            | [] ->
                (fun v_eq ->
                   fun v_if ->
                     fun v_eq_refl ->
                       fun v_eq_trans -> fun f -> fun x -> f (Unknown x))
            | uu___ ->
                (fun v_eq ->
                   fun v_if ->
                     fun v_eq_refl ->
                       fun v_eq_trans ->
                         fun f ->
                           match match l2 with | a::uu___1 -> a with
                           | (k, r) ->
                               (fun x ->
                                  v_if (maybe_enum_key_of_repr e x) (
                                    x = r) (fun h -> f (Known k))
                                    (fun h ->
                                       mk_dep_maybe_enum_destr' e ()
                                         ((match l2 with | a::uu___1 -> a) ::
                                         l1) (match l2 with | uu___1::q -> q)
                                         () () v_if () () f x)))
let mk_dep_maybe_enum_destr :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        unit ->
          (('key, 'repr, unit) maybe_enum_key ->
             Prims.bool -> (unit -> Obj.t) -> (unit -> Obj.t) -> Obj.t)
            ->
            unit ->
              unit ->
                (('key, 'repr, unit) maybe_enum_key -> Obj.t) ->
                  'repr -> Obj.t
  = fun e -> fun v -> mk_dep_maybe_enum_destr' e () [] e ()
type ('t, 'p, 'l) list_forallp = Obj.t

let destruct_maybe_enum_key :
  'key 'value .
    ('key, 'value) enum ->
      unit ->
        ('key -> unit -> Obj.t) ->
          ('value -> unit -> Obj.t) ->
            ('key, 'value, unit) maybe_enum_key -> Obj.t
  =
  fun e ->
    fun f ->
      fun f_known ->
        fun f_unknown ->
          fun x ->
            match x with
            | Known x' -> f_known x' ()
            | Unknown x' -> f_unknown x' ()

type ('key, 'repr, 'e) enum_repr_of_key'_t = 'key -> 'repr
let enum_repr_of_key_cons :
  'key 'repr .
    ('key, 'repr) enum ->
      ('key, 'repr, unit) enum_repr_of_key'_t ->
        ('key, 'repr, unit) enum_repr_of_key'_t
  =
  fun e ->
    fun f ->
      match e with | (k, r)::uu___ -> (fun x -> if k = x then r else f x)
let enum_repr_of_key_cons' :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        ('key, 'repr, unit) enum_repr_of_key'_t ->
          ('key, 'repr, unit) enum_repr_of_key'_t
  =
  fun e ->
    fun u ->
      fun f ->
        match e with | (k, r)::uu___ -> (fun x -> if k = x then r else f x)
let enum_repr_of_key_cons_nil :
  'key 'repr . ('key, 'repr) enum -> ('key, 'repr, unit) enum_repr_of_key'_t
  = fun e -> match e with | (k, r)::[] -> (fun x -> r)
let enum_repr_of_key_cons_nil' :
  'key 'repr .
    ('key, 'repr) enum ->
      unit -> unit -> ('key, 'repr, unit) enum_repr_of_key'_t
  = fun e -> fun u1 -> fun u2 -> match e with | (k, r)::[] -> (fun x -> r)

type ('key, 'repr, 'e) maybe_enum_key_of_repr'_t =
  'repr -> ('key, 'repr, unit) maybe_enum_key
let maybe_enum_key_of_repr'_t_cons_nil :
  'key 'repr .
    ('key, 'repr) enum -> ('key, 'repr, unit) maybe_enum_key_of_repr'_t
  =
  fun e ->
    match e with
    | (k, r)::[] -> (fun x -> if r = x then Known k else Unknown x)
let maybe_enum_key_of_repr'_t_cons_nil' :
  'key 'repr .
    ('key, 'repr) enum ->
      unit -> unit -> ('key, 'repr, unit) maybe_enum_key_of_repr'_t
  =
  fun e ->
    fun u1 ->
      fun u2 ->
        match e with
        | (k, r)::[] -> (fun x -> if r = x then Known k else Unknown x)
let maybe_enum_key_of_repr'_t_cons :
  'key 'repr .
    ('key, 'repr) enum ->
      ('key, 'repr, unit) maybe_enum_key_of_repr'_t ->
        ('key, 'repr, unit) maybe_enum_key_of_repr'_t
  =
  fun e ->
    fun g ->
      match e with
      | (k, r)::uu___ ->
          (fun x ->
             if r = x
             then Known k
             else
               (let y = g x in
                match y with | Known k' -> Known k' | Unknown x' -> Unknown x))
let maybe_enum_key_of_repr'_t_cons' :
  'key 'repr .
    ('key, 'repr) enum ->
      unit ->
        ('key, 'repr, unit) maybe_enum_key_of_repr'_t ->
          ('key, 'repr, unit) maybe_enum_key_of_repr'_t
  =
  fun e ->
    fun u ->
      fun g ->
        match e with
        | (k, r)::uu___ ->
            (fun x ->
               if r = x
               then Known k
               else
                 (let y = g x in
                  match y with
                  | Known k' -> Known k'
                  | Unknown x' -> Unknown x))