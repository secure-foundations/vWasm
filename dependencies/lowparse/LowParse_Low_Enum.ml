open Prims
let is_known :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key -> Prims.bool
  =
  fun e ->
    fun k ->
      match k with | LowParse_Spec_Enum.Known uu___ -> true | uu___ -> false
let validate_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'repr)
            ->
            ('key, 'repr) LowParse_Spec_Enum.enum ->
              (unit ->
                 (Prims.bool ->
                    (unit -> Prims.bool) ->
                      (unit -> Prims.bool) -> Prims.bool)
                   ->
                   unit ->
                     unit ->
                       (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key
                          -> Prims.bool)
                         -> 'repr -> Prims.bool)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t
  =
  fun k ->
    fun p ->
      fun v ->
        fun p32 ->
          fun e ->
            fun destr ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      let h1 = FStar_HyperStack_ST.get () in
                      let res = v () () input pos in
                      if LowParse_Low_ErrorCode.is_error res
                      then res
                      else
                        (let va =
                           p32 () () input
                             (FStar_Int_Cast.uint64_to_uint32 pos) in
                         if
                           Prims.op_Negation
                             (destr ()
                                (fun cond ->
                                   fun s_true ->
                                     fun s_false ->
                                       if cond then s_true () else s_false ())
                                () ()
                                (fun k1 ->
                                   match k1 with
                                   | LowParse_Spec_Enum.Known uu___1 -> true
                                   | uu___1 -> false) va)
                         then LowParse_Low_ErrorCode.validator_error_generic
                         else res)
let mk_validate_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'repr)
            ->
            ('key, 'repr) LowParse_Spec_Enum.enum ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t -> FStar_UInt64.t
  =
  fun k ->
    fun p ->
      fun v ->
        fun p32 ->
          fun e ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let h1 = FStar_HyperStack_ST.get () in
                    let res = v () () input pos in
                    if LowParse_Low_ErrorCode.is_error res
                    then res
                    else
                      (let va =
                         p32 () () input
                           (FStar_Int_Cast.uint64_to_uint32 pos) in
                       if
                         Prims.op_Negation
                           (LowParse_Spec_Enum.mk_maybe_enum_destr e ()
                              (fun cond ->
                                 fun s_true ->
                                   fun s_false ->
                                     if cond then s_true () else s_false ())
                              () ()
                              (fun k1 ->
                                 match k1 with
                                 | LowParse_Spec_Enum.Known uu___1 -> true
                                 | uu___1 -> false) va)
                       then LowParse_Low_ErrorCode.validator_error_generic
                       else res)
let validate_maybe_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t
  =
  fun k ->
    fun p ->
      fun v ->
        fun e ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in v () () input pos
let jump_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun j ->
        fun e ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let h1 = FStar_HyperStack_ST.get () in j () () input pos
let jump_maybe_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun j ->
        fun e ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in j () () input pos
let read_maybe_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'repr)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            (unit ->
               (Prims.bool ->
                  (unit ->
                     ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key)
                    ->
                    (unit ->
                       ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key)
                      ->
                      ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key)
                 ->
                 unit ->
                   unit ->
                     (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key
                        ->
                        ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key)
                       ->
                       'repr ->
                         ('key, 'repr, unit)
                           LowParse_Spec_Enum.maybe_enum_key)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t ->
                      ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key
  =
  fun k ->
    fun p ->
      fun j ->
        fun e ->
          fun destr ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let res = j () () input pos in
                    destr ()
                      (fun cond ->
                         fun s_true ->
                           fun s_false ->
                             if cond then s_true () else s_false ()) () ()
                      (fun k1 -> k1) res
let mk_read_maybe_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'repr)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t ->
                    ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key
  =
  fun k ->
    fun p ->
      fun j ->
        fun e ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let res = j () () input pos in
                  LowParse_Spec_Enum.mk_maybe_enum_destr e ()
                    (fun cond ->
                       fun s_true ->
                         fun s_false ->
                           if cond then s_true () else s_false ()) () ()
                    (fun k1 -> k1) res
type ('key, 'repr, 'e, 'k, 'ku) read_enum_key_prop = Obj.t
type ('key, 'repr, 'e, 'k) read_enum_key_t = unit -> 'key
let read_enum_key_f :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key -> unit -> 'key
  =
  fun e ->
    fun k ->
      fun sq ->
        match k with
        | LowParse_Spec_Enum.Known k_ -> k_
        | uu___ -> (match e with | (k_, uu___1)::uu___2 -> k_)
type ('key, 'repr, 'e, 'k, 'uuuuu, 'uuuuu1) read_enum_key_eq = unit
let read_enum_key_if :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
        Prims.bool ->
          (unit -> unit -> 'key) -> (unit -> unit -> 'key) -> unit -> 'key
  =
  fun e ->
    fun k ->
      fun cond ->
        fun sv_true ->
          fun sv_false ->
            fun sq -> if cond then sv_true () () else sv_false () ()
let read_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'repr)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            (unit ->
               (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  Prims.bool ->
                    (unit -> unit -> 'key) ->
                      (unit -> unit -> 'key) -> unit -> 'key)
                 ->
                 unit ->
                   unit ->
                     (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key
                        -> unit -> 'key)
                       -> 'repr -> unit -> 'key)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> 'key
  =
  fun k ->
    fun p ->
      fun p32 ->
        fun e ->
          fun destr ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let res =
                      let h1 = FStar_HyperStack_ST.get () in
                      p32 () () input pos in
                    destr ()
                      (fun k1 ->
                         fun cond ->
                           fun sv_true ->
                             fun sv_false ->
                               fun sq ->
                                 if cond
                                 then sv_true () ()
                                 else sv_false () ()) () ()
                      (fun k1 ->
                         fun sq ->
                           match k1 with
                           | LowParse_Spec_Enum.Known k_ -> k_
                           | uu___ ->
                               (match e with | (k_, uu___1)::uu___2 -> k_))
                      res ()
let mk_read_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'repr)
          ->
          ('key, 'repr) LowParse_Spec_Enum.enum ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> 'key
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun k ->
                     fun p ->
                       fun p32 ->
                         fun e ->
                           fun rrel ->
                             fun rel ->
                               fun input ->
                                 fun pos ->
                                   let h = FStar_HyperStack_ST.get () in
                                   let res =
                                     let h1 = FStar_HyperStack_ST.get () in
                                     p32 () () input pos in
                                   Obj.magic
                                     ((fun uu___ ->
                                         (Obj.magic
                                            (LowParse_Spec_Enum.mk_dep_maybe_enum_destr
                                               e () ()
                                               (fun uu___3 ->
                                                  fun uu___2 ->
                                                    fun uu___1 ->
                                                      fun uu___ ->
                                                        (fun k1 ->
                                                           fun cond ->
                                                             fun sv_true ->
                                                               let sv_true =
                                                                 Obj.magic
                                                                   sv_true in
                                                               fun sv_false
                                                                 ->
                                                                 let sv_false
                                                                   =
                                                                   Obj.magic
                                                                    sv_false in
                                                                 Obj.magic
                                                                   (fun sq ->
                                                                    if cond
                                                                    then
                                                                    sv_true
                                                                    () ()
                                                                    else
                                                                    sv_false
                                                                    () ()))
                                                          uu___3 uu___2
                                                          uu___1 uu___) () ()
                                               (fun uu___ ->
                                                  (fun k1 ->
                                                     Obj.magic
                                                       (fun sq ->
                                                          match k1 with
                                                          | LowParse_Spec_Enum.Known
                                                              k_ -> k_
                                                          | uu___ ->
                                                              (match e with
                                                               | (k_, uu___1)::uu___2
                                                                   -> k_)))
                                                    uu___) res)) uu___)
                                        (Obj.repr ()))) uu___7 uu___6 uu___5
                    uu___4 uu___3 uu___2 uu___1 uu___
let write_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('repr ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('key, 'repr) LowParse_Spec_Enum.enum ->
              ('key, 'repr, unit) LowParse_Spec_Enum.enum_repr_of_key'_t ->
                'key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun e ->
            fun destr ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let pos' =
                          let res = s32 (destr x) () () input pos in
                          let h = FStar_HyperStack_ST.get () in res in
                        let h = FStar_HyperStack_ST.get () in pos'
let write_enum_key_weak :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('repr ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('key, 'repr) LowParse_Spec_Enum.enum ->
              ('key, 'repr, unit) LowParse_Spec_Enum.enum_repr_of_key'_t ->
                'key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun e ->
            fun destr ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let pos' =
                          let res = s32 (destr x) () () input pos in
                          let h = FStar_HyperStack_ST.get () in res in
                        let h = FStar_HyperStack_ST.get () in pos'
let write_maybe_enum_key :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('repr ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('key, 'repr) LowParse_Spec_Enum.enum ->
              ('key, 'repr, unit) LowParse_Spec_Enum.enum_repr_of_key'_t ->
                ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun e ->
            fun destr ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let pos' =
                          s32
                            (match x with
                             | LowParse_Spec_Enum.Unknown r -> r
                             | LowParse_Spec_Enum.Known k1 -> destr k1) () ()
                            input pos in
                        let h = FStar_HyperStack_ST.get () in pos'
let write_maybe_enum_key_weak :
  'key 'repr .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('repr ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            ('key, 'repr) LowParse_Spec_Enum.enum ->
              ('key, 'repr, unit) LowParse_Spec_Enum.enum_repr_of_key'_t ->
                ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun e ->
            fun destr ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let pos' =
                          s32
                            (match x with
                             | LowParse_Spec_Enum.Unknown r -> r
                             | LowParse_Spec_Enum.Known k1 -> destr k1) () ()
                            input pos in
                        let h = FStar_HyperStack_ST.get () in pos'