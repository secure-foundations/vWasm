open Prims
let (parse32_maybe_enum_key_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          (Obj.t, Obj.t, unit)
                            LowParse_Spec_Enum.maybe_enum_key_of_repr'_t ->
                            LowParse_SLow_Base.bytes32 ->
                              (Obj.t * FStar_UInt32.t)
                                FStar_Pervasives_Native.option)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun p32 ->
            fun e ->
              fun k' ->
                fun t' ->
                  fun p' ->
                    fun u1 ->
                      fun u15 ->
                        fun u2 ->
                          fun f ->
                            fun input ->
                              match p32 input with
                              | FStar_Pervasives_Native.Some (v1, consumed)
                                  ->
                                  FStar_Pervasives_Native.Some
                                    ((Obj.magic (f v1)), consumed)
                              | uu___ -> FStar_Pervasives_Native.None
let (parse32_maybe_enum_key :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
              (Obj.t, Obj.t, unit)
                LowParse_Spec_Enum.maybe_enum_key_of_repr'_t ->
                LowParse_SLow_Base.bytes32 ->
                  ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key *
                    FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun p32 ->
            fun e ->
              fun f ->
                fun input ->
                  match p32 input with
                  | FStar_Pervasives_Native.Some (v1, consumed) ->
                      FStar_Pervasives_Native.Some ((f v1), consumed)
                  | uu___ -> FStar_Pervasives_Native.None
let (parse32_enum_key_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        (LowParse_SLow_Base.bytes32 ->
                           ((Obj.t, Obj.t, unit)
                             LowParse_Spec_Enum.maybe_enum_key *
                             FStar_UInt32.t) FStar_Pervasives_Native.option)
                          ->
                          LowParse_SLow_Base.bytes32 ->
                            (Obj.t * FStar_UInt32.t)
                              FStar_Pervasives_Native.option)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun e ->
            fun k' ->
              fun t' ->
                fun p' ->
                  fun u1 ->
                    fun u15 ->
                      fun u2 ->
                        fun pe ->
                          fun input ->
                            match pe input with
                            | FStar_Pervasives_Native.Some (k1, consumed) ->
                                (match k1 with
                                 | LowParse_Spec_Enum.Known k'1 ->
                                     FStar_Pervasives_Native.Some
                                       (k'1, consumed)
                                 | uu___ -> FStar_Pervasives_Native.None)
                            | uu___ -> FStar_Pervasives_Native.None
let (parse32_enum_key :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
              (Obj.t, Obj.t, unit)
                LowParse_Spec_Enum.maybe_enum_key_of_repr'_t ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun p32 ->
            fun e ->
              fun f ->
                fun input ->
                  match match p32 input with
                        | FStar_Pervasives_Native.Some (v1, consumed) ->
                            FStar_Pervasives_Native.Some ((f v1), consumed)
                        | uu___ -> FStar_Pervasives_Native.None
                  with
                  | FStar_Pervasives_Native.Some (k1, consumed) ->
                      (match k1 with
                       | LowParse_Spec_Enum.Known k' ->
                           FStar_Pervasives_Native.Some (k', consumed)
                       | uu___ -> FStar_Pervasives_Native.None)
                  | uu___ -> FStar_Pervasives_Native.None
let (serialize32_enum_key_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          unit ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t, unit)
                                  LowParse_Spec_Enum.enum_repr_of_key'_t ->
                                  Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s ->
            fun s32 ->
              fun e ->
                fun k' ->
                  fun t' ->
                    fun p' ->
                      fun s' ->
                        fun u1 ->
                          fun u15 ->
                            fun u2 ->
                              fun u3 -> fun f -> fun input -> s32 (f input)
let (serialize32_enum_key :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.enum_repr_of_key'_t
                  -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s -> fun s32 -> fun e -> fun f -> fun input -> s32 (f input)
let (size32_enum_key_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> FStar_UInt32.t) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          unit ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t, unit)
                                  LowParse_Spec_Enum.enum_repr_of_key'_t ->
                                  Obj.t -> FStar_UInt32.t)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s ->
            fun s32 ->
              fun e ->
                fun k' ->
                  fun t' ->
                    fun p' ->
                      fun s' ->
                        fun u1 ->
                          fun u15 ->
                            fun u2 ->
                              fun u3 -> fun f -> fun input -> s32 (f input)
let (size32_enum_key :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> FStar_UInt32.t) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.enum_repr_of_key'_t
                  -> Obj.t -> FStar_UInt32.t)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s -> fun s32 -> fun e -> fun f -> fun input -> s32 (f input)
let (serialize32_maybe_enum_key_gen' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> LowParse_SLow_Base.bytes32) ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s ->
            fun s32 ->
              fun e ->
                fun f ->
                  fun input ->
                    match input with
                    | LowParse_Spec_Enum.Known k1 -> f k1
                    | LowParse_Spec_Enum.Unknown r -> s32 r
let (serialize32_maybe_enum_key_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          unit ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t, unit)
                                  LowParse_Spec_Enum.enum_repr_of_key'_t ->
                                  Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun uu___16 ->
    fun uu___15 ->
      fun uu___14 ->
        fun uu___13 ->
          fun uu___12 ->
            fun uu___11 ->
              fun uu___10 ->
                fun uu___9 ->
                  fun uu___8 ->
                    fun uu___7 ->
                      fun uu___6 ->
                        fun uu___5 ->
                          fun uu___4 ->
                            fun uu___3 ->
                              fun uu___2 ->
                                fun uu___1 ->
                                  fun uu___ ->
                                    (fun k ->
                                       fun key ->
                                         fun repr ->
                                           fun p ->
                                             fun s ->
                                               fun s32 ->
                                                 fun e ->
                                                   fun k' ->
                                                     fun t' ->
                                                       fun p' ->
                                                         fun s' ->
                                                           fun u1 ->
                                                             fun u15 ->
                                                               fun u2 ->
                                                                 fun u3 ->
                                                                   fun f ->
                                                                    fun input
                                                                    ->
                                                                    let input
                                                                    =
                                                                    Obj.magic
                                                                    input in
                                                                    match input
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k1 ->
                                                                    Obj.magic
                                                                    (s32
                                                                    (f k1))
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    r ->
                                                                    Obj.magic
                                                                    (s32 r))
                                      uu___16 uu___15 uu___14 uu___13 uu___12
                                      uu___11 uu___10 uu___9 uu___8 uu___7
                                      uu___6 uu___5 uu___4 uu___3 uu___2
                                      uu___1 uu___
let (serialize32_maybe_enum_key :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.enum_repr_of_key'_t
                  ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s ->
            fun s32 ->
              fun e ->
                fun f ->
                  fun input ->
                    match input with
                    | LowParse_Spec_Enum.Known k1 -> s32 (f k1)
                    | LowParse_Spec_Enum.Unknown r -> s32 r
let (size32_maybe_enum_key_gen' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> FStar_UInt32.t) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> FStar_UInt32.t) ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    FStar_UInt32.t)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s ->
            fun s32 ->
              fun e ->
                fun f ->
                  fun input ->
                    match input with
                    | LowParse_Spec_Enum.Known k1 -> f k1
                    | LowParse_Spec_Enum.Unknown r -> s32 r
let (size32_maybe_enum_key_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> FStar_UInt32.t) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          unit ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t, unit)
                                  LowParse_Spec_Enum.enum_repr_of_key'_t ->
                                  Obj.t -> FStar_UInt32.t)
  =
  fun uu___16 ->
    fun uu___15 ->
      fun uu___14 ->
        fun uu___13 ->
          fun uu___12 ->
            fun uu___11 ->
              fun uu___10 ->
                fun uu___9 ->
                  fun uu___8 ->
                    fun uu___7 ->
                      fun uu___6 ->
                        fun uu___5 ->
                          fun uu___4 ->
                            fun uu___3 ->
                              fun uu___2 ->
                                fun uu___1 ->
                                  fun uu___ ->
                                    (fun k ->
                                       fun key ->
                                         fun repr ->
                                           fun p ->
                                             fun s ->
                                               fun s32 ->
                                                 fun e ->
                                                   fun k' ->
                                                     fun t' ->
                                                       fun p' ->
                                                         fun s' ->
                                                           fun u1 ->
                                                             fun u15 ->
                                                               fun u2 ->
                                                                 fun u3 ->
                                                                   fun f ->
                                                                    fun input
                                                                    ->
                                                                    let input
                                                                    =
                                                                    Obj.magic
                                                                    input in
                                                                    match input
                                                                    with
                                                                    | 
                                                                    LowParse_Spec_Enum.Known
                                                                    k1 ->
                                                                    Obj.magic
                                                                    (s32
                                                                    (f k1))
                                                                    | 
                                                                    LowParse_Spec_Enum.Unknown
                                                                    r ->
                                                                    Obj.magic
                                                                    (s32 r))
                                      uu___16 uu___15 uu___14 uu___13 uu___12
                                      uu___11 uu___10 uu___9 uu___8 uu___7
                                      uu___6 uu___5 uu___4 uu___3 uu___2
                                      uu___1 uu___
let (size32_maybe_enum_key :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> FStar_UInt32.t) ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.enum_repr_of_key'_t
                  ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    FStar_UInt32.t)
  =
  fun k ->
    fun key ->
      fun repr ->
        fun p ->
          fun s ->
            fun s32 ->
              fun e ->
                fun f ->
                  fun input ->
                    match input with
                    | LowParse_Spec_Enum.Known k1 -> s32 (f k1)
                    | LowParse_Spec_Enum.Unknown r -> s32 r