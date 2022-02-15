open Prims
type ('kt, 'k) serializer32_sum_gen_precond = unit
type 't parse32_sum_t =
  LowParse_SLow_Base.bytes32 ->
    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option
type ('t, 'uuuuu, 'uuuuu1) parse32_sum_eq = unit
let (parse32_sum_if :
  LowParse_Spec_Sum.sum ->
    Prims.bool ->
      (unit ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        (unit ->
           LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_SLow_Base.bytes32 ->
            (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun cond ->
      fun s_true ->
        fun s_false -> fun x -> if cond then s_true () x else s_false () x


let (parse32_sum_cases' :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        Obj.t ->
          LowParse_SLow_Base.bytes32 ->
            (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun k ->
          fun input ->
            match pc32 k input with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some
                  (((match t with
                     | LowParse_Spec_Sum.Sum
                         (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                          synth_case, uu___6, uu___7, uu___8)
                         -> synth_case k v1)), consumed)
            | uu___ -> FStar_Pervasives_Native.None

type ('t, 'pc, 'k) parse32_sum_cases_t =
  LowParse_SLow_Base.bytes32 ->
    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option
type ('t, 'pc, 'k, 'x, 'y) parse32_sum_cases_t_eq = unit
let (parse32_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      Obj.t ->
        Prims.bool ->
          (unit ->
             LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            (unit ->
               LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              LowParse_SLow_Base.bytes32 ->
                (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun sv_true ->
            fun sv_false ->
              fun input ->
                if cond then sv_true () input else sv_false () input
let (parse32_sum_cases_aux :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        Obj.t ->
          LowParse_SLow_Base.bytes32 ->
            (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun k ->
          fun input ->
            match pc32 k input with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some
                  (((match t with
                     | LowParse_Spec_Sum.Sum
                         (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                          synth_case, uu___6, uu___7, uu___8)
                         -> synth_case k v1)), consumed)
            | uu___ -> FStar_Pervasives_Native.None
let (parse32_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        (unit ->
           (Obj.t ->
              Prims.bool ->
                (unit ->
                   LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                  ->
                  (unit ->
                     LowParse_SLow_Base.bytes32 ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                    ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
             ->
             unit ->
               unit ->
                 (Obj.t ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                   ->
                   Obj.t ->
                     LowParse_SLow_Base.bytes32 ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
          ->
          Obj.t ->
            LowParse_SLow_Base.bytes32 ->
              (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun destr ->
          fun k ->
            destr ()
              (fun k1 ->
                 fun cond ->
                   fun sv_true ->
                     fun sv_false ->
                       fun input ->
                         if cond then sv_true () input else sv_false () input)
              () ()
              (fun k1 ->
                 fun input ->
                   match pc32 k1 input with
                   | FStar_Pervasives_Native.Some (v1, consumed) ->
                       FStar_Pervasives_Native.Some
                         (((match t with
                            | LowParse_Spec_Sum.Sum
                                (uu___, uu___1, uu___2, uu___3, uu___4,
                                 uu___5, synth_case, uu___6, uu___7, uu___8)
                                -> synth_case k1 v1)), consumed)
                   | uu___ -> FStar_Pervasives_Native.None) k
let (parse32_sum' :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            (Obj.t ->
               LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              (unit ->
                 (Prims.bool ->
                    (unit ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                      ->
                      (unit ->
                         (Obj.t * FStar_UInt32.t)
                           FStar_Pervasives_Native.option)
                        ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          (Obj.t * FStar_UInt32.t)
                            FStar_Pervasives_Native.option)
                         ->
                         Obj.t ->
                           (Obj.t * FStar_UInt32.t)
                             FStar_Pervasives_Native.option)
                ->
                FStar_Bytes.bytes ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun pc ->
            fun pc32 ->
              fun destr ->
                fun input ->
                  let pi = p32 input in
                  match pi with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (k, consumed_k) ->
                      let input_k =
                        FStar_Bytes.slice input consumed_k
                          (FStar_Bytes.len input) in
                      destr ()
                        (fun cond ->
                           fun s_true ->
                             fun s_false ->
                               if cond then s_true () else s_false ()) () ()
                        (fun k1 ->
                           let pcases2 =
                             match pc32 k1 input_k with
                             | FStar_Pervasives_Native.Some (v1, consumed) ->
                                 FStar_Pervasives_Native.Some
                                   (((match t with
                                      | LowParse_Spec_Sum.Sum
                                          (uu___, uu___1, uu___2, uu___3,
                                           uu___4, uu___5, synth_case,
                                           uu___6, uu___7, uu___8)
                                          -> synth_case k1 v1)), consumed)
                             | uu___ -> FStar_Pervasives_Native.None in
                           match pcases2 with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (x, consumed_x) ->
                               FStar_Pervasives_Native.Some
                                 (x,
                                   (FStar_UInt32.add consumed_k consumed_x)))
                        k
let (parse32_sum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            (Obj.t ->
               LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              (unit ->
                 (Prims.bool ->
                    (unit ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                      ->
                      (unit ->
                         (Obj.t * FStar_UInt32.t)
                           FStar_Pervasives_Native.option)
                        ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          (Obj.t * FStar_UInt32.t)
                            FStar_Pervasives_Native.option)
                         ->
                         Obj.t ->
                           (Obj.t * FStar_UInt32.t)
                             FStar_Pervasives_Native.option)
                ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun pc ->
            fun pc32 ->
              fun destr ->
                fun input ->
                  let pi = p32 input in
                  match pi with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (k, consumed_k) ->
                      let input_k =
                        FStar_Bytes.slice input consumed_k
                          (FStar_Bytes.len input) in
                      destr ()
                        (fun cond ->
                           fun s_true ->
                             fun s_false ->
                               if cond then s_true () else s_false ()) () ()
                        (fun k1 ->
                           let pcases2 =
                             match pc32 k1 input_k with
                             | FStar_Pervasives_Native.Some (v1, consumed) ->
                                 FStar_Pervasives_Native.Some
                                   (((match t with
                                      | LowParse_Spec_Sum.Sum
                                          (uu___, uu___1, uu___2, uu___3,
                                           uu___4, uu___5, synth_case,
                                           uu___6, uu___7, uu___8)
                                          -> synth_case k1 v1)), consumed)
                             | uu___ -> FStar_Pervasives_Native.None in
                           match pcases2 with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (x, consumed_x) ->
                               FStar_Pervasives_Native.Some
                                 (x,
                                   (FStar_UInt32.add consumed_k consumed_x)))
                        k
let (parse32_sum2 :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            (Obj.t ->
               LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              (unit ->
                 (Prims.bool ->
                    (unit ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                      ->
                      (unit ->
                         (Obj.t * FStar_UInt32.t)
                           FStar_Pervasives_Native.option)
                        ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          (Obj.t * FStar_UInt32.t)
                            FStar_Pervasives_Native.option)
                         ->
                         Obj.t ->
                           (Obj.t * FStar_UInt32.t)
                             FStar_Pervasives_Native.option)
                ->
                (Obj.t, Obj.t, unit)
                  LowParse_Spec_Enum.maybe_enum_key_of_repr'_t ->
                  LowParse_SLow_Base.bytes32 ->
                    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun pc ->
            fun pc32 ->
              fun destr ->
                fun f ->
                  fun input ->
                    let pi =
                      match match p32 input with
                            | FStar_Pervasives_Native.Some (v1, consumed) ->
                                FStar_Pervasives_Native.Some
                                  ((f v1), consumed)
                            | uu___ -> FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (k, consumed) ->
                          (match k with
                           | LowParse_Spec_Enum.Known k' ->
                               FStar_Pervasives_Native.Some (k', consumed)
                           | uu___ -> FStar_Pervasives_Native.None)
                      | uu___ -> FStar_Pervasives_Native.None in
                    match pi with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (k, consumed_k) ->
                        let input_k =
                          FStar_Bytes.slice input consumed_k
                            (FStar_Bytes.len input) in
                        destr ()
                          (fun cond ->
                             fun s_true ->
                               fun s_false ->
                                 if cond then s_true () else s_false ()) ()
                          ()
                          (fun k1 ->
                             let pcases2 =
                               match pc32 k1 input_k with
                               | FStar_Pervasives_Native.Some (v1, consumed)
                                   ->
                                   FStar_Pervasives_Native.Some
                                     (((match t with
                                        | LowParse_Spec_Sum.Sum
                                            (uu___, uu___1, uu___2, uu___3,
                                             uu___4, uu___5, synth_case,
                                             uu___6, uu___7, uu___8)
                                            -> synth_case k1 v1)), consumed)
                               | uu___ -> FStar_Pervasives_Native.None in
                             match pcases2 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some (x, consumed_x)
                                 ->
                                 FStar_Pervasives_Native.Some
                                   (x,
                                     (FStar_UInt32.add consumed_k consumed_x)))
                          k
type ('t, 'pc, 'sc, 'k) serialize32_sum_cases_t =
  Obj.t -> LowParse_SLow_Base.bytes32
type ('t, 'pc, 'sc, 'k, 'x, 'y) serialize32_sum_cases_t_eq = unit
let (serialize32_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        Obj.t ->
          Prims.bool ->
            (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
              (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun k ->
          fun cond ->
            fun sv_true ->
              fun sv_false ->
                fun input ->
                  if cond then sv_true () input else sv_false () input
let (serialize32_sum_cases_aux :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
          Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun sc32 ->
          fun k ->
            fun input ->
              let x =
                match t with
                | LowParse_Spec_Sum.Sum
                    (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
                     synth_case_recip, uu___7, uu___8)
                    -> synth_case_recip k input in
              sc32 k x
let (serialize32_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
          (unit ->
             (Obj.t ->
                Prims.bool ->
                  (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                    (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                      Obj.t -> LowParse_SLow_Base.bytes32)
               ->
               unit ->
                 unit ->
                   (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                     Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32)
            -> Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun sc32 ->
          fun destr ->
            fun k ->
              destr ()
                (fun k1 ->
                   fun cond ->
                     fun sv_true ->
                       fun sv_false ->
                         fun input ->
                           if cond
                           then sv_true () input
                           else sv_false () input) () ()
                (fun k1 ->
                   fun input ->
                     let x =
                       match t with
                       | LowParse_Spec_Sum.Sum
                           (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                            uu___6, synth_case_recip, uu___7, uu___8)
                           -> synth_case_recip k1 input in
                     sc32 k1 x) k

type ('t, 'k) serialize32_sum_destr_codom = Obj.t -> FStar_Bytes.bytes
type ('t, 'k, 'uuuuu, 'uuuuu1) serialize32_sum_destr_eq = unit

let (serialize32_sum_destr_if :
  LowParse_Spec_Sum.sum ->
    Obj.t ->
      Prims.bool ->
        (unit -> Obj.t -> FStar_Bytes.bytes) ->
          (unit -> Obj.t -> FStar_Bytes.bytes) -> Obj.t -> FStar_Bytes.bytes)
  =
  fun t ->
    fun k ->
      fun cond ->
        fun s_true ->
          fun s_false -> fun x -> if cond then s_true () x else s_false () x
let (serialize32_sum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit -> Obj.t -> FStar_Bytes.bytes) ->
                            (unit -> Obj.t -> FStar_Bytes.bytes) ->
                              Obj.t -> FStar_Bytes.bytes)
                       ->
                       unit ->
                         unit ->
                           (Obj.t -> Obj.t -> FStar_Bytes.bytes) ->
                             Obj.t -> Obj.t -> FStar_Bytes.bytes)
                    -> unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun pc ->
              fun sc ->
                fun sc32 ->
                  fun destr ->
                    fun u ->
                      fun x ->
                        let tg =
                          match t with
                          | LowParse_Spec_Sum.Sum
                              (uu___, uu___1, uu___2, uu___3, tag_of_data,
                               uu___4, uu___5, uu___6, uu___7, uu___8)
                              -> tag_of_data x in
                        let s1 = s32 tg in
                        let s2 =
                          destr ()
                            (fun k ->
                               fun cond ->
                                 fun s_true ->
                                   fun s_false ->
                                     fun x1 ->
                                       if cond
                                       then s_true () x1
                                       else s_false () x1) () ()
                            (fun tg1 ->
                               fun x1 ->
                                 sc32 tg1
                                   (match t with
                                    | LowParse_Spec_Sum.Sum
                                        (uu___, uu___1, uu___2, uu___3,
                                         uu___4, uu___5, uu___6,
                                         synth_case_recip, uu___7, uu___8)
                                        -> synth_case_recip tg1 x1)) tg x in
                        let res = FStar_Bytes.append s1 s2 in res
let (serialize32_sum2 :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit -> Obj.t -> FStar_Bytes.bytes) ->
                            (unit -> Obj.t -> FStar_Bytes.bytes) ->
                              Obj.t -> FStar_Bytes.bytes)
                       ->
                       unit ->
                         unit ->
                           (Obj.t -> Obj.t -> FStar_Bytes.bytes) ->
                             Obj.t -> Obj.t -> FStar_Bytes.bytes)
                    ->
                    (Obj.t, Obj.t, unit)
                      LowParse_Spec_Enum.enum_repr_of_key'_t ->
                      unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun pc ->
              fun sc ->
                fun sc32 ->
                  fun destr ->
                    fun f ->
                      fun u ->
                        fun x ->
                          let tg =
                            match t with
                            | LowParse_Spec_Sum.Sum
                                (uu___, uu___1, uu___2, uu___3, tag_of_data,
                                 uu___4, uu___5, uu___6, uu___7, uu___8)
                                -> tag_of_data x in
                          let s1 = s32 (f tg) in
                          let s2 =
                            destr ()
                              (fun k ->
                                 fun cond ->
                                   fun s_true ->
                                     fun s_false ->
                                       fun x1 ->
                                         if cond
                                         then s_true () x1
                                         else s_false () x1) () ()
                              (fun tg1 ->
                                 fun x1 ->
                                   sc32 tg1
                                     (match t with
                                      | LowParse_Spec_Sum.Sum
                                          (uu___, uu___1, uu___2, uu___3,
                                           uu___4, uu___5, uu___6,
                                           synth_case_recip, uu___7, uu___8)
                                          -> synth_case_recip tg1 x1)) tg x in
                          let res = FStar_Bytes.append s1 s2 in res
type ('t, 'pc, 'sc, 'k) size32_sum_cases_t = Obj.t -> FStar_UInt32.t
type ('t, 'pc, 'sc, 'k, 'x, 'y) size32_sum_cases_t_eq = unit
let (size32_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        Obj.t ->
          Prims.bool ->
            (unit -> Obj.t -> FStar_UInt32.t) ->
              (unit -> Obj.t -> FStar_UInt32.t) -> Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun k ->
          fun cond ->
            fun sv_true ->
              fun sv_false ->
                fun input ->
                  if cond then sv_true () input else sv_false () input
let (size32_sum_cases_aux :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> FStar_UInt32.t) ->
          Obj.t -> Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun sc32 ->
          fun k ->
            fun input ->
              sc32 k
                (match t with
                 | LowParse_Spec_Sum.Sum
                     (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
                      synth_case_recip, uu___7, uu___8)
                     -> synth_case_recip k input)
let (size32_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> FStar_UInt32.t) ->
          (unit ->
             (Obj.t ->
                Prims.bool ->
                  (unit -> Obj.t -> FStar_UInt32.t) ->
                    (unit -> Obj.t -> FStar_UInt32.t) ->
                      Obj.t -> FStar_UInt32.t)
               ->
               unit ->
                 unit ->
                   (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                     Obj.t -> Obj.t -> FStar_UInt32.t)
            -> Obj.t -> Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun sc32 ->
          fun destr ->
            fun k ->
              destr ()
                (fun k1 ->
                   fun cond ->
                     fun sv_true ->
                       fun sv_false ->
                         fun input ->
                           if cond
                           then sv_true () input
                           else sv_false () input) () ()
                (fun k1 ->
                   fun input ->
                     sc32 k1
                       (match t with
                        | LowParse_Spec_Sum.Sum
                            (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                             uu___6, synth_case_recip, uu___7, uu___8)
                            -> synth_case_recip k1 input)) k
type ('t, 'k) size32_sum_destr_codom = Obj.t -> FStar_UInt32.t
type ('t, 'k, 'uuuuu, 'uuuuu1) size32_sum_destr_eq = unit

let (size32_sum_destr_if :
  LowParse_Spec_Sum.sum ->
    Obj.t ->
      Prims.bool ->
        (unit -> Obj.t -> FStar_UInt32.t) ->
          (unit -> Obj.t -> FStar_UInt32.t) -> Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun k ->
      fun cond ->
        fun s_true ->
          fun s_false -> fun x -> if cond then s_true () x else s_false () x
type ('kt, 'k) size32_sum_gen_precond = unit
let (size32_sum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit -> Obj.t -> FStar_UInt32.t) ->
                            (unit -> Obj.t -> FStar_UInt32.t) ->
                              Obj.t -> FStar_UInt32.t)
                       ->
                       unit ->
                         unit ->
                           (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                             Obj.t -> Obj.t -> FStar_UInt32.t)
                    -> unit -> Obj.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun pc ->
              fun sc ->
                fun sc32 ->
                  fun destr ->
                    fun u ->
                      fun x ->
                        let tg =
                          match t with
                          | LowParse_Spec_Sum.Sum
                              (uu___, uu___1, uu___2, uu___3, tag_of_data,
                               uu___4, uu___5, uu___6, uu___7, uu___8)
                              -> tag_of_data x in
                        let s1 = s32 tg in
                        let s2 =
                          destr ()
                            (fun k ->
                               fun cond ->
                                 fun s_true ->
                                   fun s_false ->
                                     fun x1 ->
                                       if cond
                                       then s_true () x1
                                       else s_false () x1) () ()
                            (fun tg1 ->
                               fun x1 ->
                                 sc32 tg1
                                   (match t with
                                    | LowParse_Spec_Sum.Sum
                                        (uu___, uu___1, uu___2, uu___3,
                                         uu___4, uu___5, uu___6,
                                         synth_case_recip, uu___7, uu___8)
                                        -> synth_case_recip tg1 x1)) tg x in
                        FStar_UInt32.add s1 s2
let (size32_sum2 :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit -> Obj.t -> FStar_UInt32.t) ->
                            (unit -> Obj.t -> FStar_UInt32.t) ->
                              Obj.t -> FStar_UInt32.t)
                       ->
                       unit ->
                         unit ->
                           (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                             Obj.t -> Obj.t -> FStar_UInt32.t)
                    ->
                    (Obj.t, Obj.t, unit)
                      LowParse_Spec_Enum.enum_repr_of_key'_t ->
                      unit -> Obj.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun pc ->
              fun sc ->
                fun sc32 ->
                  fun destr ->
                    fun f ->
                      fun u ->
                        fun x ->
                          let tg =
                            match t with
                            | LowParse_Spec_Sum.Sum
                                (uu___, uu___1, uu___2, uu___3, tag_of_data,
                                 uu___4, uu___5, uu___6, uu___7, uu___8)
                                -> tag_of_data x in
                          let s1 = s32 (f tg) in
                          let s2 =
                            destr ()
                              (fun k ->
                                 fun cond ->
                                   fun s_true ->
                                     fun s_false ->
                                       fun x1 ->
                                         if cond
                                         then s_true () x1
                                         else s_false () x1) () ()
                              (fun tg1 ->
                                 fun x1 ->
                                   sc32 tg1
                                     (match t with
                                      | LowParse_Spec_Sum.Sum
                                          (uu___, uu___1, uu___2, uu___3,
                                           uu___4, uu___5, uu___6,
                                           synth_case_recip, uu___7, uu___8)
                                          -> synth_case_recip tg1 x1)) tg x in
                          FStar_UInt32.add s1 s2
let (parse32_dsum_cases' :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun f ->
      fun f32 ->
        fun k' ->
          fun g ->
            fun g32 ->
              fun x ->
                match x with
                | LowParse_Spec_Enum.Known x' ->
                    (fun input ->
                       match f32 x' input with
                       | FStar_Pervasives_Native.Some (v1, consumed) ->
                           FStar_Pervasives_Native.Some
                             ((((match t with
                                 | LowParse_Spec_Sum.DSum
                                     (uu___, uu___1, uu___2, uu___3, uu___4,
                                      uu___5, uu___6, synth_case, uu___7,
                                      uu___8, uu___9)
                                     -> synth_case))
                                 (LowParse_Spec_Enum.Known x') v1), consumed)
                       | uu___ -> FStar_Pervasives_Native.None)
                | LowParse_Spec_Enum.Unknown x' ->
                    (fun input ->
                       match g32 input with
                       | FStar_Pervasives_Native.Some (v1, consumed) ->
                           FStar_Pervasives_Native.Some
                             ((((match t with
                                 | LowParse_Spec_Sum.DSum
                                     (uu___, uu___1, uu___2, uu___3, uu___4,
                                      uu___5, uu___6, synth_case, uu___7,
                                      uu___8, uu___9)
                                     -> synth_case))
                                 (LowParse_Spec_Enum.Unknown x') v1),
                               consumed)
                       | uu___ -> FStar_Pervasives_Native.None)
let (parse32_dsum_cases_aux :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun f ->
      fun f32 ->
        fun k' ->
          fun g ->
            fun g32 ->
              fun x ->
                fun input ->
                  match x with
                  | LowParse_Spec_Enum.Known x' ->
                      (match f32 x' input with
                       | FStar_Pervasives_Native.Some (v1, consumed) ->
                           FStar_Pervasives_Native.Some
                             ((((match t with
                                 | LowParse_Spec_Sum.DSum
                                     (uu___, uu___1, uu___2, uu___3, uu___4,
                                      uu___5, uu___6, synth_case, uu___7,
                                      uu___8, uu___9)
                                     -> synth_case))
                                 (LowParse_Spec_Enum.Known x') v1), consumed)
                       | uu___ -> FStar_Pervasives_Native.None)
                  | LowParse_Spec_Enum.Unknown x' ->
                      (match g32 input with
                       | FStar_Pervasives_Native.Some (v1, consumed) ->
                           FStar_Pervasives_Native.Some
                             ((((match t with
                                 | LowParse_Spec_Sum.DSum
                                     (uu___, uu___1, uu___2, uu___3, uu___4,
                                      uu___5, uu___6, synth_case, uu___7,
                                      uu___8, uu___9)
                                     -> synth_case))
                                 (LowParse_Spec_Enum.Unknown x') v1),
                               consumed)
                       | uu___ -> FStar_Pervasives_Native.None)
type ('t, 'f, 'ku, 'g, 'k) parse32_dsum_cases_t =
  LowParse_SLow_Base.bytes32 ->
    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option
type ('t, 'f, 'ku, 'g, 'k, 'x, 'y) parse32_dsum_cases_t_eq = unit
let (parse32_dsum_cases_t_if :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          Obj.t ->
            Prims.bool ->
              (unit ->
                 LowParse_SLow_Base.bytes32 ->
                   (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                ->
                (unit ->
                   LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                  ->
                  LowParse_SLow_Base.bytes32 ->
                    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun f ->
      fun k' ->
        fun g ->
          fun k ->
            fun cond ->
              fun sv_true ->
                fun sv_false ->
                  fun input ->
                    if cond then sv_true () input else sv_false () input
let (parse32_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              (unit ->
                 (Obj.t ->
                    Prims.bool ->
                      (unit ->
                         LowParse_SLow_Base.bytes32 ->
                           (Obj.t * FStar_UInt32.t)
                             FStar_Pervasives_Native.option)
                        ->
                        (unit ->
                           LowParse_SLow_Base.bytes32 ->
                             (Obj.t * FStar_UInt32.t)
                               FStar_Pervasives_Native.option)
                          ->
                          LowParse_SLow_Base.bytes32 ->
                            (Obj.t * FStar_UInt32.t)
                              FStar_Pervasives_Native.option)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          LowParse_SLow_Base.bytes32 ->
                            (Obj.t * FStar_UInt32.t)
                              FStar_Pervasives_Native.option)
                         ->
                         Obj.t ->
                           LowParse_SLow_Base.bytes32 ->
                             (Obj.t * FStar_UInt32.t)
                               FStar_Pervasives_Native.option)
                ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  LowParse_SLow_Base.bytes32 ->
                    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun t ->
    fun f ->
      fun f32 ->
        fun k' ->
          fun g ->
            fun g32 ->
              fun destr ->
                fun x ->
                  fun input ->
                    match x with
                    | LowParse_Spec_Enum.Known k ->
                        destr ()
                          (fun k1 ->
                             fun cond ->
                               fun sv_true ->
                                 fun sv_false ->
                                   fun input1 ->
                                     if cond
                                     then sv_true () input1
                                     else sv_false () input1) () ()
                          (fun k1 ->
                             fun input1 ->
                               match f32 k1 input1 with
                               | FStar_Pervasives_Native.Some (v1, consumed)
                                   ->
                                   FStar_Pervasives_Native.Some
                                     ((((match t with
                                         | LowParse_Spec_Sum.DSum
                                             (uu___, uu___1, uu___2, uu___3,
                                              uu___4, uu___5, uu___6,
                                              synth_case, uu___7, uu___8,
                                              uu___9)
                                             -> synth_case))
                                         (LowParse_Spec_Enum.Known k1) v1),
                                       consumed)
                               | uu___ -> FStar_Pervasives_Native.None) k
                          input
                    | LowParse_Spec_Enum.Unknown r ->
                        (match g32 input with
                         | FStar_Pervasives_Native.Some (v1, consumed) ->
                             FStar_Pervasives_Native.Some
                               ((((match t with
                                   | LowParse_Spec_Sum.DSum
                                       (uu___, uu___1, uu___2, uu___3,
                                        uu___4, uu___5, uu___6, synth_case,
                                        uu___7, uu___8, uu___9)
                                       -> synth_case))
                                   (LowParse_Spec_Enum.Unknown r) v1),
                                 consumed)
                         | uu___ -> FStar_Pervasives_Native.None)

let (parse32_dsum' :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            (Obj.t ->
               LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  (LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                    ->
                    (unit ->
                       (Prims.bool ->
                          (unit ->
                             (Obj.t * FStar_UInt32.t)
                               FStar_Pervasives_Native.option)
                            ->
                            (unit ->
                               (Obj.t * FStar_UInt32.t)
                                 FStar_Pervasives_Native.option)
                              ->
                              (Obj.t * FStar_UInt32.t)
                                FStar_Pervasives_Native.option)
                         ->
                         unit ->
                           unit ->
                             ((Obj.t, Obj.t, unit)
                                LowParse_Spec_Enum.maybe_enum_key ->
                                (Obj.t * FStar_UInt32.t)
                                  FStar_Pervasives_Native.option)
                               ->
                               Obj.t ->
                                 (Obj.t * FStar_UInt32.t)
                                   FStar_Pervasives_Native.option)
                      ->
                      FStar_Bytes.bytes ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun f ->
            fun f32 ->
              fun k' ->
                fun g ->
                  fun g32 ->
                    fun destr ->
                      fun input ->
                        let pi = p32 input in
                        match pi with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (k'1, consumed_k) ->
                            let input_k =
                              FStar_Bytes.slice input consumed_k
                                (FStar_Bytes.len input) in
                            destr ()
                              (fun cond ->
                                 fun s_true ->
                                   fun s_false ->
                                     if cond then s_true () else s_false ())
                              () ()
                              (fun k ->
                                 let pcases4 =
                                   match k with
                                   | LowParse_Spec_Enum.Known x' ->
                                       (match f32 x' input_k with
                                        | FStar_Pervasives_Native.Some
                                            (v1, consumed) ->
                                            FStar_Pervasives_Native.Some
                                              ((((match t with
                                                  | LowParse_Spec_Sum.DSum
                                                      (uu___, uu___1, uu___2,
                                                       uu___3, uu___4,
                                                       uu___5, uu___6,
                                                       synth_case, uu___7,
                                                       uu___8, uu___9)
                                                      -> synth_case))
                                                  (LowParse_Spec_Enum.Known
                                                     x') v1), consumed)
                                        | uu___ ->
                                            FStar_Pervasives_Native.None)
                                   | LowParse_Spec_Enum.Unknown x' ->
                                       (match g32 input_k with
                                        | FStar_Pervasives_Native.Some
                                            (v1, consumed) ->
                                            FStar_Pervasives_Native.Some
                                              ((((match t with
                                                  | LowParse_Spec_Sum.DSum
                                                      (uu___, uu___1, uu___2,
                                                       uu___3, uu___4,
                                                       uu___5, uu___6,
                                                       synth_case, uu___7,
                                                       uu___8, uu___9)
                                                      -> synth_case))
                                                  (LowParse_Spec_Enum.Unknown
                                                     x') v1), consumed)
                                        | uu___ ->
                                            FStar_Pervasives_Native.None) in
                                 match pcases4 with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some
                                     (x, consumed_x) ->
                                     FStar_Pervasives_Native.Some
                                       (x,
                                         (FStar_UInt32.add consumed_k
                                            consumed_x))) k'1
let (parse32_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            (Obj.t ->
               LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  (LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                    ->
                    (unit ->
                       (Prims.bool ->
                          (unit ->
                             (Obj.t * FStar_UInt32.t)
                               FStar_Pervasives_Native.option)
                            ->
                            (unit ->
                               (Obj.t * FStar_UInt32.t)
                                 FStar_Pervasives_Native.option)
                              ->
                              (Obj.t * FStar_UInt32.t)
                                FStar_Pervasives_Native.option)
                         ->
                         unit ->
                           unit ->
                             ((Obj.t, Obj.t, unit)
                                LowParse_Spec_Enum.maybe_enum_key ->
                                (Obj.t * FStar_UInt32.t)
                                  FStar_Pervasives_Native.option)
                               ->
                               Obj.t ->
                                 (Obj.t * FStar_UInt32.t)
                                   FStar_Pervasives_Native.option)
                      ->
                      LowParse_SLow_Base.bytes32 ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun f ->
            fun f32 ->
              fun k' ->
                fun g ->
                  fun g32 ->
                    fun destr ->
                      fun input ->
                        let pi = p32 input in
                        match pi with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (k'1, consumed_k) ->
                            let input_k =
                              FStar_Bytes.slice input consumed_k
                                (FStar_Bytes.len input) in
                            destr ()
                              (fun cond ->
                                 fun s_true ->
                                   fun s_false ->
                                     if cond then s_true () else s_false ())
                              () ()
                              (fun k ->
                                 let pcases4 =
                                   match k with
                                   | LowParse_Spec_Enum.Known x' ->
                                       (match f32 x' input_k with
                                        | FStar_Pervasives_Native.Some
                                            (v1, consumed) ->
                                            FStar_Pervasives_Native.Some
                                              ((((match t with
                                                  | LowParse_Spec_Sum.DSum
                                                      (uu___, uu___1, uu___2,
                                                       uu___3, uu___4,
                                                       uu___5, uu___6,
                                                       synth_case, uu___7,
                                                       uu___8, uu___9)
                                                      -> synth_case))
                                                  (LowParse_Spec_Enum.Known
                                                     x') v1), consumed)
                                        | uu___ ->
                                            FStar_Pervasives_Native.None)
                                   | LowParse_Spec_Enum.Unknown x' ->
                                       (match g32 input_k with
                                        | FStar_Pervasives_Native.Some
                                            (v1, consumed) ->
                                            FStar_Pervasives_Native.Some
                                              ((((match t with
                                                  | LowParse_Spec_Sum.DSum
                                                      (uu___, uu___1, uu___2,
                                                       uu___3, uu___4,
                                                       uu___5, uu___6,
                                                       synth_case, uu___7,
                                                       uu___8, uu___9)
                                                      -> synth_case))
                                                  (LowParse_Spec_Enum.Unknown
                                                     x') v1), consumed)
                                        | uu___ ->
                                            FStar_Pervasives_Native.None) in
                                 match pcases4 with
                                 | FStar_Pervasives_Native.None ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some
                                     (x, consumed_x) ->
                                     FStar_Pervasives_Native.Some
                                       (x,
                                         (FStar_UInt32.add consumed_k
                                            consumed_x))) k'1
let (serialize32_dsum_type_of_tag :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t -> LowParse_SLow_Base.bytes32) ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun sf32 ->
          fun k' ->
            fun g ->
              fun sg ->
                fun sg32 ->
                  fun tg ->
                    match tg with
                    | LowParse_Spec_Enum.Known x' ->
                        (fun input -> sf32 x' input)
                    | LowParse_Spec_Enum.Unknown x' ->
                        (fun input -> sg32 input)
let (serialize32_dsum_cases_aux :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t -> LowParse_SLow_Base.bytes32) ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun sf32 ->
          fun k' ->
            fun g ->
              fun sg ->
                fun sg32 ->
                  fun tg ->
                    fun input ->
                      let x =
                        match t with
                        | LowParse_Spec_Sum.DSum
                            (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                             uu___6, uu___7, synth_case_recip, uu___8,
                             uu___9)
                            -> synth_case_recip tg input in
                      match tg with
                      | LowParse_Spec_Enum.Known x' -> sf32 x' x
                      | LowParse_Spec_Enum.Unknown x' -> sg32 x
type ('t, 'f, 'sf, 'ku, 'g, 'sg, 'k) serialize32_dsum_cases_t =
  Obj.t -> LowParse_SLow_Base.bytes32
type ('t, 'f, 'sf, 'ku, 'g, 'sg, 'k, 'x, 'y) serialize32_dsum_cases_t_eq =
  unit
let (serialize32_dsum_cases_t_if :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              Obj.t ->
                Prims.bool ->
                  (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                    (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                      Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun k' ->
          fun g ->
            fun sg ->
              fun k ->
                fun cond ->
                  fun sv_true ->
                    fun sv_false ->
                      fun input ->
                        if cond then sv_true () input else sv_false () input
let (serialize32_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t -> LowParse_SLow_Base.bytes32) ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                            (unit -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                              Obj.t -> LowParse_SLow_Base.bytes32)
                       ->
                       unit ->
                         unit ->
                           (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                             Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32)
                    ->
                    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun sf32 ->
          fun k' ->
            fun g ->
              fun sg ->
                fun sg32 ->
                  fun destr ->
                    fun tg ->
                      fun input ->
                        match tg with
                        | LowParse_Spec_Enum.Known k ->
                            destr ()
                              (fun k1 ->
                                 fun cond ->
                                   fun sv_true ->
                                     fun sv_false ->
                                       fun input1 ->
                                         if cond
                                         then sv_true () input1
                                         else sv_false () input1) () ()
                              (fun k1 ->
                                 fun input1 ->
                                   let x =
                                     (match t with
                                      | LowParse_Spec_Sum.DSum
                                          (uu___, uu___1, uu___2, uu___3,
                                           uu___4, uu___5, uu___6, uu___7,
                                           synth_case_recip, uu___8, uu___9)
                                          -> synth_case_recip)
                                       (LowParse_Spec_Enum.Known k1) input1 in
                                   sf32 k1 x) k input
                        | LowParse_Spec_Enum.Unknown r ->
                            let x =
                              (match t with
                               | LowParse_Spec_Sum.DSum
                                   (uu___, uu___1, uu___2, uu___3, uu___4,
                                    uu___5, uu___6, uu___7, synth_case_recip,
                                    uu___8, uu___9)
                                   -> synth_case_recip)
                                (LowParse_Spec_Enum.Unknown r) input in
                            sg32 x
type ('t, 'k) serialize32_dsum_known_destr_codom = Obj.t -> FStar_Bytes.bytes
type ('t, 'k, 'uuuuu, 'uuuuu1) serialize32_dsum_known_destr_eq = unit

let (serialize32_dsum_known_destr_if :
  LowParse_Spec_Sum.dsum ->
    Obj.t ->
      Prims.bool ->
        (unit -> Obj.t -> FStar_Bytes.bytes) ->
          (unit -> Obj.t -> FStar_Bytes.bytes) -> Obj.t -> FStar_Bytes.bytes)
  =
  fun t ->
    fun k ->
      fun cond ->
        fun s_true ->
          fun s_false -> fun x -> if cond then s_true () x else s_false () x
let (serialize32_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        unit ->
          ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
             LowParse_SLow_Base.bytes32)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                  LowParse_Spec_Base.parser_kind ->
                    unit ->
                      unit ->
                        (Obj.t -> LowParse_SLow_Base.bytes32) ->
                          (unit ->
                             (Obj.t ->
                                Prims.bool ->
                                  (unit -> Obj.t -> FStar_Bytes.bytes) ->
                                    (unit -> Obj.t -> FStar_Bytes.bytes) ->
                                      Obj.t -> FStar_Bytes.bytes)
                               ->
                               unit ->
                                 unit ->
                                   (Obj.t -> Obj.t -> FStar_Bytes.bytes) ->
                                     Obj.t -> Obj.t -> FStar_Bytes.bytes)
                            -> unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun f ->
              fun sf ->
                fun sf32 ->
                  fun k' ->
                    fun g ->
                      fun sg ->
                        fun sg32 ->
                          fun destr ->
                            fun u ->
                              fun x ->
                                let tg =
                                  match t with
                                  | LowParse_Spec_Sum.DSum
                                      (uu___, uu___1, uu___2, uu___3,
                                       tag_of_data, uu___4, uu___5, uu___6,
                                       uu___7, uu___8, uu___9)
                                      -> tag_of_data x in
                                let s1 = s32 tg in
                                let s2 =
                                  match tg with
                                  | LowParse_Spec_Enum.Known tg' ->
                                      destr ()
                                        (fun k ->
                                           fun cond ->
                                             fun s_true ->
                                               fun s_false ->
                                                 fun x1 ->
                                                   if cond
                                                   then s_true () x1
                                                   else s_false () x1) () ()
                                        (fun tg_ ->
                                           fun input ->
                                             let x1 =
                                               (match t with
                                                | LowParse_Spec_Sum.DSum
                                                    (uu___, uu___1, uu___2,
                                                     uu___3, uu___4, uu___5,
                                                     uu___6, uu___7,
                                                     synth_case_recip,
                                                     uu___8, uu___9)
                                                    -> synth_case_recip)
                                                 (LowParse_Spec_Enum.Known
                                                    tg_) input in
                                             sf32 tg_ x1) tg' x
                                  | LowParse_Spec_Enum.Unknown tg' ->
                                      let x1 =
                                        (match t with
                                         | LowParse_Spec_Sum.DSum
                                             (uu___, uu___1, uu___2, uu___3,
                                              uu___4, uu___5, uu___6, uu___7,
                                              synth_case_recip, uu___8,
                                              uu___9)
                                             -> synth_case_recip)
                                          (LowParse_Spec_Enum.Unknown tg') x in
                                      sg32 x1 in
                                let res = FStar_Bytes.append s1 s2 in res
let (size32_dsum_type_of_tag :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> FStar_UInt32.t) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t -> FStar_UInt32.t) ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun sf32 ->
          fun k' ->
            fun g ->
              fun sg ->
                fun sg32 ->
                  fun tg ->
                    match tg with
                    | LowParse_Spec_Enum.Known x' ->
                        (fun input -> sf32 x' input)
                    | LowParse_Spec_Enum.Unknown x' ->
                        (fun input -> sg32 input)
let (size32_dsum_cases_aux :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> FStar_UInt32.t) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t -> FStar_UInt32.t) ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun sf32 ->
          fun k' ->
            fun g ->
              fun sg ->
                fun sg32 ->
                  fun tg ->
                    fun input ->
                      (match tg with
                       | LowParse_Spec_Enum.Known x' ->
                           (fun input1 -> sf32 x' input1)
                       | LowParse_Spec_Enum.Unknown x' ->
                           (fun input1 -> sg32 input1))
                        (match t with
                         | LowParse_Spec_Sum.DSum
                             (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                              uu___6, uu___7, synth_case_recip, uu___8,
                              uu___9)
                             -> synth_case_recip tg input)
type ('t, 'f, 'sf, 'ku, 'g, 'sg, 'k) size32_dsum_cases_t =
  Obj.t -> FStar_UInt32.t
type ('t, 'f, 'sf, 'ku, 'g, 'sg, 'k, 'x, 'y) size32_dsum_cases_t_eq = unit
let (size32_dsum_cases_t_if :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              Obj.t ->
                Prims.bool ->
                  (unit -> Obj.t -> FStar_UInt32.t) ->
                    (unit -> Obj.t -> FStar_UInt32.t) ->
                      Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun k' ->
          fun g ->
            fun sg ->
              fun k ->
                fun cond ->
                  fun sv_true ->
                    fun sv_false ->
                      fun input ->
                        if cond then sv_true () input else sv_false () input
let (size32_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t -> Obj.t -> FStar_UInt32.t) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t -> FStar_UInt32.t) ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit -> Obj.t -> FStar_UInt32.t) ->
                            (unit -> Obj.t -> FStar_UInt32.t) ->
                              Obj.t -> FStar_UInt32.t)
                       ->
                       unit ->
                         unit ->
                           (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                             Obj.t -> Obj.t -> FStar_UInt32.t)
                    ->
                    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun f ->
      fun sf ->
        fun sf32 ->
          fun k' ->
            fun g ->
              fun sg ->
                fun sg32 ->
                  fun destr ->
                    fun tg ->
                      fun input ->
                        match tg with
                        | LowParse_Spec_Enum.Known k ->
                            destr ()
                              (fun k1 ->
                                 fun cond ->
                                   fun sv_true ->
                                     fun sv_false ->
                                       fun input1 ->
                                         if cond
                                         then sv_true () input1
                                         else sv_false () input1) () ()
                              (fun k1 ->
                                 fun input1 ->
                                   sf32 k1
                                     ((match t with
                                       | LowParse_Spec_Sum.DSum
                                           (uu___, uu___1, uu___2, uu___3,
                                            uu___4, uu___5, uu___6, uu___7,
                                            synth_case_recip, uu___8, uu___9)
                                           -> synth_case_recip)
                                        (LowParse_Spec_Enum.Known k1) input1))
                              k input
                        | LowParse_Spec_Enum.Unknown r ->
                            sg32
                              ((match t with
                                | LowParse_Spec_Sum.DSum
                                    (uu___, uu___1, uu___2, uu___3, uu___4,
                                     uu___5, uu___6, uu___7,
                                     synth_case_recip, uu___8, uu___9)
                                    -> synth_case_recip)
                                 (LowParse_Spec_Enum.Unknown r) input)
type ('t, 'k) size32_dsum_known_destr_codom = Obj.t -> FStar_UInt32.t
type ('t, 'k, 'uuuuu, 'uuuuu1) size32_dsum_known_destr_eq = unit

let (size32_dsum_known_destr_if :
  LowParse_Spec_Sum.dsum ->
    Obj.t ->
      Prims.bool ->
        (unit -> Obj.t -> FStar_UInt32.t) ->
          (unit -> Obj.t -> FStar_UInt32.t) -> Obj.t -> FStar_UInt32.t)
  =
  fun t ->
    fun k ->
      fun cond ->
        fun s_true ->
          fun s_false -> fun x -> if cond then s_true () x else s_false () x
let (size32_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        unit ->
          ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
             FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                  LowParse_Spec_Base.parser_kind ->
                    unit ->
                      unit ->
                        (Obj.t -> FStar_UInt32.t) ->
                          (unit ->
                             (Obj.t ->
                                Prims.bool ->
                                  (unit -> Obj.t -> FStar_UInt32.t) ->
                                    (unit -> Obj.t -> FStar_UInt32.t) ->
                                      Obj.t -> FStar_UInt32.t)
                               ->
                               unit ->
                                 unit ->
                                   (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                                     Obj.t -> Obj.t -> FStar_UInt32.t)
                            -> unit -> Obj.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun f ->
              fun sf ->
                fun sf32 ->
                  fun k' ->
                    fun g ->
                      fun sg ->
                        fun sg32 ->
                          fun destr ->
                            fun u ->
                              fun x ->
                                let tg =
                                  match t with
                                  | LowParse_Spec_Sum.DSum
                                      (uu___, uu___1, uu___2, uu___3,
                                       tag_of_data, uu___4, uu___5, uu___6,
                                       uu___7, uu___8, uu___9)
                                      -> tag_of_data x in
                                let s1 = s32 tg in
                                let s2 =
                                  match tg with
                                  | LowParse_Spec_Enum.Known tg' ->
                                      destr ()
                                        (fun k ->
                                           fun cond ->
                                             fun s_true ->
                                               fun s_false ->
                                                 fun x1 ->
                                                   if cond
                                                   then s_true () x1
                                                   else s_false () x1) () ()
                                        (fun tg_ ->
                                           fun input ->
                                             sf32 tg_
                                               ((match t with
                                                 | LowParse_Spec_Sum.DSum
                                                     (uu___, uu___1, uu___2,
                                                      uu___3, uu___4, uu___5,
                                                      uu___6, uu___7,
                                                      synth_case_recip,
                                                      uu___8, uu___9)
                                                     -> synth_case_recip)
                                                  (LowParse_Spec_Enum.Known
                                                     tg_) input)) tg' x
                                  | LowParse_Spec_Enum.Unknown tg' ->
                                      sg32
                                        ((match t with
                                          | LowParse_Spec_Sum.DSum
                                              (uu___, uu___1, uu___2, uu___3,
                                               uu___4, uu___5, uu___6,
                                               uu___7, synth_case_recip,
                                               uu___8, uu___9)
                                              -> synth_case_recip)
                                           (LowParse_Spec_Enum.Unknown tg') x) in
                                FStar_UInt32.add s1 s2