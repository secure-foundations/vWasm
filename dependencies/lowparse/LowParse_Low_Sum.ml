open Prims
let (validate_sum_cases_aux :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        Obj.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun vc ->
        fun k ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let h1 = FStar_HyperStack_ST.get () in vc k () () input pos
type ('t, 'pc, 'k) validate_sum_cases_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t
type ('t, 'pc, 'k, 'x, 'y) validate_sum_cases_t_eq = unit
let (validate_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      Obj.t ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun sv_true ->
            fun sv_false ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      if cond
                      then sv_true () () () input pos
                      else sv_false () () () input pos
let (validate_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        (unit ->
           (Obj.t ->
              Prims.bool ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt64.t -> FStar_UInt64.t)
                  ->
                  (unit ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
             ->
             unit ->
               unit ->
                 (Obj.t ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
                   ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
          ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun vc ->
        fun destr ->
          fun k ->
            destr ()
              (fun k1 ->
                 fun cond ->
                   fun sv_true ->
                     fun sv_false ->
                       fun rrel ->
                         fun rel ->
                           fun input ->
                             fun pos ->
                               if cond
                               then sv_true () () () input pos
                               else sv_false () () () input pos) () ()
              (fun k1 ->
                 fun rrel ->
                   fun rel ->
                     fun input ->
                       fun pos ->
                         let h = FStar_HyperStack_ST.get () in
                         let h1 = FStar_HyperStack_ST.get () in
                         vc k1 () () input pos) k
type ('t, 'pc, 'k) validate_sum_aux_payload_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t
type ('t, 'pc, 'k, 'uuuuu, 'uuuuu1) validate_sum_aux_payload_eq = unit
let (validate_sum_aux_payload_if' :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun ift ->
            fun iff ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      if cond
                      then ift () () () input pos
                      else iff () () () input pos
let (validate_sum_aux_payload_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun ift ->
            fun iff ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      if cond
                      then ift () () () input pos
                      else iff () () () input pos
let (validate_sum_aux :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun v ->
          fun p32 ->
            fun pc ->
              fun v_payload ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let len_after_tag = v () () input pos in
                        if LowParse_Low_ErrorCode.is_error len_after_tag
                        then len_after_tag
                        else
                          (let h1 = FStar_HyperStack_ST.get () in
                           let k' =
                             p32 () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           v_payload k' () () input len_after_tag)
let (validate_sum_aux_payload' :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun k ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  match k with
                  | LowParse_Spec_Enum.Known k1 -> pc32 k1 () () input pos
                  | uu___ -> LowParse_Low_ErrorCode.validator_error_generic
let (validate_sum_aux_payload :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        (unit ->
           ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
              Prims.bool ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt64.t -> FStar_UInt64.t)
                  ->
                  (unit ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
             ->
             unit ->
               unit ->
                 ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
                   ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
          ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun destr ->
          fun k ->
            destr ()
              (fun k1 ->
                 fun cond ->
                   fun ift ->
                     fun iff ->
                       fun rrel ->
                         fun rel ->
                           fun input ->
                             fun pos ->
                               if cond
                               then ift () () () input pos
                               else iff () () () input pos) () ()
              (fun k1 ->
                 fun rrel ->
                   fun rel ->
                     fun input ->
                       fun pos ->
                         match k1 with
                         | LowParse_Spec_Enum.Known k2 ->
                             pc32 k2 () () input pos
                         | uu___ ->
                             LowParse_Low_ErrorCode.validator_error_generic)
              k
let (validate_sum :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (unit ->
                   ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      Prims.bool ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                          ->
                          (unit ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt64.t -> FStar_UInt64.t)
                            ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt64.t -> FStar_UInt64.t)
                     ->
                     unit ->
                       unit ->
                         ((Obj.t, Obj.t, unit)
                            LowParse_Spec_Enum.maybe_enum_key ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt64.t -> FStar_UInt64.t)
                           ->
                           Obj.t ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt64.t -> FStar_UInt64.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun v ->
          fun p32 ->
            fun pc ->
              fun pc32 ->
                fun destr ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let len_after_tag = v () () input pos in
                          if LowParse_Low_ErrorCode.is_error len_after_tag
                          then len_after_tag
                          else
                            (let h1 = FStar_HyperStack_ST.get () in
                             let k' =
                               p32 () () input
                                 (FStar_Int_Cast.uint64_to_uint32 pos) in
                             destr ()
                               (fun k ->
                                  fun cond ->
                                    fun ift ->
                                      fun iff ->
                                        fun rrel1 ->
                                          fun rel1 ->
                                            fun input1 ->
                                              fun pos1 ->
                                                if cond
                                                then ift () () () input1 pos1
                                                else iff () () () input1 pos1)
                               () ()
                               (fun k ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          match k with
                                          | LowParse_Spec_Enum.Known k1 ->
                                              pc32 k1 () () input1 pos1
                                          | uu___1 ->
                                              LowParse_Low_ErrorCode.validator_error_generic)
                               k' () () input len_after_tag)

let (finalize_sum_case :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t, Obj.t, unit) LowParse_Spec_Enum.enum_repr_of_key'_t ->
                Obj.t ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> unit)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun s ->
          fun w ->
            fun pc ->
              fun destr ->
                fun k ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let pos1 =
                            let pos' =
                              let res = w (destr k) () () input pos in
                              let h = FStar_HyperStack_ST.get () in res in
                            let h = FStar_HyperStack_ST.get () in pos' in
                          let h = FStar_HyperStack_ST.get () in ()
let (jump_sum_cases_aux :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        Obj.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun vc ->
        fun k ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let h1 = FStar_HyperStack_ST.get () in vc k () () input pos
type ('t, 'pc, 'k) jump_sum_cases_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
type ('t, 'pc, 'k, 'x, 'y) jump_sum_cases_t_eq = unit
let (jump_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      Obj.t ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> FStar_UInt32.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun sv_true ->
            fun sv_false ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      if cond
                      then sv_true () () () input pos
                      else sv_false () () () input pos
let (jump_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        (unit ->
           (Obj.t ->
              Prims.bool ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  (unit ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
             ->
             unit ->
               unit ->
                 (Obj.t ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
                   ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
          ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun vc ->
        fun destr ->
          fun k ->
            destr ()
              (fun k1 ->
                 fun cond ->
                   fun sv_true ->
                     fun sv_false ->
                       fun rrel ->
                         fun rel ->
                           fun input ->
                             fun pos ->
                               if cond
                               then sv_true () () () input pos
                               else sv_false () () () input pos) () ()
              (fun k1 ->
                 fun rrel ->
                   fun rel ->
                     fun input ->
                       fun pos ->
                         let h = FStar_HyperStack_ST.get () in
                         let h1 = FStar_HyperStack_ST.get () in
                         vc k1 () () input pos) k
type ('t, 'pc, 'k) jump_sum_aux_payload_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
type ('t, 'pc, 'k, 'uuuuu, 'uuuuu1) jump_sum_aux_payload_eq = unit
let (jump_sum_aux_payload_if' :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> FStar_UInt32.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun ift ->
            fun iff ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      if cond
                      then ift () () () input pos
                      else iff () () () input pos
let (jump_sum_aux_payload_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> FStar_UInt32.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun ift ->
            fun iff ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      if cond
                      then ift () () () input pos
                      else iff () () () input pos




let (read_sum_tag :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
          ->
          (unit ->
             ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                Prims.bool ->
                  (unit -> unit -> Obj.t) ->
                    (unit -> unit -> Obj.t) -> unit -> Obj.t)
               ->
               unit ->
                 unit ->
                   ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      unit -> Obj.t)
                     -> Obj.t -> unit -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun p32 ->
          fun destr ->
            fun pc ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      let h1 = FStar_HyperStack_ST.get () in
                      let res =
                        let h2 = FStar_HyperStack_ST.get () in
                        p32 () () input pos in
                      destr ()
                        (fun k ->
                           fun cond ->
                             fun sv_true ->
                               fun sv_false ->
                                 fun sq ->
                                   if cond
                                   then sv_true () ()
                                   else sv_false () ()) () ()
                        (fun k ->
                           fun sq ->
                             match k with
                             | LowParse_Spec_Enum.Known k_ -> k_
                             | uu___ ->
                                 (match match t with
                                        | LowParse_Spec_Sum.Sum
                                            (uu___1, uu___2, e, uu___3,
                                             uu___4, uu___5, uu___6, uu___7,
                                             uu___8, uu___9)
                                            -> e
                                  with
                                  | (k_, uu___1)::uu___2 -> k_)) res ()
let (jump_sum_aux :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun v ->
          fun p32 ->
            fun pc ->
              fun v_payload ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let pos_after_tag = v () () input pos in
                        let k' = p32 () () input pos in
                        v_payload k' () () input pos_after_tag
let (jump_sum_aux_payload' :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun k ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  match k with
                  | LowParse_Spec_Enum.Known k1 -> pc32 k1 () () input pos
                  | uu___ -> FStar_UInt32.uint_to_t Prims.int_zero
let (jump_sum_aux_payload :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        (unit ->
           ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
              Prims.bool ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  (unit ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
             ->
             unit ->
               unit ->
                 ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
                   ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
          ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun destr ->
          fun k ->
            destr ()
              (fun k1 ->
                 fun cond ->
                   fun ift ->
                     fun iff ->
                       fun rrel ->
                         fun rel ->
                           fun input ->
                             fun pos ->
                               if cond
                               then ift () () () input pos
                               else iff () () () input pos) () ()
              (fun k1 ->
                 fun rrel ->
                   fun rel ->
                     fun input ->
                       fun pos ->
                         match k1 with
                         | LowParse_Spec_Enum.Known k2 ->
                             pc32 k2 () () input pos
                         | uu___ -> FStar_UInt32.uint_to_t Prims.int_zero) k
let (jump_sum :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
                (unit ->
                   ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      Prims.bool ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> FStar_UInt32.t)
                          ->
                          (unit ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt32.t -> FStar_UInt32.t)
                            ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt32.t -> FStar_UInt32.t)
                     ->
                     unit ->
                       unit ->
                         ((Obj.t, Obj.t, unit)
                            LowParse_Spec_Enum.maybe_enum_key ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt32.t -> FStar_UInt32.t)
                           ->
                           Obj.t ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun v ->
          fun p32 ->
            fun pc ->
              fun pc32 ->
                fun destr ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let pos_after_tag = v () () input pos in
                          let k' = p32 () () input pos in
                          destr ()
                            (fun k ->
                               fun cond ->
                                 fun ift ->
                                   fun iff ->
                                     fun rrel1 ->
                                       fun rel1 ->
                                         fun input1 ->
                                           fun pos1 ->
                                             if cond
                                             then ift () () () input1 pos1
                                             else iff () () () input1 pos1)
                            () ()
                            (fun k ->
                               fun rrel1 ->
                                 fun rel1 ->
                                   fun input1 ->
                                     fun pos1 ->
                                       match k with
                                       | LowParse_Spec_Enum.Known k1 ->
                                           pc32 k1 () () input1 pos1
                                       | uu___ ->
                                           FStar_UInt32.uint_to_t
                                             Prims.int_zero) k' () () input
                            pos_after_tag
let (read_sum_cases' :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
        ->
        Obj.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun pc ->
      fun pc32 ->
        fun k ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let res = pc32 k () () input pos in
                  match t with
                  | LowParse_Spec_Sum.Sum
                      (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                       synth_case, uu___6, uu___7, uu___8)
                      -> synth_case k res
type ('t, 'pc, 'k) read_sum_cases_t =
  unit ->
    unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t
type ('t, 'pc, 'k, 'x, 'y) read_sum_cases_t_eq = unit
let (read_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      Obj.t ->
        Prims.bool ->
          (unit ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> Obj.t)
            ->
            (unit ->
               unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt32.t -> Obj.t)
              ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun cond ->
          fun sv_true ->
            fun sv_false ->
              fun uu___ ->
                fun uu___1 ->
                  fun input ->
                    fun pos ->
                      if cond
                      then sv_true () () () input pos
                      else sv_false () () () input pos
let (read_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
        ->
        (unit ->
           (Obj.t ->
              Prims.bool ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> Obj.t)
                  ->
                  (unit ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> Obj.t)
                    ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> Obj.t)
             ->
             unit ->
               unit ->
                 (Obj.t ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> Obj.t)
                   ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> Obj.t)
          ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> Obj.t)
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
                       fun uu___ ->
                         fun uu___1 ->
                           fun input ->
                             fun pos ->
                               if cond
                               then sv_true () () () input pos
                               else sv_false () () () input pos) () ()
              (fun k1 ->
                 fun rrel ->
                   fun rel ->
                     fun input ->
                       fun pos ->
                         let h = FStar_HyperStack_ST.get () in
                         let res = pc32 k1 () () input pos in
                         match t with
                         | LowParse_Spec_Sum.Sum
                             (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                              synth_case, uu___6, uu___7, uu___8)
                             -> synth_case k1 res) k
let (read_sum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> Obj.t)
                ->
                (unit ->
                   (Obj.t ->
                      Prims.bool ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> Obj.t)
                          ->
                          (unit ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt32.t -> Obj.t)
                            ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt32.t -> Obj.t)
                     ->
                     unit ->
                       unit ->
                         (Obj.t ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt32.t -> Obj.t)
                           ->
                           Obj.t ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt32.t -> Obj.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> Obj.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun j ->
            fun pc ->
              fun pc32 ->
                fun destr ->
                  fun uu___ ->
                    fun uu___1 ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let k = p32 () () input pos in
                          let pos' =
                            let h1 = FStar_HyperStack_ST.get () in
                            let h2 = FStar_HyperStack_ST.get () in
                            j () () input pos in
                          destr ()
                            (fun k1 ->
                               fun cond ->
                                 fun sv_true ->
                                   fun sv_false ->
                                     fun uu___2 ->
                                       fun uu___3 ->
                                         fun input1 ->
                                           fun pos1 ->
                                             if cond
                                             then
                                               sv_true () () () input1 pos1
                                             else
                                               sv_false () () () input1 pos1)
                            () ()
                            (fun k1 ->
                               fun rrel ->
                                 fun rel ->
                                   fun input1 ->
                                     fun pos1 ->
                                       let h1 = FStar_HyperStack_ST.get () in
                                       let res = pc32 k1 () () input1 pos1 in
                                       match t with
                                       | LowParse_Spec_Sum.Sum
                                           (uu___2, uu___3, uu___4, uu___5,
                                            uu___6, uu___7, synth_case,
                                            uu___8, uu___9, uu___10)
                                           -> synth_case k1 res) k () ()
                            input pos'
type ('t, 'pc, 'sc, 'k) serialize32_sum_cases_t =
  Obj.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t
type ('t, 'pc, 'sc, 'k, 'x, 'y) serialize32_sum_cases_t_eq = unit
let (serialize32_sum_cases_t_if :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        Obj.t ->
          Prims.bool ->
            (unit ->
               Obj.t ->
                 unit ->
                   unit ->
                     (LowParse_Bytes.byte, Obj.t, Obj.t)
                       LowStar_Monotonic_Buffer.mbuffer ->
                       FStar_UInt32.t -> FStar_UInt32.t)
              ->
              (unit ->
                 Obj.t ->
                   unit ->
                     unit ->
                       (LowParse_Bytes.byte, Obj.t, Obj.t)
                         LowStar_Monotonic_Buffer.mbuffer ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                ->
                Obj.t ->
                  unit ->
                    unit ->
                      (LowParse_Bytes.byte, Obj.t, Obj.t)
                        LowStar_Monotonic_Buffer.mbuffer ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun k ->
          fun cond ->
            fun sv_true ->
              fun sv_false ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun b ->
                        fun pos ->
                          if cond
                          then sv_true () x () () b pos
                          else sv_false () x () () b pos
let (serialize32_sum_cases_aux :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t ->
           Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
          ->
          Obj.t ->
            Obj.t ->
              unit ->
                unit ->
                  (LowParse_Bytes.byte, Obj.t, Obj.t)
                    LowStar_Monotonic_Buffer.mbuffer ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun sc ->
        fun sc32 ->
          fun k ->
            fun x ->
              fun rrel ->
                fun rel ->
                  fun b ->
                    fun pos ->
                      sc32 k
                        (match t with
                         | LowParse_Spec_Sum.Sum
                             (uu___, uu___1, uu___2, uu___3, uu___4, uu___5,
                              uu___6, synth_case_recip, uu___7, uu___8)
                             -> synth_case_recip k x) () () b pos
let (serialize32_sum_cases :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t ->
           Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             (Obj.t ->
                Prims.bool ->
                  (unit ->
                     Obj.t ->
                       unit ->
                         unit ->
                           (LowParse_Bytes.byte, Obj.t, Obj.t)
                             LowStar_Monotonic_Buffer.mbuffer ->
                             FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    (unit ->
                       Obj.t ->
                         unit ->
                           unit ->
                             (LowParse_Bytes.byte, Obj.t, Obj.t)
                               LowStar_Monotonic_Buffer.mbuffer ->
                               FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
               ->
               unit ->
                 unit ->
                   (Obj.t ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
                     ->
                     Obj.t ->
                       Obj.t ->
                         unit ->
                           unit ->
                             (LowParse_Bytes.byte, Obj.t, Obj.t)
                               LowStar_Monotonic_Buffer.mbuffer ->
                               FStar_UInt32.t -> FStar_UInt32.t)
            ->
            Obj.t ->
              Obj.t ->
                unit ->
                  unit ->
                    (LowParse_Bytes.byte, Obj.t, Obj.t)
                      LowStar_Monotonic_Buffer.mbuffer ->
                      FStar_UInt32.t -> FStar_UInt32.t)
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
                         fun x ->
                           fun rrel ->
                             fun rel ->
                               fun b ->
                                 fun pos ->
                                   if cond
                                   then sv_true () x () () b pos
                                   else sv_false () x () () b pos) () ()
                (fun k1 ->
                   fun x ->
                     fun rrel ->
                       fun rel ->
                         fun b ->
                           fun pos ->
                             sc32 k1
                               (match t with
                                | LowParse_Spec_Sum.Sum
                                    (uu___, uu___1, uu___2, uu___3, uu___4,
                                     uu___5, uu___6, synth_case_recip,
                                     uu___7, uu___8)
                                    -> synth_case_recip k1 x) () () b pos) k
let (serialize32_sum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.sum ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (LowParse_Bytes.byte, Obj.t, Obj.t)
                           LowStar_Monotonic_Buffer.mbuffer ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit ->
                             Obj.t ->
                               unit ->
                                 unit ->
                                   (LowParse_Bytes.byte, Obj.t, Obj.t)
                                     LowStar_Monotonic_Buffer.mbuffer ->
                                     FStar_UInt32.t -> FStar_UInt32.t)
                            ->
                            (unit ->
                               Obj.t ->
                                 unit ->
                                   unit ->
                                     (LowParse_Bytes.byte, Obj.t, Obj.t)
                                       LowStar_Monotonic_Buffer.mbuffer ->
                                       FStar_UInt32.t -> FStar_UInt32.t)
                              ->
                              Obj.t ->
                                unit ->
                                  unit ->
                                    (LowParse_Bytes.byte, Obj.t, Obj.t)
                                      LowStar_Monotonic_Buffer.mbuffer ->
                                      FStar_UInt32.t -> FStar_UInt32.t)
                       ->
                       unit ->
                         unit ->
                           (Obj.t ->
                              Obj.t ->
                                unit ->
                                  unit ->
                                    (LowParse_Bytes.byte, Obj.t, Obj.t)
                                      LowStar_Monotonic_Buffer.mbuffer ->
                                      FStar_UInt32.t -> FStar_UInt32.t)
                             ->
                             Obj.t ->
                               Obj.t ->
                                 unit ->
                                   unit ->
                                     (LowParse_Bytes.byte, Obj.t, Obj.t)
                                       LowStar_Monotonic_Buffer.mbuffer ->
                                       FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    Obj.t ->
                      unit ->
                        unit ->
                          (LowParse_Bytes.byte, Obj.t, Obj.t)
                            LowStar_Monotonic_Buffer.mbuffer ->
                            FStar_UInt32.t -> FStar_UInt32.t)
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
                    fun x ->
                      fun rrel ->
                        fun rel ->
                          fun b ->
                            fun pos ->
                              let tg =
                                match t with
                                | LowParse_Spec_Sum.Sum
                                    (uu___, uu___1, uu___2, uu___3,
                                     tag_of_data, uu___4, uu___5, uu___6,
                                     uu___7, uu___8)
                                    -> tag_of_data x in
                              let len1 =
                                let h0 = FStar_HyperStack_ST.get () in
                                let res = s32 tg () () b pos in
                                let h1 = FStar_HyperStack_ST.get () in
                                let pos' = FStar_UInt32.add pos res in res in
                              let pos1 = FStar_UInt32.add pos len1 in
                              let len2 =
                                let h0 = FStar_HyperStack_ST.get () in
                                let res =
                                  destr ()
                                    (fun k ->
                                       fun cond ->
                                         fun sv_true ->
                                           fun sv_false ->
                                             fun x1 ->
                                               fun rrel1 ->
                                                 fun rel1 ->
                                                   fun b1 ->
                                                     fun pos2 ->
                                                       if cond
                                                       then
                                                         sv_true () x1 () ()
                                                           b1 pos2
                                                       else
                                                         sv_false () x1 () ()
                                                           b1 pos2) () ()
                                    (fun k ->
                                       fun x1 ->
                                         fun rrel1 ->
                                           fun rel1 ->
                                             fun b1 ->
                                               fun pos2 ->
                                                 sc32 k
                                                   (match t with
                                                    | LowParse_Spec_Sum.Sum
                                                        (uu___, uu___1,
                                                         uu___2, uu___3,
                                                         uu___4, uu___5,
                                                         uu___6,
                                                         synth_case_recip,
                                                         uu___7, uu___8)
                                                        ->
                                                        synth_case_recip k x1)
                                                   () () b1 pos2) tg x () ()
                                    b pos1 in
                                let h1 = FStar_HyperStack_ST.get () in
                                let pos' = FStar_UInt32.add pos1 res in res in
                              let h1 = FStar_HyperStack_ST.get () in
                              FStar_UInt32.add len1 len2
let (clens_sum_tag :
  LowParse_Spec_Sum.sum -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens) =
  fun s ->
    {
      LowParse_Low_Base_Spec.clens_cond = ();
      LowParse_Low_Base_Spec.clens_get = ()
    }

let (accessor_sum_tag :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun pc ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos -> let h = FStar_HyperStack_ST.get () in pos
let (clens_sum_payload :
  LowParse_Spec_Sum.sum ->
    Obj.t -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun s ->
    fun k ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }




let (accessor_clens_sum_payload' :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            Obj.t ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun j ->
          fun pc ->
            fun k ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in j () () input pos
let (accessor_clens_sum_payload :
  LowParse_Spec_Sum.sum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            Obj.t ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun j ->
          fun pc ->
            fun k ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in j () () input pos
let (clens_sum_cases_payload :
  LowParse_Spec_Sum.sum ->
    Obj.t -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun s ->
    fun k ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }

let (accessor_clens_sum_cases_payload :
  LowParse_Spec_Sum.sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      Obj.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun pc ->
      fun k ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h = FStar_HyperStack_ST.get () in
                let h1 = FStar_HyperStack_ST.get () in pos
type ('s, 'f, 'k, 'g, 'x) validate_dsum_cases_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t
type ('s, 'f, 'k, 'g, 'x, 'v1, 'v2) validate_dsum_cases_eq = unit
let (validate_dsum_cases_if' :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
            Prims.bool ->
              (unit ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt64.t -> FStar_UInt64.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun s ->
    fun f ->
      fun k ->
        fun g ->
          fun x ->
            fun cond ->
              fun ift ->
                fun iff ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun len ->
                          if cond
                          then ift () () () input len
                          else iff () () () input len
let (validate_dsum_cases_if :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
            Prims.bool ->
              (unit ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt64.t -> FStar_UInt64.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun s ->
    fun f ->
      fun k ->
        fun g ->
          fun x ->
            fun cond ->
              fun ift ->
                fun iff ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun len ->
                          if cond
                          then ift () () () input len
                          else iff () () () input len
let (validate_dsum_cases' :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun s ->
    fun f ->
      fun f' ->
        fun k ->
          fun g ->
            fun g' ->
              fun x ->
                match x with
                | LowParse_Spec_Enum.Known x' ->
                    (fun rrel ->
                       fun rel ->
                         fun input ->
                           fun pos ->
                             let h = FStar_HyperStack_ST.get () in
                             f' x' () () input pos)
                | LowParse_Spec_Enum.Unknown x' ->
                    (fun rrel ->
                       fun rel ->
                         fun input ->
                           fun pos ->
                             let h = FStar_HyperStack_ST.get () in
                             g' () () input pos)
let (validate_dsum_cases'_destr :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              (unit ->
                 (Obj.t ->
                    Prims.bool ->
                      (unit ->
                         unit ->
                           unit ->
                             (Obj.t, Obj.t) LowParse_Slice.slice ->
                               FStar_UInt64.t -> FStar_UInt64.t)
                        ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                          ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt64.t -> FStar_UInt64.t)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt64.t -> FStar_UInt64.t)
                         ->
                         Obj.t ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun s ->
    fun f ->
      fun f' ->
        fun k ->
          fun g ->
            fun g' ->
              fun destr ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          match x with
                          | LowParse_Spec_Enum.Known k1 ->
                              destr ()
                                (fun k2 ->
                                   fun cond ->
                                     fun ift ->
                                       fun iff ->
                                         fun rrel1 ->
                                           fun rel1 ->
                                             fun input1 ->
                                               fun len ->
                                                 if cond
                                                 then ift () () () input1 len
                                                 else iff () () () input1 len)
                                () ()
                                (fun k2 ->
                                   fun rrel1 ->
                                     fun rel1 ->
                                       fun input1 ->
                                         fun pos1 ->
                                           let h = FStar_HyperStack_ST.get () in
                                           f' k2 () () input1 pos1) k1 () ()
                                input pos
                          | LowParse_Spec_Enum.Unknown r ->
                              let h = FStar_HyperStack_ST.get () in
                              g' () () input pos
let (validate_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              (unit ->
                 (Obj.t ->
                    Prims.bool ->
                      (unit ->
                         unit ->
                           unit ->
                             (Obj.t, Obj.t) LowParse_Slice.slice ->
                               FStar_UInt64.t -> FStar_UInt64.t)
                        ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                          ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt64.t -> FStar_UInt64.t)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt64.t -> FStar_UInt64.t)
                         ->
                         Obj.t ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun s ->
    fun f ->
      fun f' ->
        fun k ->
          fun g ->
            fun g' ->
              fun destr ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          match x with
                          | LowParse_Spec_Enum.Known k1 ->
                              destr ()
                                (fun k2 ->
                                   fun cond ->
                                     fun ift ->
                                       fun iff ->
                                         fun rrel1 ->
                                           fun rel1 ->
                                             fun input1 ->
                                               fun len ->
                                                 if cond
                                                 then ift () () () input1 len
                                                 else iff () () () input1 len)
                                () ()
                                (fun k2 ->
                                   fun rrel1 ->
                                     fun rel1 ->
                                       fun input1 ->
                                         fun pos1 ->
                                           let h1 =
                                             FStar_HyperStack_ST.get () in
                                           f' k2 () () input1 pos1) k1 () ()
                                input pos
                          | LowParse_Spec_Enum.Unknown r ->
                              let h1 = FStar_HyperStack_ST.get () in
                              g' () () input pos
let (validate_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    (unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt64.t -> FStar_UInt64.t)
                      ->
                      (unit ->
                         ((Obj.t, Obj.t, unit)
                            LowParse_Spec_Enum.maybe_enum_key ->
                            Prims.bool ->
                              (unit ->
                                 unit ->
                                   unit ->
                                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                                       FStar_UInt64.t -> FStar_UInt64.t)
                                ->
                                (unit ->
                                   unit ->
                                     unit ->
                                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                                         FStar_UInt64.t -> FStar_UInt64.t)
                                  ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt64.t -> FStar_UInt64.t)
                           ->
                           unit ->
                             unit ->
                               ((Obj.t, Obj.t, unit)
                                  LowParse_Spec_Enum.maybe_enum_key ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt64.t -> FStar_UInt64.t)
                                 ->
                                 Obj.t ->
                                   unit ->
                                     unit ->
                                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                                         FStar_UInt64.t -> FStar_UInt64.t)
                        ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun v ->
          fun p32 ->
            fun f ->
              fun f32 ->
                fun k' ->
                  fun g ->
                    fun g32 ->
                      fun destr ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos ->
                                let h = FStar_HyperStack_ST.get () in
                                let pos_after_tag = v () () input pos in
                                if
                                  LowParse_Low_ErrorCode.is_error
                                    pos_after_tag
                                then pos_after_tag
                                else
                                  (let tg =
                                     p32 () () input
                                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                                   destr ()
                                     (fun x ->
                                        fun cond ->
                                          fun ift ->
                                            fun iff ->
                                              fun rrel1 ->
                                                fun rel1 ->
                                                  fun input1 ->
                                                    fun len ->
                                                      if cond
                                                      then
                                                        ift () () () input1
                                                          len
                                                      else
                                                        iff () () () input1
                                                          len) () ()
                                     (fun x ->
                                        match x with
                                        | LowParse_Spec_Enum.Known x' ->
                                            (fun rrel1 ->
                                               fun rel1 ->
                                                 fun input1 ->
                                                   fun pos1 ->
                                                     let h1 =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     f32 x' () () input1 pos1)
                                        | LowParse_Spec_Enum.Unknown x' ->
                                            (fun rrel1 ->
                                               fun rel1 ->
                                                 fun input1 ->
                                                   fun pos1 ->
                                                     let h1 =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     g32 () () input1 pos1))
                                     tg () () input pos_after_tag)


let (finalize_dsum_case_known :
  LowParse_Spec_Sum.dsum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.enum_repr_of_key'_t
                    ->
                    Obj.t ->
                      unit ->
                        unit ->
                          (Obj.t, Obj.t) LowParse_Slice.slice ->
                            FStar_UInt32.t -> unit)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun s ->
          fun w ->
            fun f ->
              fun ku ->
                fun g ->
                  fun destr ->
                    fun k ->
                      fun rrel ->
                        fun rel ->
                          fun input ->
                            fun pos ->
                              let pos1 =
                                let pos' =
                                  let res = w (destr k) () () input pos in
                                  let h = FStar_HyperStack_ST.get () in res in
                                let h = FStar_HyperStack_ST.get () in pos' in
                              let h = FStar_HyperStack_ST.get () in ()
let (finalize_dsum_case_unknown :
  LowParse_Spec_Sum.dsum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (Obj.t ->
             unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  Obj.t ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> unit)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun s ->
          fun w ->
            fun f ->
              fun ku ->
                fun g ->
                  fun r ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let pos1 = w r () () input pos in
                            let h = FStar_HyperStack_ST.get () in ()

let (read_dsum_tag :
  LowParse_Spec_Sum.dsum ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
          ->
          (unit ->
             (Prims.bool ->
                (unit ->
                   (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
                  ->
                  (unit ->
                     (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
                    -> (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
               ->
               unit ->
                 unit ->
                   ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
                     ->
                     Obj.t ->
                       (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t ->
                          (Obj.t, Obj.t, unit)
                            LowParse_Spec_Enum.maybe_enum_key)
  =
  fun t ->
    fun kt ->
      fun p ->
        fun p32 ->
          fun destr ->
            fun f ->
              fun ku ->
                fun g ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let h1 = FStar_HyperStack_ST.get () in
                          let res = p32 () () input pos in
                          destr ()
                            (fun cond ->
                               fun s_true ->
                                 fun s_false ->
                                   if cond then s_true () else s_false ()) ()
                            () (fun k -> k) res


type ('s, 'f, 'k, 'g, 'x) jump_dsum_cases_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
type ('s, 'f, 'k, 'g, 'x, 'v1, 'v2) jump_dsum_cases_eq = unit
let (jump_dsum_cases_if' :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
            Prims.bool ->
              (unit ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun s ->
    fun f ->
      fun k ->
        fun g ->
          fun x ->
            fun cond ->
              fun ift ->
                fun iff ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun len ->
                          if cond
                          then ift () () () input len
                          else iff () () () input len
let (jump_dsum_cases_if :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
            Prims.bool ->
              (unit ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun s ->
    fun f ->
      fun k ->
        fun g ->
          fun x ->
            fun cond ->
              fun ift ->
                fun iff ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun len ->
                          if cond
                          then ift () () () input len
                          else iff () () () input len
let (jump_dsum_cases' :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun s ->
    fun f ->
      fun f' ->
        fun k ->
          fun g ->
            fun g' ->
              fun x ->
                match x with
                | LowParse_Spec_Enum.Known x' ->
                    (fun rrel ->
                       fun rel ->
                         fun input ->
                           fun pos ->
                             let h = FStar_HyperStack_ST.get () in
                             f' x' () () input pos)
                | LowParse_Spec_Enum.Unknown x' ->
                    (fun rrel ->
                       fun rel ->
                         fun input ->
                           fun pos ->
                             let h = FStar_HyperStack_ST.get () in
                             g' () () input pos)
let (jump_dsum_cases'_destr :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              (unit ->
                 (Obj.t ->
                    Prims.bool ->
                      (unit ->
                         unit ->
                           unit ->
                             (Obj.t, Obj.t) LowParse_Slice.slice ->
                               FStar_UInt32.t -> FStar_UInt32.t)
                        ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> FStar_UInt32.t)
                          ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt32.t -> FStar_UInt32.t)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt32.t -> FStar_UInt32.t)
                         ->
                         Obj.t ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> FStar_UInt32.t)
                ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun s ->
    fun f ->
      fun f' ->
        fun k ->
          fun g ->
            fun g' ->
              fun destr ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          match x with
                          | LowParse_Spec_Enum.Known k1 ->
                              destr ()
                                (fun k2 ->
                                   fun cond ->
                                     fun ift ->
                                       fun iff ->
                                         fun rrel1 ->
                                           fun rel1 ->
                                             fun input1 ->
                                               fun len ->
                                                 if cond
                                                 then ift () () () input1 len
                                                 else iff () () () input1 len)
                                () ()
                                (fun k2 ->
                                   fun rrel1 ->
                                     fun rel1 ->
                                       fun input1 ->
                                         fun pos1 ->
                                           let h = FStar_HyperStack_ST.get () in
                                           f' k2 () () input1 pos1) k1 () ()
                                input pos
                          | LowParse_Spec_Enum.Unknown r ->
                              let h = FStar_HyperStack_ST.get () in
                              g' () () input pos
let (jump_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              (unit ->
                 (Obj.t ->
                    Prims.bool ->
                      (unit ->
                         unit ->
                           unit ->
                             (Obj.t, Obj.t) LowParse_Slice.slice ->
                               FStar_UInt32.t -> FStar_UInt32.t)
                        ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> FStar_UInt32.t)
                          ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt32.t -> FStar_UInt32.t)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt32.t -> FStar_UInt32.t)
                         ->
                         Obj.t ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> FStar_UInt32.t)
                ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun s ->
    fun f ->
      fun f' ->
        fun k ->
          fun g ->
            fun g' ->
              fun destr ->
                fun x ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          match x with
                          | LowParse_Spec_Enum.Known k1 ->
                              destr ()
                                (fun k2 ->
                                   fun cond ->
                                     fun ift ->
                                       fun iff ->
                                         fun rrel1 ->
                                           fun rel1 ->
                                             fun input1 ->
                                               fun len ->
                                                 if cond
                                                 then ift () () () input1 len
                                                 else iff () () () input1 len)
                                () ()
                                (fun k2 ->
                                   fun rrel1 ->
                                     fun rel1 ->
                                       fun input1 ->
                                         fun pos1 ->
                                           let h1 =
                                             FStar_HyperStack_ST.get () in
                                           f' k2 () () input1 pos1) k1 () ()
                                input pos
                          | LowParse_Spec_Enum.Unknown r ->
                              let h1 = FStar_HyperStack_ST.get () in
                              g' () () input pos
let (jump_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    (unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      (unit ->
                         ((Obj.t, Obj.t, unit)
                            LowParse_Spec_Enum.maybe_enum_key ->
                            Prims.bool ->
                              (unit ->
                                 unit ->
                                   unit ->
                                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                                       FStar_UInt32.t -> FStar_UInt32.t)
                                ->
                                (unit ->
                                   unit ->
                                     unit ->
                                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                                         FStar_UInt32.t -> FStar_UInt32.t)
                                  ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt32.t -> FStar_UInt32.t)
                           ->
                           unit ->
                             unit ->
                               ((Obj.t, Obj.t, unit)
                                  LowParse_Spec_Enum.maybe_enum_key ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt32.t -> FStar_UInt32.t)
                                 ->
                                 Obj.t ->
                                   unit ->
                                     unit ->
                                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                                         FStar_UInt32.t -> FStar_UInt32.t)
                        ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun v ->
          fun p32 ->
            fun f ->
              fun f32 ->
                fun k' ->
                  fun g ->
                    fun g32 ->
                      fun destr ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos ->
                                let h = FStar_HyperStack_ST.get () in
                                let pos_after_tag = v () () input pos in
                                let tg = p32 () () input pos in
                                destr ()
                                  (fun x ->
                                     fun cond ->
                                       fun ift ->
                                         fun iff ->
                                           fun rrel1 ->
                                             fun rel1 ->
                                               fun input1 ->
                                                 fun len ->
                                                   if cond
                                                   then
                                                     ift () () () input1 len
                                                   else
                                                     iff () () () input1 len)
                                  () ()
                                  (fun x ->
                                     match x with
                                     | LowParse_Spec_Enum.Known x' ->
                                         (fun rrel1 ->
                                            fun rel1 ->
                                              fun input1 ->
                                                fun pos1 ->
                                                  let h1 =
                                                    FStar_HyperStack_ST.get
                                                      () in
                                                  f32 x' () () input1 pos1)
                                     | LowParse_Spec_Enum.Unknown x' ->
                                         (fun rrel1 ->
                                            fun rel1 ->
                                              fun input1 ->
                                                fun pos1 ->
                                                  let h1 =
                                                    FStar_HyperStack_ST.get
                                                      () in
                                                  g32 () () input1 pos1)) tg
                                  () () input pos_after_tag
let (read_dsum_cases' :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> Obj.t)
              ->
              (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun f ->
      fun f32 ->
        fun k' ->
          fun g ->
            fun g32 ->
              fun x ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        match x with
                        | LowParse_Spec_Enum.Known x' ->
                            let h = FStar_HyperStack_ST.get () in
                            let res = f32 x' () () input pos in
                            ((match t with
                              | LowParse_Spec_Sum.DSum
                                  (uu___, uu___1, uu___2, uu___3, uu___4,
                                   uu___5, uu___6, synth_case, uu___7,
                                   uu___8, uu___9)
                                  -> synth_case))
                              (LowParse_Spec_Enum.Known x') res
                        | LowParse_Spec_Enum.Unknown x' ->
                            let h = FStar_HyperStack_ST.get () in
                            let res = g32 () () input pos in
                            ((match t with
                              | LowParse_Spec_Sum.DSum
                                  (uu___, uu___1, uu___2, uu___3, uu___4,
                                   uu___5, uu___6, synth_case, uu___7,
                                   uu___8, uu___9)
                                  -> synth_case))
                              (LowParse_Spec_Enum.Unknown x') res
type ('t, 'f, 'ku, 'g, 'k) read_dsum_cases_t =
  unit ->
    unit -> (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t
type ('t, 'f, 'ku, 'g, 'k, 'x, 'y) read_dsum_cases_t_eq = unit
let (read_dsum_cases_t_if :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          Obj.t ->
            Prims.bool ->
              (unit ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> Obj.t)
                ->
                (unit ->
                   unit ->
                     unit ->
                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                         FStar_UInt32.t -> Obj.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun f ->
      fun k' ->
        fun g ->
          fun k ->
            fun cond ->
              fun sv_true ->
                fun sv_false ->
                  fun uu___ ->
                    fun uu___1 ->
                      fun input ->
                        fun pos ->
                          if cond
                          then sv_true () () () input pos
                          else sv_false () () () input pos
let (read_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      (Obj.t ->
         unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Obj.t)
        ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> Obj.t)
              ->
              (unit ->
                 (Obj.t ->
                    Prims.bool ->
                      (unit ->
                         unit ->
                           unit ->
                             (Obj.t, Obj.t) LowParse_Slice.slice ->
                               FStar_UInt32.t -> Obj.t)
                        ->
                        (unit ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> Obj.t)
                          ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt32.t -> Obj.t)
                   ->
                   unit ->
                     unit ->
                       (Obj.t ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt32.t -> Obj.t)
                         ->
                         Obj.t ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt32.t -> Obj.t)
                ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun f ->
      fun f32 ->
        fun k' ->
          fun g ->
            fun g32 ->
              fun destr ->
                fun x ->
                  fun uu___ ->
                    fun uu___1 ->
                      fun input ->
                        fun pos ->
                          match x with
                          | LowParse_Spec_Enum.Known k ->
                              destr ()
                                (fun k1 ->
                                   fun cond ->
                                     fun sv_true ->
                                       fun sv_false ->
                                         fun uu___2 ->
                                           fun uu___3 ->
                                             fun input1 ->
                                               fun pos1 ->
                                                 if cond
                                                 then
                                                   sv_true () () () input1
                                                     pos1
                                                 else
                                                   sv_false () () () input1
                                                     pos1) () ()
                                (fun k1 ->
                                   fun rrel ->
                                     fun rel ->
                                       fun input1 ->
                                         fun pos1 ->
                                           let h = FStar_HyperStack_ST.get () in
                                           let res = f32 k1 () () input1 pos1 in
                                           (match t with
                                            | LowParse_Spec_Sum.DSum
                                                (uu___2, uu___3, uu___4,
                                                 uu___5, uu___6, uu___7,
                                                 uu___8, synth_case, uu___9,
                                                 uu___10, uu___11)
                                                -> synth_case)
                                             (LowParse_Spec_Enum.Known k1)
                                             res) k () () input pos
                          | LowParse_Spec_Enum.Unknown r ->
                              let h = FStar_HyperStack_ST.get () in
                              let res = g32 () () input pos in
                              ((match t with
                                | LowParse_Spec_Sum.DSum
                                    (uu___2, uu___3, uu___4, uu___5, uu___6,
                                     uu___7, uu___8, synth_case, uu___9,
                                     uu___10, uu___11)
                                    -> synth_case))
                                (LowParse_Spec_Enum.Unknown r) res
let (read_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t ->
                 (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
          ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              (Obj.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> Obj.t)
                ->
                LowParse_Spec_Base.parser_kind ->
                  unit ->
                    (unit ->
                       unit ->
                         (Obj.t, Obj.t) LowParse_Slice.slice ->
                           FStar_UInt32.t -> Obj.t)
                      ->
                      (unit ->
                         (Obj.t ->
                            Prims.bool ->
                              (unit ->
                                 unit ->
                                   unit ->
                                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                                       FStar_UInt32.t -> Obj.t)
                                ->
                                (unit ->
                                   unit ->
                                     unit ->
                                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                                         FStar_UInt32.t -> Obj.t)
                                  ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt32.t -> Obj.t)
                           ->
                           unit ->
                             unit ->
                               (Obj.t ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt32.t -> Obj.t)
                                 ->
                                 Obj.t ->
                                   unit ->
                                     unit ->
                                       (Obj.t, Obj.t) LowParse_Slice.slice ->
                                         FStar_UInt32.t -> Obj.t)
                        ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt32.t -> Obj.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun p32 ->
          fun j ->
            fun f ->
              fun f32 ->
                fun k' ->
                  fun g ->
                    fun g32 ->
                      fun destr ->
                        fun uu___ ->
                          fun uu___1 ->
                            fun input ->
                              fun pos ->
                                let h = FStar_HyperStack_ST.get () in
                                let k = p32 () () input pos in
                                let pos' =
                                  let h1 = FStar_HyperStack_ST.get () in
                                  j () () input pos in
                                match k with
                                | LowParse_Spec_Enum.Known k1 ->
                                    destr ()
                                      (fun k2 ->
                                         fun cond ->
                                           fun sv_true ->
                                             fun sv_false ->
                                               fun uu___2 ->
                                                 fun uu___3 ->
                                                   fun input1 ->
                                                     fun pos1 ->
                                                       if cond
                                                       then
                                                         sv_true () () ()
                                                           input1 pos1
                                                       else
                                                         sv_false () () ()
                                                           input1 pos1) () ()
                                      (fun k2 ->
                                         fun rrel ->
                                           fun rel ->
                                             fun input1 ->
                                               fun pos1 ->
                                                 let h1 =
                                                   FStar_HyperStack_ST.get () in
                                                 let res =
                                                   f32 k2 () () input1 pos1 in
                                                 (match t with
                                                  | LowParse_Spec_Sum.DSum
                                                      (uu___2, uu___3,
                                                       uu___4, uu___5,
                                                       uu___6, uu___7,
                                                       uu___8, synth_case,
                                                       uu___9, uu___10,
                                                       uu___11)
                                                      -> synth_case)
                                                   (LowParse_Spec_Enum.Known
                                                      k2) res) k1 () () input
                                      pos'
                                | LowParse_Spec_Enum.Unknown r ->
                                    let h1 = FStar_HyperStack_ST.get () in
                                    let res = g32 () () input pos' in
                                    ((match t with
                                      | LowParse_Spec_Sum.DSum
                                          (uu___2, uu___3, uu___4, uu___5,
                                           uu___6, uu___7, uu___8,
                                           synth_case, uu___9, uu___10,
                                           uu___11)
                                          -> synth_case))
                                      (LowParse_Spec_Enum.Unknown r) res
let (serialize32_dsum_type_of_tag :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t ->
           Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t ->
                   unit ->
                     unit ->
                       (LowParse_Bytes.byte, Obj.t, Obj.t)
                         LowStar_Monotonic_Buffer.mbuffer ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    Obj.t ->
                      unit ->
                        unit ->
                          (LowParse_Bytes.byte, Obj.t, Obj.t)
                            LowStar_Monotonic_Buffer.mbuffer ->
                            FStar_UInt32.t -> FStar_UInt32.t)
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
                        (fun x ->
                           fun rrel ->
                             fun rel ->
                               fun b -> fun pos -> sf32 x' x () () b pos)
                    | LowParse_Spec_Enum.Unknown x' ->
                        (fun x ->
                           fun rrel ->
                             fun rel ->
                               fun b -> fun pos -> sg32 x () () b pos)
let (serialize32_dsum_cases_aux :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t ->
           Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t ->
                   unit ->
                     unit ->
                       (LowParse_Bytes.byte, Obj.t, Obj.t)
                         LowStar_Monotonic_Buffer.mbuffer ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                    Obj.t ->
                      unit ->
                        unit ->
                          (LowParse_Bytes.byte, Obj.t, Obj.t)
                            LowStar_Monotonic_Buffer.mbuffer ->
                            FStar_UInt32.t -> FStar_UInt32.t)
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
                    fun x ->
                      fun rrel ->
                        fun rel ->
                          fun input ->
                            fun pos ->
                              (match tg with
                               | LowParse_Spec_Enum.Known x' ->
                                   (fun x1 ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun b ->
                                            fun pos1 ->
                                              sf32 x' x1 () () b pos1)
                               | LowParse_Spec_Enum.Unknown x' ->
                                   (fun x1 ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun b ->
                                            fun pos1 -> sg32 x1 () () b pos1))
                                (match t with
                                 | LowParse_Spec_Sum.DSum
                                     (uu___, uu___1, uu___2, uu___3, uu___4,
                                      uu___5, uu___6, uu___7,
                                      synth_case_recip, uu___8, uu___9)
                                     -> synth_case_recip tg x) () () input
                                pos
type ('t, 'f, 'sf, 'ku, 'g, 'sg, 'k) serialize32_dsum_cases_t =
  Obj.t ->
    unit ->
      unit ->
        (LowParse_Bytes.byte, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer
          -> FStar_UInt32.t -> FStar_UInt32.t
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
                  (unit ->
                     Obj.t ->
                       unit ->
                         unit ->
                           (LowParse_Bytes.byte, Obj.t, Obj.t)
                             LowStar_Monotonic_Buffer.mbuffer ->
                             FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    (unit ->
                       Obj.t ->
                         unit ->
                           unit ->
                             (LowParse_Bytes.byte, Obj.t, Obj.t)
                               LowStar_Monotonic_Buffer.mbuffer ->
                               FStar_UInt32.t -> FStar_UInt32.t)
                      ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
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
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun output ->
                              fun pos ->
                                if cond
                                then sv_true () x () () output pos
                                else sv_false () x () () output pos
let (serialize32_dsum_cases :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      unit ->
        (Obj.t ->
           Obj.t ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t ->
                   unit ->
                     unit ->
                       (LowParse_Bytes.byte, Obj.t, Obj.t)
                         LowStar_Monotonic_Buffer.mbuffer ->
                         FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  (unit ->
                     (Obj.t ->
                        Prims.bool ->
                          (unit ->
                             Obj.t ->
                               unit ->
                                 unit ->
                                   (LowParse_Bytes.byte, Obj.t, Obj.t)
                                     LowStar_Monotonic_Buffer.mbuffer ->
                                     FStar_UInt32.t -> FStar_UInt32.t)
                            ->
                            (unit ->
                               Obj.t ->
                                 unit ->
                                   unit ->
                                     (LowParse_Bytes.byte, Obj.t, Obj.t)
                                       LowStar_Monotonic_Buffer.mbuffer ->
                                       FStar_UInt32.t -> FStar_UInt32.t)
                              ->
                              Obj.t ->
                                unit ->
                                  unit ->
                                    (LowParse_Bytes.byte, Obj.t, Obj.t)
                                      LowStar_Monotonic_Buffer.mbuffer ->
                                      FStar_UInt32.t -> FStar_UInt32.t)
                       ->
                       unit ->
                         unit ->
                           (Obj.t ->
                              Obj.t ->
                                unit ->
                                  unit ->
                                    (LowParse_Bytes.byte, Obj.t, Obj.t)
                                      LowStar_Monotonic_Buffer.mbuffer ->
                                      FStar_UInt32.t -> FStar_UInt32.t)
                             ->
                             Obj.t ->
                               Obj.t ->
                                 unit ->
                                   unit ->
                                     (LowParse_Bytes.byte, Obj.t, Obj.t)
                                       LowStar_Monotonic_Buffer.mbuffer ->
                                       FStar_UInt32.t -> FStar_UInt32.t)
                    ->
                    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                      Obj.t ->
                        unit ->
                          unit ->
                            (LowParse_Bytes.byte, Obj.t, Obj.t)
                              LowStar_Monotonic_Buffer.mbuffer ->
                              FStar_UInt32.t -> FStar_UInt32.t)
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
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun output ->
                              fun pos ->
                                match tg with
                                | LowParse_Spec_Enum.Known k ->
                                    destr ()
                                      (fun k1 ->
                                         fun cond ->
                                           fun sv_true ->
                                             fun sv_false ->
                                               fun x1 ->
                                                 fun rrel1 ->
                                                   fun rel1 ->
                                                     fun output1 ->
                                                       fun pos1 ->
                                                         if cond
                                                         then
                                                           sv_true () x1 ()
                                                             () output1 pos1
                                                         else
                                                           sv_false () x1 ()
                                                             () output1 pos1)
                                      () ()
                                      (fun k1 ->
                                         fun x1 ->
                                           fun rrel1 ->
                                             fun rel1 ->
                                               fun input ->
                                                 fun pos1 ->
                                                   sf32 k1
                                                     ((match t with
                                                       | LowParse_Spec_Sum.DSum
                                                           (uu___, uu___1,
                                                            uu___2, uu___3,
                                                            uu___4, uu___5,
                                                            uu___6, uu___7,
                                                            synth_case_recip,
                                                            uu___8, uu___9)
                                                           ->
                                                           synth_case_recip)
                                                        (LowParse_Spec_Enum.Known
                                                           k1) x1) () ()
                                                     input pos1) k x () ()
                                      output pos
                                | LowParse_Spec_Enum.Unknown r ->
                                    sg32
                                      ((match t with
                                        | LowParse_Spec_Sum.DSum
                                            (uu___, uu___1, uu___2, uu___3,
                                             uu___4, uu___5, uu___6, uu___7,
                                             synth_case_recip, uu___8,
                                             uu___9)
                                            -> synth_case_recip)
                                         (LowParse_Spec_Enum.Unknown r) x) ()
                                      () output pos
let (serialize32_dsum :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        unit ->
          ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
             unit ->
               unit ->
                 (LowParse_Bytes.byte, Obj.t, Obj.t)
                   LowStar_Monotonic_Buffer.mbuffer ->
                   FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
              ->
              unit ->
                (Obj.t ->
                   Obj.t ->
                     unit ->
                       unit ->
                         (LowParse_Bytes.byte, Obj.t, Obj.t)
                           LowStar_Monotonic_Buffer.mbuffer ->
                           FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  LowParse_Spec_Base.parser_kind ->
                    unit ->
                      unit ->
                        (Obj.t ->
                           unit ->
                             unit ->
                               (LowParse_Bytes.byte, Obj.t, Obj.t)
                                 LowStar_Monotonic_Buffer.mbuffer ->
                                 FStar_UInt32.t -> FStar_UInt32.t)
                          ->
                          (unit ->
                             (Obj.t ->
                                Prims.bool ->
                                  (unit ->
                                     Obj.t ->
                                       unit ->
                                         unit ->
                                           (LowParse_Bytes.byte, Obj.t,
                                             Obj.t)
                                             LowStar_Monotonic_Buffer.mbuffer
                                             ->
                                             FStar_UInt32.t -> FStar_UInt32.t)
                                    ->
                                    (unit ->
                                       Obj.t ->
                                         unit ->
                                           unit ->
                                             (LowParse_Bytes.byte, Obj.t,
                                               Obj.t)
                                               LowStar_Monotonic_Buffer.mbuffer
                                               ->
                                               FStar_UInt32.t ->
                                                 FStar_UInt32.t)
                                      ->
                                      Obj.t ->
                                        unit ->
                                          unit ->
                                            (LowParse_Bytes.byte, Obj.t,
                                              Obj.t)
                                              LowStar_Monotonic_Buffer.mbuffer
                                              ->
                                              FStar_UInt32.t ->
                                                FStar_UInt32.t)
                               ->
                               unit ->
                                 unit ->
                                   (Obj.t ->
                                      Obj.t ->
                                        unit ->
                                          unit ->
                                            (LowParse_Bytes.byte, Obj.t,
                                              Obj.t)
                                              LowStar_Monotonic_Buffer.mbuffer
                                              ->
                                              FStar_UInt32.t ->
                                                FStar_UInt32.t)
                                     ->
                                     Obj.t ->
                                       Obj.t ->
                                         unit ->
                                           unit ->
                                             (LowParse_Bytes.byte, Obj.t,
                                               Obj.t)
                                               LowStar_Monotonic_Buffer.mbuffer
                                               ->
                                               FStar_UInt32.t ->
                                                 FStar_UInt32.t)
                            ->
                            Obj.t ->
                              unit ->
                                unit ->
                                  (LowParse_Bytes.byte, Obj.t, Obj.t)
                                    LowStar_Monotonic_Buffer.mbuffer ->
                                    FStar_UInt32.t -> FStar_UInt32.t)
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
                            fun x ->
                              fun uu___ ->
                                fun uu___1 ->
                                  fun output ->
                                    fun pos ->
                                      let tg =
                                        match t with
                                        | LowParse_Spec_Sum.DSum
                                            (uu___2, uu___3, uu___4, uu___5,
                                             tag_of_data, uu___6, uu___7,
                                             uu___8, uu___9, uu___10,
                                             uu___11)
                                            -> tag_of_data x in
                                      let len1 =
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let res = s32 tg () () output pos in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        let pos' = FStar_UInt32.add pos res in
                                        res in
                                      let pos1 = FStar_UInt32.add pos len1 in
                                      let len2 =
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let res =
                                          match tg with
                                          | LowParse_Spec_Enum.Known k ->
                                              destr ()
                                                (fun k1 ->
                                                   fun cond ->
                                                     fun sv_true ->
                                                       fun sv_false ->
                                                         fun x1 ->
                                                           fun rrel ->
                                                             fun rel ->
                                                               fun output1 ->
                                                                 fun pos2 ->
                                                                   if cond
                                                                   then
                                                                    sv_true
                                                                    () x1 ()
                                                                    ()
                                                                    output1
                                                                    pos2
                                                                   else
                                                                    sv_false
                                                                    () x1 ()
                                                                    ()
                                                                    output1
                                                                    pos2) ()
                                                ()
                                                (fun k1 ->
                                                   fun x1 ->
                                                     fun rrel ->
                                                       fun rel ->
                                                         fun input ->
                                                           fun pos2 ->
                                                             sf32 k1
                                                               ((match t with
                                                                 | LowParse_Spec_Sum.DSum
                                                                    (uu___2,
                                                                    uu___3,
                                                                    uu___4,
                                                                    uu___5,
                                                                    uu___6,
                                                                    uu___7,
                                                                    uu___8,
                                                                    uu___9,
                                                                    synth_case_recip,
                                                                    uu___10,
                                                                    uu___11)
                                                                    ->
                                                                    synth_case_recip)
                                                                  (LowParse_Spec_Enum.Known
                                                                    k1) x1)
                                                               () () input
                                                               pos2) k x ()
                                                () output pos1
                                          | LowParse_Spec_Enum.Unknown r ->
                                              sg32
                                                ((match t with
                                                  | LowParse_Spec_Sum.DSum
                                                      (uu___2, uu___3,
                                                       uu___4, uu___5,
                                                       uu___6, uu___7,
                                                       uu___8, uu___9,
                                                       synth_case_recip,
                                                       uu___10, uu___11)
                                                      -> synth_case_recip)
                                                   (LowParse_Spec_Enum.Unknown
                                                      r) x) () () output pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        let pos' = FStar_UInt32.add pos1 res in
                                        res in
                                      let h1 = FStar_HyperStack_ST.get () in
                                      FStar_UInt32.add len1 len2
let (clens_dsum_tag :
  LowParse_Spec_Sum.dsum ->
    (Obj.t, (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key)
      LowParse_Low_Base_Spec.clens)
  =
  fun s ->
    {
      LowParse_Low_Base_Spec.clens_cond = ();
      LowParse_Low_Base_Spec.clens_get = ()
    }

let (accessor_dsum_tag :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun f ->
          fun ku ->
            fun g ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos -> let h = FStar_HyperStack_ST.get () in pos
let (clens_dsum_payload :
  LowParse_Spec_Sum.dsum ->
    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
      (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun s ->
    fun k ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }
let (clens_dsum_unknown_payload :
  LowParse_Spec_Sum.dsum -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens) =
  fun s ->
    {
      LowParse_Low_Base_Spec.clens_cond = ();
      LowParse_Low_Base_Spec.clens_get = ()
    }




let (accessor_clens_dsum_payload' :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun j ->
          fun f ->
            fun ku ->
              fun g ->
                fun k ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          j () () input pos
let (accessor_clens_dsum_payload :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun j ->
          fun f ->
            fun ku ->
              fun g ->
                fun k ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          j () () input pos




let (accessor_clens_dsum_unknown_payload' :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun j ->
          fun f ->
            fun ku ->
              fun g ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        j () () input pos
let (accessor_clens_dsum_unknown_payload :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Sum.dsum ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt32.t -> FStar_UInt32.t)
          ->
          (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun kt ->
    fun t ->
      fun p ->
        fun j ->
          fun f ->
            fun ku ->
              fun g ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        j () () input pos
let (clens_dsum_cases_payload :
  LowParse_Spec_Sum.dsum ->
    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
      (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun s ->
    fun k ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }

let (accessor_clens_dsum_cases_known_payload :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun f ->
      fun ku ->
        fun g ->
          fun k ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let h1 = FStar_HyperStack_ST.get () in pos

let (accessor_clens_dsum_cases_unknown_payload :
  LowParse_Spec_Sum.dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          Obj.t ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun t ->
    fun f ->
      fun ku ->
        fun g ->
          fun k ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let h1 = FStar_HyperStack_ST.get () in pos