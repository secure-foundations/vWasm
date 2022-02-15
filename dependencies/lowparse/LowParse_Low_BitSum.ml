open Prims
let (validate_bitsum' :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum' ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> Obj.t)
                  ->
                  (Obj.t -> Prims.bool) ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun b ->
          fun k ->
            fun p ->
              fun v ->
                fun r ->
                  fun phi ->
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
                                 r () () input
                                   (FStar_Int_Cast.uint64_to_uint32 pos) in
                               if Prims.op_Negation (phi va)
                               then
                                 LowParse_Low_ErrorCode.validator_error_generic
                               else res)
let (validate_bitsum_cases_bitstop :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        unit ->
          (unit -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
            (unit ->
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
  fun tot ->
    fun t ->
      fun cl ->
        fun u ->
          fun f ->
            fun v ->
              fun x ->
                fun rrel -> fun rel -> fun sl -> fun pos -> v () () () sl pos
let (validate_bitsum_cases_bitfield :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          Prims.nat ->
            (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum' ->
              (unit ->
                 (Obj.t ->
                    (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                   ->
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
                unit ->
                  (Obj.t ->
                     (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                    ->
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
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun sz ->
            fun rest ->
              fun phi ->
                fun u ->
                  fun f ->
                    fun v ->
                      fun x ->
                        fun rrel ->
                          fun rel ->
                            fun sl ->
                              fun pos ->
                                phi () (fun x1 -> f x1) (fun x1 -> v x1) x ()
                                  () sl pos
let (validate_bitsum_cases_bitsum_gen :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t -> Obj.t) ->
                  (Obj.t ->
                     (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum')
                    ->
                    (Obj.t ->
                       unit ->
                         (Obj.t ->
                            (LowParse_Spec_Base.parser_kind, unit)
                              Prims.dtuple2)
                           ->
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
                      unit ->
                        (Obj.t ->
                           (LowParse_Spec_Base.parser_kind, unit)
                             Prims.dtuple2)
                          ->
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
                        fun f ->
                          fun v ->
                            fun x_ ->
                              fun rrel ->
                                fun rel ->
                                  fun sl ->
                                    fun pos ->
                                      destr_payload
                                        (key_of
                                           ((match cl with
                                             | { LowParse_BitFields.v = v1;
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
                                                 LowParse_BitFields.logor =
                                                   logor;
                                                 LowParse_BitFields.bitfield_eq_lhs
                                                   = bitfield_eq_lhs;
                                                 LowParse_BitFields.bitfield_eq_rhs
                                                   = bitfield_eq_rhs;_}
                                                 -> get_bitfield) x_
                                              (bitsum'_size - key_size)
                                              bitsum'_size)) ()
                                        (fun x ->
                                           f
                                             (Obj.magic
                                                (Prims.Mkdtuple2
                                                   ((key_of
                                                       ((match cl with
                                                         | {
                                                             LowParse_BitFields.v
                                                               = v1;
                                                             LowParse_BitFields.uint_to_t
                                                               = uint_to_t;
                                                             LowParse_BitFields.v_uint_to_t
                                                               = v_uint_to_t;
                                                             LowParse_BitFields.uint_to_t_v
                                                               = uint_to_t_v;
                                                             LowParse_BitFields.get_bitfield_gen
                                                               =
                                                               get_bitfield_gen;
                                                             LowParse_BitFields.set_bitfield_gen
                                                               =
                                                               set_bitfield_gen;
                                                             LowParse_BitFields.get_bitfield
                                                               = get_bitfield;
                                                             LowParse_BitFields.set_bitfield
                                                               = set_bitfield;
                                                             LowParse_BitFields.logor
                                                               = logor;
                                                             LowParse_BitFields.bitfield_eq_lhs
                                                               =
                                                               bitfield_eq_lhs;
                                                             LowParse_BitFields.bitfield_eq_rhs
                                                               =
                                                               bitfield_eq_rhs;_}
                                                             -> get_bitfield)
                                                          x_
                                                          (bitsum'_size -
                                                             key_size)
                                                          bitsum'_size)), x))))
                                        (fun x ->
                                           v
                                             (Obj.magic
                                                (Prims.Mkdtuple2
                                                   ((key_of
                                                       ((match cl with
                                                         | {
                                                             LowParse_BitFields.v
                                                               = v1;
                                                             LowParse_BitFields.uint_to_t
                                                               = uint_to_t;
                                                             LowParse_BitFields.v_uint_to_t
                                                               = v_uint_to_t;
                                                             LowParse_BitFields.uint_to_t_v
                                                               = uint_to_t_v;
                                                             LowParse_BitFields.get_bitfield_gen
                                                               =
                                                               get_bitfield_gen;
                                                             LowParse_BitFields.set_bitfield_gen
                                                               =
                                                               set_bitfield_gen;
                                                             LowParse_BitFields.get_bitfield
                                                               = get_bitfield;
                                                             LowParse_BitFields.set_bitfield
                                                               = set_bitfield;
                                                             LowParse_BitFields.logor
                                                               = logor;
                                                             LowParse_BitFields.bitfield_eq_lhs
                                                               =
                                                               bitfield_eq_lhs;
                                                             LowParse_BitFields.bitfield_eq_rhs
                                                               =
                                                               bitfield_eq_rhs;_}
                                                             -> get_bitfield)
                                                          x_
                                                          (bitsum'_size -
                                                             key_size)
                                                          bitsum'_size)), x))))
                                        x_ () () sl pos
let (validate_bitsum_cases_bitsum'_intro :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t ->
                   (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum')
                  ->
                  (unit ->
                     (Obj.t ->
                        (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                       ->
                       (Obj.t ->
                          unit ->
                            unit ->
                              (Obj.t, Obj.t) LowParse_Slice.slice ->
                                FStar_UInt64.t -> FStar_UInt64.t)
                         ->
                         Obj.t ->
                           Obj.t ->
                             unit ->
                               unit ->
                                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                                   FStar_UInt64.t -> FStar_UInt64.t)
                    ->
                    unit ->
                      (Obj.t ->
                         (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                        ->
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
  fun tot ->
    fun t ->
      fun cl ->
        fun bitsum'_size ->
          fun key ->
            fun key_size ->
              fun e ->
                fun payload ->
                  fun phi ->
                    fun u ->
                      fun f ->
                        fun v ->
                          fun x ->
                            fun rrel ->
                              fun rel ->
                                fun sl ->
                                  fun pos ->
                                    let xr =
                                      (match cl with
                                       | { LowParse_BitFields.v = v1;
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
                                           -> bitfield_eq_lhs) x
                                        (bitsum'_size - key_size)
                                        bitsum'_size in
                                    phi () f v x xr () () sl pos
let (validate_bitsum_cases_bitsum'_nil :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t ->
                   (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum')
                  ->
                  unit ->
                    unit ->
                      (Obj.t ->
                         (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                        ->
                        (Obj.t ->
                           unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                          ->
                          Obj.t ->
                            Obj.t ->
                              unit ->
                                unit ->
                                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                                    FStar_UInt64.t -> FStar_UInt64.t)
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
                      fun f ->
                        fun v ->
                          fun x ->
                            fun xr ->
                              fun rrel ->
                                fun rel ->
                                  fun sl ->
                                    fun pos ->
                                      LowParse_Low_ErrorCode.validator_error_generic
let (validate_bitsum_cases_bitsum'_cons :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        Prims.nat ->
          unit ->
            Prims.nat ->
              (Obj.t, Obj.t) LowParse_Spec_Enum.enum ->
                (Obj.t ->
                   (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum')
                  ->
                  (Obj.t * Obj.t) Prims.list ->
                    Obj.t ->
                      Obj.t ->
                        (Obj.t * Obj.t) Prims.list ->
                          (unit ->
                             (Obj.t ->
                                (LowParse_Spec_Base.parser_kind, unit)
                                  Prims.dtuple2)
                               ->
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
                            (unit ->
                               (Obj.t ->
                                  (LowParse_Spec_Base.parser_kind, unit)
                                    Prims.dtuple2)
                                 ->
                                 (Obj.t ->
                                    unit ->
                                      unit ->
                                        (Obj.t, Obj.t) LowParse_Slice.slice
                                          -> FStar_UInt64.t -> FStar_UInt64.t)
                                   ->
                                   Obj.t ->
                                     Obj.t ->
                                       unit ->
                                         unit ->
                                           (Obj.t, Obj.t)
                                             LowParse_Slice.slice ->
                                             FStar_UInt64.t -> FStar_UInt64.t)
                              ->
                              unit ->
                                (Obj.t ->
                                   (LowParse_Spec_Base.parser_kind, unit)
                                     Prims.dtuple2)
                                  ->
                                  (Obj.t ->
                                     unit ->
                                       unit ->
                                         (Obj.t, Obj.t) LowParse_Slice.slice
                                           ->
                                           FStar_UInt64.t -> FStar_UInt64.t)
                                    ->
                                    Obj.t ->
                                      Obj.t ->
                                        unit ->
                                          unit ->
                                            (Obj.t, Obj.t)
                                              LowParse_Slice.slice ->
                                              FStar_UInt64.t ->
                                                FStar_UInt64.t)
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
                                fun f ->
                                  fun v ->
                                    fun x ->
                                      fun xr ->
                                        fun rrel ->
                                          fun rel ->
                                            fun sl ->
                                              fun pos ->
                                                if
                                                  xr =
                                                    ((match cl with
                                                      | {
                                                          LowParse_BitFields.v
                                                            = v1;
                                                          LowParse_BitFields.uint_to_t
                                                            = uint_to_t;
                                                          LowParse_BitFields.v_uint_to_t
                                                            = v_uint_to_t;
                                                          LowParse_BitFields.uint_to_t_v
                                                            = uint_to_t_v;
                                                          LowParse_BitFields.get_bitfield_gen
                                                            =
                                                            get_bitfield_gen;
                                                          LowParse_BitFields.set_bitfield_gen
                                                            =
                                                            set_bitfield_gen;
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
                                                          -> bitfield_eq_rhs)
                                                       x
                                                       (bitsum'_size -
                                                          key_size)
                                                       bitsum'_size r)
                                                then
                                                  destr_payload ()
                                                    (fun x1 ->
                                                       f
                                                         (Obj.magic
                                                            (Prims.Mkdtuple2
                                                               (k, x1))))
                                                    (fun x1 ->
                                                       v
                                                         (Obj.magic
                                                            (Prims.Mkdtuple2
                                                               (k, x1)))) x
                                                    () () sl pos
                                                else
                                                  destr_tail () f v x xr ()
                                                    () sl pos
let (validate_bitsum :
  LowParse_Spec_Base.parser_kind ->
    Prims.pos ->
      unit ->
        (unit, Obj.t) LowParse_BitFields.uint_t ->
          (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum' ->
            unit ->
              (Obj.t -> Obj.t) ->
                unit ->
                  (unit, Obj.t, unit, unit, Obj.t, unit, Obj.t)
                    LowParse_Spec_BitSum.synth_case_t ->
                    unit ->
                      (unit ->
                         unit ->
                           (Obj.t, Obj.t) LowParse_Slice.slice ->
                             FStar_UInt64.t -> FStar_UInt64.t)
                        ->
                        (unit ->
                           unit ->
                             (Obj.t, Obj.t) LowParse_Slice.slice ->
                               FStar_UInt32.t -> Obj.t)
                          ->
                          (Obj.t -> Prims.bool) ->
                            (Obj.t ->
                               (LowParse_Spec_Base.parser_kind, unit)
                                 Prims.dtuple2)
                              ->
                              (Obj.t ->
                                 unit ->
                                   unit ->
                                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                                       FStar_UInt64.t -> FStar_UInt64.t)
                                ->
                                (unit ->
                                   (Obj.t ->
                                      (LowParse_Spec_Base.parser_kind, 
                                        unit) Prims.dtuple2)
                                     ->
                                     (Obj.t ->
                                        unit ->
                                          unit ->
                                            (Obj.t, Obj.t)
                                              LowParse_Slice.slice ->
                                              FStar_UInt64.t ->
                                                FStar_UInt64.t)
                                       ->
                                       Obj.t ->
                                         unit ->
                                           unit ->
                                             (Obj.t, Obj.t)
                                               LowParse_Slice.slice ->
                                               FStar_UInt64.t ->
                                                 FStar_UInt64.t)
                                  ->
                                  unit ->
                                    unit ->
                                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun kt ->
    fun tot ->
      fun t ->
        fun cl ->
          fun b ->
            fun data ->
              fun tag_of_data ->
                fun type_of_tag ->
                  fun synth_case ->
                    fun p ->
                      fun v ->
                        fun r ->
                          fun phi ->
                            fun f ->
                              fun vf ->
                                fun vs ->
                                  fun rrel ->
                                    fun rel ->
                                      fun sl ->
                                        fun pos ->
                                          let h = FStar_HyperStack_ST.get () in
                                          let pos1 =
                                            let h1 =
                                              FStar_HyperStack_ST.get () in
                                            let h2 =
                                              FStar_HyperStack_ST.get () in
                                            let res = v () () sl pos in
                                            if
                                              LowParse_Low_ErrorCode.is_error
                                                res
                                            then res
                                            else
                                              (let va =
                                                 r () () sl
                                                   (FStar_Int_Cast.uint64_to_uint32
                                                      pos) in
                                               if Prims.op_Negation (phi va)
                                               then
                                                 LowParse_Low_ErrorCode.validator_error_generic
                                               else res) in
                                          if
                                            LowParse_Low_ErrorCode.is_error
                                              pos1
                                          then pos1
                                          else
                                            (let x =
                                               r () () sl
                                                 (FStar_Int_Cast.uint64_to_uint32
                                                    pos) in
                                             vs () f vf x () () sl pos1)


