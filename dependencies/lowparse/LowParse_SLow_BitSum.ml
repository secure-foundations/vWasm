open Prims
let (parse32_bitsum :
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
                      (LowParse_SLow_Base.bytes32 ->
                         (Obj.t * FStar_UInt32.t)
                           FStar_Pervasives_Native.option)
                        ->
                        (Obj.t ->
                           (LowParse_Spec_Base.parser_kind, unit)
                             Prims.dtuple2)
                          ->
                          (Obj.t ->
                             LowParse_SLow_Base.bytes32 ->
                               (Obj.t * FStar_UInt32.t)
                                 FStar_Pervasives_Native.option)
                            ->
                            LowParse_SLow_Base.bytes32 ->
                              (Obj.t * FStar_UInt32.t)
                                FStar_Pervasives_Native.option)
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
                      fun p32 ->
                        fun f ->
                          fun f32 ->
                            fun x ->
                              match p32 x with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some (tg', consumed1)
                                  ->
                                  if
                                    LowParse_Spec_BitSum.filter_bitsum' tot
                                      () cl tot b tg'
                                  then
                                    let tg =
                                      LowParse_Spec_BitSum.synth_bitsum' tot
                                        () cl tot b tg' in
                                    let x' =
                                      FStar_Bytes.slice x consumed1
                                        (FStar_Bytes.len x) in
                                    (match f32
                                             (LowParse_Spec_BitSum.bitsum'_key_of_t
                                                tot () cl tot b tg) x'
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (y, consumed2) ->
                                         FStar_Pervasives_Native.Some
                                           (((match synth_case with
                                              | LowParse_Spec_BitSum.SynthCase
                                                  (f1, f_inj, g, f_g_eq) ->
                                                  f1 tg y)),
                                             (FStar_UInt32.add consumed1
                                                consumed2)))
                                  else FStar_Pervasives_Native.None
let (serialize32_bitsum_cond :
  Prims.pos ->
    unit ->
      (unit, Obj.t) LowParse_BitFields.uint_t ->
        (unit, Obj.t, unit, unit) LowParse_Spec_BitSum.bitsum' ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
                -> Prims.bool)
  =
  fun tot ->
    fun t ->
      fun cl ->
        fun b ->
          fun k ->
            fun type_of_tag ->
              fun f ->
                match ((match k with
                        | {
                            LowParse_Spec_Base.parser_kind_low =
                              parser_kind_low;
                            LowParse_Spec_Base.parser_kind_high =
                              parser_kind_high;
                            LowParse_Spec_Base.parser_kind_subkind =
                              parser_kind_subkind;
                            LowParse_Spec_Base.parser_kind_metadata =
                              parser_kind_metadata;_}
                            -> parser_kind_high),
                        (match LowParse_Spec_BitSum.weaken_parse_bitsum_cases_kind
                                 tot () cl b () f
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
                             -> parser_kind_high))
                with
                | (FStar_Pervasives_Native.Some max1,
                   FStar_Pervasives_Native.Some max2) ->
                    (max1 + max2) < (Prims.parse_int "4294967296")
                | uu___ -> false
let (serialize32_bitsum :
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
                      unit ->
                        (Obj.t -> LowParse_SLow_Base.bytes32) ->
                          (Obj.t ->
                             (LowParse_Spec_Base.parser_kind, unit)
                               Prims.dtuple2)
                            ->
                            unit ->
                              (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32)
                                ->
                                unit -> Obj.t -> LowParse_SLow_Base.bytes32)
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
                      fun s ->
                        fun s32 ->
                          fun f ->
                            fun g ->
                              fun g32 ->
                                fun sq ->
                                  fun x ->
                                    let tg = tag_of_data x in
                                    let k =
                                      LowParse_Spec_BitSum.bitsum'_key_of_t
                                        tot () cl tot b tg in
                                    let payload =
                                      match synth_case with
                                      | LowParse_Spec_BitSum.SynthCase
                                          (f1, f_inj, g1, f_g_eq) -> 
                                          g1 tg x in
                                    let s_tg =
                                      s32
                                        (LowParse_Spec_BitSum.synth_bitsum'_recip'
                                           tot () cl tot b tg) in
                                    let s_pl = g32 k payload in
                                    FStar_Bytes.append s_tg s_pl