open Prims

type sum =
  | Sum of unit * unit * (Obj.t, Obj.t) LowParse_Spec_Enum.enum * unit *
  (Obj.t -> Obj.t) * unit * (Obj.t -> Obj.t -> Obj.t) *
  (Obj.t -> Obj.t -> Obj.t) * unit * unit 
let (uu___is_Sum : sum -> Prims.bool) = fun projectee -> true
let (__proj__Sum__item__e : sum -> (unit, unit) LowParse_Spec_Enum.enum) =
  fun uu___ ->
    (fun projectee ->
       match projectee with
       | Sum
           (key, repr, e, data, tag_of_data, type_of_tag, synth_case,
            synth_case_recip, synth_case_recip_synth_case,
            synth_case_synth_case_recip)
           -> Obj.magic e) uu___
let (__proj__Sum__item__tag_of_data : sum -> Obj.t -> Obj.t) =
  fun projectee ->
    match projectee with
    | Sum
        (key, repr, e, data, tag_of_data, type_of_tag, synth_case,
         synth_case_recip, synth_case_recip_synth_case,
         synth_case_synth_case_recip)
        -> tag_of_data
let (__proj__Sum__item__synth_case : sum -> Obj.t -> Obj.t -> Obj.t) =
  fun projectee ->
    match projectee with
    | Sum
        (key, repr, e, data, tag_of_data, type_of_tag, synth_case,
         synth_case_recip, synth_case_recip_synth_case,
         synth_case_synth_case_recip)
        -> synth_case
let (__proj__Sum__item__synth_case_recip : sum -> Obj.t -> Obj.t -> Obj.t) =
  fun projectee ->
    match projectee with
    | Sum
        (key, repr, e, data, tag_of_data, type_of_tag, synth_case,
         synth_case_recip, synth_case_recip_synth_case,
         synth_case_synth_case_recip)
        -> synth_case_recip


type 't sum_key_type = Obj.t
type 't sum_repr_type = Obj.t
let (sum_enum : sum -> (Obj.t, Obj.t) LowParse_Spec_Enum.enum) =
  fun t ->
    match t with
    | Sum
        (uu___, uu___1, e, uu___2, uu___3, uu___4, uu___5, uu___6, uu___7,
         uu___8)
        -> e
type 't sum_key = Obj.t
let (sum_key_type_of_sum_key : sum -> Obj.t -> Obj.t) = fun t -> fun k -> k
type 't sum_type = Obj.t
let (sum_tag_of_data : sum -> Obj.t -> Obj.t) =
  fun t ->
    match t with
    | Sum
        (uu___, uu___1, uu___2, uu___3, tag_of_data, uu___4, uu___5, uu___6,
         uu___7, uu___8)
        -> tag_of_data
type ('t, 'x) sum_cases = Obj.t
type ('t, 'x) sum_type_of_tag = Obj.t
let (weaken_parse_cases_kind :
  sum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind)
  =
  fun s ->
    fun f ->
      let keys =
        FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
          (match s with
           | Sum
               (uu___, uu___1, e, uu___2, uu___3, uu___4, uu___5, uu___6,
                uu___7, uu___8)
               -> e) in
      LowParse_Spec_Base.glb_list_of
        (fun x ->
           if FStar_List_Tot_Base.mem x keys
           then
             let uu___ = f x in
             match uu___ with | Prims.Mkdtuple2 (k, uu___1) -> k
           else LowParse_Spec_Base.default_parser_kind)
        (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
           (match s with
            | Sum
                (uu___, uu___1, e, uu___2, uu___3, uu___4, uu___5, uu___6,
                 uu___7, uu___8)
                -> e))
let (synth_sum_case : sum -> Obj.t -> Obj.t -> Obj.t) =
  fun s ->
    match s with
    | Sum
        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, synth_case, uu___6,
         uu___7, uu___8)
        -> synth_case






let (parse_sum_kind :
  LowParse_Spec_Base.parser_kind ->
    sum ->
      (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
        LowParse_Spec_Base.parser_kind)
  =
  fun kt ->
    fun t ->
      fun pc ->
        {
          LowParse_Spec_Base.parser_kind_low =
            ((match kt with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low)
               +
               (match weaken_parse_cases_kind t pc with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
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
                  match match weaken_parse_cases_kind t pc with
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
                             LowParse_Spec_Base.parser_kind_metadata =
                               parser_kind_metadata;_}
                             -> parser_kind_high
                   with
                   | FStar_Pervasives_Native.Some y -> y) +
                    (match match weaken_parse_cases_kind t pc with
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
                     | FStar_Pervasives_Native.Some y -> y))
             else FStar_Pervasives_Native.None);
          LowParse_Spec_Base.parser_kind_subkind =
            (if
               (match weaken_parse_cases_kind t pc with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
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
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                    (match weaken_parse_cases_kind t pc with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                 FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
               else
                 if
                   (if
                      (match weaken_parse_cases_kind t pc with
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
                        = (FStar_Pervasives_Native.Some Prims.int_zero)
                    then
                      (match weaken_parse_cases_kind t pc with
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
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                     | uu___ -> FStar_Pervasives_Native.None),
                     (match weaken_parse_cases_kind t pc with
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
                (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
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
                 (match weaken_parse_cases_kind t pc with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
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




let (synth_sum_case_recip : sum -> Obj.t -> Obj.t -> Obj.t) =
  fun s ->
    fun k ->
      fun x ->
        match s with
        | Sum
            (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6,
             synth_case_recip, uu___7, uu___8)
            -> synth_case_recip k x






let make_sum :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      unit ->
        (Obj.t -> 'key) ->
          unit ->
            ('key -> Obj.t -> Obj.t) ->
              ('key -> Obj.t -> Obj.t) -> unit -> unit -> sum
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun e ->
                     fun data ->
                       fun tag_of_data ->
                         fun uu___ ->
                           fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             fun uu___2 ->
                               let uu___2 = Obj.magic uu___2 in
                               fun uu___3 ->
                                 fun uu___4 ->
                                   Obj.magic
                                     (Sum
                                        ((), (), (Obj.magic e), (),
                                          (fun uu___ ->
                                             (Obj.magic tag_of_data) uu___),
                                          uu___, uu___1, uu___2, uu___3,
                                          uu___4))) uu___7 uu___6 uu___5
                    uu___4 uu___3 uu___2 uu___1 uu___
type ('key, 'repr, 'e, 'data, 'taguofudata, 'typeuofutag, 'synthucase,
  'synthucaseurecip, 'x) synth_case_recip_synth_case_post = unit
let make_sum' :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      unit ->
        (Obj.t -> 'key) ->
          unit ->
            ('key -> Obj.t -> Obj.t) ->
              ('key -> Obj.t -> Obj.t) -> unit -> unit -> sum
  =
  fun e ->
    fun data ->
      fun tag_of_data ->
        fun type_of_tag ->
          fun synth_case ->
            fun synth_case_recip ->
              fun synth_case_recip_synth_case ->
                fun synth_case_synth_case_recip ->
                  Sum
                    ((), (), (Obj.magic e), (),
                      (fun uu___ -> (Obj.magic tag_of_data) uu___), (),
                      (fun uu___1 ->
                         fun uu___ -> (Obj.magic synth_case) uu___1 uu___),
                      (fun uu___1 ->
                         fun uu___ ->
                           (Obj.magic synth_case_recip) uu___1 uu___), (),
                      ())
type ('key, 'repr, 'e, 'typeuofuknownutag, 'typeuofuunknownutag,
  'k) dsum_type_of_tag' = Obj.t


type dsum =
  | DSum of unit * unit * (Obj.t, Obj.t) LowParse_Spec_Enum.enum * unit *
  (Obj.t -> (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key) * unit *
  unit *
  ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key -> Obj.t -> Obj.t)
  *
  ((Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key -> Obj.t -> Obj.t)
  * unit * unit 
let (uu___is_DSum : dsum -> Prims.bool) = fun projectee -> true
let (__proj__DSum__item__e : dsum -> (unit, unit) LowParse_Spec_Enum.enum) =
  fun uu___ ->
    (fun projectee ->
       match projectee with
       | DSum
           (key, repr, e, data, tag_of_data, type_of_known_tag,
            type_of_unknown_tag, synth_case, synth_case_recip,
            synth_case_recip_synth_case, synth_case_synth_case_recip)
           -> Obj.magic e) uu___
let (__proj__DSum__item__tag_of_data :
  dsum -> Obj.t -> (unit, unit, unit) LowParse_Spec_Enum.maybe_enum_key) =
  fun uu___1 ->
    fun uu___ ->
      (fun projectee ->
         match projectee with
         | DSum
             (key, repr, e, data, tag_of_data, type_of_known_tag,
              type_of_unknown_tag, synth_case, synth_case_recip,
              synth_case_recip_synth_case, synth_case_synth_case_recip)
             -> Obj.magic tag_of_data) uu___1 uu___
let (__proj__DSum__item__synth_case :
  dsum ->
    (unit, unit, unit) LowParse_Spec_Enum.maybe_enum_key -> Obj.t -> Obj.t)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun projectee ->
           match projectee with
           | DSum
               (key, repr, e, data, tag_of_data, type_of_known_tag,
                type_of_unknown_tag, synth_case, synth_case_recip,
                synth_case_recip_synth_case, synth_case_synth_case_recip)
               -> Obj.magic synth_case) uu___2 uu___1 uu___
let (__proj__DSum__item__synth_case_recip :
  dsum ->
    (unit, unit, unit) LowParse_Spec_Enum.maybe_enum_key -> Obj.t -> Obj.t)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun projectee ->
           match projectee with
           | DSum
               (key, repr, e, data, tag_of_data, type_of_known_tag,
                type_of_unknown_tag, synth_case, synth_case_recip,
                synth_case_recip_synth_case, synth_case_synth_case_recip)
               -> Obj.magic synth_case_recip) uu___2 uu___1 uu___


type 't dsum_key_type = Obj.t
type 't dsum_repr_type = Obj.t
let (dsum_enum : dsum -> (Obj.t, Obj.t) LowParse_Spec_Enum.enum) =
  fun t ->
    match t with
    | DSum
        (uu___, uu___1, e, uu___2, uu___3, uu___4, uu___5, uu___6, uu___7,
         uu___8, uu___9)
        -> e
type 't dsum_key = (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key
type 't dsum_known_key = Obj.t
type 't dsum_unknown_key = Obj.t
type 't dsum_type = Obj.t
let (dsum_tag_of_data :
  dsum -> Obj.t -> (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key) =
  fun t ->
    match t with
    | DSum
        (uu___, uu___1, uu___2, uu___3, tag_of_data, uu___4, uu___5, uu___6,
         uu___7, uu___8, uu___9)
        -> tag_of_data
type ('t, 'x) dsum_cases = Obj.t
type ('t, 'k) dsum_type_of_known_tag = Obj.t
type 't dsum_type_of_unknown_tag = Obj.t
type ('t, 'k) dsum_type_of_tag = Obj.t
let (weaken_parse_dsum_cases_kind :
  dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun s ->
    fun f ->
      fun k' ->
        let keys =
          FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
            (match s with
             | DSum
                 (uu___, uu___1, e, uu___2, uu___3, uu___4, uu___5, uu___6,
                  uu___7, uu___8, uu___9)
                 -> e) in
        match ((match LowParse_Spec_Base.glb_list_of
                        (fun x ->
                           if FStar_List_Tot_Base.mem x keys
                           then
                             let uu___ = f x in
                             match uu___ with
                             | Prims.Mkdtuple2 (k, uu___1) -> k
                           else k')
                        (FStar_List_Tot_Base.map FStar_Pervasives_Native.fst
                           (match s with
                            | DSum
                                (uu___, uu___1, e, uu___2, uu___3, uu___4,
                                 uu___5, uu___6, uu___7, uu___8, uu___9)
                                -> e))
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_metadata),
                (match k' with
                 | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                     LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                     LowParse_Spec_Base.parser_kind_subkind =
                       parser_kind_subkind;
                     LowParse_Spec_Base.parser_kind_metadata =
                       parser_kind_metadata;_}
                     -> parser_kind_metadata))
        with
        | (uu___, FStar_Pervasives_Native.Some
           (LowParse_Spec_Base.ParserKindMetadataFail)) ->
            {
              LowParse_Spec_Base.parser_kind_low =
                ((match LowParse_Spec_Base.glb_list_of
                          (fun x ->
                             if FStar_List_Tot_Base.mem x keys
                             then
                               let uu___1 = f x in
                               match uu___1 with
                               | Prims.Mkdtuple2 (k, uu___2) -> k
                             else k')
                          (FStar_List_Tot_Base.map
                             FStar_Pervasives_Native.fst
                             (match s with
                              | DSum
                                  (uu___1, uu___2, e, uu___3, uu___4, uu___5,
                                   uu___6, uu___7, uu___8, uu___9, uu___10)
                                  -> e))
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_low));
              LowParse_Spec_Base.parser_kind_high =
                ((match LowParse_Spec_Base.glb_list_of
                          (fun x ->
                             if FStar_List_Tot_Base.mem x keys
                             then
                               let uu___1 = f x in
                               match uu___1 with
                               | Prims.Mkdtuple2 (k, uu___2) -> k
                             else k')
                          (FStar_List_Tot_Base.map
                             FStar_Pervasives_Native.fst
                             (match s with
                              | DSum
                                  (uu___1, uu___2, e, uu___3, uu___4, uu___5,
                                   uu___6, uu___7, uu___8, uu___9, uu___10)
                                  -> e))
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_high));
              LowParse_Spec_Base.parser_kind_subkind =
                ((match LowParse_Spec_Base.glb_list_of
                          (fun x ->
                             if FStar_List_Tot_Base.mem x keys
                             then
                               let uu___1 = f x in
                               match uu___1 with
                               | Prims.Mkdtuple2 (k, uu___2) -> k
                             else k')
                          (FStar_List_Tot_Base.map
                             FStar_Pervasives_Native.fst
                             (match s with
                              | DSum
                                  (uu___1, uu___2, e, uu___3, uu___4, uu___5,
                                   uu___6, uu___7, uu___8, uu___9, uu___10)
                                  -> e))
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_subkind));
              LowParse_Spec_Base.parser_kind_metadata =
                ((match match LowParse_Spec_Base.glb_list_of
                                (fun x ->
                                   if FStar_List_Tot_Base.mem x keys
                                   then
                                     let uu___1 = f x in
                                     match uu___1 with
                                     | Prims.Mkdtuple2 (k, uu___2) -> k
                                   else k')
                                (FStar_List_Tot_Base.map
                                   FStar_Pervasives_Native.fst
                                   (match s with
                                    | DSum
                                        (uu___1, uu___2, e, uu___3, uu___4,
                                         uu___5, uu___6, uu___7, uu___8,
                                         uu___9, uu___10)
                                        -> e))
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
                            -> parser_kind_metadata
                  with
                  | FStar_Pervasives_Native.Some
                      (LowParse_Spec_Base.ParserKindMetadataFail) ->
                      FStar_Pervasives_Native.Some
                        LowParse_Spec_Base.ParserKindMetadataFail
                  | uu___1 -> FStar_Pervasives_Native.None))
            }
        | (FStar_Pervasives_Native.Some
           (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
            {
              LowParse_Spec_Base.parser_kind_low =
                ((match k' with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_low));
              LowParse_Spec_Base.parser_kind_high =
                ((match k' with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_high));
              LowParse_Spec_Base.parser_kind_subkind =
                ((match k' with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_subkind));
              LowParse_Spec_Base.parser_kind_metadata =
                FStar_Pervasives_Native.None
            }
        | uu___ ->
            {
              LowParse_Spec_Base.parser_kind_low =
                (if
                   (match LowParse_Spec_Base.glb_list_of
                            (fun x ->
                               if FStar_List_Tot_Base.mem x keys
                               then
                                 let uu___1 = f x in
                                 match uu___1 with
                                 | Prims.Mkdtuple2 (k, uu___2) -> k
                               else k')
                            (FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst
                               (match s with
                                | DSum
                                    (uu___1, uu___2, e, uu___3, uu___4,
                                     uu___5, uu___6, uu___7, uu___8, uu___9,
                                     uu___10)
                                    -> e))
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_low)
                     <
                     ((match k' with
                       | {
                           LowParse_Spec_Base.parser_kind_low =
                             parser_kind_low;
                           LowParse_Spec_Base.parser_kind_high =
                             parser_kind_high;
                           LowParse_Spec_Base.parser_kind_subkind =
                             parser_kind_subkind;
                           LowParse_Spec_Base.parser_kind_metadata =
                             parser_kind_metadata;_}
                           -> parser_kind_low))
                 then
                   (match LowParse_Spec_Base.glb_list_of
                            (fun x ->
                               if FStar_List_Tot_Base.mem x keys
                               then
                                 let uu___1 = f x in
                                 match uu___1 with
                                 | Prims.Mkdtuple2 (k, uu___2) -> k
                               else k')
                            (FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst
                               (match s with
                                | DSum
                                    (uu___1, uu___2, e, uu___3, uu___4,
                                     uu___5, uu___6, uu___7, uu___8, uu___9,
                                     uu___10)
                                    -> e))
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_low)
                 else
                   (match k' with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                      match match LowParse_Spec_Base.glb_list_of
                                    (fun x ->
                                       if FStar_List_Tot_Base.mem x keys
                                       then
                                         let uu___1 = f x in
                                         match uu___1 with
                                         | Prims.Mkdtuple2 (k, uu___2) -> k
                                       else k')
                                    (FStar_List_Tot_Base.map
                                       FStar_Pervasives_Native.fst
                                       (match s with
                                        | DSum
                                            (uu___1, uu___2, e, uu___3,
                                             uu___4, uu___5, uu___6, uu___7,
                                             uu___8, uu___9, uu___10)
                                            -> e))
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
                      | FStar_Pervasives_Native.Some uu___1 -> true
                      | uu___1 -> false
                    then
                      match match k' with
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
                      | FStar_Pervasives_Native.Some uu___1 -> true
                      | uu___1 -> false
                    else false)
                 then
                   (if
                      (match match k' with
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
                       | FStar_Pervasives_Native.Some y -> y) <
                        (match match LowParse_Spec_Base.glb_list_of
                                       (fun x ->
                                          if FStar_List_Tot_Base.mem x keys
                                          then
                                            let uu___1 = f x in
                                            match uu___1 with
                                            | Prims.Mkdtuple2 (k, uu___2) ->
                                                k
                                          else k')
                                       (FStar_List_Tot_Base.map
                                          FStar_Pervasives_Native.fst
                                          (match s with
                                           | DSum
                                               (uu___1, uu___2, e, uu___3,
                                                uu___4, uu___5, uu___6,
                                                uu___7, uu___8, uu___9,
                                                uu___10)
                                               -> e))
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
                         | FStar_Pervasives_Native.Some y -> y)
                    then
                      match LowParse_Spec_Base.glb_list_of
                              (fun x ->
                                 if FStar_List_Tot_Base.mem x keys
                                 then
                                   let uu___1 = f x in
                                   match uu___1 with
                                   | Prims.Mkdtuple2 (k, uu___2) -> k
                                 else k')
                              (FStar_List_Tot_Base.map
                                 FStar_Pervasives_Native.fst
                                 (match s with
                                  | DSum
                                      (uu___1, uu___2, e, uu___3, uu___4,
                                       uu___5, uu___6, uu___7, uu___8,
                                       uu___9, uu___10)
                                      -> e))
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
                    else
                      (match k' with
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
                 else FStar_Pervasives_Native.None);
              LowParse_Spec_Base.parser_kind_subkind =
                (if
                   (match LowParse_Spec_Base.glb_list_of
                            (fun x ->
                               if FStar_List_Tot_Base.mem x keys
                               then
                                 let uu___1 = f x in
                                 match uu___1 with
                                 | Prims.Mkdtuple2 (k, uu___2) -> k
                               else k')
                            (FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst
                               (match s with
                                | DSum
                                    (uu___1, uu___2, e, uu___3, uu___4,
                                     uu___5, uu___6, uu___7, uu___8, uu___9,
                                     uu___10)
                                    -> e))
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_subkind)
                     =
                     ((match k' with
                       | {
                           LowParse_Spec_Base.parser_kind_low =
                             parser_kind_low;
                           LowParse_Spec_Base.parser_kind_high =
                             parser_kind_high;
                           LowParse_Spec_Base.parser_kind_subkind =
                             parser_kind_subkind;
                           LowParse_Spec_Base.parser_kind_metadata =
                             parser_kind_metadata;_}
                           -> parser_kind_subkind))
                 then
                   (match LowParse_Spec_Base.glb_list_of
                            (fun x ->
                               if FStar_List_Tot_Base.mem x keys
                               then
                                 let uu___1 = f x in
                                 match uu___1 with
                                 | Prims.Mkdtuple2 (k, uu___2) -> k
                               else k')
                            (FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst
                               (match s with
                                | DSum
                                    (uu___1, uu___2, e, uu___3, uu___4,
                                     uu___5, uu___6, uu___7, uu___8, uu___9,
                                     uu___10)
                                    -> e))
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_subkind)
                 else FStar_Pervasives_Native.None);
              LowParse_Spec_Base.parser_kind_metadata =
                (if
                   (match LowParse_Spec_Base.glb_list_of
                            (fun x ->
                               if FStar_List_Tot_Base.mem x keys
                               then
                                 let uu___1 = f x in
                                 match uu___1 with
                                 | Prims.Mkdtuple2 (k, uu___2) -> k
                               else k')
                            (FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst
                               (match s with
                                | DSum
                                    (uu___1, uu___2, e, uu___3, uu___4,
                                     uu___5, uu___6, uu___7, uu___8, uu___9,
                                     uu___10)
                                    -> e))
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
                     =
                     ((match k' with
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
                 then
                   (match LowParse_Spec_Base.glb_list_of
                            (fun x ->
                               if FStar_List_Tot_Base.mem x keys
                               then
                                 let uu___1 = f x in
                                 match uu___1 with
                                 | Prims.Mkdtuple2 (k, uu___2) -> k
                               else k')
                            (FStar_List_Tot_Base.map
                               FStar_Pervasives_Native.fst
                               (match s with
                                | DSum
                                    (uu___1, uu___2, e, uu___3, uu___4,
                                     uu___5, uu___6, uu___7, uu___8, uu___9,
                                     uu___10)
                                    -> e))
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
                 else FStar_Pervasives_Native.None)
            }
let (weaken_parse_dsum_cases_kind' :
  dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit -> LowParse_Spec_Base.parser_kind)
  = fun s -> fun f -> fun k' -> fun p -> weaken_parse_dsum_cases_kind s f k'
let (synth_dsum_case :
  dsum ->
    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key -> Obj.t -> Obj.t)
  =
  fun s ->
    match s with
    | DSum
        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6, synth_case,
         uu___7, uu___8, uu___9)
        -> synth_case
let (synth_dsum_case_recip :
  dsum ->
    (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key -> Obj.t -> Obj.t)
  =
  fun s ->
    match s with
    | DSum
        (uu___, uu___1, uu___2, uu___3, uu___4, uu___5, uu___6, uu___7,
         synth_case_recip, uu___8, uu___9)
        -> synth_case_recip



let (parse_dsum_cases_kind :
  dsum ->
    (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (Obj.t, Obj.t, unit) LowParse_Spec_Enum.maybe_enum_key ->
            LowParse_Spec_Base.parser_kind)
  =
  fun s ->
    fun f ->
      fun k ->
        fun g ->
          fun x ->
            match x with
            | LowParse_Spec_Enum.Known k1 -> FStar_Pervasives.dfst (f k1)
            | uu___ -> k




let (parse_dsum_kind :
  LowParse_Spec_Base.parser_kind ->
    dsum ->
      (Obj.t -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2) ->
        LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun kt ->
    fun s ->
      fun f ->
        fun k ->
          {
            LowParse_Spec_Base.parser_kind_low =
              ((match kt with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 +
                 (match weaken_parse_dsum_cases_kind s f k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
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
                    match match weaken_parse_dsum_cases_kind s f k with
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
                               LowParse_Spec_Base.parser_kind_metadata =
                                 parser_kind_metadata;_}
                               -> parser_kind_high
                     with
                     | FStar_Pervasives_Native.Some y -> y) +
                      (match match weaken_parse_dsum_cases_kind s f k with
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
                       | FStar_Pervasives_Native.Some y -> y))
               else FStar_Pervasives_Native.None);
            LowParse_Spec_Base.parser_kind_subkind =
              (if
                 (match weaken_parse_dsum_cases_kind s f k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
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
                      (match weaken_parse_dsum_cases_kind s f k with
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
                        (match weaken_parse_dsum_cases_kind s f k with
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
                          = (FStar_Pervasives_Native.Some Prims.int_zero)
                      then
                        (match weaken_parse_dsum_cases_kind s f k with
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
              (match ((match kt with
                       | {
                           LowParse_Spec_Base.parser_kind_low =
                             parser_kind_low;
                           LowParse_Spec_Base.parser_kind_high =
                             parser_kind_high;
                           LowParse_Spec_Base.parser_kind_subkind =
                             parser_kind_subkind;
                           LowParse_Spec_Base.parser_kind_metadata =
                             parser_kind_metadata;_}
                           -> parser_kind_metadata),
                       (match weaken_parse_dsum_cases_kind s f k with
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
                  (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
                   (match kt with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
               | (uu___, FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                   (match weaken_parse_dsum_cases_kind s f k with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                   (match kt with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
               | uu___ -> FStar_Pervasives_Native.None)
          }











type ('key, 'repr, 'e, 'data, 'taguofudata, 'typeuofuknownutag,
  'typeuofuunknownutag, 'synthucase, 'synthucaseurecip,
  'x) synth_dsum_case_recip_synth_case_known_post = unit
type ('key, 'repr, 'e, 'data, 'taguofudata, 'typeuofuknownutag,
  'typeuofuunknownutag, 'synthucase, 'synthucaseurecip,
  'x) synth_dsum_case_recip_synth_case_unknown_post = unit
let make_dsum :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      unit ->
        (Obj.t -> ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key) ->
          unit ->
            unit ->
              (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                 Obj.t -> Obj.t)
                ->
                (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                   Obj.t -> Obj.t)
                  -> unit -> unit -> dsum
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
                    (fun e ->
                       fun data ->
                         fun tag_of_data ->
                           fun uu___ ->
                             fun uu___1 ->
                               fun uu___2 ->
                                 let uu___2 = Obj.magic uu___2 in
                                 fun uu___3 ->
                                   let uu___3 = Obj.magic uu___3 in
                                   fun uu___4 ->
                                     fun uu___5 ->
                                       Obj.magic
                                         (DSum
                                            ((), (), (Obj.magic e), (),
                                              (fun uu___ ->
                                                 (Obj.magic tag_of_data)
                                                   uu___), uu___, uu___1,
                                              uu___2, uu___3, uu___4, uu___5)))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let make_dsum' :
  'key 'repr .
    ('key, 'repr) LowParse_Spec_Enum.enum ->
      unit ->
        (Obj.t -> ('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key) ->
          unit ->
            unit ->
              (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                 Obj.t -> Obj.t)
                ->
                (('key, 'repr, unit) LowParse_Spec_Enum.maybe_enum_key ->
                   Obj.t -> Obj.t)
                  -> unit -> unit -> unit -> dsum
  =
  fun e ->
    fun data ->
      fun tag_of_data ->
        fun type_of_known_tag ->
          fun type_of_unknown_tag ->
            fun synth_case ->
              fun synth_case_recip ->
                fun synth_case_recip_synth_case_known ->
                  fun synth_case_recip_synth_case_unknown ->
                    fun uu___ ->
                      DSum
                        ((), (), (Obj.magic e), (),
                          (fun uu___ -> (Obj.magic tag_of_data) uu___), (),
                          (),
                          (fun uu___1 ->
                             fun uu___ -> (Obj.magic synth_case) uu___1 uu___),
                          (fun uu___1 ->
                             fun uu___ ->
                               (Obj.magic synth_case_recip) uu___1 uu___),
                          (), uu___)

