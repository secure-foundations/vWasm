open Prims
type ('min, 'max, 'ht, 'pt, 'dlf, 'pk, 'pp, 'ps) parse_deplen_data_t =
  ('ht * 'pt)

let (synth_deplen_data :
  Prims.nat ->
    Prims.nat ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  Obj.t ->
                    Obj.t ->
                      (unit, unit, Obj.t, Obj.t, unit, unit, unit, unit)
                        parse_deplen_data_t)
  =
  fun min ->
    fun max ->
      fun ht ->
        fun pt ->
          fun dlf -> fun pk -> fun pp -> fun ps -> fun h -> fun x -> (h, x)
let (parse_deplen_payload_kind :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun k ->
        {
          LowParse_Spec_Base.parser_kind_low =
            (if
               (match k with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 > min
             then
               match k with
               | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                   LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                   LowParse_Spec_Base.parser_kind_subkind =
                     parser_kind_subkind;
                   LowParse_Spec_Base.parser_kind_metadata =
                     parser_kind_metadata;_}
                   -> parser_kind_low
             else min);
          LowParse_Spec_Base.parser_kind_high =
            (FStar_Pervasives_Native.Some
               (if
                  (match match k with
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
                   | FStar_Pervasives_Native.None -> max
                   | FStar_Pervasives_Native.Some kmax ->
                       if kmax < max then kmax else max)
                    <
                    ((if
                        (match k with
                         | {
                             LowParse_Spec_Base.parser_kind_low =
                               parser_kind_low;
                             LowParse_Spec_Base.parser_kind_high =
                               parser_kind_high;
                             LowParse_Spec_Base.parser_kind_subkind =
                               parser_kind_subkind;
                             LowParse_Spec_Base.parser_kind_metadata =
                               parser_kind_metadata;_}
                             -> parser_kind_low)
                          > min
                      then
                        match k with
                        | {
                            LowParse_Spec_Base.parser_kind_low =
                              parser_kind_low;
                            LowParse_Spec_Base.parser_kind_high =
                              parser_kind_high;
                            LowParse_Spec_Base.parser_kind_subkind =
                              parser_kind_subkind;
                            LowParse_Spec_Base.parser_kind_metadata =
                              parser_kind_metadata;_}
                            -> parser_kind_low
                      else min))
                then
                  (if
                     (match k with
                      | {
                          LowParse_Spec_Base.parser_kind_low =
                            parser_kind_low;
                          LowParse_Spec_Base.parser_kind_high =
                            parser_kind_high;
                          LowParse_Spec_Base.parser_kind_subkind =
                            parser_kind_subkind;
                          LowParse_Spec_Base.parser_kind_metadata =
                            parser_kind_metadata;_}
                          -> parser_kind_low)
                       > min
                   then
                     match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_low
                   else min)
                else
                  (match match k with
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
                   | FStar_Pervasives_Native.None -> max
                   | FStar_Pervasives_Native.Some kmax ->
                       if kmax < max then kmax else max)));
          LowParse_Spec_Base.parser_kind_subkind =
            (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
          LowParse_Spec_Base.parser_kind_metadata =
            (match match k with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
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
        }


let (parse_deplen_kind :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun hk ->
        fun pk ->
          {
            LowParse_Spec_Base.parser_kind_low =
              ((match hk with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 +
                 (match parse_deplen_payload_kind min max pk with
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
                    match match hk with
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
                    match match parse_deplen_payload_kind min max pk with
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
                   ((match match hk with
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
                      (match match parse_deplen_payload_kind min max pk with
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
                 (match parse_deplen_payload_kind min max pk with
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
                      (match hk with
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
                      (match parse_deplen_payload_kind min max pk with
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
                        (match parse_deplen_payload_kind min max pk with
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
                        (match parse_deplen_payload_kind min max pk with
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
                     (match hk with
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
              (match ((match hk with
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
                       (match parse_deplen_payload_kind min max pk with
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
                   (match hk with
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
                   (match parse_deplen_payload_kind min max pk with
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
                   (match hk with
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



let (synth_deplen_data_recip :
  Prims.nat ->
    Prims.nat ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  Obj.t ->
                    (unit, unit, Obj.t, Obj.t, unit, unit, unit, unit)
                      parse_deplen_data_t -> Obj.t)
  =
  fun min ->
    fun max ->
      fun ht ->
        fun pt ->
          fun dlf ->
            fun pk ->
              fun pp ->
                fun ps -> fun h -> fun x -> FStar_Pervasives_Native.snd x



