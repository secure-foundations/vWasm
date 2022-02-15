open Prims
let (parse_vldata_payload_size :
  LowParse_Spec_BoundedInt.integer_size -> Prims.nat) =
  fun sz ->
    match sz with
    | uu___ when uu___ = Prims.int_one -> (Prims.of_int (255))
    | uu___ when uu___ = (Prims.of_int (2)) -> (Prims.parse_int "65535")
    | uu___ when uu___ = (Prims.of_int (3)) -> (Prims.parse_int "16777215")
    | uu___ when uu___ = (Prims.of_int (4)) -> (Prims.parse_int "4294967295")
let (parse_vldata_payload_kind :
  LowParse_Spec_BoundedInt.integer_size ->
    LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun sz ->
    fun k ->
      {
        LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some (parse_vldata_payload_size sz));
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


let (parse_vldata_gen_kind :
  LowParse_Spec_BoundedInt.integer_size ->
    LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun sz ->
    fun k ->
      {
        LowParse_Spec_Base.parser_kind_low = sz;
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some (sz + (parse_vldata_payload_size sz)));
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








let (parse_bounded_vldata_strong_kind :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          {
            LowParse_Spec_Base.parser_kind_low =
              (l +
                 (if
                    (match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_low
                  else min));
            LowParse_Spec_Base.parser_kind_high =
              (FStar_Pervasives_Native.Some
                 (l +
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
                              LowParse_Spec_Base.parser_kind_low =
                                parser_kind_low;
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
                            if kmax < max then kmax else max))));
            LowParse_Spec_Base.parser_kind_subkind =
              (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
            LowParse_Spec_Base.parser_kind_metadata =
              (match match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
          }






type ('min, 'max, 'k, 't, 'p, 's, 'x) parse_bounded_vldata_strong_pred = unit
type ('min, 'max, 'k, 't, 'p, 's) parse_bounded_vldata_strong_t = 't
















