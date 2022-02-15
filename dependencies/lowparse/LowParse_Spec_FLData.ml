open Prims


let (parse_fldata_kind :
  Prims.nat ->
    LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun sz ->
    fun k ->
      {
        LowParse_Spec_Base.parser_kind_low = sz;
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some sz);
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



type ('k, 't, 'p, 's, 'sz, 'x) parse_fldata_strong_pred = unit
type ('k, 't, 'p, 's, 'sz) parse_fldata_strong_t = 't



