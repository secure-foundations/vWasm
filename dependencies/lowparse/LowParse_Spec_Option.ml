open Prims
let (parse_option_kind :
  LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind) =
  fun k ->
    {
      LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
      LowParse_Spec_Base.parser_kind_high =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_high);
      LowParse_Spec_Base.parser_kind_subkind = FStar_Pervasives_Native.None;
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }





