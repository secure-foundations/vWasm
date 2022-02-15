open Prims
let (parse_u8_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_one;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some Prims.int_one);
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some
         LowParse_Spec_Base.ParserKindMetadataTotal)
  }








let (parse_u16_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = (Prims.of_int (2));
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (2)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some
         LowParse_Spec_Base.ParserKindMetadataTotal)
  }






let (parse_u32_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = (Prims.of_int (4));
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (4)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some
         LowParse_Spec_Base.ParserKindMetadataTotal)
  }






let (parse_u64_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = (Prims.of_int (8));
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (8)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some
         LowParse_Spec_Base.ParserKindMetadataTotal)
  }











