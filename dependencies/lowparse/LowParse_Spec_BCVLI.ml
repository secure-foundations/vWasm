open Prims
let (parse_bcvli_kind : LowParse_Spec_Base.parser_kind') =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_one;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (5)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }
let (parse_bcvli_payload_kind : LowParse_Spec_Base.parser_kind') =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (4)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }








let (parse_bounded_bcvli_size : Prims.nat -> Prims.nat) =
  fun max ->
    if max <= (Prims.of_int (252))
    then Prims.int_one
    else
      if max <= (Prims.parse_int "65535")
      then (Prims.of_int (3))
      else (Prims.of_int (5))
let (parse_bounded_bcvli_kind :
  Prims.nat -> Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          (if min <= (Prims.of_int (252))
           then Prims.int_one
           else
             if min <= (Prims.parse_int "65535")
             then (Prims.of_int (3))
             else (Prims.of_int (5)));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             (if max <= (Prims.of_int (252))
              then Prims.int_one
              else
                if max <= (Prims.parse_int "65535")
                then (Prims.of_int (3))
                else (Prims.of_int (5))));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }






