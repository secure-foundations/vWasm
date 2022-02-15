open Prims






let (parse_all_bytes_kind : LowParse_Spec_Base.parser_kind') =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high = FStar_Pervasives_Native.None;
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserConsumesAll);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }








type ('min, 'max, 'x) parse_bounded_vlbytes_pred = unit
type ('min, 'max) parse_bounded_vlbytes_t = FStar_Bytes.bytes
let (parse_bounded_vlbytes_kind :
  Prims.nat -> Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          ((if max < (Prims.of_int (256))
            then Prims.int_one
            else
              if max < (Prims.parse_int "65536")
              then (Prims.of_int (2))
              else
                if max < (Prims.parse_int "16777216")
                then (Prims.of_int (3))
                else (Prims.of_int (4)))
             + (if Prims.int_zero > min then Prims.int_zero else min));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             ((if max < (Prims.of_int (256))
               then Prims.int_one
               else
                 if max < (Prims.parse_int "65536")
                 then (Prims.of_int (2))
                 else
                   if max < (Prims.parse_int "16777216")
                   then (Prims.of_int (3))
                   else (Prims.of_int (4)))
                +
                (if
                   max <
                     ((if Prims.int_zero > min then Prims.int_zero else min))
                 then (if Prims.int_zero > min then Prims.int_zero else min)
                 else max)));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }
let (synth_bounded_vlbytes :
  Prims.nat ->
    Prims.nat ->
      (unit, unit, unit, FStar_Bytes.bytes, unit, unit)
        LowParse_Spec_VLData.parse_bounded_vldata_strong_t ->
        (unit, unit) parse_bounded_vlbytes_t)
  = fun min -> fun max -> fun x -> x




let (synth_bounded_vlbytes_recip :
  Prims.nat ->
    Prims.nat ->
      (unit, unit) parse_bounded_vlbytes_t ->
        (unit, unit, unit, FStar_Bytes.bytes, unit, unit)
          LowParse_Spec_VLData.parse_bounded_vldata_strong_t)
  = fun min -> fun max -> fun x -> x






