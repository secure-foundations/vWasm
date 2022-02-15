open Prims
let (parse_seq_all_bytes_kind : LowParse_Spec_Base.parser_kind') =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high = FStar_Pervasives_Native.None;
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserConsumesAll);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }








type ('min, 'max, 'x) parse_bounded_seq_vlbytes_pred = unit
type ('min, 'max) parse_bounded_seq_vlbytes_t = LowParse_Bytes.bytes
let (synth_bounded_seq_vlbytes :
  Prims.nat ->
    Prims.nat ->
      (unit, unit, unit, LowParse_Bytes.bytes, unit, unit)
        LowParse_Spec_VLData.parse_bounded_vldata_strong_t ->
        (unit, unit) parse_bounded_seq_vlbytes_t)
  = fun min -> fun max -> fun x -> x


