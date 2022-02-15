open Prims
type 'v constint32 = FStar_UInt32.t
let (parse_constint32le_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = (Prims.of_int (4));
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (4)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }
let (decode_constint32le :
  Prims.nat ->
    LowParse_Bytes.bytes -> unit constint32 FStar_Pervasives_Native.option)
  =
  fun v ->
    fun b ->
      let v' = LowParse_Spec_Int32le.decode_int32le b in
      if (FStar_UInt32.v v') = v
      then FStar_Pervasives_Native.Some v'
      else FStar_Pervasives_Native.None






