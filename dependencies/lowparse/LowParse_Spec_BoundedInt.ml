open Prims
type integer_size = Prims.nat

type ('i, 'u) bounded_integer_prop = unit

type 'i bounded_integer = FStar_UInt32.t
let (parse_bounded_integer_kind :
  integer_size -> LowParse_Spec_Base.parser_kind) =
  fun i ->
    {
      LowParse_Spec_Base.parser_kind_low = i;
      LowParse_Spec_Base.parser_kind_high = (FStar_Pervasives_Native.Some i);
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata =
        (FStar_Pervasives_Native.Some
           LowParse_Spec_Base.ParserKindMetadataTotal)
    }













let (synth_u16_le : FStar_UInt32.t -> FStar_UInt16.t) =
  fun x -> FStar_Int_Cast.uint32_to_uint16 x


let (synth_u32_le : FStar_UInt32.t -> FStar_UInt32.t) = fun x -> x




let (synth_u16_le_recip : FStar_UInt16.t -> FStar_UInt32.t) =
  fun x -> FStar_Int_Cast.uint16_to_uint32 x


let (synth_u32_le_recip : FStar_UInt32.t -> FStar_UInt32.t) = fun x -> x

let (log256' : Prims.nat -> integer_size) =
  fun n ->
    if n < (Prims.of_int (256))
    then Prims.int_one
    else
      if n < (Prims.parse_int "65536")
      then (Prims.of_int (2))
      else
        if n < (Prims.parse_int "16777216")
        then (Prims.of_int (3))
        else (Prims.of_int (4))

type ('min, 'max) bounded_int32 = FStar_UInt32.t
let (parse_bounded_int32_kind : Prims.nat -> LowParse_Spec_Base.parser_kind)
  =
  fun max ->
    {
      LowParse_Spec_Base.parser_kind_low =
        (if max < (Prims.of_int (256))
         then Prims.int_one
         else
           if max < (Prims.parse_int "65536")
           then (Prims.of_int (2))
           else
             if max < (Prims.parse_int "16777216")
             then (Prims.of_int (3))
             else (Prims.of_int (4)));
      LowParse_Spec_Base.parser_kind_high =
        (FStar_Pervasives_Native.Some
           (if max < (Prims.of_int (256))
            then Prims.int_one
            else
              if max < (Prims.parse_int "65536")
              then (Prims.of_int (2))
              else
                if max < (Prims.parse_int "16777216")
                then (Prims.of_int (3))
                else (Prims.of_int (4))));
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }




let (parse_bounded_int32_fixed_size_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = (Prims.of_int (4));
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (4)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }

