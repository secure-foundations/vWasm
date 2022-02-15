open Prims
type ('t, 'n, 's) array_pred = unit
let (fldata_array_precond :
  LowParse_Spec_Base.parser_kind -> Prims.nat -> Prims.nat -> Prims.bool) =
  fun k ->
    fun array_byte_size ->
      fun elem_count ->
        ((((match k with
            | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                LowParse_Spec_Base.parser_kind_metadata =
                  parser_kind_metadata;_}
                -> parser_kind_subkind)
             = (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong))
            &&
            ((match k with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low)
               > Prims.int_zero))
           &&
           ((match k with
             | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                 LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                 LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                 LowParse_Spec_Base.parser_kind_metadata =
                   parser_kind_metadata;_}
                 -> parser_kind_high)
              =
              (FStar_Pervasives_Native.Some
                 (match k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_low))))
          &&
          ((elem_count *
              (match k with
               | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                   LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                   LowParse_Spec_Base.parser_kind_subkind =
                     parser_kind_subkind;
                   LowParse_Spec_Base.parser_kind_metadata =
                     parser_kind_metadata;_}
                   -> parser_kind_low))
             = array_byte_size)

type ('t, 'n) array = 't Prims.list
let (fldata_to_array :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          Prims.nat ->
            Prims.nat ->
              unit ->
                (unit, Obj.t Prims.list, unit, unit, unit)
                  LowParse_Spec_FLData.parse_fldata_strong_t ->
                  Obj.t Prims.list)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s -> fun array_byte_size -> fun elem_count -> fun u -> fun x -> x

let (parse_array_kind' : Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun array_byte_size ->
    {
      LowParse_Spec_Base.parser_kind_low = array_byte_size;
      LowParse_Spec_Base.parser_kind_high =
        (FStar_Pervasives_Native.Some array_byte_size);
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }


let (parse_array_kind :
  LowParse_Spec_Base.parser_kind ->
    Prims.nat -> Prims.nat -> LowParse_Spec_Base.parser_kind)
  =
  fun k ->
    fun array_byte_size ->
      fun elem_count ->
        if
          (((((match k with
               | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                   LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                   LowParse_Spec_Base.parser_kind_subkind =
                     parser_kind_subkind;
                   LowParse_Spec_Base.parser_kind_metadata =
                     parser_kind_metadata;_}
                   -> parser_kind_subkind)
                =
                (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong))
               &&
               ((match k with
                 | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                     LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                     LowParse_Spec_Base.parser_kind_subkind =
                       parser_kind_subkind;
                     LowParse_Spec_Base.parser_kind_metadata =
                       parser_kind_metadata;_}
                     -> parser_kind_low)
                  > Prims.int_zero))
              &&
              ((match k with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_high)
                 =
                 (FStar_Pervasives_Native.Some
                    (match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_low))))
             &&
             ((elem_count *
                 (match k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_low))
                = array_byte_size))
            &&
            ((match k with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_metadata)
               =
               (FStar_Pervasives_Native.Some
                  LowParse_Spec_Base.ParserKindMetadataTotal))
        then
          {
            LowParse_Spec_Base.parser_kind_low = array_byte_size;
            LowParse_Spec_Base.parser_kind_high =
              (FStar_Pervasives_Native.Some array_byte_size);
            LowParse_Spec_Base.parser_kind_subkind =
              (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
            LowParse_Spec_Base.parser_kind_metadata =
              (FStar_Pervasives_Native.Some
                 LowParse_Spec_Base.ParserKindMetadataTotal)
          }
        else
          {
            LowParse_Spec_Base.parser_kind_low = array_byte_size;
            LowParse_Spec_Base.parser_kind_high =
              (FStar_Pervasives_Native.Some array_byte_size);
            LowParse_Spec_Base.parser_kind_subkind =
              (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
            LowParse_Spec_Base.parser_kind_metadata =
              FStar_Pervasives_Native.None
          }



let (array_to_fldata :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          Prims.nat ->
            Prims.nat ->
              unit ->
                Obj.t Prims.list ->
                  (unit, Obj.t Prims.list, unit, unit, unit)
                    LowParse_Spec_FLData.parse_fldata_strong_t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s -> fun array_byte_size -> fun elem_count -> fun u -> fun x -> x




type ('t, 'min, 'max, 's) vlarray_pred = unit



type ('t, 'min, 'max) vlarray = 't Prims.list
let (vldata_to_vlarray :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat ->
                  unit ->
                    (unit, unit, unit, Obj.t Prims.list, unit, unit)
                      LowParse_Spec_VLData.parse_bounded_vldata_strong_t ->
                      Obj.t Prims.list)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min -> fun elem_count_max -> fun u -> fun x -> x

let (parse_vlarray_kind :
  Prims.nat -> Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          ((if array_byte_size_max < (Prims.of_int (256))
            then Prims.int_one
            else
              if array_byte_size_max < (Prims.parse_int "65536")
              then (Prims.of_int (2))
              else
                if array_byte_size_max < (Prims.parse_int "16777216")
                then (Prims.of_int (3))
                else (Prims.of_int (4)))
             +
             (if Prims.int_zero > array_byte_size_min
              then Prims.int_zero
              else array_byte_size_min));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             ((if array_byte_size_max < (Prims.of_int (256))
               then Prims.int_one
               else
                 if array_byte_size_max < (Prims.parse_int "65536")
                 then (Prims.of_int (2))
                 else
                   if array_byte_size_max < (Prims.parse_int "16777216")
                   then (Prims.of_int (3))
                   else (Prims.of_int (4)))
                +
                (if
                   array_byte_size_max <
                     ((if Prims.int_zero > array_byte_size_min
                       then Prims.int_zero
                       else array_byte_size_min))
                 then
                   (if Prims.int_zero > array_byte_size_min
                    then Prims.int_zero
                    else array_byte_size_min)
                 else array_byte_size_max)));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }



let (vlarray_to_vldata :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat ->
                  unit ->
                    Obj.t Prims.list ->
                      (unit, unit, unit, Obj.t Prims.list, unit, unit)
                        LowParse_Spec_VLData.parse_bounded_vldata_strong_t)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min -> fun elem_count_max -> fun u -> fun x -> x


