open Prims

let (synth_bounded_vlgen_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit -> unit -> unit -> FStar_UInt32.t -> Obj.t -> Obj.t)
  =
  fun min ->
    fun max -> fun k -> fun t -> fun p -> fun s -> fun sz -> fun x -> x
let (parse_bounded_vlgen_payload_kind :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun k ->
        {
          LowParse_Spec_Base.parser_kind_low =
            (if
               (match k with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 > min
             then
               match k with
               | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                   LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                   LowParse_Spec_Base.parser_kind_subkind =
                     parser_kind_subkind;
                   LowParse_Spec_Base.parser_kind_metadata =
                     parser_kind_metadata;_}
                   -> parser_kind_low
             else min);
          LowParse_Spec_Base.parser_kind_high =
            (FStar_Pervasives_Native.Some
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
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                       if kmax < max then kmax else max)));
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


let (parse_bounded_vlgen_kind :
  LowParse_Spec_Base.parser_kind ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun sk ->
    fun min ->
      fun max ->
        fun k ->
          {
            LowParse_Spec_Base.parser_kind_low =
              ((match sk with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 +
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
              (if
                 (if
                    match match sk with
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
                    | FStar_Pervasives_Native.Some uu___ -> true
                    | uu___ -> false
                  then true
                  else false)
               then
                 FStar_Pervasives_Native.Some
                   ((match match sk with
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
                     | FStar_Pervasives_Native.Some y -> y) +
                      ((if
                          (match match k with
                                 | {
                                     LowParse_Spec_Base.parser_kind_low =
                                       parser_kind_low;
                                     LowParse_Spec_Base.parser_kind_high =
                                       parser_kind_high;
                                     LowParse_Spec_Base.parser_kind_subkind =
                                       parser_kind_subkind;
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
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
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
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
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
                                     -> parser_kind_high
                           with
                           | FStar_Pervasives_Native.None -> max
                           | FStar_Pervasives_Native.Some kmax ->
                               if kmax < max then kmax else max))))
               else FStar_Pervasives_Native.None);
            LowParse_Spec_Base.parser_kind_subkind =
              (if
                 (if
                    (match sk with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_subkind)
                      =
                      (FStar_Pervasives_Native.Some
                         LowParse_Spec_Base.ParserStrong)
                  then true
                  else false)
               then
                 FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
               else
                 if
                   (if
                      (FStar_Pervasives_Native.Some
                         (if
                            (match match k with
                                   | {
                                       LowParse_Spec_Base.parser_kind_low =
                                         parser_kind_low;
                                       LowParse_Spec_Base.parser_kind_high =
                                         parser_kind_high;
                                       LowParse_Spec_Base.parser_kind_subkind
                                         = parser_kind_subkind;
                                       LowParse_Spec_Base.parser_kind_metadata
                                         = parser_kind_metadata;_}
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
                                       LowParse_Spec_Base.parser_kind_subkind
                                         = parser_kind_subkind;
                                       LowParse_Spec_Base.parser_kind_metadata
                                         = parser_kind_metadata;_}
                                       -> parser_kind_low)
                                    > min
                                then
                                  match k with
                                  | {
                                      LowParse_Spec_Base.parser_kind_low =
                                        parser_kind_low;
                                      LowParse_Spec_Base.parser_kind_high =
                                        parser_kind_high;
                                      LowParse_Spec_Base.parser_kind_subkind
                                        = parser_kind_subkind;
                                      LowParse_Spec_Base.parser_kind_metadata
                                        = parser_kind_metadata;_}
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
                                       LowParse_Spec_Base.parser_kind_subkind
                                         = parser_kind_subkind;
                                       LowParse_Spec_Base.parser_kind_metadata
                                         = parser_kind_metadata;_}
                                       -> parser_kind_high
                             with
                             | FStar_Pervasives_Native.None -> max
                             | FStar_Pervasives_Native.Some kmax ->
                                 if kmax < max then kmax else max)))
                        = (FStar_Pervasives_Native.Some Prims.int_zero)
                    then true
                    else false)
                 then
                   (match sk with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_subkind)
                 else FStar_Pervasives_Native.None);
            LowParse_Spec_Base.parser_kind_metadata =
              (match ((match sk with
                       | {
                           LowParse_Spec_Base.parser_kind_low =
                             parser_kind_low;
                           LowParse_Spec_Base.parser_kind_high =
                             parser_kind_high;
                           LowParse_Spec_Base.parser_kind_subkind =
                             parser_kind_subkind;
                           LowParse_Spec_Base.parser_kind_metadata =
                             parser_kind_metadata;_}
                           -> parser_kind_metadata),
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
                                  -> parser_kind_metadata
                        with
                        | FStar_Pervasives_Native.Some
                            (LowParse_Spec_Base.ParserKindMetadataFail) ->
                            FStar_Pervasives_Native.Some
                              LowParse_Spec_Base.ParserKindMetadataFail
                        | uu___ -> FStar_Pervasives_Native.None))
               with
               | (FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
                   (match sk with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
               | (uu___, FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataFail)) ->
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
                              -> parser_kind_metadata
                    with
                    | FStar_Pervasives_Native.Some
                        (LowParse_Spec_Base.ParserKindMetadataFail) ->
                        FStar_Pervasives_Native.Some
                          LowParse_Spec_Base.ParserKindMetadataFail
                    | uu___1 -> FStar_Pervasives_Native.None)
               | (FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataTotal),
                  FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataTotal)) ->
                   (match sk with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
               | uu___ -> FStar_Pervasives_Native.None)
          }



let (synth_vlgen :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit -> unit -> unit -> Obj.t -> Obj.t)
  = fun min -> fun max -> fun k -> fun t -> fun p -> fun s -> fun x -> x



let (synth_bounded_vlgen_payload_recip :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit -> unit -> unit -> FStar_UInt32.t -> Obj.t -> Obj.t)
  =
  fun min ->
    fun max -> fun k -> fun t -> fun p -> fun s -> fun sz -> fun x -> x




let (synth_vlgen_recip :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit -> unit -> unit -> Obj.t -> Obj.t)
  = fun min -> fun max -> fun k -> fun t -> fun p -> fun s -> fun x -> x

