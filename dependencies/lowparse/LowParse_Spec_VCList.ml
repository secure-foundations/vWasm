open Prims
type ('n, 't) nlist = 't Prims.list
let nlist_nil : 't . unit -> 't Prims.list = fun uu___ -> []

let nlist_cons : 't . Prims.nat -> 't -> 't Prims.list -> 't Prims.list =
  fun n -> fun a -> fun q -> a :: q
let nlist_destruct : 't . Prims.nat -> 't Prims.list -> ('t * 't Prims.list)
  = fun n -> fun x -> match x with | a::q -> (a, q)

let (mul : Prims.int -> Prims.int -> Prims.int) = ( * )
let synth_nlist : 't . Prims.nat -> ('t * 't Prims.list) -> 't Prims.list =
  fun n -> fun xy -> match xy with | (x, y) -> x :: y
let synth_nlist_recip :
  't . Prims.nat -> 't Prims.list -> ('t * 't Prims.list) =
  fun n -> fun xy -> match xy with | a::q -> (a, q)







let (parse_nlist_kind :
  Prims.nat ->
    LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun n ->
    fun k ->
      {
        LowParse_Spec_Base.parser_kind_low =
          (n *
             (match k with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low));
        LowParse_Spec_Base.parser_kind_high =
          (match match k with
                 | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                     LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                     LowParse_Spec_Base.parser_kind_subkind =
                       parser_kind_subkind;
                     LowParse_Spec_Base.parser_kind_metadata =
                       parser_kind_metadata;_}
                     -> parser_kind_high
           with
           | FStar_Pervasives_Native.None ->
               if n = Prims.int_zero
               then FStar_Pervasives_Native.Some Prims.int_zero
               else FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some b ->
               FStar_Pervasives_Native.Some (n * b));
        LowParse_Spec_Base.parser_kind_subkind =
          (if n = Prims.int_zero
           then FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
           else
             (match k with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_subkind));
        LowParse_Spec_Base.parser_kind_metadata =
          (if n = Prims.int_zero
           then
             FStar_Pervasives_Native.Some
               LowParse_Spec_Base.ParserKindMetadataTotal
           else
             (match k with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_metadata))
      }








type ('min, 'max) bounded_count = FStar_UInt32.t
let (parse_vclist_payload_kind :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun k ->
        {
          LowParse_Spec_Base.parser_kind_low =
            (min *
               (match k with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low));
          LowParse_Spec_Base.parser_kind_high =
            (match match k with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_high
             with
             | FStar_Pervasives_Native.None ->
                 if max = Prims.int_zero
                 then FStar_Pervasives_Native.Some Prims.int_zero
                 else FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some b ->
                 FStar_Pervasives_Native.Some (max * b));
          LowParse_Spec_Base.parser_kind_subkind =
            (if max = Prims.int_zero
             then
               FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
             else
               if
                 (min = Prims.int_zero) &&
                   ((match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_subkind)
                      <>
                      (FStar_Pervasives_Native.Some
                         LowParse_Spec_Base.ParserStrong))
               then FStar_Pervasives_Native.None
               else
                 (match k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_subkind));
          LowParse_Spec_Base.parser_kind_metadata =
            (if max = Prims.int_zero
             then
               FStar_Pervasives_Native.Some
                 LowParse_Spec_Base.ParserKindMetadataTotal
             else
               if
                 (min = Prims.int_zero) &&
                   ((match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_metadata)
                      <>
                      (FStar_Pervasives_Native.Some
                         LowParse_Spec_Base.ParserKindMetadataTotal))
               then FStar_Pervasives_Native.None
               else
                 (match k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_metadata))
        }

let (synth_vclist_payload :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t -> unit -> Obj.t Prims.list -> Obj.t Prims.list)
  = fun min -> fun max -> fun n -> fun t -> fun x -> x

let (parse_vclist_kind :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun lk ->
        fun k ->
          {
            LowParse_Spec_Base.parser_kind_low =
              ((match lk with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 +
                 (min *
                    (match k with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_low)));
            LowParse_Spec_Base.parser_kind_high =
              (if
                 (if
                    match match lk with
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
                  then
                    match match match k with
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
                          | FStar_Pervasives_Native.None ->
                              if max = Prims.int_zero
                              then
                                FStar_Pervasives_Native.Some Prims.int_zero
                              else FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              FStar_Pervasives_Native.Some (max * b)
                    with
                    | FStar_Pervasives_Native.Some uu___ -> true
                    | uu___ -> false
                  else false)
               then
                 FStar_Pervasives_Native.Some
                   ((match match lk with
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
                      (match match match k with
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
                             | FStar_Pervasives_Native.None ->
                                 if max = Prims.int_zero
                                 then
                                   FStar_Pervasives_Native.Some
                                     Prims.int_zero
                                 else FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some b ->
                                 FStar_Pervasives_Native.Some (max * b)
                       with
                       | FStar_Pervasives_Native.Some y -> y))
               else FStar_Pervasives_Native.None);
            LowParse_Spec_Base.parser_kind_subkind =
              (if
                 (if max = Prims.int_zero
                  then
                    FStar_Pervasives_Native.Some
                      LowParse_Spec_Base.ParserStrong
                  else
                    if
                      (min = Prims.int_zero) &&
                        ((match k with
                          | {
                              LowParse_Spec_Base.parser_kind_low =
                                parser_kind_low;
                              LowParse_Spec_Base.parser_kind_high =
                                parser_kind_high;
                              LowParse_Spec_Base.parser_kind_subkind =
                                parser_kind_subkind;
                              LowParse_Spec_Base.parser_kind_metadata =
                                parser_kind_metadata;_}
                              -> parser_kind_subkind)
                           <>
                           (FStar_Pervasives_Native.Some
                              LowParse_Spec_Base.ParserStrong))
                    then FStar_Pervasives_Native.None
                    else
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
                           -> parser_kind_subkind))
                   =
                   (FStar_Pervasives_Native.Some
                      LowParse_Spec_Base.ParserConsumesAll)
               then
                 FStar_Pervasives_Native.Some
                   LowParse_Spec_Base.ParserConsumesAll
               else
                 if
                   (if
                      (match lk with
                       | {
                           LowParse_Spec_Base.parser_kind_low =
                             parser_kind_low;
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
                    then
                      (if max = Prims.int_zero
                       then
                         FStar_Pervasives_Native.Some
                           LowParse_Spec_Base.ParserStrong
                       else
                         if
                           (min = Prims.int_zero) &&
                             ((match k with
                               | {
                                   LowParse_Spec_Base.parser_kind_low =
                                     parser_kind_low;
                                   LowParse_Spec_Base.parser_kind_high =
                                     parser_kind_high;
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     parser_kind_subkind;
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     parser_kind_metadata;_}
                                   -> parser_kind_subkind)
                                <>
                                (FStar_Pervasives_Native.Some
                                   LowParse_Spec_Base.ParserStrong))
                         then FStar_Pervasives_Native.None
                         else
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
                                -> parser_kind_subkind))
                        =
                        (FStar_Pervasives_Native.Some
                           LowParse_Spec_Base.ParserStrong)
                    else false)
                 then
                   FStar_Pervasives_Native.Some
                     LowParse_Spec_Base.ParserStrong
                 else
                   if
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
                         | FStar_Pervasives_Native.None ->
                             if max = Prims.int_zero
                             then FStar_Pervasives_Native.Some Prims.int_zero
                             else FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some b ->
                             FStar_Pervasives_Native.Some (max * b))
                          = (FStar_Pervasives_Native.Some Prims.int_zero)
                      then
                        (if max = Prims.int_zero
                         then
                           FStar_Pervasives_Native.Some
                             LowParse_Spec_Base.ParserStrong
                         else
                           if
                             (min = Prims.int_zero) &&
                               ((match k with
                                 | {
                                     LowParse_Spec_Base.parser_kind_low =
                                       parser_kind_low;
                                     LowParse_Spec_Base.parser_kind_high =
                                       parser_kind_high;
                                     LowParse_Spec_Base.parser_kind_subkind =
                                       parser_kind_subkind;
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
                                     -> parser_kind_subkind)
                                  <>
                                  (FStar_Pervasives_Native.Some
                                     LowParse_Spec_Base.ParserStrong))
                           then FStar_Pervasives_Native.None
                           else
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
                                  -> parser_kind_subkind))
                          =
                          (FStar_Pervasives_Native.Some
                             LowParse_Spec_Base.ParserStrong)
                      else false)
                   then
                     (match lk with
                      | {
                          LowParse_Spec_Base.parser_kind_low =
                            parser_kind_low;
                          LowParse_Spec_Base.parser_kind_high =
                            parser_kind_high;
                          LowParse_Spec_Base.parser_kind_subkind =
                            parser_kind_subkind;
                          LowParse_Spec_Base.parser_kind_metadata =
                            parser_kind_metadata;_}
                          -> parser_kind_subkind)
                   else FStar_Pervasives_Native.None);
            LowParse_Spec_Base.parser_kind_metadata =
              (match ((match match lk with
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
                       | uu___ -> FStar_Pervasives_Native.None),
                       (if max = Prims.int_zero
                        then
                          FStar_Pervasives_Native.Some
                            LowParse_Spec_Base.ParserKindMetadataTotal
                        else
                          if
                            (min = Prims.int_zero) &&
                              ((match k with
                                | {
                                    LowParse_Spec_Base.parser_kind_low =
                                      parser_kind_low;
                                    LowParse_Spec_Base.parser_kind_high =
                                      parser_kind_high;
                                    LowParse_Spec_Base.parser_kind_subkind =
                                      parser_kind_subkind;
                                    LowParse_Spec_Base.parser_kind_metadata =
                                      parser_kind_metadata;_}
                                    -> parser_kind_metadata)
                                 <>
                                 (FStar_Pervasives_Native.Some
                                    LowParse_Spec_Base.ParserKindMetadataTotal))
                          then FStar_Pervasives_Native.None
                          else
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
                                 -> parser_kind_metadata)))
               with
               | (FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
                   (match match lk with
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
               | (uu___, FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                   if max = Prims.int_zero
                   then
                     FStar_Pervasives_Native.Some
                       LowParse_Spec_Base.ParserKindMetadataTotal
                   else
                     if
                       (min = Prims.int_zero) &&
                         ((match k with
                           | {
                               LowParse_Spec_Base.parser_kind_low =
                                 parser_kind_low;
                               LowParse_Spec_Base.parser_kind_high =
                                 parser_kind_high;
                               LowParse_Spec_Base.parser_kind_subkind =
                                 parser_kind_subkind;
                               LowParse_Spec_Base.parser_kind_metadata =
                                 parser_kind_metadata;_}
                               -> parser_kind_metadata)
                            <>
                            (FStar_Pervasives_Native.Some
                               LowParse_Spec_Base.ParserKindMetadataTotal))
                     then FStar_Pervasives_Native.None
                     else
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
                            -> parser_kind_metadata)
               | (FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataTotal),
                  FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataTotal)) ->
                   (match match lk with
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
                    | uu___ -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None)
          }
let (synth_bounded_count :
  Prims.nat -> Prims.nat -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun min -> fun max -> fun x -> x





