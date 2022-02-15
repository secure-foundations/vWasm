open Prims
type u8 = FStar_UInt8.t
type 't parser'' =
  {
  kind: LowParse_Spec_Base.parser_kind ;
  parser: unit ;
  serializer: unit ;
  jumper:
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t
    }
let __proj__Mkparser''__item__kind :
  't . 't parser'' -> LowParse_Spec_Base.parser_kind =
  fun projectee ->
    match projectee with | { kind; parser; serializer; jumper;_} -> kind


let __proj__Mkparser''__item__jumper :
  't .
    't parser'' ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t
  =
  fun projectee ->
    match projectee with | { kind; parser; serializer; jumper;_} -> jumper
type 't parser' = 't parser''
type parser =
  | Parser of unit * Obj.t parser' 
let (uu___is_Parser : parser -> Prims.bool) = fun projectee -> true
let (__proj__Parser__item__p : parser -> Obj.t parser') =
  fun projectee -> match projectee with | Parser (t, p) -> p

type ('p, 'h, 'b, 'pos, 'posu) valid_pos = unit




let (parse_empty' : unit parser') =
  {
    kind =
      {
        LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some Prims.int_zero);
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          (FStar_Pervasives_Native.Some
             LowParse_Spec_Base.ParserKindMetadataTotal)
      };
    parser = ();
    serializer = ();
    jumper =
      (fun rrel ->
         fun rel ->
           fun input ->
             fun pos ->
               let h = FStar_HyperStack_ST.get () in
               FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_zero))
  }
let (parse_empty : parser) =
  Parser
    ((),
      (Obj.magic
         {
           kind =
             {
               LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
               LowParse_Spec_Base.parser_kind_high =
                 (FStar_Pervasives_Native.Some Prims.int_zero);
               LowParse_Spec_Base.parser_kind_subkind =
                 (FStar_Pervasives_Native.Some
                    LowParse_Spec_Base.ParserStrong);
               LowParse_Spec_Base.parser_kind_metadata =
                 (FStar_Pervasives_Native.Some
                    LowParse_Spec_Base.ParserKindMetadataTotal)
             };
           parser = ();
           serializer = ();
           jumper =
             (fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos
                        (FStar_UInt32.uint_to_t Prims.int_zero))
         }))


let parse_pair' : 't1 't2 . 't1 parser' -> 't2 parser' -> ('t1 * 't2) parser'
  =
  fun p1 ->
    fun p2 ->
      {
        kind =
          {
            LowParse_Spec_Base.parser_kind_low =
              ((match match p1 with
                      | { kind; parser = parser1; serializer; jumper;_} ->
                          kind
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 +
                 (match match p2 with
                        | { kind; parser = parser1; serializer; jumper;_} ->
                            kind
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_low));
            LowParse_Spec_Base.parser_kind_high =
              (if
                 (if
                    match match match p1 with
                                | { kind; parser = parser1; serializer;
                                    jumper;_} -> kind
                          with
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
                    match match match p2 with
                                | { kind; parser = parser1; serializer;
                                    jumper;_} -> kind
                          with
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
                  else false)
               then
                 FStar_Pervasives_Native.Some
                   ((match match match p1 with
                                 | { kind; parser = parser1; serializer;
                                     jumper;_} -> kind
                           with
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
                      (match match match p2 with
                                   | { kind; parser = parser1; serializer;
                                       jumper;_} -> kind
                             with
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
                       | FStar_Pervasives_Native.Some y -> y))
               else FStar_Pervasives_Native.None);
            LowParse_Spec_Base.parser_kind_subkind =
              (if
                 (match match p2 with
                        | { kind; parser = parser1; serializer; jumper;_} ->
                            kind
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_subkind)
                   =
                   (FStar_Pervasives_Native.Some
                      LowParse_Spec_Base.ParserConsumesAll)
               then
                 FStar_Pervasives_Native.Some
                   LowParse_Spec_Base.ParserConsumesAll
               else
                 if
                   (if
                      (match match p1 with
                             | { kind; parser = parser1; serializer;
                                 jumper;_} -> kind
                       with
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
                      (match match p2 with
                             | { kind; parser = parser1; serializer;
                                 jumper;_} -> kind
                       with
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
                    else false)
                 then
                   FStar_Pervasives_Native.Some
                     LowParse_Spec_Base.ParserStrong
                 else
                   if
                     (if
                        (match match p2 with
                               | { kind; parser = parser1; serializer;
                                   jumper;_} -> kind
                         with
                         | {
                             LowParse_Spec_Base.parser_kind_low =
                               parser_kind_low;
                             LowParse_Spec_Base.parser_kind_high =
                               parser_kind_high;
                             LowParse_Spec_Base.parser_kind_subkind =
                               parser_kind_subkind;
                             LowParse_Spec_Base.parser_kind_metadata =
                               parser_kind_metadata;_}
                             -> parser_kind_high)
                          = (FStar_Pervasives_Native.Some Prims.int_zero)
                      then
                        (match match p2 with
                               | { kind; parser = parser1; serializer;
                                   jumper;_} -> kind
                         with
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
                      else false)
                   then
                     (match match p1 with
                            | { kind; parser = parser1; serializer; jumper;_}
                                -> kind
                      with
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
              (match ((match match p1 with
                             | { kind; parser = parser1; serializer;
                                 jumper;_} -> kind
                       with
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
                       (match match p2 with
                              | { kind; parser = parser1; serializer;
                                  jumper;_} -> kind
                        with
                        | {
                            LowParse_Spec_Base.parser_kind_low =
                              parser_kind_low;
                            LowParse_Spec_Base.parser_kind_high =
                              parser_kind_high;
                            LowParse_Spec_Base.parser_kind_subkind =
                              parser_kind_subkind;
                            LowParse_Spec_Base.parser_kind_metadata =
                              parser_kind_metadata;_}
                            -> parser_kind_metadata))
               with
               | (FStar_Pervasives_Native.Some
                  (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
                   (match match p1 with
                          | { kind; parser = parser1; serializer; jumper;_}
                              -> kind
                    with
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
                   (match match p2 with
                          | { kind; parser = parser1; serializer; jumper;_}
                              -> kind
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
                   (match match p1 with
                          | { kind; parser = parser1; serializer; jumper;_}
                              -> kind
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata)
               | uu___ -> FStar_Pervasives_Native.None)
          };
        parser = ();
        serializer = ();
        jumper =
          (fun rrel ->
             fun rel ->
               fun input ->
                 fun pos ->
                   let h = FStar_HyperStack_ST.get () in
                   let uu___ =
                     match p1 with
                     | { kind; parser = parser1; serializer; jumper;_} ->
                         jumper () () input pos in
                   match p2 with
                   | { kind; parser = parser1; serializer; jumper;_} ->
                       jumper () () input uu___)
      }
let (parse_pair : parser -> parser -> parser) =
  fun p1 ->
    fun p2 ->
      Parser
        ((),
          (Obj.magic
             {
               kind =
                 {
                   LowParse_Spec_Base.parser_kind_low =
                     ((match match match p1 with | Parser (t, p) -> p with
                             | { kind; parser = parser1; serializer;
                                 jumper;_} -> kind
                       with
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
                        +
                        (match match match p2 with | Parser (t, p) -> p with
                               | { kind; parser = parser1; serializer;
                                   jumper;_} -> kind
                         with
                         | {
                             LowParse_Spec_Base.parser_kind_low =
                               parser_kind_low;
                             LowParse_Spec_Base.parser_kind_high =
                               parser_kind_high;
                             LowParse_Spec_Base.parser_kind_subkind =
                               parser_kind_subkind;
                             LowParse_Spec_Base.parser_kind_metadata =
                               parser_kind_metadata;_}
                             -> parser_kind_low));
                   LowParse_Spec_Base.parser_kind_high =
                     (if
                        (if
                           match match match match p1 with
                                             | Parser (t, p) -> p
                                       with
                                       | { kind; parser = parser1;
                                           serializer; jumper;_} -> kind
                                 with
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
                           | FStar_Pervasives_Native.Some uu___ -> true
                           | uu___ -> false
                         then
                           match match match match p2 with
                                             | Parser (t, p) -> p
                                       with
                                       | { kind; parser = parser1;
                                           serializer; jumper;_} -> kind
                                 with
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
                           | FStar_Pervasives_Native.Some uu___ -> true
                           | uu___ -> false
                         else false)
                      then
                        FStar_Pervasives_Native.Some
                          ((match match match match p1 with
                                              | Parser (t, p) -> p
                                        with
                                        | { kind; parser = parser1;
                                            serializer; jumper;_} -> kind
                                  with
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
                            | FStar_Pervasives_Native.Some y -> y) +
                             (match match match match p2 with
                                                | Parser (t, p) -> p
                                          with
                                          | { kind; parser = parser1;
                                              serializer; jumper;_} -> kind
                                    with
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
                              | FStar_Pervasives_Native.Some y -> y))
                      else FStar_Pervasives_Native.None);
                   LowParse_Spec_Base.parser_kind_subkind =
                     (if
                        (match match match p2 with | Parser (t, p) -> p with
                               | { kind; parser = parser1; serializer;
                                   jumper;_} -> kind
                         with
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
                             LowParse_Spec_Base.ParserConsumesAll)
                      then
                        FStar_Pervasives_Native.Some
                          LowParse_Spec_Base.ParserConsumesAll
                      else
                        if
                          (if
                             (match match match p1 with | Parser (t, p) -> p
                                    with
                                    | { kind; parser = parser1; serializer;
                                        jumper;_} -> kind
                              with
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
                             (match match match p2 with | Parser (t, p) -> p
                                    with
                                    | { kind; parser = parser1; serializer;
                                        jumper;_} -> kind
                              with
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
                           else false)
                        then
                          FStar_Pervasives_Native.Some
                            LowParse_Spec_Base.ParserStrong
                        else
                          if
                            (if
                               (match match match p2 with
                                            | Parser (t, p) -> p
                                      with
                                      | { kind; parser = parser1; serializer;
                                          jumper;_} -> kind
                                with
                                | {
                                    LowParse_Spec_Base.parser_kind_low =
                                      parser_kind_low;
                                    LowParse_Spec_Base.parser_kind_high =
                                      parser_kind_high;
                                    LowParse_Spec_Base.parser_kind_subkind =
                                      parser_kind_subkind;
                                    LowParse_Spec_Base.parser_kind_metadata =
                                      parser_kind_metadata;_}
                                    -> parser_kind_high)
                                 =
                                 (FStar_Pervasives_Native.Some Prims.int_zero)
                             then
                               (match match match p2 with
                                            | Parser (t, p) -> p
                                      with
                                      | { kind; parser = parser1; serializer;
                                          jumper;_} -> kind
                                with
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
                             else false)
                          then
                            (match match match p1 with | Parser (t, p) -> p
                                   with
                                   | { kind; parser = parser1; serializer;
                                       jumper;_} -> kind
                             with
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
                     (match ((match match match p1 with | Parser (t, p) -> p
                                    with
                                    | { kind; parser = parser1; serializer;
                                        jumper;_} -> kind
                              with
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
                              (match match match p2 with | Parser (t, p) -> p
                                     with
                                     | { kind; parser = parser1; serializer;
                                         jumper;_} -> kind
                               with
                               | {
                                   LowParse_Spec_Base.parser_kind_low =
                                     parser_kind_low;
                                   LowParse_Spec_Base.parser_kind_high =
                                     parser_kind_high;
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     parser_kind_subkind;
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     parser_kind_metadata;_}
                                   -> parser_kind_metadata))
                      with
                      | (FStar_Pervasives_Native.Some
                         (LowParse_Spec_Base.ParserKindMetadataFail), uu___)
                          ->
                          (match match match p1 with | Parser (t, p) -> p
                                 with
                                 | { kind; parser = parser1; serializer;
                                     jumper;_} -> kind
                           with
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
                      | (uu___, FStar_Pervasives_Native.Some
                         (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                          (match match match p2 with | Parser (t, p) -> p
                                 with
                                 | { kind; parser = parser1; serializer;
                                     jumper;_} -> kind
                           with
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
                          (match match match p1 with | Parser (t, p) -> p
                                 with
                                 | { kind; parser = parser1; serializer;
                                     jumper;_} -> kind
                           with
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
                      | uu___ -> FStar_Pervasives_Native.None)
                 };
               parser = ();
               serializer = ();
               jumper =
                 (fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let uu___ =
                            match match p1 with | Parser (t, p) -> p with
                            | { kind; parser = parser1; serializer; jumper;_}
                                -> jumper () () input pos in
                          match match p2 with | Parser (t, p) -> p with
                          | { kind; parser = parser1; serializer; jumper;_}
                              -> jumper () () input uu___)
             }))






type 'p leaf_writer =
  FStar_UInt8.t LowStar_Buffer.buffer ->
    FStar_UInt32.t -> Obj.t -> FStar_UInt32.t FStar_Pervasives_Native.option

let (valid_parse_pair_inv :
  parser ->
    parser ->
      FStar_UInt8.t LowStar_Buffer.buffer ->
        FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun p1 ->
    fun p2 ->
      fun b ->
        fun len ->
          fun pos1 ->
            fun pos3 ->
              let h = FStar_HyperStack_ST.get () in
              (match match p1 with | Parser (t, p) -> p with
               | { kind; parser = parser1; serializer; jumper;_} -> jumper)
                () ()
                (Obj.magic
                   { LowParse_Slice.base = b; LowParse_Slice.len = len })
                pos1
type ('p, 'h, 'b) valid_buffer = unit

type 'p leaf_reader =
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> Obj.t
type ('t1, 't2) clens = {
  clens_cond: unit ;
  clens_get: unit }


type ('p1, 'p2, 'lens) gaccessor = unit



type ('p1, 'p2, 'lens, 'g) accessor =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
let (baccess :
  parser ->
    parser ->
      (Obj.t, Obj.t) clens ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            u8 LowStar_Buffer.buffer ->
              FStar_UInt32.t -> (u8 LowStar_Buffer.buffer * FStar_UInt32.t))
  =
  fun p1 ->
    fun p2 ->
      fun lens ->
        fun g ->
          fun a ->
            fun b ->
              fun len ->
                let h = FStar_HyperStack_ST.get () in
                let sl =
                  { LowParse_Slice.base = b; LowParse_Slice.len = len } in
                let pos =
                  a () () (Obj.magic sl)
                    (FStar_UInt32.uint_to_t Prims.int_zero) in
                let pos' =
                  (match match p2 with | Parser (t, p) -> p with
                   | { kind; parser = parser1; serializer; jumper;_} ->
                       jumper) () () (Obj.magic sl) pos in
                let b1 = LowStar_Monotonic_Buffer.msub b pos () in
                let len' = FStar_UInt32.sub pos' pos in
                let b' =
                  LowStar_Monotonic_Buffer.msub b1
                    (FStar_UInt32.uint_to_t Prims.int_zero) () in
                (b', len')
type 'p validator =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt64.t -> FStar_UInt64.t
let snd : 'uuuuu 'uuuuu1 . ('uuuuu * 'uuuuu1) -> 'uuuuu1 =
  fun uu___ -> match uu___ with | (a, b) -> b


let (bvalidate :
  parser ->
    (unit ->
       unit ->
         (Obj.t, Obj.t) LowParse_Slice.slice ->
           FStar_UInt64.t -> FStar_UInt64.t)
      ->
      FStar_UInt8.t LowStar_Buffer.buffer ->
        FStar_UInt32.t -> FStar_UInt32.t FStar_Pervasives_Native.option)
  =
  fun p ->
    fun v ->
      fun b ->
        fun len ->
          let res =
            v () ()
              (Obj.magic
                 { LowParse_Slice.base = b; LowParse_Slice.len = len })
              (FStar_UInt64.uint_to_t Prims.int_zero) in
          if LowParse_Low_ErrorCode.is_success res
          then
            FStar_Pervasives_Native.Some
              (FStar_Int_Cast.uint64_to_uint32 res)
          else FStar_Pervasives_Native.None