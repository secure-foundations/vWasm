open Prims
type parse_ifthenelse_param =
  {
  parse_ifthenelse_tag_kind: LowParse_Spec_Base.parser_kind ;
  parse_ifthenelse_tag_t: unit ;
  parse_ifthenelse_tag_parser: unit ;
  parse_ifthenelse_tag_cond: Obj.t -> Prims.bool ;
  parse_ifthenelse_payload_t: unit ;
  parse_ifthenelse_payload_parser:
    Prims.bool -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2 ;
  parse_ifthenelse_t: unit ;
  parse_ifthenelse_synth: unit ;
  parse_ifthenelse_synth_injective: unit }
let (__proj__Mkparse_ifthenelse_param__item__parse_ifthenelse_tag_kind :
  parse_ifthenelse_param -> LowParse_Spec_Base.parser_kind) =
  fun projectee ->
    match projectee with
    | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
        parse_ifthenelse_tag_parser; parse_ifthenelse_tag_cond;
        parse_ifthenelse_payload_t; parse_ifthenelse_payload_parser;
        parse_ifthenelse_t; parse_ifthenelse_synth;
        parse_ifthenelse_synth_injective;_} -> parse_ifthenelse_tag_kind

let (__proj__Mkparse_ifthenelse_param__item__parse_ifthenelse_tag_cond :
  parse_ifthenelse_param -> Obj.t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
        parse_ifthenelse_tag_parser; parse_ifthenelse_tag_cond;
        parse_ifthenelse_payload_t; parse_ifthenelse_payload_parser;
        parse_ifthenelse_t; parse_ifthenelse_synth;
        parse_ifthenelse_synth_injective;_} -> parse_ifthenelse_tag_cond
let (__proj__Mkparse_ifthenelse_param__item__parse_ifthenelse_payload_parser
  :
  parse_ifthenelse_param ->
    Prims.bool -> (LowParse_Spec_Base.parser_kind, unit) Prims.dtuple2)
  =
  fun projectee ->
    match projectee with
    | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
        parse_ifthenelse_tag_parser; parse_ifthenelse_tag_cond;
        parse_ifthenelse_payload_t; parse_ifthenelse_payload_parser;
        parse_ifthenelse_t; parse_ifthenelse_synth;
        parse_ifthenelse_synth_injective;_} ->
        parse_ifthenelse_payload_parser


let (parse_ifthenelse_payload_kind :
  parse_ifthenelse_param -> LowParse_Spec_Base.parser_kind) =
  fun p ->
    match ((match FStar_Pervasives.dfst
                    (match p with
                     | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                         parse_ifthenelse_tag_parser;
                         parse_ifthenelse_tag_cond;
                         parse_ifthenelse_payload_t;
                         parse_ifthenelse_payload_parser; parse_ifthenelse_t;
                         parse_ifthenelse_synth;
                         parse_ifthenelse_synth_injective;_} ->
                         parse_ifthenelse_payload_parser true)
            with
            | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                LowParse_Spec_Base.parser_kind_metadata =
                  parser_kind_metadata;_}
                -> parser_kind_metadata),
            (match FStar_Pervasives.dfst
                     (match p with
                      | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                          parse_ifthenelse_tag_parser;
                          parse_ifthenelse_tag_cond;
                          parse_ifthenelse_payload_t;
                          parse_ifthenelse_payload_parser;
                          parse_ifthenelse_t; parse_ifthenelse_synth;
                          parse_ifthenelse_synth_injective;_} ->
                          parse_ifthenelse_payload_parser false)
             with
             | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                 LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                 LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                 LowParse_Spec_Base.parser_kind_metadata =
                   parser_kind_metadata;_}
                 -> parser_kind_metadata))
    with
    | (uu___, FStar_Pervasives_Native.Some
       (LowParse_Spec_Base.ParserKindMetadataFail)) ->
        {
          LowParse_Spec_Base.parser_kind_low =
            ((match FStar_Pervasives.dfst
                      (match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_payload_parser true)
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low));
          LowParse_Spec_Base.parser_kind_high =
            ((match FStar_Pervasives.dfst
                      (match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_payload_parser true)
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_high));
          LowParse_Spec_Base.parser_kind_subkind =
            ((match FStar_Pervasives.dfst
                      (match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_payload_parser true)
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_subkind));
          LowParse_Spec_Base.parser_kind_metadata =
            ((match match FStar_Pervasives.dfst
                            (match p with
                             | { parse_ifthenelse_tag_kind;
                                 parse_ifthenelse_tag_t;
                                 parse_ifthenelse_tag_parser;
                                 parse_ifthenelse_tag_cond;
                                 parse_ifthenelse_payload_t;
                                 parse_ifthenelse_payload_parser;
                                 parse_ifthenelse_t; parse_ifthenelse_synth;
                                 parse_ifthenelse_synth_injective;_} ->
                                 parse_ifthenelse_payload_parser true)
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
              | uu___1 -> FStar_Pervasives_Native.None))
        }
    | (FStar_Pervasives_Native.Some
       (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
        {
          LowParse_Spec_Base.parser_kind_low =
            ((match FStar_Pervasives.dfst
                      (match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_payload_parser false)
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low));
          LowParse_Spec_Base.parser_kind_high =
            ((match FStar_Pervasives.dfst
                      (match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_payload_parser false)
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_high));
          LowParse_Spec_Base.parser_kind_subkind =
            ((match FStar_Pervasives.dfst
                      (match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_payload_parser false)
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_subkind));
          LowParse_Spec_Base.parser_kind_metadata =
            FStar_Pervasives_Native.None
        }
    | uu___ ->
        {
          LowParse_Spec_Base.parser_kind_low =
            (if
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser true)
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
                 <
                 ((match FStar_Pervasives.dfst
                           (match p with
                            | { parse_ifthenelse_tag_kind;
                                parse_ifthenelse_tag_t;
                                parse_ifthenelse_tag_parser;
                                parse_ifthenelse_tag_cond;
                                parse_ifthenelse_payload_t;
                                parse_ifthenelse_payload_parser;
                                parse_ifthenelse_t; parse_ifthenelse_synth;
                                parse_ifthenelse_synth_injective;_} ->
                                parse_ifthenelse_payload_parser false)
                   with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_low))
             then
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser true)
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_low)
             else
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser false)
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
                  match match FStar_Pervasives.dfst
                                (match p with
                                 | { parse_ifthenelse_tag_kind;
                                     parse_ifthenelse_tag_t;
                                     parse_ifthenelse_tag_parser;
                                     parse_ifthenelse_tag_cond;
                                     parse_ifthenelse_payload_t;
                                     parse_ifthenelse_payload_parser;
                                     parse_ifthenelse_t;
                                     parse_ifthenelse_synth;
                                     parse_ifthenelse_synth_injective;_} ->
                                     parse_ifthenelse_payload_parser true)
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
                  | FStar_Pervasives_Native.Some uu___1 -> true
                  | uu___1 -> false
                then
                  match match FStar_Pervasives.dfst
                                (match p with
                                 | { parse_ifthenelse_tag_kind;
                                     parse_ifthenelse_tag_t;
                                     parse_ifthenelse_tag_parser;
                                     parse_ifthenelse_tag_cond;
                                     parse_ifthenelse_payload_t;
                                     parse_ifthenelse_payload_parser;
                                     parse_ifthenelse_t;
                                     parse_ifthenelse_synth;
                                     parse_ifthenelse_synth_injective;_} ->
                                     parse_ifthenelse_payload_parser false)
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
                  | FStar_Pervasives_Native.Some uu___1 -> true
                  | uu___1 -> false
                else false)
             then
               (if
                  (match match FStar_Pervasives.dfst
                                 (match p with
                                  | { parse_ifthenelse_tag_kind;
                                      parse_ifthenelse_tag_t;
                                      parse_ifthenelse_tag_parser;
                                      parse_ifthenelse_tag_cond;
                                      parse_ifthenelse_payload_t;
                                      parse_ifthenelse_payload_parser;
                                      parse_ifthenelse_t;
                                      parse_ifthenelse_synth;
                                      parse_ifthenelse_synth_injective;_} ->
                                      parse_ifthenelse_payload_parser false)
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
                   | FStar_Pervasives_Native.Some y -> y) <
                    (match match FStar_Pervasives.dfst
                                   (match p with
                                    | { parse_ifthenelse_tag_kind;
                                        parse_ifthenelse_tag_t;
                                        parse_ifthenelse_tag_parser;
                                        parse_ifthenelse_tag_cond;
                                        parse_ifthenelse_payload_t;
                                        parse_ifthenelse_payload_parser;
                                        parse_ifthenelse_t;
                                        parse_ifthenelse_synth;
                                        parse_ifthenelse_synth_injective;_}
                                        ->
                                        parse_ifthenelse_payload_parser true)
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
                     | FStar_Pervasives_Native.Some y -> y)
                then
                  match FStar_Pervasives.dfst
                          (match p with
                           | { parse_ifthenelse_tag_kind;
                               parse_ifthenelse_tag_t;
                               parse_ifthenelse_tag_parser;
                               parse_ifthenelse_tag_cond;
                               parse_ifthenelse_payload_t;
                               parse_ifthenelse_payload_parser;
                               parse_ifthenelse_t; parse_ifthenelse_synth;
                               parse_ifthenelse_synth_injective;_} ->
                               parse_ifthenelse_payload_parser true)
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_high
                else
                  (match FStar_Pervasives.dfst
                           (match p with
                            | { parse_ifthenelse_tag_kind;
                                parse_ifthenelse_tag_t;
                                parse_ifthenelse_tag_parser;
                                parse_ifthenelse_tag_cond;
                                parse_ifthenelse_payload_t;
                                parse_ifthenelse_payload_parser;
                                parse_ifthenelse_t; parse_ifthenelse_synth;
                                parse_ifthenelse_synth_injective;_} ->
                                parse_ifthenelse_payload_parser false)
                   with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_high))
             else FStar_Pervasives_Native.None);
          LowParse_Spec_Base.parser_kind_subkind =
            (if
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser true)
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_subkind)
                 =
                 ((match FStar_Pervasives.dfst
                           (match p with
                            | { parse_ifthenelse_tag_kind;
                                parse_ifthenelse_tag_t;
                                parse_ifthenelse_tag_parser;
                                parse_ifthenelse_tag_cond;
                                parse_ifthenelse_payload_t;
                                parse_ifthenelse_payload_parser;
                                parse_ifthenelse_t; parse_ifthenelse_synth;
                                parse_ifthenelse_synth_injective;_} ->
                                parse_ifthenelse_payload_parser false)
                   with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_subkind))
             then
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser true)
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_subkind)
             else FStar_Pervasives_Native.None);
          LowParse_Spec_Base.parser_kind_metadata =
            (if
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser true)
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_metadata)
                 =
                 ((match FStar_Pervasives.dfst
                           (match p with
                            | { parse_ifthenelse_tag_kind;
                                parse_ifthenelse_tag_t;
                                parse_ifthenelse_tag_parser;
                                parse_ifthenelse_tag_cond;
                                parse_ifthenelse_payload_t;
                                parse_ifthenelse_payload_parser;
                                parse_ifthenelse_t; parse_ifthenelse_synth;
                                parse_ifthenelse_synth_injective;_} ->
                                parse_ifthenelse_payload_parser false)
                   with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_metadata))
             then
               (match FStar_Pervasives.dfst
                        (match p with
                         | { parse_ifthenelse_tag_kind;
                             parse_ifthenelse_tag_t;
                             parse_ifthenelse_tag_parser;
                             parse_ifthenelse_tag_cond;
                             parse_ifthenelse_payload_t;
                             parse_ifthenelse_payload_parser;
                             parse_ifthenelse_t; parse_ifthenelse_synth;
                             parse_ifthenelse_synth_injective;_} ->
                             parse_ifthenelse_payload_parser true)
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_metadata)
             else FStar_Pervasives_Native.None)
        }
let (parse_ifthenelse_kind :
  parse_ifthenelse_param -> LowParse_Spec_Base.parser_kind) =
  fun p ->
    {
      LowParse_Spec_Base.parser_kind_low =
        ((match match p with
                | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                    parse_ifthenelse_tag_parser; parse_ifthenelse_tag_cond;
                    parse_ifthenelse_payload_t;
                    parse_ifthenelse_payload_parser; parse_ifthenelse_t;
                    parse_ifthenelse_synth;
                    parse_ifthenelse_synth_injective;_} ->
                    parse_ifthenelse_tag_kind
          with
          | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
              LowParse_Spec_Base.parser_kind_high = parser_kind_high;
              LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
              LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
              -> parser_kind_low)
           +
           (match match ((match FStar_Pervasives.dfst
                                  (match p with
                                   | { parse_ifthenelse_tag_kind;
                                       parse_ifthenelse_tag_t;
                                       parse_ifthenelse_tag_parser;
                                       parse_ifthenelse_tag_cond;
                                       parse_ifthenelse_payload_t;
                                       parse_ifthenelse_payload_parser;
                                       parse_ifthenelse_t;
                                       parse_ifthenelse_synth;
                                       parse_ifthenelse_synth_injective;_} ->
                                       parse_ifthenelse_payload_parser true)
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
                          (match FStar_Pervasives.dfst
                                   (match p with
                                    | { parse_ifthenelse_tag_kind;
                                        parse_ifthenelse_tag_t;
                                        parse_ifthenelse_tag_parser;
                                        parse_ifthenelse_tag_cond;
                                        parse_ifthenelse_payload_t;
                                        parse_ifthenelse_payload_parser;
                                        parse_ifthenelse_t;
                                        parse_ifthenelse_synth;
                                        parse_ifthenelse_synth_injective;_}
                                        ->
                                        parse_ifthenelse_payload_parser false)
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
                  | (uu___, FStar_Pervasives_Native.Some
                     (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                      {
                        LowParse_Spec_Base.parser_kind_low =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                                -> parser_kind_high));
                        LowParse_Spec_Base.parser_kind_subkind =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                                -> parser_kind_subkind));
                        LowParse_Spec_Base.parser_kind_metadata =
                          ((match match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                      -> parser_kind_metadata
                            with
                            | FStar_Pervasives_Native.Some
                                (LowParse_Spec_Base.ParserKindMetadataFail)
                                ->
                                FStar_Pervasives_Native.Some
                                  LowParse_Spec_Base.ParserKindMetadataFail
                            | uu___1 -> FStar_Pervasives_Native.None))
                      }
                  | (FStar_Pervasives_Native.Some
                     (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
                      {
                        LowParse_Spec_Base.parser_kind_low =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser
                                           false)
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
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser
                                           false)
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
                                -> parser_kind_high));
                        LowParse_Spec_Base.parser_kind_subkind =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser
                                           false)
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
                                -> parser_kind_subkind));
                        LowParse_Spec_Base.parser_kind_metadata =
                          FStar_Pervasives_Native.None
                      }
                  | uu___ ->
                      {
                        LowParse_Spec_Base.parser_kind_low =
                          (if
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                               <
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_low))
                           then
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                           else
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             false)
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
                                match match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_high
                                with
                                | FStar_Pervasives_Native.Some uu___1 -> true
                                | uu___1 -> false
                              then
                                match match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_high
                                with
                                | FStar_Pervasives_Native.Some uu___1 -> true
                                | uu___1 -> false
                              else false)
                           then
                             (if
                                (match match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high
                                 with
                                 | FStar_Pervasives_Native.Some y -> y) <
                                  (match match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_high
                                   with
                                   | FStar_Pervasives_Native.Some y -> y)
                              then
                                match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                              else
                                (match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_high))
                           else FStar_Pervasives_Native.None);
                        LowParse_Spec_Base.parser_kind_subkind =
                          (if
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_subkind))
                           then
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                          (if
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                               =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_metadata))
                           then
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                           else FStar_Pervasives_Native.None)
                      }
            with
            | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                LowParse_Spec_Base.parser_kind_metadata =
                  parser_kind_metadata;_}
                -> parser_kind_low));
      LowParse_Spec_Base.parser_kind_high =
        (if
           (if
              match match match p with
                          | { parse_ifthenelse_tag_kind;
                              parse_ifthenelse_tag_t;
                              parse_ifthenelse_tag_parser;
                              parse_ifthenelse_tag_cond;
                              parse_ifthenelse_payload_t;
                              parse_ifthenelse_payload_parser;
                              parse_ifthenelse_t; parse_ifthenelse_synth;
                              parse_ifthenelse_synth_injective;_} ->
                              parse_ifthenelse_tag_kind
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
              match match match ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                      -> parser_kind_metadata),
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_metadata))
                          with
                          | (uu___, FStar_Pervasives_Native.Some
                             (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                              {
                                LowParse_Spec_Base.parser_kind_low =
                                  ((match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_low));
                                LowParse_Spec_Base.parser_kind_high =
                                  ((match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_high));
                                LowParse_Spec_Base.parser_kind_subkind =
                                  ((match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_subkind));
                                LowParse_Spec_Base.parser_kind_metadata =
                                  ((match match FStar_Pervasives.dfst
                                                  (match p with
                                                   | {
                                                       parse_ifthenelse_tag_kind;
                                                       parse_ifthenelse_tag_t;
                                                       parse_ifthenelse_tag_parser;
                                                       parse_ifthenelse_tag_cond;
                                                       parse_ifthenelse_payload_t;
                                                       parse_ifthenelse_payload_parser;
                                                       parse_ifthenelse_t;
                                                       parse_ifthenelse_synth;
                                                       parse_ifthenelse_synth_injective;_}
                                                       ->
                                                       parse_ifthenelse_payload_parser
                                                         true)
                                          with
                                          | {
                                              LowParse_Spec_Base.parser_kind_low
                                                = parser_kind_low;
                                              LowParse_Spec_Base.parser_kind_high
                                                = parser_kind_high;
                                              LowParse_Spec_Base.parser_kind_subkind
                                                = parser_kind_subkind;
                                              LowParse_Spec_Base.parser_kind_metadata
                                                = parser_kind_metadata;_}
                                              -> parser_kind_metadata
                                    with
                                    | FStar_Pervasives_Native.Some
                                        (LowParse_Spec_Base.ParserKindMetadataFail)
                                        ->
                                        FStar_Pervasives_Native.Some
                                          LowParse_Spec_Base.ParserKindMetadataFail
                                    | uu___1 -> FStar_Pervasives_Native.None))
                              }
                          | (FStar_Pervasives_Native.Some
                             (LowParse_Spec_Base.ParserKindMetadataFail),
                             uu___) ->
                              {
                                LowParse_Spec_Base.parser_kind_low =
                                  ((match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   false)
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
                                        -> parser_kind_low));
                                LowParse_Spec_Base.parser_kind_high =
                                  ((match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   false)
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
                                        -> parser_kind_high));
                                LowParse_Spec_Base.parser_kind_subkind =
                                  ((match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   false)
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
                                        -> parser_kind_subkind));
                                LowParse_Spec_Base.parser_kind_metadata =
                                  FStar_Pervasives_Native.None
                              }
                          | uu___ ->
                              {
                                LowParse_Spec_Base.parser_kind_low =
                                  (if
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_low)
                                       <
                                       ((match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        false)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_low))
                                   then
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_low)
                                   else
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_low));
                                LowParse_Spec_Base.parser_kind_high =
                                  (if
                                     (if
                                        match match FStar_Pervasives.dfst
                                                      (match p with
                                                       | {
                                                           parse_ifthenelse_tag_kind;
                                                           parse_ifthenelse_tag_t;
                                                           parse_ifthenelse_tag_parser;
                                                           parse_ifthenelse_tag_cond;
                                                           parse_ifthenelse_payload_t;
                                                           parse_ifthenelse_payload_parser;
                                                           parse_ifthenelse_t;
                                                           parse_ifthenelse_synth;
                                                           parse_ifthenelse_synth_injective;_}
                                                           ->
                                                           parse_ifthenelse_payload_parser
                                                             true)
                                              with
                                              | {
                                                  LowParse_Spec_Base.parser_kind_low
                                                    = parser_kind_low;
                                                  LowParse_Spec_Base.parser_kind_high
                                                    = parser_kind_high;
                                                  LowParse_Spec_Base.parser_kind_subkind
                                                    = parser_kind_subkind;
                                                  LowParse_Spec_Base.parser_kind_metadata
                                                    = parser_kind_metadata;_}
                                                  -> parser_kind_high
                                        with
                                        | FStar_Pervasives_Native.Some uu___1
                                            -> true
                                        | uu___1 -> false
                                      then
                                        match match FStar_Pervasives.dfst
                                                      (match p with
                                                       | {
                                                           parse_ifthenelse_tag_kind;
                                                           parse_ifthenelse_tag_t;
                                                           parse_ifthenelse_tag_parser;
                                                           parse_ifthenelse_tag_cond;
                                                           parse_ifthenelse_payload_t;
                                                           parse_ifthenelse_payload_parser;
                                                           parse_ifthenelse_t;
                                                           parse_ifthenelse_synth;
                                                           parse_ifthenelse_synth_injective;_}
                                                           ->
                                                           parse_ifthenelse_payload_parser
                                                             false)
                                              with
                                              | {
                                                  LowParse_Spec_Base.parser_kind_low
                                                    = parser_kind_low;
                                                  LowParse_Spec_Base.parser_kind_high
                                                    = parser_kind_high;
                                                  LowParse_Spec_Base.parser_kind_subkind
                                                    = parser_kind_subkind;
                                                  LowParse_Spec_Base.parser_kind_metadata
                                                    = parser_kind_metadata;_}
                                                  -> parser_kind_high
                                        with
                                        | FStar_Pervasives_Native.Some uu___1
                                            -> true
                                        | uu___1 -> false
                                      else false)
                                   then
                                     (if
                                        (match match FStar_Pervasives.dfst
                                                       (match p with
                                                        | {
                                                            parse_ifthenelse_tag_kind;
                                                            parse_ifthenelse_tag_t;
                                                            parse_ifthenelse_tag_parser;
                                                            parse_ifthenelse_tag_cond;
                                                            parse_ifthenelse_payload_t;
                                                            parse_ifthenelse_payload_parser;
                                                            parse_ifthenelse_t;
                                                            parse_ifthenelse_synth;
                                                            parse_ifthenelse_synth_injective;_}
                                                            ->
                                                            parse_ifthenelse_payload_parser
                                                              false)
                                               with
                                               | {
                                                   LowParse_Spec_Base.parser_kind_low
                                                     = parser_kind_low;
                                                   LowParse_Spec_Base.parser_kind_high
                                                     = parser_kind_high;
                                                   LowParse_Spec_Base.parser_kind_subkind
                                                     = parser_kind_subkind;
                                                   LowParse_Spec_Base.parser_kind_metadata
                                                     = parser_kind_metadata;_}
                                                   -> parser_kind_high
                                         with
                                         | FStar_Pervasives_Native.Some y ->
                                             y)
                                          <
                                          (match match FStar_Pervasives.dfst
                                                         (match p with
                                                          | {
                                                              parse_ifthenelse_tag_kind;
                                                              parse_ifthenelse_tag_t;
                                                              parse_ifthenelse_tag_parser;
                                                              parse_ifthenelse_tag_cond;
                                                              parse_ifthenelse_payload_t;
                                                              parse_ifthenelse_payload_parser;
                                                              parse_ifthenelse_t;
                                                              parse_ifthenelse_synth;
                                                              parse_ifthenelse_synth_injective;_}
                                                              ->
                                                              parse_ifthenelse_payload_parser
                                                                true)
                                                 with
                                                 | {
                                                     LowParse_Spec_Base.parser_kind_low
                                                       = parser_kind_low;
                                                     LowParse_Spec_Base.parser_kind_high
                                                       = parser_kind_high;
                                                     LowParse_Spec_Base.parser_kind_subkind
                                                       = parser_kind_subkind;
                                                     LowParse_Spec_Base.parser_kind_metadata
                                                       = parser_kind_metadata;_}
                                                     -> parser_kind_high
                                           with
                                           | FStar_Pervasives_Native.Some y
                                               -> y)
                                      then
                                        match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       true)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_high
                                      else
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        false)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_high))
                                   else FStar_Pervasives_Native.None);
                                LowParse_Spec_Base.parser_kind_subkind =
                                  (if
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_subkind)
                                       =
                                       ((match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        false)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_subkind))
                                   then
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_subkind)
                                   else FStar_Pervasives_Native.None);
                                LowParse_Spec_Base.parser_kind_metadata =
                                  (if
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_metadata)
                                       =
                                       ((match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        false)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_metadata))
                                   then
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_metadata)
                                   else FStar_Pervasives_Native.None)
                              }
                    with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
             ((match match match p with
                           | { parse_ifthenelse_tag_kind;
                               parse_ifthenelse_tag_t;
                               parse_ifthenelse_tag_parser;
                               parse_ifthenelse_tag_cond;
                               parse_ifthenelse_payload_t;
                               parse_ifthenelse_payload_parser;
                               parse_ifthenelse_t; parse_ifthenelse_synth;
                               parse_ifthenelse_synth_injective;_} ->
                               parse_ifthenelse_tag_kind
                     with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_high
               with
               | FStar_Pervasives_Native.Some y -> y) +
                (match match match ((match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_metadata),
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_metadata))
                             with
                             | (uu___, FStar_Pervasives_Native.Some
                                (LowParse_Spec_Base.ParserKindMetadataFail))
                                 ->
                                 {
                                   LowParse_Spec_Base.parser_kind_low =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      true)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_low));
                                   LowParse_Spec_Base.parser_kind_high =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      true)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high));
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      true)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_subkind));
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     ((match match FStar_Pervasives.dfst
                                                     (match p with
                                                      | {
                                                          parse_ifthenelse_tag_kind;
                                                          parse_ifthenelse_tag_t;
                                                          parse_ifthenelse_tag_parser;
                                                          parse_ifthenelse_tag_cond;
                                                          parse_ifthenelse_payload_t;
                                                          parse_ifthenelse_payload_parser;
                                                          parse_ifthenelse_t;
                                                          parse_ifthenelse_synth;
                                                          parse_ifthenelse_synth_injective;_}
                                                          ->
                                                          parse_ifthenelse_payload_parser
                                                            true)
                                             with
                                             | {
                                                 LowParse_Spec_Base.parser_kind_low
                                                   = parser_kind_low;
                                                 LowParse_Spec_Base.parser_kind_high
                                                   = parser_kind_high;
                                                 LowParse_Spec_Base.parser_kind_subkind
                                                   = parser_kind_subkind;
                                                 LowParse_Spec_Base.parser_kind_metadata
                                                   = parser_kind_metadata;_}
                                                 -> parser_kind_metadata
                                       with
                                       | FStar_Pervasives_Native.Some
                                           (LowParse_Spec_Base.ParserKindMetadataFail)
                                           ->
                                           FStar_Pervasives_Native.Some
                                             LowParse_Spec_Base.ParserKindMetadataFail
                                       | uu___1 ->
                                           FStar_Pervasives_Native.None))
                                 }
                             | (FStar_Pervasives_Native.Some
                                (LowParse_Spec_Base.ParserKindMetadataFail),
                                uu___) ->
                                 {
                                   LowParse_Spec_Base.parser_kind_low =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_low));
                                   LowParse_Spec_Base.parser_kind_high =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high));
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_subkind));
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     FStar_Pervasives_Native.None
                                 }
                             | uu___ ->
                                 {
                                   LowParse_Spec_Base.parser_kind_low =
                                     (if
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_low)
                                          <
                                          ((match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           false)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_low))
                                      then
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_low)
                                      else
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        false)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_low));
                                   LowParse_Spec_Base.parser_kind_high =
                                     (if
                                        (if
                                           match match FStar_Pervasives.dfst
                                                         (match p with
                                                          | {
                                                              parse_ifthenelse_tag_kind;
                                                              parse_ifthenelse_tag_t;
                                                              parse_ifthenelse_tag_parser;
                                                              parse_ifthenelse_tag_cond;
                                                              parse_ifthenelse_payload_t;
                                                              parse_ifthenelse_payload_parser;
                                                              parse_ifthenelse_t;
                                                              parse_ifthenelse_synth;
                                                              parse_ifthenelse_synth_injective;_}
                                                              ->
                                                              parse_ifthenelse_payload_parser
                                                                true)
                                                 with
                                                 | {
                                                     LowParse_Spec_Base.parser_kind_low
                                                       = parser_kind_low;
                                                     LowParse_Spec_Base.parser_kind_high
                                                       = parser_kind_high;
                                                     LowParse_Spec_Base.parser_kind_subkind
                                                       = parser_kind_subkind;
                                                     LowParse_Spec_Base.parser_kind_metadata
                                                       = parser_kind_metadata;_}
                                                     -> parser_kind_high
                                           with
                                           | FStar_Pervasives_Native.Some
                                               uu___1 -> true
                                           | uu___1 -> false
                                         then
                                           match match FStar_Pervasives.dfst
                                                         (match p with
                                                          | {
                                                              parse_ifthenelse_tag_kind;
                                                              parse_ifthenelse_tag_t;
                                                              parse_ifthenelse_tag_parser;
                                                              parse_ifthenelse_tag_cond;
                                                              parse_ifthenelse_payload_t;
                                                              parse_ifthenelse_payload_parser;
                                                              parse_ifthenelse_t;
                                                              parse_ifthenelse_synth;
                                                              parse_ifthenelse_synth_injective;_}
                                                              ->
                                                              parse_ifthenelse_payload_parser
                                                                false)
                                                 with
                                                 | {
                                                     LowParse_Spec_Base.parser_kind_low
                                                       = parser_kind_low;
                                                     LowParse_Spec_Base.parser_kind_high
                                                       = parser_kind_high;
                                                     LowParse_Spec_Base.parser_kind_subkind
                                                       = parser_kind_subkind;
                                                     LowParse_Spec_Base.parser_kind_metadata
                                                       = parser_kind_metadata;_}
                                                     -> parser_kind_high
                                           with
                                           | FStar_Pervasives_Native.Some
                                               uu___1 -> true
                                           | uu___1 -> false
                                         else false)
                                      then
                                        (if
                                           (match match FStar_Pervasives.dfst
                                                          (match p with
                                                           | {
                                                               parse_ifthenelse_tag_kind;
                                                               parse_ifthenelse_tag_t;
                                                               parse_ifthenelse_tag_parser;
                                                               parse_ifthenelse_tag_cond;
                                                               parse_ifthenelse_payload_t;
                                                               parse_ifthenelse_payload_parser;
                                                               parse_ifthenelse_t;
                                                               parse_ifthenelse_synth;
                                                               parse_ifthenelse_synth_injective;_}
                                                               ->
                                                               parse_ifthenelse_payload_parser
                                                                 false)
                                                  with
                                                  | {
                                                      LowParse_Spec_Base.parser_kind_low
                                                        = parser_kind_low;
                                                      LowParse_Spec_Base.parser_kind_high
                                                        = parser_kind_high;
                                                      LowParse_Spec_Base.parser_kind_subkind
                                                        = parser_kind_subkind;
                                                      LowParse_Spec_Base.parser_kind_metadata
                                                        =
                                                        parser_kind_metadata;_}
                                                      -> parser_kind_high
                                            with
                                            | FStar_Pervasives_Native.Some y
                                                -> y)
                                             <
                                             (match match FStar_Pervasives.dfst
                                                            (match p with
                                                             | {
                                                                 parse_ifthenelse_tag_kind;
                                                                 parse_ifthenelse_tag_t;
                                                                 parse_ifthenelse_tag_parser;
                                                                 parse_ifthenelse_tag_cond;
                                                                 parse_ifthenelse_payload_t;
                                                                 parse_ifthenelse_payload_parser;
                                                                 parse_ifthenelse_t;
                                                                 parse_ifthenelse_synth;
                                                                 parse_ifthenelse_synth_injective;_}
                                                                 ->
                                                                 parse_ifthenelse_payload_parser
                                                                   true)
                                                    with
                                                    | {
                                                        LowParse_Spec_Base.parser_kind_low
                                                          = parser_kind_low;
                                                        LowParse_Spec_Base.parser_kind_high
                                                          = parser_kind_high;
                                                        LowParse_Spec_Base.parser_kind_subkind
                                                          =
                                                          parser_kind_subkind;
                                                        LowParse_Spec_Base.parser_kind_metadata
                                                          =
                                                          parser_kind_metadata;_}
                                                        -> parser_kind_high
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  y -> y)
                                         then
                                           match FStar_Pervasives.dfst
                                                   (match p with
                                                    | {
                                                        parse_ifthenelse_tag_kind;
                                                        parse_ifthenelse_tag_t;
                                                        parse_ifthenelse_tag_parser;
                                                        parse_ifthenelse_tag_cond;
                                                        parse_ifthenelse_payload_t;
                                                        parse_ifthenelse_payload_parser;
                                                        parse_ifthenelse_t;
                                                        parse_ifthenelse_synth;
                                                        parse_ifthenelse_synth_injective;_}
                                                        ->
                                                        parse_ifthenelse_payload_parser
                                                          true)
                                           with
                                           | {
                                               LowParse_Spec_Base.parser_kind_low
                                                 = parser_kind_low;
                                               LowParse_Spec_Base.parser_kind_high
                                                 = parser_kind_high;
                                               LowParse_Spec_Base.parser_kind_subkind
                                                 = parser_kind_subkind;
                                               LowParse_Spec_Base.parser_kind_metadata
                                                 = parser_kind_metadata;_}
                                               -> parser_kind_high
                                         else
                                           (match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           false)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_high))
                                      else FStar_Pervasives_Native.None);
                                   LowParse_Spec_Base.parser_kind_subkind =
                                     (if
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_subkind)
                                          =
                                          ((match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           false)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_subkind))
                                      then
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_subkind)
                                      else FStar_Pervasives_Native.None);
                                   LowParse_Spec_Base.parser_kind_metadata =
                                     (if
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_metadata)
                                          =
                                          ((match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           false)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_metadata))
                                      then
                                        (match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_metadata)
                                      else FStar_Pervasives_Native.None)
                                 }
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
           (match match ((match FStar_Pervasives.dfst
                                  (match p with
                                   | { parse_ifthenelse_tag_kind;
                                       parse_ifthenelse_tag_t;
                                       parse_ifthenelse_tag_parser;
                                       parse_ifthenelse_tag_cond;
                                       parse_ifthenelse_payload_t;
                                       parse_ifthenelse_payload_parser;
                                       parse_ifthenelse_t;
                                       parse_ifthenelse_synth;
                                       parse_ifthenelse_synth_injective;_} ->
                                       parse_ifthenelse_payload_parser true)
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
                          (match FStar_Pervasives.dfst
                                   (match p with
                                    | { parse_ifthenelse_tag_kind;
                                        parse_ifthenelse_tag_t;
                                        parse_ifthenelse_tag_parser;
                                        parse_ifthenelse_tag_cond;
                                        parse_ifthenelse_payload_t;
                                        parse_ifthenelse_payload_parser;
                                        parse_ifthenelse_t;
                                        parse_ifthenelse_synth;
                                        parse_ifthenelse_synth_injective;_}
                                        ->
                                        parse_ifthenelse_payload_parser false)
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
                  | (uu___, FStar_Pervasives_Native.Some
                     (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                      {
                        LowParse_Spec_Base.parser_kind_low =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                                -> parser_kind_high));
                        LowParse_Spec_Base.parser_kind_subkind =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                                -> parser_kind_subkind));
                        LowParse_Spec_Base.parser_kind_metadata =
                          ((match match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                      -> parser_kind_metadata
                            with
                            | FStar_Pervasives_Native.Some
                                (LowParse_Spec_Base.ParserKindMetadataFail)
                                ->
                                FStar_Pervasives_Native.Some
                                  LowParse_Spec_Base.ParserKindMetadataFail
                            | uu___1 -> FStar_Pervasives_Native.None))
                      }
                  | (FStar_Pervasives_Native.Some
                     (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
                      {
                        LowParse_Spec_Base.parser_kind_low =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser
                                           false)
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
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser
                                           false)
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
                                -> parser_kind_high));
                        LowParse_Spec_Base.parser_kind_subkind =
                          ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser
                                           false)
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
                                -> parser_kind_subkind));
                        LowParse_Spec_Base.parser_kind_metadata =
                          FStar_Pervasives_Native.None
                      }
                  | uu___ ->
                      {
                        LowParse_Spec_Base.parser_kind_low =
                          (if
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                               <
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_low))
                           then
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                           else
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             false)
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
                                match match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_high
                                with
                                | FStar_Pervasives_Native.Some uu___1 -> true
                                | uu___1 -> false
                              then
                                match match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_high
                                with
                                | FStar_Pervasives_Native.Some uu___1 -> true
                                | uu___1 -> false
                              else false)
                           then
                             (if
                                (match match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high
                                 with
                                 | FStar_Pervasives_Native.Some y -> y) <
                                  (match match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_high
                                   with
                                   | FStar_Pervasives_Native.Some y -> y)
                              then
                                match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                              else
                                (match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_high))
                           else FStar_Pervasives_Native.None);
                        LowParse_Spec_Base.parser_kind_subkind =
                          (if
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_subkind))
                           then
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                          (if
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                               =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_metadata))
                           then
                             (match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                           else FStar_Pervasives_Native.None)
                      }
            with
            | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                LowParse_Spec_Base.parser_kind_metadata =
                  parser_kind_metadata;_}
                -> parser_kind_subkind)
             =
             (FStar_Pervasives_Native.Some
                LowParse_Spec_Base.ParserConsumesAll)
         then
           FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserConsumesAll
         else
           if
             (if
                (match match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_tag_kind
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
                     LowParse_Spec_Base.ParserStrong)
              then
                (match match ((match FStar_Pervasives.dfst
                                       (match p with
                                        | { parse_ifthenelse_tag_kind;
                                            parse_ifthenelse_tag_t;
                                            parse_ifthenelse_tag_parser;
                                            parse_ifthenelse_tag_cond;
                                            parse_ifthenelse_payload_t;
                                            parse_ifthenelse_payload_parser;
                                            parse_ifthenelse_t;
                                            parse_ifthenelse_synth;
                                            parse_ifthenelse_synth_injective;_}
                                            ->
                                            parse_ifthenelse_payload_parser
                                              true)
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
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               false)
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
                       | (uu___1, FStar_Pervasives_Native.Some
                          (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                           {
                             LowParse_Spec_Base.parser_kind_low =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                true)
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
                                     -> parser_kind_low));
                             LowParse_Spec_Base.parser_kind_high =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                true)
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
                                     -> parser_kind_high));
                             LowParse_Spec_Base.parser_kind_subkind =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                true)
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
                                     -> parser_kind_subkind));
                             LowParse_Spec_Base.parser_kind_metadata =
                               ((match match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      true)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_metadata
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (LowParse_Spec_Base.ParserKindMetadataFail)
                                     ->
                                     FStar_Pervasives_Native.Some
                                       LowParse_Spec_Base.ParserKindMetadataFail
                                 | uu___2 -> FStar_Pervasives_Native.None))
                           }
                       | (FStar_Pervasives_Native.Some
                          (LowParse_Spec_Base.ParserKindMetadataFail),
                          uu___1) ->
                           {
                             LowParse_Spec_Base.parser_kind_low =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_low));
                             LowParse_Spec_Base.parser_kind_high =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_high));
                             LowParse_Spec_Base.parser_kind_subkind =
                               ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_subkind));
                             LowParse_Spec_Base.parser_kind_metadata =
                               FStar_Pervasives_Native.None
                           }
                       | uu___1 ->
                           {
                             LowParse_Spec_Base.parser_kind_low =
                               (if
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_low)
                                    <
                                    ((match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_low))
                                then
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_low)
                                else
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_low));
                             LowParse_Spec_Base.parser_kind_high =
                               (if
                                  (if
                                     match match FStar_Pervasives.dfst
                                                   (match p with
                                                    | {
                                                        parse_ifthenelse_tag_kind;
                                                        parse_ifthenelse_tag_t;
                                                        parse_ifthenelse_tag_parser;
                                                        parse_ifthenelse_tag_cond;
                                                        parse_ifthenelse_payload_t;
                                                        parse_ifthenelse_payload_parser;
                                                        parse_ifthenelse_t;
                                                        parse_ifthenelse_synth;
                                                        parse_ifthenelse_synth_injective;_}
                                                        ->
                                                        parse_ifthenelse_payload_parser
                                                          true)
                                           with
                                           | {
                                               LowParse_Spec_Base.parser_kind_low
                                                 = parser_kind_low;
                                               LowParse_Spec_Base.parser_kind_high
                                                 = parser_kind_high;
                                               LowParse_Spec_Base.parser_kind_subkind
                                                 = parser_kind_subkind;
                                               LowParse_Spec_Base.parser_kind_metadata
                                                 = parser_kind_metadata;_}
                                               -> parser_kind_high
                                     with
                                     | FStar_Pervasives_Native.Some uu___2 ->
                                         true
                                     | uu___2 -> false
                                   then
                                     match match FStar_Pervasives.dfst
                                                   (match p with
                                                    | {
                                                        parse_ifthenelse_tag_kind;
                                                        parse_ifthenelse_tag_t;
                                                        parse_ifthenelse_tag_parser;
                                                        parse_ifthenelse_tag_cond;
                                                        parse_ifthenelse_payload_t;
                                                        parse_ifthenelse_payload_parser;
                                                        parse_ifthenelse_t;
                                                        parse_ifthenelse_synth;
                                                        parse_ifthenelse_synth_injective;_}
                                                        ->
                                                        parse_ifthenelse_payload_parser
                                                          false)
                                           with
                                           | {
                                               LowParse_Spec_Base.parser_kind_low
                                                 = parser_kind_low;
                                               LowParse_Spec_Base.parser_kind_high
                                                 = parser_kind_high;
                                               LowParse_Spec_Base.parser_kind_subkind
                                                 = parser_kind_subkind;
                                               LowParse_Spec_Base.parser_kind_metadata
                                                 = parser_kind_metadata;_}
                                               -> parser_kind_high
                                     with
                                     | FStar_Pervasives_Native.Some uu___2 ->
                                         true
                                     | uu___2 -> false
                                   else false)
                                then
                                  (if
                                     (match match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           false)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_high
                                      with
                                      | FStar_Pervasives_Native.Some y -> y)
                                       <
                                       (match match FStar_Pervasives.dfst
                                                      (match p with
                                                       | {
                                                           parse_ifthenelse_tag_kind;
                                                           parse_ifthenelse_tag_t;
                                                           parse_ifthenelse_tag_parser;
                                                           parse_ifthenelse_tag_cond;
                                                           parse_ifthenelse_payload_t;
                                                           parse_ifthenelse_payload_parser;
                                                           parse_ifthenelse_t;
                                                           parse_ifthenelse_synth;
                                                           parse_ifthenelse_synth_injective;_}
                                                           ->
                                                           parse_ifthenelse_payload_parser
                                                             true)
                                              with
                                              | {
                                                  LowParse_Spec_Base.parser_kind_low
                                                    = parser_kind_low;
                                                  LowParse_Spec_Base.parser_kind_high
                                                    = parser_kind_high;
                                                  LowParse_Spec_Base.parser_kind_subkind
                                                    = parser_kind_subkind;
                                                  LowParse_Spec_Base.parser_kind_metadata
                                                    = parser_kind_metadata;_}
                                                  -> parser_kind_high
                                        with
                                        | FStar_Pervasives_Native.Some y -> y)
                                   then
                                     match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_high
                                   else
                                     (match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_high))
                                else FStar_Pervasives_Native.None);
                             LowParse_Spec_Base.parser_kind_subkind =
                               (if
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_subkind)
                                    =
                                    ((match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_subkind))
                                then
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_subkind)
                                else FStar_Pervasives_Native.None);
                             LowParse_Spec_Base.parser_kind_metadata =
                               (if
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_metadata)
                                    =
                                    ((match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     false)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_metadata))
                                then
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_metadata)
                                else FStar_Pervasives_Native.None)
                           }
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
                     LowParse_Spec_Base.ParserStrong)
              else false)
           then FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
           else
             if
               (if
                  (match match ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                true)
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
                                     -> parser_kind_metadata),
                                 (match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 false)
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
                                      -> parser_kind_metadata))
                         with
                         | (uu___2, FStar_Pervasives_Native.Some
                            (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                             {
                               LowParse_Spec_Base.parser_kind_low =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_low));
                               LowParse_Spec_Base.parser_kind_high =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_high));
                               LowParse_Spec_Base.parser_kind_subkind =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_subkind));
                               LowParse_Spec_Base.parser_kind_metadata =
                                 ((match match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_metadata
                                   with
                                   | FStar_Pervasives_Native.Some
                                       (LowParse_Spec_Base.ParserKindMetadataFail)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         LowParse_Spec_Base.ParserKindMetadataFail
                                   | uu___3 -> FStar_Pervasives_Native.None))
                             }
                         | (FStar_Pervasives_Native.Some
                            (LowParse_Spec_Base.ParserKindMetadataFail),
                            uu___2) ->
                             {
                               LowParse_Spec_Base.parser_kind_low =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_low));
                               LowParse_Spec_Base.parser_kind_high =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_high));
                               LowParse_Spec_Base.parser_kind_subkind =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_subkind));
                               LowParse_Spec_Base.parser_kind_metadata =
                                 FStar_Pervasives_Native.None
                             }
                         | uu___2 ->
                             {
                               LowParse_Spec_Base.parser_kind_low =
                                 (if
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_low)
                                      <
                                      ((match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_low))
                                  then
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_low)
                                  else
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    false)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_low));
                               LowParse_Spec_Base.parser_kind_high =
                                 (if
                                    (if
                                       match match FStar_Pervasives.dfst
                                                     (match p with
                                                      | {
                                                          parse_ifthenelse_tag_kind;
                                                          parse_ifthenelse_tag_t;
                                                          parse_ifthenelse_tag_parser;
                                                          parse_ifthenelse_tag_cond;
                                                          parse_ifthenelse_payload_t;
                                                          parse_ifthenelse_payload_parser;
                                                          parse_ifthenelse_t;
                                                          parse_ifthenelse_synth;
                                                          parse_ifthenelse_synth_injective;_}
                                                          ->
                                                          parse_ifthenelse_payload_parser
                                                            true)
                                             with
                                             | {
                                                 LowParse_Spec_Base.parser_kind_low
                                                   = parser_kind_low;
                                                 LowParse_Spec_Base.parser_kind_high
                                                   = parser_kind_high;
                                                 LowParse_Spec_Base.parser_kind_subkind
                                                   = parser_kind_subkind;
                                                 LowParse_Spec_Base.parser_kind_metadata
                                                   = parser_kind_metadata;_}
                                                 -> parser_kind_high
                                       with
                                       | FStar_Pervasives_Native.Some uu___3
                                           -> true
                                       | uu___3 -> false
                                     then
                                       match match FStar_Pervasives.dfst
                                                     (match p with
                                                      | {
                                                          parse_ifthenelse_tag_kind;
                                                          parse_ifthenelse_tag_t;
                                                          parse_ifthenelse_tag_parser;
                                                          parse_ifthenelse_tag_cond;
                                                          parse_ifthenelse_payload_t;
                                                          parse_ifthenelse_payload_parser;
                                                          parse_ifthenelse_t;
                                                          parse_ifthenelse_synth;
                                                          parse_ifthenelse_synth_injective;_}
                                                          ->
                                                          parse_ifthenelse_payload_parser
                                                            false)
                                             with
                                             | {
                                                 LowParse_Spec_Base.parser_kind_low
                                                   = parser_kind_low;
                                                 LowParse_Spec_Base.parser_kind_high
                                                   = parser_kind_high;
                                                 LowParse_Spec_Base.parser_kind_subkind
                                                   = parser_kind_subkind;
                                                 LowParse_Spec_Base.parser_kind_metadata
                                                   = parser_kind_metadata;_}
                                                 -> parser_kind_high
                                       with
                                       | FStar_Pervasives_Native.Some uu___3
                                           -> true
                                       | uu___3 -> false
                                     else false)
                                  then
                                    (if
                                       (match match FStar_Pervasives.dfst
                                                      (match p with
                                                       | {
                                                           parse_ifthenelse_tag_kind;
                                                           parse_ifthenelse_tag_t;
                                                           parse_ifthenelse_tag_parser;
                                                           parse_ifthenelse_tag_cond;
                                                           parse_ifthenelse_payload_t;
                                                           parse_ifthenelse_payload_parser;
                                                           parse_ifthenelse_t;
                                                           parse_ifthenelse_synth;
                                                           parse_ifthenelse_synth_injective;_}
                                                           ->
                                                           parse_ifthenelse_payload_parser
                                                             false)
                                              with
                                              | {
                                                  LowParse_Spec_Base.parser_kind_low
                                                    = parser_kind_low;
                                                  LowParse_Spec_Base.parser_kind_high
                                                    = parser_kind_high;
                                                  LowParse_Spec_Base.parser_kind_subkind
                                                    = parser_kind_subkind;
                                                  LowParse_Spec_Base.parser_kind_metadata
                                                    = parser_kind_metadata;_}
                                                  -> parser_kind_high
                                        with
                                        | FStar_Pervasives_Native.Some y -> y)
                                         <
                                         (match match FStar_Pervasives.dfst
                                                        (match p with
                                                         | {
                                                             parse_ifthenelse_tag_kind;
                                                             parse_ifthenelse_tag_t;
                                                             parse_ifthenelse_tag_parser;
                                                             parse_ifthenelse_tag_cond;
                                                             parse_ifthenelse_payload_t;
                                                             parse_ifthenelse_payload_parser;
                                                             parse_ifthenelse_t;
                                                             parse_ifthenelse_synth;
                                                             parse_ifthenelse_synth_injective;_}
                                                             ->
                                                             parse_ifthenelse_payload_parser
                                                               true)
                                                with
                                                | {
                                                    LowParse_Spec_Base.parser_kind_low
                                                      = parser_kind_low;
                                                    LowParse_Spec_Base.parser_kind_high
                                                      = parser_kind_high;
                                                    LowParse_Spec_Base.parser_kind_subkind
                                                      = parser_kind_subkind;
                                                    LowParse_Spec_Base.parser_kind_metadata
                                                      = parser_kind_metadata;_}
                                                    -> parser_kind_high
                                          with
                                          | FStar_Pervasives_Native.Some y ->
                                              y)
                                     then
                                       match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      true)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high
                                     else
                                       (match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_high))
                                  else FStar_Pervasives_Native.None);
                               LowParse_Spec_Base.parser_kind_subkind =
                                 (if
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_subkind)
                                      =
                                      ((match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_subkind))
                                  then
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_subkind)
                                  else FStar_Pervasives_Native.None);
                               LowParse_Spec_Base.parser_kind_metadata =
                                 (if
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_metadata)
                                      =
                                      ((match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_metadata))
                                  then
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_metadata)
                                  else FStar_Pervasives_Native.None)
                             }
                   with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_high)
                    = (FStar_Pervasives_Native.Some Prims.int_zero)
                then
                  (match match ((match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                true)
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
                                     -> parser_kind_metadata),
                                 (match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 false)
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
                                      -> parser_kind_metadata))
                         with
                         | (uu___2, FStar_Pervasives_Native.Some
                            (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                             {
                               LowParse_Spec_Base.parser_kind_low =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_low));
                               LowParse_Spec_Base.parser_kind_high =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_high));
                               LowParse_Spec_Base.parser_kind_subkind =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  true)
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
                                       -> parser_kind_subkind));
                               LowParse_Spec_Base.parser_kind_metadata =
                                 ((match match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        true)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_metadata
                                   with
                                   | FStar_Pervasives_Native.Some
                                       (LowParse_Spec_Base.ParserKindMetadataFail)
                                       ->
                                       FStar_Pervasives_Native.Some
                                         LowParse_Spec_Base.ParserKindMetadataFail
                                   | uu___3 -> FStar_Pervasives_Native.None))
                             }
                         | (FStar_Pervasives_Native.Some
                            (LowParse_Spec_Base.ParserKindMetadataFail),
                            uu___2) ->
                             {
                               LowParse_Spec_Base.parser_kind_low =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_low));
                               LowParse_Spec_Base.parser_kind_high =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_high));
                               LowParse_Spec_Base.parser_kind_subkind =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_subkind));
                               LowParse_Spec_Base.parser_kind_metadata =
                                 FStar_Pervasives_Native.None
                             }
                         | uu___2 ->
                             {
                               LowParse_Spec_Base.parser_kind_low =
                                 (if
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_low)
                                      <
                                      ((match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_low))
                                  then
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_low)
                                  else
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    false)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_low));
                               LowParse_Spec_Base.parser_kind_high =
                                 (if
                                    (if
                                       match match FStar_Pervasives.dfst
                                                     (match p with
                                                      | {
                                                          parse_ifthenelse_tag_kind;
                                                          parse_ifthenelse_tag_t;
                                                          parse_ifthenelse_tag_parser;
                                                          parse_ifthenelse_tag_cond;
                                                          parse_ifthenelse_payload_t;
                                                          parse_ifthenelse_payload_parser;
                                                          parse_ifthenelse_t;
                                                          parse_ifthenelse_synth;
                                                          parse_ifthenelse_synth_injective;_}
                                                          ->
                                                          parse_ifthenelse_payload_parser
                                                            true)
                                             with
                                             | {
                                                 LowParse_Spec_Base.parser_kind_low
                                                   = parser_kind_low;
                                                 LowParse_Spec_Base.parser_kind_high
                                                   = parser_kind_high;
                                                 LowParse_Spec_Base.parser_kind_subkind
                                                   = parser_kind_subkind;
                                                 LowParse_Spec_Base.parser_kind_metadata
                                                   = parser_kind_metadata;_}
                                                 -> parser_kind_high
                                       with
                                       | FStar_Pervasives_Native.Some uu___3
                                           -> true
                                       | uu___3 -> false
                                     then
                                       match match FStar_Pervasives.dfst
                                                     (match p with
                                                      | {
                                                          parse_ifthenelse_tag_kind;
                                                          parse_ifthenelse_tag_t;
                                                          parse_ifthenelse_tag_parser;
                                                          parse_ifthenelse_tag_cond;
                                                          parse_ifthenelse_payload_t;
                                                          parse_ifthenelse_payload_parser;
                                                          parse_ifthenelse_t;
                                                          parse_ifthenelse_synth;
                                                          parse_ifthenelse_synth_injective;_}
                                                          ->
                                                          parse_ifthenelse_payload_parser
                                                            false)
                                             with
                                             | {
                                                 LowParse_Spec_Base.parser_kind_low
                                                   = parser_kind_low;
                                                 LowParse_Spec_Base.parser_kind_high
                                                   = parser_kind_high;
                                                 LowParse_Spec_Base.parser_kind_subkind
                                                   = parser_kind_subkind;
                                                 LowParse_Spec_Base.parser_kind_metadata
                                                   = parser_kind_metadata;_}
                                                 -> parser_kind_high
                                       with
                                       | FStar_Pervasives_Native.Some uu___3
                                           -> true
                                       | uu___3 -> false
                                     else false)
                                  then
                                    (if
                                       (match match FStar_Pervasives.dfst
                                                      (match p with
                                                       | {
                                                           parse_ifthenelse_tag_kind;
                                                           parse_ifthenelse_tag_t;
                                                           parse_ifthenelse_tag_parser;
                                                           parse_ifthenelse_tag_cond;
                                                           parse_ifthenelse_payload_t;
                                                           parse_ifthenelse_payload_parser;
                                                           parse_ifthenelse_t;
                                                           parse_ifthenelse_synth;
                                                           parse_ifthenelse_synth_injective;_}
                                                           ->
                                                           parse_ifthenelse_payload_parser
                                                             false)
                                              with
                                              | {
                                                  LowParse_Spec_Base.parser_kind_low
                                                    = parser_kind_low;
                                                  LowParse_Spec_Base.parser_kind_high
                                                    = parser_kind_high;
                                                  LowParse_Spec_Base.parser_kind_subkind
                                                    = parser_kind_subkind;
                                                  LowParse_Spec_Base.parser_kind_metadata
                                                    = parser_kind_metadata;_}
                                                  -> parser_kind_high
                                        with
                                        | FStar_Pervasives_Native.Some y -> y)
                                         <
                                         (match match FStar_Pervasives.dfst
                                                        (match p with
                                                         | {
                                                             parse_ifthenelse_tag_kind;
                                                             parse_ifthenelse_tag_t;
                                                             parse_ifthenelse_tag_parser;
                                                             parse_ifthenelse_tag_cond;
                                                             parse_ifthenelse_payload_t;
                                                             parse_ifthenelse_payload_parser;
                                                             parse_ifthenelse_t;
                                                             parse_ifthenelse_synth;
                                                             parse_ifthenelse_synth_injective;_}
                                                             ->
                                                             parse_ifthenelse_payload_parser
                                                               true)
                                                with
                                                | {
                                                    LowParse_Spec_Base.parser_kind_low
                                                      = parser_kind_low;
                                                    LowParse_Spec_Base.parser_kind_high
                                                      = parser_kind_high;
                                                    LowParse_Spec_Base.parser_kind_subkind
                                                      = parser_kind_subkind;
                                                    LowParse_Spec_Base.parser_kind_metadata
                                                      = parser_kind_metadata;_}
                                                    -> parser_kind_high
                                          with
                                          | FStar_Pervasives_Native.Some y ->
                                              y)
                                     then
                                       match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      true)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high
                                     else
                                       (match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_high))
                                  else FStar_Pervasives_Native.None);
                               LowParse_Spec_Base.parser_kind_subkind =
                                 (if
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_subkind)
                                      =
                                      ((match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_subkind))
                                  then
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_subkind)
                                  else FStar_Pervasives_Native.None);
                               LowParse_Spec_Base.parser_kind_metadata =
                                 (if
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_metadata)
                                      =
                                      ((match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_metadata))
                                  then
                                    (match FStar_Pervasives.dfst
                                             (match p with
                                              | { parse_ifthenelse_tag_kind;
                                                  parse_ifthenelse_tag_t;
                                                  parse_ifthenelse_tag_parser;
                                                  parse_ifthenelse_tag_cond;
                                                  parse_ifthenelse_payload_t;
                                                  parse_ifthenelse_payload_parser;
                                                  parse_ifthenelse_t;
                                                  parse_ifthenelse_synth;
                                                  parse_ifthenelse_synth_injective;_}
                                                  ->
                                                  parse_ifthenelse_payload_parser
                                                    true)
                                     with
                                     | {
                                         LowParse_Spec_Base.parser_kind_low =
                                           parser_kind_low;
                                         LowParse_Spec_Base.parser_kind_high
                                           = parser_kind_high;
                                         LowParse_Spec_Base.parser_kind_subkind
                                           = parser_kind_subkind;
                                         LowParse_Spec_Base.parser_kind_metadata
                                           = parser_kind_metadata;_}
                                         -> parser_kind_metadata)
                                  else FStar_Pervasives_Native.None)
                             }
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
                       LowParse_Spec_Base.ParserStrong)
                else false)
             then
               (match match p with
                      | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                          parse_ifthenelse_tag_parser;
                          parse_ifthenelse_tag_cond;
                          parse_ifthenelse_payload_t;
                          parse_ifthenelse_payload_parser;
                          parse_ifthenelse_t; parse_ifthenelse_synth;
                          parse_ifthenelse_synth_injective;_} ->
                          parse_ifthenelse_tag_kind
                with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_subkind)
             else FStar_Pervasives_Native.None);
      LowParse_Spec_Base.parser_kind_metadata =
        (match ((match match p with
                       | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                           parse_ifthenelse_tag_parser;
                           parse_ifthenelse_tag_cond;
                           parse_ifthenelse_payload_t;
                           parse_ifthenelse_payload_parser;
                           parse_ifthenelse_t; parse_ifthenelse_synth;
                           parse_ifthenelse_synth_injective;_} ->
                           parse_ifthenelse_tag_kind
                 with
                 | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                     LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                     LowParse_Spec_Base.parser_kind_subkind =
                       parser_kind_subkind;
                     LowParse_Spec_Base.parser_kind_metadata =
                       parser_kind_metadata;_}
                     -> parser_kind_metadata),
                 (match match ((match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                                (match FStar_Pervasives.dfst
                                         (match p with
                                          | { parse_ifthenelse_tag_kind;
                                              parse_ifthenelse_tag_t;
                                              parse_ifthenelse_tag_parser;
                                              parse_ifthenelse_tag_cond;
                                              parse_ifthenelse_payload_t;
                                              parse_ifthenelse_payload_parser;
                                              parse_ifthenelse_t;
                                              parse_ifthenelse_synth;
                                              parse_ifthenelse_synth_injective;_}
                                              ->
                                              parse_ifthenelse_payload_parser
                                                false)
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
                                     -> parser_kind_metadata))
                        with
                        | (uu___, FStar_Pervasives_Native.Some
                           (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                            {
                              LowParse_Spec_Base.parser_kind_low =
                                ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                      -> parser_kind_low));
                              LowParse_Spec_Base.parser_kind_high =
                                ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                      -> parser_kind_high));
                              LowParse_Spec_Base.parser_kind_subkind =
                                ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                      -> parser_kind_subkind));
                              LowParse_Spec_Base.parser_kind_metadata =
                                ((match match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       true)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_metadata
                                  with
                                  | FStar_Pervasives_Native.Some
                                      (LowParse_Spec_Base.ParserKindMetadataFail)
                                      ->
                                      FStar_Pervasives_Native.Some
                                        LowParse_Spec_Base.ParserKindMetadataFail
                                  | uu___1 -> FStar_Pervasives_Native.None))
                            }
                        | (FStar_Pervasives_Native.Some
                           (LowParse_Spec_Base.ParserKindMetadataFail),
                           uu___) ->
                            {
                              LowParse_Spec_Base.parser_kind_low =
                                ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 false)
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
                                      -> parser_kind_low));
                              LowParse_Spec_Base.parser_kind_high =
                                ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 false)
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
                                      -> parser_kind_high));
                              LowParse_Spec_Base.parser_kind_subkind =
                                ((match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 false)
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
                                      -> parser_kind_subkind));
                              LowParse_Spec_Base.parser_kind_metadata =
                                FStar_Pervasives_Native.None
                            }
                        | uu___ ->
                            {
                              LowParse_Spec_Base.parser_kind_low =
                                (if
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_low)
                                     <
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_low))
                                 then
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_low)
                                 else
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   false)
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
                                        -> parser_kind_low));
                              LowParse_Spec_Base.parser_kind_high =
                                (if
                                   (if
                                      match match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           true)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_high
                                      with
                                      | FStar_Pervasives_Native.Some uu___1
                                          -> true
                                      | uu___1 -> false
                                    then
                                      match match FStar_Pervasives.dfst
                                                    (match p with
                                                     | {
                                                         parse_ifthenelse_tag_kind;
                                                         parse_ifthenelse_tag_t;
                                                         parse_ifthenelse_tag_parser;
                                                         parse_ifthenelse_tag_cond;
                                                         parse_ifthenelse_payload_t;
                                                         parse_ifthenelse_payload_parser;
                                                         parse_ifthenelse_t;
                                                         parse_ifthenelse_synth;
                                                         parse_ifthenelse_synth_injective;_}
                                                         ->
                                                         parse_ifthenelse_payload_parser
                                                           false)
                                            with
                                            | {
                                                LowParse_Spec_Base.parser_kind_low
                                                  = parser_kind_low;
                                                LowParse_Spec_Base.parser_kind_high
                                                  = parser_kind_high;
                                                LowParse_Spec_Base.parser_kind_subkind
                                                  = parser_kind_subkind;
                                                LowParse_Spec_Base.parser_kind_metadata
                                                  = parser_kind_metadata;_}
                                                -> parser_kind_high
                                      with
                                      | FStar_Pervasives_Native.Some uu___1
                                          -> true
                                      | uu___1 -> false
                                    else false)
                                 then
                                   (if
                                      (match match FStar_Pervasives.dfst
                                                     (match p with
                                                      | {
                                                          parse_ifthenelse_tag_kind;
                                                          parse_ifthenelse_tag_t;
                                                          parse_ifthenelse_tag_parser;
                                                          parse_ifthenelse_tag_cond;
                                                          parse_ifthenelse_payload_t;
                                                          parse_ifthenelse_payload_parser;
                                                          parse_ifthenelse_t;
                                                          parse_ifthenelse_synth;
                                                          parse_ifthenelse_synth_injective;_}
                                                          ->
                                                          parse_ifthenelse_payload_parser
                                                            false)
                                             with
                                             | {
                                                 LowParse_Spec_Base.parser_kind_low
                                                   = parser_kind_low;
                                                 LowParse_Spec_Base.parser_kind_high
                                                   = parser_kind_high;
                                                 LowParse_Spec_Base.parser_kind_subkind
                                                   = parser_kind_subkind;
                                                 LowParse_Spec_Base.parser_kind_metadata
                                                   = parser_kind_metadata;_}
                                                 -> parser_kind_high
                                       with
                                       | FStar_Pervasives_Native.Some y -> y)
                                        <
                                        (match match FStar_Pervasives.dfst
                                                       (match p with
                                                        | {
                                                            parse_ifthenelse_tag_kind;
                                                            parse_ifthenelse_tag_t;
                                                            parse_ifthenelse_tag_parser;
                                                            parse_ifthenelse_tag_cond;
                                                            parse_ifthenelse_payload_t;
                                                            parse_ifthenelse_payload_parser;
                                                            parse_ifthenelse_t;
                                                            parse_ifthenelse_synth;
                                                            parse_ifthenelse_synth_injective;_}
                                                            ->
                                                            parse_ifthenelse_payload_parser
                                                              true)
                                               with
                                               | {
                                                   LowParse_Spec_Base.parser_kind_low
                                                     = parser_kind_low;
                                                   LowParse_Spec_Base.parser_kind_high
                                                     = parser_kind_high;
                                                   LowParse_Spec_Base.parser_kind_subkind
                                                     = parser_kind_subkind;
                                                   LowParse_Spec_Base.parser_kind_metadata
                                                     = parser_kind_metadata;_}
                                                   -> parser_kind_high
                                         with
                                         | FStar_Pervasives_Native.Some y ->
                                             y)
                                    then
                                      match FStar_Pervasives.dfst
                                              (match p with
                                               | { parse_ifthenelse_tag_kind;
                                                   parse_ifthenelse_tag_t;
                                                   parse_ifthenelse_tag_parser;
                                                   parse_ifthenelse_tag_cond;
                                                   parse_ifthenelse_payload_t;
                                                   parse_ifthenelse_payload_parser;
                                                   parse_ifthenelse_t;
                                                   parse_ifthenelse_synth;
                                                   parse_ifthenelse_synth_injective;_}
                                                   ->
                                                   parse_ifthenelse_payload_parser
                                                     true)
                                      with
                                      | {
                                          LowParse_Spec_Base.parser_kind_low
                                            = parser_kind_low;
                                          LowParse_Spec_Base.parser_kind_high
                                            = parser_kind_high;
                                          LowParse_Spec_Base.parser_kind_subkind
                                            = parser_kind_subkind;
                                          LowParse_Spec_Base.parser_kind_metadata
                                            = parser_kind_metadata;_}
                                          -> parser_kind_high
                                    else
                                      (match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_high))
                                 else FStar_Pervasives_Native.None);
                              LowParse_Spec_Base.parser_kind_subkind =
                                (if
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_subkind)
                                     =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_subkind))
                                 then
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_subkind)
                                 else FStar_Pervasives_Native.None);
                              LowParse_Spec_Base.parser_kind_metadata =
                                (if
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_metadata)
                                     =
                                     ((match FStar_Pervasives.dfst
                                               (match p with
                                                | {
                                                    parse_ifthenelse_tag_kind;
                                                    parse_ifthenelse_tag_t;
                                                    parse_ifthenelse_tag_parser;
                                                    parse_ifthenelse_tag_cond;
                                                    parse_ifthenelse_payload_t;
                                                    parse_ifthenelse_payload_parser;
                                                    parse_ifthenelse_t;
                                                    parse_ifthenelse_synth;
                                                    parse_ifthenelse_synth_injective;_}
                                                    ->
                                                    parse_ifthenelse_payload_parser
                                                      false)
                                       with
                                       | {
                                           LowParse_Spec_Base.parser_kind_low
                                             = parser_kind_low;
                                           LowParse_Spec_Base.parser_kind_high
                                             = parser_kind_high;
                                           LowParse_Spec_Base.parser_kind_subkind
                                             = parser_kind_subkind;
                                           LowParse_Spec_Base.parser_kind_metadata
                                             = parser_kind_metadata;_}
                                           -> parser_kind_metadata))
                                 then
                                   (match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_metadata)
                                 else FStar_Pervasives_Native.None)
                            }
                  with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_metadata))
         with
         | (FStar_Pervasives_Native.Some
            (LowParse_Spec_Base.ParserKindMetadataFail), uu___) ->
             (match match p with
                    | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                        parse_ifthenelse_tag_parser;
                        parse_ifthenelse_tag_cond;
                        parse_ifthenelse_payload_t;
                        parse_ifthenelse_payload_parser; parse_ifthenelse_t;
                        parse_ifthenelse_synth;
                        parse_ifthenelse_synth_injective;_} ->
                        parse_ifthenelse_tag_kind
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_metadata)
         | (uu___, FStar_Pervasives_Native.Some
            (LowParse_Spec_Base.ParserKindMetadataFail)) ->
             (match match ((match FStar_Pervasives.dfst
                                    (match p with
                                     | { parse_ifthenelse_tag_kind;
                                         parse_ifthenelse_tag_t;
                                         parse_ifthenelse_tag_parser;
                                         parse_ifthenelse_tag_cond;
                                         parse_ifthenelse_payload_t;
                                         parse_ifthenelse_payload_parser;
                                         parse_ifthenelse_t;
                                         parse_ifthenelse_synth;
                                         parse_ifthenelse_synth_injective;_}
                                         ->
                                         parse_ifthenelse_payload_parser true)
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
                            (match FStar_Pervasives.dfst
                                     (match p with
                                      | { parse_ifthenelse_tag_kind;
                                          parse_ifthenelse_tag_t;
                                          parse_ifthenelse_tag_parser;
                                          parse_ifthenelse_tag_cond;
                                          parse_ifthenelse_payload_t;
                                          parse_ifthenelse_payload_parser;
                                          parse_ifthenelse_t;
                                          parse_ifthenelse_synth;
                                          parse_ifthenelse_synth_injective;_}
                                          ->
                                          parse_ifthenelse_payload_parser
                                            false)
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
                    | (uu___1, FStar_Pervasives_Native.Some
                       (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                        {
                          LowParse_Spec_Base.parser_kind_low =
                            ((match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                            ((match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                                  -> parser_kind_high));
                          LowParse_Spec_Base.parser_kind_subkind =
                            ((match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             true)
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
                                  -> parser_kind_subkind));
                          LowParse_Spec_Base.parser_kind_metadata =
                            ((match match FStar_Pervasives.dfst
                                            (match p with
                                             | { parse_ifthenelse_tag_kind;
                                                 parse_ifthenelse_tag_t;
                                                 parse_ifthenelse_tag_parser;
                                                 parse_ifthenelse_tag_cond;
                                                 parse_ifthenelse_payload_t;
                                                 parse_ifthenelse_payload_parser;
                                                 parse_ifthenelse_t;
                                                 parse_ifthenelse_synth;
                                                 parse_ifthenelse_synth_injective;_}
                                                 ->
                                                 parse_ifthenelse_payload_parser
                                                   true)
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
                                        -> parser_kind_metadata
                              with
                              | FStar_Pervasives_Native.Some
                                  (LowParse_Spec_Base.ParserKindMetadataFail)
                                  ->
                                  FStar_Pervasives_Native.Some
                                    LowParse_Spec_Base.ParserKindMetadataFail
                              | uu___2 -> FStar_Pervasives_Native.None))
                        }
                    | (FStar_Pervasives_Native.Some
                       (LowParse_Spec_Base.ParserKindMetadataFail), uu___1)
                        ->
                        {
                          LowParse_Spec_Base.parser_kind_low =
                            ((match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             false)
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
                            ((match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             false)
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
                                  -> parser_kind_high));
                          LowParse_Spec_Base.parser_kind_subkind =
                            ((match FStar_Pervasives.dfst
                                      (match p with
                                       | { parse_ifthenelse_tag_kind;
                                           parse_ifthenelse_tag_t;
                                           parse_ifthenelse_tag_parser;
                                           parse_ifthenelse_tag_cond;
                                           parse_ifthenelse_payload_t;
                                           parse_ifthenelse_payload_parser;
                                           parse_ifthenelse_t;
                                           parse_ifthenelse_synth;
                                           parse_ifthenelse_synth_injective;_}
                                           ->
                                           parse_ifthenelse_payload_parser
                                             false)
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
                                  -> parser_kind_subkind));
                          LowParse_Spec_Base.parser_kind_metadata =
                            FStar_Pervasives_Native.None
                        }
                    | uu___1 ->
                        {
                          LowParse_Spec_Base.parser_kind_low =
                            (if
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                                 <
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_low))
                             then
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                             else
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               false)
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
                                  match match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       true)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_high
                                  with
                                  | FStar_Pervasives_Native.Some uu___2 ->
                                      true
                                  | uu___2 -> false
                                then
                                  match match FStar_Pervasives.dfst
                                                (match p with
                                                 | {
                                                     parse_ifthenelse_tag_kind;
                                                     parse_ifthenelse_tag_t;
                                                     parse_ifthenelse_tag_parser;
                                                     parse_ifthenelse_tag_cond;
                                                     parse_ifthenelse_payload_t;
                                                     parse_ifthenelse_payload_parser;
                                                     parse_ifthenelse_t;
                                                     parse_ifthenelse_synth;
                                                     parse_ifthenelse_synth_injective;_}
                                                     ->
                                                     parse_ifthenelse_payload_parser
                                                       false)
                                        with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_high
                                  with
                                  | FStar_Pervasives_Native.Some uu___2 ->
                                      true
                                  | uu___2 -> false
                                else false)
                             then
                               (if
                                  (match match FStar_Pervasives.dfst
                                                 (match p with
                                                  | {
                                                      parse_ifthenelse_tag_kind;
                                                      parse_ifthenelse_tag_t;
                                                      parse_ifthenelse_tag_parser;
                                                      parse_ifthenelse_tag_cond;
                                                      parse_ifthenelse_payload_t;
                                                      parse_ifthenelse_payload_parser;
                                                      parse_ifthenelse_t;
                                                      parse_ifthenelse_synth;
                                                      parse_ifthenelse_synth_injective;_}
                                                      ->
                                                      parse_ifthenelse_payload_parser
                                                        false)
                                         with
                                         | {
                                             LowParse_Spec_Base.parser_kind_low
                                               = parser_kind_low;
                                             LowParse_Spec_Base.parser_kind_high
                                               = parser_kind_high;
                                             LowParse_Spec_Base.parser_kind_subkind
                                               = parser_kind_subkind;
                                             LowParse_Spec_Base.parser_kind_metadata
                                               = parser_kind_metadata;_}
                                             -> parser_kind_high
                                   with
                                   | FStar_Pervasives_Native.Some y -> y) <
                                    (match match FStar_Pervasives.dfst
                                                   (match p with
                                                    | {
                                                        parse_ifthenelse_tag_kind;
                                                        parse_ifthenelse_tag_t;
                                                        parse_ifthenelse_tag_parser;
                                                        parse_ifthenelse_tag_cond;
                                                        parse_ifthenelse_payload_t;
                                                        parse_ifthenelse_payload_parser;
                                                        parse_ifthenelse_t;
                                                        parse_ifthenelse_synth;
                                                        parse_ifthenelse_synth_injective;_}
                                                        ->
                                                        parse_ifthenelse_payload_parser
                                                          true)
                                           with
                                           | {
                                               LowParse_Spec_Base.parser_kind_low
                                                 = parser_kind_low;
                                               LowParse_Spec_Base.parser_kind_high
                                                 = parser_kind_high;
                                               LowParse_Spec_Base.parser_kind_subkind
                                                 = parser_kind_subkind;
                                               LowParse_Spec_Base.parser_kind_metadata
                                                 = parser_kind_metadata;_}
                                               -> parser_kind_high
                                     with
                                     | FStar_Pervasives_Native.Some y -> y)
                                then
                                  match FStar_Pervasives.dfst
                                          (match p with
                                           | { parse_ifthenelse_tag_kind;
                                               parse_ifthenelse_tag_t;
                                               parse_ifthenelse_tag_parser;
                                               parse_ifthenelse_tag_cond;
                                               parse_ifthenelse_payload_t;
                                               parse_ifthenelse_payload_parser;
                                               parse_ifthenelse_t;
                                               parse_ifthenelse_synth;
                                               parse_ifthenelse_synth_injective;_}
                                               ->
                                               parse_ifthenelse_payload_parser
                                                 true)
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
                                else
                                  (match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_high))
                             else FStar_Pervasives_Native.None);
                          LowParse_Spec_Base.parser_kind_subkind =
                            (if
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_subkind))
                             then
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                            (if
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                                 =
                                 ((match FStar_Pervasives.dfst
                                           (match p with
                                            | { parse_ifthenelse_tag_kind;
                                                parse_ifthenelse_tag_t;
                                                parse_ifthenelse_tag_parser;
                                                parse_ifthenelse_tag_cond;
                                                parse_ifthenelse_payload_t;
                                                parse_ifthenelse_payload_parser;
                                                parse_ifthenelse_t;
                                                parse_ifthenelse_synth;
                                                parse_ifthenelse_synth_injective;_}
                                                ->
                                                parse_ifthenelse_payload_parser
                                                  false)
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
                                       -> parser_kind_metadata))
                             then
                               (match FStar_Pervasives.dfst
                                        (match p with
                                         | { parse_ifthenelse_tag_kind;
                                             parse_ifthenelse_tag_t;
                                             parse_ifthenelse_tag_parser;
                                             parse_ifthenelse_tag_cond;
                                             parse_ifthenelse_payload_t;
                                             parse_ifthenelse_payload_parser;
                                             parse_ifthenelse_t;
                                             parse_ifthenelse_synth;
                                             parse_ifthenelse_synth_injective;_}
                                             ->
                                             parse_ifthenelse_payload_parser
                                               true)
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
                             else FStar_Pervasives_Native.None)
                        }
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_metadata)
         | (FStar_Pervasives_Native.Some
            (LowParse_Spec_Base.ParserKindMetadataTotal),
            FStar_Pervasives_Native.Some
            (LowParse_Spec_Base.ParserKindMetadataTotal)) ->
             (match match p with
                    | { parse_ifthenelse_tag_kind; parse_ifthenelse_tag_t;
                        parse_ifthenelse_tag_parser;
                        parse_ifthenelse_tag_cond;
                        parse_ifthenelse_payload_t;
                        parse_ifthenelse_payload_parser; parse_ifthenelse_t;
                        parse_ifthenelse_synth;
                        parse_ifthenelse_synth_injective;_} ->
                        parse_ifthenelse_tag_kind
              with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_metadata)
         | uu___ -> FStar_Pervasives_Native.None)
    }









