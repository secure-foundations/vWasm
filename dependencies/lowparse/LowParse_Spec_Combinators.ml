open Prims

type ('sz, 't, 'f, 's1, 's2) make_constant_size_parser_precond_precond = unit
type ('sz, 't, 'f) make_constant_size_parser_precond = unit
type ('sz, 't, 'f) make_constant_size_parser_precond' = unit

let (constant_size_parser_kind : Prims.nat -> LowParse_Spec_Base.parser_kind)
  =
  fun sz ->
    {
      LowParse_Spec_Base.parser_kind_low = sz;
      LowParse_Spec_Base.parser_kind_high = (FStar_Pervasives_Native.Some sz);
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }

type ('sz, 't, 'f) make_total_constant_size_parser_precond = unit


let (parse_ret_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some Prims.int_zero);
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some
         LowParse_Spec_Base.ParserKindMetadataTotal)
  }




type 'k fail_parser_kind_precond = unit



let (parse_false_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some Prims.int_zero);
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserKindMetadataFail)
  }



type ('t, 'tu, 'pu, 'x1, 'x2, 'b1, 'b2) and_then_cases_injective_precond =
  unit
type ('t, 'tu, 'pu) and_then_cases_injective = unit



let (and_then_metadata :
  LowParse_Spec_Base.parser_kind_metadata_t ->
    LowParse_Spec_Base.parser_kind_metadata_t ->
      LowParse_Spec_Base.parser_kind_metadata_t)
  =
  fun k1 ->
    fun k2 ->
      match (k1, k2) with
      | (FStar_Pervasives_Native.Some
         (LowParse_Spec_Base.ParserKindMetadataFail), uu___) -> k1
      | (uu___, FStar_Pervasives_Native.Some
         (LowParse_Spec_Base.ParserKindMetadataFail)) -> k2
      | (FStar_Pervasives_Native.Some
         (LowParse_Spec_Base.ParserKindMetadataTotal),
         FStar_Pervasives_Native.Some
         (LowParse_Spec_Base.ParserKindMetadataTotal)) -> k1
      | uu___ -> FStar_Pervasives_Native.None
let (and_then_kind :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun k1 ->
    fun k2 ->
      {
        LowParse_Spec_Base.parser_kind_low =
          ((match k1 with
            | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                LowParse_Spec_Base.parser_kind_metadata =
                  parser_kind_metadata;_}
                -> parser_kind_low)
             +
             (match k2 with
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
                match match k1 with
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
                match match k2 with
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
               ((match match k1 with
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
                  (match match k2 with
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
             (match k2 with
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
                  (match k1 with
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
                  (match k2 with
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
               FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
             else
               if
                 (if
                    (match k2 with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_high)
                      = (FStar_Pervasives_Native.Some Prims.int_zero)
                  then
                    (match k2 with
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
                  else false)
               then
                 (match k1 with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_subkind)
               else FStar_Pervasives_Native.None);
        LowParse_Spec_Base.parser_kind_metadata =
          (match ((match k1 with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_metadata),
                   (match k2 with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
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
               (match k1 with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_metadata)
           | (uu___, FStar_Pervasives_Native.Some
              (LowParse_Spec_Base.ParserKindMetadataFail)) ->
               (match k2 with
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
               (match k1 with
                | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                    LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                    LowParse_Spec_Base.parser_kind_subkind =
                      parser_kind_subkind;
                    LowParse_Spec_Base.parser_kind_metadata =
                      parser_kind_metadata;_}
                    -> parser_kind_metadata)
           | uu___ -> FStar_Pervasives_Native.None)
      }






type ('t1, 't2, 'f) synth_injective = unit







type ('t1, 't2, 'f2, 'g1) synth_inverse = unit











let synth_tagged_union_data :
  'tagut 'dataut . unit -> 'tagut -> 'dataut -> 'dataut =
  fun tag_of_data -> fun tg -> fun x -> x












let synth_dtuple2 : 't1 't2 . 't1 -> 't2 -> ('t1, 't2) Prims.dtuple2 =
  fun x -> fun y -> Prims.Mkdtuple2 (x, y)

let synth_dtuple2_recip : 't1 't2 . 't1 -> ('t1, 't2) Prims.dtuple2 -> 't2 =
  fun x -> fun y -> FStar_Pervasives.dsnd y





















type ('k, 't1, 'p1, 'p2) parse_strengthen_prf = unit
















let (parse_filter_kind :
  LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind) =
  fun k ->
    {
      LowParse_Spec_Base.parser_kind_low =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_low);
      LowParse_Spec_Base.parser_kind_high =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_high);
      LowParse_Spec_Base.parser_kind_subkind =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_subkind);
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
let (parse_filter_payload_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some Prims.int_zero);
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }
type ('t, 'f) parse_filter_refine = 't







type 'cond cond_true = unit
type 'cond cond_false = unit