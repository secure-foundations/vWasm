open Prims
let rec (to_uint8 : Prims.nat -> unit FStar_BitVector.bv_t -> FStar_UInt8.t)
  =
  fun n ->
    fun x ->
      if n = Prims.int_zero
      then FStar_UInt8.uint_to_t Prims.int_zero
      else
        (let hi =
           to_uint8 (n - Prims.int_one)
             (FStar_Seq_Base.slice x Prims.int_zero (n - Prims.int_one)) in
         let hi' =
           FStar_UInt8.mul hi (FStar_UInt8.uint_to_t (Prims.of_int (2))) in
         let r =
           if FStar_Seq_Base.index x (n - Prims.int_one)
           then FStar_UInt8.uint_to_t Prims.int_one
           else FStar_UInt8.uint_to_t Prims.int_zero in
         FStar_UInt8.add hi' r)
let rec (of_uint8 : Prims.nat -> FStar_UInt8.t -> unit FStar_BitVector.bv_t)
  =
  fun n ->
    fun x ->
      if n = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let hi =
           of_uint8 (n - Prims.int_one)
             (FStar_UInt8.div x (FStar_UInt8.uint_to_t (Prims.of_int (2)))) in
         FStar_Seq_Properties.snoc hi
           ((FStar_UInt8.rem x (FStar_UInt8.uint_to_t (Prims.of_int (2)))) =
              (FStar_UInt8.uint_to_t Prims.int_one)))


let (synth_bv8 : FStar_UInt8.t -> unit FStar_BitVector.bv_t) =
  fun x -> of_uint8 (Prims.of_int (8)) x
let (synth_bv8_recip : unit FStar_BitVector.bv_t -> FStar_UInt8.t) =
  fun x -> to_uint8 (Prims.of_int (8)) x


let (parse_bv8_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_one;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some Prims.int_one);
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata =
      (FStar_Pervasives_Native.Some
         LowParse_Spec_Base.ParserKindMetadataTotal)
  }


let (synth_byte_bv :
  Prims.nat ->
    (unit FStar_BitVector.bv_t * unit FStar_BitVector.bv_t) ->
      unit FStar_BitVector.bv_t)
  =
  fun n ->
    fun x ->
      FStar_Seq_Base.append (FStar_Pervasives_Native.fst x)
        (FStar_Pervasives_Native.snd x)
let (synth_byte_bv_recip :
  Prims.nat ->
    unit FStar_BitVector.bv_t ->
      (unit FStar_BitVector.bv_t * unit FStar_BitVector.bv_t))
  =
  fun n ->
    fun x ->
      ((FStar_Seq_Base.slice x Prims.int_zero (Prims.of_int (8))),
        (FStar_Seq_Base.slice x (Prims.of_int (8)) (FStar_Seq_Base.length x)))


let rec (parse_byte_bv_kind' : Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun n ->
    if n = Prims.int_zero
    then
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
    else
      {
        LowParse_Spec_Base.parser_kind_low =
          ((match parse_bv8_kind with
            | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
                LowParse_Spec_Base.parser_kind_metadata =
                  parser_kind_metadata;_}
                -> parser_kind_low)
             +
             ((match parse_byte_bv_kind' (n - Prims.int_one) with
               | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                   LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                   LowParse_Spec_Base.parser_kind_subkind =
                     parser_kind_subkind;
                   LowParse_Spec_Base.parser_kind_metadata =
                     parser_kind_metadata;_}
                   -> parser_kind_low)));
        LowParse_Spec_Base.parser_kind_high =
          (if
             (if
                match match parse_bv8_kind with
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
                match match parse_byte_bv_kind' (n - Prims.int_one) with
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
             FStar_Pervasives_Native.Some
               ((match match parse_bv8_kind with
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
                  ((match match parse_byte_bv_kind' (n - Prims.int_one) with
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
                    | FStar_Pervasives_Native.Some y -> y)))
           else FStar_Pervasives_Native.None);
        LowParse_Spec_Base.parser_kind_subkind =
          (if
             (match parse_byte_bv_kind' (n - Prims.int_one) with
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
                  (match parse_bv8_kind with
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
                  (match parse_byte_bv_kind' (n - Prims.int_one) with
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
                    (match parse_byte_bv_kind' (n - Prims.int_one) with
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
                    (match parse_byte_bv_kind' (n - Prims.int_one) with
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
                 (match parse_bv8_kind with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_subkind)
               else FStar_Pervasives_Native.None);
        LowParse_Spec_Base.parser_kind_metadata =
          ((match ((match parse_bv8_kind with
                    | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                        LowParse_Spec_Base.parser_kind_high =
                          parser_kind_high;
                        LowParse_Spec_Base.parser_kind_subkind =
                          parser_kind_subkind;
                        LowParse_Spec_Base.parser_kind_metadata =
                          parser_kind_metadata;_}
                        -> parser_kind_metadata),
                    (match parse_byte_bv_kind' (n - Prims.int_one) with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_metadata))
            with
            | (FStar_Pervasives_Native.Some
               (LowParse_Spec_Base.ParserKindMetadataFail), uu___1) ->
                (match parse_bv8_kind with
                 | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                     LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                     LowParse_Spec_Base.parser_kind_subkind =
                       parser_kind_subkind;
                     LowParse_Spec_Base.parser_kind_metadata =
                       parser_kind_metadata;_}
                     -> parser_kind_metadata)
            | (uu___1, FStar_Pervasives_Native.Some
               (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                (match parse_byte_bv_kind' (n - Prims.int_one) with
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
                (match parse_bv8_kind with
                 | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                     LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                     LowParse_Spec_Base.parser_kind_subkind =
                       parser_kind_subkind;
                     LowParse_Spec_Base.parser_kind_metadata =
                       parser_kind_metadata;_}
                     -> parser_kind_metadata)
            | uu___1 -> FStar_Pervasives_Native.None))
      }
let (parse_byte_bv_kind : Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun n ->
    {
      LowParse_Spec_Base.parser_kind_low = n;
      LowParse_Spec_Base.parser_kind_high = (FStar_Pervasives_Native.Some n);
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata =
        (FStar_Pervasives_Native.Some
           LowParse_Spec_Base.ParserKindMetadataTotal)
    }



let (extra_bytes_prop : Prims.nat -> FStar_UInt8.t -> Prims.bool) =
  fun n ->
    fun x -> (FStar_UInt8.v x) < (Prims.pow2 (n mod (Prims.of_int (8))))
let (synth_extra_bv8 :
  Prims.nat ->
    (FStar_UInt8.t, unit) LowParse_Spec_Combinators.parse_filter_refine ->
      unit FStar_BitVector.bv_t)
  = fun n -> fun x -> of_uint8 (n mod (Prims.of_int (8))) x
let (synth_extra_bv8_recip :
  Prims.nat ->
    unit FStar_BitVector.bv_t ->
      (FStar_UInt8.t, unit) LowParse_Spec_Combinators.parse_filter_refine)
  = fun n -> fun x -> to_uint8 (n mod (Prims.of_int (8))) x


let (parse_extra_bv8_kind : Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun n ->
    {
      LowParse_Spec_Base.parser_kind_low = Prims.int_one;
      LowParse_Spec_Base.parser_kind_high =
        (FStar_Pervasives_Native.Some Prims.int_one);
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }


let (synth_bv :
  Prims.nat ->
    (unit FStar_BitVector.bv_t * unit FStar_BitVector.bv_t) ->
      unit FStar_BitVector.bv_t)
  =
  fun n ->
    fun x ->
      FStar_Seq_Base.append (FStar_Pervasives_Native.fst x)
        (FStar_Pervasives_Native.snd x)
let (synth_bv_recip :
  Prims.nat ->
    unit FStar_BitVector.bv_t ->
      (unit FStar_BitVector.bv_t * unit FStar_BitVector.bv_t))
  =
  fun n ->
    fun x ->
      ((FStar_Seq_Base.slice x Prims.int_zero (n mod (Prims.of_int (8)))),
        (FStar_Seq_Base.slice x (n mod (Prims.of_int (8)))
           (FStar_Seq_Base.length x)))


let (parse_bv_kind : Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun n ->
    if (n mod (Prims.of_int (8))) = Prims.int_zero
    then
      {
        LowParse_Spec_Base.parser_kind_low = (n / (Prims.of_int (8)));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some (n / (Prims.of_int (8))));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          (FStar_Pervasives_Native.Some
             LowParse_Spec_Base.ParserKindMetadataTotal)
      }
    else
      {
        LowParse_Spec_Base.parser_kind_low =
          (Prims.int_one + (n / (Prims.of_int (8))));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             (Prims.int_one + (n / (Prims.of_int (8)))));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }


type ('min, 'max) bounded_bv_t =
  (FStar_UInt32.t, unit FStar_BitVector.bv_t) Prims.dtuple2
let (parse_bounded_bv_payload_kind :
  Prims.nat -> Prims.nat -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          (if (min mod (Prims.of_int (8))) = Prims.int_zero
           then min / (Prims.of_int (8))
           else Prims.int_one + (min / (Prims.of_int (8))));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             (if (max mod (Prims.of_int (8))) = Prims.int_zero
              then max / (Prims.of_int (8))
              else Prims.int_one + (max / (Prims.of_int (8)))));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }

let (parse_bounded_bv_kind :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind)
  =
  fun min ->
    fun max ->
      fun hk ->
        {
          LowParse_Spec_Base.parser_kind_low =
            ((match hk with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low)
               +
               (match parse_bounded_bv_payload_kind min max with
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
                  match match hk with
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
                  match match parse_bounded_bv_payload_kind min max with
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
                 ((match match hk with
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
                    (match match parse_bounded_bv_payload_kind min max with
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
               (match parse_bounded_bv_payload_kind min max with
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
                    (match hk with
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
                  then
                    (match parse_bounded_bv_payload_kind min max with
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
                 FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
               else
                 if
                   (if
                      (match parse_bounded_bv_payload_kind min max with
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
                      (match parse_bounded_bv_payload_kind min max with
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
                   (match hk with
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
            (match ((match hk with
                     | {
                         LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                         LowParse_Spec_Base.parser_kind_high =
                           parser_kind_high;
                         LowParse_Spec_Base.parser_kind_subkind =
                           parser_kind_subkind;
                         LowParse_Spec_Base.parser_kind_metadata =
                           parser_kind_metadata;_}
                         -> parser_kind_metadata),
                     (match parse_bounded_bv_payload_kind min max with
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
                 (match hk with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_metadata)
             | (uu___, FStar_Pervasives_Native.Some
                (LowParse_Spec_Base.ParserKindMetadataFail)) ->
                 (match parse_bounded_bv_payload_kind min max with
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
                 (match hk with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_metadata)
             | uu___ -> FStar_Pervasives_Native.None)
        }

