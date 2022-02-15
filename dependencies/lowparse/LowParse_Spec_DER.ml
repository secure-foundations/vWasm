open Prims
let (der_length_max : Prims.nat) =
  (Prims.parse_int "2743062034396844341627968125593604635037196317966166035056000994228098690879836473582587849768181396806642362668936055872479091931372323951612051859122835149807249350355003132267795098895967012320756270631179897595796976964454084495146379250195728106130226298287754794921070036903071843030324651025760255")

type der_length_t = Prims.nat
let rec (log256 : Prims.nat -> Prims.nat) =
  fun x ->
    if x < (Prims.of_int (256))
    then Prims.int_one
    else (let n = log256 (x / (Prims.of_int (256))) in n + Prims.int_one)


let (der_length_payload_size_of_tag : FStar_UInt8.t -> Prims.nat) =
  fun x ->
    if
      ((FStar_UInt8.v x) <= (Prims.of_int (128))) ||
        ((FStar_UInt8.v x) = (Prims.of_int (255)))
    then Prims.int_zero
    else (FStar_UInt8.v x) - (Prims.of_int (128))
let (parse_der_length_payload_kind :
  FStar_UInt8.t -> LowParse_Spec_Base.parser_kind) =
  fun x ->
    let len =
      if
        ((FStar_UInt8.v x) <= (Prims.of_int (128))) ||
          ((FStar_UInt8.v x) = (Prims.of_int (255)))
      then Prims.int_zero
      else (FStar_UInt8.v x) - (Prims.of_int (128)) in
    {
      LowParse_Spec_Base.parser_kind_low = len;
      LowParse_Spec_Base.parser_kind_high =
        (FStar_Pervasives_Native.Some len);
      LowParse_Spec_Base.parser_kind_subkind =
        (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }
let (tag_of_der_length : der_length_t -> FStar_UInt8.t) =
  fun x ->
    if x < (Prims.of_int (128))
    then FStar_UInt8.uint_to_t x
    else
      (let len_len = log256 x in
       FStar_UInt8.add (FStar_UInt8.uint_to_t (Prims.of_int (128)))
         (FStar_UInt8.uint_to_t len_len))
let (der_length_payload_size : der_length_t -> Prims.nat) =
  fun x ->
    if
      ((FStar_UInt8.v (tag_of_der_length x)) <= (Prims.of_int (128))) ||
        ((FStar_UInt8.v (tag_of_der_length x)) = (Prims.of_int (255)))
    then Prims.int_zero
    else (FStar_UInt8.v (tag_of_der_length x)) - (Prims.of_int (128))

type 'len lint = Prims.nat




let (synth_der_length_greater :
  FStar_UInt8.t -> Prims.nat -> unit lint -> der_length_t) =
  fun x -> fun len -> fun y -> y


let (parse_der_length_payload_kind_weak : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (126)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }
let (parse_der_length_weak_kind : LowParse_Spec_Base.parser_kind) =
  {
    LowParse_Spec_Base.parser_kind_low = Prims.int_one;
    LowParse_Spec_Base.parser_kind_high =
      (FStar_Pervasives_Native.Some (Prims.of_int (127)));
    LowParse_Spec_Base.parser_kind_subkind =
      (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
    LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
  }

let (parse_bounded_der_length_payload_kind :
  der_length_t -> der_length_t -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low = (der_length_payload_size min);
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some (der_length_payload_size max));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }
type ('min, 'max) bounded_int = Prims.int

let (tag_of_bounded_der_length :
  der_length_t -> der_length_t -> (unit, unit) bounded_int -> FStar_UInt8.t)
  = fun min -> fun max -> fun x -> tag_of_der_length x

let (parse_bounded_der_length_kind :
  der_length_t -> der_length_t -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          (Prims.int_one +
             (match parse_bounded_der_length_payload_kind min max with
              | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                  LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                  LowParse_Spec_Base.parser_kind_subkind =
                    parser_kind_subkind;
                  LowParse_Spec_Base.parser_kind_metadata =
                    parser_kind_metadata;_}
                  -> parser_kind_low));
        LowParse_Spec_Base.parser_kind_high =
          (if
             match match parse_bounded_der_length_payload_kind min max with
                   | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                       LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                       LowParse_Spec_Base.parser_kind_subkind =
                         parser_kind_subkind;
                       LowParse_Spec_Base.parser_kind_metadata =
                         parser_kind_metadata;_}
                       -> parser_kind_high
             with
             | FStar_Pervasives_Native.Some uu___ -> true
             | uu___ -> false
           then
             FStar_Pervasives_Native.Some
               (Prims.int_one +
                  (match match parse_bounded_der_length_payload_kind min max
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
             (match parse_bounded_der_length_payload_kind min max with
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
               (match parse_bounded_der_length_payload_kind min max with
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
               FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong
             else
               if
                 (if
                    (match parse_bounded_der_length_payload_kind min max with
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
                    (match parse_bounded_der_length_payload_kind min max with
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
               else FStar_Pervasives_Native.None);
        LowParse_Spec_Base.parser_kind_metadata =
          (match (FStar_Pervasives_Native.None,
                   (match parse_bounded_der_length_payload_kind min max with
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
               FStar_Pervasives_Native.None
           | (uu___, FStar_Pervasives_Native.Some
              (LowParse_Spec_Base.ParserKindMetadataFail)) ->
               (match parse_bounded_der_length_payload_kind min max with
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
               FStar_Pervasives_Native.None
           | uu___ -> FStar_Pervasives_Native.None)
      }













let (synth_der_length_greater_recip :
  FStar_UInt8.t -> Prims.nat -> der_length_t -> unit lint) =
  fun x -> fun len -> fun y -> y

















let (tag_of_der_length32' : der_length_t -> FStar_UInt8.t) =
  fun x ->
    if x < (Prims.of_int (128))
    then FStar_UInt8.uint_to_t x
    else
      FStar_UInt8.add (FStar_UInt8.uint_to_t (Prims.of_int (128)))
        (FStar_UInt8.uint_to_t
           (if x < (Prims.of_int (256))
            then Prims.int_one
            else
              if x < (Prims.parse_int "65536")
              then (Prims.of_int (2))
              else
                if x < (Prims.parse_int "16777216")
                then (Prims.of_int (3))
                else (Prims.of_int (4))))
let (parse_bounded_der_length_payload32_kind :
  der_length_t -> der_length_t -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          (if
             ((FStar_UInt8.v
                 (if min < (Prims.of_int (128))
                  then FStar_UInt8.uint_to_t min
                  else
                    FStar_UInt8.add
                      (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                      (FStar_UInt8.uint_to_t
                         (if min < (Prims.of_int (256))
                          then Prims.int_one
                          else
                            if min < (Prims.parse_int "65536")
                            then (Prims.of_int (2))
                            else
                              if min < (Prims.parse_int "16777216")
                              then (Prims.of_int (3))
                              else (Prims.of_int (4))))))
                <= (Prims.of_int (128)))
               ||
               ((FStar_UInt8.v
                   (if min < (Prims.of_int (128))
                    then FStar_UInt8.uint_to_t min
                    else
                      FStar_UInt8.add
                        (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                        (FStar_UInt8.uint_to_t
                           (if min < (Prims.of_int (256))
                            then Prims.int_one
                            else
                              if min < (Prims.parse_int "65536")
                              then (Prims.of_int (2))
                              else
                                if min < (Prims.parse_int "16777216")
                                then (Prims.of_int (3))
                                else (Prims.of_int (4))))))
                  = (Prims.of_int (255)))
           then Prims.int_zero
           else
             (FStar_UInt8.v
                (if min < (Prims.of_int (128))
                 then FStar_UInt8.uint_to_t min
                 else
                   FStar_UInt8.add
                     (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                     (FStar_UInt8.uint_to_t
                        (if min < (Prims.of_int (256))
                         then Prims.int_one
                         else
                           if min < (Prims.parse_int "65536")
                           then (Prims.of_int (2))
                           else
                             if min < (Prims.parse_int "16777216")
                             then (Prims.of_int (3))
                             else (Prims.of_int (4))))))
               - (Prims.of_int (128)));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             (if
                ((FStar_UInt8.v
                    (if max < (Prims.of_int (128))
                     then FStar_UInt8.uint_to_t max
                     else
                       FStar_UInt8.add
                         (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                         (FStar_UInt8.uint_to_t
                            (if max < (Prims.of_int (256))
                             then Prims.int_one
                             else
                               if max < (Prims.parse_int "65536")
                               then (Prims.of_int (2))
                               else
                                 if max < (Prims.parse_int "16777216")
                                 then (Prims.of_int (3))
                                 else (Prims.of_int (4))))))
                   <= (Prims.of_int (128)))
                  ||
                  ((FStar_UInt8.v
                      (if max < (Prims.of_int (128))
                       then FStar_UInt8.uint_to_t max
                       else
                         FStar_UInt8.add
                           (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                           (FStar_UInt8.uint_to_t
                              (if max < (Prims.of_int (256))
                               then Prims.int_one
                               else
                                 if max < (Prims.parse_int "65536")
                                 then (Prims.of_int (2))
                                 else
                                   if max < (Prims.parse_int "16777216")
                                   then (Prims.of_int (3))
                                   else (Prims.of_int (4))))))
                     = (Prims.of_int (255)))
              then Prims.int_zero
              else
                (FStar_UInt8.v
                   (if max < (Prims.of_int (128))
                    then FStar_UInt8.uint_to_t max
                    else
                      FStar_UInt8.add
                        (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                        (FStar_UInt8.uint_to_t
                           (if max < (Prims.of_int (256))
                            then Prims.int_one
                            else
                              if max < (Prims.parse_int "65536")
                              then (Prims.of_int (2))
                              else
                                if max < (Prims.parse_int "16777216")
                                then (Prims.of_int (3))
                                else (Prims.of_int (4))))))
                  - (Prims.of_int (128))));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }
let (parse_bounded_der_length32_kind :
  der_length_t -> der_length_t -> LowParse_Spec_Base.parser_kind) =
  fun min ->
    fun max ->
      {
        LowParse_Spec_Base.parser_kind_low =
          (Prims.int_one +
             (if
                ((FStar_UInt8.v
                    (if min < (Prims.of_int (128))
                     then FStar_UInt8.uint_to_t min
                     else
                       FStar_UInt8.add
                         (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                         (FStar_UInt8.uint_to_t
                            (if min < (Prims.of_int (256))
                             then Prims.int_one
                             else
                               if min < (Prims.parse_int "65536")
                               then (Prims.of_int (2))
                               else
                                 if min < (Prims.parse_int "16777216")
                                 then (Prims.of_int (3))
                                 else (Prims.of_int (4))))))
                   <= (Prims.of_int (128)))
                  ||
                  ((FStar_UInt8.v
                      (if min < (Prims.of_int (128))
                       then FStar_UInt8.uint_to_t min
                       else
                         FStar_UInt8.add
                           (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                           (FStar_UInt8.uint_to_t
                              (if min < (Prims.of_int (256))
                               then Prims.int_one
                               else
                                 if min < (Prims.parse_int "65536")
                                 then (Prims.of_int (2))
                                 else
                                   if min < (Prims.parse_int "16777216")
                                   then (Prims.of_int (3))
                                   else (Prims.of_int (4))))))
                     = (Prims.of_int (255)))
              then Prims.int_zero
              else
                (FStar_UInt8.v
                   (if min < (Prims.of_int (128))
                    then FStar_UInt8.uint_to_t min
                    else
                      FStar_UInt8.add
                        (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                        (FStar_UInt8.uint_to_t
                           (if min < (Prims.of_int (256))
                            then Prims.int_one
                            else
                              if min < (Prims.parse_int "65536")
                              then (Prims.of_int (2))
                              else
                                if min < (Prims.parse_int "16777216")
                                then (Prims.of_int (3))
                                else (Prims.of_int (4))))))
                  - (Prims.of_int (128))));
        LowParse_Spec_Base.parser_kind_high =
          (FStar_Pervasives_Native.Some
             (Prims.int_one +
                (if
                   ((FStar_UInt8.v
                       (if max < (Prims.of_int (128))
                        then FStar_UInt8.uint_to_t max
                        else
                          FStar_UInt8.add
                            (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                            (FStar_UInt8.uint_to_t
                               (if max < (Prims.of_int (256))
                                then Prims.int_one
                                else
                                  if max < (Prims.parse_int "65536")
                                  then (Prims.of_int (2))
                                  else
                                    if max < (Prims.parse_int "16777216")
                                    then (Prims.of_int (3))
                                    else (Prims.of_int (4))))))
                      <= (Prims.of_int (128)))
                     ||
                     ((FStar_UInt8.v
                         (if max < (Prims.of_int (128))
                          then FStar_UInt8.uint_to_t max
                          else
                            FStar_UInt8.add
                              (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                              (FStar_UInt8.uint_to_t
                                 (if max < (Prims.of_int (256))
                                  then Prims.int_one
                                  else
                                    if max < (Prims.parse_int "65536")
                                    then (Prims.of_int (2))
                                    else
                                      if max < (Prims.parse_int "16777216")
                                      then (Prims.of_int (3))
                                      else (Prims.of_int (4))))))
                        = (Prims.of_int (255)))
                 then Prims.int_zero
                 else
                   (FStar_UInt8.v
                      (if max < (Prims.of_int (128))
                       then FStar_UInt8.uint_to_t max
                       else
                         FStar_UInt8.add
                           (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                           (FStar_UInt8.uint_to_t
                              (if max < (Prims.of_int (256))
                               then Prims.int_one
                               else
                                 if max < (Prims.parse_int "65536")
                                 then (Prims.of_int (2))
                                 else
                                   if max < (Prims.parse_int "16777216")
                                   then (Prims.of_int (3))
                                   else (Prims.of_int (4))))))
                     - (Prims.of_int (128)))));
        LowParse_Spec_Base.parser_kind_subkind =
          (FStar_Pervasives_Native.Some LowParse_Spec_Base.ParserStrong);
        LowParse_Spec_Base.parser_kind_metadata =
          FStar_Pervasives_Native.None
      }



let (der_length_payload_size_of_tag8 : FStar_UInt8.t -> FStar_UInt8.t) =
  fun x ->
    if
      (FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (129)))) ||
        (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
    then FStar_UInt8.uint_to_t Prims.int_zero
    else FStar_UInt8.sub x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
let (log256_32 : FStar_UInt32.t -> FStar_UInt8.t) =
  fun n ->
    if FStar_UInt32.lt n (FStar_UInt32.uint_to_t (Prims.of_int (256)))
    then FStar_UInt8.uint_to_t Prims.int_one
    else
      if FStar_UInt32.lt n (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
      then FStar_UInt8.uint_to_t (Prims.of_int (2))
      else
        if
          FStar_UInt32.lt n
            (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
        then FStar_UInt8.uint_to_t (Prims.of_int (3))
        else FStar_UInt8.uint_to_t (Prims.of_int (4))
let (tag_of_der_length32_impl : FStar_UInt32.t -> FStar_UInt8.t) =
  fun x ->
    if FStar_UInt32.lt x (FStar_UInt32.uint_to_t (Prims.of_int (128)))
    then FStar_Int_Cast.uint32_to_uint8 x
    else
      (let len_len =
         if FStar_UInt32.lt x (FStar_UInt32.uint_to_t (Prims.of_int (256)))
         then FStar_UInt8.uint_to_t Prims.int_one
         else
           if
             FStar_UInt32.lt x
               (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
           then FStar_UInt8.uint_to_t (Prims.of_int (2))
           else
             if
               FStar_UInt32.lt x
                 (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
             then FStar_UInt8.uint_to_t (Prims.of_int (3))
             else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
       FStar_UInt8.add (FStar_UInt8.uint_to_t (Prims.of_int (128))) len_len)



