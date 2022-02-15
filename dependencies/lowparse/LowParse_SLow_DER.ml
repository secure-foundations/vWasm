open Prims
let (parse32_der_length_payload32 :
  FStar_UInt8.t ->
    LowParse_SLow_Base.bytes32 ->
      (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun x ->
    fun input ->
      if FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
      then
        FStar_Pervasives_Native.Some
          ((FStar_Int_Cast.uint8_to_uint32 x),
            (FStar_UInt32.uint_to_t Prims.int_zero))
      else
        if
          (x = (FStar_UInt8.uint_to_t (Prims.of_int (128)))) ||
            (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
        then FStar_Pervasives_Native.None
        else
          if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
          then
            (match LowParse_SLow_Int.parse32_u8 input with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (z, consumed) ->
                 if
                   FStar_UInt8.lt z
                     (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                 then FStar_Pervasives_Native.None
                 else
                   FStar_Pervasives_Native.Some
                     ((FStar_Int_Cast.uint8_to_uint32 z), consumed))
          else
            (let len =
               FStar_UInt8.sub x (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
             if len = (FStar_UInt8.uint_to_t (Prims.of_int (2)))
             then
               match LowParse_SLow_BoundedInt.parse32_bounded_integer_2 input
               with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (y, consumed) ->
                   (if
                      FStar_UInt32.lt y
                        (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                    then FStar_Pervasives_Native.None
                    else FStar_Pervasives_Native.Some (y, consumed))
             else
               if len = (FStar_UInt8.uint_to_t (Prims.of_int (3)))
               then
                 (match LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                          input
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (y, consumed) ->
                      if
                        FStar_UInt32.lt y
                          (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                      then FStar_Pervasives_Native.None
                      else FStar_Pervasives_Native.Some (y, consumed))
               else
                 (match LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                          input
                  with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (y, consumed) ->
                      if
                        FStar_UInt32.lt y
                          (FStar_UInt32.uint_to_t
                             (Prims.parse_int "16777216"))
                      then FStar_Pervasives_Native.None
                      else FStar_Pervasives_Native.Some (y, consumed)))
let (parse32_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    FStar_UInt32.t ->
      LowParse_Spec_DER.der_length_t ->
        FStar_UInt32.t ->
          LowParse_SLow_Base.bytes32 ->
            (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun input ->
            match LowParse_SLow_Int.parse32_u8 input with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (x, consumed_x) ->
                let len =
                  if
                    (FStar_UInt8.lt x
                       (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                      || (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                  then FStar_UInt8.uint_to_t Prims.int_zero
                  else
                    FStar_UInt8.sub x
                      (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                let tg1 =
                  if
                    FStar_UInt32.lt min
                      (FStar_UInt32.uint_to_t (Prims.of_int (128)))
                  then FStar_Int_Cast.uint32_to_uint8 min
                  else
                    (let len_len =
                       if
                         FStar_UInt32.lt min
                           (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                       then FStar_UInt8.uint_to_t Prims.int_one
                       else
                         if
                           FStar_UInt32.lt min
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "65536"))
                         then FStar_UInt8.uint_to_t (Prims.of_int (2))
                         else
                           if
                             FStar_UInt32.lt min
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "16777216"))
                           then FStar_UInt8.uint_to_t (Prims.of_int (3))
                           else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
                     FStar_UInt8.add
                       (FStar_UInt8.uint_to_t (Prims.of_int (128))) len_len) in
                let l1 =
                  if
                    (FStar_UInt8.lt tg1
                       (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                      || (tg1 = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                  then FStar_UInt8.uint_to_t Prims.int_zero
                  else
                    FStar_UInt8.sub tg1
                      (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                let tg2 =
                  if
                    FStar_UInt32.lt max
                      (FStar_UInt32.uint_to_t (Prims.of_int (128)))
                  then FStar_Int_Cast.uint32_to_uint8 max
                  else
                    (let len_len =
                       if
                         FStar_UInt32.lt max
                           (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                       then FStar_UInt8.uint_to_t Prims.int_one
                       else
                         if
                           FStar_UInt32.lt max
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "65536"))
                         then FStar_UInt8.uint_to_t (Prims.of_int (2))
                         else
                           if
                             FStar_UInt32.lt max
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "16777216"))
                           then FStar_UInt8.uint_to_t (Prims.of_int (3))
                           else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
                     FStar_UInt8.add
                       (FStar_UInt8.uint_to_t (Prims.of_int (128))) len_len) in
                let l2 =
                  if
                    (FStar_UInt8.lt tg2
                       (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                      || (tg2 = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                  then FStar_UInt8.uint_to_t Prims.int_zero
                  else
                    FStar_UInt8.sub tg2
                      (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                if (FStar_UInt8.lt len l1) || (FStar_UInt8.lt l2 len)
                then FStar_Pervasives_Native.None
                else
                  (let input' =
                     FStar_Bytes.slice input consumed_x
                       (FStar_Bytes.len input) in
                   match if
                           FStar_UInt8.lt x
                             (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                         then
                           FStar_Pervasives_Native.Some
                             ((FStar_Int_Cast.uint8_to_uint32 x),
                               (FStar_UInt32.uint_to_t Prims.int_zero))
                         else
                           if
                             (x =
                                (FStar_UInt8.uint_to_t (Prims.of_int (128))))
                               ||
                               (x =
                                  (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                           then FStar_Pervasives_Native.None
                           else
                             if
                               x =
                                 (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                             then
                               (match LowParse_SLow_Int.parse32_u8 input'
                                with
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.Some (z, consumed)
                                    ->
                                    if
                                      FStar_UInt8.lt z
                                        (FStar_UInt8.uint_to_t
                                           (Prims.of_int (128)))
                                    then FStar_Pervasives_Native.None
                                    else
                                      FStar_Pervasives_Native.Some
                                        ((FStar_Int_Cast.uint8_to_uint32 z),
                                          consumed))
                             else
                               (let len1 =
                                  FStar_UInt8.sub x
                                    (FStar_UInt8.uint_to_t
                                       (Prims.of_int (128))) in
                                if
                                  len1 =
                                    (FStar_UInt8.uint_to_t (Prims.of_int (2)))
                                then
                                  match LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                          input'
                                  with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some
                                      (y, consumed) ->
                                      (if
                                         FStar_UInt32.lt y
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))
                                       then FStar_Pervasives_Native.None
                                       else
                                         FStar_Pervasives_Native.Some
                                           (y, consumed))
                                else
                                  if
                                    len1 =
                                      (FStar_UInt8.uint_to_t
                                         (Prims.of_int (3)))
                                  then
                                    (match LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                             input'
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (y, consumed) ->
                                         if
                                           FStar_UInt32.lt y
                                             (FStar_UInt32.uint_to_t
                                                (Prims.parse_int "65536"))
                                         then FStar_Pervasives_Native.None
                                         else
                                           FStar_Pervasives_Native.Some
                                             (y, consumed))
                                  else
                                    (match LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                             input'
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some
                                         (y, consumed) ->
                                         if
                                           FStar_UInt32.lt y
                                             (FStar_UInt32.uint_to_t
                                                (Prims.parse_int "16777216"))
                                         then FStar_Pervasives_Native.None
                                         else
                                           FStar_Pervasives_Native.Some
                                             (y, consumed)))
                   with
                   | FStar_Pervasives_Native.Some (y, consumed_y) ->
                       if (FStar_UInt32.lt y min) || (FStar_UInt32.lt max y)
                       then FStar_Pervasives_Native.None
                       else
                         FStar_Pervasives_Native.Some
                           (y, (FStar_UInt32.add consumed_x consumed_y))
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None)
let (serialize32_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      FStar_UInt32.t -> LowParse_SLow_Base.bytes32)
  =
  fun vmin ->
    fun vmax ->
      fun y' ->
        let x =
          if FStar_UInt32.lt y' (FStar_UInt32.uint_to_t (Prims.of_int (128)))
          then FStar_Int_Cast.uint32_to_uint8 y'
          else
            (let len_len =
               if
                 FStar_UInt32.lt y'
                   (FStar_UInt32.uint_to_t (Prims.of_int (256)))
               then FStar_UInt8.uint_to_t Prims.int_one
               else
                 if
                   FStar_UInt32.lt y'
                     (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                 then FStar_UInt8.uint_to_t (Prims.of_int (2))
                 else
                   if
                     FStar_UInt32.lt y'
                       (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
                   then FStar_UInt8.uint_to_t (Prims.of_int (3))
                   else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
             FStar_UInt8.add (FStar_UInt8.uint_to_t (Prims.of_int (128)))
               len_len) in
        let sx = FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one) x in
        if FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
        then sx
        else
          if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
          then
            FStar_Bytes.append sx
              (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                 (FStar_Int_Cast.uint32_to_uint8 y'))
          else
            if x = (FStar_UInt8.uint_to_t (Prims.of_int (130)))
            then
              FStar_Bytes.append sx
                (LowParse_SLow_BoundedInt.serialize32_bounded_integer_2 y')
            else
              if x = (FStar_UInt8.uint_to_t (Prims.of_int (131)))
              then
                FStar_Bytes.append sx
                  (LowParse_SLow_BoundedInt.serialize32_bounded_integer_3 y')
              else
                FStar_Bytes.append sx
                  (LowParse_SLow_BoundedInt.serialize32_bounded_integer_4 y')
let (size32_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t -> FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun y' ->
        if FStar_UInt32.lt y' (FStar_UInt32.uint_to_t (Prims.of_int (128)))
        then FStar_UInt32.uint_to_t Prims.int_one
        else
          if FStar_UInt32.lt y' (FStar_UInt32.uint_to_t (Prims.of_int (256)))
          then FStar_UInt32.uint_to_t (Prims.of_int (2))
          else
            if
              FStar_UInt32.lt y'
                (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
            then FStar_UInt32.uint_to_t (Prims.of_int (3))
            else
              if
                FStar_UInt32.lt y'
                  (FStar_UInt32.uint_to_t (Prims.parse_int "16777216"))
              then FStar_UInt32.uint_to_t (Prims.of_int (4))
              else FStar_UInt32.uint_to_t (Prims.of_int (5))