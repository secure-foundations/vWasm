open Prims
let (parse32_bcvli :
  LowParse_SLow_Base.bytes32 ->
    (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match LowParse_SLow_BoundedInt.parse32_bounded_integer_le_1 input with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (x32, consumed_x) ->
        if FStar_UInt32.lt x32 (FStar_UInt32.uint_to_t (Prims.of_int (253)))
        then FStar_Pervasives_Native.Some (x32, consumed_x)
        else
          (let input' =
             FStar_Bytes.slice input consumed_x (FStar_Bytes.len input) in
           if x32 = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
           then
             match LowParse_SLow_BoundedInt.parse32_bounded_integer_le_2
                     input'
             with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (y, consumed_y) ->
                 (if
                    FStar_UInt32.lt y
                      (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                  then FStar_Pervasives_Native.None
                  else
                    FStar_Pervasives_Native.Some
                      (y, (FStar_UInt32.add consumed_x consumed_y)))
           else
             if x32 = (FStar_UInt32.uint_to_t (Prims.of_int (254)))
             then
               (match LowParse_SLow_BoundedInt.parse32_bounded_integer_le_4
                        input'
                with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (y, consumed_y) ->
                    if
                      FStar_UInt32.lt y
                        (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                    then FStar_Pervasives_Native.None
                    else
                      FStar_Pervasives_Native.Some
                        (y, (FStar_UInt32.add consumed_x consumed_y)))
             else FStar_Pervasives_Native.None)
let (serialize32_bcvli : FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let c1 =
      if FStar_UInt32.lt x (FStar_UInt32.uint_to_t (Prims.of_int (253)))
      then x
      else
        if
          FStar_UInt32.lt x
            (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
        then FStar_UInt32.uint_to_t (Prims.of_int (253))
        else FStar_UInt32.uint_to_t (Prims.of_int (254)) in
    let s1 = LowParse_SLow_BoundedInt.serialize32_bounded_integer_le_1 c1 in
    if FStar_UInt32.lt c1 (FStar_UInt32.uint_to_t (Prims.of_int (253)))
    then s1
    else
      if c1 = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
      then
        FStar_Bytes.append s1
          (LowParse_SLow_BoundedInt.serialize32_bounded_integer_le_2 x)
      else
        FStar_Bytes.append s1
          (LowParse_SLow_BoundedInt.serialize32_bounded_integer_le_4 x)
let (size32_bcvli : FStar_UInt32.t -> FStar_UInt32.t) =
  fun x ->
    if FStar_UInt32.lt x (FStar_UInt32.uint_to_t (Prims.of_int (253)))
    then FStar_UInt32.uint_to_t Prims.int_one
    else
      if FStar_UInt32.lt x (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
      then FStar_UInt32.uint_to_t (Prims.of_int (3))
      else FStar_UInt32.uint_to_t (Prims.of_int (5))
let (parse32_bounded_bcvli :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          LowParse_SLow_Base.bytes32 ->
            (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun input ->
            match LowParse_SLow_BoundedInt.parse32_bounded_integer_le_1 input
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (x32, consumed_x) ->
                if
                  ((FStar_UInt32.lt x32
                      (FStar_UInt32.uint_to_t (Prims.of_int (253))))
                     && (FStar_UInt32.lte min32 x32))
                    && (FStar_UInt32.lte x32 max32)
                then FStar_Pervasives_Native.Some (x32, consumed_x)
                else
                  if
                    FStar_UInt32.lt max32
                      (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                  then FStar_Pervasives_Native.None
                  else
                    if x32 = (FStar_UInt32.uint_to_t (Prims.of_int (253)))
                    then
                      (if
                         FStar_UInt32.lte
                           (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                           min32
                       then FStar_Pervasives_Native.None
                       else
                         (let input' =
                            FStar_Bytes.slice input consumed_x
                              (FStar_Bytes.len input) in
                          match LowParse_SLow_BoundedInt.parse32_bounded_integer_le_2
                                  input'
                          with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some (y, consumed_y) ->
                              if
                                ((FStar_UInt32.lt y
                                    (FStar_UInt32.uint_to_t
                                       (Prims.of_int (253))))
                                   || (FStar_UInt32.lt y min32))
                                  || (FStar_UInt32.lt max32 y)
                              then FStar_Pervasives_Native.None
                              else
                                FStar_Pervasives_Native.Some
                                  (y,
                                    (FStar_UInt32.add consumed_x consumed_y))))
                    else
                      if
                        FStar_UInt32.lt max32
                          (FStar_UInt32.uint_to_t (Prims.parse_int "65536"))
                      then FStar_Pervasives_Native.None
                      else
                        if
                          x32 = (FStar_UInt32.uint_to_t (Prims.of_int (254)))
                        then
                          (let input' =
                             FStar_Bytes.slice input consumed_x
                               (FStar_Bytes.len input) in
                           match LowParse_SLow_BoundedInt.parse32_bounded_integer_le_4
                                   input'
                           with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (y, consumed_y) ->
                               if
                                 ((FStar_UInt32.lt y
                                     (FStar_UInt32.uint_to_t
                                        (Prims.parse_int "65536")))
                                    || (FStar_UInt32.lt y min32))
                                   || (FStar_UInt32.lt max32 y)
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_Pervasives_Native.Some
                                   (y,
                                     (FStar_UInt32.add consumed_x consumed_y)))
                        else FStar_Pervasives_Native.None
let (serialize32_bounded_bcvli :
  Prims.nat -> Prims.nat -> FStar_UInt32.t -> LowParse_SLow_Base.bytes32) =
  fun min -> fun max -> fun x -> serialize32_bcvli x
let (size32_bounded_bcvli :
  Prims.nat -> Prims.nat -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun min -> fun max -> fun x -> size32_bcvli x