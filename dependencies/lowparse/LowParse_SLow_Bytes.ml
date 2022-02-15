open Prims
let (parse32_flbytes_gen :
  Prims.nat -> unit FStar_Bytes.lbytes -> unit FStar_Bytes.lbytes) =
  fun sz -> fun x -> x
let (parse32_flbytes :
  Prims.nat ->
    FStar_UInt32.t ->
      LowParse_SLow_Base.bytes32 ->
        (unit FStar_Bytes.lbytes * FStar_UInt32.t)
          FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun sz' ->
      fun input ->
        if FStar_UInt32.lt (FStar_Bytes.len input) sz'
        then FStar_Pervasives_Native.None
        else
          (let s' =
             FStar_Bytes.slice input (FStar_UInt32.uint_to_t Prims.int_zero)
               sz' in
           FStar_Pervasives_Native.Some (s', sz'))
let (serialize32_flbytes :
  Prims.nat -> unit FStar_Bytes.lbytes -> LowParse_SLow_Base.bytes32) =
  fun sz -> fun input -> input
let (parse32_all_bytes :
  LowParse_SLow_Base.bytes32 ->
    (FStar_Bytes.bytes * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    let res = FStar_Pervasives_Native.Some (input, (FStar_Bytes.len input)) in
    res
let (serialize32_all_bytes : FStar_Bytes.bytes -> LowParse_SLow_Base.bytes32)
  = fun input -> input
let (parse32_bounded_vlbytes' :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          Prims.nat ->
            LowParse_SLow_Base.bytes32 ->
              ((unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t *
                FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun l ->
            fun input ->
              match let res =
                      match match match match l with
                                        | uu___ when uu___ = Prims.int_one ->
                                            LowParse_SLow_BoundedInt.parse32_bounded_integer_1
                                              input
                                        | uu___ when
                                            uu___ = (Prims.of_int (2)) ->
                                            LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                              input
                                        | uu___ when
                                            uu___ = (Prims.of_int (3)) ->
                                            LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                              input
                                        | uu___ when
                                            uu___ = (Prims.of_int (4)) ->
                                            LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                              input
                                  with
                                  | FStar_Pervasives_Native.Some
                                      (v, consumed) ->
                                      if
                                        Prims.op_Negation
                                          ((FStar_UInt32.lt v min32) ||
                                             (FStar_UInt32.lt max32 v))
                                      then
                                        FStar_Pervasives_Native.Some
                                          (v, consumed)
                                      else FStar_Pervasives_Native.None
                                  | uu___ -> FStar_Pervasives_Native.None
                            with
                            | FStar_Pervasives_Native.Some (v, l1) ->
                                let input' =
                                  FStar_Bytes.slice input l1
                                    (FStar_Bytes.len input) in
                                (match if
                                         FStar_UInt32.lt
                                           (FStar_Bytes.len input') v
                                       then FStar_Pervasives_Native.None
                                       else
                                         (match let res1 =
                                                  FStar_Pervasives_Native.Some
                                                    ((FStar_Bytes.slice
                                                        input'
                                                        (FStar_UInt32.uint_to_t
                                                           Prims.int_zero) v),
                                                      (FStar_Bytes.len
                                                         (FStar_Bytes.slice
                                                            input'
                                                            (FStar_UInt32.uint_to_t
                                                               Prims.int_zero)
                                                            v))) in
                                                res1
                                          with
                                          | FStar_Pervasives_Native.Some
                                              (v1, consumed) ->
                                              if consumed = v
                                              then
                                                FStar_Pervasives_Native.Some
                                                  (v1, consumed)
                                              else
                                                FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None)
                                 with
                                 | FStar_Pervasives_Native.Some (v', l') ->
                                     FStar_Pervasives_Native.Some
                                       (v', (FStar_UInt32.add l1 l'))
                                 | uu___ -> FStar_Pervasives_Native.None)
                            | uu___ -> FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (x, consumed) ->
                          FStar_Pervasives_Native.Some (x, consumed)
                      | uu___ -> FStar_Pervasives_Native.None in
                    match res with
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.None
                    | FStar_Pervasives_Native.Some (x, consumed) ->
                        let x1 = x in
                        FStar_Pervasives_Native.Some (x1, consumed)
              with
              | FStar_Pervasives_Native.Some (v1, consumed) ->
                  FStar_Pervasives_Native.Some (v1, consumed)
              | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_vlbytes :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          LowParse_SLow_Base.bytes32 ->
            ((unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t *
              FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun input ->
            match let res =
                    match match match match if max < (Prims.of_int (256))
                                            then Prims.int_one
                                            else
                                              if
                                                max <
                                                  (Prims.parse_int "65536")
                                              then (Prims.of_int (2))
                                              else
                                                if
                                                  max <
                                                    (Prims.parse_int "16777216")
                                                then (Prims.of_int (3))
                                                else (Prims.of_int (4))
                                      with
                                      | uu___ when uu___ = Prims.int_one ->
                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_1
                                            input
                                      | uu___ when uu___ = (Prims.of_int (2))
                                          ->
                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                            input
                                      | uu___ when uu___ = (Prims.of_int (3))
                                          ->
                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                            input
                                      | uu___ when uu___ = (Prims.of_int (4))
                                          ->
                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                            input
                                with
                                | FStar_Pervasives_Native.Some (v, consumed)
                                    ->
                                    if
                                      Prims.op_Negation
                                        ((FStar_UInt32.lt v min32) ||
                                           (FStar_UInt32.lt max32 v))
                                    then
                                      FStar_Pervasives_Native.Some
                                        (v, consumed)
                                    else FStar_Pervasives_Native.None
                                | uu___ -> FStar_Pervasives_Native.None
                          with
                          | FStar_Pervasives_Native.Some (v, l) ->
                              let input' =
                                FStar_Bytes.slice input l
                                  (FStar_Bytes.len input) in
                              (match if
                                       FStar_UInt32.lt
                                         (FStar_Bytes.len input') v
                                     then FStar_Pervasives_Native.None
                                     else
                                       (match let res1 =
                                                FStar_Pervasives_Native.Some
                                                  ((FStar_Bytes.slice input'
                                                      (FStar_UInt32.uint_to_t
                                                         Prims.int_zero) v),
                                                    (FStar_Bytes.len
                                                       (FStar_Bytes.slice
                                                          input'
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_zero)
                                                          v))) in
                                              res1
                                        with
                                        | FStar_Pervasives_Native.Some
                                            (v1, consumed) ->
                                            if consumed = v
                                            then
                                              FStar_Pervasives_Native.Some
                                                (v1, consumed)
                                            else FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Pervasives_Native.None)
                               with
                               | FStar_Pervasives_Native.Some (v', l') ->
                                   FStar_Pervasives_Native.Some
                                     (v', (FStar_UInt32.add l l'))
                               | uu___ -> FStar_Pervasives_Native.None)
                          | uu___ -> FStar_Pervasives_Native.None
                    with
                    | FStar_Pervasives_Native.Some (x, consumed) ->
                        FStar_Pervasives_Native.Some (x, consumed)
                    | uu___ -> FStar_Pervasives_Native.None in
                  match res with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (x, consumed) ->
                      let x1 = x in
                      FStar_Pervasives_Native.Some (x1, consumed)
            with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some (v1, consumed)
            | uu___ -> FStar_Pervasives_Native.None
let (serialize32_bounded_vlbytes_aux :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        (unit, unit, unit, FStar_Bytes.bytes, unit, unit)
          LowParse_Spec_VLData.parse_bounded_vldata_strong_t ->
          LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun l ->
        fun input ->
          let pl = input in
          let len = FStar_Bytes.len pl in
          let slen =
            match l with
            | uu___ when uu___ = Prims.int_one ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_1 len
            | uu___ when uu___ = (Prims.of_int (2)) ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_2 len
            | uu___ when uu___ = (Prims.of_int (3)) ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_3 len
            | uu___ when uu___ = (Prims.of_int (4)) ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_4 len in
          let res = FStar_Bytes.append slen pl in res
let (serialize32_bounded_vlbytes' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        (unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t ->
          LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun l ->
        fun input ->
          let x = input in
          let pl = x in
          let len = FStar_Bytes.len pl in
          let slen =
            match l with
            | uu___ when uu___ = Prims.int_one ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_1 len
            | uu___ when uu___ = (Prims.of_int (2)) ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_2 len
            | uu___ when uu___ = (Prims.of_int (3)) ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_3 len
            | uu___ when uu___ = (Prims.of_int (4)) ->
                LowParse_SLow_BoundedInt.serialize32_bounded_integer_4 len in
          let res = FStar_Bytes.append slen pl in res
let (serialize32_bounded_vlbytes :
  Prims.nat ->
    Prims.nat ->
      (unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t ->
        LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun input ->
        let x = input in
        let pl = x in
        let len = FStar_Bytes.len pl in
        let slen =
          match if max < (Prims.of_int (256))
                then Prims.int_one
                else
                  if max < (Prims.parse_int "65536")
                  then (Prims.of_int (2))
                  else
                    if max < (Prims.parse_int "16777216")
                    then (Prims.of_int (3))
                    else (Prims.of_int (4))
          with
          | uu___ when uu___ = Prims.int_one ->
              LowParse_SLow_BoundedInt.serialize32_bounded_integer_1 len
          | uu___ when uu___ = (Prims.of_int (2)) ->
              LowParse_SLow_BoundedInt.serialize32_bounded_integer_2 len
          | uu___ when uu___ = (Prims.of_int (3)) ->
              LowParse_SLow_BoundedInt.serialize32_bounded_integer_3 len
          | uu___ when uu___ = (Prims.of_int (4)) ->
              LowParse_SLow_BoundedInt.serialize32_bounded_integer_4 len in
        let res = FStar_Bytes.append slen pl in res
let (size32_all_bytes : FStar_Bytes.bytes -> FStar_UInt32.t) =
  fun input -> let res = FStar_Bytes.len input in res
let (size32_bounded_vlbytes_aux :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        (unit, unit, unit, FStar_Bytes.bytes, unit, unit)
          LowParse_Spec_VLData.parse_bounded_vldata_strong_t ->
          FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun input ->
          let len = let res = FStar_Bytes.len input in res in
          FStar_UInt32.add (FStar_UInt32.uint_to_t l) len
let (size32_bounded_vlbytes' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        (unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t ->
          FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun input ->
          let len = let res = FStar_Bytes.len input in res in
          FStar_UInt32.add (FStar_UInt32.uint_to_t l) len
let (size32_bounded_vlbytes :
  Prims.nat ->
    Prims.nat ->
      (unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t ->
        FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun input ->
        let len = let res = FStar_Bytes.len input in res in
        FStar_UInt32.add
          (FStar_UInt32.uint_to_t
             (if max < (Prims.of_int (256))
              then Prims.int_one
              else
                if max < (Prims.parse_int "65536")
                then (Prims.of_int (2))
                else
                  if max < (Prims.parse_int "16777216")
                  then (Prims.of_int (3))
                  else (Prims.of_int (4)))) len
let (parse32_bounded_vlgenbytes :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              (LowParse_SLow_Base.bytes32 ->
                 (FStar_UInt32.t * FStar_UInt32.t)
                   FStar_Pervasives_Native.option)
                ->
                LowParse_SLow_Base.bytes32 ->
                  ((unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t *
                    FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun kk ->
            fun pk ->
              fun pk32 ->
                fun input ->
                  match match pk32 input with
                        | FStar_Pervasives_Native.None ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some (sz, consumed) ->
                            let input' =
                              FStar_Bytes.slice input consumed
                                (FStar_Bytes.len input) in
                            (match match if
                                           FStar_UInt32.lt
                                             (FStar_Bytes.len input') sz
                                         then FStar_Pervasives_Native.None
                                         else
                                           (match let res =
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_Bytes.slice
                                                          input'
                                                          (FStar_UInt32.uint_to_t
                                                             Prims.int_zero)
                                                          sz),
                                                        (FStar_Bytes.len
                                                           (FStar_Bytes.slice
                                                              input'
                                                              (FStar_UInt32.uint_to_t
                                                                 Prims.int_zero)
                                                              sz))) in
                                                  res
                                            with
                                            | FStar_Pervasives_Native.Some
                                                (v, consumed1) ->
                                                if consumed1 = sz
                                                then
                                                  FStar_Pervasives_Native.Some
                                                    (v, consumed1)
                                                else
                                                  FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.None ->
                                                FStar_Pervasives_Native.None)
                                   with
                                   | FStar_Pervasives_Native.Some
                                       (v, consumed1) ->
                                       FStar_Pervasives_Native.Some
                                         (v, consumed1)
                                   | FStar_Pervasives_Native.None ->
                                       FStar_Pervasives_Native.None
                             with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Pervasives_Native.None
                             | FStar_Pervasives_Native.Some (x, consumed') ->
                                 FStar_Pervasives_Native.Some
                                   (x, (FStar_UInt32.add consumed consumed')))
                  with
                  | FStar_Pervasives_Native.Some (v1, consumed) ->
                      FStar_Pervasives_Native.Some (v1, consumed)
                  | uu___ -> FStar_Pervasives_Native.None
let (serialize32_bounded_vlgenbytes :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> LowParse_SLow_Base.bytes32) ->
              (unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t ->
                LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun kk ->
        fun pk ->
          fun sk ->
            fun sk32 ->
              fun input ->
                let x = input in
                let sp = x in
                let len = FStar_Bytes.len sp in
                FStar_Bytes.append (sk32 len) sp
let (size32_bounded_vlgenbytes :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> FStar_UInt32.t) ->
              (unit, unit) LowParse_Spec_Bytes.parse_bounded_vlbytes_t ->
                FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun kk ->
        fun pk ->
          fun sk ->
            fun sk32 ->
              fun input ->
                let sp = let res = FStar_Bytes.len input in res in
                FStar_UInt32.add (sk32 sp) sp