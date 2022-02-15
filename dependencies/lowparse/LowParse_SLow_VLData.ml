open Prims
let (parse32_vldata_payload :
  LowParse_Spec_BoundedInt.integer_size ->
    unit ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              FStar_UInt32.t ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun f ->
      fun k ->
        fun t ->
          fun p ->
            fun p32 ->
              fun i ->
                fun input ->
                  if FStar_UInt32.lt (FStar_Bytes.len input) i
                  then FStar_Pervasives_Native.None
                  else
                    (match p32
                             (FStar_Bytes.slice input
                                (FStar_UInt32.uint_to_t Prims.int_zero) i)
                     with
                     | FStar_Pervasives_Native.Some (v, consumed) ->
                         if consumed = i
                         then FStar_Pervasives_Native.Some (v, consumed)
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None)
let (parse32_vldata_gen :
  LowParse_Spec_BoundedInt.integer_size ->
    unit ->
      (FStar_UInt32.t -> Prims.bool) ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun f ->
      fun f' ->
        fun k ->
          fun t ->
            fun p ->
              fun p32 ->
                fun input ->
                  match match match sz with
                              | uu___ when uu___ = Prims.int_one ->
                                  LowParse_SLow_BoundedInt.parse32_bounded_integer_1
                                    input
                              | uu___ when uu___ = (Prims.of_int (2)) ->
                                  LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                    input
                              | uu___ when uu___ = (Prims.of_int (3)) ->
                                  LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                    input
                              | uu___ when uu___ = (Prims.of_int (4)) ->
                                  LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                    input
                        with
                        | FStar_Pervasives_Native.Some (v, consumed) ->
                            if f' v
                            then FStar_Pervasives_Native.Some (v, consumed)
                            else FStar_Pervasives_Native.None
                        | uu___ -> FStar_Pervasives_Native.None
                  with
                  | FStar_Pervasives_Native.Some (v, l) ->
                      let input' =
                        FStar_Bytes.slice input l (FStar_Bytes.len input) in
                      (match if FStar_UInt32.lt (FStar_Bytes.len input') v
                             then FStar_Pervasives_Native.None
                             else
                               (match p32
                                        (FStar_Bytes.slice input'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero) v)
                                with
                                | FStar_Pervasives_Native.Some (v1, consumed)
                                    ->
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
let (parse32_vldata :
  LowParse_Spec_BoundedInt.integer_size ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            LowParse_SLow_Base.bytes32 ->
              (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun k ->
      fun t ->
        fun p ->
          fun p32 ->
            fun input ->
              match match match sz with
                          | uu___ when uu___ = Prims.int_one ->
                              LowParse_SLow_BoundedInt.parse32_bounded_integer_1
                                input
                          | uu___ when uu___ = (Prims.of_int (2)) ->
                              LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                input
                          | uu___ when uu___ = (Prims.of_int (3)) ->
                              LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                input
                          | uu___ when uu___ = (Prims.of_int (4)) ->
                              LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                input
                    with
                    | FStar_Pervasives_Native.Some (v, consumed) ->
                        FStar_Pervasives_Native.Some (v, consumed)
                    | uu___ -> FStar_Pervasives_Native.None
              with
              | FStar_Pervasives_Native.Some (v, l) ->
                  let input' =
                    FStar_Bytes.slice input l (FStar_Bytes.len input) in
                  (match if FStar_UInt32.lt (FStar_Bytes.len input') v
                         then FStar_Pervasives_Native.None
                         else
                           (match p32
                                    (FStar_Bytes.slice input'
                                       (FStar_UInt32.uint_to_t Prims.int_zero)
                                       v)
                            with
                            | FStar_Pervasives_Native.Some (v1, consumed) ->
                                if consumed = v
                                then
                                  FStar_Pervasives_Native.Some (v1, consumed)
                                else FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None)
                   with
                   | FStar_Pervasives_Native.Some (v', l') ->
                       FStar_Pervasives_Native.Some
                         (v', (FStar_UInt32.add l l'))
                   | uu___ -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_vldata' :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          Prims.nat ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  (LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                    ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun l ->
            fun k ->
              fun t ->
                fun p ->
                  fun p32 ->
                    fun input ->
                      match match match l with
                                  | uu___ when uu___ = Prims.int_one ->
                                      LowParse_SLow_BoundedInt.parse32_bounded_integer_1
                                        input
                                  | uu___ when uu___ = (Prims.of_int (2)) ->
                                      LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                        input
                                  | uu___ when uu___ = (Prims.of_int (3)) ->
                                      LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                        input
                                  | uu___ when uu___ = (Prims.of_int (4)) ->
                                      LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                        input
                            with
                            | FStar_Pervasives_Native.Some (v, consumed) ->
                                if
                                  Prims.op_Negation
                                    ((FStar_UInt32.lt v min32) ||
                                       (FStar_UInt32.lt max32 v))
                                then
                                  FStar_Pervasives_Native.Some (v, consumed)
                                else FStar_Pervasives_Native.None
                            | uu___ -> FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (v, l1) ->
                          let input' =
                            FStar_Bytes.slice input l1
                              (FStar_Bytes.len input) in
                          (match if
                                   FStar_UInt32.lt (FStar_Bytes.len input') v
                                 then FStar_Pervasives_Native.None
                                 else
                                   (match p32
                                            (FStar_Bytes.slice input'
                                               (FStar_UInt32.uint_to_t
                                                  Prims.int_zero) v)
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
                                 (v', (FStar_UInt32.add l1 l'))
                           | uu___ -> FStar_Pervasives_Native.None)
                      | uu___ -> FStar_Pervasives_Native.None
let (parse32_bounded_vldata :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (LowParse_SLow_Base.bytes32 ->
                   (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                  ->
                  LowParse_SLow_Base.bytes32 ->
                    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun k ->
            fun t ->
              fun p ->
                fun p32 ->
                  fun input ->
                    match match match if max < (Prims.of_int (256))
                                      then Prims.int_one
                                      else
                                        if max < (Prims.parse_int "65536")
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
                                | uu___ when uu___ = (Prims.of_int (2)) ->
                                    LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                      input
                                | uu___ when uu___ = (Prims.of_int (3)) ->
                                    LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                      input
                                | uu___ when uu___ = (Prims.of_int (4)) ->
                                    LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                      input
                          with
                          | FStar_Pervasives_Native.Some (v, consumed) ->
                              if
                                Prims.op_Negation
                                  ((FStar_UInt32.lt v min32) ||
                                     (FStar_UInt32.lt max32 v))
                              then FStar_Pervasives_Native.Some (v, consumed)
                              else FStar_Pervasives_Native.None
                          | uu___ -> FStar_Pervasives_Native.None
                    with
                    | FStar_Pervasives_Native.Some (v, l) ->
                        let input' =
                          FStar_Bytes.slice input l (FStar_Bytes.len input) in
                        (match if FStar_UInt32.lt (FStar_Bytes.len input') v
                               then FStar_Pervasives_Native.None
                               else
                                 (match p32
                                          (FStar_Bytes.slice input'
                                             (FStar_UInt32.uint_to_t
                                                Prims.int_zero) v)
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
let (parse32_bounded_vldata_strong_aux :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          Prims.nat ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (LowParse_SLow_Base.bytes32 ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                      ->
                      LowParse_SLow_Base.bytes32 ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun l ->
            fun k ->
              fun t ->
                fun p ->
                  fun s ->
                    fun p32 ->
                      fun input ->
                        let res =
                          match match match match l with
                                            | uu___ when
                                                uu___ = Prims.int_one ->
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
                                             (match p32
                                                      (FStar_Bytes.slice
                                                         input'
                                                         (FStar_UInt32.uint_to_t
                                                            Prims.int_zero) v)
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  (v1, consumed) ->
                                                  if consumed = v
                                                  then
                                                    FStar_Pervasives_Native.Some
                                                      (v1, consumed)
                                                  else
                                                    FStar_Pervasives_Native.None
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  FStar_Pervasives_Native.None)
                                     with
                                     | FStar_Pervasives_Native.Some (v', l')
                                         ->
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

let (parse32_bounded_vldata_strong' :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          Prims.nat ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (LowParse_SLow_Base.bytes32 ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                      ->
                      LowParse_SLow_Base.bytes32 ->
                        (Obj.t * FStar_UInt32.t)
                          FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun l ->
            fun k ->
              fun t ->
                fun p ->
                  fun s ->
                    fun p32 ->
                      fun input ->
                        let res =
                          match match match match l with
                                            | uu___ when
                                                uu___ = Prims.int_one ->
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
                                             (match p32
                                                      (FStar_Bytes.slice
                                                         input'
                                                         (FStar_UInt32.uint_to_t
                                                            Prims.int_zero) v)
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  (v1, consumed) ->
                                                  if consumed = v
                                                  then
                                                    FStar_Pervasives_Native.Some
                                                      (v1, consumed)
                                                  else
                                                    FStar_Pervasives_Native.None
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  FStar_Pervasives_Native.None)
                                     with
                                     | FStar_Pervasives_Native.Some (v', l')
                                         ->
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
let (parse32_bounded_vldata_strong :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit ->
                  (LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                    ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun k ->
            fun t ->
              fun p ->
                fun s ->
                  fun p32 ->
                    fun input ->
                      let res =
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
                                          | uu___ when uu___ = Prims.int_one
                                              ->
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
                              | FStar_Pervasives_Native.Some (v, l) ->
                                  let input' =
                                    FStar_Bytes.slice input l
                                      (FStar_Bytes.len input) in
                                  (match if
                                           FStar_UInt32.lt
                                             (FStar_Bytes.len input') v
                                         then FStar_Pervasives_Native.None
                                         else
                                           (match p32
                                                    (FStar_Bytes.slice input'
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_zero) v)
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
let (serialize32_bounded_vldata_strong_aux :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              unit ->
                (Obj.t -> LowParse_SLow_Base.bytes32) ->
                  Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun s ->
                fun s32 ->
                  fun input ->
                    let pl = s32 input in
                    let len = FStar_Bytes.len pl in
                    let slen =
                      match l with
                      | uu___ when uu___ = Prims.int_one ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_1
                            len
                      | uu___ when uu___ = (Prims.of_int (2)) ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_2
                            len
                      | uu___ when uu___ = (Prims.of_int (3)) ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_3
                            len
                      | uu___ when uu___ = (Prims.of_int (4)) ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_4
                            len in
                    let res = FStar_Bytes.append slen pl in res

let (serialize32_bounded_vldata_strong' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              unit ->
                (Obj.t -> LowParse_SLow_Base.bytes32) ->
                  Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun s ->
                fun s32 ->
                  fun input ->
                    let pl = s32 input in
                    let len = FStar_Bytes.len pl in
                    let slen =
                      match l with
                      | uu___ when uu___ = Prims.int_one ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_1
                            len
                      | uu___ when uu___ = (Prims.of_int (2)) ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_2
                            len
                      | uu___ when uu___ = (Prims.of_int (3)) ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_3
                            len
                      | uu___ when uu___ = (Prims.of_int (4)) ->
                          LowParse_SLow_BoundedInt.serialize32_bounded_integer_4
                            len in
                    let res = FStar_Bytes.append slen pl in res
let (serialize32_bounded_vldata_strong :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> LowParse_SLow_Base.bytes32) ->
                Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun s32 ->
                fun input ->
                  let pl = s32 input in
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
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_1
                          len
                    | uu___ when uu___ = (Prims.of_int (2)) ->
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_2
                          len
                    | uu___ when uu___ = (Prims.of_int (3)) ->
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_3
                          len
                    | uu___ when uu___ = (Prims.of_int (4)) ->
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_4
                          len in
                  let res = FStar_Bytes.append slen pl in res
let (serialize32_bounded_vldata :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> LowParse_SLow_Base.bytes32) ->
                Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun s32 ->
                fun input ->
                  let pl = s32 input in
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
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_1
                          len
                    | uu___ when uu___ = (Prims.of_int (2)) ->
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_2
                          len
                    | uu___ when uu___ = (Prims.of_int (3)) ->
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_3
                          len
                    | uu___ when uu___ = (Prims.of_int (4)) ->
                        LowParse_SLow_BoundedInt.serialize32_bounded_integer_4
                          len in
                  let res = FStar_Bytes.append slen pl in res
let (check_vldata_payload_size32 :
  Prims.nat ->
    FStar_UInt32.t ->
      Prims.nat ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit -> (Obj.t -> FStar_UInt32.t) -> Obj.t -> Prims.bool)
  =
  fun min ->
    fun min32 ->
      fun max ->
        fun max32 ->
          fun k ->
            fun t ->
              fun p ->
                fun s ->
                  fun s32 ->
                    fun input ->
                      let sz = s32 input in
                      Prims.op_Negation
                        (((sz =
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")))
                            || (FStar_UInt32.lt sz min32))
                           || (FStar_UInt32.lt max32 sz))
let (size32_bounded_vldata_strong' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              unit ->
                (Obj.t -> FStar_UInt32.t) ->
                  FStar_UInt32.t -> Obj.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun s ->
                fun s32 ->
                  fun sz32 ->
                    fun input ->
                      let len = s32 input in FStar_UInt32.add sz32 len
let (size32_bounded_vldata_strong :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> FStar_UInt32.t) ->
                FStar_UInt32.t -> Obj.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun s32 ->
                fun sz32 ->
                  fun input ->
                    let len = s32 input in FStar_UInt32.add sz32 len
let (size32_bounded_vldata :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> FStar_UInt32.t) ->
                FStar_UInt32.t -> Obj.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun s32 ->
                fun sz32 ->
                  fun input ->
                    let len = s32 input in FStar_UInt32.add sz32 len