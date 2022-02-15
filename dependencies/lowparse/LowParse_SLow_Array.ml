open Prims
let (parse32_array' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            Prims.nat ->
              FStar_UInt32.t ->
                Prims.nat ->
                  unit ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t Prims.list * FStar_UInt32.t)
                        FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun p32 ->
            fun array_byte_size ->
              fun array_byte_size32 ->
                fun elem_count ->
                  fun u ->
                    fun input ->
                      match match if
                                    FStar_UInt32.lt (FStar_Bytes.len input)
                                      array_byte_size32
                                  then FStar_Pervasives_Native.None
                                  else
                                    (match match let accu =
                                                   let uu___1 =
                                                     C_Loops.total_while_gen
                                                       () ()
                                                       (fun uu___2 ->
                                                          match uu___2 with
                                                          | (x, uu___3) -> x)
                                                       (fun uu___2 ->
                                                          match uu___2 with
                                                          | (uu___3, x) ->
                                                              let uu___4 = x in
                                                              (match uu___4
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   (input',
                                                                    accu')
                                                                   ->
                                                                   let len =
                                                                    FStar_Bytes.len
                                                                    input' in
                                                                   if
                                                                    len =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                   then
                                                                    (false,
                                                                    x)
                                                                   else
                                                                    (match 
                                                                    p32
                                                                    input'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (v,
                                                                    consumed)
                                                                    ->
                                                                    if
                                                                    consumed
                                                                    =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    then
                                                                    (false,
                                                                    FStar_Pervasives_Native.None)
                                                                    else
                                                                    (let input''
                                                                    =
                                                                    FStar_Bytes.slice
                                                                    input'
                                                                    consumed
                                                                    len in
                                                                    (true,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (input'',
                                                                    (v ::
                                                                    accu')))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (false,
                                                                    FStar_Pervasives_Native.None))))
                                                       (true,
                                                         (FStar_Pervasives_Native.Some
                                                            ((FStar_Bytes.slice
                                                                input
                                                                (FStar_UInt32.uint_to_t
                                                                   Prims.int_zero)
                                                                array_byte_size32),
                                                              []))) in
                                                   match uu___1 with
                                                   | (uu___2, res) -> res in
                                                 match accu with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     FStar_Pervasives_Native.None
                                                 | FStar_Pervasives_Native.Some
                                                     (uu___1, accu') ->
                                                     FStar_Pervasives_Native.Some
                                                       (LowParse_SLow_List.list_rev
                                                          accu')
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some res
                                               ->
                                               FStar_Pervasives_Native.Some
                                                 (res,
                                                   (FStar_Bytes.len
                                                      (FStar_Bytes.slice
                                                         input
                                                         (FStar_UInt32.uint_to_t
                                                            Prims.int_zero)
                                                         array_byte_size32)))
                                     with
                                     | FStar_Pervasives_Native.Some
                                         (v, consumed) ->
                                         if consumed = array_byte_size32
                                         then
                                           FStar_Pervasives_Native.Some
                                             (v, consumed)
                                         else FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None)
                            with
                            | FStar_Pervasives_Native.Some (v, consumed) ->
                                FStar_Pervasives_Native.Some (v, consumed)
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (v1, consumed) ->
                          FStar_Pervasives_Native.Some (v1, consumed)
                      | uu___ -> FStar_Pervasives_Native.None
let (parse32_array :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            Prims.nat ->
              FStar_UInt32.t ->
                Prims.nat ->
                  unit ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t Prims.list * FStar_UInt32.t)
                        FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun p32 ->
            fun array_byte_size ->
              fun array_byte_size32 ->
                fun elem_count ->
                  fun u ->
                    fun x ->
                      match match if
                                    FStar_UInt32.lt (FStar_Bytes.len x)
                                      array_byte_size32
                                  then FStar_Pervasives_Native.None
                                  else
                                    (match match let accu =
                                                   let uu___1 =
                                                     C_Loops.total_while_gen
                                                       () ()
                                                       (fun uu___2 ->
                                                          match uu___2 with
                                                          | (x1, uu___3) ->
                                                              x1)
                                                       (fun uu___2 ->
                                                          match uu___2 with
                                                          | (uu___3, x1) ->
                                                              let uu___4 = x1 in
                                                              (match uu___4
                                                               with
                                                               | FStar_Pervasives_Native.Some
                                                                   (input',
                                                                    accu')
                                                                   ->
                                                                   let len =
                                                                    FStar_Bytes.len
                                                                    input' in
                                                                   if
                                                                    len =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                   then
                                                                    (false,
                                                                    x1)
                                                                   else
                                                                    (match 
                                                                    p32
                                                                    input'
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (v,
                                                                    consumed)
                                                                    ->
                                                                    if
                                                                    consumed
                                                                    =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    then
                                                                    (false,
                                                                    FStar_Pervasives_Native.None)
                                                                    else
                                                                    (let input''
                                                                    =
                                                                    FStar_Bytes.slice
                                                                    input'
                                                                    consumed
                                                                    len in
                                                                    (true,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (input'',
                                                                    (v ::
                                                                    accu')))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (false,
                                                                    FStar_Pervasives_Native.None))))
                                                       (true,
                                                         (FStar_Pervasives_Native.Some
                                                            ((FStar_Bytes.slice
                                                                x
                                                                (FStar_UInt32.uint_to_t
                                                                   Prims.int_zero)
                                                                array_byte_size32),
                                                              []))) in
                                                   match uu___1 with
                                                   | (uu___2, res) -> res in
                                                 match accu with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     FStar_Pervasives_Native.None
                                                 | FStar_Pervasives_Native.Some
                                                     (uu___1, accu') ->
                                                     FStar_Pervasives_Native.Some
                                                       (LowParse_SLow_List.list_rev
                                                          accu')
                                           with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some res
                                               ->
                                               FStar_Pervasives_Native.Some
                                                 (res,
                                                   (FStar_Bytes.len
                                                      (FStar_Bytes.slice x
                                                         (FStar_UInt32.uint_to_t
                                                            Prims.int_zero)
                                                         array_byte_size32)))
                                     with
                                     | FStar_Pervasives_Native.Some
                                         (v, consumed) ->
                                         if consumed = array_byte_size32
                                         then
                                           FStar_Pervasives_Native.Some
                                             (v, consumed)
                                         else FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Pervasives_Native.None)
                            with
                            | FStar_Pervasives_Native.Some (v, consumed) ->
                                FStar_Pervasives_Native.Some (v, consumed)
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (v1, consumed) ->
                          FStar_Pervasives_Native.Some (v1, consumed)
                      | uu___ -> FStar_Pervasives_Native.None
let (serialize32_array' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            Prims.nat ->
              Prims.nat ->
                unit -> Obj.t Prims.list -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun array_byte_size ->
              fun elem_count ->
                fun u ->
                  fun input ->
                    let x = input in
                    let uu___ =
                      let uu___1 =
                        C_Loops.total_while_gen () ()
                          (fun uu___2 ->
                             match uu___2 with | (x1, uu___3) -> x1)
                          (fun uu___2 ->
                             match uu___2 with
                             | (uu___3, x1) ->
                                 let uu___4 = x1 in
                                 (match uu___4 with
                                  | (accu, input') ->
                                      (match input' with
                                       | [] -> (false, x1)
                                       | a::q ->
                                           let sa = s32 a in
                                           let accu' =
                                             FStar_Bytes.append accu sa in
                                           (true, (accu', q)))))
                          (true, (FStar_Bytes.empty_bytes, x)) in
                      match uu___1 with | (uu___2, res) -> res in
                    match uu___ with | (res, uu___1) -> res
let (serialize32_array :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            Prims.nat ->
              Prims.nat ->
                unit -> Obj.t Prims.list -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun array_byte_size ->
              fun elem_count ->
                fun u ->
                  fun x ->
                    let x1 = x in
                    let uu___ =
                      let uu___1 =
                        C_Loops.total_while_gen () ()
                          (fun uu___2 ->
                             match uu___2 with | (x2, uu___3) -> x2)
                          (fun uu___2 ->
                             match uu___2 with
                             | (uu___3, x2) ->
                                 let uu___4 = x2 in
                                 (match uu___4 with
                                  | (accu, input') ->
                                      (match input' with
                                       | [] -> (false, x2)
                                       | a::q ->
                                           let sa = s32 a in
                                           let accu' =
                                             FStar_Bytes.append accu sa in
                                           (true, (accu', q)))))
                          (true, (FStar_Bytes.empty_bytes, x1)) in
                      match uu___1 with | (uu___2, res) -> res in
                    match uu___ with | (res, uu___1) -> res
let (size32_array :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          Prims.nat ->
            FStar_UInt32.t ->
              Prims.nat -> unit -> Obj.t Prims.list -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun array_byte_size ->
            fun array_byte_size32 ->
              fun elem_count -> fun u -> fun x -> array_byte_size32
let (parse32_vlarray :
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
                    Prims.nat ->
                      Prims.nat ->
                        unit ->
                          LowParse_SLow_Base.bytes32 ->
                            (Obj.t Prims.list * FStar_UInt32.t)
                              FStar_Pervasives_Native.option)
  =
  fun array_byte_size_min ->
    fun array_byte_size_min32 ->
      fun array_byte_size_max ->
        fun array_byte_size_max32 ->
          fun k ->
            fun t ->
              fun p ->
                fun s ->
                  fun p32 ->
                    fun elem_count_min ->
                      fun elem_count_max ->
                        fun u ->
                          fun input ->
                            match let res =
                                    match match match match if
                                                              array_byte_size_max
                                                                <
                                                                (Prims.of_int (256))
                                                            then
                                                              Prims.int_one
                                                            else
                                                              if
                                                                array_byte_size_max
                                                                  <
                                                                  (Prims.parse_int "65536")
                                                              then
                                                                (Prims.of_int (2))
                                                              else
                                                                if
                                                                  array_byte_size_max
                                                                    <
                                                                    (Prims.parse_int "16777216")
                                                                then
                                                                  (Prims.of_int (3))
                                                                else
                                                                  (Prims.of_int (4))
                                                      with
                                                      | uu___ when
                                                          uu___ =
                                                            Prims.int_one
                                                          ->
                                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_1
                                                            input
                                                      | uu___ when
                                                          uu___ =
                                                            (Prims.of_int (2))
                                                          ->
                                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_2
                                                            input
                                                      | uu___ when
                                                          uu___ =
                                                            (Prims.of_int (3))
                                                          ->
                                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                                            input
                                                      | uu___ when
                                                          uu___ =
                                                            (Prims.of_int (4))
                                                          ->
                                                          LowParse_SLow_BoundedInt.parse32_bounded_integer_4
                                                            input
                                                with
                                                | FStar_Pervasives_Native.Some
                                                    (v, consumed) ->
                                                    if
                                                      Prims.op_Negation
                                                        ((FStar_UInt32.lt v
                                                            array_byte_size_min32)
                                                           ||
                                                           (FStar_UInt32.lt
                                                              array_byte_size_max32
                                                              v))
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        (v, consumed)
                                                    else
                                                      FStar_Pervasives_Native.None
                                                | uu___ ->
                                                    FStar_Pervasives_Native.None
                                          with
                                          | FStar_Pervasives_Native.Some
                                              (v, l) ->
                                              let input' =
                                                FStar_Bytes.slice input l
                                                  (FStar_Bytes.len input) in
                                              (match if
                                                       FStar_UInt32.lt
                                                         (FStar_Bytes.len
                                                            input') v
                                                     then
                                                       FStar_Pervasives_Native.None
                                                     else
                                                       (match match let accu
                                                                    =
                                                                    let uu___1
                                                                    =
                                                                    C_Loops.total_while_gen
                                                                    () ()
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (x,
                                                                    uu___3)
                                                                    -> x)
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (uu___3,
                                                                    x) ->
                                                                    let uu___4
                                                                    = x in
                                                                    (match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (input'1,
                                                                    accu') ->
                                                                    let len =
                                                                    FStar_Bytes.len
                                                                    input'1 in
                                                                    if
                                                                    len =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    then
                                                                    (false,
                                                                    x)
                                                                    else
                                                                    (match 
                                                                    p32
                                                                    input'1
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (v1,
                                                                    consumed)
                                                                    ->
                                                                    if
                                                                    consumed
                                                                    =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    then
                                                                    (false,
                                                                    FStar_Pervasives_Native.None)
                                                                    else
                                                                    (let input''
                                                                    =
                                                                    FStar_Bytes.slice
                                                                    input'1
                                                                    consumed
                                                                    len in
                                                                    (true,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (input'',
                                                                    (v1 ::
                                                                    accu')))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (false,
                                                                    FStar_Pervasives_Native.None))))
                                                                    (true,
                                                                    (FStar_Pervasives_Native.Some
                                                                    ((FStar_Bytes.slice
                                                                    input'
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    v), []))) in
                                                                    match uu___1
                                                                    with
                                                                    | 
                                                                    (uu___2,
                                                                    res1) ->
                                                                    res1 in
                                                                    match accu
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (uu___1,
                                                                    accu') ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (LowParse_SLow_List.list_rev
                                                                    accu')
                                                              with
                                                              | FStar_Pervasives_Native.None
                                                                  ->
                                                                  FStar_Pervasives_Native.None
                                                              | FStar_Pervasives_Native.Some
                                                                  res1 ->
                                                                  FStar_Pervasives_Native.Some
                                                                    (res1,
                                                                    (FStar_Bytes.len
                                                                    (FStar_Bytes.slice
                                                                    input'
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    v)))
                                                        with
                                                        | FStar_Pervasives_Native.Some
                                                            (v1, consumed) ->
                                                            if consumed = v
                                                            then
                                                              FStar_Pervasives_Native.Some
                                                                (v1,
                                                                  consumed)
                                                            else
                                                              FStar_Pervasives_Native.None
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            FStar_Pervasives_Native.None)
                                               with
                                               | FStar_Pervasives_Native.Some
                                                   (v', l') ->
                                                   FStar_Pervasives_Native.Some
                                                     (v',
                                                       (FStar_UInt32.add l l'))
                                               | uu___ ->
                                                   FStar_Pervasives_Native.None)
                                          | uu___ ->
                                              FStar_Pervasives_Native.None
                                    with
                                    | FStar_Pervasives_Native.Some
                                        (x, consumed) ->
                                        FStar_Pervasives_Native.Some
                                          (x, consumed)
                                    | uu___ -> FStar_Pervasives_Native.None in
                                  match res with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some
                                      (x, consumed) ->
                                      let x1 = x in
                                      FStar_Pervasives_Native.Some
                                        (x1, consumed)
                            with
                            | FStar_Pervasives_Native.Some (v1, consumed) ->
                                FStar_Pervasives_Native.Some (v1, consumed)
                            | uu___ -> FStar_Pervasives_Native.None
let (serialize32_vlarray :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> LowParse_SLow_Base.bytes32) ->
                Prims.nat ->
                  Prims.nat ->
                    unit -> Obj.t Prims.list -> LowParse_SLow_Base.bytes32)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun s32 ->
                fun elem_count_min ->
                  fun elem_count_max ->
                    fun u ->
                      fun input ->
                        let x = input in
                        let pl =
                          let uu___ =
                            let uu___1 =
                              C_Loops.total_while_gen () ()
                                (fun uu___2 ->
                                   match uu___2 with | (x1, uu___3) -> x1)
                                (fun uu___2 ->
                                   match uu___2 with
                                   | (uu___3, x1) ->
                                       let uu___4 = x1 in
                                       (match uu___4 with
                                        | (accu, input') ->
                                            (match input' with
                                             | [] -> (false, x1)
                                             | a::q ->
                                                 let sa = s32 a in
                                                 let accu' =
                                                   FStar_Bytes.append accu sa in
                                                 (true, (accu', q)))))
                                (true, (FStar_Bytes.empty_bytes, x)) in
                            match uu___1 with | (uu___2, res) -> res in
                          match uu___ with | (res, uu___1) -> res in
                        let len = FStar_Bytes.len pl in
                        let slen =
                          match if array_byte_size_max < (Prims.of_int (256))
                                then Prims.int_one
                                else
                                  if
                                    array_byte_size_max <
                                      (Prims.parse_int "65536")
                                  then (Prims.of_int (2))
                                  else
                                    if
                                      array_byte_size_max <
                                        (Prims.parse_int "16777216")
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
let (size32_vlarray :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat ->
                  unit ->
                    FStar_UInt32.t ->
                      FStar_UInt32.t -> Obj.t Prims.list -> FStar_UInt32.t)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min ->
                fun elem_count_max ->
                  fun u ->
                    fun size_header_byte_size32 ->
                      fun elem_byte_size32 ->
                        fun input ->
                          let len =
                            match let uu___ =
                                    C_Loops.total_while_gen () ()
                                      (fun uu___1 ->
                                         match uu___1 with | (x, uu___2) -> x)
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | (uu___2, x) ->
                                             let uu___3 = x in
                                             (match uu___3 with
                                              | (len1, rem) ->
                                                  (match rem with
                                                   | [] -> (false, x)
                                                   | a::q ->
                                                       let sza =
                                                         elem_byte_size32 in
                                                       let len' =
                                                         if
                                                           FStar_UInt32.lt
                                                             (FStar_UInt32.sub
                                                                (FStar_UInt32.uint_to_t
                                                                   (Prims.parse_int "4294967295"))
                                                                sza) len1
                                                         then
                                                           FStar_UInt32.uint_to_t
                                                             (Prims.parse_int "4294967295")
                                                         else
                                                           FStar_UInt32.add
                                                             len1 sza in
                                                       if
                                                         len' =
                                                           (FStar_UInt32.uint_to_t
                                                              (Prims.parse_int "4294967295"))
                                                       then
                                                         (false,
                                                           ((FStar_UInt32.uint_to_t
                                                               (Prims.parse_int "4294967295")),
                                                             []))
                                                       else (true, (len', q)))))
                                      (true,
                                        ((FStar_UInt32.uint_to_t
                                            Prims.int_zero), input)) in
                                  match uu___ with | (uu___1, res) -> res
                            with
                            | (len1, uu___) -> len1 in
                          FStar_UInt32.add size_header_byte_size32 len