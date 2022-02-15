open Prims
let (validate_vldata_payload :
  LowParse_Spec_BoundedInt.integer_size ->
    unit ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              FStar_UInt32.t ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun sz ->
    fun f ->
      fun k ->
        fun t ->
          fun p ->
            fun v ->
              fun i ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        if
                          (match k with
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
                          let h1 = FStar_HyperStack_ST.get () in
                          (if
                             FStar_UInt64.lt
                               (FStar_UInt64.sub
                                  (FStar_Int_Cast.uint32_to_uint64
                                     (match input with
                                      | { LowParse_Slice.base = base;
                                          LowParse_Slice.len = len;_} -> len))
                                  pos) (FStar_Int_Cast.uint32_to_uint64 i)
                           then
                             LowParse_Low_ErrorCode.validator_error_not_enough_data
                           else
                             (let pos' =
                                v () ()
                                  {
                                    LowParse_Slice.base =
                                      (match input with
                                       | { LowParse_Slice.base = base;
                                           LowParse_Slice.len = len;_} ->
                                           base);
                                    LowParse_Slice.len =
                                      (FStar_UInt32.add
                                         (FStar_Int_Cast.uint64_to_uint32 pos)
                                         i)
                                  } pos in
                              if LowParse_Low_ErrorCode.is_error pos'
                              then
                                (if
                                   pos' =
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 then
                                   LowParse_Low_ErrorCode.validator_error_generic
                                 else pos')
                              else pos'))
                        else
                          (let h1 = FStar_HyperStack_ST.get () in
                           if
                             FStar_UInt64.lt
                               (FStar_UInt64.sub
                                  (FStar_Int_Cast.uint32_to_uint64
                                     (match input with
                                      | { LowParse_Slice.base = base;
                                          LowParse_Slice.len = len;_} -> len))
                                  pos) (FStar_Int_Cast.uint32_to_uint64 i)
                           then
                             LowParse_Low_ErrorCode.validator_error_not_enough_data
                           else
                             (let pos' =
                                v () ()
                                  {
                                    LowParse_Slice.base =
                                      (match input with
                                       | { LowParse_Slice.base = base;
                                           LowParse_Slice.len = len;_} ->
                                           base);
                                    LowParse_Slice.len =
                                      (FStar_UInt32.add
                                         (FStar_Int_Cast.uint64_to_uint32 pos)
                                         i)
                                  } pos in
                              if LowParse_Low_ErrorCode.is_error pos'
                              then
                                (if
                                   pos' =
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 then
                                   LowParse_Low_ErrorCode.validator_error_generic
                                 else pos')
                              else
                                if
                                  (FStar_UInt64.sub pos' pos) <>
                                    (FStar_Int_Cast.uint32_to_uint64 i)
                                then
                                  LowParse_Low_ErrorCode.validator_error_generic
                                else pos'))
let (validate_vldata_gen :
  LowParse_Spec_BoundedInt.integer_size ->
    unit ->
      (FStar_UInt32.t -> Prims.bool) ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun sz ->
    fun f ->
      fun f' ->
        fun k ->
          fun t ->
            fun p ->
              fun v ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let res =
                          let h1 = FStar_HyperStack_ST.get () in
                          if
                            FStar_UInt64.lt
                              (FStar_UInt64.sub
                                 (FStar_Int_Cast.uint32_to_uint64
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len;_} -> len))
                                 pos) (FStar_UInt64.uint_to_t sz)
                          then
                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                          else
                            FStar_UInt64.add pos (FStar_UInt64.uint_to_t sz) in
                        if LowParse_Low_ErrorCode.is_error res
                        then res
                        else
                          (let va =
                             (match sz with
                              | uu___1 when uu___1 = Prims.int_one ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_1
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (2)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_2
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (3)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_3
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (4)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_4
                                    ()) () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           if f' va
                           then
                             let h1 = FStar_HyperStack_ST.get () in
                             (if
                                (match k with
                                 | {
                                     LowParse_Spec_Base.parser_kind_low =
                                       parser_kind_low;
                                     LowParse_Spec_Base.parser_kind_high =
                                       parser_kind_high;
                                     LowParse_Spec_Base.parser_kind_subkind =
                                       parser_kind_subkind;
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
                                     -> parser_kind_subkind)
                                  =
                                  (FStar_Pervasives_Native.Some
                                     LowParse_Spec_Base.ParserConsumesAll)
                              then
                                let h2 = FStar_HyperStack_ST.get () in
                                (if
                                   FStar_UInt64.lt
                                     (FStar_UInt64.sub
                                        (FStar_Int_Cast.uint32_to_uint64
                                           (match input with
                                            | { LowParse_Slice.base = base;
                                                LowParse_Slice.len = len;_}
                                                -> len)) res)
                                     (FStar_Int_Cast.uint32_to_uint64 va)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 else
                                   (let pos' =
                                      v () ()
                                        {
                                          LowParse_Slice.base =
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> base);
                                          LowParse_Slice.len =
                                            (FStar_UInt32.add
                                               (FStar_Int_Cast.uint64_to_uint32
                                                  res) va)
                                        } res in
                                    if LowParse_Low_ErrorCode.is_error pos'
                                    then
                                      (if
                                         pos' =
                                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else pos')
                                    else pos'))
                              else
                                (let h2 = FStar_HyperStack_ST.get () in
                                 if
                                   FStar_UInt64.lt
                                     (FStar_UInt64.sub
                                        (FStar_Int_Cast.uint32_to_uint64
                                           (match input with
                                            | { LowParse_Slice.base = base;
                                                LowParse_Slice.len = len;_}
                                                -> len)) res)
                                     (FStar_Int_Cast.uint32_to_uint64 va)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 else
                                   (let pos' =
                                      v () ()
                                        {
                                          LowParse_Slice.base =
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> base);
                                          LowParse_Slice.len =
                                            (FStar_UInt32.add
                                               (FStar_Int_Cast.uint64_to_uint32
                                                  res) va)
                                        } res in
                                    if LowParse_Low_ErrorCode.is_error pos'
                                    then
                                      (if
                                         pos' =
                                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else pos')
                                    else
                                      if
                                        (FStar_UInt64.sub pos' res) <>
                                          (FStar_Int_Cast.uint32_to_uint64 va)
                                      then
                                        LowParse_Low_ErrorCode.validator_error_generic
                                      else pos')))
                           else
                             LowParse_Low_ErrorCode.validator_error_generic)

let (jump_vldata_gen :
  LowParse_Spec_BoundedInt.integer_size ->
    unit ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun sz ->
    fun f ->
      fun k ->
        fun t ->
          fun p ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    let uu___ =
                      let uu___1 =
                        match sz with
                        | uu___2 when uu___2 = Prims.int_one ->
                            (LowParse_Low_BoundedInt.read_bounded_integer_1
                               ()) () () input pos
                        | uu___2 when uu___2 = (Prims.of_int (2)) ->
                            (LowParse_Low_BoundedInt.read_bounded_integer_2
                               ()) () () input pos
                        | uu___2 when uu___2 = (Prims.of_int (3)) ->
                            (LowParse_Low_BoundedInt.read_bounded_integer_3
                               ()) () () input pos
                        | uu___2 when uu___2 = (Prims.of_int (4)) ->
                            (LowParse_Low_BoundedInt.read_bounded_integer_4
                               ()) () () input pos in
                      FStar_UInt32.add (FStar_UInt32.uint_to_t sz) uu___1 in
                    FStar_UInt32.add pos uu___
let (validate_bounded_vldata' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
                ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun v ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let h1 = FStar_HyperStack_ST.get () in
                        let res =
                          let h2 = FStar_HyperStack_ST.get () in
                          if
                            FStar_UInt64.lt
                              (FStar_UInt64.sub
                                 (FStar_Int_Cast.uint32_to_uint64
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len;_} -> len))
                                 pos) (FStar_UInt64.uint_to_t l)
                          then
                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                          else
                            FStar_UInt64.add pos (FStar_UInt64.uint_to_t l) in
                        if LowParse_Low_ErrorCode.is_error res
                        then res
                        else
                          (let va =
                             (match l with
                              | uu___1 when uu___1 = Prims.int_one ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_1
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (2)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_2
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (3)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_3
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (4)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_4
                                    ()) () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           if
                             (if min = Prims.int_zero
                              then
                                FStar_UInt32.lte va
                                  (FStar_UInt32.uint_to_t max)
                              else
                                (FStar_UInt32.lte
                                   (FStar_UInt32.uint_to_t min) va)
                                  &&
                                  (FStar_UInt32.lte va
                                     (FStar_UInt32.uint_to_t max)))
                           then
                             let h2 = FStar_HyperStack_ST.get () in
                             (if
                                (match k with
                                 | {
                                     LowParse_Spec_Base.parser_kind_low =
                                       parser_kind_low;
                                     LowParse_Spec_Base.parser_kind_high =
                                       parser_kind_high;
                                     LowParse_Spec_Base.parser_kind_subkind =
                                       parser_kind_subkind;
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
                                     -> parser_kind_subkind)
                                  =
                                  (FStar_Pervasives_Native.Some
                                     LowParse_Spec_Base.ParserConsumesAll)
                              then
                                let h3 = FStar_HyperStack_ST.get () in
                                (if
                                   FStar_UInt64.lt
                                     (FStar_UInt64.sub
                                        (FStar_Int_Cast.uint32_to_uint64
                                           (match input with
                                            | { LowParse_Slice.base = base;
                                                LowParse_Slice.len = len;_}
                                                -> len)) res)
                                     (FStar_Int_Cast.uint32_to_uint64 va)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 else
                                   (let pos' =
                                      v () ()
                                        {
                                          LowParse_Slice.base =
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> base);
                                          LowParse_Slice.len =
                                            (FStar_UInt32.add
                                               (FStar_Int_Cast.uint64_to_uint32
                                                  res) va)
                                        } res in
                                    if LowParse_Low_ErrorCode.is_error pos'
                                    then
                                      (if
                                         pos' =
                                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else pos')
                                    else pos'))
                              else
                                (let h3 = FStar_HyperStack_ST.get () in
                                 if
                                   FStar_UInt64.lt
                                     (FStar_UInt64.sub
                                        (FStar_Int_Cast.uint32_to_uint64
                                           (match input with
                                            | { LowParse_Slice.base = base;
                                                LowParse_Slice.len = len;_}
                                                -> len)) res)
                                     (FStar_Int_Cast.uint32_to_uint64 va)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 else
                                   (let pos' =
                                      v () ()
                                        {
                                          LowParse_Slice.base =
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> base);
                                          LowParse_Slice.len =
                                            (FStar_UInt32.add
                                               (FStar_Int_Cast.uint64_to_uint32
                                                  res) va)
                                        } res in
                                    if LowParse_Low_ErrorCode.is_error pos'
                                    then
                                      (if
                                         pos' =
                                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else pos')
                                    else
                                      if
                                        (FStar_UInt64.sub pos' res) <>
                                          (FStar_Int_Cast.uint32_to_uint64 va)
                                      then
                                        LowParse_Low_ErrorCode.validator_error_generic
                                      else pos')))
                           else
                             LowParse_Low_ErrorCode.validator_error_generic)
let (validate_bounded_vldata :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun v ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let h1 = FStar_HyperStack_ST.get () in
                        let res =
                          let h2 = FStar_HyperStack_ST.get () in
                          if
                            FStar_UInt64.lt
                              (FStar_UInt64.sub
                                 (FStar_Int_Cast.uint32_to_uint64
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len;_} -> len))
                                 pos)
                              (FStar_UInt64.uint_to_t
                                 (if max < (Prims.of_int (256))
                                  then Prims.int_one
                                  else
                                    if max < (Prims.parse_int "65536")
                                    then (Prims.of_int (2))
                                    else
                                      if max < (Prims.parse_int "16777216")
                                      then (Prims.of_int (3))
                                      else (Prims.of_int (4))))
                          then
                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                          else
                            FStar_UInt64.add pos
                              (FStar_UInt64.uint_to_t
                                 (if max < (Prims.of_int (256))
                                  then Prims.int_one
                                  else
                                    if max < (Prims.parse_int "65536")
                                    then (Prims.of_int (2))
                                    else
                                      if max < (Prims.parse_int "16777216")
                                      then (Prims.of_int (3))
                                      else (Prims.of_int (4)))) in
                        if LowParse_Low_ErrorCode.is_error res
                        then res
                        else
                          (let va =
                             (match if max < (Prims.of_int (256))
                                    then Prims.int_one
                                    else
                                      if max < (Prims.parse_int "65536")
                                      then (Prims.of_int (2))
                                      else
                                        if max < (Prims.parse_int "16777216")
                                        then (Prims.of_int (3))
                                        else (Prims.of_int (4))
                              with
                              | uu___1 when uu___1 = Prims.int_one ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_1
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (2)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_2
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (3)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_3
                                    ()
                              | uu___1 when uu___1 = (Prims.of_int (4)) ->
                                  LowParse_Low_BoundedInt.read_bounded_integer_4
                                    ()) () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           if
                             (if min = Prims.int_zero
                              then
                                FStar_UInt32.lte va
                                  (FStar_UInt32.uint_to_t max)
                              else
                                (FStar_UInt32.lte
                                   (FStar_UInt32.uint_to_t min) va)
                                  &&
                                  (FStar_UInt32.lte va
                                     (FStar_UInt32.uint_to_t max)))
                           then
                             let h2 = FStar_HyperStack_ST.get () in
                             (if
                                (match k with
                                 | {
                                     LowParse_Spec_Base.parser_kind_low =
                                       parser_kind_low;
                                     LowParse_Spec_Base.parser_kind_high =
                                       parser_kind_high;
                                     LowParse_Spec_Base.parser_kind_subkind =
                                       parser_kind_subkind;
                                     LowParse_Spec_Base.parser_kind_metadata
                                       = parser_kind_metadata;_}
                                     -> parser_kind_subkind)
                                  =
                                  (FStar_Pervasives_Native.Some
                                     LowParse_Spec_Base.ParserConsumesAll)
                              then
                                let h3 = FStar_HyperStack_ST.get () in
                                (if
                                   FStar_UInt64.lt
                                     (FStar_UInt64.sub
                                        (FStar_Int_Cast.uint32_to_uint64
                                           (match input with
                                            | { LowParse_Slice.base = base;
                                                LowParse_Slice.len = len;_}
                                                -> len)) res)
                                     (FStar_Int_Cast.uint32_to_uint64 va)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 else
                                   (let pos' =
                                      v () ()
                                        {
                                          LowParse_Slice.base =
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> base);
                                          LowParse_Slice.len =
                                            (FStar_UInt32.add
                                               (FStar_Int_Cast.uint64_to_uint32
                                                  res) va)
                                        } res in
                                    if LowParse_Low_ErrorCode.is_error pos'
                                    then
                                      (if
                                         pos' =
                                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else pos')
                                    else pos'))
                              else
                                (let h3 = FStar_HyperStack_ST.get () in
                                 if
                                   FStar_UInt64.lt
                                     (FStar_UInt64.sub
                                        (FStar_Int_Cast.uint32_to_uint64
                                           (match input with
                                            | { LowParse_Slice.base = base;
                                                LowParse_Slice.len = len;_}
                                                -> len)) res)
                                     (FStar_Int_Cast.uint32_to_uint64 va)
                                 then
                                   LowParse_Low_ErrorCode.validator_error_not_enough_data
                                 else
                                   (let pos' =
                                      v () ()
                                        {
                                          LowParse_Slice.base =
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> base);
                                          LowParse_Slice.len =
                                            (FStar_UInt32.add
                                               (FStar_Int_Cast.uint64_to_uint32
                                                  res) va)
                                        } res in
                                    if LowParse_Low_ErrorCode.is_error pos'
                                    then
                                      (if
                                         pos' =
                                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else pos')
                                    else
                                      if
                                        (FStar_UInt64.sub pos' res) <>
                                          (FStar_Int_Cast.uint32_to_uint64 va)
                                      then
                                        LowParse_Low_ErrorCode.validator_error_generic
                                      else pos')))
                           else
                             LowParse_Low_ErrorCode.validator_error_generic)
let (jump_bounded_vldata' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      let h1 = FStar_HyperStack_ST.get () in
                      let uu___ =
                        let uu___1 =
                          match l with
                          | uu___2 when uu___2 = Prims.int_one ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_1
                                 ()) () () input pos
                          | uu___2 when uu___2 = (Prims.of_int (2)) ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_2
                                 ()) () () input pos
                          | uu___2 when uu___2 = (Prims.of_int (3)) ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_3
                                 ()) () () input pos
                          | uu___2 when uu___2 = (Prims.of_int (4)) ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_4
                                 ()) () () input pos in
                        FStar_UInt32.add (FStar_UInt32.uint_to_t l) uu___1 in
                      FStar_UInt32.add pos uu___
let (jump_bounded_vldata :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun u ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      let h1 = FStar_HyperStack_ST.get () in
                      let uu___ =
                        let uu___1 =
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
                          | uu___2 when uu___2 = Prims.int_one ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_1
                                 ()) () () input pos
                          | uu___2 when uu___2 = (Prims.of_int (2)) ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_2
                                 ()) () () input pos
                          | uu___2 when uu___2 = (Prims.of_int (3)) ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_3
                                 ()) () () input pos
                          | uu___2 when uu___2 = (Prims.of_int (4)) ->
                              (LowParse_Low_BoundedInt.read_bounded_integer_4
                                 ()) () () input pos in
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
                                  else (Prims.of_int (4)))) uu___1 in
                      FStar_UInt32.add pos uu___
let (validate_bounded_vldata_strong' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              unit ->
                (unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt64.t -> FStar_UInt64.t)
                  ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun s ->
                fun v ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let h1 = FStar_HyperStack_ST.get () in
                          let h2 = FStar_HyperStack_ST.get () in
                          let res =
                            let h3 = FStar_HyperStack_ST.get () in
                            if
                              FStar_UInt64.lt
                                (FStar_UInt64.sub
                                   (FStar_Int_Cast.uint32_to_uint64
                                      (match input with
                                       | { LowParse_Slice.base = base;
                                           LowParse_Slice.len = len;_} -> len))
                                   pos) (FStar_UInt64.uint_to_t l)
                            then
                              LowParse_Low_ErrorCode.validator_error_not_enough_data
                            else
                              FStar_UInt64.add pos (FStar_UInt64.uint_to_t l) in
                          if LowParse_Low_ErrorCode.is_error res
                          then res
                          else
                            (let va =
                               (match l with
                                | uu___1 when uu___1 = Prims.int_one ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_1
                                      ()
                                | uu___1 when uu___1 = (Prims.of_int (2)) ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_2
                                      ()
                                | uu___1 when uu___1 = (Prims.of_int (3)) ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_3
                                      ()
                                | uu___1 when uu___1 = (Prims.of_int (4)) ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_4
                                      ()) () () input
                                 (FStar_Int_Cast.uint64_to_uint32 pos) in
                             if
                               (if min = Prims.int_zero
                                then
                                  FStar_UInt32.lte va
                                    (FStar_UInt32.uint_to_t max)
                                else
                                  (FStar_UInt32.lte
                                     (FStar_UInt32.uint_to_t min) va)
                                    &&
                                    (FStar_UInt32.lte va
                                       (FStar_UInt32.uint_to_t max)))
                             then
                               let h3 = FStar_HyperStack_ST.get () in
                               (if
                                  (match k with
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
                                    (FStar_Pervasives_Native.Some
                                       LowParse_Spec_Base.ParserConsumesAll)
                                then
                                  let h4 = FStar_HyperStack_ST.get () in
                                  (if
                                     FStar_UInt64.lt
                                       (FStar_UInt64.sub
                                          (FStar_Int_Cast.uint32_to_uint64
                                             (match input with
                                              | { LowParse_Slice.base = base;
                                                  LowParse_Slice.len = len;_}
                                                  -> len)) res)
                                       (FStar_Int_Cast.uint32_to_uint64 va)
                                   then
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                   else
                                     (let pos' =
                                        v () ()
                                          {
                                            LowParse_Slice.base =
                                              (match input with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len;_}
                                                   -> base);
                                            LowParse_Slice.len =
                                              (FStar_UInt32.add
                                                 (FStar_Int_Cast.uint64_to_uint32
                                                    res) va)
                                          } res in
                                      if LowParse_Low_ErrorCode.is_error pos'
                                      then
                                        (if
                                           pos' =
                                             LowParse_Low_ErrorCode.validator_error_not_enough_data
                                         then
                                           LowParse_Low_ErrorCode.validator_error_generic
                                         else pos')
                                      else pos'))
                                else
                                  (let h4 = FStar_HyperStack_ST.get () in
                                   if
                                     FStar_UInt64.lt
                                       (FStar_UInt64.sub
                                          (FStar_Int_Cast.uint32_to_uint64
                                             (match input with
                                              | { LowParse_Slice.base = base;
                                                  LowParse_Slice.len = len;_}
                                                  -> len)) res)
                                       (FStar_Int_Cast.uint32_to_uint64 va)
                                   then
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                   else
                                     (let pos' =
                                        v () ()
                                          {
                                            LowParse_Slice.base =
                                              (match input with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len;_}
                                                   -> base);
                                            LowParse_Slice.len =
                                              (FStar_UInt32.add
                                                 (FStar_Int_Cast.uint64_to_uint32
                                                    res) va)
                                          } res in
                                      if LowParse_Low_ErrorCode.is_error pos'
                                      then
                                        (if
                                           pos' =
                                             LowParse_Low_ErrorCode.validator_error_not_enough_data
                                         then
                                           LowParse_Low_ErrorCode.validator_error_generic
                                         else pos')
                                      else
                                        if
                                          (FStar_UInt64.sub pos' res) <>
                                            (FStar_Int_Cast.uint32_to_uint64
                                               va)
                                        then
                                          LowParse_Low_ErrorCode.validator_error_generic
                                        else pos')))
                             else
                               LowParse_Low_ErrorCode.validator_error_generic)
let (validate_bounded_vldata_strong :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
                ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun v ->
                fun u ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let h1 = FStar_HyperStack_ST.get () in
                          let h2 = FStar_HyperStack_ST.get () in
                          let res =
                            let h3 = FStar_HyperStack_ST.get () in
                            if
                              FStar_UInt64.lt
                                (FStar_UInt64.sub
                                   (FStar_Int_Cast.uint32_to_uint64
                                      (match input with
                                       | { LowParse_Slice.base = base;
                                           LowParse_Slice.len = len;_} -> len))
                                   pos)
                                (FStar_UInt64.uint_to_t
                                   (if max < (Prims.of_int (256))
                                    then Prims.int_one
                                    else
                                      if max < (Prims.parse_int "65536")
                                      then (Prims.of_int (2))
                                      else
                                        if max < (Prims.parse_int "16777216")
                                        then (Prims.of_int (3))
                                        else (Prims.of_int (4))))
                            then
                              LowParse_Low_ErrorCode.validator_error_not_enough_data
                            else
                              FStar_UInt64.add pos
                                (FStar_UInt64.uint_to_t
                                   (if max < (Prims.of_int (256))
                                    then Prims.int_one
                                    else
                                      if max < (Prims.parse_int "65536")
                                      then (Prims.of_int (2))
                                      else
                                        if max < (Prims.parse_int "16777216")
                                        then (Prims.of_int (3))
                                        else (Prims.of_int (4)))) in
                          if LowParse_Low_ErrorCode.is_error res
                          then res
                          else
                            (let va =
                               (match if max < (Prims.of_int (256))
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
                                | uu___1 when uu___1 = Prims.int_one ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_1
                                      ()
                                | uu___1 when uu___1 = (Prims.of_int (2)) ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_2
                                      ()
                                | uu___1 when uu___1 = (Prims.of_int (3)) ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_3
                                      ()
                                | uu___1 when uu___1 = (Prims.of_int (4)) ->
                                    LowParse_Low_BoundedInt.read_bounded_integer_4
                                      ()) () () input
                                 (FStar_Int_Cast.uint64_to_uint32 pos) in
                             if
                               (if min = Prims.int_zero
                                then
                                  FStar_UInt32.lte va
                                    (FStar_UInt32.uint_to_t max)
                                else
                                  (FStar_UInt32.lte
                                     (FStar_UInt32.uint_to_t min) va)
                                    &&
                                    (FStar_UInt32.lte va
                                       (FStar_UInt32.uint_to_t max)))
                             then
                               let h3 = FStar_HyperStack_ST.get () in
                               (if
                                  (match k with
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
                                    (FStar_Pervasives_Native.Some
                                       LowParse_Spec_Base.ParserConsumesAll)
                                then
                                  let h4 = FStar_HyperStack_ST.get () in
                                  (if
                                     FStar_UInt64.lt
                                       (FStar_UInt64.sub
                                          (FStar_Int_Cast.uint32_to_uint64
                                             (match input with
                                              | { LowParse_Slice.base = base;
                                                  LowParse_Slice.len = len;_}
                                                  -> len)) res)
                                       (FStar_Int_Cast.uint32_to_uint64 va)
                                   then
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                   else
                                     (let pos' =
                                        v () ()
                                          {
                                            LowParse_Slice.base =
                                              (match input with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len;_}
                                                   -> base);
                                            LowParse_Slice.len =
                                              (FStar_UInt32.add
                                                 (FStar_Int_Cast.uint64_to_uint32
                                                    res) va)
                                          } res in
                                      if LowParse_Low_ErrorCode.is_error pos'
                                      then
                                        (if
                                           pos' =
                                             LowParse_Low_ErrorCode.validator_error_not_enough_data
                                         then
                                           LowParse_Low_ErrorCode.validator_error_generic
                                         else pos')
                                      else pos'))
                                else
                                  (let h4 = FStar_HyperStack_ST.get () in
                                   if
                                     FStar_UInt64.lt
                                       (FStar_UInt64.sub
                                          (FStar_Int_Cast.uint32_to_uint64
                                             (match input with
                                              | { LowParse_Slice.base = base;
                                                  LowParse_Slice.len = len;_}
                                                  -> len)) res)
                                       (FStar_Int_Cast.uint32_to_uint64 va)
                                   then
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                   else
                                     (let pos' =
                                        v () ()
                                          {
                                            LowParse_Slice.base =
                                              (match input with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len;_}
                                                   -> base);
                                            LowParse_Slice.len =
                                              (FStar_UInt32.add
                                                 (FStar_Int_Cast.uint64_to_uint32
                                                    res) va)
                                          } res in
                                      if LowParse_Low_ErrorCode.is_error pos'
                                      then
                                        (if
                                           pos' =
                                             LowParse_Low_ErrorCode.validator_error_not_enough_data
                                         then
                                           LowParse_Low_ErrorCode.validator_error_generic
                                         else pos')
                                      else
                                        if
                                          (FStar_UInt64.sub pos' res) <>
                                            (FStar_Int_Cast.uint32_to_uint64
                                               va)
                                        then
                                          LowParse_Low_ErrorCode.validator_error_generic
                                        else pos')))
                             else
                               LowParse_Low_ErrorCode.validator_error_generic)
let (jump_bounded_vldata_strong' :
  Prims.nat ->
    Prims.nat ->
      Prims.nat ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun l ->
        fun k ->
          fun t ->
            fun p ->
              fun s ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let h1 = FStar_HyperStack_ST.get () in
                        let h2 = FStar_HyperStack_ST.get () in
                        let uu___ =
                          let uu___1 =
                            match l with
                            | uu___2 when uu___2 = Prims.int_one ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_1
                                   ()) () () input pos
                            | uu___2 when uu___2 = (Prims.of_int (2)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_2
                                   ()) () () input pos
                            | uu___2 when uu___2 = (Prims.of_int (3)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_3
                                   ()) () () input pos
                            | uu___2 when uu___2 = (Prims.of_int (4)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_4
                                   ()) () () input pos in
                          FStar_UInt32.add (FStar_UInt32.uint_to_t l) uu___1 in
                        FStar_UInt32.add pos uu___
let (jump_bounded_vldata_strong :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun u ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        let h1 = FStar_HyperStack_ST.get () in
                        let h2 = FStar_HyperStack_ST.get () in
                        let uu___ =
                          let uu___1 =
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
                            | uu___2 when uu___2 = Prims.int_one ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_1
                                   ()) () () input pos
                            | uu___2 when uu___2 = (Prims.of_int (2)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_2
                                   ()) () () input pos
                            | uu___2 when uu___2 = (Prims.of_int (3)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_3
                                   ()) () () input pos
                            | uu___2 when uu___2 = (Prims.of_int (4)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_4
                                   ()) () () input pos in
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
                                    else (Prims.of_int (4)))) uu___1 in
                        FStar_UInt32.add pos uu___

let (finalize_vldata_gen :
  LowParse_Spec_BoundedInt.integer_size ->
    unit ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun sz ->
    fun f ->
      fun k ->
        fun t ->
          fun p ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    fun pos' ->
                      let uu___ =
                        (match sz with
                         | uu___1 when uu___1 = Prims.int_one ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (2)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (3)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (4)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len))
                          (FStar_UInt32.sub pos'
                             (FStar_UInt32.add pos
                                (FStar_UInt32.uint_to_t sz))) () () input pos in
                      let h = FStar_HyperStack_ST.get () in ()






let (finalize_bounded_vldata_strong_exact :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      fun pos' ->
                        let h = FStar_HyperStack_ST.get () in
                        let uu___ =
                          (match if max < (Prims.of_int (256))
                                 then Prims.int_one
                                 else
                                   if max < (Prims.parse_int "65536")
                                   then (Prims.of_int (2))
                                   else
                                     if max < (Prims.parse_int "16777216")
                                     then (Prims.of_int (3))
                                     else (Prims.of_int (4))
                           with
                           | uu___1 when uu___1 = Prims.int_one ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h1 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len)
                           | uu___1 when uu___1 = (Prims.of_int (2)) ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h1 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len)
                           | uu___1 when uu___1 = (Prims.of_int (3)) ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h1 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len)
                           | uu___1 when uu___1 = (Prims.of_int (4)) ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h1 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len))
                            (FStar_UInt32.sub pos'
                               (FStar_UInt32.add pos
                                  (FStar_UInt32.uint_to_t
                                     (if max < (Prims.of_int (256))
                                      then Prims.int_one
                                      else
                                        if max < (Prims.parse_int "65536")
                                        then (Prims.of_int (2))
                                        else
                                          if
                                            max <
                                              (Prims.parse_int "16777216")
                                          then (Prims.of_int (3))
                                          else (Prims.of_int (4)))))) () ()
                            input pos in
                        let h1 = FStar_HyperStack_ST.get () in ()
let (finalize_bounded_vldata_strong :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      fun pos' ->
                        let h = FStar_HyperStack_ST.get () in
                        let h1 = FStar_HyperStack_ST.get () in
                        let uu___ =
                          (match if max < (Prims.of_int (256))
                                 then Prims.int_one
                                 else
                                   if max < (Prims.parse_int "65536")
                                   then (Prims.of_int (2))
                                   else
                                     if max < (Prims.parse_int "16777216")
                                     then (Prims.of_int (3))
                                     else (Prims.of_int (4))
                           with
                           | uu___1 when uu___1 = Prims.int_one ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h2 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len)
                           | uu___1 when uu___1 = (Prims.of_int (2)) ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h2 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len)
                           | uu___1 when uu___1 = (Prims.of_int (3)) ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h2 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len)
                           | uu___1 when uu___1 = (Prims.of_int (4)) ->
                               (fun x ->
                                  fun rrel1 ->
                                    fun rel1 ->
                                      fun input1 ->
                                        fun pos1 ->
                                          let h0 = FStar_HyperStack_ST.get () in
                                          let len =
                                            LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                              () x () ()
                                              (match input1 with
                                               | {
                                                   LowParse_Slice.base = base;
                                                   LowParse_Slice.len = len1;_}
                                                   -> base) pos1 in
                                          let h2 = FStar_HyperStack_ST.get () in
                                          FStar_UInt32.add pos1 len))
                            (FStar_UInt32.sub pos'
                               (FStar_UInt32.add pos
                                  (FStar_UInt32.uint_to_t
                                     (if max < (Prims.of_int (256))
                                      then Prims.int_one
                                      else
                                        if max < (Prims.parse_int "65536")
                                        then (Prims.of_int (2))
                                        else
                                          if
                                            max <
                                              (Prims.parse_int "16777216")
                                          then (Prims.of_int (3))
                                          else (Prims.of_int (4)))))) () ()
                            input pos in
                        let h2 = FStar_HyperStack_ST.get () in ()
let (finalize_bounded_vldata_exact :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    fun pos' ->
                      let h = FStar_HyperStack_ST.get () in
                      let uu___ =
                        (match if max < (Prims.of_int (256))
                               then Prims.int_one
                               else
                                 if max < (Prims.parse_int "65536")
                                 then (Prims.of_int (2))
                                 else
                                   if max < (Prims.parse_int "16777216")
                                   then (Prims.of_int (3))
                                   else (Prims.of_int (4))
                         with
                         | uu___1 when uu___1 = Prims.int_one ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (2)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (3)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (4)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len))
                          (FStar_UInt32.sub pos'
                             (FStar_UInt32.add pos
                                (FStar_UInt32.uint_to_t
                                   (if max < (Prims.of_int (256))
                                    then Prims.int_one
                                    else
                                      if max < (Prims.parse_int "65536")
                                      then (Prims.of_int (2))
                                      else
                                        if max < (Prims.parse_int "16777216")
                                        then (Prims.of_int (3))
                                        else (Prims.of_int (4)))))) () ()
                          input pos in
                      let h1 = FStar_HyperStack_ST.get () in ()
let (finalize_bounded_vldata :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    fun pos' ->
                      let h = FStar_HyperStack_ST.get () in
                      let uu___ =
                        (match if max < (Prims.of_int (256))
                               then Prims.int_one
                               else
                                 if max < (Prims.parse_int "65536")
                                 then (Prims.of_int (2))
                                 else
                                   if max < (Prims.parse_int "16777216")
                                   then (Prims.of_int (3))
                                   else (Prims.of_int (4))
                         with
                         | uu___1 when uu___1 = Prims.int_one ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (2)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (3)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len)
                         | uu___1 when uu___1 = (Prims.of_int (4)) ->
                             (fun x ->
                                fun rrel1 ->
                                  fun rel1 ->
                                    fun input1 ->
                                      fun pos1 ->
                                        let h0 = FStar_HyperStack_ST.get () in
                                        let len =
                                          LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                            () x () ()
                                            (match input1 with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len1;_}
                                                 -> base) pos1 in
                                        let h1 = FStar_HyperStack_ST.get () in
                                        FStar_UInt32.add pos1 len))
                          (FStar_UInt32.sub pos'
                             (FStar_UInt32.add pos
                                (FStar_UInt32.uint_to_t
                                   (if max < (Prims.of_int (256))
                                    then Prims.int_one
                                    else
                                      if max < (Prims.parse_int "65536")
                                      then (Prims.of_int (2))
                                      else
                                        if max < (Prims.parse_int "16777216")
                                        then (Prims.of_int (3))
                                        else (Prims.of_int (4)))))) () ()
                          input pos in
                      let h1 = FStar_HyperStack_ST.get () in ()
let (weak_finalize_bounded_vldata_strong_exact :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t -> Prims.bool)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      fun pos' ->
                        let len_payload =
                          FStar_UInt32.sub pos'
                            (FStar_UInt32.add pos
                               (FStar_UInt32.uint_to_t
                                  (if max < (Prims.of_int (256))
                                   then Prims.int_one
                                   else
                                     if max < (Prims.parse_int "65536")
                                     then (Prims.of_int (2))
                                     else
                                       if max < (Prims.parse_int "16777216")
                                       then (Prims.of_int (3))
                                       else (Prims.of_int (4))))) in
                        if
                          (FStar_UInt32.lt (FStar_UInt32.uint_to_t max)
                             len_payload)
                            ||
                            (FStar_UInt32.lt len_payload
                               (FStar_UInt32.uint_to_t min))
                        then false
                        else
                          ((let h = FStar_HyperStack_ST.get () in
                            let uu___2 =
                              (match if max < (Prims.of_int (256))
                                     then Prims.int_one
                                     else
                                       if max < (Prims.parse_int "65536")
                                       then (Prims.of_int (2))
                                       else
                                         if
                                           max < (Prims.parse_int "16777216")
                                         then (Prims.of_int (3))
                                         else (Prims.of_int (4))
                               with
                               | uu___3 when uu___3 = Prims.int_one ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h1 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len)
                               | uu___3 when uu___3 = (Prims.of_int (2)) ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h1 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len)
                               | uu___3 when uu___3 = (Prims.of_int (3)) ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h1 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len)
                               | uu___3 when uu___3 = (Prims.of_int (4)) ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h1 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len))
                                (FStar_UInt32.sub pos'
                                   (FStar_UInt32.add pos
                                      (FStar_UInt32.uint_to_t
                                         (if max < (Prims.of_int (256))
                                          then Prims.int_one
                                          else
                                            if
                                              max < (Prims.parse_int "65536")
                                            then (Prims.of_int (2))
                                            else
                                              if
                                                max <
                                                  (Prims.parse_int "16777216")
                                              then (Prims.of_int (3))
                                              else (Prims.of_int (4)))))) ()
                                () input pos in
                            let h1 = FStar_HyperStack_ST.get () in ());
                           true)
let (weak_finalize_bounded_vldata_strong :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t -> Prims.bool)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      fun pos' ->
                        let h = FStar_HyperStack_ST.get () in
                        let len_payload =
                          FStar_UInt32.sub pos'
                            (FStar_UInt32.add pos
                               (FStar_UInt32.uint_to_t
                                  (if max < (Prims.of_int (256))
                                   then Prims.int_one
                                   else
                                     if max < (Prims.parse_int "65536")
                                     then (Prims.of_int (2))
                                     else
                                       if max < (Prims.parse_int "16777216")
                                       then (Prims.of_int (3))
                                       else (Prims.of_int (4))))) in
                        if
                          (FStar_UInt32.lt (FStar_UInt32.uint_to_t max)
                             len_payload)
                            ||
                            (FStar_UInt32.lt len_payload
                               (FStar_UInt32.uint_to_t min))
                        then false
                        else
                          ((let h1 = FStar_HyperStack_ST.get () in
                            let uu___2 =
                              (match if max < (Prims.of_int (256))
                                     then Prims.int_one
                                     else
                                       if max < (Prims.parse_int "65536")
                                       then (Prims.of_int (2))
                                       else
                                         if
                                           max < (Prims.parse_int "16777216")
                                         then (Prims.of_int (3))
                                         else (Prims.of_int (4))
                               with
                               | uu___3 when uu___3 = Prims.int_one ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h2 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len)
                               | uu___3 when uu___3 = (Prims.of_int (2)) ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h2 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len)
                               | uu___3 when uu___3 = (Prims.of_int (3)) ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h2 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len)
                               | uu___3 when uu___3 = (Prims.of_int (4)) ->
                                   (fun x ->
                                      fun rrel1 ->
                                        fun rel1 ->
                                          fun input1 ->
                                            fun pos1 ->
                                              let h0 =
                                                FStar_HyperStack_ST.get () in
                                              let len =
                                                LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                                  () x () ()
                                                  (match input1 with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len1;_}
                                                       -> base) pos1 in
                                              let h2 =
                                                FStar_HyperStack_ST.get () in
                                              FStar_UInt32.add pos1 len))
                                (FStar_UInt32.sub pos'
                                   (FStar_UInt32.add pos
                                      (FStar_UInt32.uint_to_t
                                         (if max < (Prims.of_int (256))
                                          then Prims.int_one
                                          else
                                            if
                                              max < (Prims.parse_int "65536")
                                            then (Prims.of_int (2))
                                            else
                                              if
                                                max <
                                                  (Prims.parse_int "16777216")
                                              then (Prims.of_int (3))
                                              else (Prims.of_int (4)))))) ()
                                () input pos in
                            let h2 = FStar_HyperStack_ST.get () in ());
                           true)


let (accessor_bounded_vldata_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos
                      (FStar_UInt32.uint_to_t
                         (if max < (Prims.of_int (256))
                          then Prims.int_one
                          else
                            if max < (Prims.parse_int "65536")
                            then (Prims.of_int (2))
                            else
                              if max < (Prims.parse_int "16777216")
                              then (Prims.of_int (3))
                              else (Prims.of_int (4))))
let (clens_bounded_vldata_strong_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit -> unit -> unit -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              {
                LowParse_Low_Base_Spec.clens_cond = ();
                LowParse_Low_Base_Spec.clens_get = ()
              }


let (accessor_bounded_vldata_strong_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos
                        (FStar_UInt32.uint_to_t
                           (if max < (Prims.of_int (256))
                            then Prims.int_one
                            else
                              if max < (Prims.parse_int "65536")
                              then (Prims.of_int (2))
                              else
                                if max < (Prims.parse_int "16777216")
                                then (Prims.of_int (3))
                                else (Prims.of_int (4))))