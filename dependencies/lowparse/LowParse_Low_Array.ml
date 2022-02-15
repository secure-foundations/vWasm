open Prims

let clens_array_nth :
  't .
    Prims.nat ->
      Prims.nat -> ('t Prims.list, 't) LowParse_Low_Base_Spec.clens
  =
  fun elem_count ->
    fun i ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }





let (array_nth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          Prims.nat ->
            Prims.nat ->
              FStar_UInt32.t ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun array_byte_size ->
            fun elem_count ->
              fun i ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        FStar_UInt32.add pos
                          (FStar_UInt32.mul i
                             (FStar_UInt32.uint_to_t
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
                                     -> parser_kind_low)))




let (validate_array' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt64.t -> FStar_UInt64.t)
            ->
            Prims.nat ->
              FStar_UInt32.t ->
                Prims.nat ->
                  unit ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun v ->
            fun array_byte_size ->
              fun array_byte_size32 ->
                fun elem_count ->
                  fun u ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            let h1 = FStar_HyperStack_ST.get () in
                            let h2 = FStar_HyperStack_ST.get () in
                            if
                              FStar_UInt64.lt
                                (FStar_UInt64.sub
                                   (FStar_Int_Cast.uint32_to_uint64
                                      (match input with
                                       | { LowParse_Slice.base = base;
                                           LowParse_Slice.len = len;_} -> len))
                                   pos)
                                (FStar_Int_Cast.uint32_to_uint64
                                   array_byte_size32)
                            then
                              LowParse_Low_ErrorCode.validator_error_not_enough_data
                            else
                              (let pos' =
                                 let h3 = FStar_HyperStack_ST.get () in
                                 let h0 = FStar_HyperStack_ST.get () in
                                 FStar_HyperStack_ST.push_frame ();
                                 (let h02 = FStar_HyperStack_ST.get () in
                                  let bpos =
                                    LowStar_Monotonic_Buffer.malloca pos
                                      (FStar_UInt32.uint_to_t Prims.int_one) in
                                  let h11 = FStar_HyperStack_ST.get () in
                                  C_Loops.do_while
                                    (fun uu___3 ->
                                       let pos1 =
                                         LowStar_Monotonic_Buffer.index bpos
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero) in
                                       if
                                         pos1 =
                                           (FStar_Int_Cast.uint32_to_uint64
                                              (FStar_UInt32.add
                                                 (FStar_Int_Cast.uint64_to_uint32
                                                    pos) array_byte_size32))
                                       then true
                                       else
                                         (let pos11 =
                                            v () ()
                                              {
                                                LowParse_Slice.base =
                                                  (match input with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len;_}
                                                       -> base);
                                                LowParse_Slice.len =
                                                  (FStar_UInt32.add
                                                     (FStar_Int_Cast.uint64_to_uint32
                                                        pos)
                                                     array_byte_size32)
                                              } pos1 in
                                          (let h4 =
                                             FStar_HyperStack_ST.get () in
                                           LowStar_Monotonic_Buffer.upd' bpos
                                             (FStar_UInt32.uint_to_t
                                                Prims.int_zero) pos11);
                                          LowParse_Low_ErrorCode.is_error
                                            pos11));
                                  (let posf =
                                     LowStar_Monotonic_Buffer.index bpos
                                       (FStar_UInt32.uint_to_t Prims.int_zero) in
                                   FStar_HyperStack_ST.pop_frame (); posf)) in
                               if LowParse_Low_ErrorCode.is_error pos'
                               then
                                 (if
                                    pos' =
                                      LowParse_Low_ErrorCode.validator_error_not_enough_data
                                  then
                                    LowParse_Low_ErrorCode.validator_error_generic
                                  else pos')
                               else pos')
let (validate_array :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt64.t -> FStar_UInt64.t)
            ->
            Prims.nat ->
              FStar_UInt32.t ->
                Prims.nat ->
                  unit ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun v ->
            fun array_byte_size ->
              fun array_byte_size32 ->
                fun elem_count ->
                  fun u ->
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
                           -> parser_kind_metadata)
                        =
                        (FStar_Pervasives_Native.Some
                           LowParse_Spec_Base.ParserKindMetadataTotal)
                    then
                      fun rrel ->
                        fun rel ->
                          fun sl ->
                            fun pos ->
                              let h = FStar_HyperStack_ST.get () in
                              (if
                                 FStar_UInt64.lt
                                   (FStar_UInt64.sub
                                      (FStar_Int_Cast.uint32_to_uint64
                                         (match sl with
                                          | { LowParse_Slice.base = base;
                                              LowParse_Slice.len = len;_} ->
                                              len)) pos)
                                   (FStar_Int_Cast.uint32_to_uint64
                                      array_byte_size32)
                               then
                                 LowParse_Low_ErrorCode.validator_error_not_enough_data
                               else
                                 FStar_UInt64.add pos
                                   (FStar_Int_Cast.uint32_to_uint64
                                      array_byte_size32))
                    else
                      (fun rrel ->
                         fun rel ->
                           fun input ->
                             fun pos ->
                               let h = FStar_HyperStack_ST.get () in
                               let h1 = FStar_HyperStack_ST.get () in
                               let h2 = FStar_HyperStack_ST.get () in
                               if
                                 FStar_UInt64.lt
                                   (FStar_UInt64.sub
                                      (FStar_Int_Cast.uint32_to_uint64
                                         (match input with
                                          | { LowParse_Slice.base = base;
                                              LowParse_Slice.len = len;_} ->
                                              len)) pos)
                                   (FStar_Int_Cast.uint32_to_uint64
                                      array_byte_size32)
                               then
                                 LowParse_Low_ErrorCode.validator_error_not_enough_data
                               else
                                 (let pos' =
                                    let h3 = FStar_HyperStack_ST.get () in
                                    let h0 = FStar_HyperStack_ST.get () in
                                    FStar_HyperStack_ST.push_frame ();
                                    (let h02 = FStar_HyperStack_ST.get () in
                                     let bpos =
                                       LowStar_Monotonic_Buffer.malloca pos
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_one) in
                                     let h11 = FStar_HyperStack_ST.get () in
                                     C_Loops.do_while
                                       (fun uu___4 ->
                                          let pos1 =
                                            LowStar_Monotonic_Buffer.index
                                              bpos
                                              (FStar_UInt32.uint_to_t
                                                 Prims.int_zero) in
                                          if
                                            pos1 =
                                              (FStar_Int_Cast.uint32_to_uint64
                                                 (FStar_UInt32.add
                                                    (FStar_Int_Cast.uint64_to_uint32
                                                       pos) array_byte_size32))
                                          then true
                                          else
                                            (let pos11 =
                                               v () ()
                                                 {
                                                   LowParse_Slice.base =
                                                     (match input with
                                                      | {
                                                          LowParse_Slice.base
                                                            = base;
                                                          LowParse_Slice.len
                                                            = len;_}
                                                          -> base);
                                                   LowParse_Slice.len =
                                                     (FStar_UInt32.add
                                                        (FStar_Int_Cast.uint64_to_uint32
                                                           pos)
                                                        array_byte_size32)
                                                 } pos1 in
                                             (let h4 =
                                                FStar_HyperStack_ST.get () in
                                              LowStar_Monotonic_Buffer.upd'
                                                bpos
                                                (FStar_UInt32.uint_to_t
                                                   Prims.int_zero) pos11);
                                             LowParse_Low_ErrorCode.is_error
                                               pos11));
                                     (let posf =
                                        LowStar_Monotonic_Buffer.index bpos
                                          (FStar_UInt32.uint_to_t
                                             Prims.int_zero) in
                                      FStar_HyperStack_ST.pop_frame (); posf)) in
                                  if LowParse_Low_ErrorCode.is_error pos'
                                  then
                                    (if
                                       pos' =
                                         LowParse_Low_ErrorCode.validator_error_not_enough_data
                                     then
                                       LowParse_Low_ErrorCode.validator_error_generic
                                     else pos')
                                  else pos'))
let (jump_array :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          Prims.nat ->
            FStar_UInt32.t ->
              Prims.nat ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun array_byte_size ->
            fun array_byte_size32 ->
              fun elem_count ->
                fun u ->
                  fun rrel ->
                    fun rel ->
                      fun input ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          FStar_UInt32.add pos array_byte_size32
let (validate_vlarray :
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
                Prims.nat ->
                  Prims.nat ->
                    unit ->
                      FStar_UInt32.t ->
                        unit ->
                          unit ->
                            (Obj.t, Obj.t) LowParse_Slice.slice ->
                              FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun v ->
                fun elem_count_min ->
                  fun elem_count_max ->
                    fun u ->
                      fun sz32 ->
                        fun rrel ->
                          fun rel ->
                            fun input ->
                              fun pos ->
                                let h = FStar_HyperStack_ST.get () in
                                let h1 = FStar_HyperStack_ST.get () in
                                let h2 = FStar_HyperStack_ST.get () in
                                let h3 = FStar_HyperStack_ST.get () in
                                let res =
                                  let h4 = FStar_HyperStack_ST.get () in
                                  if
                                    FStar_UInt64.lt
                                      (FStar_UInt64.sub
                                         (FStar_Int_Cast.uint32_to_uint64
                                            (match input with
                                             | { LowParse_Slice.base = base;
                                                 LowParse_Slice.len = len;_}
                                                 -> len)) pos)
                                      (FStar_UInt64.uint_to_t
                                         (if
                                            array_byte_size_max <
                                              (Prims.of_int (256))
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
                                              else (Prims.of_int (4))))
                                  then
                                    LowParse_Low_ErrorCode.validator_error_not_enough_data
                                  else
                                    FStar_UInt64.add pos
                                      (FStar_UInt64.uint_to_t
                                         (if
                                            array_byte_size_max <
                                              (Prims.of_int (256))
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
                                              else (Prims.of_int (4)))) in
                                if LowParse_Low_ErrorCode.is_error res
                                then res
                                else
                                  (let va =
                                     (match if
                                              array_byte_size_max <
                                                (Prims.of_int (256))
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
                                      | uu___1 when uu___1 = Prims.int_one ->
                                          LowParse_Low_BoundedInt.read_bounded_integer_1
                                            ()
                                      | uu___1 when
                                          uu___1 = (Prims.of_int (2)) ->
                                          LowParse_Low_BoundedInt.read_bounded_integer_2
                                            ()
                                      | uu___1 when
                                          uu___1 = (Prims.of_int (3)) ->
                                          LowParse_Low_BoundedInt.read_bounded_integer_3
                                            ()
                                      | uu___1 when
                                          uu___1 = (Prims.of_int (4)) ->
                                          LowParse_Low_BoundedInt.read_bounded_integer_4
                                            ()) () () input
                                       (FStar_Int_Cast.uint64_to_uint32 pos) in
                                   if
                                     (if array_byte_size_min = Prims.int_zero
                                      then
                                        FStar_UInt32.lte va
                                          (FStar_UInt32.uint_to_t
                                             array_byte_size_max)
                                      else
                                        (FStar_UInt32.lte
                                           (FStar_UInt32.uint_to_t
                                              array_byte_size_min) va)
                                          &&
                                          (FStar_UInt32.lte va
                                             (FStar_UInt32.uint_to_t
                                                array_byte_size_max)))
                                   then
                                     let h4 = FStar_HyperStack_ST.get () in
                                     let h5 = FStar_HyperStack_ST.get () in
                                     (if
                                        FStar_UInt64.lt
                                          (FStar_UInt64.sub
                                             (FStar_Int_Cast.uint32_to_uint64
                                                (match input with
                                                 | {
                                                     LowParse_Slice.base =
                                                       base;
                                                     LowParse_Slice.len = len;_}
                                                     -> len)) res)
                                          (FStar_Int_Cast.uint32_to_uint64 va)
                                      then
                                        LowParse_Low_ErrorCode.validator_error_not_enough_data
                                      else
                                        (let pos' =
                                           let h6 =
                                             FStar_HyperStack_ST.get () in
                                           let h0 =
                                             FStar_HyperStack_ST.get () in
                                           FStar_HyperStack_ST.push_frame ();
                                           (let h02 =
                                              FStar_HyperStack_ST.get () in
                                            let bpos =
                                              LowStar_Monotonic_Buffer.malloca
                                                res
                                                (FStar_UInt32.uint_to_t
                                                   Prims.int_one) in
                                            let h11 =
                                              FStar_HyperStack_ST.get () in
                                            C_Loops.do_while
                                              (fun uu___4 ->
                                                 let pos1 =
                                                   LowStar_Monotonic_Buffer.index
                                                     bpos
                                                     (FStar_UInt32.uint_to_t
                                                        Prims.int_zero) in
                                                 if
                                                   pos1 =
                                                     (FStar_Int_Cast.uint32_to_uint64
                                                        (FStar_UInt32.add
                                                           (FStar_Int_Cast.uint64_to_uint32
                                                              res) va))
                                                 then true
                                                 else
                                                   (let pos11 =
                                                      v () ()
                                                        {
                                                          LowParse_Slice.base
                                                            =
                                                            (match input with
                                                             | {
                                                                 LowParse_Slice.base
                                                                   = base;
                                                                 LowParse_Slice.len
                                                                   = len;_}
                                                                 -> base);
                                                          LowParse_Slice.len
                                                            =
                                                            (FStar_UInt32.add
                                                               (FStar_Int_Cast.uint64_to_uint32
                                                                  res) va)
                                                        } pos1 in
                                                    (let h7 =
                                                       FStar_HyperStack_ST.get
                                                         () in
                                                     LowStar_Monotonic_Buffer.upd'
                                                       bpos
                                                       (FStar_UInt32.uint_to_t
                                                          Prims.int_zero)
                                                       pos11);
                                                    LowParse_Low_ErrorCode.is_error
                                                      pos11));
                                            (let posf =
                                               LowStar_Monotonic_Buffer.index
                                                 bpos
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_zero) in
                                             FStar_HyperStack_ST.pop_frame ();
                                             posf)) in
                                         if
                                           LowParse_Low_ErrorCode.is_error
                                             pos'
                                         then
                                           (if
                                              pos' =
                                                LowParse_Low_ErrorCode.validator_error_not_enough_data
                                            then
                                              LowParse_Low_ErrorCode.validator_error_generic
                                            else pos')
                                         else pos'))
                                   else
                                     LowParse_Low_ErrorCode.validator_error_generic)
let (jump_vlarray :
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
                      unit ->
                        unit ->
                          (Obj.t, Obj.t) LowParse_Slice.slice ->
                            FStar_UInt32.t -> FStar_UInt32.t)
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
                    fun sz32 ->
                      fun rrel ->
                        fun rel ->
                          fun input ->
                            fun pos ->
                              let h = FStar_HyperStack_ST.get () in
                              let h1 = FStar_HyperStack_ST.get () in
                              let h2 = FStar_HyperStack_ST.get () in
                              let h3 = FStar_HyperStack_ST.get () in
                              let uu___ =
                                let uu___1 =
                                  match if
                                          array_byte_size_max <
                                            (Prims.of_int (256))
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
                                  | uu___2 when uu___2 = Prims.int_one ->
                                      (LowParse_Low_BoundedInt.read_bounded_integer_1
                                         ()) () () input pos
                                  | uu___2 when uu___2 = (Prims.of_int (2))
                                      ->
                                      (LowParse_Low_BoundedInt.read_bounded_integer_2
                                         ()) () () input pos
                                  | uu___2 when uu___2 = (Prims.of_int (3))
                                      ->
                                      (LowParse_Low_BoundedInt.read_bounded_integer_3
                                         ()) () () input pos
                                  | uu___2 when uu___2 = (Prims.of_int (4))
                                      ->
                                      (LowParse_Low_BoundedInt.read_bounded_integer_4
                                         ()) () () input pos in
                                FStar_UInt32.add
                                  (FStar_UInt32.uint_to_t
                                     (if
                                        array_byte_size_max <
                                          (Prims.of_int (256))
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
                                          else (Prims.of_int (4)))) uu___1 in
                              FStar_UInt32.add pos uu___
let (finalize_vlarray :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t -> unit)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min ->
                fun elem_count_max ->
                  fun rrel ->
                    fun rel ->
                      fun sl ->
                        fun pos ->
                          fun pos' ->
                            let h = FStar_HyperStack_ST.get () in
                            let pos1 =
                              FStar_UInt32.add pos
                                (FStar_UInt32.uint_to_t
                                   (if
                                      array_byte_size_max <
                                        (Prims.of_int (256))
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
                                        else (Prims.of_int (4)))) in
                            (let h1 = FStar_HyperStack_ST.get () in
                             let uu___1 =
                               (match if
                                        array_byte_size_max <
                                          (Prims.of_int (256))
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
                                | uu___2 when uu___2 = Prims.int_one ->
                                    (fun x ->
                                       fun rrel1 ->
                                         fun rel1 ->
                                           fun input ->
                                             fun pos2 ->
                                               let h0 =
                                                 FStar_HyperStack_ST.get () in
                                               let len =
                                                 LowParse_Low_BoundedInt.serialize32_bounded_integer_1
                                                   () x () ()
                                                   (match input with
                                                    | {
                                                        LowParse_Slice.base =
                                                          base;
                                                        LowParse_Slice.len =
                                                          len1;_}
                                                        -> base) pos2 in
                                               let h2 =
                                                 FStar_HyperStack_ST.get () in
                                               FStar_UInt32.add pos2 len)
                                | uu___2 when uu___2 = (Prims.of_int (2)) ->
                                    (fun x ->
                                       fun rrel1 ->
                                         fun rel1 ->
                                           fun input ->
                                             fun pos2 ->
                                               let h0 =
                                                 FStar_HyperStack_ST.get () in
                                               let len =
                                                 LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                                                   () x () ()
                                                   (match input with
                                                    | {
                                                        LowParse_Slice.base =
                                                          base;
                                                        LowParse_Slice.len =
                                                          len1;_}
                                                        -> base) pos2 in
                                               let h2 =
                                                 FStar_HyperStack_ST.get () in
                                               FStar_UInt32.add pos2 len)
                                | uu___2 when uu___2 = (Prims.of_int (3)) ->
                                    (fun x ->
                                       fun rrel1 ->
                                         fun rel1 ->
                                           fun input ->
                                             fun pos2 ->
                                               let h0 =
                                                 FStar_HyperStack_ST.get () in
                                               let len =
                                                 LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                                   () x () ()
                                                   (match input with
                                                    | {
                                                        LowParse_Slice.base =
                                                          base;
                                                        LowParse_Slice.len =
                                                          len1;_}
                                                        -> base) pos2 in
                                               let h2 =
                                                 FStar_HyperStack_ST.get () in
                                               FStar_UInt32.add pos2 len)
                                | uu___2 when uu___2 = (Prims.of_int (4)) ->
                                    (fun x ->
                                       fun rrel1 ->
                                         fun rel1 ->
                                           fun input ->
                                             fun pos2 ->
                                               let h0 =
                                                 FStar_HyperStack_ST.get () in
                                               let len =
                                                 LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                                   () x () ()
                                                   (match input with
                                                    | {
                                                        LowParse_Slice.base =
                                                          base;
                                                        LowParse_Slice.len =
                                                          len1;_}
                                                        -> base) pos2 in
                                               let h2 =
                                                 FStar_HyperStack_ST.get () in
                                               FStar_UInt32.add pos2 len))
                                 (FStar_UInt32.sub pos'
                                    (FStar_UInt32.add pos
                                       (FStar_UInt32.uint_to_t
                                          (if
                                             array_byte_size_max <
                                               (Prims.of_int (256))
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
                                               else (Prims.of_int (4)))))) ()
                                 () sl pos in
                             let h2 = FStar_HyperStack_ST.get () in ());
                            (let h1 = FStar_HyperStack_ST.get () in ())
let clens_vlarray_nth :
  't .
    Prims.nat ->
      Prims.nat ->
        Prims.nat -> ('t Prims.list, 't) LowParse_Low_Base_Spec.clens
  =
  fun min ->
    fun max ->
      fun i ->
        {
          LowParse_Low_Base_Spec.clens_cond = ();
          LowParse_Low_Base_Spec.clens_get = ()
        }
let (vlarray_list_length :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat ->
                  unit ->
                    unit ->
                      (Obj.t, Obj.t) LowParse_Slice.slice ->
                        FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min ->
                fun elem_count_max ->
                  fun rrel ->
                    fun rel ->
                      fun sl ->
                        fun pos ->
                          let h = FStar_HyperStack_ST.get () in
                          let blen =
                            match if
                                    array_byte_size_max <
                                      (Prims.of_int (256))
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
                                (LowParse_Low_BoundedInt.read_bounded_integer_1
                                   ()) () () sl pos
                            | uu___ when uu___ = (Prims.of_int (2)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_2
                                   ()) () () sl pos
                            | uu___ when uu___ = (Prims.of_int (3)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_3
                                   ()) () () sl pos
                            | uu___ when uu___ = (Prims.of_int (4)) ->
                                (LowParse_Low_BoundedInt.read_bounded_integer_4
                                   ()) () () sl pos in
                          FStar_UInt32.div blen
                            (FStar_UInt32.uint_to_t
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
                                    -> parser_kind_low))


let (vlarray_nth_compute :
  Prims.nat -> FStar_UInt32.t -> FStar_UInt32.t -> unit -> FStar_UInt32.t) =
  fun a ->
    fun b ->
      fun c ->
        fun bound ->
          FStar_UInt32.add (FStar_UInt32.uint_to_t a) (FStar_UInt32.mul b c)
let (vlarray_nth_body :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat -> FStar_UInt32.t -> unit -> FStar_UInt32.t)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min ->
                fun elem_count_max ->
                  fun i ->
                    fun input ->
                      FStar_UInt32.add
                        (FStar_UInt32.uint_to_t
                           (if array_byte_size_max < (Prims.of_int (256))
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
                                else (Prims.of_int (4))))
                        (FStar_UInt32.mul i
                           (FStar_UInt32.uint_to_t
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
                                   -> parser_kind_low)))





let (vlarray_nth :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            unit ->
              Prims.nat ->
                Prims.nat ->
                  FStar_UInt32.t ->
                    unit ->
                      unit ->
                        (Obj.t, Obj.t) LowParse_Slice.slice ->
                          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun array_byte_size_min ->
    fun array_byte_size_max ->
      fun k ->
        fun t ->
          fun p ->
            fun s ->
              fun elem_count_min ->
                fun elem_count_max ->
                  fun i ->
                    fun rrel ->
                      fun rel ->
                        fun sl ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            FStar_UInt32.add pos
                              (FStar_UInt32.add
                                 (FStar_UInt32.uint_to_t
                                    (if
                                       array_byte_size_max <
                                         (Prims.of_int (256))
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
                                         else (Prims.of_int (4))))
                                 (FStar_UInt32.mul i
                                    (FStar_UInt32.uint_to_t
                                       (match k with
                                        | {
                                            LowParse_Spec_Base.parser_kind_low
                                              = parser_kind_low;
                                            LowParse_Spec_Base.parser_kind_high
                                              = parser_kind_high;
                                            LowParse_Spec_Base.parser_kind_subkind
                                              = parser_kind_subkind;
                                            LowParse_Spec_Base.parser_kind_metadata
                                              = parser_kind_metadata;_}
                                            -> parser_kind_low))))

let (bounded_vldata_strong_list_payload_size :
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
                      let pos' =
                        let h1 = FStar_HyperStack_ST.get () in
                        let h2 = FStar_HyperStack_ST.get () in
                        let h3 = FStar_HyperStack_ST.get () in
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
                        FStar_UInt32.add pos uu___ in
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
                                   else (Prims.of_int (4)))))
let (finalize_bounded_vldata_strong_list :
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