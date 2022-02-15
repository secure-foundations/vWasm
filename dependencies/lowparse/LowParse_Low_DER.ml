open Prims
let (validate_der_length_payload32 :
  FStar_UInt8.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun x ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            if FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
            then pos
            else
              if
                (x = (FStar_UInt8.uint_to_t (Prims.of_int (128)))) ||
                  (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
              then LowParse_Low_ErrorCode.validator_error_generic
              else
                if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                then
                  (let v =
                     let h1 = FStar_HyperStack_ST.get () in
                     if
                       FStar_UInt64.lt
                         (FStar_UInt64.sub
                            (FStar_Int_Cast.uint32_to_uint64
                               (match input with
                                | { LowParse_Slice.base = base;
                                    LowParse_Slice.len = len;_} -> len)) pos)
                         (FStar_UInt64.uint_to_t Prims.int_one)
                     then
                       LowParse_Low_ErrorCode.validator_error_not_enough_data
                     else
                       FStar_UInt64.add pos
                         (FStar_UInt64.uint_to_t Prims.int_one) in
                   if LowParse_Low_ErrorCode.is_error v
                   then v
                   else
                     (let z =
                        LowParse_Low_Int.read_u8 () () input
                          (FStar_Int_Cast.uint64_to_uint32 pos) in
                      if
                        FStar_UInt8.lt z
                          (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                      then LowParse_Low_ErrorCode.validator_error_generic
                      else v))
                else
                  (let len =
                     FStar_UInt8.sub x
                       (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                   if len = (FStar_UInt8.uint_to_t (Prims.of_int (2)))
                   then
                     let v =
                       let h1 = FStar_HyperStack_ST.get () in
                       if
                         FStar_UInt64.lt
                           (FStar_UInt64.sub
                              (FStar_Int_Cast.uint32_to_uint64
                                 (match input with
                                  | { LowParse_Slice.base = base;
                                      LowParse_Slice.len = len1;_} -> len1))
                              pos)
                           (FStar_UInt64.uint_to_t (Prims.of_int (2)))
                       then
                         LowParse_Low_ErrorCode.validator_error_not_enough_data
                       else
                         FStar_UInt64.add pos
                           (FStar_UInt64.uint_to_t (Prims.of_int (2))) in
                     (if LowParse_Low_ErrorCode.is_error v
                      then v
                      else
                        (let y =
                           LowParse_Low_BoundedInt.read_bounded_integer_2 ()
                             () () input
                             (FStar_Int_Cast.uint64_to_uint32 pos) in
                         if
                           FStar_UInt32.lt y
                             (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                         then LowParse_Low_ErrorCode.validator_error_generic
                         else v))
                   else
                     if len = (FStar_UInt8.uint_to_t (Prims.of_int (3)))
                     then
                       (let v =
                          let h1 = FStar_HyperStack_ST.get () in
                          if
                            FStar_UInt64.lt
                              (FStar_UInt64.sub
                                 (FStar_Int_Cast.uint32_to_uint64
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len1;_} -> len1))
                                 pos)
                              (FStar_UInt64.uint_to_t (Prims.of_int (3)))
                          then
                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                          else
                            FStar_UInt64.add pos
                              (FStar_UInt64.uint_to_t (Prims.of_int (3))) in
                        if LowParse_Low_ErrorCode.is_error v
                        then v
                        else
                          (let y =
                             LowParse_Low_BoundedInt.read_bounded_integer_3
                               () () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           if
                             FStar_UInt32.lt y
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "65536"))
                           then
                             LowParse_Low_ErrorCode.validator_error_generic
                           else v))
                     else
                       (let v =
                          let h1 = FStar_HyperStack_ST.get () in
                          if
                            FStar_UInt64.lt
                              (FStar_UInt64.sub
                                 (FStar_Int_Cast.uint32_to_uint64
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len1;_} -> len1))
                                 pos)
                              (FStar_UInt64.uint_to_t (Prims.of_int (4)))
                          then
                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                          else
                            FStar_UInt64.add pos
                              (FStar_UInt64.uint_to_t (Prims.of_int (4))) in
                        if LowParse_Low_ErrorCode.is_error v
                        then v
                        else
                          (let y =
                             LowParse_Low_BoundedInt.read_bounded_integer_4
                               () () () input
                               (FStar_Int_Cast.uint64_to_uint32 pos) in
                           if
                             FStar_UInt32.lt y
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "16777216"))
                           then
                             LowParse_Low_ErrorCode.validator_error_generic
                           else v)))
let (jump_der_length_payload32 :
  FStar_UInt8.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            if FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
            then pos
            else
              FStar_UInt32.add pos
                (FStar_Int_Cast.uint8_to_uint32
                   (FStar_UInt8.sub x
                      (FStar_UInt8.uint_to_t (Prims.of_int (128)))))
let (read_der_length_payload32 :
  FStar_UInt8.t ->
    unit ->
      unit ->
        (Obj.t, Obj.t) LowParse_Slice.slice ->
          FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun x ->
    fun rrel ->
      fun rel ->
        fun input ->
          fun pos ->
            let h = FStar_HyperStack_ST.get () in
            if FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
            then FStar_Int_Cast.uint8_to_uint32 x
            else
              if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
              then
                (let z = LowParse_Low_Int.read_u8 () () input pos in
                 FStar_Int_Cast.uint8_to_uint32 z)
              else
                (let len =
                   FStar_UInt8.sub x
                     (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                 if len = (FStar_UInt8.uint_to_t (Prims.of_int (2)))
                 then
                   let res =
                     LowParse_Low_BoundedInt.read_bounded_integer_2 () () ()
                       input pos in
                   res
                 else
                   if len = (FStar_UInt8.uint_to_t (Prims.of_int (3)))
                   then
                     (let res =
                        LowParse_Low_BoundedInt.read_bounded_integer_3 () ()
                          () input pos in
                      res)
                   else
                     (let res =
                        LowParse_Low_BoundedInt.read_bounded_integer_4 () ()
                          () input pos in
                      res))
let (validate_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    FStar_UInt32.t ->
      LowParse_Spec_DER.der_length_t ->
        FStar_UInt32.t ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let v =
                    let h1 = FStar_HyperStack_ST.get () in
                    if
                      FStar_UInt64.lt
                        (FStar_UInt64.sub
                           (FStar_Int_Cast.uint32_to_uint64
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len;_} -> len)) pos)
                        (FStar_UInt64.uint_to_t Prims.int_one)
                    then
                      LowParse_Low_ErrorCode.validator_error_not_enough_data
                    else
                      FStar_UInt64.add pos
                        (FStar_UInt64.uint_to_t Prims.int_one) in
                  if LowParse_Low_ErrorCode.is_error v
                  then v
                  else
                    (let x =
                       LowParse_Low_Int.read_u8 () () input
                         (FStar_Int_Cast.uint64_to_uint32 pos) in
                     let len =
                       if
                         (FStar_UInt8.lt x
                            (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                           ||
                           (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
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
                            (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                            len_len) in
                     let l1 =
                       if
                         (FStar_UInt8.lt tg1
                            (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                           ||
                           (tg1 =
                              (FStar_UInt8.uint_to_t (Prims.of_int (255))))
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
                            (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                            len_len) in
                     let l2 =
                       if
                         (FStar_UInt8.lt tg2
                            (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                           ||
                           (tg2 =
                              (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                       then FStar_UInt8.uint_to_t Prims.int_zero
                       else
                         FStar_UInt8.sub tg2
                           (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                     if (FStar_UInt8.lt len l1) || (FStar_UInt8.lt l2 len)
                     then LowParse_Low_ErrorCode.validator_error_generic
                     else
                       (let v2 =
                          let h1 = FStar_HyperStack_ST.get () in
                          if
                            FStar_UInt8.lt x
                              (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                          then v
                          else
                            if
                              (x =
                                 (FStar_UInt8.uint_to_t (Prims.of_int (128))))
                                ||
                                (x =
                                   (FStar_UInt8.uint_to_t
                                      (Prims.of_int (255))))
                            then
                              LowParse_Low_ErrorCode.validator_error_generic
                            else
                              if
                                x =
                                  (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                              then
                                (let v1 =
                                   let h2 = FStar_HyperStack_ST.get () in
                                   if
                                     FStar_UInt64.lt
                                       (FStar_UInt64.sub
                                          (FStar_Int_Cast.uint32_to_uint64
                                             (match input with
                                              | { LowParse_Slice.base = base;
                                                  LowParse_Slice.len = len1;_}
                                                  -> len1)) v)
                                       (FStar_UInt64.uint_to_t Prims.int_one)
                                   then
                                     LowParse_Low_ErrorCode.validator_error_not_enough_data
                                   else
                                     FStar_UInt64.add v
                                       (FStar_UInt64.uint_to_t Prims.int_one) in
                                 if LowParse_Low_ErrorCode.is_error v1
                                 then v1
                                 else
                                   (let z =
                                      LowParse_Low_Int.read_u8 () () input
                                        (FStar_Int_Cast.uint64_to_uint32 v) in
                                    if
                                      FStar_UInt8.lt z
                                        (FStar_UInt8.uint_to_t
                                           (Prims.of_int (128)))
                                    then
                                      LowParse_Low_ErrorCode.validator_error_generic
                                    else v1))
                              else
                                (let len1 =
                                   FStar_UInt8.sub x
                                     (FStar_UInt8.uint_to_t
                                        (Prims.of_int (128))) in
                                 if
                                   len1 =
                                     (FStar_UInt8.uint_to_t
                                        (Prims.of_int (2)))
                                 then
                                   let v1 =
                                     let h2 = FStar_HyperStack_ST.get () in
                                     if
                                       FStar_UInt64.lt
                                         (FStar_UInt64.sub
                                            (FStar_Int_Cast.uint32_to_uint64
                                               (match input with
                                                | {
                                                    LowParse_Slice.base =
                                                      base;
                                                    LowParse_Slice.len = len2;_}
                                                    -> len2)) v)
                                         (FStar_UInt64.uint_to_t
                                            (Prims.of_int (2)))
                                     then
                                       LowParse_Low_ErrorCode.validator_error_not_enough_data
                                     else
                                       FStar_UInt64.add v
                                         (FStar_UInt64.uint_to_t
                                            (Prims.of_int (2))) in
                                   (if LowParse_Low_ErrorCode.is_error v1
                                    then v1
                                    else
                                      (let y =
                                         LowParse_Low_BoundedInt.read_bounded_integer_2
                                           () () () input
                                           (FStar_Int_Cast.uint64_to_uint32 v) in
                                       if
                                         FStar_UInt32.lt y
                                           (FStar_UInt32.uint_to_t
                                              (Prims.of_int (256)))
                                       then
                                         LowParse_Low_ErrorCode.validator_error_generic
                                       else v1))
                                 else
                                   if
                                     len1 =
                                       (FStar_UInt8.uint_to_t
                                          (Prims.of_int (3)))
                                   then
                                     (let v1 =
                                        let h2 = FStar_HyperStack_ST.get () in
                                        if
                                          FStar_UInt64.lt
                                            (FStar_UInt64.sub
                                               (FStar_Int_Cast.uint32_to_uint64
                                                  (match input with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len2;_}
                                                       -> len2)) v)
                                            (FStar_UInt64.uint_to_t
                                               (Prims.of_int (3)))
                                        then
                                          LowParse_Low_ErrorCode.validator_error_not_enough_data
                                        else
                                          FStar_UInt64.add v
                                            (FStar_UInt64.uint_to_t
                                               (Prims.of_int (3))) in
                                      if LowParse_Low_ErrorCode.is_error v1
                                      then v1
                                      else
                                        (let y =
                                           LowParse_Low_BoundedInt.read_bounded_integer_3
                                             () () () input
                                             (FStar_Int_Cast.uint64_to_uint32
                                                v) in
                                         if
                                           FStar_UInt32.lt y
                                             (FStar_UInt32.uint_to_t
                                                (Prims.parse_int "65536"))
                                         then
                                           LowParse_Low_ErrorCode.validator_error_generic
                                         else v1))
                                   else
                                     (let v1 =
                                        let h2 = FStar_HyperStack_ST.get () in
                                        if
                                          FStar_UInt64.lt
                                            (FStar_UInt64.sub
                                               (FStar_Int_Cast.uint32_to_uint64
                                                  (match input with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len2;_}
                                                       -> len2)) v)
                                            (FStar_UInt64.uint_to_t
                                               (Prims.of_int (4)))
                                        then
                                          LowParse_Low_ErrorCode.validator_error_not_enough_data
                                        else
                                          FStar_UInt64.add v
                                            (FStar_UInt64.uint_to_t
                                               (Prims.of_int (4))) in
                                      if LowParse_Low_ErrorCode.is_error v1
                                      then v1
                                      else
                                        (let y =
                                           LowParse_Low_BoundedInt.read_bounded_integer_4
                                             () () () input
                                             (FStar_Int_Cast.uint64_to_uint32
                                                v) in
                                         if
                                           FStar_UInt32.lt y
                                             (FStar_UInt32.uint_to_t
                                                (Prims.parse_int "16777216"))
                                         then
                                           LowParse_Low_ErrorCode.validator_error_generic
                                         else v1))) in
                        if LowParse_Low_ErrorCode.is_error v2
                        then v2
                        else
                          (let y =
                             let h1 = FStar_HyperStack_ST.get () in
                             if
                               FStar_UInt8.lt x
                                 (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                             then FStar_Int_Cast.uint8_to_uint32 x
                             else
                               if
                                 x =
                                   (FStar_UInt8.uint_to_t
                                      (Prims.of_int (129)))
                               then
                                 (let z =
                                    LowParse_Low_Int.read_u8 () () input
                                      (FStar_Int_Cast.uint64_to_uint32 v) in
                                  FStar_Int_Cast.uint8_to_uint32 z)
                               else
                                 (let len1 =
                                    FStar_UInt8.sub x
                                      (FStar_UInt8.uint_to_t
                                         (Prims.of_int (128))) in
                                  if
                                    len1 =
                                      (FStar_UInt8.uint_to_t
                                         (Prims.of_int (2)))
                                  then
                                    let res =
                                      LowParse_Low_BoundedInt.read_bounded_integer_2
                                        () () () input
                                        (FStar_Int_Cast.uint64_to_uint32 v) in
                                    res
                                  else
                                    if
                                      len1 =
                                        (FStar_UInt8.uint_to_t
                                           (Prims.of_int (3)))
                                    then
                                      (let res =
                                         LowParse_Low_BoundedInt.read_bounded_integer_3
                                           () () () input
                                           (FStar_Int_Cast.uint64_to_uint32 v) in
                                       res)
                                    else
                                      (let res =
                                         LowParse_Low_BoundedInt.read_bounded_integer_4
                                           () () () input
                                           (FStar_Int_Cast.uint64_to_uint32 v) in
                                       res)) in
                           if
                             (FStar_UInt32.lt y min) ||
                               (FStar_UInt32.lt max y)
                           then
                             LowParse_Low_ErrorCode.validator_error_generic
                           else v2)))
let (jump_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let v =
                let h1 = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one) in
              let x = LowParse_Low_Int.read_u8 () () input pos in
              let len =
                if
                  (FStar_UInt8.lt x
                     (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                    || (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                then FStar_UInt8.uint_to_t Prims.int_zero
                else
                  FStar_UInt8.sub x
                    (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
              let h1 = FStar_HyperStack_ST.get () in
              if
                FStar_UInt8.lt x (FStar_UInt8.uint_to_t (Prims.of_int (128)))
              then v
              else
                FStar_UInt32.add v
                  (FStar_Int_Cast.uint8_to_uint32
                     (FStar_UInt8.sub x
                        (FStar_UInt8.uint_to_t (Prims.of_int (128)))))
let (read_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun rrel ->
        fun rel ->
          fun input ->
            fun pos ->
              let h = FStar_HyperStack_ST.get () in
              let v =
                let h1 = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos (FStar_UInt32.uint_to_t Prims.int_one) in
              let x = LowParse_Low_Int.read_u8 () () input pos in
              let len =
                if
                  (FStar_UInt8.lt x
                     (FStar_UInt8.uint_to_t (Prims.of_int (129))))
                    || (x = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
                then FStar_UInt8.uint_to_t Prims.int_zero
                else
                  FStar_UInt8.sub x
                    (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
              let y =
                let h1 = FStar_HyperStack_ST.get () in
                if
                  FStar_UInt8.lt x
                    (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                then FStar_Int_Cast.uint8_to_uint32 x
                else
                  if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                  then
                    (let z = LowParse_Low_Int.read_u8 () () input v in
                     FStar_Int_Cast.uint8_to_uint32 z)
                  else
                    (let len1 =
                       FStar_UInt8.sub x
                         (FStar_UInt8.uint_to_t (Prims.of_int (128))) in
                     if len1 = (FStar_UInt8.uint_to_t (Prims.of_int (2)))
                     then
                       let res =
                         LowParse_Low_BoundedInt.read_bounded_integer_2 () ()
                           () input v in
                       res
                     else
                       if len1 = (FStar_UInt8.uint_to_t (Prims.of_int (3)))
                       then
                         (let res =
                            LowParse_Low_BoundedInt.read_bounded_integer_3 ()
                              () () input v in
                          res)
                       else
                         (let res =
                            LowParse_Low_BoundedInt.read_bounded_integer_4 ()
                              () () input v in
                          res)) in
              y
let (serialize32_bounded_der_length32' :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (FStar_UInt8.t, Obj.t, Obj.t) LowStar_Monotonic_Buffer.mbuffer ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun y' ->
        fun rrel ->
          fun rel ->
            fun b ->
              fun pos ->
                let x =
                  if
                    FStar_UInt32.lt y'
                      (FStar_UInt32.uint_to_t (Prims.of_int (128)))
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
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "65536"))
                         then FStar_UInt8.uint_to_t (Prims.of_int (2))
                         else
                           if
                             FStar_UInt32.lt y'
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "16777216"))
                           then FStar_UInt8.uint_to_t (Prims.of_int (3))
                           else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
                     FStar_UInt8.add
                       (FStar_UInt8.uint_to_t (Prims.of_int (128))) len_len) in
                if
                  FStar_UInt8.lt x
                    (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                then
                  ((let h = FStar_HyperStack_ST.get () in
                    LowStar_Monotonic_Buffer.upd' b pos x);
                   FStar_UInt32.uint_to_t Prims.int_one)
                else
                  if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                  then
                    ((let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' b pos x);
                     (let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' b
                        (FStar_UInt32.add pos
                           (FStar_UInt32.uint_to_t Prims.int_one))
                        (FStar_Int_Cast.uint32_to_uint8 y'));
                     FStar_UInt32.uint_to_t (Prims.of_int (2)))
                  else
                    if x = (FStar_UInt8.uint_to_t (Prims.of_int (130)))
                    then
                      ((let h = FStar_HyperStack_ST.get () in
                        LowStar_Monotonic_Buffer.upd' b pos x);
                       (let h = FStar_HyperStack_ST.get () in
                        let z =
                          LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                            () y' () () b
                            (FStar_UInt32.add pos
                               (FStar_UInt32.uint_to_t Prims.int_one)) in
                        let h' = FStar_HyperStack_ST.get () in
                        FStar_UInt32.uint_to_t (Prims.of_int (3))))
                    else
                      if x = (FStar_UInt8.uint_to_t (Prims.of_int (131)))
                      then
                        ((let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd' b pos x);
                         (let h = FStar_HyperStack_ST.get () in
                          let z =
                            LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                              () y' () () b
                              (FStar_UInt32.add pos
                                 (FStar_UInt32.uint_to_t Prims.int_one)) in
                          let h' = FStar_HyperStack_ST.get () in
                          FStar_UInt32.uint_to_t (Prims.of_int (4))))
                      else
                        ((let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd' b pos x);
                         (let h = FStar_HyperStack_ST.get () in
                          let z =
                            LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                              () y' () () b
                              (FStar_UInt32.add pos
                                 (FStar_UInt32.uint_to_t Prims.int_one)) in
                          let h' = FStar_HyperStack_ST.get () in
                          FStar_UInt32.uint_to_t (Prims.of_int (5))))
let (serialize32_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (LowParse_Bytes.byte, Obj.t, Obj.t)
              LowStar_Monotonic_Buffer.mbuffer ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun y' ->
        fun rrel ->
          fun rel ->
            fun b ->
              fun pos ->
                let x =
                  if
                    FStar_UInt32.lt y'
                      (FStar_UInt32.uint_to_t (Prims.of_int (128)))
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
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "65536"))
                         then FStar_UInt8.uint_to_t (Prims.of_int (2))
                         else
                           if
                             FStar_UInt32.lt y'
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "16777216"))
                           then FStar_UInt8.uint_to_t (Prims.of_int (3))
                           else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
                     FStar_UInt8.add
                       (FStar_UInt8.uint_to_t (Prims.of_int (128))) len_len) in
                if
                  FStar_UInt8.lt x
                    (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                then
                  ((let h = FStar_HyperStack_ST.get () in
                    LowStar_Monotonic_Buffer.upd' b pos x);
                   FStar_UInt32.uint_to_t Prims.int_one)
                else
                  if x = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                  then
                    ((let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' b pos x);
                     (let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd' b
                        (FStar_UInt32.add pos
                           (FStar_UInt32.uint_to_t Prims.int_one))
                        (FStar_Int_Cast.uint32_to_uint8 y'));
                     FStar_UInt32.uint_to_t (Prims.of_int (2)))
                  else
                    if x = (FStar_UInt8.uint_to_t (Prims.of_int (130)))
                    then
                      ((let h = FStar_HyperStack_ST.get () in
                        LowStar_Monotonic_Buffer.upd' b pos x);
                       (let h = FStar_HyperStack_ST.get () in
                        let z =
                          LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                            () y' () () b
                            (FStar_UInt32.add pos
                               (FStar_UInt32.uint_to_t Prims.int_one)) in
                        let h' = FStar_HyperStack_ST.get () in
                        FStar_UInt32.uint_to_t (Prims.of_int (3))))
                    else
                      if x = (FStar_UInt8.uint_to_t (Prims.of_int (131)))
                      then
                        ((let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd' b pos x);
                         (let h = FStar_HyperStack_ST.get () in
                          let z =
                            LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                              () y' () () b
                              (FStar_UInt32.add pos
                                 (FStar_UInt32.uint_to_t Prims.int_one)) in
                          let h' = FStar_HyperStack_ST.get () in
                          FStar_UInt32.uint_to_t (Prims.of_int (4))))
                      else
                        ((let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd' b pos x);
                         (let h = FStar_HyperStack_ST.get () in
                          let z =
                            LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                              () y' () () b
                              (FStar_UInt32.add pos
                                 (FStar_UInt32.uint_to_t Prims.int_one)) in
                          let h' = FStar_HyperStack_ST.get () in
                          FStar_UInt32.uint_to_t (Prims.of_int (5))))
let (write_bounded_der_length32 :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      FStar_UInt32.t ->
        unit ->
          unit ->
            (Obj.t, Obj.t) LowParse_Slice.slice ->
              FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun x ->
        fun rrel ->
          fun rel ->
            fun input ->
              fun pos ->
                let h0 = FStar_HyperStack_ST.get () in
                let len =
                  let x1 =
                    if
                      FStar_UInt32.lt x
                        (FStar_UInt32.uint_to_t (Prims.of_int (128)))
                    then FStar_Int_Cast.uint32_to_uint8 x
                    else
                      (let len_len =
                         if
                           FStar_UInt32.lt x
                             (FStar_UInt32.uint_to_t (Prims.of_int (256)))
                         then FStar_UInt8.uint_to_t Prims.int_one
                         else
                           if
                             FStar_UInt32.lt x
                               (FStar_UInt32.uint_to_t
                                  (Prims.parse_int "65536"))
                           then FStar_UInt8.uint_to_t (Prims.of_int (2))
                           else
                             if
                               FStar_UInt32.lt x
                                 (FStar_UInt32.uint_to_t
                                    (Prims.parse_int "16777216"))
                             then FStar_UInt8.uint_to_t (Prims.of_int (3))
                             else FStar_UInt8.uint_to_t (Prims.of_int (4)) in
                       FStar_UInt8.add
                         (FStar_UInt8.uint_to_t (Prims.of_int (128))) len_len) in
                  if
                    FStar_UInt8.lt x1
                      (FStar_UInt8.uint_to_t (Prims.of_int (128)))
                  then
                    ((let h = FStar_HyperStack_ST.get () in
                      LowStar_Monotonic_Buffer.upd'
                        (match input with
                         | { LowParse_Slice.base = base;
                             LowParse_Slice.len = len1;_} -> base) pos x1);
                     FStar_UInt32.uint_to_t Prims.int_one)
                  else
                    if x1 = (FStar_UInt8.uint_to_t (Prims.of_int (129)))
                    then
                      ((let h = FStar_HyperStack_ST.get () in
                        LowStar_Monotonic_Buffer.upd'
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len1;_} -> base) pos x1);
                       (let h = FStar_HyperStack_ST.get () in
                        LowStar_Monotonic_Buffer.upd'
                          (match input with
                           | { LowParse_Slice.base = base;
                               LowParse_Slice.len = len1;_} -> base)
                          (FStar_UInt32.add pos
                             (FStar_UInt32.uint_to_t Prims.int_one))
                          (FStar_Int_Cast.uint32_to_uint8 x));
                       FStar_UInt32.uint_to_t (Prims.of_int (2)))
                    else
                      if x1 = (FStar_UInt8.uint_to_t (Prims.of_int (130)))
                      then
                        ((let h = FStar_HyperStack_ST.get () in
                          LowStar_Monotonic_Buffer.upd'
                            (match input with
                             | { LowParse_Slice.base = base;
                                 LowParse_Slice.len = len1;_} -> base) pos x1);
                         (let h = FStar_HyperStack_ST.get () in
                          let z =
                            LowParse_Low_BoundedInt.serialize32_bounded_integer_2
                              () x () ()
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base)
                              (FStar_UInt32.add pos
                                 (FStar_UInt32.uint_to_t Prims.int_one)) in
                          let h' = FStar_HyperStack_ST.get () in
                          FStar_UInt32.uint_to_t (Prims.of_int (3))))
                      else
                        if x1 = (FStar_UInt8.uint_to_t (Prims.of_int (131)))
                        then
                          ((let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd'
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base) pos
                              x1);
                           (let h = FStar_HyperStack_ST.get () in
                            let z =
                              LowParse_Low_BoundedInt.serialize32_bounded_integer_3
                                () x () ()
                                (match input with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len1;_} -> base)
                                (FStar_UInt32.add pos
                                   (FStar_UInt32.uint_to_t Prims.int_one)) in
                            let h' = FStar_HyperStack_ST.get () in
                            FStar_UInt32.uint_to_t (Prims.of_int (4))))
                        else
                          ((let h = FStar_HyperStack_ST.get () in
                            LowStar_Monotonic_Buffer.upd'
                              (match input with
                               | { LowParse_Slice.base = base;
                                   LowParse_Slice.len = len1;_} -> base) pos
                              x1);
                           (let h = FStar_HyperStack_ST.get () in
                            let z =
                              LowParse_Low_BoundedInt.serialize32_bounded_integer_4
                                () x () ()
                                (match input with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len1;_} -> base)
                                (FStar_UInt32.add pos
                                   (FStar_UInt32.uint_to_t Prims.int_one)) in
                            let h' = FStar_HyperStack_ST.get () in
                            FStar_UInt32.uint_to_t (Prims.of_int (5)))) in
                let h = FStar_HyperStack_ST.get () in
                FStar_UInt32.add pos len