open Prims


let (validate_fldata_gen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          Prims.nat ->
            FStar_UInt32.t ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun sz ->
            fun sz32 ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      if
                        FStar_UInt64.lt
                          (FStar_UInt64.sub
                             (FStar_Int_Cast.uint32_to_uint64
                                (match input with
                                 | { LowParse_Slice.base = base;
                                     LowParse_Slice.len = len;_} -> len)) pos)
                          (FStar_Int_Cast.uint32_to_uint64 sz32)
                      then
                        LowParse_Low_ErrorCode.validator_error_not_enough_data
                      else
                        (let pos' =
                           v () ()
                             {
                               LowParse_Slice.base =
                                 (match input with
                                  | { LowParse_Slice.base = base;
                                      LowParse_Slice.len = len;_} -> base);
                               LowParse_Slice.len =
                                 (FStar_UInt32.add
                                    (FStar_Int_Cast.uint64_to_uint32 pos)
                                    sz32)
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
                               (FStar_Int_Cast.uint32_to_uint64 sz32)
                           then
                             LowParse_Low_ErrorCode.validator_error_generic
                           else pos')
let (validate_fldata_consumes_all :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          Prims.nat ->
            FStar_UInt32.t ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t, Obj.t) LowParse_Slice.slice ->
                      FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun sz ->
            fun sz32 ->
              fun sq ->
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        if
                          FStar_UInt64.lt
                            (FStar_UInt64.sub
                               (FStar_Int_Cast.uint32_to_uint64
                                  (match input with
                                   | { LowParse_Slice.base = base;
                                       LowParse_Slice.len = len;_} -> len))
                               pos) (FStar_Int_Cast.uint32_to_uint64 sz32)
                        then
                          LowParse_Low_ErrorCode.validator_error_not_enough_data
                        else
                          (let pos' =
                             v () ()
                               {
                                 LowParse_Slice.base =
                                   (match input with
                                    | { LowParse_Slice.base = base;
                                        LowParse_Slice.len = len;_} -> base);
                                 LowParse_Slice.len =
                                   (FStar_UInt32.add
                                      (FStar_Int_Cast.uint64_to_uint32 pos)
                                      sz32)
                               } pos in
                           if LowParse_Low_ErrorCode.is_error pos'
                           then
                             (if
                                pos' =
                                  LowParse_Low_ErrorCode.validator_error_not_enough_data
                              then
                                LowParse_Low_ErrorCode.validator_error_generic
                              else pos')
                           else pos')
let (validate_fldata :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (unit ->
           unit ->
             (Obj.t, Obj.t) LowParse_Slice.slice ->
               FStar_UInt64.t -> FStar_UInt64.t)
          ->
          Prims.nat ->
            FStar_UInt32.t ->
              unit ->
                unit ->
                  (Obj.t, Obj.t) LowParse_Slice.slice ->
                    FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun sz ->
            fun sz32 ->
              if
                (match k with
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
                fun rrel ->
                  fun rel ->
                    fun input ->
                      fun pos ->
                        let h = FStar_HyperStack_ST.get () in
                        (if
                           FStar_UInt64.lt
                             (FStar_UInt64.sub
                                (FStar_Int_Cast.uint32_to_uint64
                                   (match input with
                                    | { LowParse_Slice.base = base;
                                        LowParse_Slice.len = len;_} -> len))
                                pos) (FStar_Int_Cast.uint32_to_uint64 sz32)
                         then
                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                         else
                           (let pos' =
                              v () ()
                                {
                                  LowParse_Slice.base =
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len;_} -> base);
                                  LowParse_Slice.len =
                                    (FStar_UInt32.add
                                       (FStar_Int_Cast.uint64_to_uint32 pos)
                                       sz32)
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
                (fun rrel ->
                   fun rel ->
                     fun input ->
                       fun pos ->
                         let h = FStar_HyperStack_ST.get () in
                         if
                           FStar_UInt64.lt
                             (FStar_UInt64.sub
                                (FStar_Int_Cast.uint32_to_uint64
                                   (match input with
                                    | { LowParse_Slice.base = base;
                                        LowParse_Slice.len = len;_} -> len))
                                pos) (FStar_Int_Cast.uint32_to_uint64 sz32)
                         then
                           LowParse_Low_ErrorCode.validator_error_not_enough_data
                         else
                           (let pos' =
                              v () ()
                                {
                                  LowParse_Slice.base =
                                    (match input with
                                     | { LowParse_Slice.base = base;
                                         LowParse_Slice.len = len;_} -> base);
                                  LowParse_Slice.len =
                                    (FStar_UInt32.add
                                       (FStar_Int_Cast.uint64_to_uint32 pos)
                                       sz32)
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
                                  (FStar_Int_Cast.uint32_to_uint64 sz32)
                              then
                                LowParse_Low_ErrorCode.validator_error_generic
                              else pos'))


let (validate_fldata_strong :
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
            fun sz ->
              fun sz32 ->
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
                                  pos) (FStar_Int_Cast.uint32_to_uint64 sz32)
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
                                         sz32)
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
                                  pos) (FStar_Int_Cast.uint32_to_uint64 sz32)
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
                                         sz32)
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
                                    (FStar_Int_Cast.uint32_to_uint64 sz32)
                                then
                                  LowParse_Low_ErrorCode.validator_error_generic
                                else pos'))
let (jump_fldata :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
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
        fun sz ->
          fun sz32 ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos ->
                    let h = FStar_HyperStack_ST.get () in
                    FStar_UInt32.add pos sz32
let (jump_fldata_strong :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
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
          fun sz ->
            fun sz32 ->
              fun rrel ->
                fun rel ->
                  fun input ->
                    fun pos ->
                      let h = FStar_HyperStack_ST.get () in
                      FStar_UInt32.add pos sz32


let (accessor_fldata :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        Prims.nat ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun sz ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos -> let h = FStar_HyperStack_ST.get () in pos
let (clens_fldata_strong :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit -> Prims.nat -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun sz ->
            {
              LowParse_Low_Base_Spec.clens_cond = ();
              LowParse_Low_Base_Spec.clens_get = ()
            }


let (accessor_fldata_strong :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          Prims.nat ->
            unit ->
              unit ->
                (Obj.t, Obj.t) LowParse_Slice.slice ->
                  FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun sz ->
            fun rrel ->
              fun rel ->
                fun input ->
                  fun pos -> let h = FStar_HyperStack_ST.get () in pos