open Prims




let (finalize_bounded_vlgen_exact :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (FStar_UInt32.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
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
      fun sz32 ->
        fun sk ->
          fun pk ->
            fun ssk ->
              fun wk ->
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
                                    wk
                                      (FStar_UInt32.sub pos'
                                         (FStar_UInt32.add pos sz32)) () ()
                                      input pos in
                                  let h1 = FStar_HyperStack_ST.get () in ()
let (finalize_bounded_vlgen :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (FStar_UInt32.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
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
      fun sz32 ->
        fun sk ->
          fun pk ->
            fun ssk ->
              fun wk ->
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
                                    wk
                                      (FStar_UInt32.sub pos'
                                         (FStar_UInt32.add pos sz32)) () ()
                                      input pos in
                                  let h2 = FStar_HyperStack_ST.get () in ()
let (validate_bounded_vlgen :
  LowParse_Spec_DER.der_length_t ->
    FStar_UInt32.t ->
      LowParse_Spec_DER.der_length_t ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                  ->
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
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun sk ->
            fun pk ->
              fun vk ->
                fun rk ->
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
                                    let n = vk () () input pos in
                                    if LowParse_Low_ErrorCode.is_error n
                                    then n
                                    else
                                      (let len =
                                         rk () () input
                                           (FStar_Int_Cast.uint64_to_uint32
                                              pos) in
                                       let h1 = FStar_HyperStack_ST.get () in
                                       if
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
                                                     | {
                                                         LowParse_Slice.base
                                                           = base;
                                                         LowParse_Slice.len =
                                                           len1;_}
                                                         -> len1)) n)
                                              (FStar_Int_Cast.uint32_to_uint64
                                                 len)
                                          then
                                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                                          else
                                            (let pos' =
                                               v () ()
                                                 {
                                                   LowParse_Slice.base =
                                                     (match input with
                                                      | {
                                                          LowParse_Slice.base
                                                            = base;
                                                          LowParse_Slice.len
                                                            = len1;_}
                                                          -> base);
                                                   LowParse_Slice.len =
                                                     (FStar_UInt32.add
                                                        (FStar_Int_Cast.uint64_to_uint32
                                                           n) len)
                                                 } n in
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
                                         (let h2 = FStar_HyperStack_ST.get () in
                                          if
                                            FStar_UInt64.lt
                                              (FStar_UInt64.sub
                                                 (FStar_Int_Cast.uint32_to_uint64
                                                    (match input with
                                                     | {
                                                         LowParse_Slice.base
                                                           = base;
                                                         LowParse_Slice.len =
                                                           len1;_}
                                                         -> len1)) n)
                                              (FStar_Int_Cast.uint32_to_uint64
                                                 len)
                                          then
                                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                                          else
                                            (let pos' =
                                               v () ()
                                                 {
                                                   LowParse_Slice.base =
                                                     (match input with
                                                      | {
                                                          LowParse_Slice.base
                                                            = base;
                                                          LowParse_Slice.len
                                                            = len1;_}
                                                          -> base);
                                                   LowParse_Slice.len =
                                                     (FStar_UInt32.add
                                                        (FStar_Int_Cast.uint64_to_uint32
                                                           n) len)
                                                 } n in
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
                                             else
                                               if
                                                 (FStar_UInt64.sub pos' n) <>
                                                   (FStar_Int_Cast.uint32_to_uint64
                                                      len)
                                               then
                                                 LowParse_Low_ErrorCode.validator_error_generic
                                               else pos')))

let (finalize_vlgen_exact :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (FStar_UInt32.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
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
      fun sz32 ->
        fun sk ->
          fun pk ->
            fun ssk ->
              fun wk ->
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
                                    wk
                                      (FStar_UInt32.sub pos'
                                         (FStar_UInt32.add pos sz32)) () ()
                                      input pos in
                                  let h1 = FStar_HyperStack_ST.get () in ()
let (finalize_vlgen :
  Prims.nat ->
    Prims.nat ->
      FStar_UInt32.t ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit ->
              (FStar_UInt32.t ->
                 unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                ->
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
      fun sz32 ->
        fun sk ->
          fun pk ->
            fun ssk ->
              fun wk ->
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
                                    wk
                                      (FStar_UInt32.sub pos'
                                         (FStar_UInt32.add pos sz32)) () ()
                                      input pos in
                                  let h2 = FStar_HyperStack_ST.get () in ()
let (validate_vlgen :
  LowParse_Spec_DER.der_length_t ->
    FStar_UInt32.t ->
      LowParse_Spec_DER.der_length_t ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              (unit ->
                 unit ->
                   (Obj.t, Obj.t) LowParse_Slice.slice ->
                     FStar_UInt64.t -> FStar_UInt64.t)
                ->
                (unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                  ->
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
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun sk ->
            fun pk ->
              fun vk ->
                fun rk ->
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
                                    let n = vk () () input pos in
                                    if LowParse_Low_ErrorCode.is_error n
                                    then n
                                    else
                                      (let len =
                                         rk () () input
                                           (FStar_Int_Cast.uint64_to_uint32
                                              pos) in
                                       let h2 = FStar_HyperStack_ST.get () in
                                       if
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
                                                     | {
                                                         LowParse_Slice.base
                                                           = base;
                                                         LowParse_Slice.len =
                                                           len1;_}
                                                         -> len1)) n)
                                              (FStar_Int_Cast.uint32_to_uint64
                                                 len)
                                          then
                                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                                          else
                                            (let pos' =
                                               v () ()
                                                 {
                                                   LowParse_Slice.base =
                                                     (match input with
                                                      | {
                                                          LowParse_Slice.base
                                                            = base;
                                                          LowParse_Slice.len
                                                            = len1;_}
                                                          -> base);
                                                   LowParse_Slice.len =
                                                     (FStar_UInt32.add
                                                        (FStar_Int_Cast.uint64_to_uint32
                                                           n) len)
                                                 } n in
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
                                         (let h3 = FStar_HyperStack_ST.get () in
                                          if
                                            FStar_UInt64.lt
                                              (FStar_UInt64.sub
                                                 (FStar_Int_Cast.uint32_to_uint64
                                                    (match input with
                                                     | {
                                                         LowParse_Slice.base
                                                           = base;
                                                         LowParse_Slice.len =
                                                           len1;_}
                                                         -> len1)) n)
                                              (FStar_Int_Cast.uint32_to_uint64
                                                 len)
                                          then
                                            LowParse_Low_ErrorCode.validator_error_not_enough_data
                                          else
                                            (let pos' =
                                               v () ()
                                                 {
                                                   LowParse_Slice.base =
                                                     (match input with
                                                      | {
                                                          LowParse_Slice.base
                                                            = base;
                                                          LowParse_Slice.len
                                                            = len1;_}
                                                          -> base);
                                                   LowParse_Slice.len =
                                                     (FStar_UInt32.add
                                                        (FStar_Int_Cast.uint64_to_uint32
                                                           n) len)
                                                 } n in
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
                                             else
                                               if
                                                 (FStar_UInt64.sub pos' n) <>
                                                   (FStar_Int_Cast.uint32_to_uint64
                                                      len)
                                               then
                                                 LowParse_Low_ErrorCode.validator_error_generic
                                               else pos')))
let (jump_bounded_vlgen :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          (Obj.t, Obj.t) LowParse_Slice.slice ->
                            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun sk ->
        fun pk ->
          fun vk ->
            fun rk ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun rrel ->
                        fun rel ->
                          fun input ->
                            fun pos ->
                              let h = FStar_HyperStack_ST.get () in
                              let n = vk () () input pos in
                              let len = rk () () input pos in
                              let h1 = FStar_HyperStack_ST.get () in
                              FStar_UInt32.add n len
let (jump_vlgen :
  LowParse_Spec_DER.der_length_t ->
    LowParse_Spec_DER.der_length_t ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt32.t -> FStar_UInt32.t)
              ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        unit ->
                          (Obj.t, Obj.t) LowParse_Slice.slice ->
                            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun vmin ->
    fun vmax ->
      fun sk ->
        fun pk ->
          fun vk ->
            fun rk ->
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
                              let n = vk () () input pos in
                              let len = rk () () input pos in
                              let h2 = FStar_HyperStack_ST.get () in
                              FStar_UInt32.add n len






let (accessor_bounded_vlgen_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
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
      fun sk ->
        fun pk ->
          fun jk ->
            fun k ->
              fun t ->
                fun p ->
                  fun s ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            jk () () input pos






let (accessor_vlgen_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
            ->
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
      fun sk ->
        fun pk ->
          fun jk ->
            fun k ->
              fun t ->
                fun p ->
                  fun s ->
                    fun rrel ->
                      fun rel ->
                        fun input ->
                          fun pos ->
                            let h = FStar_HyperStack_ST.get () in
                            jk () () input pos



