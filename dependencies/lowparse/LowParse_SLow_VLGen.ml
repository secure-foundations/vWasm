open Prims
let (parse32_bounded_vlgen :
  LowParse_Spec_DER.der_length_t ->
    FStar_UInt32.t ->
      LowParse_Spec_DER.der_length_t ->
        FStar_UInt32.t ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              (LowParse_SLow_Base.bytes32 ->
                 (FStar_UInt32.t * FStar_UInt32.t)
                   FStar_Pervasives_Native.option)
                ->
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
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun sk ->
            fun pk ->
              fun pk32 ->
                fun k ->
                  fun t ->
                    fun p ->
                      fun s ->
                        fun p32 ->
                          fun input ->
                            match pk32 input with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some (sz, consumed) ->
                                let input' =
                                  FStar_Bytes.slice input consumed
                                    (FStar_Bytes.len input) in
                                (match match if
                                               FStar_UInt32.lt
                                                 (FStar_Bytes.len input') sz
                                             then
                                               FStar_Pervasives_Native.None
                                             else
                                               (match p32
                                                        (FStar_Bytes.slice
                                                           input'
                                                           (FStar_UInt32.uint_to_t
                                                              Prims.int_zero)
                                                           sz)
                                                with
                                                | FStar_Pervasives_Native.Some
                                                    (v, consumed1) ->
                                                    if consumed1 = sz
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        (v, consumed1)
                                                    else
                                                      FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.None
                                                    ->
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
                                 | FStar_Pervasives_Native.Some
                                     (x, consumed') ->
                                     FStar_Pervasives_Native.Some
                                       (x,
                                         (FStar_UInt32.add consumed consumed')))
let (parse32_vlgen :
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
  fun vmin ->
    fun min ->
      fun vmax ->
        fun max ->
          fun sk ->
            fun pk ->
              fun pk32 ->
                fun k ->
                  fun t ->
                    fun p ->
                      fun s ->
                        fun p32 ->
                          fun input ->
                            match match pk32 input with
                                  | FStar_Pervasives_Native.None ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some
                                      (sz, consumed) ->
                                      let input' =
                                        FStar_Bytes.slice input consumed
                                          (FStar_Bytes.len input) in
                                      (match match if
                                                     FStar_UInt32.lt
                                                       (FStar_Bytes.len
                                                          input') sz
                                                   then
                                                     FStar_Pervasives_Native.None
                                                   else
                                                     (match p32
                                                              (FStar_Bytes.slice
                                                                 input'
                                                                 (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                 sz)
                                                      with
                                                      | FStar_Pervasives_Native.Some
                                                          (v, consumed1) ->
                                                          if consumed1 = sz
                                                          then
                                                            FStar_Pervasives_Native.Some
                                                              (v, consumed1)
                                                          else
                                                            FStar_Pervasives_Native.None
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Pervasives_Native.None)
                                             with
                                             | FStar_Pervasives_Native.Some
                                                 (v, consumed1) ->
                                                 FStar_Pervasives_Native.Some
                                                   (v, consumed1)
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 FStar_Pervasives_Native.None
                                       with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Pervasives_Native.None
                                       | FStar_Pervasives_Native.Some
                                           (x, consumed') ->
                                           FStar_Pervasives_Native.Some
                                             (x,
                                               (FStar_UInt32.add consumed
                                                  consumed')))
                            with
                            | FStar_Pervasives_Native.Some (v1, consumed) ->
                                FStar_Pervasives_Native.Some (v1, consumed)
                            | uu___ -> FStar_Pervasives_Native.None

let (serialize32_bounded_vlgen :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> LowParse_SLow_Base.bytes32) ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t -> LowParse_SLow_Base.bytes32) ->
                        Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun sk ->
        fun pk ->
          fun ssk ->
            fun ssk32 ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun s32 ->
                        fun input ->
                          let sp = s32 input in
                          let len = FStar_Bytes.len sp in
                          FStar_Bytes.append (ssk32 len) sp
let (serialize32_vlgen :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> LowParse_SLow_Base.bytes32) ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t -> LowParse_SLow_Base.bytes32) ->
                        Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun sk ->
        fun pk ->
          fun ssk ->
            fun ssk32 ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun s32 ->
                        fun input ->
                          let x = input in
                          let sp = s32 x in
                          let len = FStar_Bytes.len sp in
                          FStar_Bytes.append (ssk32 len) sp
let (size32_bounded_vlgen :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> FStar_UInt32.t) ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t -> FStar_UInt32.t) -> Obj.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun sk ->
        fun pk ->
          fun ssk ->
            fun ssk32 ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun s32 ->
                        fun input ->
                          let sp = s32 input in
                          FStar_UInt32.add (ssk32 sp) sp
let (size32_vlgen :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> FStar_UInt32.t) ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t -> FStar_UInt32.t) -> Obj.t -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun sk ->
        fun pk ->
          fun ssk ->
            fun ssk32 ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun s32 ->
                        fun input ->
                          let sp = s32 input in
                          FStar_UInt32.add (ssk32 sp) sp