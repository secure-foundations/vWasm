open Prims
let (parse32_fldata :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          Prims.nat ->
            FStar_UInt32.t ->
              LowParse_SLow_Base.bytes32 ->
                (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun sz ->
            fun sz32 ->
              fun input ->
                if FStar_UInt32.lt (FStar_Bytes.len input) sz32
                then FStar_Pervasives_Native.None
                else
                  (match p32
                           (FStar_Bytes.slice input
                              (FStar_UInt32.uint_to_t Prims.int_zero) sz32)
                   with
                   | FStar_Pervasives_Native.Some (v, consumed) ->
                       if consumed = sz32
                       then FStar_Pervasives_Native.Some (v, consumed)
                       else FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None)
let (parse32_fldata_strong :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            Prims.nat ->
              FStar_UInt32.t ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun p32 ->
            fun sz ->
              fun sz32 ->
                fun input ->
                  match if FStar_UInt32.lt (FStar_Bytes.len input) sz32
                        then FStar_Pervasives_Native.None
                        else
                          (match p32
                                   (FStar_Bytes.slice input
                                      (FStar_UInt32.uint_to_t Prims.int_zero)
                                      sz32)
                           with
                           | FStar_Pervasives_Native.Some (v, consumed) ->
                               if consumed = sz32
                               then
                                 FStar_Pervasives_Native.Some (v, consumed)
                               else FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None)
                  with
                  | FStar_Pervasives_Native.Some (v, consumed) ->
                      FStar_Pervasives_Native.Some (v, consumed)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
let (serialize32_fldata_strong :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            Prims.nat -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t -> fun p -> fun s -> fun s32 -> fun sz -> fun input -> s32 input
let (size32_fldata_strong :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit -> unit -> Prims.nat -> FStar_UInt32.t -> Obj.t -> FStar_UInt32.t)
  = fun k -> fun t -> fun p -> fun s -> fun sz -> fun sz32 -> fun x -> sz32