open Prims
let (parse32_option :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_SLow_Base.bytes32 ->
            (Obj.t FStar_Pervasives_Native.option * FStar_UInt32.t)
              FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun input ->
            match p32 input with
            | FStar_Pervasives_Native.Some (x, consumed) ->
                FStar_Pervasives_Native.Some
                  ((FStar_Pervasives_Native.Some x), consumed)
            | uu___ ->
                FStar_Pervasives_Native.Some
                  (FStar_Pervasives_Native.None,
                    (FStar_UInt32.uint_to_t Prims.int_zero))
let (serialize32_option :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            unit ->
              Obj.t FStar_Pervasives_Native.option ->
                LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun u ->
              fun input ->
                match input with
                | FStar_Pervasives_Native.None -> FStar_Bytes.empty_bytes
                | FStar_Pervasives_Native.Some y -> s32 y
let (size32_option :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            unit -> Obj.t FStar_Pervasives_Native.option -> FStar_UInt32.t)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 ->
            fun u ->
              fun input ->
                match input with
                | FStar_Pervasives_Native.None ->
                    FStar_UInt32.uint_to_t Prims.int_zero
                | FStar_Pervasives_Native.Some y -> s32 y