open Prims
let (validate_option :
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
  fun k ->
    fun t ->
      fun p ->
        fun v ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let r = v () () input pos in
                  if LowParse_Low_ErrorCode.is_error r then pos else r