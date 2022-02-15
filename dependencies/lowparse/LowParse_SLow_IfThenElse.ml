open Prims
let (parse32_ifthenelse :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    (LowParse_SLow_Base.bytes32 ->
       (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
      ->
      (Obj.t -> Prims.bool) ->
        (Prims.bool ->
           LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          (Prims.bool -> Obj.t -> Obj.t -> Obj.t) ->
            LowParse_SLow_Base.bytes32 ->
              (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun p ->
    fun pt32 ->
      fun b32 ->
        fun pp32 ->
          fun synt ->
            fun input ->
              match pt32 input with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some (t, consumed_t) ->
                  let b = b32 t in
                  let input' =
                    FStar_Bytes.slice input consumed_t
                      (FStar_Bytes.len input) in
                  if b
                  then
                    (match pp32 true input' with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (pl, consumed_pl) ->
                         FStar_Pervasives_Native.Some
                           ((synt true t pl),
                             (FStar_UInt32.add consumed_t consumed_pl)))
                  else
                    (match pp32 false input' with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some (pl, consumed_pl) ->
                         FStar_Pervasives_Native.Some
                           ((synt false t pl),
                             (FStar_UInt32.add consumed_t consumed_pl)))
let (serialize32_ifthenelse :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t ->
      (Obj.t -> LowParse_SLow_Base.bytes32) ->
        (Obj.t -> Obj.t) ->
          (Obj.t -> Prims.bool) ->
            (Prims.bool -> Obj.t -> Obj.t) ->
              (Prims.bool -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun p ->
    fun s ->
      fun st32 ->
        fun syntt ->
          fun b32 ->
            fun syntp ->
              fun sp32 ->
                fun input ->
                  let t = syntt input in
                  let st = st32 t in
                  let b = b32 t in
                  if b
                  then
                    let y = syntp true input in
                    FStar_Bytes.append st (sp32 true y)
                  else
                    (let y = syntp false input in
                     FStar_Bytes.append st (sp32 false y))
let (size32_ifthenelse :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t ->
      (Obj.t -> FStar_UInt32.t) ->
        (Obj.t -> Obj.t) ->
          (Obj.t -> Prims.bool) ->
            (Prims.bool -> Obj.t -> Obj.t) ->
              (Prims.bool -> Obj.t -> FStar_UInt32.t) ->
                Obj.t -> FStar_UInt32.t)
  =
  fun p ->
    fun s ->
      fun st32 ->
        fun syntt ->
          fun b32 ->
            fun syntp ->
              fun sp32 ->
                fun input ->
                  let t = syntt input in
                  let st = st32 t in
                  let b = b32 t in
                  if b
                  then
                    let y = syntp true input in
                    FStar_UInt32.add st (sp32 true y)
                  else
                    (let y = syntp false input in
                     FStar_UInt32.add st (sp32 false y))