open Prims


type 'p test_ifthenelse_tag =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> Prims.bool
let (validate_ifthenelse :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    (unit ->
       unit ->
         (Obj.t, Obj.t) LowParse_Slice.slice ->
           FStar_UInt64.t -> FStar_UInt64.t)
      ->
      (unit ->
         unit ->
           (Obj.t, Obj.t) LowParse_Slice.slice ->
             FStar_UInt32.t -> Prims.bool)
        ->
        (Prims.bool ->
           unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt64.t -> FStar_UInt64.t)
          ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun p ->
    fun vt ->
      fun test ->
        fun vp ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let pos_after_t = vt () () input pos in
                  if LowParse_Low_ErrorCode.is_error pos_after_t
                  then pos_after_t
                  else
                    (let b =
                       test () () input (FStar_Int_Cast.uint64_to_uint32 pos) in
                     if b
                     then vp true () () input pos_after_t
                     else vp false () () input pos_after_t)
let (jump_ifthenelse :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    (unit ->
       unit ->
         (Obj.t, Obj.t) LowParse_Slice.slice ->
           FStar_UInt32.t -> FStar_UInt32.t)
      ->
      (unit ->
         unit ->
           (Obj.t, Obj.t) LowParse_Slice.slice ->
             FStar_UInt32.t -> Prims.bool)
        ->
        (Prims.bool ->
           unit ->
             unit ->
               (Obj.t, Obj.t) LowParse_Slice.slice ->
                 FStar_UInt32.t -> FStar_UInt32.t)
          ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun p ->
    fun vt ->
      fun test ->
        fun vp ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in
                  let pos_after_t = vt () () input pos in
                  let b = test () () input pos in
                  if b
                  then vp true () () input pos_after_t
                  else vp false () () input pos_after_t
let (clens_ifthenelse_tag :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun p ->
    fun s ->
      {
        LowParse_Low_Base_Spec.clens_cond = ();
        LowParse_Low_Base_Spec.clens_get = ()
      }


let (accessor_ifthenelse_tag :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t ->
      unit ->
        unit ->
          (Obj.t, Obj.t) LowParse_Slice.slice ->
            FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun p ->
    fun s ->
      fun rrel ->
        fun rel ->
          fun sl -> fun pos -> let h = FStar_HyperStack_ST.get () in pos
let (clens_ifthenelse_payload :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t -> Prims.bool -> (Obj.t, Obj.t) LowParse_Low_Base_Spec.clens)
  =
  fun p ->
    fun s ->
      fun b ->
        {
          LowParse_Low_Base_Spec.clens_cond = ();
          LowParse_Low_Base_Spec.clens_get = ()
        }





let (accessor_ifthenelse_payload' :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t ->
      (unit ->
         unit ->
           (Obj.t, Obj.t) LowParse_Slice.slice ->
             FStar_UInt32.t -> FStar_UInt32.t)
        ->
        Prims.bool ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun p ->
    fun s ->
      fun j ->
        fun b ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in j () () input pos
let (accessor_ifthenelse_payload :
  LowParse_Spec_IfThenElse.parse_ifthenelse_param ->
    Obj.t ->
      (unit ->
         unit ->
           (Obj.t, Obj.t) LowParse_Slice.slice ->
             FStar_UInt32.t -> FStar_UInt32.t)
        ->
        Prims.bool ->
          unit ->
            unit ->
              (Obj.t, Obj.t) LowParse_Slice.slice ->
                FStar_UInt32.t -> FStar_UInt32.t)
  =
  fun p ->
    fun s ->
      fun j ->
        fun b ->
          fun rrel ->
            fun rel ->
              fun input ->
                fun pos ->
                  let h = FStar_HyperStack_ST.get () in j () () input pos