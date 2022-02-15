open Prims
type importdesc =
  | T_func of Wasm_Parse_Typeidx.typeidx 
  | T_table of Wasm_Parse_Tabletype.tabletype 
  | T_mem of Wasm_Parse_Memtype.memtype 
  | T_global of Wasm_Parse_Globaltype.globaltype 
let (uu___is_T_func : importdesc -> Prims.bool) =
  fun projectee -> match projectee with | T_func _0 -> true | uu___ -> false
let (__proj__T_func__item___0 : importdesc -> Wasm_Parse_Typeidx.typeidx) =
  fun projectee -> match projectee with | T_func _0 -> _0
let (uu___is_T_table : importdesc -> Prims.bool) =
  fun projectee -> match projectee with | T_table _0 -> true | uu___ -> false
let (__proj__T_table__item___0 :
  importdesc -> Wasm_Parse_Tabletype.tabletype) =
  fun projectee -> match projectee with | T_table _0 -> _0
let (uu___is_T_mem : importdesc -> Prims.bool) =
  fun projectee -> match projectee with | T_mem _0 -> true | uu___ -> false
let (__proj__T_mem__item___0 : importdesc -> Wasm_Parse_Memtype.memtype) =
  fun projectee -> match projectee with | T_mem _0 -> _0
let (uu___is_T_global : importdesc -> Prims.bool) =
  fun projectee ->
    match projectee with | T_global _0 -> true | uu___ -> false
let (__proj__T_global__item___0 :
  importdesc -> Wasm_Parse_Globaltype.globaltype) =
  fun projectee -> match projectee with | T_global _0 -> _0
let (tag_of_importdesc :
  importdesc -> Wasm_Parse_Aux_importdesc_label.aux_importdesc_label) =
  fun x ->
    match x with
    | T_func uu___ -> Wasm_Parse_Aux_importdesc_label.Func
    | T_table uu___ -> Wasm_Parse_Aux_importdesc_label.Table
    | T_mem uu___ -> Wasm_Parse_Aux_importdesc_label.Mem
    | T_global uu___ -> Wasm_Parse_Aux_importdesc_label.Global
let (aux_importdesc_label_as_enum_key :
  Wasm_Parse_Aux_importdesc_label.aux_importdesc_label ->
    Wasm_Parse_Aux_importdesc_label.aux_importdesc_label)
  = fun x -> x
let (key_of_importdesc :
  importdesc -> Wasm_Parse_Aux_importdesc_label.aux_importdesc_label) =
  fun x ->
    match x with
    | T_func uu___ -> Wasm_Parse_Aux_importdesc_label.Func
    | T_table uu___ -> Wasm_Parse_Aux_importdesc_label.Table
    | T_mem uu___ -> Wasm_Parse_Aux_importdesc_label.Mem
    | T_global uu___ -> Wasm_Parse_Aux_importdesc_label.Global
type 'x importdesc_case_of_aux_importdesc_label = Obj.t
let (to_importdesc_case_of_aux_importdesc_label :
  Wasm_Parse_Aux_importdesc_label.aux_importdesc_label ->
    Wasm_Parse_Aux_importdesc_label.aux_importdesc_label -> Obj.t -> Obj.t)
  = fun x -> fun x' -> fun y -> y
let (importdesc_refine :
  Wasm_Parse_Aux_importdesc_label.aux_importdesc_label ->
    importdesc -> importdesc)
  = fun k -> fun x -> x
let (synth_importdesc_cases :
  Wasm_Parse_Aux_importdesc_label.aux_importdesc_label -> Obj.t -> importdesc)
  =
  fun x ->
    fun y ->
      match x with
      | Wasm_Parse_Aux_importdesc_label.Func -> T_func (Obj.magic y)
      | Wasm_Parse_Aux_importdesc_label.Table -> T_table (Obj.magic y)
      | Wasm_Parse_Aux_importdesc_label.Mem -> T_mem (Obj.magic y)
      | Wasm_Parse_Aux_importdesc_label.Global -> T_global (Obj.magic y)
let (from_importdesc_case_of_aux_importdesc_label :
  Wasm_Parse_Aux_importdesc_label.aux_importdesc_label ->
    Wasm_Parse_Aux_importdesc_label.aux_importdesc_label -> Obj.t -> Obj.t)
  = fun x' -> fun x -> fun y -> y


let (synth_importdesc_cases_recip :
  Wasm_Parse_Aux_importdesc_label.aux_importdesc_label -> importdesc -> Obj.t)
  =
  fun k ->
    fun x ->
      match k with
      | Wasm_Parse_Aux_importdesc_label.Func ->
          Obj.repr (match x with | T_func y -> y)
      | Wasm_Parse_Aux_importdesc_label.Table ->
          Obj.repr (match x with | T_table y -> y)
      | Wasm_Parse_Aux_importdesc_label.Mem ->
          Obj.repr (match x with | T_mem y -> y)
      | Wasm_Parse_Aux_importdesc_label.Global ->
          Obj.repr (match x with | T_global y -> y)
let (importdesc_sum : LowParse_Spec_Sum.sum) =
  LowParse_Spec_Sum.Sum
    ((), (),
      (Obj.magic
         [(Wasm_Parse_Aux_importdesc_label.Func,
            (FStar_UInt8.uint_to_t Prims.int_zero));
         (Wasm_Parse_Aux_importdesc_label.Table,
           (FStar_UInt8.uint_to_t Prims.int_one));
         (Wasm_Parse_Aux_importdesc_label.Mem,
           (FStar_UInt8.uint_to_t (Prims.of_int (2))));
         (Wasm_Parse_Aux_importdesc_label.Global,
           (FStar_UInt8.uint_to_t (Prims.of_int (3))))]), (),
      (fun uu___ ->
         (fun x ->
            let x = Obj.magic x in
            match x with
            | T_func uu___ -> Obj.magic Wasm_Parse_Aux_importdesc_label.Func
            | T_table uu___ ->
                Obj.magic Wasm_Parse_Aux_importdesc_label.Table
            | T_mem uu___ -> Obj.magic Wasm_Parse_Aux_importdesc_label.Mem
            | T_global uu___ ->
                Obj.magic Wasm_Parse_Aux_importdesc_label.Global) uu___), (),
      (fun uu___1 ->
         fun uu___ ->
           (fun x ->
              let x = Obj.magic x in
              fun y ->
                match x with
                | Wasm_Parse_Aux_importdesc_label.Func ->
                    Obj.magic (T_func (Obj.magic y))
                | Wasm_Parse_Aux_importdesc_label.Table ->
                    Obj.magic (T_table (Obj.magic y))
                | Wasm_Parse_Aux_importdesc_label.Mem ->
                    Obj.magic (T_mem (Obj.magic y))
                | Wasm_Parse_Aux_importdesc_label.Global ->
                    Obj.magic (T_global (Obj.magic y))) uu___1 uu___),
      (fun uu___1 ->
         fun uu___ ->
           (fun k ->
              let k = Obj.magic k in
              fun x ->
                let x = Obj.magic x in
                match k with
                | Wasm_Parse_Aux_importdesc_label.Func ->
                    Obj.magic (Obj.repr (match x with | T_func y -> y))
                | Wasm_Parse_Aux_importdesc_label.Table ->
                    Obj.magic (Obj.repr (match x with | T_table y -> y))
                | Wasm_Parse_Aux_importdesc_label.Mem ->
                    Obj.magic (Obj.repr (match x with | T_mem y -> y))
                | Wasm_Parse_Aux_importdesc_label.Global ->
                    Obj.magic (Obj.repr (match x with | T_global y -> y)))
             uu___1 uu___), (), ())
let (importdesc_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (importdesc * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    let pi =
      match match LowParse_SLow_Int.parse32_u8 input with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some
                  ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                    then
                      LowParse_Spec_Enum.Known
                        Wasm_Parse_Aux_importdesc_label.Func
                    else
                      (let y =
                         if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                         then
                           LowParse_Spec_Enum.Known
                             Wasm_Parse_Aux_importdesc_label.Table
                         else
                           (let y1 =
                              if
                                (FStar_UInt8.uint_to_t (Prims.of_int (2))) =
                                  v1
                              then
                                LowParse_Spec_Enum.Known
                                  Wasm_Parse_Aux_importdesc_label.Mem
                              else
                                (let y2 =
                                   if
                                     (FStar_UInt8.uint_to_t
                                        (Prims.of_int (3)))
                                       = v1
                                   then
                                     LowParse_Spec_Enum.Known
                                       Wasm_Parse_Aux_importdesc_label.Global
                                   else LowParse_Spec_Enum.Unknown v1 in
                                 match y2 with
                                 | LowParse_Spec_Enum.Known k' ->
                                     LowParse_Spec_Enum.Known k'
                                 | LowParse_Spec_Enum.Unknown x' ->
                                     LowParse_Spec_Enum.Unknown v1) in
                            match y1 with
                            | LowParse_Spec_Enum.Known k' ->
                                LowParse_Spec_Enum.Known k'
                            | LowParse_Spec_Enum.Unknown x' ->
                                LowParse_Spec_Enum.Unknown v1) in
                       match y with
                       | LowParse_Spec_Enum.Known k' ->
                           LowParse_Spec_Enum.Known k'
                       | LowParse_Spec_Enum.Unknown x' ->
                           LowParse_Spec_Enum.Unknown v1)), consumed)
            | uu___ -> FStar_Pervasives_Native.None
      with
      | FStar_Pervasives_Native.Some (k, consumed) ->
          (match k with
           | LowParse_Spec_Enum.Known k' ->
               FStar_Pervasives_Native.Some (k', consumed)
           | uu___ -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None in
    match pi with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (k, consumed_k) ->
        let input_k =
          FStar_Bytes.slice input consumed_k (FStar_Bytes.len input) in
        if Wasm_Parse_Aux_importdesc_label.Func = k
        then
          let pcases2 =
            match Wasm_Parse_Typeidx.typeidx_parser32 input_k with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some ((T_func v1), consumed)
            | uu___ -> FStar_Pervasives_Native.None in
          (match pcases2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (x, consumed_x) ->
               FStar_Pervasives_Native.Some
                 (x, (FStar_UInt32.add consumed_k consumed_x)))
        else
          if Wasm_Parse_Aux_importdesc_label.Table = k
          then
            (let pcases2 =
               match Wasm_Parse_Tabletype.tabletype_parser32 input_k with
               | FStar_Pervasives_Native.Some (v1, consumed) ->
                   FStar_Pervasives_Native.Some ((T_table v1), consumed)
               | uu___1 -> FStar_Pervasives_Native.None in
             match pcases2 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (x, consumed_x) ->
                 FStar_Pervasives_Native.Some
                   (x, (FStar_UInt32.add consumed_k consumed_x)))
          else
            if Wasm_Parse_Aux_importdesc_label.Mem = k
            then
              (let pcases2 =
                 match Wasm_Parse_Memtype.memtype_parser32 input_k with
                 | FStar_Pervasives_Native.Some (v1, consumed) ->
                     FStar_Pervasives_Native.Some ((T_mem v1), consumed)
                 | uu___2 -> FStar_Pervasives_Native.None in
               match pcases2 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (x, consumed_x) ->
                   FStar_Pervasives_Native.Some
                     (x, (FStar_UInt32.add consumed_k consumed_x)))
            else
              (let pcases2 =
                 match Wasm_Parse_Globaltype.globaltype_parser32 input_k with
                 | FStar_Pervasives_Native.Some (v1, consumed) ->
                     FStar_Pervasives_Native.Some ((T_global v1), consumed)
                 | uu___3 -> FStar_Pervasives_Native.None in
               match pcases2 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (x, consumed_x) ->
                   FStar_Pervasives_Native.Some
                     (x, (FStar_UInt32.add consumed_k consumed_x)))
let (importdesc_serializer32 : importdesc -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let tg =
      match x with
      | T_func uu___ -> Wasm_Parse_Aux_importdesc_label.Func
      | T_table uu___ -> Wasm_Parse_Aux_importdesc_label.Table
      | T_mem uu___ -> Wasm_Parse_Aux_importdesc_label.Mem
      | T_global uu___ -> Wasm_Parse_Aux_importdesc_label.Global in
    let s1 =
      LowParse_SLow_Int.serialize32_u8
        (if Wasm_Parse_Aux_importdesc_label.Func = tg
         then FStar_UInt8.uint_to_t Prims.int_zero
         else
           if Wasm_Parse_Aux_importdesc_label.Table = tg
           then FStar_UInt8.uint_to_t Prims.int_one
           else
             if Wasm_Parse_Aux_importdesc_label.Mem = tg
             then FStar_UInt8.uint_to_t (Prims.of_int (2))
             else FStar_UInt8.uint_to_t (Prims.of_int (3))) in
    let s2 =
      if Wasm_Parse_Aux_importdesc_label.Func = tg
      then
        Wasm_Parse_Typeidx.typeidx_serializer32
          (match x with | T_func y -> y)
      else
        if Wasm_Parse_Aux_importdesc_label.Table = tg
        then
          Wasm_Parse_Tabletype.tabletype_serializer32
            (match x with | T_table y -> y)
        else
          if Wasm_Parse_Aux_importdesc_label.Mem = tg
          then
            Wasm_Parse_Memtype.memtype_serializer32
              (match x with | T_mem y -> y)
          else
            Wasm_Parse_Globaltype.globaltype_serializer32
              (match x with | T_global y -> y) in
    let res = FStar_Bytes.append s1 s2 in res
let (importdesc_size32 : importdesc -> FStar_UInt32.t) =
  fun x ->
    let tg =
      match x with
      | T_func uu___ -> Wasm_Parse_Aux_importdesc_label.Func
      | T_table uu___ -> Wasm_Parse_Aux_importdesc_label.Table
      | T_mem uu___ -> Wasm_Parse_Aux_importdesc_label.Mem
      | T_global uu___ -> Wasm_Parse_Aux_importdesc_label.Global in
    let s1 = FStar_UInt32.uint_to_t Prims.int_one in
    let s2 =
      if Wasm_Parse_Aux_importdesc_label.Func = tg
      then Wasm_Parse_Typeidx.typeidx_size32 (match x with | T_func y -> y)
      else
        if Wasm_Parse_Aux_importdesc_label.Table = tg
        then
          Wasm_Parse_Tabletype.tabletype_size32
            (match x with | T_table y -> y)
        else
          if Wasm_Parse_Aux_importdesc_label.Mem = tg
          then
            Wasm_Parse_Memtype.memtype_size32 (match x with | T_mem y -> y)
          else
            Wasm_Parse_Globaltype.globaltype_size32
              (match x with | T_global y -> y) in
    FStar_UInt32.add s1 s2



