open Prims
type exportdesc =
  | X_func of Wasm_Parse_Funcidx.funcidx 
  | X_table of Wasm_Parse_Tableidx.tableidx 
  | X_mem of Wasm_Parse_Memidx.memidx 
  | X_global of Wasm_Parse_Globalidx.globalidx 
let (uu___is_X_func : exportdesc -> Prims.bool) =
  fun projectee -> match projectee with | X_func _0 -> true | uu___ -> false
let (__proj__X_func__item___0 : exportdesc -> Wasm_Parse_Funcidx.funcidx) =
  fun projectee -> match projectee with | X_func _0 -> _0
let (uu___is_X_table : exportdesc -> Prims.bool) =
  fun projectee -> match projectee with | X_table _0 -> true | uu___ -> false
let (__proj__X_table__item___0 : exportdesc -> Wasm_Parse_Tableidx.tableidx)
  = fun projectee -> match projectee with | X_table _0 -> _0
let (uu___is_X_mem : exportdesc -> Prims.bool) =
  fun projectee -> match projectee with | X_mem _0 -> true | uu___ -> false
let (__proj__X_mem__item___0 : exportdesc -> Wasm_Parse_Memidx.memidx) =
  fun projectee -> match projectee with | X_mem _0 -> _0
let (uu___is_X_global : exportdesc -> Prims.bool) =
  fun projectee ->
    match projectee with | X_global _0 -> true | uu___ -> false
let (__proj__X_global__item___0 :
  exportdesc -> Wasm_Parse_Globalidx.globalidx) =
  fun projectee -> match projectee with | X_global _0 -> _0
let (tag_of_exportdesc :
  exportdesc -> Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label) =
  fun x ->
    match x with
    | X_func uu___ -> Wasm_Parse_Aux_exportdesc_label.Func
    | X_table uu___ -> Wasm_Parse_Aux_exportdesc_label.Table
    | X_mem uu___ -> Wasm_Parse_Aux_exportdesc_label.Mem
    | X_global uu___ -> Wasm_Parse_Aux_exportdesc_label.Global
let (aux_exportdesc_label_as_enum_key :
  Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label ->
    Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label)
  = fun x -> x
let (key_of_exportdesc :
  exportdesc -> Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label) =
  fun x ->
    match x with
    | X_func uu___ -> Wasm_Parse_Aux_exportdesc_label.Func
    | X_table uu___ -> Wasm_Parse_Aux_exportdesc_label.Table
    | X_mem uu___ -> Wasm_Parse_Aux_exportdesc_label.Mem
    | X_global uu___ -> Wasm_Parse_Aux_exportdesc_label.Global
type 'x exportdesc_case_of_aux_exportdesc_label = Obj.t
let (to_exportdesc_case_of_aux_exportdesc_label :
  Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label ->
    Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label -> Obj.t -> Obj.t)
  = fun x -> fun x' -> fun y -> y
let (exportdesc_refine :
  Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label ->
    exportdesc -> exportdesc)
  = fun k -> fun x -> x
let (synth_exportdesc_cases :
  Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label -> Obj.t -> exportdesc)
  =
  fun x ->
    fun y ->
      match x with
      | Wasm_Parse_Aux_exportdesc_label.Func -> X_func (Obj.magic y)
      | Wasm_Parse_Aux_exportdesc_label.Table -> X_table (Obj.magic y)
      | Wasm_Parse_Aux_exportdesc_label.Mem -> X_mem (Obj.magic y)
      | Wasm_Parse_Aux_exportdesc_label.Global -> X_global (Obj.magic y)
let (from_exportdesc_case_of_aux_exportdesc_label :
  Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label ->
    Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label -> Obj.t -> Obj.t)
  = fun x' -> fun x -> fun y -> y


let (synth_exportdesc_cases_recip :
  Wasm_Parse_Aux_exportdesc_label.aux_exportdesc_label -> exportdesc -> Obj.t)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun k ->
         fun x ->
           match k with
           | Wasm_Parse_Aux_exportdesc_label.Func ->
               (match x with | X_func y -> Obj.magic y)
           | Wasm_Parse_Aux_exportdesc_label.Table ->
               (match x with | X_table y -> Obj.magic y)
           | Wasm_Parse_Aux_exportdesc_label.Mem ->
               (match x with | X_mem y -> Obj.magic y)
           | Wasm_Parse_Aux_exportdesc_label.Global ->
               (match x with | X_global y -> Obj.magic y)) uu___1 uu___
let (exportdesc_sum : LowParse_Spec_Sum.sum) =
  LowParse_Spec_Sum.Sum
    ((), (),
      (Obj.magic
         [(Wasm_Parse_Aux_exportdesc_label.Func,
            (FStar_UInt8.uint_to_t Prims.int_zero));
         (Wasm_Parse_Aux_exportdesc_label.Table,
           (FStar_UInt8.uint_to_t Prims.int_one));
         (Wasm_Parse_Aux_exportdesc_label.Mem,
           (FStar_UInt8.uint_to_t (Prims.of_int (2))));
         (Wasm_Parse_Aux_exportdesc_label.Global,
           (FStar_UInt8.uint_to_t (Prims.of_int (3))))]), (),
      (fun uu___ ->
         (fun x ->
            let x = Obj.magic x in
            match x with
            | X_func uu___ -> Obj.magic Wasm_Parse_Aux_exportdesc_label.Func
            | X_table uu___ ->
                Obj.magic Wasm_Parse_Aux_exportdesc_label.Table
            | X_mem uu___ -> Obj.magic Wasm_Parse_Aux_exportdesc_label.Mem
            | X_global uu___ ->
                Obj.magic Wasm_Parse_Aux_exportdesc_label.Global) uu___), (),
      (fun uu___1 ->
         fun uu___ ->
           (fun x ->
              let x = Obj.magic x in
              fun y ->
                match x with
                | Wasm_Parse_Aux_exportdesc_label.Func ->
                    Obj.magic (X_func (Obj.magic y))
                | Wasm_Parse_Aux_exportdesc_label.Table ->
                    Obj.magic (X_table (Obj.magic y))
                | Wasm_Parse_Aux_exportdesc_label.Mem ->
                    Obj.magic (X_mem (Obj.magic y))
                | Wasm_Parse_Aux_exportdesc_label.Global ->
                    Obj.magic (X_global (Obj.magic y))) uu___1 uu___),
      (fun uu___1 ->
         fun uu___ ->
           (fun k ->
              let k = Obj.magic k in
              fun x ->
                let x = Obj.magic x in
                match k with
                | Wasm_Parse_Aux_exportdesc_label.Func ->
                    (match x with | X_func y -> Obj.magic y)
                | Wasm_Parse_Aux_exportdesc_label.Table ->
                    (match x with | X_table y -> Obj.magic y)
                | Wasm_Parse_Aux_exportdesc_label.Mem ->
                    (match x with | X_mem y -> Obj.magic y)
                | Wasm_Parse_Aux_exportdesc_label.Global ->
                    (match x with | X_global y -> Obj.magic y)) uu___1 uu___),
      (), ())
let (exportdesc_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (exportdesc * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    let pi =
      match match LowParse_SLow_Int.parse32_u8 input with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some
                  ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                    then
                      LowParse_Spec_Enum.Known
                        Wasm_Parse_Aux_exportdesc_label.Func
                    else
                      (let y =
                         if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                         then
                           LowParse_Spec_Enum.Known
                             Wasm_Parse_Aux_exportdesc_label.Table
                         else
                           (let y1 =
                              if
                                (FStar_UInt8.uint_to_t (Prims.of_int (2))) =
                                  v1
                              then
                                LowParse_Spec_Enum.Known
                                  Wasm_Parse_Aux_exportdesc_label.Mem
                              else
                                (let y2 =
                                   if
                                     (FStar_UInt8.uint_to_t
                                        (Prims.of_int (3)))
                                       = v1
                                   then
                                     LowParse_Spec_Enum.Known
                                       Wasm_Parse_Aux_exportdesc_label.Global
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
        if Wasm_Parse_Aux_exportdesc_label.Func = k
        then
          let pcases2 =
            match Wasm_Parse_Funcidx.funcidx_parser32 input_k with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some ((X_func v1), consumed)
            | uu___ -> FStar_Pervasives_Native.None in
          (match pcases2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (x, consumed_x) ->
               FStar_Pervasives_Native.Some
                 (x, (FStar_UInt32.add consumed_k consumed_x)))
        else
          if Wasm_Parse_Aux_exportdesc_label.Table = k
          then
            (let pcases2 =
               match Wasm_Parse_Tableidx.tableidx_parser32 input_k with
               | FStar_Pervasives_Native.Some (v1, consumed) ->
                   FStar_Pervasives_Native.Some ((X_table v1), consumed)
               | uu___1 -> FStar_Pervasives_Native.None in
             match pcases2 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some (x, consumed_x) ->
                 FStar_Pervasives_Native.Some
                   (x, (FStar_UInt32.add consumed_k consumed_x)))
          else
            if Wasm_Parse_Aux_exportdesc_label.Mem = k
            then
              (let pcases2 =
                 match Wasm_Parse_Memidx.memidx_parser32 input_k with
                 | FStar_Pervasives_Native.Some (v1, consumed) ->
                     FStar_Pervasives_Native.Some ((X_mem v1), consumed)
                 | uu___2 -> FStar_Pervasives_Native.None in
               match pcases2 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (x, consumed_x) ->
                   FStar_Pervasives_Native.Some
                     (x, (FStar_UInt32.add consumed_k consumed_x)))
            else
              (let pcases2 =
                 match Wasm_Parse_Globalidx.globalidx_parser32 input_k with
                 | FStar_Pervasives_Native.Some (v1, consumed) ->
                     FStar_Pervasives_Native.Some ((X_global v1), consumed)
                 | uu___3 -> FStar_Pervasives_Native.None in
               match pcases2 with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some (x, consumed_x) ->
                   FStar_Pervasives_Native.Some
                     (x, (FStar_UInt32.add consumed_k consumed_x)))
let (exportdesc_serializer32 : exportdesc -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let tg =
      match x with
      | X_func uu___ -> Wasm_Parse_Aux_exportdesc_label.Func
      | X_table uu___ -> Wasm_Parse_Aux_exportdesc_label.Table
      | X_mem uu___ -> Wasm_Parse_Aux_exportdesc_label.Mem
      | X_global uu___ -> Wasm_Parse_Aux_exportdesc_label.Global in
    let s1 =
      LowParse_SLow_Int.serialize32_u8
        (if Wasm_Parse_Aux_exportdesc_label.Func = tg
         then FStar_UInt8.uint_to_t Prims.int_zero
         else
           if Wasm_Parse_Aux_exportdesc_label.Table = tg
           then FStar_UInt8.uint_to_t Prims.int_one
           else
             if Wasm_Parse_Aux_exportdesc_label.Mem = tg
             then FStar_UInt8.uint_to_t (Prims.of_int (2))
             else FStar_UInt8.uint_to_t (Prims.of_int (3))) in
    let s2 =
      if Wasm_Parse_Aux_exportdesc_label.Func = tg
      then
        Wasm_Parse_Funcidx.funcidx_serializer32
          (match x with | X_func y -> y)
      else
        if Wasm_Parse_Aux_exportdesc_label.Table = tg
        then
          Wasm_Parse_Tableidx.tableidx_serializer32
            (match x with | X_table y -> y)
        else
          if Wasm_Parse_Aux_exportdesc_label.Mem = tg
          then
            Wasm_Parse_Memidx.memidx_serializer32
              (match x with | X_mem y -> y)
          else
            Wasm_Parse_Globalidx.globalidx_serializer32
              (match x with | X_global y -> y) in
    let res = FStar_Bytes.append s1 s2 in res
let (exportdesc_size32 : exportdesc -> FStar_UInt32.t) =
  fun x ->
    let tg =
      match x with
      | X_func uu___ -> Wasm_Parse_Aux_exportdesc_label.Func
      | X_table uu___ -> Wasm_Parse_Aux_exportdesc_label.Table
      | X_mem uu___ -> Wasm_Parse_Aux_exportdesc_label.Mem
      | X_global uu___ -> Wasm_Parse_Aux_exportdesc_label.Global in
    let s1 = FStar_UInt32.uint_to_t Prims.int_one in
    let s2 =
      if Wasm_Parse_Aux_exportdesc_label.Func = tg
      then Wasm_Parse_Funcidx.funcidx_size32 (match x with | X_func y -> y)
      else
        if Wasm_Parse_Aux_exportdesc_label.Table = tg
        then
          Wasm_Parse_Tableidx.tableidx_size32 (match x with | X_table y -> y)
        else
          if Wasm_Parse_Aux_exportdesc_label.Mem = tg
          then Wasm_Parse_Memidx.memidx_size32 (match x with | X_mem y -> y)
          else
            Wasm_Parse_Globalidx.globalidx_size32
              (match x with | X_global y -> y) in
    FStar_UInt32.add s1 s2



