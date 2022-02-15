open Prims
type limits =
  | L_absent of Wasm_Parse_Aux_only_min.aux_only_min 
  | L_present of Wasm_Parse_Aux_min_max.aux_min_max 
let (uu___is_L_absent : limits -> Prims.bool) =
  fun projectee ->
    match projectee with | L_absent _0 -> true | uu___ -> false
let (__proj__L_absent__item___0 :
  limits -> Wasm_Parse_Aux_only_min.aux_only_min) =
  fun projectee -> match projectee with | L_absent _0 -> _0
let (uu___is_L_present : limits -> Prims.bool) =
  fun projectee ->
    match projectee with | L_present _0 -> true | uu___ -> false
let (__proj__L_present__item___0 :
  limits -> Wasm_Parse_Aux_min_max.aux_min_max) =
  fun projectee -> match projectee with | L_present _0 -> _0
let (tag_of_limits : limits -> Wasm_Parse_Aux_max_present.aux_max_present) =
  fun x ->
    match x with
    | L_absent uu___ -> Wasm_Parse_Aux_max_present.Absent
    | L_present uu___ -> Wasm_Parse_Aux_max_present.Present
let (aux_max_present_as_enum_key :
  Wasm_Parse_Aux_max_present.aux_max_present ->
    Wasm_Parse_Aux_max_present.aux_max_present)
  = fun x -> x
let (key_of_limits : limits -> Wasm_Parse_Aux_max_present.aux_max_present) =
  fun x ->
    match x with
    | L_absent uu___ -> Wasm_Parse_Aux_max_present.Absent
    | L_present uu___ -> Wasm_Parse_Aux_max_present.Present
type 'x limits_case_of_aux_max_present = Obj.t
let (to_limits_case_of_aux_max_present :
  Wasm_Parse_Aux_max_present.aux_max_present ->
    Wasm_Parse_Aux_max_present.aux_max_present -> Obj.t -> Obj.t)
  = fun x -> fun x' -> fun y -> y
let (limits_refine :
  Wasm_Parse_Aux_max_present.aux_max_present -> limits -> limits) =
  fun k -> fun x -> x
let (synth_limits_cases :
  Wasm_Parse_Aux_max_present.aux_max_present -> Obj.t -> limits) =
  fun x ->
    fun y ->
      match x with
      | Wasm_Parse_Aux_max_present.Absent -> L_absent (Obj.magic y)
      | Wasm_Parse_Aux_max_present.Present -> L_present (Obj.magic y)
let (from_limits_case_of_aux_max_present :
  Wasm_Parse_Aux_max_present.aux_max_present ->
    Wasm_Parse_Aux_max_present.aux_max_present -> Obj.t -> Obj.t)
  = fun x' -> fun x -> fun y -> y


let (synth_limits_cases_recip :
  Wasm_Parse_Aux_max_present.aux_max_present -> limits -> Obj.t) =
  fun k ->
    fun x ->
      match k with
      | Wasm_Parse_Aux_max_present.Absent ->
          Obj.repr (match x with | L_absent y -> y)
      | Wasm_Parse_Aux_max_present.Present ->
          Obj.repr (match x with | L_present y -> y)
let (limits_sum : LowParse_Spec_Sum.sum) =
  LowParse_Spec_Sum.Sum
    ((), (),
      (Obj.magic
         [(Wasm_Parse_Aux_max_present.Absent,
            (FStar_UInt8.uint_to_t Prims.int_zero));
         (Wasm_Parse_Aux_max_present.Present,
           (FStar_UInt8.uint_to_t Prims.int_one))]), (),
      (fun uu___ ->
         (fun x ->
            let x = Obj.magic x in
            match x with
            | L_absent uu___ -> Obj.magic Wasm_Parse_Aux_max_present.Absent
            | L_present uu___ -> Obj.magic Wasm_Parse_Aux_max_present.Present)
           uu___), (),
      (fun uu___1 ->
         fun uu___ ->
           (fun x ->
              let x = Obj.magic x in
              fun y ->
                match x with
                | Wasm_Parse_Aux_max_present.Absent ->
                    Obj.magic (L_absent (Obj.magic y))
                | Wasm_Parse_Aux_max_present.Present ->
                    Obj.magic (L_present (Obj.magic y))) uu___1 uu___),
      (fun uu___1 ->
         fun uu___ ->
           (fun k ->
              let k = Obj.magic k in
              fun x ->
                let x = Obj.magic x in
                match k with
                | Wasm_Parse_Aux_max_present.Absent ->
                    Obj.magic (Obj.repr (match x with | L_absent y -> y))
                | Wasm_Parse_Aux_max_present.Present ->
                    Obj.magic (Obj.repr (match x with | L_present y -> y)))
             uu___1 uu___), (), ())
let (limits_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (limits * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    let pi =
      match match LowParse_SLow_Int.parse32_u8 input with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some
                  ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                    then
                      LowParse_Spec_Enum.Known
                        Wasm_Parse_Aux_max_present.Absent
                    else
                      (let y =
                         if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                         then
                           LowParse_Spec_Enum.Known
                             Wasm_Parse_Aux_max_present.Present
                         else LowParse_Spec_Enum.Unknown v1 in
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
        if Wasm_Parse_Aux_max_present.Absent = k
        then
          let pcases2 =
            match Wasm_Parse_Aux_only_min.aux_only_min_parser32 input_k with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some ((L_absent v1), consumed)
            | uu___ -> FStar_Pervasives_Native.None in
          (match pcases2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (x, consumed_x) ->
               FStar_Pervasives_Native.Some
                 (x, (FStar_UInt32.add consumed_k consumed_x)))
        else
          (let pcases2 =
             match Wasm_Parse_Aux_min_max.aux_min_max_parser32 input_k with
             | FStar_Pervasives_Native.Some (v1, consumed) ->
                 FStar_Pervasives_Native.Some ((L_present v1), consumed)
             | uu___1 -> FStar_Pervasives_Native.None in
           match pcases2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (x, consumed_x) ->
               FStar_Pervasives_Native.Some
                 (x, (FStar_UInt32.add consumed_k consumed_x)))
let (limits_serializer32 : limits -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let tg =
      match x with
      | L_absent uu___ -> Wasm_Parse_Aux_max_present.Absent
      | L_present uu___ -> Wasm_Parse_Aux_max_present.Present in
    let s1 =
      LowParse_SLow_Int.serialize32_u8
        (if Wasm_Parse_Aux_max_present.Absent = tg
         then FStar_UInt8.uint_to_t Prims.int_zero
         else FStar_UInt8.uint_to_t Prims.int_one) in
    let s2 =
      if Wasm_Parse_Aux_max_present.Absent = tg
      then
        Wasm_Parse_Aux_only_min.aux_only_min_serializer32
          (match x with | L_absent y -> y)
      else
        Wasm_Parse_Aux_min_max.aux_min_max_serializer32
          (match x with | L_present y -> y) in
    let res = FStar_Bytes.append s1 s2 in res
let (limits_size32 : limits -> FStar_UInt32.t) =
  fun x ->
    let tg =
      match x with
      | L_absent uu___ -> Wasm_Parse_Aux_max_present.Absent
      | L_present uu___ -> Wasm_Parse_Aux_max_present.Present in
    let s1 = FStar_UInt32.uint_to_t Prims.int_one in
    let s2 =
      if Wasm_Parse_Aux_max_present.Absent = tg
      then
        Wasm_Parse_Aux_only_min.aux_only_min_size32
          (match x with | L_absent y -> y)
      else
        Wasm_Parse_Aux_min_max.aux_min_max_size32
          (match x with | L_present y -> y) in
    FStar_UInt32.add s1 s2

