open Prims
type opt_elemsec =
  | X_absent of unit 
  | X_present of Wasm_Parse_Elemsec.elemsec 
let (uu___is_X_absent : opt_elemsec -> Prims.bool) =
  fun projectee ->
    match projectee with | X_absent _0 -> true | uu___ -> false

let (uu___is_X_present : opt_elemsec -> Prims.bool) =
  fun projectee ->
    match projectee with | X_present _0 -> true | uu___ -> false
let (__proj__X_present__item___0 : opt_elemsec -> Wasm_Parse_Elemsec.elemsec)
  = fun projectee -> match projectee with | X_present _0 -> _0
let (tag_of_opt_elemsec :
  opt_elemsec -> Wasm_Parse_Optional_tag.optional_tag) =
  fun x ->
    match x with
    | X_absent uu___ -> Wasm_Parse_Optional_tag.Absent
    | X_present uu___ -> Wasm_Parse_Optional_tag.Present
let (optional_tag_as_enum_key :
  Wasm_Parse_Optional_tag.optional_tag ->
    Wasm_Parse_Optional_tag.optional_tag)
  = fun x -> x
let (key_of_opt_elemsec :
  opt_elemsec -> Wasm_Parse_Optional_tag.optional_tag) =
  fun x ->
    match x with
    | X_absent uu___ -> Wasm_Parse_Optional_tag.Absent
    | X_present uu___ -> Wasm_Parse_Optional_tag.Present
type 'x opt_elemsec_case_of_optional_tag = Obj.t
let (to_opt_elemsec_case_of_optional_tag :
  Wasm_Parse_Optional_tag.optional_tag ->
    Wasm_Parse_Optional_tag.optional_tag -> Obj.t -> Obj.t)
  = fun x -> fun x' -> fun y -> y
let (opt_elemsec_refine :
  Wasm_Parse_Optional_tag.optional_tag -> opt_elemsec -> opt_elemsec) =
  fun k -> fun x -> x
let (synth_opt_elemsec_cases :
  Wasm_Parse_Optional_tag.optional_tag -> Obj.t -> opt_elemsec) =
  fun x ->
    fun y ->
      match x with
      | Wasm_Parse_Optional_tag.Absent -> X_absent ()
      | Wasm_Parse_Optional_tag.Present -> X_present (Obj.magic y)
let (from_opt_elemsec_case_of_optional_tag :
  Wasm_Parse_Optional_tag.optional_tag ->
    Wasm_Parse_Optional_tag.optional_tag -> Obj.t -> Obj.t)
  = fun x' -> fun x -> fun y -> y


let (synth_opt_elemsec_cases_recip :
  Wasm_Parse_Optional_tag.optional_tag -> opt_elemsec -> Obj.t) =
  fun k ->
    fun x ->
      match k with
      | Wasm_Parse_Optional_tag.Absent -> Obj.repr ()
      | Wasm_Parse_Optional_tag.Present ->
          Obj.repr (match x with | X_present y -> y)
let (opt_elemsec_sum : LowParse_Spec_Sum.sum) =
  LowParse_Spec_Sum.Sum
    ((), (),
      (Obj.magic
         [(Wasm_Parse_Optional_tag.Absent,
            (FStar_UInt8.uint_to_t Prims.int_zero));
         (Wasm_Parse_Optional_tag.Present,
           (FStar_UInt8.uint_to_t Prims.int_one))]), (),
      (fun uu___ ->
         (fun x ->
            let x = Obj.magic x in
            match x with
            | X_absent uu___ -> Obj.magic Wasm_Parse_Optional_tag.Absent
            | X_present uu___ -> Obj.magic Wasm_Parse_Optional_tag.Present)
           uu___), (),
      (fun uu___1 ->
         fun uu___ ->
           (fun x ->
              let x = Obj.magic x in
              fun y ->
                match x with
                | Wasm_Parse_Optional_tag.Absent -> Obj.magic (X_absent ())
                | Wasm_Parse_Optional_tag.Present ->
                    Obj.magic (X_present (Obj.magic y))) uu___1 uu___),
      (fun uu___1 ->
         fun uu___ ->
           (fun k ->
              let k = Obj.magic k in
              fun x ->
                let x = Obj.magic x in
                match k with
                | Wasm_Parse_Optional_tag.Absent -> Obj.magic (Obj.repr ())
                | Wasm_Parse_Optional_tag.Present ->
                    Obj.magic (Obj.repr (match x with | X_present y -> y)))
             uu___1 uu___), (), ())
let (opt_elemsec_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (opt_elemsec * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    let pi =
      match match LowParse_SLow_Int.parse32_u8 input with
            | FStar_Pervasives_Native.Some (v1, consumed) ->
                FStar_Pervasives_Native.Some
                  ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                    then
                      LowParse_Spec_Enum.Known Wasm_Parse_Optional_tag.Absent
                    else
                      (let y =
                         if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                         then
                           LowParse_Spec_Enum.Known
                             Wasm_Parse_Optional_tag.Present
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
        if Wasm_Parse_Optional_tag.Absent = k
        then
          let pcases2 =
            FStar_Pervasives_Native.Some
              ((X_absent ()), (FStar_UInt32.uint_to_t Prims.int_zero)) in
          (match pcases2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (x, consumed_x) ->
               FStar_Pervasives_Native.Some
                 (x, (FStar_UInt32.add consumed_k consumed_x)))
        else
          (let pcases2 =
             match Wasm_Parse_Elemsec.elemsec_parser32 input_k with
             | FStar_Pervasives_Native.Some (v1, consumed) ->
                 FStar_Pervasives_Native.Some ((X_present v1), consumed)
             | uu___1 -> FStar_Pervasives_Native.None in
           match pcases2 with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (x, consumed_x) ->
               FStar_Pervasives_Native.Some
                 (x, (FStar_UInt32.add consumed_k consumed_x)))
let (opt_elemsec_serializer32 : opt_elemsec -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let tg =
      match x with
      | X_absent uu___ -> Wasm_Parse_Optional_tag.Absent
      | X_present uu___ -> Wasm_Parse_Optional_tag.Present in
    let s1 =
      LowParse_SLow_Int.serialize32_u8
        (if Wasm_Parse_Optional_tag.Absent = tg
         then FStar_UInt8.uint_to_t Prims.int_zero
         else FStar_UInt8.uint_to_t Prims.int_one) in
    let s2 =
      if Wasm_Parse_Optional_tag.Absent = tg
      then FStar_Bytes.empty_bytes
      else
        Wasm_Parse_Elemsec.elemsec_serializer32
          (match x with | X_present y -> y) in
    let res = FStar_Bytes.append s1 s2 in res
let (opt_elemsec_size32 : opt_elemsec -> FStar_UInt32.t) =
  fun x ->
    let tg =
      match x with
      | X_absent uu___ -> Wasm_Parse_Optional_tag.Absent
      | X_present uu___ -> Wasm_Parse_Optional_tag.Present in
    let s1 = FStar_UInt32.uint_to_t Prims.int_one in
    let s2 =
      if Wasm_Parse_Optional_tag.Absent = tg
      then FStar_UInt32.uint_to_t Prims.int_zero
      else
        Wasm_Parse_Elemsec.elemsec_size32 (match x with | X_present y -> y) in
    FStar_UInt32.add s1 s2

