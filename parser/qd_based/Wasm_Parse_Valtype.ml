open Prims
type valtype =
  | I32 
  | I64 
  | F32 
  | F64 
let (uu___is_I32 : valtype -> Prims.bool) =
  fun projectee -> match projectee with | I32 -> true | uu___ -> false
let (uu___is_I64 : valtype -> Prims.bool) =
  fun projectee -> match projectee with | I64 -> true | uu___ -> false
let (uu___is_F32 : valtype -> Prims.bool) =
  fun projectee -> match projectee with | F32 -> true | uu___ -> false
let (uu___is_F64 : valtype -> Prims.bool) =
  fun projectee -> match projectee with | F64 -> true | uu___ -> false
let (string_of_valtype : valtype -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | I32 -> "i32"
    | I64 -> "i64"
    | F32 -> "f32"
    | F64 -> "f64"
let (valtype_enum : (valtype, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(I32, (FStar_UInt8.uint_to_t (Prims.of_int (127))));
  (I64, (FStar_UInt8.uint_to_t (Prims.of_int (126))));
  (F32, (FStar_UInt8.uint_to_t (Prims.of_int (125))));
  (F64, (FStar_UInt8.uint_to_t (Prims.of_int (124))))]
let (synth_valtype : valtype -> valtype) = fun x -> x
let (synth_valtype_inv : valtype -> valtype) = fun x -> x


let (parse32_valtype_key :
  LowParse_SLow_Base.bytes32 ->
    (valtype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (127))) = v1
                  then LowParse_Spec_Enum.Known I32
                  else
                    (let y =
                       if (FStar_UInt8.uint_to_t (Prims.of_int (126))) = v1
                       then LowParse_Spec_Enum.Known I64
                       else
                         (let y1 =
                            if
                              (FStar_UInt8.uint_to_t (Prims.of_int (125))) =
                                v1
                            then LowParse_Spec_Enum.Known F32
                            else
                              (let y2 =
                                 if
                                   (FStar_UInt8.uint_to_t
                                      (Prims.of_int (124)))
                                     = v1
                                 then LowParse_Spec_Enum.Known F64
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
    | uu___ -> FStar_Pervasives_Native.None
let (valtype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (valtype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_valtype_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_valtype_key : valtype -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if I32 = input
       then FStar_UInt8.uint_to_t (Prims.of_int (127))
       else
         if I64 = input
         then FStar_UInt8.uint_to_t (Prims.of_int (126))
         else
           if F32 = input
           then FStar_UInt8.uint_to_t (Prims.of_int (125))
           else FStar_UInt8.uint_to_t (Prims.of_int (124)))
let (valtype_serializer32 : valtype -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_valtype_key x
let (valtype_size32 : valtype -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one