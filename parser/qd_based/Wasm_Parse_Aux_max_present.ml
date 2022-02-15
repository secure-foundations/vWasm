open Prims
type aux_max_present =
  | Absent 
  | Present 
let (uu___is_Absent : aux_max_present -> Prims.bool) =
  fun projectee -> match projectee with | Absent -> true | uu___ -> false
let (uu___is_Present : aux_max_present -> Prims.bool) =
  fun projectee -> match projectee with | Present -> true | uu___ -> false
let (string_of_aux_max_present : aux_max_present -> Prims.string) =
  fun uu___ -> match uu___ with | Absent -> "absent" | Present -> "present"
let (aux_max_present_enum :
  (aux_max_present, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Absent, (FStar_UInt8.uint_to_t Prims.int_zero));
  (Present, (FStar_UInt8.uint_to_t Prims.int_one))]
let (synth_aux_max_present : aux_max_present -> aux_max_present) = fun x -> x
let (synth_aux_max_present_inv : aux_max_present -> aux_max_present) =
  fun x -> x


let (parse32_aux_max_present_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_max_present * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                  then LowParse_Spec_Enum.Known Absent
                  else
                    (let y =
                       if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                       then LowParse_Spec_Enum.Known Present
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
    | uu___ -> FStar_Pervasives_Native.None
let (aux_max_present_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_max_present * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_max_present_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_max_present_key :
  aux_max_present -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if Absent = input
       then FStar_UInt8.uint_to_t Prims.int_zero
       else FStar_UInt8.uint_to_t Prims.int_one)
let (aux_max_present_serializer32 :
  aux_max_present -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_max_present_key x
let (aux_max_present_size32 : aux_max_present -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one