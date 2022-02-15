open Prims
type optional_tag =
  | Absent 
  | Present 
let (uu___is_Absent : optional_tag -> Prims.bool) =
  fun projectee -> match projectee with | Absent -> true | uu___ -> false
let (uu___is_Present : optional_tag -> Prims.bool) =
  fun projectee -> match projectee with | Present -> true | uu___ -> false
let (string_of_optional_tag : optional_tag -> Prims.string) =
  fun uu___ -> match uu___ with | Absent -> "absent" | Present -> "present"
let (optional_tag_enum :
  (optional_tag, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Absent, (FStar_UInt8.uint_to_t Prims.int_zero));
  (Present, (FStar_UInt8.uint_to_t Prims.int_one))]
let (synth_optional_tag : optional_tag -> optional_tag) = fun x -> x
let (synth_optional_tag_inv : optional_tag -> optional_tag) = fun x -> x


let (parse32_optional_tag_key :
  LowParse_SLow_Base.bytes32 ->
    (optional_tag * FStar_UInt32.t) FStar_Pervasives_Native.option)
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
let (optional_tag_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (optional_tag * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_optional_tag_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_optional_tag_key :
  optional_tag -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if Absent = input
       then FStar_UInt8.uint_to_t Prims.int_zero
       else FStar_UInt8.uint_to_t Prims.int_one)
let (optional_tag_serializer32 : optional_tag -> LowParse_SLow_Base.bytes32)
  = fun input -> let x = input in serialize32_optional_tag_key x
let (optional_tag_size32 : optional_tag -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one