open Prims
type aux_version_1 =
  | Version_1 
let (uu___is_Version_1 : aux_version_1 -> Prims.bool) = fun projectee -> true
let (string_of_aux_version_1 : aux_version_1 -> Prims.string) =
  fun uu___ -> match uu___ with | Version_1 -> "version_1"
let (aux_version_1_enum :
  (aux_version_1, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Version_1, (FStar_UInt8.uint_to_t Prims.int_one))]
let (synth_aux_version_1 : aux_version_1 -> aux_version_1) = fun x -> x
let (synth_aux_version_1_inv : aux_version_1 -> aux_version_1) = fun x -> x


let (parse32_aux_version_1_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_version_1 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                  then LowParse_Spec_Enum.Known Version_1
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_version_1_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_version_1 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_version_1_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_version_1_key :
  aux_version_1 -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8 (FStar_UInt8.uint_to_t Prims.int_one)
let (aux_version_1_serializer32 :
  aux_version_1 -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_version_1_key x
let (aux_version_1_size32 : aux_version_1 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one