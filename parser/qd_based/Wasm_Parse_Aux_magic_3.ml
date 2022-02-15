open Prims
type aux_magic_3 =
  | Magic_3 
let (uu___is_Magic_3 : aux_magic_3 -> Prims.bool) = fun projectee -> true
let (string_of_aux_magic_3 : aux_magic_3 -> Prims.string) =
  fun uu___ -> match uu___ with | Magic_3 -> "magic_3"
let (aux_magic_3_enum : (aux_magic_3, FStar_UInt8.t) LowParse_Spec_Enum.enum)
  = [(Magic_3, (FStar_UInt8.uint_to_t (Prims.of_int (109))))]
let (synth_aux_magic_3 : aux_magic_3 -> aux_magic_3) = fun x -> x
let (synth_aux_magic_3_inv : aux_magic_3 -> aux_magic_3) = fun x -> x


let (parse32_aux_magic_3_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_magic_3 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (109))) = v1
                  then LowParse_Spec_Enum.Known Magic_3
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_magic_3_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_magic_3 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_magic_3_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_magic_3_key : aux_magic_3 -> LowParse_SLow_Base.bytes32)
  =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (FStar_UInt8.uint_to_t (Prims.of_int (109)))
let (aux_magic_3_serializer32 : aux_magic_3 -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_magic_3_key x
let (aux_magic_3_size32 : aux_magic_3 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one