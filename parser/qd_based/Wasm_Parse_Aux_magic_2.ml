open Prims
type aux_magic_2 =
  | Magic_2 
let (uu___is_Magic_2 : aux_magic_2 -> Prims.bool) = fun projectee -> true
let (string_of_aux_magic_2 : aux_magic_2 -> Prims.string) =
  fun uu___ -> match uu___ with | Magic_2 -> "magic_2"
let (aux_magic_2_enum : (aux_magic_2, FStar_UInt8.t) LowParse_Spec_Enum.enum)
  = [(Magic_2, (FStar_UInt8.uint_to_t (Prims.of_int (115))))]
let (synth_aux_magic_2 : aux_magic_2 -> aux_magic_2) = fun x -> x
let (synth_aux_magic_2_inv : aux_magic_2 -> aux_magic_2) = fun x -> x


let (parse32_aux_magic_2_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_magic_2 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (115))) = v1
                  then LowParse_Spec_Enum.Known Magic_2
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_magic_2_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_magic_2 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_magic_2_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_magic_2_key : aux_magic_2 -> LowParse_SLow_Base.bytes32)
  =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (FStar_UInt8.uint_to_t (Prims.of_int (115)))
let (aux_magic_2_serializer32 : aux_magic_2 -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_magic_2_key x
let (aux_magic_2_size32 : aux_magic_2 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one