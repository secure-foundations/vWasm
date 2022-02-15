open Prims
type aux_constbyte0 =
  | Zero 
let (uu___is_Zero : aux_constbyte0 -> Prims.bool) = fun projectee -> true
let (string_of_aux_constbyte0 : aux_constbyte0 -> Prims.string) =
  fun uu___ -> match uu___ with | Zero -> "zero"
let (aux_constbyte0_enum :
  (aux_constbyte0, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Zero, (FStar_UInt8.uint_to_t Prims.int_zero))]
let (synth_aux_constbyte0 : aux_constbyte0 -> aux_constbyte0) = fun x -> x
let (synth_aux_constbyte0_inv : aux_constbyte0 -> aux_constbyte0) =
  fun x -> x


let (parse32_aux_constbyte0_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_constbyte0 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                  then LowParse_Spec_Enum.Known Zero
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_constbyte0_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_constbyte0 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_constbyte0_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_constbyte0_key :
  aux_constbyte0 -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8 (FStar_UInt8.uint_to_t Prims.int_zero)
let (aux_constbyte0_serializer32 :
  aux_constbyte0 -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_constbyte0_key x
let (aux_constbyte0_size32 : aux_constbyte0 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one