open Prims
type aux_section_const10 =
  | C 
let (uu___is_C : aux_section_const10 -> Prims.bool) = fun projectee -> true
let (string_of_aux_section_const10 : aux_section_const10 -> Prims.string) =
  fun uu___ -> match uu___ with | C -> "c"
let (aux_section_const10_enum :
  (aux_section_const10, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(C, (FStar_UInt8.uint_to_t (Prims.of_int (10))))]
let (synth_aux_section_const10 : aux_section_const10 -> aux_section_const10)
  = fun x -> x
let (synth_aux_section_const10_inv :
  aux_section_const10 -> aux_section_const10) = fun x -> x


let (parse32_aux_section_const10_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_section_const10 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (10))) = v1
                  then LowParse_Spec_Enum.Known C
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_section_const10_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_section_const10 * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_section_const10_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_section_const10_key :
  aux_section_const10 -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (FStar_UInt8.uint_to_t (Prims.of_int (10)))
let (aux_section_const10_serializer32 :
  aux_section_const10 -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_section_const10_key x
let (aux_section_const10_size32 : aux_section_const10 -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one