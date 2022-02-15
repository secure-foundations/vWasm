open Prims
type elemtype =
  | Funcref 
let (uu___is_Funcref : elemtype -> Prims.bool) = fun projectee -> true
let (string_of_elemtype : elemtype -> Prims.string) =
  fun uu___ -> match uu___ with | Funcref -> "funcref"
let (elemtype_enum : (elemtype, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Funcref, (FStar_UInt8.uint_to_t (Prims.of_int (112))))]
let (synth_elemtype : elemtype -> elemtype) = fun x -> x
let (synth_elemtype_inv : elemtype -> elemtype) = fun x -> x


let (parse32_elemtype_key :
  LowParse_SLow_Base.bytes32 ->
    (elemtype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (112))) = v1
                  then LowParse_Spec_Enum.Known Funcref
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (elemtype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (elemtype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_elemtype_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_elemtype_key : elemtype -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (FStar_UInt8.uint_to_t (Prims.of_int (112)))
let (elemtype_serializer32 : elemtype -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_elemtype_key x
let (elemtype_size32 : elemtype -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one