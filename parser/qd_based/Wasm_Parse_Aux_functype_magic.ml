open Prims
type aux_functype_magic =
  | Functype 
let (uu___is_Functype : aux_functype_magic -> Prims.bool) =
  fun projectee -> true
let (string_of_aux_functype_magic : aux_functype_magic -> Prims.string) =
  fun uu___ -> match uu___ with | Functype -> "functype"
let (aux_functype_magic_enum :
  (aux_functype_magic, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Functype, (FStar_UInt8.uint_to_t (Prims.of_int (96))))]
let (synth_aux_functype_magic : aux_functype_magic -> aux_functype_magic) =
  fun x -> x
let (synth_aux_functype_magic_inv : aux_functype_magic -> aux_functype_magic)
  = fun x -> x


let (parse32_aux_functype_magic_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_functype_magic * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (96))) = v1
                  then LowParse_Spec_Enum.Known Functype
                  else LowParse_Spec_Enum.Unknown v1), consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (k, consumed) ->
        (match k with
         | LowParse_Spec_Enum.Known k' ->
             FStar_Pervasives_Native.Some (k', consumed)
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_functype_magic_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_functype_magic * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_functype_magic_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_functype_magic_key :
  aux_functype_magic -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (FStar_UInt8.uint_to_t (Prims.of_int (96)))
let (aux_functype_magic_serializer32 :
  aux_functype_magic -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_functype_magic_key x
let (aux_functype_magic_size32 : aux_functype_magic -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one