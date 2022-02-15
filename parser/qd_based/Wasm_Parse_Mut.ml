open Prims
type mut =
  | Cnst 
  | Var 
let (uu___is_Cnst : mut -> Prims.bool) =
  fun projectee -> match projectee with | Cnst -> true | uu___ -> false
let (uu___is_Var : mut -> Prims.bool) =
  fun projectee -> match projectee with | Var -> true | uu___ -> false
let (string_of_mut : mut -> Prims.string) =
  fun uu___ -> match uu___ with | Cnst -> "cnst" | Var -> "var"
let (mut_enum : (mut, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Cnst, (FStar_UInt8.uint_to_t Prims.int_zero));
  (Var, (FStar_UInt8.uint_to_t Prims.int_one))]
let (synth_mut : mut -> mut) = fun x -> x
let (synth_mut_inv : mut -> mut) = fun x -> x


let (parse32_mut_key :
  LowParse_SLow_Base.bytes32 ->
    (mut * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                  then LowParse_Spec_Enum.Known Cnst
                  else
                    (let y =
                       if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                       then LowParse_Spec_Enum.Known Var
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
let (mut_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (mut * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_mut_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_mut_key : mut -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if Cnst = input
       then FStar_UInt8.uint_to_t Prims.int_zero
       else FStar_UInt8.uint_to_t Prims.int_one)
let (mut_serializer32 : mut -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_mut_key x
let (mut_size32 : mut -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one