open Prims
type blocktype =
  | R_none 
  | R_i32 
  | R_i64 
  | R_f32 
  | R_f64 
let (uu___is_R_none : blocktype -> Prims.bool) =
  fun projectee -> match projectee with | R_none -> true | uu___ -> false
let (uu___is_R_i32 : blocktype -> Prims.bool) =
  fun projectee -> match projectee with | R_i32 -> true | uu___ -> false
let (uu___is_R_i64 : blocktype -> Prims.bool) =
  fun projectee -> match projectee with | R_i64 -> true | uu___ -> false
let (uu___is_R_f32 : blocktype -> Prims.bool) =
  fun projectee -> match projectee with | R_f32 -> true | uu___ -> false
let (uu___is_R_f64 : blocktype -> Prims.bool) =
  fun projectee -> match projectee with | R_f64 -> true | uu___ -> false
let (string_of_blocktype : blocktype -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | R_none -> "r_none"
    | R_i32 -> "r_i32"
    | R_i64 -> "r_i64"
    | R_f32 -> "r_f32"
    | R_f64 -> "r_f64"
let (blocktype_enum : (blocktype, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(R_none, (FStar_UInt8.uint_to_t (Prims.of_int (64))));
  (R_i32, (FStar_UInt8.uint_to_t (Prims.of_int (127))));
  (R_i64, (FStar_UInt8.uint_to_t (Prims.of_int (126))));
  (R_f32, (FStar_UInt8.uint_to_t (Prims.of_int (125))));
  (R_f64, (FStar_UInt8.uint_to_t (Prims.of_int (124))))]
let (synth_blocktype : blocktype -> blocktype) = fun x -> x
let (synth_blocktype_inv : blocktype -> blocktype) = fun x -> x


let (parse32_blocktype_key :
  LowParse_SLow_Base.bytes32 ->
    (blocktype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t (Prims.of_int (64))) = v1
                  then LowParse_Spec_Enum.Known R_none
                  else
                    (let y =
                       if (FStar_UInt8.uint_to_t (Prims.of_int (127))) = v1
                       then LowParse_Spec_Enum.Known R_i32
                       else
                         (let y1 =
                            if
                              (FStar_UInt8.uint_to_t (Prims.of_int (126))) =
                                v1
                            then LowParse_Spec_Enum.Known R_i64
                            else
                              (let y2 =
                                 if
                                   (FStar_UInt8.uint_to_t
                                      (Prims.of_int (125)))
                                     = v1
                                 then LowParse_Spec_Enum.Known R_f32
                                 else
                                   (let y3 =
                                      if
                                        (FStar_UInt8.uint_to_t
                                           (Prims.of_int (124)))
                                          = v1
                                      then LowParse_Spec_Enum.Known R_f64
                                      else LowParse_Spec_Enum.Unknown v1 in
                                    match y3 with
                                    | LowParse_Spec_Enum.Known k' ->
                                        LowParse_Spec_Enum.Known k'
                                    | LowParse_Spec_Enum.Unknown x' ->
                                        LowParse_Spec_Enum.Unknown v1) in
                               match y2 with
                               | LowParse_Spec_Enum.Known k' ->
                                   LowParse_Spec_Enum.Known k'
                               | LowParse_Spec_Enum.Unknown x' ->
                                   LowParse_Spec_Enum.Unknown v1) in
                          match y1 with
                          | LowParse_Spec_Enum.Known k' ->
                              LowParse_Spec_Enum.Known k'
                          | LowParse_Spec_Enum.Unknown x' ->
                              LowParse_Spec_Enum.Unknown v1) in
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
let (blocktype_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (blocktype * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_blocktype_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_blocktype_key : blocktype -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if R_none = input
       then FStar_UInt8.uint_to_t (Prims.of_int (64))
       else
         if R_i32 = input
         then FStar_UInt8.uint_to_t (Prims.of_int (127))
         else
           if R_i64 = input
           then FStar_UInt8.uint_to_t (Prims.of_int (126))
           else
             if R_f32 = input
             then FStar_UInt8.uint_to_t (Prims.of_int (125))
             else FStar_UInt8.uint_to_t (Prims.of_int (124)))
let (blocktype_serializer32 : blocktype -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_blocktype_key x
let (blocktype_size32 : blocktype -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one