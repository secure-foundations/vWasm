open Prims
type aux_importdesc_label =
  | Func 
  | Table 
  | Mem 
  | Global 
let (uu___is_Func : aux_importdesc_label -> Prims.bool) =
  fun projectee -> match projectee with | Func -> true | uu___ -> false
let (uu___is_Table : aux_importdesc_label -> Prims.bool) =
  fun projectee -> match projectee with | Table -> true | uu___ -> false
let (uu___is_Mem : aux_importdesc_label -> Prims.bool) =
  fun projectee -> match projectee with | Mem -> true | uu___ -> false
let (uu___is_Global : aux_importdesc_label -> Prims.bool) =
  fun projectee -> match projectee with | Global -> true | uu___ -> false
let (string_of_aux_importdesc_label : aux_importdesc_label -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Func -> "func"
    | Table -> "table"
    | Mem -> "mem"
    | Global -> "global"
let (aux_importdesc_label_enum :
  (aux_importdesc_label, FStar_UInt8.t) LowParse_Spec_Enum.enum) =
  [(Func, (FStar_UInt8.uint_to_t Prims.int_zero));
  (Table, (FStar_UInt8.uint_to_t Prims.int_one));
  (Mem, (FStar_UInt8.uint_to_t (Prims.of_int (2))));
  (Global, (FStar_UInt8.uint_to_t (Prims.of_int (3))))]
let (synth_aux_importdesc_label :
  aux_importdesc_label -> aux_importdesc_label) = fun x -> x
let (synth_aux_importdesc_label_inv :
  aux_importdesc_label -> aux_importdesc_label) = fun x -> x


let (parse32_aux_importdesc_label_key :
  LowParse_SLow_Base.bytes32 ->
    (aux_importdesc_label * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match LowParse_SLow_Int.parse32_u8 input with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some
                ((if (FStar_UInt8.uint_to_t Prims.int_zero) = v1
                  then LowParse_Spec_Enum.Known Func
                  else
                    (let y =
                       if (FStar_UInt8.uint_to_t Prims.int_one) = v1
                       then LowParse_Spec_Enum.Known Table
                       else
                         (let y1 =
                            if
                              (FStar_UInt8.uint_to_t (Prims.of_int (2))) = v1
                            then LowParse_Spec_Enum.Known Mem
                            else
                              (let y2 =
                                 if
                                   (FStar_UInt8.uint_to_t (Prims.of_int (3)))
                                     = v1
                                 then LowParse_Spec_Enum.Known Global
                                 else LowParse_Spec_Enum.Unknown v1 in
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
let (aux_importdesc_label_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_importdesc_label * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match parse32_aux_importdesc_label_key input with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_aux_importdesc_label_key :
  aux_importdesc_label -> LowParse_SLow_Base.bytes32) =
  fun input ->
    LowParse_SLow_Int.serialize32_u8
      (if Func = input
       then FStar_UInt8.uint_to_t Prims.int_zero
       else
         if Table = input
         then FStar_UInt8.uint_to_t Prims.int_one
         else
           if Mem = input
           then FStar_UInt8.uint_to_t (Prims.of_int (2))
           else FStar_UInt8.uint_to_t (Prims.of_int (3)))
let (aux_importdesc_label_serializer32 :
  aux_importdesc_label -> LowParse_SLow_Base.bytes32) =
  fun input -> let x = input in serialize32_aux_importdesc_label_key x
let (aux_importdesc_label_size32 : aux_importdesc_label -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_one