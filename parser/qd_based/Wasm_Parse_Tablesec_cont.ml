open Prims
type tablesec_cont = Wasm_Parse_Aux_vectable.aux_vectable
let (check_tablesec_cont_bytesize :
  Wasm_Parse_Aux_vectable.aux_vectable -> Prims.bool) =
  fun x ->
    let l = Wasm_Parse_Aux_vectable.aux_vectable_size32 x in
    (FStar_UInt32.lte (FStar_UInt32.uint_to_t Prims.int_zero) l) &&
      (FStar_UInt32.lte l
         (FStar_UInt32.uint_to_t (Prims.parse_int "16777215")))
type tablesec_cont' =
  (unit, unit, unit, Wasm_Parse_Aux_vectable.aux_vectable, unit, unit)
    LowParse_Spec_VLData.parse_bounded_vldata_strong_t
let (synth_tablesec_cont : tablesec_cont' -> tablesec_cont) = fun x -> x
let (synth_tablesec_cont_recip : tablesec_cont -> tablesec_cont') =
  fun x -> x
let (tablesec_cont'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (tablesec_cont' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    let res =
      match match match LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                          input
                  with
                  | FStar_Pervasives_Native.Some (v, consumed) ->
                      if
                        Prims.op_Negation
                          ((FStar_UInt32.lt v
                              (FStar_UInt32.uint_to_t Prims.int_zero))
                             ||
                             (FStar_UInt32.lt
                                (FStar_UInt32.uint_to_t
                                   (Prims.parse_int "16777215")) v))
                      then FStar_Pervasives_Native.Some (v, consumed)
                      else FStar_Pervasives_Native.None
                  | uu___ -> FStar_Pervasives_Native.None
            with
            | FStar_Pervasives_Native.Some (v, l) ->
                let input' =
                  FStar_Bytes.slice input l (FStar_Bytes.len input) in
                (match if FStar_UInt32.lt (FStar_Bytes.len input') v
                       then FStar_Pervasives_Native.None
                       else
                         (match Wasm_Parse_Aux_vectable.aux_vectable_parser32
                                  (FStar_Bytes.slice input'
                                     (FStar_UInt32.uint_to_t Prims.int_zero)
                                     v)
                          with
                          | FStar_Pervasives_Native.Some (v1, consumed) ->
                              if consumed = v
                              then
                                FStar_Pervasives_Native.Some (v1, consumed)
                              else FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None)
                 with
                 | FStar_Pervasives_Native.Some (v', l') ->
                     FStar_Pervasives_Native.Some
                       (v', (FStar_UInt32.add l l'))
                 | uu___ -> FStar_Pervasives_Native.None)
            | uu___ -> FStar_Pervasives_Native.None
      with
      | FStar_Pervasives_Native.Some (x, consumed) ->
          FStar_Pervasives_Native.Some (x, consumed)
      | uu___ -> FStar_Pervasives_Native.None in
    match res with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (x, consumed) ->
        let x1 = x in FStar_Pervasives_Native.Some (x1, consumed)
let (tablesec_cont_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (tablesec_cont * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match let res =
            match match match LowParse_SLow_BoundedInt.parse32_bounded_integer_3
                                input
                        with
                        | FStar_Pervasives_Native.Some (v, consumed) ->
                            if
                              Prims.op_Negation
                                ((FStar_UInt32.lt v
                                    (FStar_UInt32.uint_to_t Prims.int_zero))
                                   ||
                                   (FStar_UInt32.lt
                                      (FStar_UInt32.uint_to_t
                                         (Prims.parse_int "16777215")) v))
                            then FStar_Pervasives_Native.Some (v, consumed)
                            else FStar_Pervasives_Native.None
                        | uu___ -> FStar_Pervasives_Native.None
                  with
                  | FStar_Pervasives_Native.Some (v, l) ->
                      let input' =
                        FStar_Bytes.slice input l (FStar_Bytes.len input) in
                      (match if FStar_UInt32.lt (FStar_Bytes.len input') v
                             then FStar_Pervasives_Native.None
                             else
                               (match Wasm_Parse_Aux_vectable.aux_vectable_parser32
                                        (FStar_Bytes.slice input'
                                           (FStar_UInt32.uint_to_t
                                              Prims.int_zero) v)
                                with
                                | FStar_Pervasives_Native.Some (v1, consumed)
                                    ->
                                    if consumed = v
                                    then
                                      FStar_Pervasives_Native.Some
                                        (v1, consumed)
                                    else FStar_Pervasives_Native.None
                                | FStar_Pervasives_Native.None ->
                                    FStar_Pervasives_Native.None)
                       with
                       | FStar_Pervasives_Native.Some (v', l') ->
                           FStar_Pervasives_Native.Some
                             (v', (FStar_UInt32.add l l'))
                       | uu___ -> FStar_Pervasives_Native.None)
                  | uu___ -> FStar_Pervasives_Native.None
            with
            | FStar_Pervasives_Native.Some (x, consumed) ->
                FStar_Pervasives_Native.Some (x, consumed)
            | uu___ -> FStar_Pervasives_Native.None in
          match res with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (x, consumed) ->
              let x1 = x in FStar_Pervasives_Native.Some (x1, consumed)
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some (v1, consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (tablesec_cont_serializer32 :
  tablesec_cont -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = input in
    let pl = Wasm_Parse_Aux_vectable.aux_vectable_serializer32 x in
    let len = FStar_Bytes.len pl in
    let slen = LowParse_SLow_BoundedInt.serialize32_bounded_integer_3 len in
    let res = FStar_Bytes.append slen pl in res
let (tablesec_cont_size32 : tablesec_cont -> FStar_UInt32.t) =
  fun input ->
    let len = Wasm_Parse_Aux_vectable.aux_vectable_size32 input in
    FStar_UInt32.add (FStar_UInt32.uint_to_t (Prims.of_int (3))) len
