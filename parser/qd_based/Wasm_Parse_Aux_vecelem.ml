open Prims
type aux_vecelem = Wasm_Parse_Elem.elem Prims.list



let (aux_vecelem_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (aux_vecelem * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match LowParse_SLow_Int.parse32_u32 input with
                | FStar_Pervasives_Native.Some (v, consumed) ->
                    if
                      Prims.op_Negation
                        ((FStar_UInt32.lt v
                            (FStar_UInt32.uint_to_t Prims.int_zero))
                           ||
                           (FStar_UInt32.lt
                              (FStar_UInt32.uint_to_t (Prims.of_int (16383)))
                              v))
                    then FStar_Pervasives_Native.Some (v, consumed)
                    else FStar_Pervasives_Native.None
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v1, consumed) ->
              FStar_Pervasives_Native.Some (v1, consumed)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match match let res =
                       let uu___ =
                         C_Loops.total_while_gen () ()
                           (fun uu___1 ->
                              match uu___1 with | (x, uu___2) -> x)
                           (fun uu___1 ->
                              match uu___1 with
                              | (uu___2, x) ->
                                  (match x with
                                   | FStar_Pervasives_Native.Some
                                       (input'1, i, accu', consumed') ->
                                       if i = v
                                       then (false, x)
                                       else
                                         (match Wasm_Parse_Elem.elem_parser32
                                                  input'1
                                          with
                                          | FStar_Pervasives_Native.None ->
                                              (false,
                                                FStar_Pervasives_Native.None)
                                          | FStar_Pervasives_Native.Some
                                              (y, consumed1) ->
                                              let input2 =
                                                FStar_Bytes.slice input'1
                                                  consumed1
                                                  (FStar_Bytes.len input'1) in
                                              (true,
                                                (FStar_Pervasives_Native.Some
                                                   (input2,
                                                     (FStar_UInt32.add i
                                                        (FStar_UInt32.uint_to_t
                                                           Prims.int_one)),
                                                     (y :: accu'),
                                                     (FStar_UInt32.add
                                                        consumed' consumed1)))))))
                           (true,
                             (FStar_Pervasives_Native.Some
                                (input',
                                  (FStar_UInt32.uint_to_t Prims.int_zero),
                                  [],
                                  (FStar_UInt32.uint_to_t Prims.int_zero)))) in
                       match uu___ with | (uu___1, res1) -> res1 in
                     match res with
                     | FStar_Pervasives_Native.Some
                         (uu___, uu___1, accu, consumed) ->
                         FStar_Pervasives_Native.Some
                           ((LowParse_SLow_List.list_rev accu), consumed)
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
               with
               | FStar_Pervasives_Native.Some (v1, consumed) ->
                   FStar_Pervasives_Native.Some (v1, consumed)
               | uu___ -> FStar_Pervasives_Native.None
         with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some (v', (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (aux_vecelem_serializer32 : aux_vecelem -> LowParse_SLow_Base.bytes32) =
  fun x ->
    let ln =
      match let uu___ =
              C_Loops.total_while_gen () ()
                (fun uu___1 -> match uu___1 with | (x1, uu___2) -> x1)
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2, x1) ->
                       (match x1 with
                        | (len, l') ->
                            (match l' with
                             | [] -> (false, x1)
                             | uu___3::q ->
                                 (true,
                                   ((FStar_UInt32.add len
                                       (FStar_UInt32.uint_to_t Prims.int_one)),
                                     q)))))
                (true, ((FStar_UInt32.uint_to_t Prims.int_zero), x)) in
            match uu___ with | (uu___1, res) -> res
      with
      | (len, uu___) -> len in
    let sn = LowParse_SLow_Int.serialize32_u32 ln in
    let sl =
      let x1 =
        let uu___ =
          C_Loops.total_while_gen () ()
            (fun uu___1 -> match uu___1 with | (x2, uu___2) -> x2)
            (fun uu___1 ->
               match uu___1 with
               | (uu___2, x2) ->
                   (match x2 with
                    | ([], res) -> (false, x2)
                    | (a::q, res) ->
                        let sa = Wasm_Parse_Elem.elem_serializer32 a in
                        let res' = FStar_Bytes.append res sa in
                        (true, (q, res'))))
            (true, (x, FStar_Bytes.empty_bytes)) in
        match uu___ with | (uu___1, res) -> res in
      match x1 with | (uu___, res) -> res in
    FStar_Bytes.append sn sl
let (aux_vecelem_size32 : aux_vecelem -> FStar_UInt32.t) =
  fun x ->
    let ln =
      match let uu___ =
              C_Loops.total_while_gen () ()
                (fun uu___1 -> match uu___1 with | (x1, uu___2) -> x1)
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2, x1) ->
                       (match x1 with
                        | (len, l') ->
                            (match l' with
                             | [] -> (false, x1)
                             | uu___3::q ->
                                 (true,
                                   ((FStar_UInt32.add len
                                       (FStar_UInt32.uint_to_t Prims.int_one)),
                                     q)))))
                (true, ((FStar_UInt32.uint_to_t Prims.int_zero), x)) in
            match uu___ with | (uu___1, res) -> res
      with
      | (len, uu___) -> len in
    let sn = FStar_UInt32.uint_to_t (Prims.of_int (4)) in
    let sl =
      let x1 =
        let uu___ =
          C_Loops.total_while_gen () ()
            (fun uu___1 -> match uu___1 with | (x2, uu___2) -> x2)
            (fun uu___1 ->
               match uu___1 with
               | (uu___2, x2) ->
                   (match x2 with
                    | ([], res) -> (false, x2)
                    | (a::q, res) ->
                        let sa = Wasm_Parse_Elem.elem_size32 a in
                        let res' = FStar_UInt32.add res sa in
                        (true, (q, res'))))
            (true, (x, (FStar_UInt32.uint_to_t Prims.int_zero))) in
        match uu___ with | (uu___1, res) -> res in
      match x1 with | (uu___, res) -> res in
    FStar_UInt32.add sn sl