open Prims
type constexpr = Wasm_Parse_Instr.instr Prims.list


let (check_constexpr_list_bytesize :
  Wasm_Parse_Instr.instr Prims.list -> Prims.bool) =
  fun l ->
    let x =
      match let uu___ =
              C_Loops.total_while_gen () ()
                (fun uu___1 -> match uu___1 with | (x1, uu___2) -> x1)
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2, x1) ->
                       let uu___3 = x1 in
                       (match uu___3 with
                        | (len, rem) ->
                            (match rem with
                             | [] -> (false, x1)
                             | a::q ->
                                 let sza = Wasm_Parse_Instr.instr_size32 a in
                                 let len' =
                                   if
                                     FStar_UInt32.lt
                                       (FStar_UInt32.sub
                                          (FStar_UInt32.uint_to_t
                                             (Prims.parse_int "4294967295"))
                                          sza) len
                                   then
                                     FStar_UInt32.uint_to_t
                                       (Prims.parse_int "4294967295")
                                   else FStar_UInt32.add len sza in
                                 if
                                   len' =
                                     (FStar_UInt32.uint_to_t
                                        (Prims.parse_int "4294967295"))
                                 then
                                   (false,
                                     ((FStar_UInt32.uint_to_t
                                         (Prims.parse_int "4294967295")), []))
                                 else (true, (len', q)))))
                (true, ((FStar_UInt32.uint_to_t Prims.int_zero), l)) in
            match uu___ with | (uu___1, res) -> res
      with
      | (len, uu___) -> len in
    (FStar_UInt32.lte (FStar_UInt32.uint_to_t Prims.int_zero) x) &&
      (FStar_UInt32.lte x (FStar_UInt32.uint_to_t (Prims.of_int (1023))))
type constexpr' =
  (unit, unit, unit, Wasm_Parse_Instr.instr Prims.list, unit, unit)
    LowParse_Spec_VLData.parse_bounded_vldata_strong_t
let (synth_constexpr : constexpr' -> constexpr) = fun x -> x
let (synth_constexpr_recip : constexpr -> constexpr') = fun x -> x
let (constexpr_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (constexpr * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match let res =
            match match match LowParse_SLow_BoundedInt.parse32_bounded_integer_2
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
                                         (Prims.of_int (1023))) v))
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
                               (match match let accu =
                                              let uu___1 =
                                                C_Loops.total_while_gen () ()
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | (x, uu___3) -> x)
                                                  (fun uu___2 ->
                                                     match uu___2 with
                                                     | (uu___3, x) ->
                                                         let uu___4 = x in
                                                         (match uu___4 with
                                                          | FStar_Pervasives_Native.Some
                                                              (input'1,
                                                               accu')
                                                              ->
                                                              let len =
                                                                FStar_Bytes.len
                                                                  input'1 in
                                                              if
                                                                len =
                                                                  (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                              then (false, x)
                                                              else
                                                                (match 
                                                                   Wasm_Parse_Instr.instr_parser32
                                                                    input'1
                                                                 with
                                                                 | FStar_Pervasives_Native.Some
                                                                    (v1,
                                                                    consumed)
                                                                    ->
                                                                    if
                                                                    consumed
                                                                    =
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_zero)
                                                                    then
                                                                    (false,
                                                                    FStar_Pervasives_Native.None)
                                                                    else
                                                                    (let input''
                                                                    =
                                                                    FStar_Bytes.slice
                                                                    input'1
                                                                    consumed
                                                                    len in
                                                                    (true,
                                                                    (FStar_Pervasives_Native.Some
                                                                    (input'',
                                                                    (v1 ::
                                                                    accu')))))
                                                                 | FStar_Pervasives_Native.None
                                                                    ->
                                                                    (false,
                                                                    FStar_Pervasives_Native.None))))
                                                  (true,
                                                    (FStar_Pervasives_Native.Some
                                                       ((FStar_Bytes.slice
                                                           input'
                                                           (FStar_UInt32.uint_to_t
                                                              Prims.int_zero)
                                                           v), []))) in
                                              match uu___1 with
                                              | (uu___2, res1) -> res1 in
                                            match accu with
                                            | FStar_Pervasives_Native.None ->
                                                FStar_Pervasives_Native.None
                                            | FStar_Pervasives_Native.Some
                                                (uu___1, accu') ->
                                                FStar_Pervasives_Native.Some
                                                  (LowParse_SLow_List.list_rev
                                                     accu')
                                      with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some res1 ->
                                          FStar_Pervasives_Native.Some
                                            (res1,
                                              (FStar_Bytes.len
                                                 (FStar_Bytes.slice input'
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero) v)))
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
let (constexpr_serializer32 : constexpr -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x = input in
    let pl =
      let uu___ =
        let uu___1 =
          C_Loops.total_while_gen () ()
            (fun uu___2 -> match uu___2 with | (x1, uu___3) -> x1)
            (fun uu___2 ->
               match uu___2 with
               | (uu___3, x1) ->
                   let uu___4 = x1 in
                   (match uu___4 with
                    | (accu, input') ->
                        (match input' with
                         | [] -> (false, x1)
                         | a::q ->
                             let sa = Wasm_Parse_Instr.instr_serializer32 a in
                             let accu' = FStar_Bytes.append accu sa in
                             (true, (accu', q)))))
            (true, (FStar_Bytes.empty_bytes, x)) in
        match uu___1 with | (uu___2, res) -> res in
      match uu___ with | (res, uu___1) -> res in
    let len = FStar_Bytes.len pl in
    let slen = LowParse_SLow_BoundedInt.serialize32_bounded_integer_2 len in
    let res = FStar_Bytes.append slen pl in res
let (constexpr_size32 : constexpr -> FStar_UInt32.t) =
  fun input ->
    let len =
      match let uu___ =
              C_Loops.total_while_gen () ()
                (fun uu___1 -> match uu___1 with | (x, uu___2) -> x)
                (fun uu___1 ->
                   match uu___1 with
                   | (uu___2, x) ->
                       let uu___3 = x in
                       (match uu___3 with
                        | (len1, rem) ->
                            (match rem with
                             | [] -> (false, x)
                             | a::q ->
                                 let sza = Wasm_Parse_Instr.instr_size32 a in
                                 let len' =
                                   if
                                     FStar_UInt32.lt
                                       (FStar_UInt32.sub
                                          (FStar_UInt32.uint_to_t
                                             (Prims.parse_int "4294967295"))
                                          sza) len1
                                   then
                                     FStar_UInt32.uint_to_t
                                       (Prims.parse_int "4294967295")
                                   else FStar_UInt32.add len1 sza in
                                 if
                                   len' =
                                     (FStar_UInt32.uint_to_t
                                        (Prims.parse_int "4294967295"))
                                 then
                                   (false,
                                     ((FStar_UInt32.uint_to_t
                                         (Prims.parse_int "4294967295")), []))
                                 else (true, (len', q)))))
                (true, ((FStar_UInt32.uint_to_t Prims.int_zero), input)) in
            match uu___ with | (uu___1, res) -> res
      with
      | (len1, uu___) -> len1 in
    FStar_UInt32.add (FStar_UInt32.uint_to_t (Prims.of_int (2))) len
