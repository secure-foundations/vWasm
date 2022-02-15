open Prims




type ('t, 'l, 'b, 'x) list_rev_inv = Obj.t
let list_rev : 't . 't Prims.list -> 't Prims.list =
  fun l ->
    match l with
    | [] -> []
    | uu___ ->
        let uu___1 =
          let uu___2 =
            C_Loops.total_while_gen () ()
              (fun uu___3 -> match uu___3 with | (x, uu___4) -> x)
              (fun uu___3 ->
                 match uu___3 with
                 | (uu___4, x) ->
                     (match x with
                      | (rem, acc) ->
                          (match rem with
                           | [] -> (false, (rem, acc))
                           | a::q -> (true, (q, (a :: acc))))))
              (true, (l, [])) in
          match uu___2 with | (uu___3, res) -> res in
        (match uu___1 with | (uu___2, l') -> l')
type ('k, 't, 'p, 'p32, 'input, 'b, 'x) parse_list_tailrec_inv = Obj.t

let (parse_list_tailrec_body :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_SLow_Base.bytes32 ->
            (LowParse_SLow_Base.bytes32 * Obj.t Prims.list)
              FStar_Pervasives_Native.option ->
              (Prims.bool * (LowParse_SLow_Base.bytes32 * Obj.t Prims.list)
                FStar_Pervasives_Native.option))
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun input ->
            fun x ->
              let uu___ = x in
              match uu___ with
              | FStar_Pervasives_Native.Some (input', accu') ->
                  let len = FStar_Bytes.len input' in
                  if len = (FStar_UInt32.uint_to_t Prims.int_zero)
                  then (false, x)
                  else
                    (match p32 input' with
                     | FStar_Pervasives_Native.Some (v, consumed) ->
                         if
                           consumed = (FStar_UInt32.uint_to_t Prims.int_zero)
                         then (false, FStar_Pervasives_Native.None)
                         else
                           (let input'' =
                              FStar_Bytes.slice input' consumed len in
                            (true,
                              (FStar_Pervasives_Native.Some
                                 (input'', (v :: accu')))))
                     | FStar_Pervasives_Native.None ->
                         (false, FStar_Pervasives_Native.None))
let (parse_list_tailrec :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_SLow_Base.bytes32 ->
            Obj.t Prims.list FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun input ->
            let accu =
              let uu___ =
                C_Loops.total_while_gen () ()
                  (fun uu___1 -> match uu___1 with | (x, uu___2) -> x)
                  (fun uu___1 ->
                     match uu___1 with
                     | (uu___2, x) ->
                         let uu___3 = x in
                         (match uu___3 with
                          | FStar_Pervasives_Native.Some (input', accu') ->
                              let len = FStar_Bytes.len input' in
                              if
                                len = (FStar_UInt32.uint_to_t Prims.int_zero)
                              then (false, x)
                              else
                                (match p32 input' with
                                 | FStar_Pervasives_Native.Some (v, consumed)
                                     ->
                                     if
                                       consumed =
                                         (FStar_UInt32.uint_to_t
                                            Prims.int_zero)
                                     then
                                       (false, FStar_Pervasives_Native.None)
                                     else
                                       (let input'' =
                                          FStar_Bytes.slice input' consumed
                                            len in
                                        (true,
                                          (FStar_Pervasives_Native.Some
                                             (input'', (v :: accu')))))
                                 | FStar_Pervasives_Native.None ->
                                     (false, FStar_Pervasives_Native.None))))
                  (true, (FStar_Pervasives_Native.Some (input, []))) in
              match uu___ with | (uu___1, res) -> res in
            match accu with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (uu___, accu') ->
                FStar_Pervasives_Native.Some (list_rev accu')
let (parse32_list :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_SLow_Base.bytes32 ->
            (Obj.t Prims.list * FStar_UInt32.t)
              FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun input ->
            match let accu =
                    let uu___ =
                      C_Loops.total_while_gen () ()
                        (fun uu___1 -> match uu___1 with | (x, uu___2) -> x)
                        (fun uu___1 ->
                           match uu___1 with
                           | (uu___2, x) ->
                               let uu___3 = x in
                               (match uu___3 with
                                | FStar_Pervasives_Native.Some
                                    (input', accu') ->
                                    let len = FStar_Bytes.len input' in
                                    if
                                      len =
                                        (FStar_UInt32.uint_to_t
                                           Prims.int_zero)
                                    then (false, x)
                                    else
                                      (match p32 input' with
                                       | FStar_Pervasives_Native.Some
                                           (v, consumed) ->
                                           if
                                             consumed =
                                               (FStar_UInt32.uint_to_t
                                                  Prims.int_zero)
                                           then
                                             (false,
                                               FStar_Pervasives_Native.None)
                                           else
                                             (let input'' =
                                                FStar_Bytes.slice input'
                                                  consumed len in
                                              (true,
                                                (FStar_Pervasives_Native.Some
                                                   (input'', (v :: accu')))))
                                       | FStar_Pervasives_Native.None ->
                                           (false,
                                             FStar_Pervasives_Native.None))))
                        (true, (FStar_Pervasives_Native.Some (input, []))) in
                    match uu___ with | (uu___1, res) -> res in
                  match accu with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some (uu___, accu') ->
                      FStar_Pervasives_Native.Some (list_rev accu')
            with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some res ->
                FStar_Pervasives_Native.Some (res, (FStar_Bytes.len input))


type ('t, 'k, 'p, 's, 's32, 'input, 'continue,
  'x) partial_serialize32_list'_inv = unit

let partial_serialize32_list'_body :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('t -> LowParse_SLow_Base.bytes32) ->
            't Prims.list ->
              (LowParse_SLow_Base.bytes32 * 't Prims.list) ->
                (Prims.bool * (LowParse_SLow_Base.bytes32 * 't Prims.list))
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun input ->
            fun x ->
              let uu___ = x in
              match uu___ with
              | (accu, input') ->
                  (match input' with
                   | [] -> (false, x)
                   | a::q ->
                       let sa = s32 a in
                       let accu' = FStar_Bytes.append accu sa in
                       (true, (accu', q)))

let partial_serialize32_list :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('t -> LowParse_SLow_Base.bytes32) ->
            unit -> 't Prims.list -> LowParse_SLow_Base.bytes32
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun u ->
            fun input ->
              let uu___ =
                let uu___1 =
                  C_Loops.total_while_gen () ()
                    (fun uu___2 -> match uu___2 with | (x, uu___3) -> x)
                    (fun uu___2 ->
                       match uu___2 with
                       | (uu___3, x) ->
                           let uu___4 = x in
                           (match uu___4 with
                            | (accu, input') ->
                                (match input' with
                                 | [] -> (false, x)
                                 | a::q ->
                                     let sa = s32 a in
                                     let accu' = FStar_Bytes.append accu sa in
                                     (true, (accu', q)))))
                    (true, (FStar_Bytes.empty_bytes, input)) in
                match uu___1 with | (uu___2, res) -> res in
              match uu___ with | (res, uu___1) -> res
type ('t, 'k, 'p, 's, 's32, 'u, 'input, 'continue, 'accu) size32_list_inv =
  Obj.t

let size32_list_body :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('t -> FStar_UInt32.t) ->
            unit ->
              't Prims.list ->
                (FStar_UInt32.t * 't Prims.list) ->
                  (Prims.bool * (FStar_UInt32.t * 't Prims.list))
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun u ->
            fun input ->
              fun accu ->
                let uu___ = accu in
                match uu___ with
                | (len, rem) ->
                    (match rem with
                     | [] -> (false, accu)
                     | a::q ->
                         let sza = s32 a in
                         let len' =
                           if
                             FStar_UInt32.lt
                               (FStar_UInt32.sub
                                  (FStar_UInt32.uint_to_t
                                     (Prims.parse_int "4294967295")) sza) len
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
                         else (true, (len', q)))
let size32_list :
  't .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          ('t -> FStar_UInt32.t) -> unit -> 't Prims.list -> FStar_UInt32.t
  =
  fun k ->
    fun p ->
      fun s ->
        fun s32 ->
          fun u ->
            fun input ->
              match let uu___ =
                      C_Loops.total_while_gen () ()
                        (fun uu___1 -> match uu___1 with | (x, uu___2) -> x)
                        (fun uu___1 ->
                           match uu___1 with
                           | (uu___2, x) ->
                               let uu___3 = x in
                               (match uu___3 with
                                | (len, rem) ->
                                    (match rem with
                                     | [] -> (false, x)
                                     | a::q ->
                                         let sza = s32 a in
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
                                                 (Prims.parse_int "4294967295")),
                                               []))
                                         else (true, (len', q)))))
                        (true,
                          ((FStar_UInt32.uint_to_t Prims.int_zero), input)) in
                    match uu___ with | (uu___1, res) -> res
              with
              | (len, uu___) -> len