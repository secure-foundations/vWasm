open Prims



type ('n, 'k, 't, 'p, 'accu, 'input, 'b, 'x) parse_nlist_tailrec_inv = Obj.t

let (parse_nlist_body :
  FStar_UInt32.t ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            LowParse_SLow_Base.bytes32 ->
              (LowParse_SLow_Base.bytes32 * FStar_UInt32.t * Obj.t Prims.list
                * FStar_UInt32.t) FStar_Pervasives_Native.option ->
                (Prims.bool * (LowParse_SLow_Base.bytes32 * FStar_UInt32.t *
                  Obj.t Prims.list * FStar_UInt32.t)
                  FStar_Pervasives_Native.option))
  =
  fun n ->
    fun k ->
      fun t ->
        fun p ->
          fun p32 ->
            fun input ->
              fun x ->
                match x with
                | FStar_Pervasives_Native.Some (input', i, accu', consumed')
                    ->
                    if i = n
                    then (false, x)
                    else
                      (match p32 input' with
                       | FStar_Pervasives_Native.None ->
                           (false, FStar_Pervasives_Native.None)
                       | FStar_Pervasives_Native.Some (y, consumed1) ->
                           let input2 =
                             FStar_Bytes.slice input' consumed1
                               (FStar_Bytes.len input') in
                           (true,
                             (FStar_Pervasives_Native.Some
                                (input2,
                                  (FStar_UInt32.add i
                                     (FStar_UInt32.uint_to_t Prims.int_one)),
                                  (y :: accu'),
                                  (FStar_UInt32.add consumed' consumed1)))))
let (parse32_nlist :
  FStar_UInt32.t ->
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
  fun n ->
    fun k ->
      fun t ->
        fun p ->
          fun p32 ->
            fun input ->
              let res =
                let uu___ =
                  C_Loops.total_while_gen () ()
                    (fun uu___1 -> match uu___1 with | (x, uu___2) -> x)
                    (fun uu___1 ->
                       match uu___1 with
                       | (uu___2, x) ->
                           (match x with
                            | FStar_Pervasives_Native.Some
                                (input', i, accu', consumed') ->
                                if i = n
                                then (false, x)
                                else
                                  (match p32 input' with
                                   | FStar_Pervasives_Native.None ->
                                       (false, FStar_Pervasives_Native.None)
                                   | FStar_Pervasives_Native.Some
                                       (y, consumed1) ->
                                       let input2 =
                                         FStar_Bytes.slice input' consumed1
                                           (FStar_Bytes.len input') in
                                       (true,
                                         (FStar_Pervasives_Native.Some
                                            (input2,
                                              (FStar_UInt32.add i
                                                 (FStar_UInt32.uint_to_t
                                                    Prims.int_one)), (y ::
                                              accu'),
                                              (FStar_UInt32.add consumed'
                                                 consumed1)))))))
                    (true,
                      (FStar_Pervasives_Native.Some
                         (input, (FStar_UInt32.uint_to_t Prims.int_zero), [],
                           (FStar_UInt32.uint_to_t Prims.int_zero)))) in
                match uu___ with | (uu___1, res1) -> res1 in
              match res with
              | FStar_Pervasives_Native.Some (uu___, uu___1, accu, consumed)
                  ->
                  FStar_Pervasives_Native.Some
                    ((LowParse_SLow_List.list_rev accu), consumed)
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
type ('n, 'k) serialize32_nlist_precond = unit
let (serialize32_nlist :
  Prims.nat ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              unit -> Obj.t Prims.list -> LowParse_SLow_Base.bytes32)
  =
  fun n ->
    fun k ->
      fun t ->
        fun p ->
          fun s ->
            fun s32 ->
              fun u ->
                fun input ->
                  let x =
                    let uu___ =
                      C_Loops.total_while_gen () ()
                        (fun uu___1 -> match uu___1 with | (x1, uu___2) -> x1)
                        (fun uu___1 ->
                           match uu___1 with
                           | (uu___2, x1) ->
                               (match x1 with
                                | ([], res) -> (false, x1)
                                | (a::q, res) ->
                                    let sa = s32 a in
                                    let res' = FStar_Bytes.append res sa in
                                    (true, (q, res'))))
                        (true, (input, FStar_Bytes.empty_bytes)) in
                    match uu___ with | (uu___1, res) -> res in
                  match x with | (uu___, res) -> res
let (size32_nlist :
  Prims.nat ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> FStar_UInt32.t) ->
              unit -> Obj.t Prims.list -> FStar_UInt32.t)
  =
  fun n ->
    fun k ->
      fun t ->
        fun p ->
          fun s ->
            fun s32 ->
              fun u ->
                fun input ->
                  let x =
                    let uu___ =
                      C_Loops.total_while_gen () ()
                        (fun uu___1 -> match uu___1 with | (x1, uu___2) -> x1)
                        (fun uu___1 ->
                           match uu___1 with
                           | (uu___2, x1) ->
                               (match x1 with
                                | ([], res) -> (false, x1)
                                | (a::q, res) ->
                                    let sa = s32 a in
                                    let res' = FStar_UInt32.add res sa in
                                    (true, (q, res'))))
                        (true,
                          (input, (FStar_UInt32.uint_to_t Prims.int_zero))) in
                    match uu___ with | (uu___1, res) -> res in
                  match x with | (uu___, res) -> res
let (parse32_vclist_payload :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              FStar_UInt32.t ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t Prims.list * FStar_UInt32.t)
                    FStar_Pervasives_Native.option)
  =
  fun min ->
    fun max ->
      fun k ->
        fun t ->
          fun p ->
            fun p32 ->
              fun n ->
                fun x ->
                  match let res =
                          let uu___ =
                            C_Loops.total_while_gen () ()
                              (fun uu___1 ->
                                 match uu___1 with | (x1, uu___2) -> x1)
                              (fun uu___1 ->
                                 match uu___1 with
                                 | (uu___2, x1) ->
                                     (match x1 with
                                      | FStar_Pervasives_Native.Some
                                          (input', i, accu', consumed') ->
                                          if i = n
                                          then (false, x1)
                                          else
                                            (match p32 input' with
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 (false,
                                                   FStar_Pervasives_Native.None)
                                             | FStar_Pervasives_Native.Some
                                                 (y, consumed1) ->
                                                 let input2 =
                                                   FStar_Bytes.slice input'
                                                     consumed1
                                                     (FStar_Bytes.len input') in
                                                 (true,
                                                   (FStar_Pervasives_Native.Some
                                                      (input2,
                                                        (FStar_UInt32.add i
                                                           (FStar_UInt32.uint_to_t
                                                              Prims.int_one)),
                                                        (y :: accu'),
                                                        (FStar_UInt32.add
                                                           consumed'
                                                           consumed1)))))))
                              (true,
                                (FStar_Pervasives_Native.Some
                                   (x,
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
let (parse32_vclist :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (FStar_UInt32.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
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
  fun min ->
    fun max ->
      fun lk ->
        fun lp ->
          fun lp32 ->
            fun k ->
              fun t ->
                fun p ->
                  fun p32 ->
                    fun input ->
                      match match match lp32 input with
                                  | FStar_Pervasives_Native.Some
                                      (v, consumed) ->
                                      if
                                        Prims.op_Negation
                                          ((FStar_UInt32.lt v min) ||
                                             (FStar_UInt32.lt max v))
                                      then
                                        FStar_Pervasives_Native.Some
                                          (v, consumed)
                                      else FStar_Pervasives_Native.None
                                  | uu___ -> FStar_Pervasives_Native.None
                            with
                            | FStar_Pervasives_Native.Some (v1, consumed) ->
                                FStar_Pervasives_Native.Some (v1, consumed)
                            | uu___ -> FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (v, l) ->
                          let input' =
                            FStar_Bytes.slice input l (FStar_Bytes.len input) in
                          (match match let res =
                                         let uu___ =
                                           C_Loops.total_while_gen () ()
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | (x, uu___2) -> x)
                                             (fun uu___1 ->
                                                match uu___1 with
                                                | (uu___2, x) ->
                                                    (match x with
                                                     | FStar_Pervasives_Native.Some
                                                         (input'1, i, accu',
                                                          consumed')
                                                         ->
                                                         if i = v
                                                         then (false, x)
                                                         else
                                                           (match p32 input'1
                                                            with
                                                            | FStar_Pervasives_Native.None
                                                                ->
                                                                (false,
                                                                  FStar_Pervasives_Native.None)
                                                            | FStar_Pervasives_Native.Some
                                                                (y,
                                                                 consumed1)
                                                                ->
                                                                let input2 =
                                                                  FStar_Bytes.slice
                                                                    input'1
                                                                    consumed1
                                                                    (
                                                                    FStar_Bytes.len
                                                                    input'1) in
                                                                (true,
                                                                  (FStar_Pervasives_Native.Some
                                                                    (input2,
                                                                    (FStar_UInt32.add
                                                                    i
                                                                    (FStar_UInt32.uint_to_t
                                                                    Prims.int_one)),
                                                                    (y ::
                                                                    accu'),
                                                                    (FStar_UInt32.add
                                                                    consumed'
                                                                    consumed1)))))))
                                             (true,
                                               (FStar_Pervasives_Native.Some
                                                  (input',
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero), [],
                                                    (FStar_UInt32.uint_to_t
                                                       Prims.int_zero)))) in
                                         match uu___ with
                                         | (uu___1, res1) -> res1 in
                                       match res with
                                       | FStar_Pervasives_Native.Some
                                           (uu___, uu___1, accu, consumed) ->
                                           FStar_Pervasives_Native.Some
                                             ((LowParse_SLow_List.list_rev
                                                 accu), consumed)
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Pervasives_Native.None
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (v1, consumed) ->
                                     FStar_Pervasives_Native.Some
                                       (v1, consumed)
                                 | uu___ -> FStar_Pervasives_Native.None
                           with
                           | FStar_Pervasives_Native.Some (v', l') ->
                               FStar_Pervasives_Native.Some
                                 (v', (FStar_UInt32.add l l'))
                           | uu___ -> FStar_Pervasives_Native.None)
                      | uu___ -> FStar_Pervasives_Native.None
type ('min, 'max, 'lk, 'k) serialize32_vclist_precond = Obj.t
let list_length32 : 't . 't Prims.list -> FStar_UInt32.t =
  fun l ->
    match let uu___ =
            C_Loops.total_while_gen () ()
              (fun uu___1 -> match uu___1 with | (x, uu___2) -> x)
              (fun uu___1 ->
                 match uu___1 with
                 | (uu___2, x) ->
                     (match x with
                      | (len, l') ->
                          (match l' with
                           | [] -> (false, x)
                           | uu___3::q ->
                               (true,
                                 ((FStar_UInt32.add len
                                     (FStar_UInt32.uint_to_t Prims.int_one)),
                                   q)))))
              (true, ((FStar_UInt32.uint_to_t Prims.int_zero), l)) in
          match uu___ with | (uu___1, res) -> res
    with
    | (len, uu___) -> len
let (serialize32_vclist :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> LowParse_SLow_Base.bytes32) ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t -> LowParse_SLow_Base.bytes32) ->
                        Obj.t Prims.list -> LowParse_SLow_Base.bytes32)
  =
  fun min ->
    fun max ->
      fun lk ->
        fun lp ->
          fun ls ->
            fun ls32 ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun s32 ->
                        fun x ->
                          let ln =
                            match let uu___ =
                                    C_Loops.total_while_gen () ()
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | (x1, uu___2) -> x1)
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | (uu___2, x1) ->
                                             (match x1 with
                                              | (len, l') ->
                                                  (match l' with
                                                   | [] -> (false, x1)
                                                   | uu___3::q ->
                                                       (true,
                                                         ((FStar_UInt32.add
                                                             len
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_one)),
                                                           q)))))
                                      (true,
                                        ((FStar_UInt32.uint_to_t
                                            Prims.int_zero), x)) in
                                  match uu___ with | (uu___1, res) -> res
                            with
                            | (len, uu___) -> len in
                          let sn = ls32 ln in
                          let sl =
                            let x1 =
                              let uu___ =
                                C_Loops.total_while_gen () ()
                                  (fun uu___1 ->
                                     match uu___1 with | (x2, uu___2) -> x2)
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (uu___2, x2) ->
                                         (match x2 with
                                          | ([], res) -> (false, x2)
                                          | (a::q, res) ->
                                              let sa = s32 a in
                                              let res' =
                                                FStar_Bytes.append res sa in
                                              (true, (q, res'))))
                                  (true, (x, FStar_Bytes.empty_bytes)) in
                              match uu___ with | (uu___1, res) -> res in
                            match x1 with | (uu___, res) -> res in
                          FStar_Bytes.append sn sl
let (size32_vclist :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (FStar_UInt32.t -> FStar_UInt32.t) ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  unit ->
                    unit ->
                      (Obj.t -> FStar_UInt32.t) ->
                        Obj.t Prims.list -> FStar_UInt32.t)
  =
  fun min ->
    fun max ->
      fun lk ->
        fun lp ->
          fun ls ->
            fun ls32 ->
              fun k ->
                fun t ->
                  fun p ->
                    fun s ->
                      fun s32 ->
                        fun x ->
                          let ln =
                            match let uu___ =
                                    C_Loops.total_while_gen () ()
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | (x1, uu___2) -> x1)
                                      (fun uu___1 ->
                                         match uu___1 with
                                         | (uu___2, x1) ->
                                             (match x1 with
                                              | (len, l') ->
                                                  (match l' with
                                                   | [] -> (false, x1)
                                                   | uu___3::q ->
                                                       (true,
                                                         ((FStar_UInt32.add
                                                             len
                                                             (FStar_UInt32.uint_to_t
                                                                Prims.int_one)),
                                                           q)))))
                                      (true,
                                        ((FStar_UInt32.uint_to_t
                                            Prims.int_zero), x)) in
                                  match uu___ with | (uu___1, res) -> res
                            with
                            | (len, uu___) -> len in
                          let sn = ls32 ln in
                          let sl =
                            let x1 =
                              let uu___ =
                                C_Loops.total_while_gen () ()
                                  (fun uu___1 ->
                                     match uu___1 with | (x2, uu___2) -> x2)
                                  (fun uu___1 ->
                                     match uu___1 with
                                     | (uu___2, x2) ->
                                         (match x2 with
                                          | ([], res) -> (false, x2)
                                          | (a::q, res) ->
                                              let sa = s32 a in
                                              let res' =
                                                FStar_UInt32.add res sa in
                                              (true, (q, res'))))
                                  (true,
                                    (x,
                                      (FStar_UInt32.uint_to_t Prims.int_zero))) in
                              match uu___ with | (uu___1, res) -> res in
                            match x1 with | (uu___, res) -> res in
                          FStar_UInt32.add sn sl