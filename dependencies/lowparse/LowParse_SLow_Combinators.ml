open Prims
let parse32_ret :
  't .
    't ->
      LowParse_SLow_Base.bytes32 ->
        ('t * FStar_UInt32.t) FStar_Pervasives_Native.option
  =
  fun x ->
    fun input ->
      FStar_Pervasives_Native.Some
        (x, (FStar_UInt32.uint_to_t Prims.int_zero))
let (parse32_empty :
  LowParse_SLow_Base.bytes32 ->
    (unit * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    FStar_Pervasives_Native.Some
      ((), (FStar_UInt32.uint_to_t Prims.int_zero))
let serialize32_ret : 't . 't -> unit -> 't -> LowParse_SLow_Base.bytes32 =
  fun v -> fun v_unique -> fun input -> FStar_Bytes.empty_bytes
let (serialize32_empty : unit -> LowParse_SLow_Base.bytes32) =
  fun input -> FStar_Bytes.empty_bytes
let size32_ret : 't . 't -> unit -> 't -> FStar_UInt32.t =
  fun v -> fun v_unique -> fun x -> FStar_UInt32.uint_to_t Prims.int_zero
let (size32_empty : unit -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t Prims.int_zero
let (parse32_false :
  LowParse_SLow_Base.bytes32 ->
    (unit * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = fun uu___ -> FStar_Pervasives_Native.None
let (serialize32_false : unit -> LowParse_SLow_Base.bytes32) =
  fun input -> FStar_Bytes.empty_bytes
let (size32_false : unit -> FStar_UInt32.t) =
  fun input -> FStar_UInt32.uint_to_t Prims.int_zero
let (parse32_and_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                unit ->
                  (Obj.t ->
                     LowParse_SLow_Base.bytes32 ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                    ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun k' ->
            fun t' ->
              fun p' ->
                fun u ->
                  fun p32' ->
                    fun input ->
                      match p32 input with
                      | FStar_Pervasives_Native.Some (v, l) ->
                          let input' =
                            FStar_Bytes.slice input l (FStar_Bytes.len input) in
                          (match p32' v input' with
                           | FStar_Pervasives_Native.Some (v', l') ->
                               FStar_Pervasives_Native.Some
                                 (v', (FStar_UInt32.add l l'))
                           | uu___ -> FStar_Pervasives_Native.None)
                      | uu___ -> FStar_Pervasives_Native.None
let (parse32_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (LowParse_SLow_Base.bytes32 ->
                   (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                  ->
                  LowParse_SLow_Base.bytes32 ->
                    ((Obj.t * Obj.t) * FStar_UInt32.t)
                      FStar_Pervasives_Native.option)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun p1' ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun p2' ->
                  fun input ->
                    match p1' input with
                    | FStar_Pervasives_Native.Some (v, l) ->
                        let input' =
                          FStar_Bytes.slice input l (FStar_Bytes.len input) in
                        (match p2' input' with
                         | FStar_Pervasives_Native.Some (v', l') ->
                             FStar_Pervasives_Native.Some
                               ((v, v'), (FStar_UInt32.add l l'))
                         | uu___ -> FStar_Pervasives_Native.None)
                    | uu___ -> FStar_Pervasives_Native.None

let (serialize32_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t -> LowParse_SLow_Base.bytes32) ->
                      (Obj.t * Obj.t) -> LowParse_SLow_Base.bytes32)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun input ->
                        match input with
                        | (fs, sn) ->
                            let output1 = s1' fs in
                            let output2 = s2' sn in
                            FStar_Bytes.append output1 output2
let (parse32_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_Spec_Base.parser_kind ->
            unit ->
              unit ->
                (Obj.t ->
                   LowParse_SLow_Base.bytes32 ->
                     (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                  ->
                  LowParse_SLow_Base.bytes32 ->
                    ((Obj.t, Obj.t) Prims.dtuple2 * FStar_UInt32.t)
                      FStar_Pervasives_Native.option)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun p1' ->
          fun k2 ->
            fun t2 ->
              fun p2 ->
                fun p2' ->
                  fun input ->
                    match p1' input with
                    | FStar_Pervasives_Native.Some (v, l) ->
                        let input' =
                          FStar_Bytes.slice input l (FStar_Bytes.len input) in
                        (match p2' v input' with
                         | FStar_Pervasives_Native.Some (v', l') ->
                             FStar_Pervasives_Native.Some
                               ((Prims.Mkdtuple2 (v, v')),
                                 (FStar_UInt32.add l l'))
                         | uu___ -> FStar_Pervasives_Native.None)
                    | uu___ -> FStar_Pervasives_Native.None
let (serialize32_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                      (Obj.t, Obj.t) Prims.dtuple2 ->
                        LowParse_SLow_Base.bytes32)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun input ->
                        match input with
                        | Prims.Mkdtuple2 (fs, sn) ->
                            let output1 = s1' fs in
                            let output2 = s2' fs sn in
                            FStar_Bytes.append output1 output2
let (parse32_strengthen :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          unit ->
            unit ->
              LowParse_SLow_Base.bytes32 ->
                (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t1 ->
      fun p1 ->
        fun p1' ->
          fun p2 ->
            fun prf ->
              fun xbytes ->
                match p1' xbytes with
                | FStar_Pervasives_Native.Some (x, consumed) ->
                    FStar_Pervasives_Native.Some (x, consumed)
                | uu___ -> FStar_Pervasives_Native.None
let (parse32_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> Obj.t) ->
              (LowParse_SLow_Base.bytes32 ->
                 (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                ->
                unit ->
                  LowParse_SLow_Base.bytes32 ->
                    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun f2' ->
              fun p1' ->
                fun u ->
                  fun input ->
                    match p1' input with
                    | FStar_Pervasives_Native.Some (v1, consumed) ->
                        FStar_Pervasives_Native.Some ((f2' v1), consumed)
                    | uu___ -> FStar_Pervasives_Native.None
let (parse32_synth' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> Obj.t) ->
            (LowParse_SLow_Base.bytes32 ->
               (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
              ->
              unit ->
                LowParse_SLow_Base.bytes32 ->
                  (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun p1' ->
              fun u ->
                fun input ->
                  match p1' input with
                  | FStar_Pervasives_Native.Some (v1, consumed) ->
                      FStar_Pervasives_Native.Some ((f2 v1), consumed)
                  | uu___ -> FStar_Pervasives_Native.None
let (serialize32_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> LowParse_SLow_Base.bytes32) ->
                unit ->
                  (Obj.t -> Obj.t) ->
                    unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun s1 ->
              fun s1' ->
                fun g1 ->
                  fun g1' -> fun u -> fun input -> let x = g1' input in s1' x
let (serialize32_synth' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> LowParse_SLow_Base.bytes32) ->
                (Obj.t -> Obj.t) ->
                  unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun s1 ->
              fun s1' ->
                fun g1 -> fun u -> fun input -> let x = g1 input in s1' x
let (parse32_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          unit ->
            (Obj.t -> Prims.bool) ->
              LowParse_SLow_Base.bytes32 ->
                (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun f ->
            fun g ->
              fun input ->
                match p32 input with
                | FStar_Pervasives_Native.Some (v, consumed) ->
                    if g v
                    then FStar_Pervasives_Native.Some (v, consumed)
                    else FStar_Pervasives_Native.None
                | uu___ -> FStar_Pervasives_Native.None
let (serialize32_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k ->
    fun t -> fun p -> fun s -> fun s32 -> fun f -> fun input -> s32 input
let (make_constant_size_parser32 :
  Prims.nat ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          unit ->
            (unit FStar_Bytes.lbytes -> Obj.t FStar_Pervasives_Native.option)
              ->
              LowParse_SLow_Base.bytes32 ->
                (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun sz' ->
      fun t ->
        fun f ->
          fun u ->
            fun f' ->
              fun input ->
                if FStar_UInt32.lt (FStar_Bytes.len input) sz'
                then FStar_Pervasives_Native.None
                else
                  (let s' =
                     FStar_Bytes.slice input
                       (FStar_UInt32.uint_to_t Prims.int_zero) sz' in
                   match f' s' with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some v ->
                       FStar_Pervasives_Native.Some (v, sz'))
let (make_total_constant_size_parser32 :
  Prims.nat ->
    FStar_UInt32.t ->
      unit ->
        unit ->
          unit ->
            (unit FStar_Bytes.lbytes -> Obj.t) ->
              LowParse_SLow_Base.bytes32 ->
                (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun sz ->
    fun sz' ->
      fun t ->
        fun f ->
          fun u ->
            fun f' ->
              fun input ->
                if FStar_UInt32.lt (FStar_Bytes.len input) sz'
                then FStar_Pervasives_Native.None
                else
                  (let s' =
                     FStar_Bytes.slice input
                       (FStar_UInt32.uint_to_t Prims.int_zero) sz' in
                   FStar_Pervasives_Native.Some ((f' s'), sz'))
let (size32_nondep_then :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t -> FStar_UInt32.t) ->
                      (Obj.t * Obj.t) -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun x ->
                        match x with
                        | (x1, x2) ->
                            let v1 = s1' x1 in
                            let v2 = s2' x2 in
                            let res =
                              if
                                FStar_UInt32.lt
                                  (FStar_UInt32.sub
                                     (FStar_UInt32.uint_to_t
                                        (Prims.parse_int "4294967295")) v2)
                                  v1
                              then
                                FStar_UInt32.uint_to_t
                                  (Prims.parse_int "4294967295")
                              else FStar_UInt32.add v1 v2 in
                            res
let (size32_dtuple2 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            LowParse_Spec_Base.parser_kind ->
              unit ->
                unit ->
                  unit ->
                    (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                      (Obj.t, Obj.t) Prims.dtuple2 -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 ->
              fun t2 ->
                fun p2 ->
                  fun s2 ->
                    fun s2' ->
                      fun x ->
                        match x with
                        | Prims.Mkdtuple2 (x1, x2) ->
                            let v1 = s1' x1 in
                            let v2 = s2' x1 x2 in
                            let res =
                              if
                                FStar_UInt32.lt
                                  (FStar_UInt32.sub
                                     (FStar_UInt32.uint_to_t
                                        (Prims.parse_int "4294967295")) v2)
                                  v1
                              then
                                FStar_UInt32.uint_to_t
                                  (Prims.parse_int "4294967295")
                              else FStar_UInt32.add v1 v2 in
                            res
let (size32_filter :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit -> (Obj.t -> FStar_UInt32.t) -> unit -> Obj.t -> FStar_UInt32.t)
  = fun k -> fun t -> fun p -> fun s -> fun s32 -> fun f -> fun x -> s32 x
let (size32_synth :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> FStar_UInt32.t) ->
                unit -> (Obj.t -> Obj.t) -> unit -> Obj.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun s1 ->
              fun s1' ->
                fun g1 -> fun g1' -> fun u -> fun input -> s1' (g1' input)
let (size32_synth' :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (Obj.t -> FStar_UInt32.t) ->
                (Obj.t -> Obj.t) -> unit -> Obj.t -> FStar_UInt32.t)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        fun p1 ->
          fun f2 ->
            fun s1 ->
              fun s1' -> fun g1 -> fun u -> fun input -> s1' (g1 input)
let (parse32_compose_context :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Obj.t) ->
          unit ->
            unit ->
              (Obj.t ->
                 LowParse_SLow_Base.bytes32 ->
                   (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
                ->
                Obj.t ->
                  LowParse_SLow_Base.bytes32 ->
                    (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun pk ->
    fun kt1 ->
      fun kt2 ->
        fun f ->
          fun t -> fun p -> fun p32 -> fun k -> fun input -> p32 (f k) input
let (serialize32_compose_context :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Obj.t) ->
          unit ->
            unit ->
              unit ->
                (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                  Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun pk ->
    fun kt1 ->
      fun kt2 ->
        fun f ->
          fun t ->
            fun p ->
              fun s -> fun s32 -> fun k -> fun input -> s32 (f k) input
let (size32_compose_context :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (Obj.t -> Obj.t) ->
          unit ->
            unit ->
              unit ->
                (Obj.t -> Obj.t -> FStar_UInt32.t) ->
                  Obj.t -> Obj.t -> FStar_UInt32.t)
  =
  fun pk ->
    fun kt1 ->
      fun kt2 ->
        fun f ->
          fun t ->
            fun p ->
              fun s -> fun s32 -> fun k -> fun input -> s32 (f k) input
let (parse32_weaken :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (LowParse_SLow_Base.bytes32 ->
             (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            LowParse_SLow_Base.bytes32 ->
              (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = fun k1 -> fun k2 -> fun t -> fun p2 -> fun p2' -> fun x -> p2' x
let (serialize32_weaken :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          unit ->
            (Obj.t -> LowParse_SLow_Base.bytes32) ->
              Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun k1 -> fun k2 -> fun t -> fun p2 -> fun s2 -> fun s2' -> fun x -> s2' x
let (size32_weaken :
  LowParse_Spec_Base.parser_kind ->
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit -> unit -> (Obj.t -> FStar_UInt32.t) -> Obj.t -> FStar_UInt32.t)
  =
  fun k1 -> fun k2 -> fun t -> fun p2 -> fun s2 -> fun s2' -> fun x -> s2' x
let (lift_parser32 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_SLow_Base.bytes32 ->
            (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = fun k -> fun t -> fun f -> fun f32 -> fun x -> f32 x
let (lift_serializer32 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            Obj.t -> LowParse_SLow_Base.bytes32)
  = fun k -> fun t -> fun f -> fun s -> fun s32 -> fun x -> s32 x
let (parse32_tagged_union :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (LowParse_SLow_Base.bytes32 ->
           (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          unit ->
            unit ->
              LowParse_Spec_Base.parser_kind ->
                unit ->
                  (Obj.t ->
                     LowParse_SLow_Base.bytes32 ->
                       (Obj.t * FStar_UInt32.t)
                         FStar_Pervasives_Native.option)
                    ->
                    LowParse_SLow_Base.bytes32 ->
                      (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun kt ->
    fun tag_t ->
      fun pt ->
        fun pt32 ->
          fun data_t ->
            fun tag_of_data ->
              fun k ->
                fun p ->
                  fun p32 ->
                    fun input ->
                      match pt32 input with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some (tg, consumed_tg) ->
                          let input_tg =
                            FStar_Bytes.slice input consumed_tg
                              (FStar_Bytes.len input) in
                          (match p32 tg input_tg with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (x, consumed_x) ->
                               FStar_Pervasives_Native.Some
                                 (x,
                                   (FStar_UInt32.add consumed_tg consumed_x)))
let (serialize32_tagged_union :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> LowParse_SLow_Base.bytes32) ->
            unit ->
              unit ->
                (Obj.t -> Obj.t) ->
                  LowParse_Spec_Base.parser_kind ->
                    unit ->
                      unit ->
                        (Obj.t -> Obj.t -> LowParse_SLow_Base.bytes32) ->
                          unit -> Obj.t -> LowParse_SLow_Base.bytes32)
  =
  fun kt ->
    fun tag_t ->
      fun pt ->
        fun st ->
          fun st32 ->
            fun data_t ->
              fun tag_of_data ->
                fun tag_of_data' ->
                  fun k ->
                    fun p ->
                      fun s ->
                        fun s32 ->
                          fun x ->
                            fun x1 ->
                              let tg = tag_of_data' x1 in
                              FStar_Bytes.append (st32 tg) (s32 tg x1)