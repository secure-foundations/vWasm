open Prims
type bytes32 = FStar_Bytes.bytes
type ('k, 't, 'p, 'input, 'res) parser32_correct = Obj.t
type ('k, 't, 'p) parser32 =
  bytes32 -> ('t * FStar_UInt32.t) FStar_Pervasives_Native.option


let (make_parser32 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (bytes32 -> (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          bytes32 -> (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
  = fun k -> fun t -> fun p -> fun p32 -> fun input -> p32 input
let coerce_parser32 :
  't2 .
    LowParse_Spec_Base.parser_kind ->
      unit ->
        unit ->
          (bytes32 -> (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
            ->
            unit ->
              bytes32 ->
                ('t2 * FStar_UInt32.t) FStar_Pervasives_Native.option
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun k -> fun t1 -> fun p -> fun p32 -> fun u -> Obj.magic p32)
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
type ('k, 't, 'p, 'input, 'res) validator_correct = Obj.t
type ('k, 't, 'p) validator =
  bytes32 -> FStar_UInt32.t FStar_Pervasives_Native.option
type ('k, 't, 'p, 's, 'input, 'res) serializer32_correct = unit
type ('k, 't, 'p, 's, 'input, 'res) serializer32_correct' =
  (unit, unit) LowParse_Bytes.bytes_equal
type ('k, 't, 'p, 's) serializer32 = 't -> bytes32

let (serialize32_ext :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> bytes32) ->
            LowParse_Spec_Base.parser_kind ->
              unit -> unit -> unit -> Obj.t -> bytes32)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 -> fun t2 -> fun p2 -> fun u -> fun input -> s1' input
type ('k, 't, 'p, 's) partial_serializer32 = 't -> bytes32







let (u32_max : FStar_UInt32.t) =
  FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
let (add_overflow : FStar_UInt32.t -> FStar_UInt32.t -> FStar_UInt32.t) =
  fun x ->
    fun y ->
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) y) x
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add x y
type ('k, 't, 'p, 's, 'x, 'y) size32_postcond = Obj.t
type ('k, 't, 'p, 's) size32 = 't -> FStar_UInt32.t
type ('k, 't, 'p, 's, 'len32) size32_constant_precond = unit
let (size32_constant :
  LowParse_Spec_Base.parser_kind ->
    unit -> unit -> unit -> FStar_UInt32.t -> unit -> Obj.t -> FStar_UInt32.t)
  = fun k -> fun t -> fun p -> fun s -> fun len32 -> fun u -> fun x -> len32
let (size32_ext :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        unit ->
          (Obj.t -> FStar_UInt32.t) ->
            LowParse_Spec_Base.parser_kind ->
              unit -> unit -> unit -> Obj.t -> FStar_UInt32.t)
  =
  fun k1 ->
    fun t1 ->
      fun p1 ->
        fun s1 ->
          fun s1' ->
            fun k2 -> fun t2 -> fun p2 -> fun u -> fun input -> s1' input
let rec (bytes_of_seq' :
  LowParse_Bytes.byte FStar_Seq_Base.seq -> bytes32 -> bytes32) =
  fun x ->
    fun accu ->
      if (FStar_Seq_Base.length x) = Prims.int_zero
      then accu
      else
        bytes_of_seq' (FStar_Seq_Properties.tail x)
          (FStar_Bytes.append accu
             (FStar_Bytes.create (FStar_UInt32.uint_to_t Prims.int_one)
                (FStar_Seq_Properties.head x)))
let (bytes_of_seq : LowParse_Bytes.byte FStar_Seq_Base.seq -> bytes32) =
  fun x -> bytes_of_seq' x FStar_Bytes.empty_bytes
let (parse_tot_seq_of_parser32 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        (bytes32 -> (Obj.t * FStar_UInt32.t) FStar_Pervasives_Native.option)
          ->
          LowParse_Bytes.byte FStar_Seq_Base.seq ->
            (Obj.t * Prims.nat) FStar_Pervasives_Native.option)
  =
  fun k ->
    fun t ->
      fun p ->
        fun p32 ->
          fun x ->
            match match k with
                  | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
                      LowParse_Spec_Base.parser_kind_high = parser_kind_high;
                      LowParse_Spec_Base.parser_kind_subkind =
                        parser_kind_subkind;
                      LowParse_Spec_Base.parser_kind_metadata =
                        parser_kind_metadata;_}
                      -> parser_kind_high
            with
            | FStar_Pervasives_Native.Some max ->
                if (FStar_Seq_Base.length x) < max
                then
                  (match p32 (bytes_of_seq' x FStar_Bytes.empty_bytes) with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some (x1, consumed) ->
                       FStar_Pervasives_Native.Some
                         (x1, (FStar_UInt32.v consumed)))
                else
                  (let res =
                     p32
                       (bytes_of_seq'
                          (FStar_Seq_Base.slice x Prims.int_zero max)
                          FStar_Bytes.empty_bytes) in
                   match res with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some (x1, consumed) ->
                       FStar_Pervasives_Native.Some
                         (x1, (FStar_UInt32.v consumed)))
let rec (seq_of_bytes' :
  bytes32 ->
    LowParse_Bytes.byte FStar_Seq_Base.seq ->
      LowParse_Bytes.byte FStar_Seq_Base.seq)
  =
  fun x ->
    fun accu ->
      if (FStar_Bytes.len x) = (FStar_UInt32.uint_to_t Prims.int_zero)
      then accu
      else
        seq_of_bytes'
          (FStar_Bytes.slice x (FStar_UInt32.uint_to_t Prims.int_one)
             (FStar_Bytes.len x))
          (FStar_Seq_Base.append accu
             (FStar_Seq_Base.create Prims.int_one
                (FStar_Bytes.get x (FStar_UInt32.uint_to_t Prims.int_zero))))
let (seq_of_bytes : bytes32 -> LowParse_Bytes.byte FStar_Seq_Base.seq) =
  fun x -> seq_of_bytes' x (FStar_Seq_Base.empty ())
let (serialize_tot_seq_of_serializer32 :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit -> unit -> (Obj.t -> bytes32) -> Obj.t -> LowParse_Bytes.bytes)
  =
  fun k ->
    fun t ->
      fun p ->
        fun s ->
          fun s32 -> fun x -> seq_of_bytes' (s32 x) (FStar_Seq_Base.empty ())