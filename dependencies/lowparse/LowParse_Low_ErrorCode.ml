open Prims
let (max_uint32 : FStar_UInt32.t) =
  FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")

let (max_uint32_as_uint64 : FStar_UInt64.t) =
  FStar_UInt64.uint_to_t (Prims.parse_int "4294967295")
let (validator_max_length : FStar_UInt64.t) =
  FStar_UInt64.uint_to_t (Prims.parse_int "4294967295")
let (is_error : FStar_UInt64.t -> Prims.bool) =
  fun positionOrError -> FStar_UInt64.gt positionOrError validator_max_length
let (is_success : FStar_UInt64.t -> Prims.bool) =
  fun positionOrError ->
    FStar_UInt64.lte positionOrError validator_max_length
type validator_error = FStar_UInt64.t
type pos_t = FStar_UInt64.t

let (set_validator_error_pos :
  validator_error -> FStar_UInt64.t -> validator_error) =
  fun error ->
    fun position ->
      match LowParse_BitFields.uint64 with
      | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
          LowParse_BitFields.v_uint_to_t = v_uint_to_t;
          LowParse_BitFields.uint_to_t_v = uint_to_t_v;
          LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
          LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
          LowParse_BitFields.get_bitfield = get_bitfield;
          LowParse_BitFields.set_bitfield = set_bitfield;
          LowParse_BitFields.logor = logor;
          LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
          LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
          set_bitfield error Prims.int_zero (Prims.of_int (32)) position
let (get_validator_error_pos : FStar_UInt64.t -> FStar_UInt64.t) =
  fun x ->
    match LowParse_BitFields.uint64 with
    | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
        LowParse_BitFields.v_uint_to_t = v_uint_to_t;
        LowParse_BitFields.uint_to_t_v = uint_to_t_v;
        LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
        LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
        LowParse_BitFields.get_bitfield = get_bitfield;
        LowParse_BitFields.set_bitfield = set_bitfield;
        LowParse_BitFields.logor = logor;
        LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
        LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
        get_bitfield x Prims.int_zero (Prims.of_int (32))
let (set_validator_error_kind :
  FStar_UInt64.t -> FStar_UInt64.t -> validator_error) =
  fun error ->
    fun code ->
      match LowParse_BitFields.uint64 with
      | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
          LowParse_BitFields.v_uint_to_t = v_uint_to_t;
          LowParse_BitFields.uint_to_t_v = uint_to_t_v;
          LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
          LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
          LowParse_BitFields.get_bitfield = get_bitfield;
          LowParse_BitFields.set_bitfield = set_bitfield;
          LowParse_BitFields.logor = logor;
          LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
          LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
          set_bitfield error (Prims.of_int (32)) (Prims.of_int (46)) code
let (get_validator_error_kind : FStar_UInt64.t -> FStar_UInt64.t) =
  fun error ->
    match LowParse_BitFields.uint64 with
    | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
        LowParse_BitFields.v_uint_to_t = v_uint_to_t;
        LowParse_BitFields.uint_to_t_v = uint_to_t_v;
        LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
        LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
        LowParse_BitFields.get_bitfield = get_bitfield;
        LowParse_BitFields.set_bitfield = set_bitfield;
        LowParse_BitFields.logor = logor;
        LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
        LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
        get_bitfield error (Prims.of_int (32)) (Prims.of_int (46))
type error_code = FStar_UInt64.t
let (set_validator_error_code :
  FStar_UInt64.t -> FStar_UInt64.t -> validator_error) =
  fun error ->
    fun code ->
      match LowParse_BitFields.uint64 with
      | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
          LowParse_BitFields.v_uint_to_t = v_uint_to_t;
          LowParse_BitFields.uint_to_t_v = uint_to_t_v;
          LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
          LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
          LowParse_BitFields.get_bitfield = get_bitfield;
          LowParse_BitFields.set_bitfield = set_bitfield;
          LowParse_BitFields.logor = logor;
          LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
          LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
          set_bitfield error (Prims.of_int (48)) (Prims.of_int (64)) code
let (get_validator_error_code : FStar_UInt64.t -> FStar_UInt64.t) =
  fun error ->
    match LowParse_BitFields.uint64 with
    | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
        LowParse_BitFields.v_uint_to_t = v_uint_to_t;
        LowParse_BitFields.uint_to_t_v = uint_to_t_v;
        LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
        LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
        LowParse_BitFields.get_bitfield = get_bitfield;
        LowParse_BitFields.set_bitfield = set_bitfield;
        LowParse_BitFields.logor = logor;
        LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
        LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
        get_bitfield error (Prims.of_int (48)) (Prims.of_int (64))
let (validator_error_generic : validator_error) =
  (match LowParse_BitFields.uint64 with
   | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
       LowParse_BitFields.v_uint_to_t = v_uint_to_t;
       LowParse_BitFields.uint_to_t_v = uint_to_t_v;
       LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
       LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
       LowParse_BitFields.get_bitfield = get_bitfield;
       LowParse_BitFields.set_bitfield = set_bitfield;
       LowParse_BitFields.logor = logor;
       LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
       LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
       set_bitfield) (FStar_UInt64.uint_to_t Prims.int_zero)
    (Prims.of_int (32)) (Prims.of_int (46))
    (FStar_UInt64.uint_to_t Prims.int_one)
let (validator_error_not_enough_data : validator_error) =
  (match LowParse_BitFields.uint64 with
   | { LowParse_BitFields.v = v; LowParse_BitFields.uint_to_t = uint_to_t;
       LowParse_BitFields.v_uint_to_t = v_uint_to_t;
       LowParse_BitFields.uint_to_t_v = uint_to_t_v;
       LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
       LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
       LowParse_BitFields.get_bitfield = get_bitfield;
       LowParse_BitFields.set_bitfield = set_bitfield;
       LowParse_BitFields.logor = logor;
       LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
       LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
       set_bitfield) (FStar_UInt64.uint_to_t Prims.int_zero)
    (Prims.of_int (32)) (Prims.of_int (46))
    (FStar_UInt64.uint_to_t (Prims.of_int (2)))
let (set_validator_error_pos_and_code :
  validator_error -> FStar_UInt64.t -> FStar_UInt64.t -> validator_error) =
  fun error ->
    fun position ->
      fun code ->
        set_validator_error_pos (set_validator_error_code error code)
          position
let (maybe_set_validator_error_pos_and_code :
  validator_error -> FStar_UInt64.t -> FStar_UInt64.t -> validator_error) =
  fun error ->
    fun pos ->
      fun c ->
        if
          (get_validator_error_code error) =
            (FStar_UInt64.uint_to_t Prims.int_zero)
        then set_validator_error_pos_and_code error pos c
        else error
let (maybe_set_error_code :
  FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t -> FStar_UInt64.t) =
  fun positionOrError ->
    fun positionAtError ->
      fun code ->
        if
          (is_error positionOrError) &&
            ((get_validator_error_code positionOrError) =
               (FStar_UInt64.uint_to_t Prims.int_zero))
        then
          set_validator_error_pos_and_code positionOrError positionAtError
            code
        else positionOrError