open Prims
let (max : Prims.nat -> Prims.nat -> Prims.nat) =
  fun x1 -> fun x2 -> if x1 > x2 then x1 else x2
let (serialize32_bounded_integer_ct :
  FStar_UInt32.t ->
    FStar_UInt32.t ->
      LowParse_Bytes.byte LowStar_Buffer.buffer -> FStar_UInt32.t -> unit)
  =
  fun i ->
    fun x ->
      fun b ->
        fun pos ->
          let h = FStar_HyperStack_ST.get () in
          let before = LowStar_Endianness.load32_be_i b pos in
          let after =
            (match LowParse_BitFields.uint32 with
             | { LowParse_BitFields.v = v;
                 LowParse_BitFields.uint_to_t = uint_to_t;
                 LowParse_BitFields.v_uint_to_t = v_uint_to_t;
                 LowParse_BitFields.uint_to_t_v = uint_to_t_v;
                 LowParse_BitFields.get_bitfield_gen = get_bitfield_gen;
                 LowParse_BitFields.set_bitfield_gen = set_bitfield_gen;
                 LowParse_BitFields.get_bitfield = get_bitfield;
                 LowParse_BitFields.set_bitfield = set_bitfield;
                 LowParse_BitFields.logor = logor;
                 LowParse_BitFields.bitfield_eq_lhs = bitfield_eq_lhs;
                 LowParse_BitFields.bitfield_eq_rhs = bitfield_eq_rhs;_} ->
                 set_bitfield_gen) before
              (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.of_int (8)))
                 (FStar_UInt32.sub
                    (FStar_UInt32.uint_to_t (Prims.of_int (4))) i))
              (FStar_UInt32.uint_to_t (Prims.of_int (32))) x in
          LowStar_Endianness.store32_be_i b pos after;
          (let h' = FStar_HyperStack_ST.get () in ())