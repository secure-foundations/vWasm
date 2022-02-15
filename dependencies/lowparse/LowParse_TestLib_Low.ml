open Prims
type testbuffer_t =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice ->
        (Obj.t, Obj.t) LowParse_Slice.slice FStar_Pervasives_Native.option
let (load_file_buffer :
  Prims.string ->
    ((LowParse_Bytes.byte, unit, unit)
       LowStar_ImmutableBuffer.immutable_preorder,
      (LowParse_Bytes.byte, unit, unit)
        LowStar_ImmutableBuffer.immutable_preorder)
      LowParse_Slice.slice)
  = fun filename -> failwith "Not yet implemented:load_file_buffer"
let (load_file_buffer_c :
  C_String.t ->
    ((LowParse_Bytes.byte, unit, unit)
       LowStar_ImmutableBuffer.immutable_preorder,
      (LowParse_Bytes.byte, unit, unit)
        LowStar_ImmutableBuffer.immutable_preorder)
      LowParse_Slice.slice)
  = fun filename -> failwith "Not yet implemented:load_file_buffer_c"
let (beqb :
  unit ->
    unit ->
      unit ->
        unit ->
          unit ->
            (LowParse_Bytes.byte, Obj.t, Obj.t)
              LowStar_Monotonic_Buffer.mbuffer ->
              (LowParse_Bytes.byte, Obj.t, Obj.t)
                LowStar_Monotonic_Buffer.mbuffer ->
                FStar_UInt32.t -> Prims.bool)
  =
  fun uu___ ->
    fun rrel1 ->
      fun rel1 ->
        fun rrel2 ->
          fun rel2 ->
            fun b1 ->
              fun b2 -> fun len -> failwith "Not yet implemented:beqb"