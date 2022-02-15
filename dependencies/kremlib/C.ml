open Prims
let (srand : FStar_UInt32.t -> unit) =
  fun uu___ -> failwith "Not yet implemented:srand"
let (rand : unit -> FStar_Int32.t) =
  fun uu___ -> failwith "Not yet implemented:rand"
let (exit : FStar_Int32.t -> unit) =
  fun uu___ -> failwith "Not yet implemented:exit"
let (portable_exit : FStar_Int32.t -> unit) =
  fun uu___ -> failwith "Not yet implemented:portable_exit"
type channel = unit
let (stdout : channel) =
  Obj.magic (fun uu___ -> failwith "Not yet implemented:stdout")
let (stderr : channel) =
  Obj.magic (fun uu___ -> failwith "Not yet implemented:stderr")
let (fflush : channel -> FStar_Int32.t) =
  fun uu___ -> failwith "Not yet implemented:fflush"
type char = unit
let (char_of_uint8 : FStar_UInt8.t -> char) =
  fun uu___ -> failwith "Not yet implemented:char_of_uint8"
let (uint8_of_char : char -> FStar_UInt8.t) =
  fun uu___ -> failwith "Not yet implemented:uint8_of_char"
type int = unit
type clock_t = unit
let (clock : unit -> clock_t) =
  fun uu___ -> failwith "Not yet implemented:clock"
type exit_code =
  | EXIT_SUCCESS 
  | EXIT_FAILURE 
let (uu___is_EXIT_SUCCESS : exit_code -> Prims.bool) =
  fun projectee ->
    match projectee with | EXIT_SUCCESS -> true | uu___ -> false
let (uu___is_EXIT_FAILURE : exit_code -> Prims.bool) =
  fun projectee ->
    match projectee with | EXIT_FAILURE -> true | uu___ -> false
let (print_bytes :
  FStar_UInt8.t LowStar_Buffer.buffer -> FStar_UInt32.t -> unit) =
  fun b -> fun len -> failwith "Not yet implemented:print_bytes"