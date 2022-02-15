open Prims
type test_t =
  FStar_Bytes.bytes ->
    (FStar_Bytes.bytes * FStar_UInt32.t) FStar_Pervasives_Native.option
let (load_file : Prims.string -> FStar_Bytes.bytes) =
  fun filename -> failwith "Not yet implemented:load_file"
let (test_bytes : test_t -> Prims.string -> FStar_Bytes.bytes -> unit) =
  fun t ->
    fun testname ->
      fun input ->
        FStar_HyperStack_ST.push_frame ();
        FStar_HyperStack_IO.print_string
          (Prims.strcat "==== Testing Bytes "
             (Prims.strcat testname " ====\n"));
        (let result = t input in
         (match result with
          | FStar_Pervasives_Native.Some (formattedresult, offset) ->
              if FStar_UInt32.gt offset (FStar_Bytes.len input)
              then
                FStar_HyperStack_IO.print_string
                  "Invalid length return - it is longer than the input buffer!"
              else
                if
                  formattedresult =
                    (FStar_Bytes.slice input
                       (FStar_UInt32.uint_to_t Prims.int_zero) offset)
                then
                  FStar_HyperStack_IO.print_string
                    "Formatted data matches original input data\n"
                else
                  FStar_HyperStack_IO.print_string
                    "FAIL:  formatted data does not match original input data\n"
          | uu___3 -> FStar_HyperStack_IO.print_string "Failed to parse\n");
         FStar_HyperStack_IO.print_string
           (Prims.strcat "==== Finished " (Prims.strcat testname " ====\n"));
         FStar_HyperStack_ST.pop_frame ())
let (test_string : test_t -> Prims.string -> Prims.string -> unit) =
  fun t ->
    fun testname ->
      fun inputstring ->
        FStar_HyperStack_ST.push_frame ();
        (let input = FStar_Bytes.bytes_of_hex inputstring in
         test_bytes t testname input; FStar_HyperStack_ST.pop_frame ())
let (test_file : test_t -> Prims.string -> unit) =
  fun t ->
    fun filename ->
      FStar_HyperStack_ST.push_frame ();
      (let input = load_file filename in
       test_bytes t filename input; FStar_HyperStack_ST.pop_frame ())