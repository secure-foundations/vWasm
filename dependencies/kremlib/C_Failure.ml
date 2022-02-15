open Prims
let (whatever : unit -> Prims.bool) = fun uu___ -> true
let rec failwith : 'a . C_String.t -> 'a =
  fun s ->
    C_String.print s;
    (let uu___2 = whatever () in
     if uu___2
     then C.portable_exit (FStar_Int32.int_to_t (Prims.of_int (255)))
     else ());
    failwith s