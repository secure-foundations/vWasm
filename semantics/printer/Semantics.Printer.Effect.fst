module Semantics.Printer.Effect

open FStar.List.Tot
open FStar.String

(* NOTE: all the sections are stored "reversed" in the internal state
   since that improves performance when printing, and only has a
   1-time cost of reversing again at the end. *)

type printer_internal_state = {
  freshness_floatingconstant: nat;
  sec_main: list string;
  sec_constants: list string;
  sec_aux_routines: list string;
  sec_aux_rw_data: list string;
}

let _initial_state : printer_internal_state = {
  freshness_floatingconstant = 0;
  sec_main = [];
  sec_constants = [];
  sec_aux_routines = [];
  sec_aux_rw_data = [];
}

let triv_repr (a:Type) = _repr a (fun _ -> True) (fun _ _ _ -> True)

inline_for_extraction
let impl_print (s:section) (data:string) : triv_repr unit =
  match s with
  | Main        -> fun st -> { st with sec_main         = data :: st.sec_main         }, ()
  | Constants   -> fun st -> { st with sec_constants    = data :: st.sec_constants    }, ()
  | AuxRoutines -> fun st -> { st with sec_aux_routines = data :: st.sec_aux_routines }, ()
  | AuxRWData   -> fun st -> { st with sec_aux_rw_data  = data :: st.sec_aux_rw_data  }, ()

let print (s:section) (data:string) : Printer unit =
  PRINTER?.reflect (impl_print s data)

let prints (s:section) (l:list string) : Printer unit =
  print s (concat "" l)

inline_for_extraction
let impl_get_fresh (f:freshness_source) : triv_repr nat =
  match f with
  | FloatingConstant ->
    fun st -> { st with freshness_floatingconstant = st.freshness_floatingconstant + 1 },
              st.freshness_floatingconstant

let get_fresh (f:freshness_source) : Printer nat =
  PRINTER?.reflect (impl_get_fresh f)

let impl_to_list (st:printer_internal_state) : Tot (section -> Tot (list string)) =
  function
  | Main ->        rev st.sec_main
  | Constants ->   rev st.sec_constants
  | AuxRoutines -> rev st.sec_aux_routines
  | AuxRWData ->   rev st.sec_aux_rw_data

let serialize_to_list (f:(unit -> Printer unit)) : Tot (section -> Tot (list string)) =
  let (st, ()) = reify (f ()) _initial_state in
  impl_to_list st

let rec print_list_to_stdout (l:list string) : FStar.All.ML unit =
  match l with
  | [] -> ()
  | x :: xs ->
    FStar.IO.print_string x;
    print_list_to_stdout xs

let serialize_to_stdout (f:(unit -> Printer unit)) : Tot (section -> FStar.All.ML unit) =
  let f = serialize_to_list f in
  fun s -> print_list_to_stdout (f s)

let impl_unimplemented_die #t (context:string) : triv_repr t =
  fun st -> (
      let l = impl_to_list st in
      let b = FStar.IO.debug_print_string ("=====\n[" ^ context ^ "] unimplemented\n") in
      let b = FStar.IO.debug_print_string ("=====\nMain:\n\n" ^ concat "" (l Main)) in
      let b = FStar.IO.debug_print_string ("=====\nConstants:\n\n" ^ concat "" (l Constants)) in
      let b = FStar.IO.debug_print_string ("=====\nAuxRoutines:\n\n" ^ concat "" (l AuxRoutines)) in
      let b = FStar.IO.debug_print_string ("=====\nAuxRWData:\n\n" ^ concat "" (l AuxRWData)) in
      let b = FStar.IO.debug_print_string ("=====\n[" ^ context ^ "] unimplemented\n") in
      (* This "admit" is what kills the process. *)
      admit ()
    )

let unimplemented_die (#t) (context:string) : Printer t =
  PRINTER?.reflect (impl_unimplemented_die context)

let rec impl_printer_map #a #b (f:(a -> triv_repr b)) (l:list a) : triv_repr (list b) =
  fun init ->
  match l with
  | [] -> init, []
  | x :: xs ->
    let st, y = f x init in
    let st2, z = impl_printer_map f xs st in
    st2, y :: z

let printer_map #a #b (f:(a -> Printer b)) (l:list a) : Printer (list b) =
  PRINTER?.reflect (impl_printer_map (fun x -> reify (f x)) l)

let rec impl_printer_fold_left (f:('a -> 'b -> triv_repr 'a)) (init:'a) (l:list 'b) :
  Tot (triv_repr 'a)
    (decreases %[l]) =
  fun st0 ->
  match l with
  | [] -> st0, init
  | x :: xs ->
    let st1, y = f init x st0 in
    impl_printer_fold_left f y xs st1

let printer_for_each #a (l:list a) (f:(a -> Printer unit)) : Printer unit =
  PRINTER?.reflect (impl_printer_fold_left (fun () x -> reify (f x)) () l)

let rec printer_fold_right (f:('a -> 'b -> Printer 'b)) (l:list 'a) (x:'b) :
  Printer 'b =
  match l with
  | [] -> x
  | hd::tl -> f hd (printer_fold_right f tl x)

let printer_fold_left (f:('a -> 'b -> Printer 'a)) (x:'a) (y:list 'b) : Printer 'a =
  PRINTER?.reflect (impl_printer_fold_left (fun a b -> reify (f a b)) x y)
