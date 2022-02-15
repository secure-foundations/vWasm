(** Define the [Printer] effect.

    This module introduces a new set of effects, specifically designed
    for the x64 printer. At a high-level, it is simply a
    state+freshness+writer monad, but it also contains optimizations
    to make overall printing fast. It provides functionality for
    multiple freshness sources, useful for printing.

    Scroll to the "Actual effect operations" section of this file to
    see the operations that can be performed in this effect. The first
    half of this file is largely just machinery needed to set up the
    layered effects to support the [Printer] effect. *)
module Semantics.Printer.Effect

/// Layered effect definitions. Here, we first define an effect called
/// [PRINTER] which we then use to make the [Printer] effect which is
/// much more convenient to use.

(** The actual internal state of the printer. *)
val printer_internal_state: Type0

type _pre_t = printer_internal_state -> GTot Type0
type _post_t (a:Type) = printer_internal_state -> a -> printer_internal_state -> GTot Type0

type _repr (a:Type) (pre:_pre_t) (post:_post_t a) : Type =
  (init:printer_internal_state) ->
  Pure (printer_internal_state & a)
    (requires (pre init))
    (ensures (fun (fini, x) -> post init x fini))

unfold
let _return (a:Type) (x:a) :
  _repr a (fun _ -> True) (fun p0 r p1 -> r == x /\ p0 == p1) =
  fun init -> (init, x)

unfold
let _bind (a:Type) (b:Type)
  (pre_f:_pre_t) (post_f:_post_t a) (pre_g:a -> _pre_t) (post_g:a -> _post_t b)
  (f:_repr a pre_f post_f) (g:(x:a -> _repr b (pre_g x) (post_g x))) :
  _repr b
    (fun p0 -> pre_f p0 /\ (forall (x:a) (p1:printer_internal_state). post_f p0 x p1 ==> pre_g x p1))
    (fun p0 y p2 -> exists (x:a) (p1:printer_internal_state). pre_f p0 /\ post_f p0 x p1 /\ post_g x p1 y p2) =
  fun init ->
    let st, x = f init in
    g x st

unfold
let _subcomp (a:Type)
  (pre_f:_pre_t) (post_f:_post_t a)
  (pre_g:_pre_t) (post_g:_post_t a)
  (f:_repr a pre_f post_f) :
  Pure (_repr a pre_g post_g)
    (requires
       (forall (p:printer_internal_state). pre_g p ==> pre_f p) /\
     (forall (p0 p1:printer_internal_state) (x:a). (pre_g p0 /\ post_f p0 x p1) ==> post_g p0 x p1))
    (ensures fun _ -> True) = f

unfold
let _if_then_else (a:Type)
  (pre_f:_pre_t) (post_f:_post_t a)
  (pre_g:_pre_t) (post_g:_post_t a)
  (f:_repr a pre_f post_f)
  (g:_repr a pre_g post_g)
  (p:bool) : Type =
  _repr a
    (fun h -> (p ==> pre_f h) /\ ((~ p) ==> pre_g h))
    (fun h0 r h1 -> (p ==> post_f h0 r h1) /\ ((~ p) ==> post_g h0 r h1))

(** The main [PRINTER] effect that supports Hoare-style pre- and post- conditions *)
total reifiable reflectable
layered_effect {
  PRINTER : a:Type -> pre:_pre_t -> post:_post_t a -> Effect
    with
  repr         = _repr;
  return       = _return;
  bind         = _bind;
  subcomp      = _subcomp;
  if_then_else = _if_then_else
}

let _lift_pure_to_printer (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp) :
  _repr a
    (fun p0 -> wp (fun _ -> True))
    (fun p0 r p1 -> ~ (wp (fun x -> x =!= r \/ p0 =!= p1))) =
  FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun (init:printer_internal_state) -> (init, f ())

sub_effect PURE ~> PRINTER = _lift_pure_to_printer

(** The main [Printer] effect which is what would actually be used by the x64 printer. *)
effect Printer (a:Type) = PRINTER a (fun p -> True) (fun p0 x p1 -> True)

/// Actual effect operations. These are what are expected to be used
/// in practice by the actual printer.

(** Printing happens in sections. At any point, the programmer can
    choose to print to any of the sections they want to print to, and
    this doesn't impact the other sections. When the printer is
    finally [serialize]d (or [serialize_to_list]ed), these sections
    are provided separately, and it is the user's job to merge them
    together as they see fit. *)
type section =
  | Main
  | Constants
  | AuxRoutines
  | AuxRWData

(** Print string to relevant section *)
val print : section -> string -> Printer unit

(** Print the concatenation of the provided list of strings to the relevant section. *)
val prints : section -> list string -> Printer unit

(** Multiple freshness counters are maintained in the printer. This
    lets you pick which one to use. *)
type freshness_source =
  | FloatingConstant

(** Get a fresh value from a freshness source. This does not impact
    the output of the printer, and only impacts the freshness count of
    that particular source. *)
val get_fresh : freshness_source -> Printer nat

(** Provides a serialized version of the printer, "consuming" it in
    the process. The result is a function from sections to list of
    strings, where the concatenation of these strings is the body of
    that section. *)
val serialize_to_list : (unit -> Printer unit) -> Tot (section -> Tot (list string))

(** An even more convenient serializer to print sections to
    stdout. "Consumes" the printer and provides a thunked computation
    that will print the provided section to stdout. *)
val serialize_to_stdout : (unit -> Printer unit) -> Tot (section -> FStar.All.ML unit)

(** A convenience method to denote "unimplemented" but prints (extra)
    context to the screen (alongside all currently accumulated
    information in the printer) before killing the runtime process.

    It is clearly unsound (since it has return type as ['a]), but this
    is perfectly ok, since it is only used in the printer, and its
    immediate effect is to kill the process. *)
val unimplemented_die : string -> Printer 'a

(** Map a [Printer] effect computation over a list. Note: runs left-to-right. *)
val printer_map : (#a:Type) -> (#b:Type) -> (f:a -> Printer b) -> (l:list a) -> Printer (list b)

(** Run the printer from left to right for each element in the list. *)
val printer_for_each : (#a:Type) -> (l:list a) -> (f:a -> Printer unit) -> Printer unit

(** [fold_right] but for the [Printer] effect *)
val printer_fold_right: ('a -> 'b -> Printer 'b) -> list 'a -> 'b -> Printer 'b

(** [fold_left] but for the [Printer] effect *)
val printer_fold_left: ('a -> 'b -> Printer 'a) -> 'a -> list 'b -> Printer 'a
