(** Define the Error and Err effects.

    This module introduces two new effects, that behave otherwise
    simply like they are in PURE. However, they make it much more
    convenient to be able to program in, and use the error monad.

    It is generally more convenient to be able to program in the Err
    effect than the Error effect. *)
module Common.Err

/// Define some internals. Anything that starts with an underscore or
/// ends with a single-quote is meant to be internal to this module,
/// and should be completely ignored by a user of this library.
type error 'a =
  | Ok' of 'a
  | Error' of string

type _pre_t = Type0
type _post_t (a:Type) = error a -> GTot Type0

type _wp_t (a:Type) = wp:(_post_t a -> _pre_t){
    forall p q. (forall r. p r ==> q r) ==> (wp p ==> wp q)
  }

type _repr (a:Type) (wp:_wp_t a) = unit -> PURE (error a) wp

unfold
let _return_wp #a (x:a) : _wp_t a =
  fun p -> p (Ok' x)

inline_for_extraction
let _return (a:Type) (x:a) : _repr a (_return_wp x) =
  fun () -> Ok' x

unfold
let _bind_wp #a #b (wp_f:_wp_t a) (wp_g:a -> _wp_t b) : _wp_t b =
  fun p ->
    wp_f (fun r ->
      match r with
      | Error' e -> p (Error' e)
      | Ok' x -> wp_g x p)

inline_for_extraction
let _bind (a:Type) (b:Type)
    (wp_f:_wp_t a) (wp_g:a -> _wp_t b)
    (f:_repr a wp_f) (g:(x:a -> _repr b (wp_g x))) :
  _repr b (_bind_wp wp_f wp_g) =
  fun () ->
    let r = f () in
    match r with
    | Ok' x -> g x ()
    | Error' e -> Error' e

inline_for_extraction
let _subcomp (a:Type)
    (wp_f wp_g:_wp_t a)
    (f:_repr a wp_f) :
  Pure (_repr a wp_g)
    (requires (forall p. wp_g p ==> wp_f p))
    (ensures (fun _ -> True)) =
  f

unfold
let _ite_wp #a (wp_f wp_g : _wp_t a) (p : bool) : _wp_t a =
  fun post ->
    (p ==> wp_f post) /\
    ((~p) ==> wp_g post)

inline_for_extraction
let _if_then_else (a:Type)
    (wp_f wp_g:_wp_t a)
    (f:_repr a wp_f) (g:_repr a wp_g)
    (p:bool) : Type =
  _repr a (_ite_wp wp_f wp_g p)

total reifiable reflectable
layered_effect {
  ERROR : a:Type -> _wp_t a -> Effect
  with
  repr = _repr;
  return = _return;
  bind = _bind;
  subcomp = _subcomp;
  if_then_else = _if_then_else
}

/// Lift from PURE to ERROR

unfold
let _pure_wp_to_error_wp #a (wp:pure_wp a) : _wp_t a =
  FStar.Monotonic.Pure.wp_monotonic_pure ();
  (fun p -> wp (fun x -> p (Ok' x)))

let _lift_pure_error (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp):
  _repr a (_pure_wp_to_error_wp wp) =
  FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun () ->  Ok' (f ())

sub_effect PURE ~> ERROR = _lift_pure_error

/// Convenient Hoare-style specs

effect Error (a:Type) (pre:Type0) (post_v:a -> Type0) (post_e:string -> Type0) =
  ERROR a (fun p ->
            pre /\
            (forall (x:a). post_v x ==> p (Ok' x)) /\
            (forall (e:string). post_e e ==> p (Error' e)))

effect Err (a:Type) (pre:Type0) (post_v:a -> Type0) =
  Error a pre post_v (fun _ -> True)

effect Err_ (a:Type) = Err a True (fun _ -> True)

/// Expose convenient functionalities

inline_for_extraction
let _fail_with (a:Type) (e:string) :
  _repr a (fun p -> p (Error' e)) =
  fun () -> Error' e

(** Immediately force failure *)
let fail_with (#a:Type) (s:string) : Error a (True) (fun _ -> False) (fun r -> r == s) =
  ERROR?.reflect (_fail_with a s)

unfold
let _wrap_error_wp (a:Type) (wp:_wp_t a) (wrapper:string -> string) : _wp_t a =
  fun (p:_post_t a) ->
    wp (fun (r:error a) ->
        match r with
        | Ok' x -> p (Ok' x)
        | Error' e -> p (Error' (wrapper e)))

inline_for_extraction
let _wrap_errors
    (a:Type) (wp:_wp_t a)
    (wrapper:string -> string)
    (r:_repr a wp) :
  _repr a (_wrap_error_wp a wp wrapper) =
  fun () ->
    match r () with
    | Ok' y -> Ok' y
    | Error' e -> Error' (wrapper e)

(** Wrap the error message with a custom function. *)
let wrap_errors
    (#a #b:Type)
    (#wp:_wp_t b)
    (wrapper:string -> string)
    (f:a -> ERROR b wp) :
  a -> ERROR b (_wrap_error_wp b wp wrapper)
  =
  fun x ->
    ERROR?.reflect (_wrap_errors b wp wrapper (reify (f x)))

(** Run an [Err] computation with a custom wrapping function to the error case. *)
let wrap_err_with
    (#a:Type)
    (pre:Type0) (post:a -> Type0)
    (wrapper:string -> string)
    (f:unit -> Err a pre post) :
  Err a pre post =
  ERROR?.reflect (fun () ->
      match reify (f ()) () with
      | Ok' x -> Ok' x
      | Error' e -> Error' (wrapper e))
