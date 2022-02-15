module Semantics.Common.Class

open FStar.Tactics.Typeclasses
open Semantics.Common.FunctionInfo

(** Class for a semantics *)
class sem c s = {
    codes : (e:Type0{e == c});
    state : (e:Type0{e == s});
    funcs : (e:Type0{e == list (string * (fn_info * codes))});
    ok : state -> bool;
    oom : state -> bool;
    eval : funcs -> c -> (fuel:nat) -> s -> option state;
    lemma_more_fuel : (fs:funcs) -> (c:c) -> (fuel1:nat) -> (fuel2:nat) -> (s0:s) -> (sN:s) ->
      Lemma
        (requires (eval fs c fuel1 s0 == Some sN /\ fuel1 <= fuel2))
        (ensures (eval fs c fuel2 s0 == Some sN));
    lemma_oom_not_ok : (s:state) ->
      Lemma
        (requires (oom s))
        (ensures (not (ok s)));
    lemma_not_ok_propagate : (fs:funcs) -> (c:c) -> (fuel:nat) -> (s:s) ->
      Lemma
        (ensures
           (match eval fs c fuel s with
            | None -> True
            | Some s' -> (not (ok s) ==> not (ok s')) /\ (not (ok s) /\ not (oom s) ==> not (oom s'))));
}

let mksem codes state ok oom eval lemma_more_fuel lemma_oom_not_ok lemma_not_ok_propagate : sem codes state =
  Mksem codes state (list (string * (fn_info * codes))) ok oom eval lemma_more_fuel lemma_oom_not_ok lemma_not_ok_propagate
