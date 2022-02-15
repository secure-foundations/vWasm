module Compiler.Sandbox.Helpers

open FStar.Tactics

#reset-options "--fuel 0 --ifuel 0"

#push-options "--ifuel 1"
inline_for_extraction
let last_binder_after_intros () : Tac binder =
  let _ = intros () in
  let bs = cur_binders () in
  if Cons? bs then List.Tot.last bs else fail "not enough binders"
#pop-options
