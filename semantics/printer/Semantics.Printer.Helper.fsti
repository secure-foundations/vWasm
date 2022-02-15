module Semantics.Printer.Helper

open Semantics.Common.CFG
open I2.Semantics

(** Provides a function that mentions whether a particular location in
    the module should be labeled when printing, or not. *)
val should_loc_be_labeled : module_ -> Tot (loc -> Tot bool)
