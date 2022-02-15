open Prims
type ('rrel, 'rel, 'k, 't, 'p, 'h, 's, 'pos) valid' = unit
type ('rrel, 'rel, 'k, 't, 'p, 'h, 's, 'pos) valid = unit















type ('rrel, 'rel, 'k, 't, 'p, 'h, 'sl, 'pos, 'posu) valid_pos = unit



type ('rrel, 'rel, 'k, 't, 'p, 'h, 'sl, 'pos, 'x) valid_content = unit
type ('rrel, 'rel, 'k, 't, 'p, 'h, 'sl, 'pos, 'x, 'posu) valid_content_pos =
  unit


type ('rrel, 'rel, 'k, 't, 'p, 'h, 's, 'pos, 'posu) valid_exact' = unit
type ('rrel, 'rel, 'k, 't, 'p, 'h, 's, 'pos, 'posu) valid_exact = unit























type ('t1, 't2) clens = {
  clens_cond: unit ;
  clens_get: unit }

let clens_id : 't . unit -> ('t, 't) clens =
  fun uu___ -> { clens_cond = (); clens_get = () }
type ('t, 'tu, 'cl1, 'cl2) clens_eq = unit


type ('t1, 't2, 'l12, 'clensucond2, 'x1) clens_compose_cond = unit
let clens_compose :
  't1 't2 't3 . ('t1, 't2) clens -> ('t2, 't3) clens -> ('t1, 't3) clens =
  fun l12 -> fun l23 -> { clens_cond = (); clens_get = () }
type ('t1, 't2, 't3, 'l12, 'l23) clens_compose_strong_pre = unit
let clens_compose_strong :
  't1 't2 't3 . ('t1, 't2) clens -> ('t2, 't3) clens -> ('t1, 't3) clens =
  fun l12 -> fun l23 -> { clens_cond = (); clens_get = () }
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'sl) gaccessor_pre = Obj.t
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'sl, 'res) gaccessor_post = unit
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'sl, 'res) gaccessor_post' = unit
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl) gaccessor' = unit
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'f) gaccessor_no_lookahead = unit

type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'f) gaccessor_injective = unit
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'f) gaccessor_prop' = unit
type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl, 'f) gaccessor_prop = unit

type ('k1, 't1, 'p1, 'k2, 't2, 'p2, 'cl) gaccessor = unit
let (get_gaccessor_clens :
  LowParse_Spec_Base.parser_kind ->
    unit ->
      unit ->
        LowParse_Spec_Base.parser_kind ->
          unit ->
            unit -> (Obj.t, Obj.t) clens -> unit -> (Obj.t, Obj.t) clens)
  =
  fun k1 ->
    fun t1 -> fun p1 -> fun k2 -> fun t2 -> fun p2 -> fun cl -> fun g -> cl

















type ('rrel, 'rel, 'k, 't, 'p, 'h, 'sl, 'pos, 'posu) valid_list = Obj.t























