open Prims
let negate_cond : 't . ('t -> Prims.bool) -> 't -> Prims.bool =
  fun cond -> fun x -> Prims.op_Negation (cond x)
type ('t, 'cond) refine_with_cond = 't
type ('t, 'cond) parse_list_up_to_t =
  (('t, unit) refine_with_cond Prims.list * ('t, unit) refine_with_cond)
let (parse_list_up_to_kind :
  LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind) =
  fun k ->
    {
      LowParse_Spec_Base.parser_kind_low =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_low);
      LowParse_Spec_Base.parser_kind_high = FStar_Pervasives_Native.None;
      LowParse_Spec_Base.parser_kind_subkind =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_subkind);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }
type ('k, 't, 'cond, 'p) consumes_if_not_cond = unit
type ('t, 'fuel) llist = 't Prims.list
type ('t, 'cond, 'fuel) parse_list_up_to_fuel_t =
  ((('t, unit) refine_with_cond, unit) llist * ('t, unit) refine_with_cond)
type up_unit =
  | UP_UNIT 
let (uu___is_UP_UNIT : up_unit -> Prims.bool) = fun projectee -> true
type ('t, 'cond, 'fuel, 'x) parse_list_up_to_payload_t = Obj.t
let synth_list_up_to_fuel :
  't .
    ('t -> Prims.bool) ->
      Prims.nat ->
        ('t, Obj.t) Prims.dtuple2 -> ('t, unit, unit) parse_list_up_to_fuel_t
  =
  fun cond ->
    fun fuel ->
      fun xy ->
        let uu___ = xy in
        match uu___ with
        | Prims.Mkdtuple2 (x, yz) ->
            if cond x
            then ([], x)
            else
              (let uu___2 = Obj.magic yz in
               match uu___2 with | (y, z) -> ((x :: y), z))

let (parse_list_up_to_payload_kind :
  LowParse_Spec_Base.parser_kind -> LowParse_Spec_Base.parser_kind) =
  fun k ->
    {
      LowParse_Spec_Base.parser_kind_low = Prims.int_zero;
      LowParse_Spec_Base.parser_kind_high = FStar_Pervasives_Native.None;
      LowParse_Spec_Base.parser_kind_subkind =
        (match k with
         | { LowParse_Spec_Base.parser_kind_low = parser_kind_low;
             LowParse_Spec_Base.parser_kind_high = parser_kind_high;
             LowParse_Spec_Base.parser_kind_subkind = parser_kind_subkind;
             LowParse_Spec_Base.parser_kind_metadata = parser_kind_metadata;_}
             -> parser_kind_subkind);
      LowParse_Spec_Base.parser_kind_metadata = FStar_Pervasives_Native.None
    }






let synth_list_up_to' :
  't .
    ('t -> Prims.bool) ->
      Prims.nat ->
        ('t, unit, unit) parse_list_up_to_fuel_t ->
          ('t, unit) parse_list_up_to_t
  =
  fun cond ->
    fun fuel ->
      fun xy ->
        ((FStar_Pervasives_Native.fst xy), (FStar_Pervasives_Native.snd xy))







let synth_list_up_to_fuel_recip :
  't .
    ('t -> Prims.bool) ->
      Prims.nat ->
        ('t, unit, unit) parse_list_up_to_fuel_t -> ('t, Obj.t) Prims.dtuple2
  =
  fun cond ->
    fun fuel ->
      fun xy ->
        let uu___ = xy in
        match uu___ with
        | (l, z) ->
            (match l with
             | [] -> Prims.Mkdtuple2 (z, (Obj.magic UP_UNIT))
             | x::y -> Prims.Mkdtuple2 (x, (Obj.magic (y, z))))






