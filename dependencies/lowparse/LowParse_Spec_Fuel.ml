open Prims
type ('fuel, 't, 'p) injective_fuel = unit
type ('fuel, 't, 'f) no_lookahead_fuel = unit
type ('fuel, 't, 'p) consumes_all_fuel = unit
type ('fuel, 'k, 't, 'f) parser_subkind_prop_fuel = Obj.t
type ('fuel, 'sz, 't, 'f) parses_at_least_fuel = unit
type ('fuel, 'sz, 't, 'f) parses_at_most_fuel = unit
type ('fuel, 'sz, 't, 'f) is_total_constant_size_parser_fuel = unit
type ('fuel, 't, 'f) parser_always_fails_fuel = unit
type ('fuel, 't, 'k, 'f) parser_kind_metadata_prop_fuel = Obj.t
type ('fuel, 't, 'k, 'f) parser_kind_prop_fuel = unit
type ('t, 'k, 'f) parser_kind_prop' = unit












