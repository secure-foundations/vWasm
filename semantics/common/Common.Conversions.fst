module Common.Conversions

unfold let pow2_8 = Words_s.pow2_8
unfold let pow2_16 = Words_s.pow2_16
unfold let pow2_32 = Words_s.pow2_32
unfold let pow2_64 = Words_s.pow2_64

unfold let nat8 = Types_s.nat8
unfold let nat16 = Types_s.nat16
unfold let nat32 = Types_s.nat32
unfold let nat64 = Types_s.nat64

let int_to_nat8 (i:int) : n:nat8{0 <= i && i < pow2_8 ==> i == n} =
  Words_s.int_to_natN pow2_8 i
let int_to_nat16 (i:int) : n:nat16{0 <= i && i < pow2_16 ==> i == n} =
  Words_s.int_to_natN pow2_16 i
let int_to_nat32 (i:int) : n:nat32{0 <= i && i < pow2_32 ==> i == n} =
  Words_s.int_to_natN pow2_32 i
let int_to_nat64 (i:int) : n:nat64{0 <= i && i < pow2_64 ==> i == n} =
  Words_s.int_to_natN pow2_64 i
