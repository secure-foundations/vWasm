open Prims

type ('rrel, 'rel) slice =
  {
  base: (LowParse_Bytes.byte, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer ;
  len: FStar_UInt32.t }
let __proj__Mkslice__item__base :
  'rrel 'rel .
    ('rrel, 'rel) slice ->
      (LowParse_Bytes.byte, 'rrel, 'rel) LowStar_Monotonic_Buffer.mbuffer
  = fun projectee -> match projectee with | { base; len;_} -> base
let __proj__Mkslice__item__len :
  'rrel 'rel . ('rrel, 'rel) slice -> FStar_UInt32.t =
  fun projectee -> match projectee with | { base; len;_} -> len
type ('rrel, 'rel, 'h, 's) live_slice =
  (LowParse_Bytes.byte, 'rrel, 'rel, unit, unit)
    LowStar_Monotonic_Buffer.live


