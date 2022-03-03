module LowParse.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8

let bytes_equal (b1 b2: bytes) : GTot Type0 =
  Seq.length b1 == Seq.length b2 /\
  (forall (i: nat { i < Seq.length b1 } ) . {:pattern (Seq.index b1 i); (Seq.index b2 i) } U8.v (Seq.index b1 i) == U8.v (Seq.index b2 i))

let bytes_equal_intro (b1 b2: bytes) : Lemma
  (requires (
    Seq.length b1 == Seq.length b2 /\
  (forall (i: nat { i < Seq.length b1 } ) . U8.v (Seq.index b1 i) == U8.v (Seq.index b2 i))
  ))
  (ensures (bytes_equal b1 b2))
  [SMTPat (bytes_equal b1 b2)]
= ()

let bytes_equal_refl (b1 b2: bytes) : Lemma
  (requires (b1 == b2))
  (ensures (b1 `bytes_equal` b2))
  [SMTPat (bytes_equal b1 b2)]
= ()

let bytes_equal_elim (b1 b2: bytes) : Lemma
  (requires (b1 `bytes_equal` b2))
  (ensures (b1 == b2))
  [SMTPat (b1 `bytes_equal` b2)]
= assert (b1 `Seq.equal` b2)
