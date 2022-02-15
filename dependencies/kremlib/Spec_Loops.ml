open Prims
let rec seq_map :
  'a 'b . ('a -> 'b) -> 'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq =
  fun f ->
    fun s ->
      if (FStar_Seq_Base.length s) = Prims.int_zero
      then FStar_Seq_Base.empty ()
      else
        (let s' =
           FStar_Seq_Properties.cons (f (FStar_Seq_Properties.head s))
             (seq_map f (FStar_Seq_Properties.tail s)) in
         s')
let rec seq_map2 :
  'a 'b 'c .
    ('a -> 'b -> 'c) ->
      'a FStar_Seq_Base.seq -> 'b FStar_Seq_Base.seq -> 'c FStar_Seq_Base.seq
  =
  fun f ->
    fun s ->
      fun s' ->
        if (FStar_Seq_Base.length s) = Prims.int_zero
        then FStar_Seq_Base.empty ()
        else
          (let s'' =
             FStar_Seq_Properties.cons
               (f (FStar_Seq_Properties.head s)
                  (FStar_Seq_Properties.head s'))
               (seq_map2 f (FStar_Seq_Properties.tail s)
                  (FStar_Seq_Properties.tail s')) in
           s'')
let rec repeat : 'a . Prims.nat -> ('a -> 'a) -> 'a -> 'a =
  fun n ->
    fun f ->
      fun x ->
        if n = Prims.int_zero then x else repeat (n - Prims.int_one) f (f x)


let rec repeat_range :
  'a . Prims.nat -> Prims.nat -> ('a -> Prims.nat -> 'a) -> 'a -> 'a =
  fun min ->
    fun max ->
      fun f ->
        fun x ->
          if min = max
          then x
          else repeat_range (min + Prims.int_one) max f (f x min)


let repeat_spec :
  'uuuuu . unit -> Prims.nat -> ('uuuuu -> 'uuuuu) -> 'uuuuu -> 'uuuuu =
  fun uu___ -> repeat


let repeat_range_spec :
  'uuuuu .
    unit ->
      Prims.nat ->
        Prims.nat -> ('uuuuu -> Prims.nat -> 'uuuuu) -> 'uuuuu -> 'uuuuu
  = fun uu___ -> repeat_range

