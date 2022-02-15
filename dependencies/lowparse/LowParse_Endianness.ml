open Prims











let rec seq_rev : 't . 't FStar_Seq_Base.seq -> 't FStar_Seq_Base.seq =
  fun x ->
    if (FStar_Seq_Base.length x) = Prims.int_zero
    then FStar_Seq_Base.empty ()
    else
      FStar_Seq_Base.append (seq_rev (FStar_Seq_Properties.tail x))
        (FStar_Seq_Base.create Prims.int_one (FStar_Seq_Properties.head x))










