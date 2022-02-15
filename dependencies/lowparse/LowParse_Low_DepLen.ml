open Prims

type ('min, 'max, 'hk, 'ht, 'hp, 'dlf, 'pk, 'pt, 'pp, 'rrel, 'rel, 'input,
  'pos, 'h) valid_deplen_decomp = unit


type ('min, 'max, 'k, 't, 'p, 'dlf) deplen_func =
  unit ->
    unit ->
      (Obj.t, Obj.t) LowParse_Slice.slice -> FStar_UInt32.t -> FStar_UInt32.t
let (validate_deplen :
  Prims.nat ->
    Prims.nat ->
      LowParse_Spec_Base.parser_kind ->
        unit ->
          unit ->
            (unit ->
               unit ->
                 (Obj.t, Obj.t) LowParse_Slice.slice ->
                   FStar_UInt64.t -> FStar_UInt64.t)
              ->
              (Obj.t -> FStar_UInt32.t) ->
                (unit ->
                   unit ->
                     (Obj.t, Obj.t) LowParse_Slice.slice ->
                       FStar_UInt32.t -> FStar_UInt32.t)
                  ->
                  LowParse_Spec_Base.parser_kind ->
                    unit ->
                      unit ->
                        unit ->
                          (unit ->
                             unit ->
                               (Obj.t, Obj.t) LowParse_Slice.slice ->
                                 FStar_UInt64.t -> FStar_UInt64.t)
                            ->
                            unit ->
                              unit ->
                                (Obj.t, Obj.t) LowParse_Slice.slice ->
                                  FStar_UInt64.t -> FStar_UInt64.t)
  =
  fun min ->
    fun max ->
      fun hk ->
        fun ht ->
          fun hp ->
            fun hv ->
              fun dlf ->
                fun dlfc ->
                  fun pk ->
                    fun pt ->
                      fun pp ->
                        fun ps ->
                          fun pv ->
                            fun rrel ->
                              fun rel ->
                                fun input ->
                                  fun pos ->
                                    let h = FStar_HyperStack_ST.get () in
                                    let pos_payload = hv () () input pos in
                                    if
                                      LowParse_Low_ErrorCode.is_error
                                        pos_payload
                                    then pos_payload
                                    else
                                      (let payload_len =
                                         dlfc () () input
                                           (FStar_Int_Cast.uint64_to_uint32
                                              pos) in
                                       if
                                         FStar_UInt64.lt
                                           (FStar_UInt64.sub
                                              (FStar_Int_Cast.uint32_to_uint64
                                                 (match input with
                                                  | {
                                                      LowParse_Slice.base =
                                                        base;
                                                      LowParse_Slice.len =
                                                        len;_}
                                                      -> len)) pos_payload)
                                           (FStar_Int_Cast.uint32_to_uint64
                                              payload_len)
                                       then
                                         LowParse_Low_ErrorCode.validator_error_not_enough_data
                                       else
                                         (let pos_end =
                                            FStar_UInt32.add
                                              (FStar_Int_Cast.uint64_to_uint32
                                                 pos_payload) payload_len in
                                          let pos_end' =
                                            pv () ()
                                              {
                                                LowParse_Slice.base =
                                                  (match input with
                                                   | {
                                                       LowParse_Slice.base =
                                                         base;
                                                       LowParse_Slice.len =
                                                         len;_}
                                                       -> base);
                                                LowParse_Slice.len = pos_end
                                              } pos_payload in
                                          if
                                            LowParse_Low_ErrorCode.is_error
                                              pos_end'
                                          then pos_end'
                                          else
                                            if
                                              (FStar_Int_Cast.uint64_to_uint32
                                                 pos_end')
                                                = pos_end
                                            then pos_end'
                                            else
                                              LowParse_Low_ErrorCode.validator_error_generic))