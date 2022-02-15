open Prims
let rec (destruct_lhs_pairs :
  FStar_Reflection_Types.term ->
    Prims.nat ->
      FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun n ->
      if n = Prims.int_zero
      then FStar_Tactics_Derived.trefl ()
      else
        (fun ps ->
           match (FStar_Tactics_Derived.destruct t)
                   (FStar_Tactics_Types.incr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "LowParse.Spec.Tac.Combinators.fst"
                               (Prims.of_int (12)) (Prims.of_int (4))
                               (Prims.of_int (12)) (Prims.of_int (14))))))
           with
           | FStar_Tactics_Result.Success (a, ps') ->
               (match FStar_Tactics_Types.tracepoint
                        (FStar_Tactics_Types.set_proofstate_range ps'
                           (FStar_Range.prims_to_fstar_range
                              (Prims.mk_range
                                 "LowParse.Spec.Tac.Combinators.fst"
                                 (Prims.of_int (13)) (Prims.of_int (4))
                                 (Prims.of_int (17)) (Prims.of_int (49)))))
                with
                | true ->
                    (match (FStar_Tactics_Builtins.intro ())
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.decr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps'
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "LowParse.Spec.Tac.Combinators.fst"
                                               (Prims.of_int (13))
                                               (Prims.of_int (4))
                                               (Prims.of_int (17))
                                               (Prims.of_int (49))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range
                                         "LowParse.Spec.Tac.Combinators.fst"
                                         (Prims.of_int (13))
                                         (Prims.of_int (12))
                                         (Prims.of_int (13))
                                         (Prims.of_int (20))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "LowParse.Spec.Tac.Combinators.fst"
                                           (Prims.of_int (14))
                                           (Prims.of_int (4))
                                           (Prims.of_int (17))
                                           (Prims.of_int (49)))))
                          with
                          | true ->
                              (match (FStar_Tactics_Builtins.intro ())
                                       (FStar_Tactics_Types.incr_depth
                                          (FStar_Tactics_Types.set_proofstate_range
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'1
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "LowParse.Spec.Tac.Combinators.fst"
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (17))
                                                         (Prims.of_int (49))))))
                                             (FStar_Range.prims_to_fstar_range
                                                (Prims.mk_range
                                                   "LowParse.Spec.Tac.Combinators.fst"
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (20))))))
                               with
                               | FStar_Tactics_Result.Success (a2, ps'2) ->
                                   (match FStar_Tactics_Types.tracepoint
                                            (FStar_Tactics_Types.set_proofstate_range
                                               ps'2
                                               (FStar_Range.prims_to_fstar_range
                                                  (Prims.mk_range
                                                     "LowParse.Spec.Tac.Combinators.fst"
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (49)))))
                                    with
                                    | true ->
                                        (match (FStar_Tactics_Builtins.intro
                                                  ())
                                                 (FStar_Tactics_Types.incr_depth
                                                    (FStar_Tactics_Types.set_proofstate_range
                                                       (FStar_Tactics_Types.decr_depth
                                                          (FStar_Tactics_Types.set_proofstate_range
                                                             ps'2
                                                             (FStar_Range.prims_to_fstar_range
                                                                (Prims.mk_range
                                                                   "LowParse.Spec.Tac.Combinators.fst"
                                                                   (Prims.of_int (15))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (17))
                                                                   (Prims.of_int (49))))))
                                                       (FStar_Range.prims_to_fstar_range
                                                          (Prims.mk_range
                                                             "LowParse.Spec.Tac.Combinators.fst"
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (23))))))
                                         with
                                         | FStar_Tactics_Result.Success
                                             (a3, ps'3) ->
                                             (match FStar_Tactics_Types.tracepoint
                                                      (FStar_Tactics_Types.set_proofstate_range
                                                         ps'3
                                                         (FStar_Range.prims_to_fstar_range
                                                            (Prims.mk_range
                                                               "LowParse.Spec.Tac.Combinators.fst"
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (17))
                                                               (Prims.of_int (49)))))
                                              with
                                              | true ->
                                                  (match (FStar_Tactics_Builtins.rewrite
                                                            a3)
                                                           (FStar_Tactics_Types.incr_depth
                                                              (FStar_Tactics_Types.set_proofstate_range
                                                                 (FStar_Tactics_Types.decr_depth
                                                                    (
                                                                    FStar_Tactics_Types.set_proofstate_range
                                                                    ps'3
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49))))))
                                                                 (FStar_Range.prims_to_fstar_range
                                                                    (
                                                                    Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (16))))))
                                                   with
                                                   | FStar_Tactics_Result.Success
                                                       (a4, ps'4) ->
                                                       (match FStar_Tactics_Types.tracepoint
                                                                (FStar_Tactics_Types.set_proofstate_range
                                                                   ps'4
                                                                   (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49)))))
                                                        with
                                                        | true ->
                                                            (match (FStar_Tactics_Derived.binder_to_term
                                                                    a1)
                                                                    (FStar_Tactics_Types.incr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'4
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49))))))
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (41))))))
                                                             with
                                                             | FStar_Tactics_Result.Success
                                                                 (a5, ps'5)
                                                                 ->
                                                                 (match 
                                                                    FStar_Tactics_Types.tracepoint
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49)))))
                                                                  with
                                                                  | true ->
                                                                    (destruct_lhs_pairs
                                                                    a5
                                                                    (n -
                                                                    Prims.int_one))
                                                                    (FStar_Tactics_Types.decr_depth
                                                                    (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'5
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (49)))))))
                                                             | FStar_Tactics_Result.Failed
                                                                 (e, ps'5) ->
                                                                 FStar_Tactics_Result.Failed
                                                                   (e, ps'5)))
                                                   | FStar_Tactics_Result.Failed
                                                       (e, ps'4) ->
                                                       FStar_Tactics_Result.Failed
                                                         (e, ps'4)))
                                         | FStar_Tactics_Result.Failed
                                             (e, ps'3) ->
                                             FStar_Tactics_Result.Failed
                                               (e, ps'3)))
                               | FStar_Tactics_Result.Failed (e, ps'2) ->
                                   FStar_Tactics_Result.Failed (e, ps'2)))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
           | FStar_Tactics_Result.Failed (e, ps') ->
               FStar_Tactics_Result.Failed (e, ps'))
let (synth_pairs_to_struct_to_pairs_tac' :
  Prims.nat ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun n ->
    fun ps ->
      match (FStar_Tactics_Builtins.norm [FStar_Pervasives.delta])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "LowParse.Spec.Tac.Combinators.fst"
                          (Prims.of_int (21)) (Prims.of_int (2))
                          (Prims.of_int (21)) (Prims.of_int (14))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.Spec.Tac.Combinators.fst"
                            (Prims.of_int (22)) (Prims.of_int (2))
                            (Prims.of_int (23)) (Prims.of_int (41)))))
           with
           | true ->
               (match (FStar_Tactics_Logic.forall_intro ())
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range
                                          "LowParse.Spec.Tac.Combinators.fst"
                                          (Prims.of_int (22))
                                          (Prims.of_int (2))
                                          (Prims.of_int (23))
                                          (Prims.of_int (41))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range
                                    "LowParse.Spec.Tac.Combinators.fst"
                                    (Prims.of_int (22)) (Prims.of_int (10))
                                    (Prims.of_int (22)) (Prims.of_int (25))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "LowParse.Spec.Tac.Combinators.fst"
                                      (Prims.of_int (23)) (Prims.of_int (2))
                                      (Prims.of_int (23)) (Prims.of_int (41)))))
                     with
                     | true ->
                         (match (FStar_Tactics_Derived.binder_to_term a1)
                                  (FStar_Tactics_Types.incr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        (FStar_Tactics_Types.decr_depth
                                           (FStar_Tactics_Types.set_proofstate_range
                                              ps'1
                                              (FStar_Range.prims_to_fstar_range
                                                 (Prims.mk_range
                                                    "LowParse.Spec.Tac.Combinators.fst"
                                                    (Prims.of_int (23))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (23))
                                                    (Prims.of_int (41))))))
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "LowParse.Spec.Tac.Combinators.fst"
                                              (Prims.of_int (23))
                                              (Prims.of_int (21))
                                              (Prims.of_int (23))
                                              (Prims.of_int (39))))))
                          with
                          | FStar_Tactics_Result.Success (a2, ps'2) ->
                              (match FStar_Tactics_Types.tracepoint
                                       (FStar_Tactics_Types.set_proofstate_range
                                          ps'2
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "LowParse.Spec.Tac.Combinators.fst"
                                                (Prims.of_int (23))
                                                (Prims.of_int (2))
                                                (Prims.of_int (23))
                                                (Prims.of_int (41)))))
                               with
                               | true ->
                                   (destruct_lhs_pairs a2 n)
                                     (FStar_Tactics_Types.decr_depth
                                        (FStar_Tactics_Types.set_proofstate_range
                                           ps'2
                                           (FStar_Range.prims_to_fstar_range
                                              (Prims.mk_range
                                                 "LowParse.Spec.Tac.Combinators.fst"
                                                 (Prims.of_int (23))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (23))
                                                 (Prims.of_int (41)))))))
                          | FStar_Tactics_Result.Failed (e, ps'2) ->
                              FStar_Tactics_Result.Failed (e, ps'2)))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let synth_pairs_to_struct_to_pairs_tac :
  'structut 'pairsut .
    unit ->
      Prims.nat ->
        FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result
  =
  fun recip ->
    fun n ->
      fun ps ->
        match match FStar_Tactics_Types.tracepoint
                      (FStar_Tactics_Types.set_proofstate_range
                         (FStar_Tactics_Types.incr_depth
                            (FStar_Tactics_Types.set_proofstate_range
                               (FStar_Tactics_Types.incr_depth
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range
                                           "LowParse.Spec.Tac.Combinators.fst"
                                           (Prims.of_int (26))
                                           (Prims.of_int (2))
                                           (Prims.of_int (26))
                                           (Prims.of_int (54))))))
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range
                                     "LowParse.Spec.Tac.Combinators.fst"
                                     (Prims.of_int (26)) (Prims.of_int (8))
                                     (Prims.of_int (26)) (Prims.of_int (54))))))
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "LowParse.Spec.Tac.Combinators.fst"
                               (Prims.of_int (26)) (Prims.of_int (2))
                               (Prims.of_int (26)) (Prims.of_int (54)))))
              with
              | true ->
                  (FStar_Tactics_Derived.apply
                     (Obj.magic
                        (failwith "Cannot evaluate open quotation at runtime")))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "LowParse.Spec.Tac.Combinators.fst"
                                            (Prims.of_int (26))
                                            (Prims.of_int (2))
                                            (Prims.of_int (26))
                                            (Prims.of_int (54))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range
                                      "LowParse.Spec.Tac.Combinators.fst"
                                      (Prims.of_int (26)) (Prims.of_int (8))
                                      (Prims.of_int (26)) (Prims.of_int (54))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range
                                "LowParse.Spec.Tac.Combinators.fst"
                                (Prims.of_int (26)) (Prims.of_int (2))
                                (Prims.of_int (26)) (Prims.of_int (54))))))
        with
        | FStar_Tactics_Result.Success (a, ps') ->
            (match FStar_Tactics_Types.tracepoint
                     (FStar_Tactics_Types.set_proofstate_range ps'
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range
                              "LowParse.Spec.Tac.Combinators.fst"
                              (Prims.of_int (27)) (Prims.of_int (2))
                              (Prims.of_int (27)) (Prims.of_int (39)))))
             with
             | true ->
                 (synth_pairs_to_struct_to_pairs_tac' n)
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range
                               "LowParse.Spec.Tac.Combinators.fst"
                               (Prims.of_int (27)) (Prims.of_int (2))
                               (Prims.of_int (27)) (Prims.of_int (39)))))))
        | FStar_Tactics_Result.Failed (e, ps') ->
            FStar_Tactics_Result.Failed (e, ps')