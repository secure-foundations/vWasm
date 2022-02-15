open Prims
let (conclude :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.norm
               [FStar_Pervasives.delta;
               FStar_Pervasives.iota;
               FStar_Pervasives.primops])
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "LowParse.TacLib.fst"
                          (Prims.of_int (10)) (Prims.of_int (2))
                          (Prims.of_int (10)) (Prims.of_int (29))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (11)) (Prims.of_int (2))
                            (Prims.of_int (20)) (Prims.of_int (8)))))
           with
           | true ->
               (match match (FStar_Tactics_Builtins.lax_on ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "LowParse.TacLib.fst"
                                                      (Prims.of_int (11))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (8))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "LowParse.TacLib.fst"
                                                (Prims.of_int (11))
                                                (Prims.of_int (8))
                                                (Prims.of_int (17))
                                                (Prims.of_int (5))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range "LowParse.TacLib.fst"
                                          (Prims.of_int (11))
                                          (Prims.of_int (11))
                                          (Prims.of_int (11))
                                          (Prims.of_int (20))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "LowParse.TacLib.fst"
                                            (Prims.of_int (11))
                                            (Prims.of_int (8))
                                            (Prims.of_int (17))
                                            (Prims.of_int (5)))))
                           with
                           | true ->
                               (if a1
                                then FStar_Tactics_Derived.smt ()
                                else
                                  FStar_Tactics_Derived.first
                                    [FStar_Tactics_Derived.trefl;
                                    FStar_Tactics_Builtins.trivial])
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "LowParse.TacLib.fst"
                                             (Prims.of_int (11))
                                             (Prims.of_int (8))
                                             (Prims.of_int (17))
                                             (Prims.of_int (5)))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "LowParse.TacLib.fst"
                                      (Prims.of_int (20)) (Prims.of_int (2))
                                      (Prims.of_int (20)) (Prims.of_int (8)))))
                     with
                     | true ->
                         (FStar_Tactics_Derived.qed ())
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "LowParse.TacLib.fst"
                                       (Prims.of_int (20)) (Prims.of_int (2))
                                       (Prims.of_int (20)) (Prims.of_int (8)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (solve_vc :
  unit ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match match FStar_Tactics_Types.tracepoint
                    (FStar_Tactics_Types.set_proofstate_range
                       (FStar_Tactics_Types.incr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "LowParse.TacLib.fst"
                                         (Prims.of_int (25))
                                         (Prims.of_int (2))
                                         (Prims.of_int (25))
                                         (Prims.of_int (24))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "LowParse.TacLib.fst"
                                   (Prims.of_int (25)) (Prims.of_int (14))
                                   (Prims.of_int (25)) (Prims.of_int (24))))))
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "LowParse.TacLib.fst"
                             (Prims.of_int (25)) (Prims.of_int (2))
                             (Prims.of_int (25)) (Prims.of_int (24)))))
            with
            | true ->
                (FStar_Tactics_Derived.exact_guard
                   (Obj.magic
                      (failwith "Cannot evaluate open quotation at runtime")))
                  (FStar_Tactics_Types.decr_depth
                     (FStar_Tactics_Types.set_proofstate_range
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range ps
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range "LowParse.TacLib.fst"
                                          (Prims.of_int (25))
                                          (Prims.of_int (2))
                                          (Prims.of_int (25))
                                          (Prims.of_int (24))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "LowParse.TacLib.fst"
                                    (Prims.of_int (25)) (Prims.of_int (14))
                                    (Prims.of_int (25)) (Prims.of_int (24))))))
                        (FStar_Range.prims_to_fstar_range
                           (Prims.mk_range "LowParse.TacLib.fst"
                              (Prims.of_int (25)) (Prims.of_int (2))
                              (Prims.of_int (25)) (Prims.of_int (24))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (25)) (Prims.of_int (26))
                            (Prims.of_int (25)) (Prims.of_int (37)))))
           with
           | true ->
               (conclude ())
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "LowParse.TacLib.fst"
                             (Prims.of_int (25)) (Prims.of_int (26))
                             (Prims.of_int (25)) (Prims.of_int (37)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (app_head_rev_tail :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list)
        FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (FStar_Tactics_Builtins.inspect t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "LowParse.TacLib.fst"
                          (Prims.of_int (31)) (Prims.of_int (12))
                          (Prims.of_int (31)) (Prims.of_int (21))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (32)) (Prims.of_int (2))
                            (Prims.of_int (38)) (Prims.of_int (11)))))
           with
           | true ->
               (if FStar_Reflection_Data.uu___is_Tv_App a
                then
                  (fun ps1 ->
                     match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "LowParse.TacLib.fst"
                                            (Prims.of_int (34))
                                            (Prims.of_int (23))
                                            (Prims.of_int (34))
                                            (Prims.of_int (26))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "LowParse.TacLib.fst"
                                      (Prims.of_int (34)) (Prims.of_int (4))
                                      (Prims.of_int (36)) (Prims.of_int (15)))))
                     with
                     | true ->
                         ((match a with
                           | FStar_Reflection_Data.Tv_App (u, v) ->
                               (fun ps2 ->
                                  match (app_head_rev_tail u)
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps2
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "LowParse.TacLib.fst"
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (36))))))
                                  with
                                  | FStar_Tactics_Result.Success (a1, ps'1)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'1
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "LowParse.TacLib.fst"
                                                        (Prims.of_int (35))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (36))
                                                        (Prims.of_int (15)))))
                                       with
                                       | true ->
                                           FStar_Tactics_Result.Success
                                             (((match a1 with
                                                | (x, l) -> (x, (v :: l)))),
                                               (FStar_Tactics_Types.decr_depth
                                                  (FStar_Tactics_Types.set_proofstate_range
                                                     ps'1
                                                     (FStar_Range.prims_to_fstar_range
                                                        (Prims.mk_range
                                                           "LowParse.TacLib.fst"
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (36))
                                                           (Prims.of_int (15))))))))
                                  | FStar_Tactics_Result.Failed (e, ps'1) ->
                                      FStar_Tactics_Result.Failed (e, ps'1))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range
                                 (FStar_Tactics_Types.incr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "LowParse.TacLib.fst"
                                             (Prims.of_int (34))
                                             (Prims.of_int (23))
                                             (Prims.of_int (34))
                                             (Prims.of_int (26))))))
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "LowParse.TacLib.fst"
                                       (Prims.of_int (34)) (Prims.of_int (4))
                                       (Prims.of_int (36))
                                       (Prims.of_int (15)))))))
                else (fun s -> FStar_Tactics_Result.Success ((t, []), s)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "LowParse.TacLib.fst"
                             (Prims.of_int (32)) (Prims.of_int (2))
                             (Prims.of_int (38)) (Prims.of_int (11)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (app_head_tail :
  FStar_Reflection_Types.term ->
    FStar_Tactics_Types.proofstate ->
      (FStar_Reflection_Types.term * FStar_Reflection_Data.argv Prims.list)
        FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match (app_head_rev_tail t)
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "LowParse.TacLib.fst"
                          (Prims.of_int (43)) (Prims.of_int (15))
                          (Prims.of_int (43)) (Prims.of_int (34))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (43)) (Prims.of_int (2))
                            (Prims.of_int (44)) (Prims.of_int (14)))))
           with
           | true ->
               FStar_Tactics_Result.Success
                 (((match a with | (x, l) -> (x, (FStar_List_Tot_Base.rev l)))),
                   (FStar_Tactics_Types.decr_depth
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "LowParse.TacLib.fst"
                               (Prims.of_int (43)) (Prims.of_int (2))
                               (Prims.of_int (44)) (Prims.of_int (14))))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let (tassert :
  Prims.bool ->
    FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun b ->
    if b
    then fun s -> FStar_Tactics_Result.Success ((), s)
    else
      (fun ps ->
         match match FStar_Tactics_Types.tracepoint
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range
                                (FStar_Tactics_Types.incr_depth
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "LowParse.TacLib.fst"
                                            (Prims.of_int (51))
                                            (Prims.of_int (12))
                                            (Prims.of_int (51))
                                            (Prims.of_int (36))))))
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "LowParse.TacLib.fst"
                                      (Prims.of_int (51)) (Prims.of_int (27))
                                      (Prims.of_int (51)) (Prims.of_int (36))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "LowParse.TacLib.fst"
                                (Prims.of_int (51)) (Prims.of_int (12))
                                (Prims.of_int (51)) (Prims.of_int (36)))))
               with
               | true ->
                   FStar_Tactics_Result.Success
                     ((FStar_Reflection_Builtins.term_to_string
                         (Obj.magic
                            (failwith
                               "Cannot evaluate open quotation at runtime"))),
                       (FStar_Tactics_Types.decr_depth
                          (FStar_Tactics_Types.set_proofstate_range
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range
                                   (FStar_Tactics_Types.incr_depth
                                      (FStar_Tactics_Types.set_proofstate_range
                                         ps
                                         (FStar_Range.prims_to_fstar_range
                                            (Prims.mk_range
                                               "LowParse.TacLib.fst"
                                               (Prims.of_int (51))
                                               (Prims.of_int (12))
                                               (Prims.of_int (51))
                                               (Prims.of_int (36))))))
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "LowParse.TacLib.fst"
                                         (Prims.of_int (51))
                                         (Prims.of_int (27))
                                         (Prims.of_int (51))
                                         (Prims.of_int (36))))))
                             (FStar_Range.prims_to_fstar_range
                                (Prims.mk_range "LowParse.TacLib.fst"
                                   (Prims.of_int (51)) (Prims.of_int (12))
                                   (Prims.of_int (51)) (Prims.of_int (36)))))))
         with
         | FStar_Tactics_Result.Success (a, ps') ->
             (match FStar_Tactics_Types.tracepoint
                      (FStar_Tactics_Types.set_proofstate_range ps'
                         (FStar_Range.prims_to_fstar_range
                            (Prims.mk_range "LowParse.TacLib.fst"
                               (Prims.of_int (52)) (Prims.of_int (4))
                               (Prims.of_int (52)) (Prims.of_int (42)))))
              with
              | true ->
                  (FStar_Tactics_Derived.fail
                     (Prims.strcat "Tactic assertion failed: " a))
                    (FStar_Tactics_Types.decr_depth
                       (FStar_Tactics_Types.set_proofstate_range ps'
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "LowParse.TacLib.fst"
                                (Prims.of_int (52)) (Prims.of_int (4))
                                (Prims.of_int (52)) (Prims.of_int (42)))))))
         | FStar_Tactics_Result.Failed (e, ps') ->
             FStar_Tactics_Result.Failed (e, ps'))
let rec (to_all_goals :
  (unit ->
     FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
    -> FStar_Tactics_Types.proofstate -> unit FStar_Tactics_Result.__result)
  =
  fun t ->
    fun ps ->
      match match (FStar_Tactics_Derived.ngoals ())
                    (FStar_Tactics_Types.incr_depth
                       (FStar_Tactics_Types.set_proofstate_range
                          (FStar_Tactics_Types.incr_depth
                             (FStar_Tactics_Types.set_proofstate_range ps
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "LowParse.TacLib.fst"
                                      (Prims.of_int (56)) (Prims.of_int (5))
                                      (Prims.of_int (56)) (Prims.of_int (18))))))
                          (FStar_Range.prims_to_fstar_range
                             (Prims.mk_range "LowParse.TacLib.fst"
                                (Prims.of_int (56)) (Prims.of_int (5))
                                (Prims.of_int (56)) (Prims.of_int (14))))))
            with
            | FStar_Tactics_Result.Success (a, ps') ->
                (match FStar_Tactics_Types.tracepoint
                         (FStar_Tactics_Types.set_proofstate_range ps'
                            (FStar_Range.prims_to_fstar_range
                               (Prims.mk_range "LowParse.TacLib.fst"
                                  (Prims.of_int (56)) (Prims.of_int (5))
                                  (Prims.of_int (56)) (Prims.of_int (18)))))
                 with
                 | true ->
                     FStar_Tactics_Result.Success
                       ((a = Prims.int_zero),
                         (FStar_Tactics_Types.decr_depth
                            (FStar_Tactics_Types.set_proofstate_range ps'
                               (FStar_Range.prims_to_fstar_range
                                  (Prims.mk_range "LowParse.TacLib.fst"
                                     (Prims.of_int (56)) (Prims.of_int (5))
                                     (Prims.of_int (56)) (Prims.of_int (18))))))))
            | FStar_Tactics_Result.Failed (e, ps') ->
                FStar_Tactics_Result.Failed (e, ps')
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (56)) (Prims.of_int (2))
                            (Prims.of_int (59)) (Prims.of_int (55)))))
           with
           | true ->
               (if a
                then (fun s -> FStar_Tactics_Result.Success ((), s))
                else
                  (fun ps1 ->
                     match (FStar_Tactics_Derived.divide Prims.int_one t
                              (fun uu___1 -> to_all_goals t))
                             (FStar_Tactics_Types.incr_depth
                                (FStar_Tactics_Types.set_proofstate_range ps1
                                   (FStar_Range.prims_to_fstar_range
                                      (Prims.mk_range "LowParse.TacLib.fst"
                                         (Prims.of_int (59))
                                         (Prims.of_int (12))
                                         (Prims.of_int (59))
                                         (Prims.of_int (49))))))
                     with
                     | FStar_Tactics_Result.Success (a1, ps'1) ->
                         (match FStar_Tactics_Types.tracepoint
                                  (FStar_Tactics_Types.set_proofstate_range
                                     ps'1
                                     (FStar_Range.prims_to_fstar_range
                                        (Prims.mk_range "LowParse.TacLib.fst"
                                           (Prims.of_int (59))
                                           (Prims.of_int (53))
                                           (Prims.of_int (59))
                                           (Prims.of_int (55)))))
                          with
                          | true ->
                              FStar_Tactics_Result.Success
                                ((),
                                  (FStar_Tactics_Types.decr_depth
                                     (FStar_Tactics_Types.set_proofstate_range
                                        ps'1
                                        (FStar_Range.prims_to_fstar_range
                                           (Prims.mk_range
                                              "LowParse.TacLib.fst"
                                              (Prims.of_int (59))
                                              (Prims.of_int (53))
                                              (Prims.of_int (59))
                                              (Prims.of_int (55))))))))
                     | FStar_Tactics_Result.Failed (e, ps'1) ->
                         FStar_Tactics_Result.Failed (e, ps'1)))
                 (FStar_Tactics_Types.decr_depth
                    (FStar_Tactics_Types.set_proofstate_range ps'
                       (FStar_Range.prims_to_fstar_range
                          (Prims.mk_range "LowParse.TacLib.fst"
                             (Prims.of_int (56)) (Prims.of_int (2))
                             (Prims.of_int (59)) (Prims.of_int (55)))))))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (intros_until_squash :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.intro ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "LowParse.TacLib.fst"
                          (Prims.of_int (65)) (Prims.of_int (10))
                          (Prims.of_int (65)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (66)) (Prims.of_int (2))
                            (Prims.of_int (69)) (Prims.of_int (29)))))
           with
           | true ->
               (match match (FStar_Tactics_Derived.cur_goal ())
                              (FStar_Tactics_Types.incr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    (FStar_Tactics_Types.incr_depth
                                       (FStar_Tactics_Types.set_proofstate_range
                                          (FStar_Tactics_Types.decr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps'
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "LowParse.TacLib.fst"
                                                      (Prims.of_int (66))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (69))
                                                      (Prims.of_int (29))))))
                                          (FStar_Range.prims_to_fstar_range
                                             (Prims.mk_range
                                                "LowParse.TacLib.fst"
                                                (Prims.of_int (66))
                                                (Prims.of_int (16))
                                                (Prims.of_int (66))
                                                (Prims.of_int (43))))))
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range "LowParse.TacLib.fst"
                                          (Prims.of_int (66))
                                          (Prims.of_int (30))
                                          (Prims.of_int (66))
                                          (Prims.of_int (43))))))
                      with
                      | FStar_Tactics_Result.Success (a1, ps'1) ->
                          (match FStar_Tactics_Types.tracepoint
                                   (FStar_Tactics_Types.set_proofstate_range
                                      ps'1
                                      (FStar_Range.prims_to_fstar_range
                                         (Prims.mk_range
                                            "LowParse.TacLib.fst"
                                            (Prims.of_int (66))
                                            (Prims.of_int (16))
                                            (Prims.of_int (66))
                                            (Prims.of_int (43)))))
                           with
                           | true ->
                               (app_head_tail a1)
                                 (FStar_Tactics_Types.decr_depth
                                    (FStar_Tactics_Types.set_proofstate_range
                                       ps'1
                                       (FStar_Range.prims_to_fstar_range
                                          (Prims.mk_range
                                             "LowParse.TacLib.fst"
                                             (Prims.of_int (66))
                                             (Prims.of_int (16))
                                             (Prims.of_int (66))
                                             (Prims.of_int (43)))))))
                      | FStar_Tactics_Result.Failed (e, ps'1) ->
                          FStar_Tactics_Result.Failed (e, ps'1)
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "LowParse.TacLib.fst"
                                      (Prims.of_int (66)) (Prims.of_int (2))
                                      (Prims.of_int (69)) (Prims.of_int (29)))))
                     with
                     | true ->
                         ((match a1 with
                           | (tm, uu___1) ->
                               if
                                 FStar_Reflection_Builtins.term_eq tm
                                   (FStar_Reflection_Builtins.pack_ln
                                      (FStar_Reflection_Data.Tv_FVar
                                         (FStar_Reflection_Builtins.pack_fv
                                            ["Prims"; "squash"])))
                               then
                                 (fun s ->
                                    FStar_Tactics_Result.Success (a, s))
                               else intros_until_squash ()))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "LowParse.TacLib.fst"
                                       (Prims.of_int (66)) (Prims.of_int (2))
                                       (Prims.of_int (69))
                                       (Prims.of_int (29)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')
let rec (intros_until_eq_hyp :
  unit ->
    FStar_Tactics_Types.proofstate ->
      FStar_Reflection_Types.binder FStar_Tactics_Result.__result)
  =
  fun uu___ ->
    fun ps ->
      match (FStar_Tactics_Builtins.intro ())
              (FStar_Tactics_Types.incr_depth
                 (FStar_Tactics_Types.set_proofstate_range ps
                    (FStar_Range.prims_to_fstar_range
                       (Prims.mk_range "LowParse.TacLib.fst"
                          (Prims.of_int (75)) (Prims.of_int (10))
                          (Prims.of_int (75)) (Prims.of_int (18))))))
      with
      | FStar_Tactics_Result.Success (a, ps') ->
          (match FStar_Tactics_Types.tracepoint
                   (FStar_Tactics_Types.set_proofstate_range ps'
                      (FStar_Range.prims_to_fstar_range
                         (Prims.mk_range "LowParse.TacLib.fst"
                            (Prims.of_int (76)) (Prims.of_int (2))
                            (Prims.of_int (88)) (Prims.of_int (29)))))
           with
           | true ->
               (match (app_head_tail
                         (FStar_Reflection_Derived.type_of_binder a))
                        (FStar_Tactics_Types.incr_depth
                           (FStar_Tactics_Types.set_proofstate_range
                              (FStar_Tactics_Types.decr_depth
                                 (FStar_Tactics_Types.set_proofstate_range
                                    ps'
                                    (FStar_Range.prims_to_fstar_range
                                       (Prims.mk_range "LowParse.TacLib.fst"
                                          (Prims.of_int (76))
                                          (Prims.of_int (2))
                                          (Prims.of_int (88))
                                          (Prims.of_int (29))))))
                              (FStar_Range.prims_to_fstar_range
                                 (Prims.mk_range "LowParse.TacLib.fst"
                                    (Prims.of_int (76)) (Prims.of_int (17))
                                    (Prims.of_int (76)) (Prims.of_int (49))))))
                with
                | FStar_Tactics_Result.Success (a1, ps'1) ->
                    (match FStar_Tactics_Types.tracepoint
                             (FStar_Tactics_Types.set_proofstate_range ps'1
                                (FStar_Range.prims_to_fstar_range
                                   (Prims.mk_range "LowParse.TacLib.fst"
                                      (Prims.of_int (76)) (Prims.of_int (2))
                                      (Prims.of_int (88)) (Prims.of_int (29)))))
                     with
                     | true ->
                         ((match a1 with
                           | (sq, ar) ->
                               (fun ps1 ->
                                  match (if
                                           FStar_Reflection_Builtins.term_eq
                                             sq
                                             (FStar_Reflection_Builtins.pack_ln
                                                (FStar_Reflection_Data.Tv_FVar
                                                   (FStar_Reflection_Builtins.pack_fv
                                                      ["Prims"; "squash"])))
                                         then
                                           match ar with
                                           | (ar1, uu___1)::uu___2 ->
                                               (fun ps2 ->
                                                  match (app_head_tail ar1)
                                                          (FStar_Tactics_Types.incr_depth
                                                             (FStar_Tactics_Types.set_proofstate_range
                                                                ps2
                                                                (FStar_Range.prims_to_fstar_range
                                                                   (Prims.mk_range
                                                                    "LowParse.TacLib.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (39))))))
                                                  with
                                                  | FStar_Tactics_Result.Success
                                                      (a2, ps'2) ->
                                                      (match FStar_Tactics_Types.tracepoint
                                                               (FStar_Tactics_Types.set_proofstate_range
                                                                  ps'2
                                                                  (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.TacLib.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (27)))))
                                                       with
                                                       | true ->
                                                           FStar_Tactics_Result.Success
                                                             (((match a2 with
                                                                | (eq,
                                                                   uu___3) ->
                                                                    FStar_Reflection_Builtins.term_eq
                                                                    eq
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "eq2"]))))),
                                                               (FStar_Tactics_Types.decr_depth
                                                                  (FStar_Tactics_Types.set_proofstate_range
                                                                    ps'2
                                                                    (FStar_Range.prims_to_fstar_range
                                                                    (Prims.mk_range
                                                                    "LowParse.TacLib.fst"
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (27))))))))
                                                  | FStar_Tactics_Result.Failed
                                                      (e, ps'2) ->
                                                      FStar_Tactics_Result.Failed
                                                        (e, ps'2))
                                           | uu___1 ->
                                               (fun s ->
                                                  FStar_Tactics_Result.Success
                                                    (false, s))
                                         else
                                           (fun s ->
                                              FStar_Tactics_Result.Success
                                                (false, s)))
                                          (FStar_Tactics_Types.incr_depth
                                             (FStar_Tactics_Types.set_proofstate_range
                                                ps1
                                                (FStar_Range.prims_to_fstar_range
                                                   (Prims.mk_range
                                                      "LowParse.TacLib.fst"
                                                      (Prims.of_int (78))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (84))
                                                      (Prims.of_int (14))))))
                                  with
                                  | FStar_Tactics_Result.Success (a2, ps'2)
                                      ->
                                      (match FStar_Tactics_Types.tracepoint
                                               (FStar_Tactics_Types.set_proofstate_range
                                                  ps'2
                                                  (FStar_Range.prims_to_fstar_range
                                                     (Prims.mk_range
                                                        "LowParse.TacLib.fst"
                                                        (Prims.of_int (86))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (88))
                                                        (Prims.of_int (29)))))
                                       with
                                       | true ->
                                           (if a2
                                            then
                                              (fun s ->
                                                 FStar_Tactics_Result.Success
                                                   (a, s))
                                            else intros_until_eq_hyp ())
                                             (FStar_Tactics_Types.decr_depth
                                                (FStar_Tactics_Types.set_proofstate_range
                                                   ps'2
                                                   (FStar_Range.prims_to_fstar_range
                                                      (Prims.mk_range
                                                         "LowParse.TacLib.fst"
                                                         (Prims.of_int (86))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (88))
                                                         (Prims.of_int (29)))))))
                                  | FStar_Tactics_Result.Failed (e, ps'2) ->
                                      FStar_Tactics_Result.Failed (e, ps'2))))
                           (FStar_Tactics_Types.decr_depth
                              (FStar_Tactics_Types.set_proofstate_range ps'1
                                 (FStar_Range.prims_to_fstar_range
                                    (Prims.mk_range "LowParse.TacLib.fst"
                                       (Prims.of_int (76)) (Prims.of_int (2))
                                       (Prims.of_int (88))
                                       (Prims.of_int (29)))))))
                | FStar_Tactics_Result.Failed (e, ps'1) ->
                    FStar_Tactics_Result.Failed (e, ps'1)))
      | FStar_Tactics_Result.Failed (e, ps') ->
          FStar_Tactics_Result.Failed (e, ps')