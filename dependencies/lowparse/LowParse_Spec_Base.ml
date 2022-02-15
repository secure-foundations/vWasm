open Prims
type 'b consumed_length = Prims.nat
type 't bare_parser = unit

type ('t, 'p, 'b1, 'b2) injective_precond = unit

type ('t, 'p, 'b1, 'b2) injective_postcond = unit

type ('t, 'p) injective = unit

type ('t, 'f, 'x, 'xu) no_lookahead_on_precond = unit
type ('t, 'f, 'x, 'xu) no_lookahead_on_postcond = unit
type ('t, 'f, 'x, 'xu) no_lookahead_on = unit

type ('t, 'f) no_lookahead = unit

type ('t, 'p) consumes_all = unit
type ('sz, 't, 'f) parses_at_least = unit


type ('sz, 't, 'f) parses_at_most = unit
type ('sz, 't, 'f) is_constant_size_parser = unit

type ('sz, 't, 'f) is_total_constant_size_parser = unit
type parser_subkind =
  | ParserStrong 
  | ParserConsumesAll 
let (uu___is_ParserStrong : parser_subkind -> Prims.bool) =
  fun projectee ->
    match projectee with | ParserStrong -> true | uu___ -> false
let (uu___is_ParserConsumesAll : parser_subkind -> Prims.bool) =
  fun projectee ->
    match projectee with | ParserConsumesAll -> true | uu___ -> false
type ('k, 't, 'f) parser_subkind_prop = Obj.t
type parser_kind_metadata_some =
  | ParserKindMetadataTotal 
  | ParserKindMetadataFail 
let (uu___is_ParserKindMetadataTotal :
  parser_kind_metadata_some -> Prims.bool) =
  fun projectee ->
    match projectee with | ParserKindMetadataTotal -> true | uu___ -> false
let (uu___is_ParserKindMetadataFail :
  parser_kind_metadata_some -> Prims.bool) =
  fun projectee ->
    match projectee with | ParserKindMetadataFail -> true | uu___ -> false
type parser_kind_metadata_t =
  parser_kind_metadata_some FStar_Pervasives_Native.option
type parser_kind' =
  {
  parser_kind_low: Prims.nat ;
  parser_kind_high: Prims.nat FStar_Pervasives_Native.option ;
  parser_kind_subkind: parser_subkind FStar_Pervasives_Native.option ;
  parser_kind_metadata: parser_kind_metadata_t }
let (__proj__Mkparser_kind'__item__parser_kind_low :
  parser_kind' -> Prims.nat) =
  fun projectee ->
    match projectee with
    | { parser_kind_low; parser_kind_high; parser_kind_subkind;
        parser_kind_metadata;_} -> parser_kind_low
let (__proj__Mkparser_kind'__item__parser_kind_high :
  parser_kind' -> Prims.nat FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { parser_kind_low; parser_kind_high; parser_kind_subkind;
        parser_kind_metadata;_} -> parser_kind_high
let (__proj__Mkparser_kind'__item__parser_kind_subkind :
  parser_kind' -> parser_subkind FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { parser_kind_low; parser_kind_high; parser_kind_subkind;
        parser_kind_metadata;_} -> parser_kind_subkind
let (__proj__Mkparser_kind'__item__parser_kind_metadata :
  parser_kind' -> parser_kind_metadata_t) =
  fun projectee ->
    match projectee with
    | { parser_kind_low; parser_kind_high; parser_kind_subkind;
        parser_kind_metadata;_} -> parser_kind_metadata
type parser_kind = parser_kind'
let (strong_parser_kind :
  Prims.nat -> Prims.nat -> parser_kind_metadata_t -> parser_kind) =
  fun lo ->
    fun hi ->
      fun md ->
        {
          parser_kind_low = lo;
          parser_kind_high = (FStar_Pervasives_Native.Some hi);
          parser_kind_subkind = (FStar_Pervasives_Native.Some ParserStrong);
          parser_kind_metadata = md
        }
let (total_constant_size_parser_kind : Prims.nat -> parser_kind) =
  fun sz ->
    {
      parser_kind_low = sz;
      parser_kind_high = (FStar_Pervasives_Native.Some sz);
      parser_kind_subkind = (FStar_Pervasives_Native.Some ParserStrong);
      parser_kind_metadata =
        (FStar_Pervasives_Native.Some ParserKindMetadataTotal)
    }
type ('t, 'f) parser_always_fails = unit
type ('t, 'k, 'f) parser_kind_metadata_prop = Obj.t
type ('t, 'k, 'f) parser_kind_prop' = unit
type ('a, 'k, 'f) parser_kind_prop = unit


type ('k, 't) parser = unit
let (get_parser_kind : parser_kind -> unit -> unit -> parser_kind) =
  fun k -> fun t -> fun p -> k
type ('k, 't, 'p) get_parser_type = 't

let (is_strong : parser_kind -> unit -> unit -> Prims.bool) =
  fun k ->
    fun t ->
      fun p ->
        (match k with
         | { parser_kind_low; parser_kind_high; parser_kind_subkind;
             parser_kind_metadata;_} -> parser_kind_subkind)
          = (FStar_Pervasives_Native.Some ParserStrong)
type ('k1, 'k2) is_weaker_than = unit




let is_some : 't . 't FStar_Pervasives_Native.option -> Prims.bool =
  fun x ->
    match x with
    | FStar_Pervasives_Native.Some uu___ -> true
    | uu___ -> false
let some_v : 't . 't FStar_Pervasives_Native.option -> 't =
  fun x -> match x with | FStar_Pervasives_Native.Some y -> y
let (bool_and : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1 -> fun b2 -> if b1 then b2 else false
let (bool_or : Prims.bool -> Prims.bool -> Prims.bool) =
  fun b1 -> fun b2 -> if b1 then true else b2
let (glb : parser_kind -> parser_kind -> parser_kind) =
  fun k1 ->
    fun k2 ->
      match ((match k1 with
              | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                  parser_kind_metadata;_} -> parser_kind_metadata),
              (match k2 with
               | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                   parser_kind_metadata;_} -> parser_kind_metadata))
      with
      | (uu___, FStar_Pervasives_Native.Some (ParserKindMetadataFail)) ->
          {
            parser_kind_low =
              ((match k1 with
                | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                    parser_kind_metadata;_} -> parser_kind_low));
            parser_kind_high =
              ((match k1 with
                | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                    parser_kind_metadata;_} -> parser_kind_high));
            parser_kind_subkind =
              ((match k1 with
                | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                    parser_kind_metadata;_} -> parser_kind_subkind));
            parser_kind_metadata =
              ((match match k1 with
                      | { parser_kind_low; parser_kind_high;
                          parser_kind_subkind; parser_kind_metadata;_} ->
                          parser_kind_metadata
                with
                | FStar_Pervasives_Native.Some (ParserKindMetadataFail) ->
                    FStar_Pervasives_Native.Some ParserKindMetadataFail
                | uu___1 -> FStar_Pervasives_Native.None))
          }
      | (FStar_Pervasives_Native.Some (ParserKindMetadataFail), uu___) ->
          {
            parser_kind_low =
              ((match k2 with
                | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                    parser_kind_metadata;_} -> parser_kind_low));
            parser_kind_high =
              ((match k2 with
                | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                    parser_kind_metadata;_} -> parser_kind_high));
            parser_kind_subkind =
              ((match k2 with
                | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                    parser_kind_metadata;_} -> parser_kind_subkind));
            parser_kind_metadata = FStar_Pervasives_Native.None
          }
      | uu___ ->
          {
            parser_kind_low =
              (if
                 (match k1 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_low)
                   <
                   ((match k2 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_low))
               then
                 (match k1 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_low)
               else
                 (match k2 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_low));
            parser_kind_high =
              (if
                 (if
                    match match k1 with
                          | { parser_kind_low; parser_kind_high;
                              parser_kind_subkind; parser_kind_metadata;_} ->
                              parser_kind_high
                    with
                    | FStar_Pervasives_Native.Some uu___1 -> true
                    | uu___1 -> false
                  then
                    match match k2 with
                          | { parser_kind_low; parser_kind_high;
                              parser_kind_subkind; parser_kind_metadata;_} ->
                              parser_kind_high
                    with
                    | FStar_Pervasives_Native.Some uu___1 -> true
                    | uu___1 -> false
                  else false)
               then
                 (if
                    (match match k2 with
                           | { parser_kind_low; parser_kind_high;
                               parser_kind_subkind; parser_kind_metadata;_}
                               -> parser_kind_high
                     with
                     | FStar_Pervasives_Native.Some y -> y) <
                      (match match k1 with
                             | { parser_kind_low; parser_kind_high;
                                 parser_kind_subkind; parser_kind_metadata;_}
                                 -> parser_kind_high
                       with
                       | FStar_Pervasives_Native.Some y -> y)
                  then
                    match k1 with
                    | { parser_kind_low; parser_kind_high;
                        parser_kind_subkind; parser_kind_metadata;_} ->
                        parser_kind_high
                  else
                    (match k2 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_high))
               else FStar_Pervasives_Native.None);
            parser_kind_subkind =
              (if
                 (match k1 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_subkind)
                   =
                   ((match k2 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_subkind))
               then
                 (match k1 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_subkind)
               else FStar_Pervasives_Native.None);
            parser_kind_metadata =
              (if
                 (match k1 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_metadata)
                   =
                   ((match k2 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_metadata))
               then
                 (match k1 with
                  | { parser_kind_low; parser_kind_high; parser_kind_subkind;
                      parser_kind_metadata;_} -> parser_kind_metadata)
               else FStar_Pervasives_Native.None)
          }
let (default_parser_kind : parser_kind) =
  let x =
    {
      parser_kind_low = Prims.int_zero;
      parser_kind_high = FStar_Pervasives_Native.None;
      parser_kind_subkind = FStar_Pervasives_Native.None;
      parser_kind_metadata = FStar_Pervasives_Native.None
    } in
  x
let rec glb_list_of :
  't . ('t -> parser_kind) -> 't Prims.list -> parser_kind =
  fun f ->
    fun l ->
      match l with
      | [] -> default_parser_kind
      | k::[] -> f k
      | k1::q ->
          let k' = glb_list_of f q in
          (match ((match f k1 with
                   | { parser_kind_low; parser_kind_high;
                       parser_kind_subkind; parser_kind_metadata;_} ->
                       parser_kind_metadata),
                   (match k' with
                    | { parser_kind_low; parser_kind_high;
                        parser_kind_subkind; parser_kind_metadata;_} ->
                        parser_kind_metadata))
           with
           | (uu___, FStar_Pervasives_Native.Some (ParserKindMetadataFail))
               ->
               {
                 parser_kind_low =
                   ((match f k1 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_low));
                 parser_kind_high =
                   ((match f k1 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_high));
                 parser_kind_subkind =
                   ((match f k1 with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_subkind));
                 parser_kind_metadata =
                   ((match match f k1 with
                           | { parser_kind_low; parser_kind_high;
                               parser_kind_subkind; parser_kind_metadata;_}
                               -> parser_kind_metadata
                     with
                     | FStar_Pervasives_Native.Some (ParserKindMetadataFail)
                         ->
                         FStar_Pervasives_Native.Some ParserKindMetadataFail
                     | uu___1 -> FStar_Pervasives_Native.None))
               }
           | (FStar_Pervasives_Native.Some (ParserKindMetadataFail), uu___)
               ->
               {
                 parser_kind_low =
                   ((match k' with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_low));
                 parser_kind_high =
                   ((match k' with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_high));
                 parser_kind_subkind =
                   ((match k' with
                     | { parser_kind_low; parser_kind_high;
                         parser_kind_subkind; parser_kind_metadata;_} ->
                         parser_kind_subkind));
                 parser_kind_metadata = FStar_Pervasives_Native.None
               }
           | uu___ ->
               {
                 parser_kind_low =
                   (if
                      (match f k1 with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_low)
                        <
                        ((match k' with
                          | { parser_kind_low; parser_kind_high;
                              parser_kind_subkind; parser_kind_metadata;_} ->
                              parser_kind_low))
                    then
                      (match f k1 with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_low)
                    else
                      (match k' with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_low));
                 parser_kind_high =
                   (if
                      (if
                         match match f k1 with
                               | { parser_kind_low; parser_kind_high;
                                   parser_kind_subkind;
                                   parser_kind_metadata;_} ->
                                   parser_kind_high
                         with
                         | FStar_Pervasives_Native.Some uu___1 -> true
                         | uu___1 -> false
                       then
                         match match k' with
                               | { parser_kind_low; parser_kind_high;
                                   parser_kind_subkind;
                                   parser_kind_metadata;_} ->
                                   parser_kind_high
                         with
                         | FStar_Pervasives_Native.Some uu___1 -> true
                         | uu___1 -> false
                       else false)
                    then
                      (if
                         (match match k' with
                                | { parser_kind_low; parser_kind_high;
                                    parser_kind_subkind;
                                    parser_kind_metadata;_} ->
                                    parser_kind_high
                          with
                          | FStar_Pervasives_Native.Some y -> y) <
                           (match match f k1 with
                                  | { parser_kind_low; parser_kind_high;
                                      parser_kind_subkind;
                                      parser_kind_metadata;_} ->
                                      parser_kind_high
                            with
                            | FStar_Pervasives_Native.Some y -> y)
                       then
                         match f k1 with
                         | { parser_kind_low; parser_kind_high;
                             parser_kind_subkind; parser_kind_metadata;_} ->
                             parser_kind_high
                       else
                         (match k' with
                          | { parser_kind_low; parser_kind_high;
                              parser_kind_subkind; parser_kind_metadata;_} ->
                              parser_kind_high))
                    else FStar_Pervasives_Native.None);
                 parser_kind_subkind =
                   (if
                      (match f k1 with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_subkind)
                        =
                        ((match k' with
                          | { parser_kind_low; parser_kind_high;
                              parser_kind_subkind; parser_kind_metadata;_} ->
                              parser_kind_subkind))
                    then
                      (match f k1 with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_subkind)
                    else FStar_Pervasives_Native.None);
                 parser_kind_metadata =
                   (if
                      (match f k1 with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_metadata)
                        =
                        ((match k' with
                          | { parser_kind_low; parser_kind_high;
                              parser_kind_subkind; parser_kind_metadata;_} ->
                              parser_kind_metadata))
                    then
                      (match f k1 with
                       | { parser_kind_low; parser_kind_high;
                           parser_kind_subkind; parser_kind_metadata;_} ->
                           parser_kind_metadata)
                    else FStar_Pervasives_Native.None)
               })
let (glb_list : parser_kind Prims.list -> parser_kind) =
  fun l -> glb_list_of (fun x -> x) l
let coerce : 't2 't1 . 't1 -> 't2 = fun uu___ -> (fun x -> Obj.magic x) uu___
let coerce' : 't2 't1 . 't1 -> 't2 =
  fun uu___ -> (fun x -> Obj.magic x) uu___



type 't bare_serializer = unit
type ('k, 't, 'p, 'f) serializer_correct = unit

type ('k, 't, 'p, 'f) serializer_complete = unit

type ('k, 't, 'p) serializer = unit















let seq_upd_seq :
  't .
    't FStar_Seq_Base.seq ->
      Prims.nat -> 't FStar_Seq_Base.seq -> 't FStar_Seq_Base.seq
  =
  fun s ->
    fun i ->
      fun s' ->
        FStar_Seq_Base.append (FStar_Seq_Base.slice s Prims.int_zero i)
          (FStar_Seq_Base.append s'
             (FStar_Seq_Base.slice s (i + (FStar_Seq_Base.length s'))
                (FStar_Seq_Base.length s)))

















let seq_upd_bw_seq :
  't .
    't FStar_Seq_Base.seq ->
      Prims.nat -> 't FStar_Seq_Base.seq -> 't FStar_Seq_Base.seq
  =
  fun s ->
    fun i ->
      fun s' ->
        seq_upd_seq s
          (((FStar_Seq_Base.length s) - i) - (FStar_Seq_Base.length s')) s'

type ('tagut, 'dataut, 'taguofudata, 'x) refine_with_tag = 'dataut