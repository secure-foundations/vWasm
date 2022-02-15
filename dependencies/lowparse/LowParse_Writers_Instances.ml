open Prims


let (parse_synth :
  LowParse_Writers_Parser.parser ->
    unit -> unit -> unit -> LowParse_Writers_Parser.parser)
  =
  fun p1 ->
    fun t2 ->
      fun f2 ->
        fun f1 ->
          LowParse_Writers_Parser.Parser
            ((),
              {
                LowParse_Writers_Parser.kind =
                  (match match p1 with
                         | LowParse_Writers_Parser.Parser (t, p) -> p
                   with
                   | { LowParse_Writers_Parser.kind = kind;
                       LowParse_Writers_Parser.parser = parser;
                       LowParse_Writers_Parser.serializer = serializer;
                       LowParse_Writers_Parser.jumper = jumper;_} -> kind);
                LowParse_Writers_Parser.parser = ();
                LowParse_Writers_Parser.serializer = ();
                LowParse_Writers_Parser.jumper =
                  (fun rrel ->
                     fun rel ->
                       fun input ->
                         fun pos ->
                           let h = FStar_HyperStack_ST.get () in
                           match match p1 with
                                 | LowParse_Writers_Parser.Parser (t, p) -> p
                           with
                           | { LowParse_Writers_Parser.kind = kind;
                               LowParse_Writers_Parser.parser = parser;
                               LowParse_Writers_Parser.serializer =
                                 serializer;
                               LowParse_Writers_Parser.jumper = jumper;_} ->
                               jumper () () input pos)
              })











