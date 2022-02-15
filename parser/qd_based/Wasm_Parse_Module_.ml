open Prims
type module_ =
  {
  _m: Wasm_Parse_Magic_.magic_ ;
  _v: Wasm_Parse_Version.version ;
  functype: Wasm_Parse_Opt_typesec.opt_typesec ;
  import: Wasm_Parse_Opt_importsec.opt_importsec ;
  typeidx: Wasm_Parse_Opt_funcsec.opt_funcsec ;
  table: Wasm_Parse_Opt_tablesec.opt_tablesec ;
  mem: Wasm_Parse_Opt_memsec.opt_memsec ;
  global: Wasm_Parse_Opt_globalsec.opt_globalsec ;
  export: Wasm_Parse_Opt_exportsec.opt_exportsec ;
  start: Wasm_Parse_Opt_startsec.opt_startsec ;
  elem: Wasm_Parse_Opt_elemsec.opt_elemsec ;
  code: Wasm_Parse_Opt_codesec.opt_codesec ;
  data: Wasm_Parse_Opt_datasec.opt_datasec }
let (__proj__Mkmodule___item___m : module_ -> Wasm_Parse_Magic_.magic_) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> _m
let (__proj__Mkmodule___item___v : module_ -> Wasm_Parse_Version.version) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> _v
let (__proj__Mkmodule___item__functype :
  module_ -> Wasm_Parse_Opt_typesec.opt_typesec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> functype
let (__proj__Mkmodule___item__import :
  module_ -> Wasm_Parse_Opt_importsec.opt_importsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> import
let (__proj__Mkmodule___item__typeidx :
  module_ -> Wasm_Parse_Opt_funcsec.opt_funcsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> typeidx
let (__proj__Mkmodule___item__table :
  module_ -> Wasm_Parse_Opt_tablesec.opt_tablesec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> table
let (__proj__Mkmodule___item__mem :
  module_ -> Wasm_Parse_Opt_memsec.opt_memsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> mem
let (__proj__Mkmodule___item__global :
  module_ -> Wasm_Parse_Opt_globalsec.opt_globalsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> global
let (__proj__Mkmodule___item__export :
  module_ -> Wasm_Parse_Opt_exportsec.opt_exportsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> export
let (__proj__Mkmodule___item__start :
  module_ -> Wasm_Parse_Opt_startsec.opt_startsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> start
let (__proj__Mkmodule___item__elem :
  module_ -> Wasm_Parse_Opt_elemsec.opt_elemsec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> elem
let (__proj__Mkmodule___item__code :
  module_ -> Wasm_Parse_Opt_codesec.opt_codesec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> code
let (__proj__Mkmodule___item__data :
  module_ -> Wasm_Parse_Opt_datasec.opt_datasec) =
  fun projectee ->
    match projectee with
    | { _m; _v; functype; import; typeidx; table; mem; global; export; 
        start; elem; code; data;_} -> data
type module_' =
  ((((Wasm_Parse_Magic_.magic_ * Wasm_Parse_Version.version) *
    (Wasm_Parse_Opt_typesec.opt_typesec *
    Wasm_Parse_Opt_importsec.opt_importsec)) *
    ((Wasm_Parse_Opt_funcsec.opt_funcsec *
    Wasm_Parse_Opt_tablesec.opt_tablesec) * (Wasm_Parse_Opt_memsec.opt_memsec
    * Wasm_Parse_Opt_globalsec.opt_globalsec))) *
    (((Wasm_Parse_Opt_exportsec.opt_exportsec *
    Wasm_Parse_Opt_startsec.opt_startsec) *
    (Wasm_Parse_Opt_elemsec.opt_elemsec *
    Wasm_Parse_Opt_codesec.opt_codesec)) *
    Wasm_Parse_Opt_datasec.opt_datasec))
let (synth_module_ : module_' -> module_) =
  fun x ->
    match x with
    | ((((_m, _v), (functype, import)), ((typeidx, table), (mem, global))),
       (((export, start), (elem, code)), data)) ->
        {
          _m;
          _v;
          functype;
          import;
          typeidx;
          table;
          mem;
          global;
          export;
          start;
          elem;
          code;
          data
        }
let (synth_module__recip : module_ -> module_') =
  fun x ->
    (((((x._m), (x._v)), ((x.functype), (x.import))),
       (((x.typeidx), (x.table)), ((x.mem), (x.global)))),
      ((((x.export), (x.start)), ((x.elem), (x.code))), (x.data)))




let (module_'_parser32 :
  LowParse_SLow_Base.bytes32 ->
    (module_' * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match match Wasm_Parse_Magic_.magic__parser32 input with
                      | FStar_Pervasives_Native.Some (v, l) ->
                          let input' =
                            FStar_Bytes.slice input l (FStar_Bytes.len input) in
                          (match Wasm_Parse_Version.version_parser32 input'
                           with
                           | FStar_Pervasives_Native.Some (v', l') ->
                               FStar_Pervasives_Native.Some
                                 ((v, v'), (FStar_UInt32.add l l'))
                           | uu___ -> FStar_Pervasives_Native.None)
                      | uu___ -> FStar_Pervasives_Native.None
                with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match match Wasm_Parse_Opt_typesec.opt_typesec_parser32
                                   input'
                           with
                           | FStar_Pervasives_Native.Some (v1, l1) ->
                               let input'1 =
                                 FStar_Bytes.slice input' l1
                                   (FStar_Bytes.len input') in
                               (match Wasm_Parse_Opt_importsec.opt_importsec_parser32
                                        input'1
                                with
                                | FStar_Pervasives_Native.Some (v', l') ->
                                    FStar_Pervasives_Native.Some
                                      ((v1, v'), (FStar_UInt32.add l1 l'))
                                | uu___ -> FStar_Pervasives_Native.None)
                           | uu___ -> FStar_Pervasives_Native.None
                     with
                     | FStar_Pervasives_Native.Some (v', l') ->
                         FStar_Pervasives_Native.Some
                           ((v, v'), (FStar_UInt32.add l l'))
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match match match Wasm_Parse_Opt_funcsec.opt_funcsec_parser32
                                   input'
                           with
                           | FStar_Pervasives_Native.Some (v1, l1) ->
                               let input'1 =
                                 FStar_Bytes.slice input' l1
                                   (FStar_Bytes.len input') in
                               (match Wasm_Parse_Opt_tablesec.opt_tablesec_parser32
                                        input'1
                                with
                                | FStar_Pervasives_Native.Some (v', l') ->
                                    FStar_Pervasives_Native.Some
                                      ((v1, v'), (FStar_UInt32.add l1 l'))
                                | uu___ -> FStar_Pervasives_Native.None)
                           | uu___ -> FStar_Pervasives_Native.None
                     with
                     | FStar_Pervasives_Native.Some (v1, l1) ->
                         let input'1 =
                           FStar_Bytes.slice input' l1
                             (FStar_Bytes.len input') in
                         (match match Wasm_Parse_Opt_memsec.opt_memsec_parser32
                                        input'1
                                with
                                | FStar_Pervasives_Native.Some (v2, l2) ->
                                    let input'2 =
                                      FStar_Bytes.slice input'1 l2
                                        (FStar_Bytes.len input'1) in
                                    (match Wasm_Parse_Opt_globalsec.opt_globalsec_parser32
                                             input'2
                                     with
                                     | FStar_Pervasives_Native.Some (v', l')
                                         ->
                                         FStar_Pervasives_Native.Some
                                           ((v2, v'),
                                             (FStar_UInt32.add l2 l'))
                                     | uu___ -> FStar_Pervasives_Native.None)
                                | uu___ -> FStar_Pervasives_Native.None
                          with
                          | FStar_Pervasives_Native.Some (v', l') ->
                              FStar_Pervasives_Native.Some
                                ((v1, v'), (FStar_UInt32.add l1 l'))
                          | uu___ -> FStar_Pervasives_Native.None)
                     | uu___ -> FStar_Pervasives_Native.None
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v, l) ->
        let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
        (match match match match Wasm_Parse_Opt_exportsec.opt_exportsec_parser32
                                   input'
                           with
                           | FStar_Pervasives_Native.Some (v1, l1) ->
                               let input'1 =
                                 FStar_Bytes.slice input' l1
                                   (FStar_Bytes.len input') in
                               (match Wasm_Parse_Opt_startsec.opt_startsec_parser32
                                        input'1
                                with
                                | FStar_Pervasives_Native.Some (v', l') ->
                                    FStar_Pervasives_Native.Some
                                      ((v1, v'), (FStar_UInt32.add l1 l'))
                                | uu___ -> FStar_Pervasives_Native.None)
                           | uu___ -> FStar_Pervasives_Native.None
                     with
                     | FStar_Pervasives_Native.Some (v1, l1) ->
                         let input'1 =
                           FStar_Bytes.slice input' l1
                             (FStar_Bytes.len input') in
                         (match match Wasm_Parse_Opt_elemsec.opt_elemsec_parser32
                                        input'1
                                with
                                | FStar_Pervasives_Native.Some (v2, l2) ->
                                    let input'2 =
                                      FStar_Bytes.slice input'1 l2
                                        (FStar_Bytes.len input'1) in
                                    (match Wasm_Parse_Opt_codesec.opt_codesec_parser32
                                             input'2
                                     with
                                     | FStar_Pervasives_Native.Some (v', l')
                                         ->
                                         FStar_Pervasives_Native.Some
                                           ((v2, v'),
                                             (FStar_UInt32.add l2 l'))
                                     | uu___ -> FStar_Pervasives_Native.None)
                                | uu___ -> FStar_Pervasives_Native.None
                          with
                          | FStar_Pervasives_Native.Some (v', l') ->
                              FStar_Pervasives_Native.Some
                                ((v1, v'), (FStar_UInt32.add l1 l'))
                          | uu___ -> FStar_Pervasives_Native.None)
                     | uu___ -> FStar_Pervasives_Native.None
               with
               | FStar_Pervasives_Native.Some (v1, l1) ->
                   let input'1 =
                     FStar_Bytes.slice input' l1 (FStar_Bytes.len input') in
                   (match Wasm_Parse_Opt_datasec.opt_datasec_parser32 input'1
                    with
                    | FStar_Pervasives_Native.Some (v', l') ->
                        FStar_Pervasives_Native.Some
                          ((v1, v'), (FStar_UInt32.add l1 l'))
                    | uu___ -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None
         with
         | FStar_Pervasives_Native.Some (v', l') ->
             FStar_Pervasives_Native.Some ((v, v'), (FStar_UInt32.add l l'))
         | uu___ -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None
let (module__parser32 :
  LowParse_SLow_Base.bytes32 ->
    (module_ * FStar_UInt32.t) FStar_Pervasives_Native.option)
  =
  fun input ->
    match match match match match Wasm_Parse_Magic_.magic__parser32 input
                            with
                            | FStar_Pervasives_Native.Some (v, l) ->
                                let input' =
                                  FStar_Bytes.slice input l
                                    (FStar_Bytes.len input) in
                                (match Wasm_Parse_Version.version_parser32
                                         input'
                                 with
                                 | FStar_Pervasives_Native.Some (v', l') ->
                                     FStar_Pervasives_Native.Some
                                       ((v, v'), (FStar_UInt32.add l l'))
                                 | uu___ -> FStar_Pervasives_Native.None)
                            | uu___ -> FStar_Pervasives_Native.None
                      with
                      | FStar_Pervasives_Native.Some (v, l) ->
                          let input' =
                            FStar_Bytes.slice input l (FStar_Bytes.len input) in
                          (match match Wasm_Parse_Opt_typesec.opt_typesec_parser32
                                         input'
                                 with
                                 | FStar_Pervasives_Native.Some (v1, l1) ->
                                     let input'1 =
                                       FStar_Bytes.slice input' l1
                                         (FStar_Bytes.len input') in
                                     (match Wasm_Parse_Opt_importsec.opt_importsec_parser32
                                              input'1
                                      with
                                      | FStar_Pervasives_Native.Some 
                                          (v', l') ->
                                          FStar_Pervasives_Native.Some
                                            ((v1, v'),
                                              (FStar_UInt32.add l1 l'))
                                      | uu___ -> FStar_Pervasives_Native.None)
                                 | uu___ -> FStar_Pervasives_Native.None
                           with
                           | FStar_Pervasives_Native.Some (v', l') ->
                               FStar_Pervasives_Native.Some
                                 ((v, v'), (FStar_UInt32.add l l'))
                           | uu___ -> FStar_Pervasives_Native.None)
                      | uu___ -> FStar_Pervasives_Native.None
                with
                | FStar_Pervasives_Native.Some (v, l) ->
                    let input' =
                      FStar_Bytes.slice input l (FStar_Bytes.len input) in
                    (match match match Wasm_Parse_Opt_funcsec.opt_funcsec_parser32
                                         input'
                                 with
                                 | FStar_Pervasives_Native.Some (v1, l1) ->
                                     let input'1 =
                                       FStar_Bytes.slice input' l1
                                         (FStar_Bytes.len input') in
                                     (match Wasm_Parse_Opt_tablesec.opt_tablesec_parser32
                                              input'1
                                      with
                                      | FStar_Pervasives_Native.Some 
                                          (v', l') ->
                                          FStar_Pervasives_Native.Some
                                            ((v1, v'),
                                              (FStar_UInt32.add l1 l'))
                                      | uu___ -> FStar_Pervasives_Native.None)
                                 | uu___ -> FStar_Pervasives_Native.None
                           with
                           | FStar_Pervasives_Native.Some (v1, l1) ->
                               let input'1 =
                                 FStar_Bytes.slice input' l1
                                   (FStar_Bytes.len input') in
                               (match match Wasm_Parse_Opt_memsec.opt_memsec_parser32
                                              input'1
                                      with
                                      | FStar_Pervasives_Native.Some 
                                          (v2, l2) ->
                                          let input'2 =
                                            FStar_Bytes.slice input'1 l2
                                              (FStar_Bytes.len input'1) in
                                          (match Wasm_Parse_Opt_globalsec.opt_globalsec_parser32
                                                   input'2
                                           with
                                           | FStar_Pervasives_Native.Some
                                               (v', l') ->
                                               FStar_Pervasives_Native.Some
                                                 ((v2, v'),
                                                   (FStar_UInt32.add l2 l'))
                                           | uu___ ->
                                               FStar_Pervasives_Native.None)
                                      | uu___ -> FStar_Pervasives_Native.None
                                with
                                | FStar_Pervasives_Native.Some (v', l') ->
                                    FStar_Pervasives_Native.Some
                                      ((v1, v'), (FStar_UInt32.add l1 l'))
                                | uu___ -> FStar_Pervasives_Native.None)
                           | uu___ -> FStar_Pervasives_Native.None
                     with
                     | FStar_Pervasives_Native.Some (v', l') ->
                         FStar_Pervasives_Native.Some
                           ((v, v'), (FStar_UInt32.add l l'))
                     | uu___ -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
          with
          | FStar_Pervasives_Native.Some (v, l) ->
              let input' = FStar_Bytes.slice input l (FStar_Bytes.len input) in
              (match match match match Wasm_Parse_Opt_exportsec.opt_exportsec_parser32
                                         input'
                                 with
                                 | FStar_Pervasives_Native.Some (v1, l1) ->
                                     let input'1 =
                                       FStar_Bytes.slice input' l1
                                         (FStar_Bytes.len input') in
                                     (match Wasm_Parse_Opt_startsec.opt_startsec_parser32
                                              input'1
                                      with
                                      | FStar_Pervasives_Native.Some 
                                          (v', l') ->
                                          FStar_Pervasives_Native.Some
                                            ((v1, v'),
                                              (FStar_UInt32.add l1 l'))
                                      | uu___ -> FStar_Pervasives_Native.None)
                                 | uu___ -> FStar_Pervasives_Native.None
                           with
                           | FStar_Pervasives_Native.Some (v1, l1) ->
                               let input'1 =
                                 FStar_Bytes.slice input' l1
                                   (FStar_Bytes.len input') in
                               (match match Wasm_Parse_Opt_elemsec.opt_elemsec_parser32
                                              input'1
                                      with
                                      | FStar_Pervasives_Native.Some 
                                          (v2, l2) ->
                                          let input'2 =
                                            FStar_Bytes.slice input'1 l2
                                              (FStar_Bytes.len input'1) in
                                          (match Wasm_Parse_Opt_codesec.opt_codesec_parser32
                                                   input'2
                                           with
                                           | FStar_Pervasives_Native.Some
                                               (v', l') ->
                                               FStar_Pervasives_Native.Some
                                                 ((v2, v'),
                                                   (FStar_UInt32.add l2 l'))
                                           | uu___ ->
                                               FStar_Pervasives_Native.None)
                                      | uu___ -> FStar_Pervasives_Native.None
                                with
                                | FStar_Pervasives_Native.Some (v', l') ->
                                    FStar_Pervasives_Native.Some
                                      ((v1, v'), (FStar_UInt32.add l1 l'))
                                | uu___ -> FStar_Pervasives_Native.None)
                           | uu___ -> FStar_Pervasives_Native.None
                     with
                     | FStar_Pervasives_Native.Some (v1, l1) ->
                         let input'1 =
                           FStar_Bytes.slice input' l1
                             (FStar_Bytes.len input') in
                         (match Wasm_Parse_Opt_datasec.opt_datasec_parser32
                                  input'1
                          with
                          | FStar_Pervasives_Native.Some (v', l') ->
                              FStar_Pervasives_Native.Some
                                ((v1, v'), (FStar_UInt32.add l1 l'))
                          | uu___ -> FStar_Pervasives_Native.None)
                     | uu___ -> FStar_Pervasives_Native.None
               with
               | FStar_Pervasives_Native.Some (v', l') ->
                   FStar_Pervasives_Native.Some
                     ((v, v'), (FStar_UInt32.add l l'))
               | uu___ -> FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
    with
    | FStar_Pervasives_Native.Some (v1, consumed) ->
        FStar_Pervasives_Native.Some
          (((match v1 with
             | ((((_m, _v), (functype, import)),
                 ((typeidx, table), (mem, global))),
                (((export, start), (elem, code)), data)) ->
                 {
                   _m;
                   _v;
                   functype;
                   import;
                   typeidx;
                   table;
                   mem;
                   global;
                   export;
                   start;
                   elem;
                   code;
                   data
                 })), consumed)
    | uu___ -> FStar_Pervasives_Native.None
let (module_'_serializer32 : module_' -> LowParse_SLow_Base.bytes32) =
  fun input ->
    match input with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                match fs1 with
                | (fs2, sn2) ->
                    let output12 =
                      match fs2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Magic_.magic__serializer32 fs3 in
                          let output2 =
                            Wasm_Parse_Version.version_serializer32 sn3 in
                          FStar_Bytes.append output13 output2 in
                    let output2 =
                      match sn2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_typesec.opt_typesec_serializer32
                              fs3 in
                          let output21 =
                            Wasm_Parse_Opt_importsec.opt_importsec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output21 in
                    FStar_Bytes.append output12 output2 in
              let output2 =
                match sn1 with
                | (fs2, sn2) ->
                    let output12 =
                      match fs2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_funcsec.opt_funcsec_serializer32
                              fs3 in
                          let output21 =
                            Wasm_Parse_Opt_tablesec.opt_tablesec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output21 in
                    let output21 =
                      match sn2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_memsec.opt_memsec_serializer32 fs3 in
                          let output22 =
                            Wasm_Parse_Opt_globalsec.opt_globalsec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output22 in
                    FStar_Bytes.append output12 output21 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          match sn with
          | (fs1, sn1) ->
              let output11 =
                match fs1 with
                | (fs2, sn2) ->
                    let output12 =
                      match fs2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_exportsec.opt_exportsec_serializer32
                              fs3 in
                          let output21 =
                            Wasm_Parse_Opt_startsec.opt_startsec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output21 in
                    let output21 =
                      match sn2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_elemsec.opt_elemsec_serializer32
                              fs3 in
                          let output22 =
                            Wasm_Parse_Opt_codesec.opt_codesec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output22 in
                    FStar_Bytes.append output12 output21 in
              let output21 =
                Wasm_Parse_Opt_datasec.opt_datasec_serializer32 sn1 in
              FStar_Bytes.append output11 output21 in
        FStar_Bytes.append output1 output2
let (module__serializer32 : module_ -> LowParse_SLow_Base.bytes32) =
  fun input ->
    let x =
      (((((input._m), (input._v)), ((input.functype), (input.import))),
         (((input.typeidx), (input.table)), ((input.mem), (input.global)))),
        ((((input.export), (input.start)), ((input.elem), (input.code))),
          (input.data))) in
    match x with
    | (fs, sn) ->
        let output1 =
          match fs with
          | (fs1, sn1) ->
              let output11 =
                match fs1 with
                | (fs2, sn2) ->
                    let output12 =
                      match fs2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Magic_.magic__serializer32 fs3 in
                          let output2 =
                            Wasm_Parse_Version.version_serializer32 sn3 in
                          FStar_Bytes.append output13 output2 in
                    let output2 =
                      match sn2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_typesec.opt_typesec_serializer32
                              fs3 in
                          let output21 =
                            Wasm_Parse_Opt_importsec.opt_importsec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output21 in
                    FStar_Bytes.append output12 output2 in
              let output2 =
                match sn1 with
                | (fs2, sn2) ->
                    let output12 =
                      match fs2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_funcsec.opt_funcsec_serializer32
                              fs3 in
                          let output21 =
                            Wasm_Parse_Opt_tablesec.opt_tablesec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output21 in
                    let output21 =
                      match sn2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_memsec.opt_memsec_serializer32 fs3 in
                          let output22 =
                            Wasm_Parse_Opt_globalsec.opt_globalsec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output22 in
                    FStar_Bytes.append output12 output21 in
              FStar_Bytes.append output11 output2 in
        let output2 =
          match sn with
          | (fs1, sn1) ->
              let output11 =
                match fs1 with
                | (fs2, sn2) ->
                    let output12 =
                      match fs2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_exportsec.opt_exportsec_serializer32
                              fs3 in
                          let output21 =
                            Wasm_Parse_Opt_startsec.opt_startsec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output21 in
                    let output21 =
                      match sn2 with
                      | (fs3, sn3) ->
                          let output13 =
                            Wasm_Parse_Opt_elemsec.opt_elemsec_serializer32
                              fs3 in
                          let output22 =
                            Wasm_Parse_Opt_codesec.opt_codesec_serializer32
                              sn3 in
                          FStar_Bytes.append output13 output22 in
                    FStar_Bytes.append output12 output21 in
              let output21 =
                Wasm_Parse_Opt_datasec.opt_datasec_serializer32 sn1 in
              FStar_Bytes.append output11 output21 in
        FStar_Bytes.append output1 output2
let (module_'_size32 : module_' -> FStar_UInt32.t) =
  fun x ->
    match x with
    | (x1, x2) ->
        let v1 =
          match x1 with
          | (x11, x21) ->
              let v11 =
                match x11 with
                | (x12, x22) ->
                    let v12 =
                      match x12 with
                      | (x13, x23) ->
                          let v13 = Wasm_Parse_Magic_.magic__size32 x13 in
                          let v2 = Wasm_Parse_Version.version_size32 x23 in
                          let res =
                            if
                              FStar_UInt32.lt
                                (FStar_UInt32.sub
                                   (FStar_UInt32.uint_to_t
                                      (Prims.parse_int "4294967295")) v2) v13
                            then
                              FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")
                            else FStar_UInt32.add v13 v2 in
                          res in
                    let v2 =
                      match x22 with
                      | (x13, x23) ->
                          let v13 =
                            Wasm_Parse_Opt_typesec.opt_typesec_size32 x13 in
                          let v21 =
                            Wasm_Parse_Opt_importsec.opt_importsec_size32 x23 in
                          let res =
                            if
                              FStar_UInt32.lt
                                (FStar_UInt32.sub
                                   (FStar_UInt32.uint_to_t
                                      (Prims.parse_int "4294967295")) v21)
                                v13
                            then
                              FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")
                            else FStar_UInt32.add v13 v21 in
                          res in
                    let res =
                      if
                        FStar_UInt32.lt
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")) v2) v12
                      then
                        FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                      else FStar_UInt32.add v12 v2 in
                    res in
              let v2 =
                match x21 with
                | (x12, x22) ->
                    let v12 =
                      match x12 with
                      | (x13, x23) ->
                          let v13 =
                            Wasm_Parse_Opt_funcsec.opt_funcsec_size32 x13 in
                          let v21 =
                            Wasm_Parse_Opt_tablesec.opt_tablesec_size32 x23 in
                          let res =
                            if
                              FStar_UInt32.lt
                                (FStar_UInt32.sub
                                   (FStar_UInt32.uint_to_t
                                      (Prims.parse_int "4294967295")) v21)
                                v13
                            then
                              FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")
                            else FStar_UInt32.add v13 v21 in
                          res in
                    let v21 =
                      match x22 with
                      | (x13, x23) ->
                          let v13 =
                            Wasm_Parse_Opt_memsec.opt_memsec_size32 x13 in
                          let v22 =
                            Wasm_Parse_Opt_globalsec.opt_globalsec_size32 x23 in
                          let res =
                            if
                              FStar_UInt32.lt
                                (FStar_UInt32.sub
                                   (FStar_UInt32.uint_to_t
                                      (Prims.parse_int "4294967295")) v22)
                                v13
                            then
                              FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")
                            else FStar_UInt32.add v13 v22 in
                          res in
                    let res =
                      if
                        FStar_UInt32.lt
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")) v21) v12
                      then
                        FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                      else FStar_UInt32.add v12 v21 in
                    res in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v2) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v2 in
              res in
        let v2 =
          match x2 with
          | (x11, x21) ->
              let v11 =
                match x11 with
                | (x12, x22) ->
                    let v12 =
                      match x12 with
                      | (x13, x23) ->
                          let v13 =
                            Wasm_Parse_Opt_exportsec.opt_exportsec_size32 x13 in
                          let v21 =
                            Wasm_Parse_Opt_startsec.opt_startsec_size32 x23 in
                          let res =
                            if
                              FStar_UInt32.lt
                                (FStar_UInt32.sub
                                   (FStar_UInt32.uint_to_t
                                      (Prims.parse_int "4294967295")) v21)
                                v13
                            then
                              FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")
                            else FStar_UInt32.add v13 v21 in
                          res in
                    let v21 =
                      match x22 with
                      | (x13, x23) ->
                          let v13 =
                            Wasm_Parse_Opt_elemsec.opt_elemsec_size32 x13 in
                          let v22 =
                            Wasm_Parse_Opt_codesec.opt_codesec_size32 x23 in
                          let res =
                            if
                              FStar_UInt32.lt
                                (FStar_UInt32.sub
                                   (FStar_UInt32.uint_to_t
                                      (Prims.parse_int "4294967295")) v22)
                                v13
                            then
                              FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")
                            else FStar_UInt32.add v13 v22 in
                          res in
                    let res =
                      if
                        FStar_UInt32.lt
                          (FStar_UInt32.sub
                             (FStar_UInt32.uint_to_t
                                (Prims.parse_int "4294967295")) v21) v12
                      then
                        FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                      else FStar_UInt32.add v12 v21 in
                    res in
              let v21 = Wasm_Parse_Opt_datasec.opt_datasec_size32 x21 in
              let res =
                if
                  FStar_UInt32.lt
                    (FStar_UInt32.sub
                       (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                       v21) v11
                then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
                else FStar_UInt32.add v11 v21 in
              res in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v1
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v1 v2 in
        res
let (module__size32 : module_ -> FStar_UInt32.t) =
  fun input ->
    let v1 =
      let v11 =
        let v12 =
          let v13 = Wasm_Parse_Magic_.magic__size32 input._m in
          let v2 = Wasm_Parse_Version.version_size32 input._v in
          let res =
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
                v13
            then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
            else FStar_UInt32.add v13 v2 in
          res in
        let v2 =
          let v13 = Wasm_Parse_Opt_typesec.opt_typesec_size32 input.functype in
          let v21 =
            Wasm_Parse_Opt_importsec.opt_importsec_size32 input.import in
          let res =
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                   v21) v13
            then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
            else FStar_UInt32.add v13 v21 in
          res in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
              v12
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v12 v2 in
        res in
      let v2 =
        let v12 =
          let v13 = Wasm_Parse_Opt_funcsec.opt_funcsec_size32 input.typeidx in
          let v21 = Wasm_Parse_Opt_tablesec.opt_tablesec_size32 input.table in
          let res =
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                   v21) v13
            then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
            else FStar_UInt32.add v13 v21 in
          res in
        let v21 =
          let v13 = Wasm_Parse_Opt_memsec.opt_memsec_size32 input.mem in
          let v22 =
            Wasm_Parse_Opt_globalsec.opt_globalsec_size32 input.global in
          let res =
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                   v22) v13
            then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
            else FStar_UInt32.add v13 v22 in
          res in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v21)
              v12
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v12 v21 in
        res in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v2 in
      res in
    let v2 =
      let v11 =
        let v12 =
          let v13 =
            Wasm_Parse_Opt_exportsec.opt_exportsec_size32 input.export in
          let v21 = Wasm_Parse_Opt_startsec.opt_startsec_size32 input.start in
          let res =
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                   v21) v13
            then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
            else FStar_UInt32.add v13 v21 in
          res in
        let v21 =
          let v13 = Wasm_Parse_Opt_elemsec.opt_elemsec_size32 input.elem in
          let v22 = Wasm_Parse_Opt_codesec.opt_codesec_size32 input.code in
          let res =
            if
              FStar_UInt32.lt
                (FStar_UInt32.sub
                   (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295"))
                   v22) v13
            then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
            else FStar_UInt32.add v13 v22 in
          res in
        let res =
          if
            FStar_UInt32.lt
              (FStar_UInt32.sub
                 (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v21)
              v12
          then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
          else FStar_UInt32.add v12 v21 in
        res in
      let v21 = Wasm_Parse_Opt_datasec.opt_datasec_size32 input.data in
      let res =
        if
          FStar_UInt32.lt
            (FStar_UInt32.sub
               (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v21)
            v11
        then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
        else FStar_UInt32.add v11 v21 in
      res in
    let res =
      if
        FStar_UInt32.lt
          (FStar_UInt32.sub
             (FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")) v2) v1
      then FStar_UInt32.uint_to_t (Prims.parse_int "4294967295")
      else FStar_UInt32.add v1 v2 in
    res
