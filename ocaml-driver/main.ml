exception Unimplemented

let parse_and_compile
      (wasm_data:bytes)
      (last_pass:string)
      (mem_pages:int)
      (peephole_optimize:bool)
    : unit =
  let m:Wasm_Ast.module_ = Wasm_Parse_Parser.parse (Bytes.to_string wasm_data) in
  Compile_All.compile_and_print m last_pass (Z.of_int mem_pages) peephole_optimize


let readfile filename =
  let in_ch = open_in_bin filename in
  let n = in_channel_length in_ch in
  let buf = Bytes.create n in
  really_input in_ch buf 0 n;
  close_in in_ch;
  buf

(* default argument values *)
let arg_last_pass = ref "wasi_sbx"
let arg_peephole = ref false
let arg_mem_pages = ref 160
let arg_filepath = ref ""

let allowed_last_pass = ["wasm"; "simp"; "elim"; "alloc"; "x64"; "sbx"; "wasi_x64"; "wasi_sbx"]

let arg_usage = ("Usage:\n  "
                 ^ Sys.argv.(0)
                 ^ " [--peephole-optimize]"
                 ^ " [-l lastpass=" ^ !arg_last_pass ^ "]"
                 ^ " [-p mem_pages_of_64k=" ^ string_of_int !arg_mem_pages ^ "]"
                 ^ " {input.vasm}"
                 ^ "\n")

let arg_last_pass_fun arg =
  if List.mem arg allowed_last_pass then
    arg_last_pass := arg
  else (
    raise (Arg.Bad ("Invalid last pass. Allowed: " ^ String.concat ", " allowed_last_pass))
  )

let arg_speclist = Arg.align [
    ("--peephole-optimize", Arg.Set arg_peephole, " Enable peephole optimization");
    ("-l", Arg.String arg_last_pass_fun, "LASTPASS Set last pass of the compiler");
    ("-p", Arg.Set_int arg_mem_pages, "MEMPAGES Set number of 64k pages to sandbox");
  ]

let arg_anon arg =
  if !arg_filepath = "" then (
    arg_filepath := arg
  ) else (
    raise (Arg.Bad "Multiple input files not supported right now")
  )

let () =
  Arg.parse arg_speclist arg_anon arg_usage;
  if !arg_filepath = "" then (
    Arg.usage arg_speclist arg_usage
  ) else (
    let buf = readfile !arg_filepath in
    parse_and_compile buf !arg_last_pass !arg_mem_pages !arg_peephole
  )
