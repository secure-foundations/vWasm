module Compile.All

open Words_s

open Common.Err
open Semantics.Common.CFG
open Semantics.Common.CFG.Printer
open Semantics.Common.CFG.LowLevelSemantics

let compile (m1:Wasm.Ast.module_) (last_pass:string) (mem_pages:nat32) (peephole_optimize:bool) : Err_ (list string) =
  if last_pass = "wasm" then ["wasm printing unimplemented"] else (
    let m2 = Compiler.Phase.Simplify.compile_module m1 mem_pages in
    if last_pass = "simp" then [Wasm_simple.Print.module_to_str m2] else (
      let m3 = Compiler.Phase.StackElimination.compile_module m2 in
      if last_pass = "elim" then (
        I1.Semantics.print_strings_of_cfg m3.module_cfg @ "\n\n" :: [string_of_aux m3.module_aux]
      ) else (
        let m4 = Compiler.Phase.Allocator.compile_module m3 in
        let m4 = if peephole_optimize then Compiler.Phase.BasicPeephole.compile_module m4 else m4 in
        if last_pass = "alloc" then (
          I2.Semantics.print_strings_of_cfg m4.module_cfg @ "\n\n" :: [string_of_aux m4.module_aux]
        ) else (
          if last_pass = "x64" then (Semantics.Printer.print_module_as_list m4 false)
          else if last_pass = "wasi_x64" then (Semantics.Printer.print_module_as_list m4 true)
          else (
            let mem_sb_size = mem_pages `op_Multiply` 65536 in
            if not (Compiler.Sandbox.is_nat64 mem_sb_size) || mem_sb_size <= 8 then (
              fail_with "invalid sandbox size. Expected nat64 above 8"
            ) else if FStar.List.Tot.length m4.module_cfg = 0 then (
              fail_with "Impossible 0 sized CFG"
            ) else (
              let m5 = Compiler.Sandbox.compile mem_sb_size m4
                  (Compiler.Sandbox.init_state mem_sb_size m4) 0 in
              if last_pass = "sbx" then (Semantics.Printer.print_module_as_list m5 false)
              else if last_pass = "wasi_sbx" then (Semantics.Printer.print_module_as_list m5 true)
                else (
                  fail_with "[Compile.All] Unknown last_pass."
                )
            )
          )
        )
      )
    )
  )

let rec print_all (l:list string) : FStar.All.ML unit =
  match l with
  | [] -> ()
  | h :: t ->
    FStar.IO.print_string h;
    print_all t

let compile_and_print (m:Wasm.Ast.module_) (last_pass:string) (mem_pages: int) (peephole_optimize:bool):
  FStar.All.ML unit =
  let mem_pages:nat32 = if mem_pages >= 0 && mem_pages < pow2_32 then mem_pages else (
      FStar.IO.print_string "; Invalid mem_pages. Using 160 instead.\n";
      160
    ) in
  match reify (compile m last_pass mem_pages peephole_optimize) () with
  | Error' err -> FStar.IO.print_string ("Compilation failed: " ^ err ^ "\n")
  | Ok' s -> print_all s
