# OCaml Driver

This directory contains trusted OCaml code whose only job is to
perform simple command line argument parsing and file I/O, and
effectively wrap around main compiler, whose code starts in
[`compiler/doall/Compile.All.fst`](../compiler/doall/Compile.All.fst).
