# `qd_based` parser

This directory contains many auto-generated files, produced from the
`wasm.prerfc` description of the parser. This file is compiled to
`wasm.rfc` using the C pre-processor which is then passed into Quacky
Ducky to produce verified parsers built with LowParse/EverParse
combinators.

All generated files in this directory have already been verified and
this directory is marked to not unnecessarily re-verify files, since
it can take **many** hours to perform a reverification (due to the
nature of LowParse/EverParse parsers of this size). However, if you
_really_ want to regenerate all the files, run `make clean-more` to
remove all auto-generated files. Then run `make fstgen` to re-produce
all the `.rfc`/`.fst`/`.fsti` files. Then run `make DONTVERIFY=f` to
perform re-verification. Then run `make extract DONTEXTRACT=f` to
perform extraction of the `.ml` files from the verified code.

## Note

We are using the branch `taramana_lowparse` of quacky ducky. Use
`dev` branch from `mitls` for `lowparse`.
