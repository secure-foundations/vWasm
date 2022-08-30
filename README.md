# vWasm

A formally-verified provably-safe sandboxing Wasm-to-native compiler,
built in F*. Currently supports x86-64 on Linux.

Formal verification refers to a mathematical machine-checked proof
that the code matches the specification. In the case of vWasm, this
means that the compiler, which takes WebAssembly as input and produces
native x86-64 assembly output, is mathematically proven to only
produce output code that is mathematically guaranteed to stay within
its provided sandbox.

Somewhat informally, this means that the execution of the produced
code cannot (under any possible inputs) read or write to memory
outside of the space given to it, nor can it utilize or jump to any
code outside the given boundary. However, note that this does not
guarantee that the code must execute correctly (although we try to
faithfully maintain the semantics of the input Wasm, with semantic
assurance provided by the
[wasm-semantics-fuzzer](https://github.com/secure-foundations/wasm-semantics-fuzzer)),
nor does it guarantee that the API boundary is even reasonable (vWasm
just guarantees that the compile-time requested boundary is
maintained).

For a precise high-level theorem statement, see the type signature for
`compile` in
[`Compiler.Sandbox.fsti`](compiler/sandbox/Compiler.Sandbox.fsti), or
read our [paper](#publications).

To better understand the guarantee provided by vWasm, it is important
to understand the assumptions the proof makes. Our proof assumes the
correctness of the following: our top-level theorem statement, our
x86-64 machine model, our trusted x86-64 assembly printer, the
verification tool (F*) and all that comes with using it (Z3 and
OCaml), and the assembler (nasm) that converts printed assembly into
machine code.

## Usage

Requires [F*](https://www.fstar-lang.org/),
[Rust](https://www.rust-lang.org/), [nasm](https://nasm.us/),
QuackyDucky (`qd` from
[EverParse](https://github.com/project-everest/everparse)),
[wabt](https://github.com/WebAssembly/wabt), and [modified
wabt](https://github.com/secure-foundations/wabt/tree/06e29d927b49e3c8188793dbad5fa8a69e3236e7). See
the [docker container documentation](.docker/README.md) for a
convenient container with all pre-requisites built in.

1. First, build `libwasi.a`:
    ```sh
    cd wasi-integration && cargo build --release
    ```

2. Next, build `main.native`, the main vWasm binary:
    ```sh
    make -j all
    ```

   Note that the above command performs a full verification of vWasm
   and only if that succeeds, will it build `./main.native`. If you
   want to skip the verification step, you can instead run `make -j
   all DONTVERIFY=t` (note that skipping verification this way will
   cause a non-trivial number of warnings to show up).

   The verification step is the most time consuming step of the whole
   process, and when trying to verify `Compiler.Sandbox.fst`, it may
   even seem like it is stuck; this is normal, just give it a few more
   minutes.

3. Ensure that `wasm2wat` from the original wabt is in your `$PATH`
   and a symlink called `wat2vasm` (notice the `vasm`) to the
   `wat2wasm` binary from our modified wabt is also in your `$PATH`
   (the [docker container](./docker/README.md) already takes care of
   this). This will allow the next step to automatically pick up and
   perform the necessary transformations when needed. In particular,
   vWasm requires a special binary format which we call `.vasm` to
   parse input programs, and we generate these files by converting
   `.wasm` binary Wasm files to `.wat` text Wasm files, and then
   convert `.wat` text Wasm files to `.vasm` binary vWasm-input files.

4. Finally, you can run `.wasm`/`.wat`/`.vasm` files using
   `./run_wasm.sh`, which does all the necessary steps to use
   `./main.native`. For example, to run
   [`answer.wasm`](examples/wasi/answer.wat) which is expected to
   terminate with no effect other than an exit-code of 42:
    ```sh
    ./run_wasm.sh examples/wasi/answer.wasm
    ```

   `./run_wasm.sh` performs the following steps:
   1. Convert `.wasm` to `.wat` (skipped for `.wat`/`.vasm` input)
   2. Convert `.wat` to `.vasm` (skipped for `.vasm` input)
   3. Run `./main.native` on the `.vasm` to produce provably-sandboxed assembly
   4. Run an assembler on the produced assembly file to produce an object file
   5. Link the object file against the WASI runtime to produce an executable
   6. Run the executable

   See `./run_wasm.sh --help` for extra options you can pass to it.

## Related Projects

+ [rWasm](https://github.com/secure-foundations/rWasm): a
  high-performance informally-verified provably-safe sandboxing
  compiler
+ [wasm-semantics-fuzzer](https://github.com/secure-foundations/wasm-semantics-fuzzer):
  a tool for providing greater assurance in the semantic correctness
  of any Wasm implementation

## License

BSD 3-Clause License. See [LICENSE](./LICENSE).

## Publications

[**Provably-Safe Multilingual Software Sandboxing using
WebAssembly**](https://www.usenix.org/conference/usenixsecurity22/presentation/bosamiya).
Jay Bosamiya, Wen Shih Lim, and Bryan Parno. In Proceedings
of the USENIX Security Symposium, August, 2022.

```bibtex
@inproceedings{provably-safe-sandboxing-wasm,
  author    = {Bosamiya, Jay and Lim, Wen Shih and Parno, Bryan},
  booktitle = {Proceedings of the USENIX Security Symposium},
  month     = {August},
  title     = {Provably-Safe Multilingual Software Sandboxing using {WebAssembly}},
  year      = {2022}
}
```
