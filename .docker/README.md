# Dockerfile for working with vWasm

The [`Dockerfile`](./Dockerfile) in this directory installs the
following version of F*:

```
$ fstar.exe --version
F* 0.9.7.0-alpha1
platform=Linux_x86_64
compiler=OCaml 4.09.1
date=2021-02-18 01:38:22 -0500
commit=a09faa2523eb436e4f1d14d8cce0dda2fdb7dbfb
```

This version of F* has been tested to work with vWasm. While
older/newer versions of F* may work, your mileage may vary.

The Docker container also installs the latest version of Rust stable
(due to backwards-compatibility of Rust, no specific version is
explicitly specified, but as of writing this document, this means Rust
version 1.58.1).

Finally, the Docker container installs the required versions of nasm,
qd, `wabt` and modified-`wabt`, and sets up required aliases.

## Building the Docker Image

You can either choose to rebuild the image yourself manually, or you
can import a prebuilt Docker image. This step needs to only be done
once.

1. Manual rebuild: run `make build` in the current directory. Grab a
   cup of coffee, since this can take a while.

2. Prebuilt Docker image: download `vwasm-build-image.tar.xz` from
   [here](https://github.com/secure-foundations/vWasm/releases/tag/docker-image)
   into the current directory, and run `make prebuilt`

# Running the Docker container

Make sure that you've built the container first following the
instructions above. Then, you can run `make run` to run the container.

This will drop you into a `bash` shell, into a directory which
contains a single file. If you run `./copy_from_outside_world`, this
will copy the vWasm git repository inside the container, such that any
modifications to that directory inside the container no longer impact
the outside.

You can still access repository outside the container at `/vWasm` if
you wish to, or alternatively, you can move files in and out of the
container using `docker cp`, although this is not necessary.

## Troubleshooting

If you hit permission issues or errors including the string `ulib`,
then it is likely caused due to an unclean starting state. In this
scenario, we recommend running `git clean -fdX .` at the root of this
repository, and trying again.
