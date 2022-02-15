FROM ubuntu:20.04

# Install some basic pre-requisites
RUN apt-get -qq update
RUN apt-get install -y software-properties-common
RUN add-apt-repository -y ppa:avsm/ppa # for opam 2
RUN apt-get -qq update
RUN apt-get install -y sudo wget libssl-dev libsqlite3-dev g++ gcc m4 make opam pkg-config python libgmp3-dev unzip cmake

# Change to a non-root user for everything else
RUN useradd -ms /bin/bash build
RUN echo "build ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER build

# Get the specific version of F* we want
WORKDIR /home/build
RUN git clone https://github.com/FStarLang/FStar.git
ENV FSTAR_HOME=/home/build/FStar
WORKDIR $FSTAR_HOME
RUN git reset --hard a09faa2523eb436e4f1d14d8cce0dda2fdb7dbfb

# Install z3
WORKDIR /home/build
ENV z3=z3-4.8.5-x64-debian-8.11
RUN wget https://github.com/FStarLang/binaries/raw/master/z3-tested/${z3}.zip
RUN unzip ${z3}.zip
ENV PATH=/home/build/${z3}/bin:${PATH}

# Get all pre-requisites for building F*
WORKDIR /home/build
RUN opam init -y --disable-sandboxing --compiler=4.09.1
RUN opam update
RUN opam install -y \
    batteries=3.0.0 \
    fileutils=0.6.2 \
    fix=20200131 \
    menhir=20200624 \
    ocamlbuild=0.14.0 \
    ocamlfind=1.8.1 \
    ocaml-migrate-parsetree=1.7.3 \
    pprint=20200410 \
    ppx_deriving=4.5 \
    ppx_deriving_yojson=3.5.2 \
    process=0.2.1 \
    stdint=0.6.0 \
    ulex=1.2 \
    visitors=20200210 \
    wasm=1.0.1 \
    yojson=1.7.0 \
    zarith=1.9.1

# Build F* and add to PATH
WORKDIR $FSTAR_HOME
RUN opam exec -- make -j $(nproc)
ENV PATH=${FSTAR_HOME}/bin:${PATH}

# Install Rust
WORKDIR /home/build
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs -o rustup && sh rustup -y
ENV PATH=/home/build/.cargo/bin:${PATH}

# Set up ~/.local/bin as part of PATH
RUN mkdir -p /home/build/.local/bin
ENV PATH=/home/build/.local/bin:${PATH}

# Install wasm2wat
WORKDIR /home/build
RUN git clone https://github.com/WebAssembly/wabt
WORKDIR /home/build/wabt
RUN git reset --hard 189c0e61cb164b6db98a97b6bc4f19205d9f2dc6
RUN mkdir build && cd build && cmake .. -DBUILD_TESTS=OFF && make -j $(nproc)
RUN ln $(realpath build/wasm2wat) /home/build/.local/bin/wasm2wat

# Install wat2vasm
WORKDIR /home/build
RUN git clone https://github.com/secure-foundations/wabt sfwabt
WORKDIR /home/build/sfwabt
RUN git reset --hard 06e29d927b49e3c8188793dbad5fa8a69e3236e7
RUN mkdir build && cd build && cmake .. -DBUILD_TESTS=OFF && make -j $(nproc)
RUN ln $(realpath build/wat2wasm) /home/build/.local/bin/wat2vasm

# Install quacky-ducky (we don't need anything else from everparse,
# but this is the most convenient way to get the qd binary)
WORKDIR /home/build
RUN wget https://github.com/project-everest/everparse/releases/download/v2021.03.28/everparse_v2021.03.28_Linux_x86_64.tar.gz \
    && tar xf everparse_v2021.03.28_Linux_x86_64.tar.gz \
    && rm everparse_v2021.03.28_Linux_x86_64.tar.gz \
    && mv everparse/bin/qd /home/build/.local/bin \
    && rm -r everparse

# Make sure that ocamlbuild and such exists in the path, and `/usr/bin/time` exists
RUN echo 'eval $(opam env)' > /home/build/.bashrc
USER root
RUN apt-get install -y time
USER build

# Install nasm
WORKDIR /home/build
RUN wget https://www.nasm.us/pub/nasm/releasebuilds/2.14/nasm-2.14.tar.bz2 \
    && tar xf nasm-2.14.tar.bz2 \
    && rm nasm-2.14.tar.bz2 \
    && cd nasm-2.14 \
    && ./configure \
    && make -j $(nproc) \
    && sudo make install \
    && cd .. \
    && rm -rf nasm-2.14

# Set up space for vWasm inside the container
WORKDIR /home/build
RUN mkdir -p /home/build/vWasm
WORKDIR /home/build/vWasm
RUN echo 'cp -r /vWasm /home/build && rm /home/build/vWasm/copy_from_outside_world' > copy_from_outside_world && chmod +x copy_from_outside_world
