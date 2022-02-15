#! /bin/bash

set -o nounset   # Fail command if trying to access undefined variable
set -o pipefail  # Fail command if anything in pipe fails
set -o errexit   # Fail the script if any command fails

function usage() {
    echo "Usage:"
    echo "    $0 [options...] {input} [arguments ...]"
    echo ""
    echo "Compiles and runs {input} WebAssembly file"
    echo ""
    echo "{input} can be any of .wasm, .wat, or .vasm"
    echo ""
    echo "Options:"
    echo "    -h, --help                      Show this help menu"
    echo "    -d, --debug-dump                Obtains a compiler-phase-wise dump. Implies -k."
    echo "    -k, --keep-work-dir             Keep working directory around."
    echo "    -n, --no-sandbox                Compile and run without the sandbox."
    echo "    -w WORKDIR, --work-dir WORKDIR  Use WORKDIR as working directory. Implies -k."
    echo "    -s S, --sandbox-pages S         Use S number of sandbox pages. Default: 160"
    echo "    -a ARG, --asm-extra-arg ARG     Pass ARG along when assembling with Nasm. Can be repeated."
    echo "    --peephole-optimize             Enable peephole optimization."
    echo "    --debug-no-strip-locals         Do not strip internal local symbols."
    echo "    -q, --quiet                     Don't print any logging from this script"
    exit 1
}

if [ "$#" -lt 1 ]; then
    usage "$0"
fi

function echo_to_stderr() {
    echo "$@" 1>&2
}

NO_SANDBOX=0
DEBUG_DUMP=0
KEEP_WORK_DIR=0
FIXED_WORK_DIR=
NO_STRIP_LOCALS=0
SANDBOX_PAGES=160
PEEPHOLE_OPTIMIZE=0
EXTRA_NASM_ARGS=
ECHO="echo_to_stderr"

while true; do
    case "$1" in
        "-k"|"--keep-work-dir")
            KEEP_WORK_DIR=1
            shift
            ;;
        "-d"|"--debug-dump")
            DEBUG_DUMP=1
            KEEP_WORK_DIR=1
            shift
            ;;
        "-n"|"--no-sandbox")
            NO_SANDBOX=1
            shift
            ;;
        "-w"|"--work-dir")
            KEEP_WORK_DIR=1
            FIXED_WORK_DIR="$2"
            shift
            shift
            ;;
        "-s"|"--sandbox-pages")
            SANDBOX_PAGES="$2"
            shift
            shift
            ;;
        "-a"|"--asm-extra-arg")
            EXTRA_NASM_ARGS="${EXTRA_NASM_ARGS} $2"
            shift
            shift
            ;;
        "--debug-no-strip-locals")
            NO_STRIP_LOCALS=1
            shift
            ;;
        "--peephole-optimize")
            PEEPHOLE_OPTIMIZE=1
            shift
            ;;
        "-q"|"--quiet")
            ECHO="true"
            shift
            ;;
        "-h"|"--help")
            usage "$0"
            ;;
        -*)
            echo "Invalid option $1"
            usage "$0"
            ;;
        *)
            # do nothing
            break
            ;;
    esac
done

INPUTFILE=$(realpath "$1")
shift # Remove the first argument from being looked at

if [ "$FIXED_WORK_DIR" = "" ]; then
    WORKINGDIR=$(mktemp -d ./working-dir-XXXXXXXX)
else
    mkdir -p "$FIXED_WORK_DIR"
    WORKINGDIR="$FIXED_WORK_DIR"
fi
CURRENTDIR=$(pwd)

INPUTFORMAT="${INPUTFILE##*.}"
INPUTFILEBASE=$(basename -s ".$INPUTFORMAT" "$INPUTFILE")
INPUT_NO_FORMAT=$(dirname "$INPUTFILE")/"${INPUTFILEBASE}"

case "${INPUTFORMAT}" in
    "wasm")
        ${ECHO} "[+] Converting wasm -> wat"
        wasm2wat -o "${INPUT_NO_FORMAT}.wat" "${INPUT_NO_FORMAT}.wasm"
        if [ $KEEP_WORK_DIR = 1 ]; then
            cp "${INPUT_NO_FORMAT}.wasm" "${WORKINGDIR}/t.wasm"
            cp "${INPUT_NO_FORMAT}.wat" "${WORKINGDIR}/t.wat"
        fi
        ${ECHO} "[+] Converting wat -> vasm"
        wat2vasm -o "${INPUT_NO_FORMAT}.vasm" "${INPUT_NO_FORMAT}.wat"
    ;;
    "wat")
        if [ $KEEP_WORK_DIR = 1 ]; then
            cp "${INPUT_NO_FORMAT}.wat" "${WORKINGDIR}/t.wat"
            wat2wasm -o "${WORKINGDIR}/t.wasm" "${WORKINGDIR}/t.wat"
        fi
        ${ECHO} "[+] Converting wat -> vasm"
        wat2vasm -o "${INPUT_NO_FORMAT}.vasm" "${INPUT_NO_FORMAT}.wat"
    ;;
    "vasm")
        # Use directly
    ;;
    *)
        ${ECHO} "[!] Invalid format '.$INPUTFORMAT'. Expected .wasm/.wat/.vasm"
        exit 1
    ;;
esac

function time_run() {
    TIMING_FILE=$(mktemp ./timing-info-XXXXXXXX)
    /usr/bin/time -f "%e" -o "${TIMING_FILE}" "$@"
    ${ECHO} "done in $(cat "${TIMING_FILE}") seconds" 1>&2
    rm "${TIMING_FILE}"
}

VWASM="$(git rev-parse --show-toplevel)/main.native"
LIBWASI="$(git rev-parse --show-toplevel)/wasi-integration/target/release/libwasi.a"

${ECHO} "[+] Switched to working directory: ${WORKINGDIR}"
cd "${WORKINGDIR}"

${ECHO} "[+] Copying into working directory"
cp "${INPUT_NO_FORMAT}.vasm" t.vasm

if [ $PEEPHOLE_OPTIMIZE = 1 ]; then
    ${ECHO} "[i] Enabling peephole optimization"
else
    ${ECHO} "[i] Disabling peephole optimization (enable using --peephole-optimize)"
fi

function run_vwasm_with() {
    if [ $PEEPHOLE_OPTIMIZE = 1 ]; then
        time_run "${VWASM}" t.vasm -p "${SANDBOX_PAGES}" --peephole-optimize "$@"
    else
        time_run "${VWASM}" t.vasm -p "${SANDBOX_PAGES}" "$@"
    fi
}

if [ $DEBUG_DUMP = 1 ]; then
    ${ECHO} -n "[+] [DEBUG] vWasm simp: "
    run_vwasm_with -l simp > t.0.simp
    ${ECHO} -n "[+] [DEBUG] vWasm elim: "
    run_vwasm_with -l elim > t.1.elim
    ${ECHO} -n "[+] [DEBUG] vWasm alloc: "
    run_vwasm_with -l alloc > t.2.alloc
    ${ECHO} -n "[+] [DEBUG] vWasm nosbx x64: "
    run_vwasm_with -l wasi_x64 > t.3.nosbx-asm
    ${ECHO} -n "[+] Compiling to sandboxed assembly using vWasm: "
    run_vwasm_with -l wasi_sbx > t.4.sbx-asm
    if [ $NO_SANDBOX = 1 ]; then
        ${ECHO} "[+] Using non-sandboxed assembly for compilation"
        cp t.3.nosbx-asm t.asm
    else
        cp t.4.sbx-asm t.asm
    fi
else
    if [ $NO_SANDBOX = 1 ]; then
        ${ECHO} -n "[+] Compiling to NON sandboxed assembly using vWasm: "
        run_vwasm_with -l wasi_x64 > t.asm
    else
        ${ECHO} -n "[+] Compiling to sandboxed assembly using vWasm: "
        run_vwasm_with -l wasi_sbx > t.asm
    fi
fi

if [ "$EXTRA_NASM_ARGS" = "" ]; then
    ${ECHO} -n "[+] Assembling into an object file: "
else
    ${ECHO} -n "[+] Assembling into an object file (with extra args:${EXTRA_NASM_ARGS}): "
fi
# Since we do want to expand out the args and their corresponding
# whitespace (which shellcheck doesn't like, and would generally be a
# bad idea, so we don't want to disable globally, but just at this
# line):
#
# shellcheck disable=SC2086
time_run nasm -f elf64 ${EXTRA_NASM_ARGS} t.asm

${ECHO} -n "[+] Compiling against WASI runtime: "
time_run gcc -o t.native t.o "${LIBWASI}" -lpthread -ldl -no-pie

if [ $NO_STRIP_LOCALS = 1 ]; then
    ${ECHO} "[ ] Not stripping local symbols"
else
    ${ECHO} "[+] Stripping local symbols"
    strip --wildcard --strip-symbol '_L*' --strip-symbol '..@*' t.native
fi

if [ $KEEP_WORK_DIR = 1 ]; then
    ${ECHO} "[+] Copying executable back"
    cp t.native "${INPUT_NO_FORMAT}.native"
else
    ${ECHO} "[+] Moving executable back"
    mv t.native "${INPUT_NO_FORMAT}.native"
fi

if [ $KEEP_WORK_DIR = 1 ]; then
    ${ECHO} "[+] Keeping working directory ${WORKINGDIR}"
else
    ${ECHO} "[+] Cleaning up and removing ${WORKINGDIR}"
    cd "${CURRENTDIR}"
    rm -rf "${WORKINGDIR}"
fi

${ECHO} "[+] Running executable '${INPUTFILEBASE}.native' with $# args"
set +o errexit   # Temporarily disable errexit
"${INPUT_NO_FORMAT}.native"
${ECHO} "[+] Finished with exit code: $?"
set -o errexit   # Re-enable errexit
