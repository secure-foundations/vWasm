#! /bin/sh

GIT_ROOT="$(git rev-parse --show-toplevel)"
GIT_ROOT="$(realpath --relative-to=. "$GIT_ROOT")"

echo $(cat "${GIT_ROOT}/fstar-args" | \
	   sed 's/[[:space:]]*#.*$//' | \
	   sed 's|--include \(.*\)$|--include "'"${GIT_ROOT}"'/\1"|') \
     '--warn_error -242' \
     '--include '"${FSTAR_HOME}"'/ulib/.cache'
