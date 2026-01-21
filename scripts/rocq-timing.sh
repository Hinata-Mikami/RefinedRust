#!/usr/bin/env bash
# From RefinedC: https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/tools/coqc_timing.sh?ref_type=heads

set -e

# Wrapper for rocq that is used when running the perf script in the CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling rocq.
# we need to use opam exec -- rocq to get the rocq installed by opam, not this script
# If PROFILE is set, generate a profile in the $PROFILE file (relative to the root of the repo).

# This file is in "_build/default/scripts"
REPO_DIR="$(dirname $(readlink -f $0))/../../../"

PROFILE_ARG=()
TIMECMD_ARG=()

# Only alter behavior when calling `rocq compile`.
if [[ "$1" == "compile" ]]; then
    if [[ -n "$PROFILE" ]]; then
        PROFILE_ARG=("-profile" "$REPO_DIR/$PROFILE")
    fi
    if [[ -n "$TIMECMD" ]]; then
        TIMECMD_ARG=("$TIMECMD")
    fi
fi

opam exec -- "${TIMECMD_ARG[@]}" rocq "$1" "${PROFILE_ARG[@]}" "${@:2}"
