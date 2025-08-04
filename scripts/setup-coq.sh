#!/bin/bash

# Installs RefinedRust's dependencies in the current opam switch.
# Inputs:
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

cd $REFINEDRUST_ROOT
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
# NOTE: only needed as long as we depend on an RC version of Rocq.
# Remove once 9.1 is released.
opam repo add rocq-core-dev https://rocq-prover.org/opam/core-dev

# install deps
export OPAMFLAGS="$OPAMFLAGS -y"
make builddep
