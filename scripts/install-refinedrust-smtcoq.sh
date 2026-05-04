#!/usr/bin/env bash

# Installs RefinedRust in the current opam switch.
# Inputs:
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

opam pin remove refinedrust-smtcoq -y
opam remove refinedrust-smtcoq -y
opam pin add refinedrust-smtcoq.dev $REFINEDRUST_ROOT/theories -y
opam install refinedrust-smtcoq
