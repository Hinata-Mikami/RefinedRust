#!/usr/bin/env bash

# Build and install VeriT.

# First check if required tools are presents
for tool in autoconf bison curl flex make sed tar
do

    if ! command -v ${tool} >/dev/null 2>&1
    then

        echo "${tool} could not be found. Exiting."
        exit 1

    fi

done

# Create a temporary directory
BUILD_DIR=$(mktemp -d)
cd "${BUILD_DIR}" || exit 1

curl https://usr.lmf.cnrs.fr/~ckeller/Documents-recherche/Smtcoq/veriT9f48a98.tar.gz -o veriT.tar.gz
tar xf veriT.tar.gz
cd veriT9f48a98 || exit 1

# Compilation patches
sed -i -e '3i#include "DAG-print.h"' src/instantiation/ccfv-{constr,mod}.c
sed -i -e '4iconst char *byte_to_binary(unsigned x, unsigned size);' src/instantiation/ccfv-mod.c
sed -i -e '248iTproof proof_tmp_eq_norm(Tproof clause, TDAG DAG);' src/proof/proof.h

# Multiple definition patches
sed -i -e 's/bb_data/bb_data_xx/g' src/arith/LA-xx.c.tpl
sed -i -e 's/conflict_eqs/conflict_eqs_xx/g' src/arith/LA-xx.c.tpl
sed -i -e 's/conflict_lits/conflict_lits_xx/g' src/arith/LA-xx.c.tpl
sed -i -e 's/LA_bound_ranking/LA_bound_ranking_xx/g' src/arith/LA-xx.c.tpl
sed -i -e 's/veriT_conflict_eqs_xx/veriT_conflict_eqs/g' src/arith/LA-xx.c.tpl
sed -i -e '200iextern' src/arith/simplex-xx.c.tpl
sed -i -e '3iTstack_simplex_var integer_stack;' src/arith/simplex.c
sed -i -e '2350d' src/congruence/congruence.c
sed -i -e '28,32d' src/instantiation/inst-man.c
sed -i -e '20iextern' src/instantiation/inst-trigger.c
sed -i -e '403iextern' src/SAT/veriT-SAT.h
sed -i -e '29d' src/parsers/tptp/tptplex.l


autoconf --force
./configure
make
make install

rm -rf "${BUILD_DIR}"
