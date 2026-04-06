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

git clone https://gitlab.mpi-sws.org/lgaeher/verit.git verit
cd verit || exit 1

autoconf --force
./configure
make
make install

rm -rf "${BUILD_DIR}"
