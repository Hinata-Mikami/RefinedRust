#!/usr/bin/env bash
set -euo pipefail

url="https://static.rust-lang.org/dist/channel-rust-nightly.toml"

date=$(curl -s "$url" | grep '^date = ' | head -n1 | cut -d '"' -f2)

latest="nightly-$date"

echo "Latest nightly: $latest"

# update rust-toolchain.toml
sed -i.bak -E "s/channel = \"nightly-[0-9]{4}-[0-9]{2}-[0-9]{2}\"/channel = \"$latest\"/" rr_frontend/rust-toolchain.toml
