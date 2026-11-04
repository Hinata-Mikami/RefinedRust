# Source this file in Bash before running cargo refinedrust or dune build:
#   source /home/mikam/RefinedRust/hinata_mikami/gc/activate.sh
_rr_gc_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
eval "$(opam env --switch=refinedrust-rocq92-upgrade --set-switch)"
export PATH="${_rr_gc_root}/rr_frontend/target/x86_64-unknown-linux-gnu/release:${HOME}/.cargo/bin:${PATH}"
export RUSTUP_TOOLCHAIN=nightly-2026-08-28
export DUNE_JOBS=1
# Large native OCaml/Rocq computations can exceed the WSL default stack.
ulimit -S -s unlimited
unset _rr_gc_root
