#!/bin/sh

GIT_ROOT=$(pwd)

cd /tmp

rustup default stable
rustup target add wasm32-unknown-unknown wasm32-wasi

cargo new foobar
cd foobar
cargo add --path "${GIT_ROOT}/halo2_proofs" --features batch,dev-graph,gadget-traces
cargo add getrandom --features js --target wasm32-unknown-unknown

cargo build --release --target wasm32-unknown-unknown
cargo build --release --target wasm32-wasi

cd ../
rm -rf foobar
