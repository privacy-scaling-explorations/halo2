GIT_ROOT=$(pwd)

cd /tmp

cp -R "${GIT_ROOT}" . || true
cd halo2
rustup target add wasm32-unknown-unknown wasm32-wasi

cd halo2_proofs
cargo add getrandom --features js
cd ../

cargo build --release --no-default-features --features batch,dev-graph,gadget-traces --target wasm32-unknown-unknown
cargo build --release --no-default-features --features batch,dev-graph,gadget-traces --target wasm32-wasi

cd ../
rm -rf halo2
