#!/usr/bin/env bash

set -eux

rm -rf target/debug/deps/pico_sat-*

export CARGO_INCREMENTAL=0
export RUSTFLAGS="-Zprofile -Ccodegen-units=1 -Cinline-threshold=0 -Clink-dead-code -Coverflow-checks=off"

cargo +nightly build --verbose
cargo +nightly test --verbose

grcov ./target/debug/deps -s . -t lcov --llvm --branch --ignore-not-existing --ignore "/*" -o lcov.info
genhtml -o ./target/report/ --show-details --highlight --ignore-errors source --legend lcov.info
