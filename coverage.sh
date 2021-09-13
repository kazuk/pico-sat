#!/usr/bin/env bash

set -eux
export CARGO_BUILD_TARGET_DIR="./target/cover"
export RUSTFLAGS="-Zinstrument-coverage -Ccodegen-units=1 -Cinline-threshold=0 -Clink-dead-code -Coverflow-checks=off"
export RUSTDOCFLAGS="-Cpanic=abort"

cargo +nightly build --verbose

rm -rf ./target/cover/debug/deps/profraw
mkdir ./target/cover/debug/deps/profraw/

export LLVM_PROFILE_FILE="./target/cover/debug/deps/profraw/coverage-%p-%m.profraw"

cargo +nightly test --verbose

RUSTUP_TOOLCHAIN="nightly" grcov ./target/cover/debug/deps/profraw/ -b ./target/cover/debug/deps -s . -t lcov --llvm --branch --ignore-not-existing --ignore "/*" -o ./target/lcov.info
