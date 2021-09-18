#!/usr/bin/env bash

git stash push
cargo bench --bench $1 -- --save-baseline base
git stash pop
cargo bench --bench $1 -- --baseline base
