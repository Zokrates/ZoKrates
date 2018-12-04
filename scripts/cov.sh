#!/bin/bash
apt-get update
apt-get install -qq curl zlib1g-dev build-essential python
apt-get install -qq cmake g++ pkg-config jq
apt-get install -qq libcurl4-openssl-dev libelf-dev libdw-dev binutils-dev libiberty-dev
cargo install cargo-kcov
cargo kcov --print-install-kcov-sh | sh
cd zokrates_fs_resolver && WITH_LIBSNARK=1 LIBSNARK_SOURCE_PATH=$HOME/libsnark cargo kcov --verbose && cd ..
cd zokrates_core && WITH_LIBSNARK=1 LIBSNARK_SOURCE_PATH=$HOME/libsnark cargo kcov --verbose && cd ..
cd zokrates_cli && WITH_LIBSNARK=1 LIBSNARK_SOURCE_PATH=$HOME/libsnark cargo kcov --verbose && cd ..
bash <(curl -s https://codecov.io/bash)