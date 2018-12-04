#!/bin/bash

WITH_LIBSNARK=1 LIBSNARK_SOURCE_PATH=$HOME/libsnark RUSTFLAGS="-D warnings -C link-dead-code" cargo clean && cargo test -- --test-threads=1

apt-get update -yqq
apt-get install -y build-essentials
apt-get install -y wget zlib1g-dev libcurl4-openssl-dev libelf-dev libdw-dev cmake gcc binutils-dev libiberty-dev sudo

wget https://github.com/SimonKagstrom/kcov/archive/master.tar.gz &&
        tar xzf master.tar.gz &&
        cd kcov-master &&
        mkdir build &&
        cd build &&
        cmake .. &&
        make &&
        sudo make install &&
        cd ../.. &&
        rm -rf kcov-master &&
        for file in target/debug/zokrates-*[^\.d]; do mkdir -p "target/cov/$(basename $file)"; kcov --exclude-pattern=/.cargo,/usr/lib --verify "target/cov/$(basename $file)" "$file"; done &&
        bash <(curl -s https://codecov.io/bash) &&
        echo "Uploaded code coverage"