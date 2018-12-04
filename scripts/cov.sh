#!/bin/bash
apt-get update
apt-get install -qq curl zlib1g-dev build-essential python
apt-get install -qq cmake g++ pkg-config jq
apt-get install -qq libcurl4-openssl-dev libelf-dev libdw-dev binutils-dev libiberty-dev
cargo install cargo-kcov
cargo kcov --print-install-kcov-sh | sh
cd zokrates_fs_resolver && cargo kcov --verbose && cd ..
cd zokrates_core && cargo kcov --verbose && cd ..
cd zokrates_cli && cargo kcov --verbose && cd ..
bash <(curl -s https://codecov.io/bash)

# apt-get update -yqq
# apt-get install -y build-essentials
# apt-get install -y wget zlib1g-dev libcurl4-openssl-dev libelf-dev libdw-dev cmake gcc binutils-dev libiberty-dev sudo

# wget https://github.com/SimonKagstrom/kcov/archive/master.tar.gz &&
#         tar xzf master.tar.gz &&
#         cd kcov-master &&
#         mkdir build &&
#         cd build &&
#         cmake .. &&
#         make &&
#         sudo make install &&
#         cd ../.. &&
#         rm -rf kcov-master &&
#         for file in target/debug/zokrates*-*[^\.d]; do mkdir -p "target/cov/$(basename $file)"; kcov --exclude-pattern=/.cargo,/usr/lib --verify "target/cov/$(basename $file)" "$file"; done &&
#         bash <(curl -s https://codecov.io/bash) &&
#         echo "Uploaded code coverage"