#!/bin/bash

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    # apt-get update && apt-get install -y --no-install-recommends \
    #     build-essential \
    #     cmake \
    #     libboost-dev \
    #     libboost-program-options-dev \
    #     libgmp3-dev \
    #     libprocps-dev \
    #     libssl-dev \
    #     pkg-config \
    #     python-markdown \
    #     && rm -rf /var/lib/apt/lists/*

elif [[ "$OSTYPE" == "darwin"* ]]; then
    # brew install boost
    # brew install cmake
    # brew install openssl

    brew info boost
    brew info cmake
    brew info openssl
elif [[ "$OSTYPE" == "cygwin" ]]; then
    echo "Libsnark not supported"
elif [[ "$OSTYPE" == "msys" ]]; then
    echo "Libsnark not supported"
elif [[ "$OSTYPE" == "win32" ]]; then
    echo "Libsnark not supported"
elif [[ "$OSTYPE" == "freebsd"* ]]; then
    echo "Libsnark not supported"
else
    echo "Libsnark not supported"
fi
