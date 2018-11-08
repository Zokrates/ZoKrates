#!/bin/bash

LIBSNARK_COMMIT=f7c87b88744ecfd008126d415494d9b34c4c1b20

apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    build-essential \
    cmake \
    curl \
    libboost-dev \
    libboost-program-options-dev \
    libgmp3-dev \
    libprocps-dev \
    libssl-dev \
    pkg-config \
    python-markdown \
    git \
    && rm -rf /var/lib/apt/lists/* \
    && git clone https://github.com/scipr-lab/libsnark.git $LIBSNARK_SOURCE_PATH \
    && git -C $LIBSNARK_SOURCE_PATH checkout $LIBSNARK_COMMIT \
    && git -C $LIBSNARK_SOURCE_PATH submodule update --init --recursive \
