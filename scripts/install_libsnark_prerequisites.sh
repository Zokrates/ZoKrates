#!/bin/bash

apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    cmake \
    libboost-dev \
    libboost-program-options-dev \
    libgmp3-dev \
    libprocps-dev \
    libssl-dev \
    pkg-config \
    python-markdown \
    && rm -rf /var/lib/apt/lists/* \
