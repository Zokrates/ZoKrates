FROM ubuntu:14.04

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>

ARG rust_toolchain=nightly-2018-02-10

WORKDIR /root/

RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    curl \
    libboost-all-dev \
    libgmp3-dev \
    libprocps3-dev \
    libssl-dev \
    pkg-config \
    python-markdown

ENV LD_LIBRARY_PATH $LD_LIBRARY_PATH:/usr/local/lib

RUN curl https://sh.rustup.rs -sSf | \
    sh -s -- --default-toolchain $rust_toolchain -y

ENV PATH=/root/.cargo/bin:$PATH

COPY . /root/ZoKrates
RUN  cd ZoKrates \
    && cargo build
