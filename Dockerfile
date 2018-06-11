FROM ubuntu:14.04

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>

ARG rust_toolchain=nightly-2018-06-04
ARG LIBSNARK_PATH=/root/libsnark

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
    python-markdown \
    git

ENV LD_LIBRARY_PATH $LD_LIBRARY_PATH:/usr/local/lib

RUN curl https://sh.rustup.rs -sSf | \
    sh -s -- --default-toolchain $rust_toolchain -y

ENV PATH=/root/.cargo/bin:$PATH

RUN git clone https://github.com/scipr-lab/libsnark.git $LIBSNARK_PATH
RUN cd $LIBSNARK_PATH && git submodule update --init --recursive

COPY . /root/ZoKrates

#RUN cd ZoKrates \
#    && cargo build
