FROM ubuntu:14.04

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>

ARG libsnarkcommit=deprecated-master

WORKDIR /root

RUN apt-get update && \
    apt-get install -y \
    wget unzip curl \
    build-essential git libgmp3-dev libprocps3-dev libgtest-dev python-markdown libboost-all-dev libssl-dev

RUN wget https://github.com/scipr-lab/libsnark/archive/$libsnarkcommit.zip \
  && mv $libsnarkcommit.zip libsnark.zip \
  && unzip libsnark.zip \
  && cd libsnark-$libsnarkcommit \
  && ./prepare-depends.sh

RUN curl https://sh.rustup.rs -sSf | \
  sh -s -- --default-toolchain nightly-2018-02-05 -y

ENV PATH=/root/.cargo/bin:$PATH

RUN cd libsnark-$libsnarkcommit \
  && make install lib PREFIX=/usr/local \
    NO_PROCPS=1 NO_GTEST=1 NO_DOCS=1 CURVE=ALT_BN128 FEATUREFLAGS="-DBINARY_OUTPUT=1 -DMONTGOMERY_OUTPUT=1 -DNO_PT_COMPRESSION=1"

ENV LD_LIBRARY_PATH $LD_LIBRARY_PATH:/usr/local/lib

COPY . /root/ZoKrates

RUN cd ZoKrates \
  && cargo build --release --features nolibsnark
