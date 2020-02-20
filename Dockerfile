FROM ubuntu:18.04

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Thibaut Schaeffer <thibaut@schaeff.fr>

RUN useradd -u 1000 -m zokrates

ARG RUST_TOOLCHAIN=nightly-2020-01-01
ENV WITH_LIBSNARK=1
ENV ZOKRATES_HOME=/home/zokrates/.zokrates

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    && rm -rf /var/lib/apt/lists/*

COPY ./scripts/install_libsnark_prerequisites.sh /tmp/
RUN /tmp/install_libsnark_prerequisites.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . src

RUN mkdir $ZOKRATES_HOME

RUN curl https://sh.rustup.rs -sSf | sh -s -- --default-toolchain $RUST_TOOLCHAIN -y \
    && export PATH=/home/zokrates/.cargo/bin:$PATH \
    && (cd src;./build_release.sh) \
    && mv ./src/target/release/zokrates . \
    && mv ./src/zokrates_cli/examples . \
    && mv ./src/zokrates_stdlib/stdlib/* $ZOKRATES_HOME \
    && rustup self uninstall -y \
    && rm -rf src