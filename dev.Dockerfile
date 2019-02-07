FROM ubuntu:18.04

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Dennis Kuhnert <mail@kyroy.com>, Thibaut Schaeffer <thibaut@schaeff.fr>

RUN useradd -u 1000 -m zokrates

ARG RUST_TOOLCHAIN=nightly-2019-01-01
ENV WITH_LIBSNARK=1
ENV ZOKRATES_HOME=/home/zokrates/ZoKrates/stdlib/

RUN apt-get update && apt-get install -y --no-install-recommends \
	ca-certificates \
	curl

COPY --chown=zokrates:zokrates . ZoKrates

RUN ./ZoKrates/scripts/install_libsnark_prerequisites.sh

USER zokrates

RUN curl https://sh.rustup.rs -sSf | \
    sh -s -- --default-toolchain $RUST_TOOLCHAIN -y

ENV PATH=/home/zokrates/.cargo/bin:$PATH

RUN cd ZoKrates \
	&& ./build.sh
