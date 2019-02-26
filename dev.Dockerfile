FROM rustlang/rust:nightly

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Thibaut Schaeffer <thibaut@schaeff.fr>

RUN useradd -u 1000 -m zokrates

ARG RUST_TOOLCHAIN=nightly-2019-01-01
ENV WITH_LIBSNARK=1
ENV ZOKRATES_HOME=/home/zokrates/ZoKrates/zokrates_stdlib/stdlib/

COPY ./scripts/install_libsnark_prerequisites.sh /tmp/
RUN /tmp/install_libsnark_prerequisites.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . ZoKrates
