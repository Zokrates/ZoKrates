FROM rustlang/rust:nightly

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Thibaut Schaeffer <thibaut@schaeff.fr>

RUN useradd -u 1000 -m zokrates

ARG RUST_TOOLCHAIN=nightly-2019-01-01
ENV WITH_LIBSNARK=1
ENV ZOKRATES_HOME=/home/zokrates/ZoKrates/stdlib/

COPY ./scripts/install_libsnark_prerequisites.sh /tmp/
RUN /tmp/install_libsnark_prerequisites.sh

COPY ./scripts/install_solcjs_deb.sh /tmp/
RUN /tmp/install_solcjs_deb.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . ZoKrates
