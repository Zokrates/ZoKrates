FROM rustlang/rust:nightly

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Thibaut Schaeffer <thibaut@schaeff.fr>

RUN useradd -u 1000 -m zokrates

ENV WITH_LIBSNARK=1

COPY ./scripts/install_libsnark_prerequisites.sh /tmp/
RUN /tmp/install_libsnark_prerequisites.sh

COPY ./scripts/install_solcjs_deb.sh /tmp/
RUN /tmp/install_solcjs_deb.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . ZoKrates
