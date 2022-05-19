FROM rustlang/rust:nightly

MAINTAINER JacobEberhardt <jacob.eberhardt@tu-berlin.de>, Thibaut Schaeffer <thibaut@schaeff.fr>

RUN useradd -u 1000 -m zokrates

COPY ./scripts/install_solcjs_deb.sh /tmp/
RUN /tmp/install_solcjs_deb.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . ZoKrates
