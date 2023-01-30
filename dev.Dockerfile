FROM rustlang/rust:nightly

RUN useradd -u 1000 -m zokrates

COPY ./scripts/install_foundry_deb.sh /tmp/
RUN /tmp/install_foundry_deb.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . ZoKrates
