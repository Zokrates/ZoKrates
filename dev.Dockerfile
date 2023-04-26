FROM rust:latest

RUN useradd -u 1000 -m zokrates

COPY ./scripts/install_foundry.sh /tmp/
RUN /tmp/install_foundry.sh

USER zokrates

WORKDIR /home/zokrates

COPY --chown=zokrates:zokrates . ZoKrates
