FROM rust:latest as builder
WORKDIR /src
COPY . .
RUN apt-get update
# RUN apt-get install -y git clang llvm
RUN rustup toolchain install nightly
RUN cargo +nightly build --release

FROM ubuntu:latest
RUN useradd -u 1000 -m zokrates
WORKDIR /home/zokrates/
COPY --from=builder --chown=zokrates:zokrates /src/target/release/zokrates /home/zokrates/
COPY --from=builder --chown=zokrates:zokrates /src/zokrates_stdlib/stdlib /home/zokrates/.zokrates/
COPY --from=builder --chown=zokrates:zokrates /src/zokrates_cli/examples /home/zokrates/examples/
ENV ZOKRATES_HOME=/home/zokrates/.zokrates
USER zokrates
ENV PATH=/home/zokrates/:$PATH
CMD ["zokrates", "--version"]
