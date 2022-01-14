ARG BASE_IMAGE=ubuntu:18.04
ARG WITH_LIBSNARK=1

FROM zokrates/env:latest as build
ENV WITH_LIBSNARK=$WITH_LIBSNARK

WORKDIR /build

COPY . src
RUN cd src; ./build_release.sh

FROM $BASE_IMAGE

ARG WITH_LIBSNARK
ENV ZOKRATES_HOME=/home/zokrates/.zokrates

RUN apt-get update; \
    [ "$WITH_LIBSNARK" -eq 1 ] && apt-get install -y --no-install-recommends libgmp3-dev; \
    useradd -u 1000 -m zokrates

USER zokrates
WORKDIR /home/zokrates

COPY --from=build --chown=zokrates:zokrates /build/src/target/release/zokrates $ZOKRATES_HOME/bin/
COPY --from=build --chown=zokrates:zokrates /build/src/zokrates_cli/examples $ZOKRATES_HOME/examples
COPY --from=build --chown=zokrates:zokrates /build/src/zokrates_stdlib/stdlib $ZOKRATES_HOME/stdlib

ENV PATH "$ZOKRATES_HOME/bin:$PATH"
ENV ZOKRATES_STDLIB "$ZOKRATES_HOME/stdlib"