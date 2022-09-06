FROM zokrates/env:20.04 as build

WORKDIR /build

COPY . src
RUN cd src; ./build_release.sh

FROM ubuntu:20.04
ENV ZOKRATES_HOME=/home/zokrates/.zokrates

RUN useradd -u 1000 -m zokrates

USER zokrates
WORKDIR /home/zokrates

COPY --from=build --chown=zokrates:zokrates /build/src/target/release/zokrates $ZOKRATES_HOME/bin/
COPY --from=build --chown=zokrates:zokrates /build/src/zokrates_cli/examples $ZOKRATES_HOME/examples
COPY --from=build --chown=zokrates:zokrates /build/src/zokrates_stdlib/stdlib $ZOKRATES_HOME/stdlib

ENV PATH "$ZOKRATES_HOME/bin:$PATH"
ENV ZOKRATES_STDLIB "$ZOKRATES_HOME/stdlib"