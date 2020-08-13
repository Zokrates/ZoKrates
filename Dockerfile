FROM zokrates/env:latest as build

ENV WITH_LIBSNARK=1
WORKDIR /build

COPY . src
RUN cd src; ./build_release.sh

FROM ubuntu:18.04
ENV ZOKRATES_BASE=/home/zokrates/.zokrates

COPY --from=build /build/src/scripts/install_libsnark_prerequisites.sh /tmp/

RUN /tmp/install_libsnark_prerequisites.sh \
&& useradd -u 1000 -m zokrates

USER zokrates
WORKDIR /home/zokrates

COPY --from=build --chown=zokrates:zokrates /build/src/target/release/zokrates $ZOKRATES_BASE/bin/
COPY --from=build --chown=zokrates:zokrates /build/src/zokrates_cli/examples $ZOKRATES_BASE/examples
COPY --from=build --chown=zokrates:zokrates /build/src/zokrates_stdlib/stdlib $ZOKRATES_BASE/stdlib

ENV PATH "$ZOKRATES_BASE/bin:$PATH"
ENV ZOKRATES_STDLIB "$ZOKRATES_BASE/stdlib"