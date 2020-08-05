FROM zokrates/env:latest

COPY . src
RUN cd src/zokrates_js && npm run build && rm -rf target/

RUN cd / && mkdir build \
    && mv src/zokrates_js/* /build \
    && rm -rf src