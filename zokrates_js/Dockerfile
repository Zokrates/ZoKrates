FROM rustlang/rust:nightly as build

RUN curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh -s -- -y

COPY . src
RUN cd src/zokrates_js && wasm-pack build --out-name index --release --target bundler && rm -rf target/

FROM node:10-alpine

COPY --from=build src/zokrates_js src/zokrates_js
COPY --from=build src/zokrates_stdlib src/zokrates_stdlib

RUN cd src/zokrates_js && npm run setup \
    && cd / && mkdir build && mv src/zokrates_js/* /build \
    && rm -rf src