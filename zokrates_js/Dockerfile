FROM blockchainit/rust-wasm-env:latest

ARG WORKSPACE_DIR=/build
WORKDIR ${WORKSPACE_DIR}

COPY . .
RUN npm run build