// https://docs.rs/getrandom/0.2.8/getrandom/index.html#nodejs-es-module-support
import { webcrypto } from "node:crypto";
if (typeof globalThis.crypto === "undefined") {
  globalThis.crypto = webcrypto;
}

export * from "./index.js";
