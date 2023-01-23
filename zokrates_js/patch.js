import { parse } from "acorn";
import { generate } from "astring";
import fs from "fs/promises";
import pako from "pako";

(async function () {
  const packageObject = JSON.parse(
    await fs.readFile("pkg/package.json", { encoding: "utf-8" })
  );
  const wasmPath = packageObject.files.find((file) => file.endsWith(".wasm"));
  const wasm = await fs.readFile(`pkg/${wasmPath}`);

  const deflated = Buffer.from(pako.deflate(wasm));
  const wasmBase64 = deflated.toString("base64");

  const init = `export async function init(inflate) {
  const encoded = '${wasmBase64}';

  let bytes;

  if (typeof Buffer === "function") {
    bytes = Buffer.from(encoded, "base64");
  } else if (typeof atob === "function") {
    const binary = atob(encoded);
    bytes = new Uint8Array(binary.length);

    for (let i = 0; i < binary.length; i++) {
      bytes[i] = binary.charCodeAt(i);
    }
  } else {
    throw new Error("Unsupported platform");
  }

  const imports = getImports();
  initMemory(imports);

  bytes = inflate(bytes);

  const { instance, module } = await WebAssembly.instantiate(bytes, imports);
  return finalizeInit(instance, module);
}

export default init;`;

  const generatedSource = await fs.readFile(`pkg/${packageObject.module}`, {
    encoding: "utf-8",
  });

  const ast = parse(generatedSource, {
    ecmaVersion: "latest",
    sourceType: "module",
  });

  let body = ast.body.filter((v) => {
    switch (v.type) {
      case "FunctionDeclaration":
        // we don't use these functions so we strip them out
        return !["load", "init", "initSync"].includes(v.id.name);
      case "ExportDefaultDeclaration":
        // we will provide our own default export
        return false;
      default:
        return true;
    }
  });

  body.pop(); // removes `export { initSync }`

  const source = generate({
    ...ast,
    body,
  });

  await fs.writeFile("wasm.js", source + init);
})();
