import lib from "./lib.js";
import metadata from "./metadata.js";

const initialize = async () => {
  const pkg = await import("./pkg/index.js");
  return lib(pkg);
};

export { initialize, metadata };
