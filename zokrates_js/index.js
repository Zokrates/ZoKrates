import lib from "./lib.js";

const initialize = async () => {
  const pkg = await import("./pkg/index.js");
  return lib(pkg);
};

export { initialize };
