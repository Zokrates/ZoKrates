import wrapper from "./wrapper.js";
import stdlib from "./stdlib.js";
import metadata from "./metadata.js";

const initialize = async () => {
  const zokrates = await import("./pkg/index.js");
  return wrapper({ zokrates, stdlib });
};

export { initialize, metadata };