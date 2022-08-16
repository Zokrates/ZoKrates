const lib = require("../lib.js");
const metadata = require("../metadata.js");

const initialize = async () => {
  return lib(require("./pkg/index.js"));
};

module.exports = { initialize, metadata };
