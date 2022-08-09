const lib = require("../lib.js");

const initialize = async () => {
  return lib(require("./pkg/index.js"));
};

module.exports = { initialize };
