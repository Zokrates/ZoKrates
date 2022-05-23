const wrapper = require("../wrapper.js");
const stdlib = require("../stdlib.js");
const metadata = require("../metadata.js");

const initialize = async () => {
  return wrapper({
    zokrates: require("./pkg/index.js"),
    stdlib,
  });
};

module.exports = { initialize, metadata };
