const wrapper = require('../wrapper.js');
const stdlib = require('../stdlib.json');

const initialize = async () => {
    return wrapper({ 
        zokrates: require('./pkg/index.js'),
        stdlib
    });
}

module.exports = { initialize };