const wrapper = require('../wrapper.js');
const stdlib = require('../stdlib.json');
const metadata = require('../metadata.json');

const initialize = async () => {

    console.log("in init");

    let p = require('./pkg/index.js');

    console.log("got p");

    let w = wrapper({ 
        zokrates: p,
        stdlib
    });

    console.log("got wrapper");

    return w;
}

function foo() {
    console.log("in foo");
    return;
}

module.exports = { initialize, metadata, foo };