const assert = require('assert');
const utils = require('../utils');
const stdlib = require('../stdlib.json');

describe('stdlib', function() {

    it('should resolve module from stdlib (1)', function() {
        let basePath = 'hashes/sha256/512bitPacked.zok';
        let relativePath = '../../utils/pack/pack128';

        let absolutePath = utils.appendExtension(utils.getAbsolutePath(basePath, relativePath), '.zok');
        assert.notEqual(stdlib[absolutePath], undefined);
    });

    it('should resolve module from stdlib (2)', function() {
        let basePath = 'hashes/sha256/256bitPadded.zok';
        let relativePath = './512bit';

        let absolutePath = utils.appendExtension(utils.getAbsolutePath(basePath, relativePath), '.zok');
        assert.notEqual(stdlib[absolutePath], undefined);
    });

    it('should resolve module from stdlib (3)', function() {
        let basePath = 'hashes/pedersen/6bit.zok';
        let relativePath = 'ecc/babyjubjubParams';

        let absolutePath = utils.appendExtension(utils.getAbsolutePath(basePath, relativePath), '.zok');
        assert.notEqual(stdlib[absolutePath], undefined);
    });
});