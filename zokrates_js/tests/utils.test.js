const assert = require('assert')
const utils = require('../utils');

describe('absolute path resolving', function() {

    it('should resolve valid absolute path (root)', function() {
        let basePath = 'hashes/pedersen/6bit';
        let relativePath = 'ecc/babyjubjubParams';

        let absolutePath = utils.getAbsolutePath(basePath, relativePath);
        assert.equal(absolutePath, 'ecc/babyjubjubParams');
    });

    it('should resolve valid absolute path (../)', function() {
        let basePath = 'hashes/sha256/512bitPacked';
        let relativePath = '../../utils/pack/pack128';

        let absolutePath = utils.getAbsolutePath(basePath, relativePath);
        assert.equal(absolutePath, 'utils/pack/pack128');
    });

    it('should resolve valid absolute path (./)', function() {
        let basePath = 'hashes/sha256/256bitPadded';
        let relativePath = './512bit';

        let absolutePath = utils.getAbsolutePath(basePath, relativePath);
        assert.equal(absolutePath, 'hashes/sha256/512bit');
    });
});