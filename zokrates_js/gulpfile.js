/** general */
const gulp = require('gulp');
const dree = require('dree');
const fs = require('fs');
const path = require('path');

/** stdlib constants */
const stdlibRoot  = '../zokrates_stdlib/stdlib';
const output = 'stdlib.json';

const options = {
    extensions: ['zok']
};

/**
 * Serializes standard library directory tree to a json file.
 */
gulp.task('stdlib', function (done) {
    var stdlib = {};
    dree.scan(stdlibRoot, options, function (file) {
        const content = fs.readFileSync(file.path).toString();
        stdlib[file.relativePath] = content;
    });

    fs.writeFileSync(path.resolve(__dirname, output), JSON.stringify(stdlib));
    done();
});