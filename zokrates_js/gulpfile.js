/** general */
const gulp = require('gulp');
const dree = require('dree');
const fs = require('fs');
const path = require('path');
const babel = require('gulp-babel');
const replace = require('gulp-replace');

/** stdlib constants */
const stdlibRoot = '../zokrates_stdlib/stdlib';
const output = 'stdlib.json';

const options = {
    extensions: ['zok']
};

/**
 * Serializes standard library directory tree to a json file.
 */
gulp.task('stdlib', (done) => {
    var stdlib = {};
    dree.scan(stdlibRoot, options, function (file) {
        const content = fs.readFileSync(file.path).toString();
        stdlib[file.relativePath] = content;
    });

    fs.writeFileSync(path.resolve(__dirname, output), JSON.stringify(stdlib));
    done();
});

gulp.task('node:deps', () =>
    gulp.src(['pkg/*', 'index.d.ts', 'package.json', 'stdlib.json', 'README.md'], { "base": "." })
        .pipe(gulp.dest('dist-node'))
);

gulp.task('node:babel', () =>
    gulp.src(['./index.js', './utils.js'])
        .pipe(babel({
            presets: [
                [
                    '@babel/preset-env', {
                        "targets": { "node": 10 }
                    }
                ]
            ]
        })).pipe(gulp.dest('dist-node'))
);

gulp.task('node:diff', () =>
    gulp.src(['package.json', 'index.d.ts', 'README.md'])
        .pipe(replace(/(zokrates-js)/gm, 'zokrates-js-node'))
        .pipe(replace(/(import { (.*) } from '(.*)';)/, "const { $2 } = require('$3');"))
        .pipe(gulp.dest('dist-node'))
);

gulp.task('node:build', gulp.series('node:deps', 'node:babel', 'node:diff'));