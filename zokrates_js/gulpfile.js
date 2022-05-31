const gulp = require("gulp");
const dree = require("dree");
const fs = require("fs");
const path = require("path");
const toml = require("toml");

const stdlibRoot = "../zokrates_stdlib/stdlib";
const options = {
  extensions: ["zok"],
};

// Serializes the standard library directory tree to a js file.
gulp.task("stdlib", (done) => {
  var stdlib = {};
  dree.scan(stdlibRoot, options, function (file) {
    const content = fs.readFileSync(file.path).toString();
    stdlib[file.relativePath] = content;
  });

  fs.writeFileSync(
    path.resolve(__dirname, "stdlib.js"),
    `module.exports = ${JSON.stringify(stdlib)}`
  );
  done();
});

gulp.task("metadata", (done) => {
  const config = toml.parse(
    fs.readFileSync("../zokrates_cli/Cargo.toml").toString()
  );
  const metadata = JSON.stringify({
    version: config.package.version,
  });
  fs.writeFileSync(
    path.resolve(__dirname, "metadata.js"),
    `module.exports = ${metadata}`
  );
  done();
});

gulp.task("setup", gulp.parallel("stdlib", "metadata"));
