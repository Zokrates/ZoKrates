#!/bin/bash

NPM_VERSION=$(npm view zokrates-js dist-tags.latest)

PACKAGE_VERSION=$(cat package.json \
  | grep version \
  | head -1 \
  | awk -F: '{ print $2 }' \
  | sed 's/[",]//g' \
  | tr -d '[[:space:]]')

CARGO_VERSION=$(cat Cargo.toml \
  | grep '^version' \
  | awk '{print $3}' \
  | sed -e 's/"//g')

if [ $NPM_VERSION = $PACKAGE_VERSION ]; then
    echo "Latest npm version is equal to current package version. Up the version to publish to npm."
    exit 0
fi

if [ $PACKAGE_VERSION != $CARGO_VERSION ]; then
    echo "Cargo crate version must be equal to npm package version ($CARGO_VERSION -> $PACKAGE_VERSION)"
    exit 0
fi

# npm
npm run build
npm run test

# publish package
npm set //registry.npmjs.org/:_authToken=${NPM_TOKEN}
npm publish