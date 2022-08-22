#!/bin/bash

# Exit if any subcommand fails
set -e

# Get tag
TAG=$(cat ./zokrates_cli/Cargo.toml | grep '^version' | awk '{print $3}' | sed -e 's/"//g') && echo $TAG

# Use zokrates github bot
git config --global user.email $GH_USER

# Release on Dockerhub

## Build
docker build -t zokrates .

## Log into Dockerhub
echo $DOCKERHUB_PASS | docker login -u $DOCKERHUB_USER --password-stdin

## Release under `latest` tag
docker tag zokrates:latest zokrates/zokrates:latest
docker push zokrates/zokrates:latest
echo "Published zokrates/zokrates:latest"

## Release under $TAG tag
docker tag zokrates:latest zokrates/zokrates:$TAG
docker push zokrates/zokrates:$TAG
echo "Published zokrates/zokrates:$TAG"

# Release on Github
git tag -f latest
git tag -f $TAG
git push origin -f latest
git push origin $TAG

# Create a release draft
curl \
  -X POST \
  -H "Accept: application/vnd.github+json" \
  -H "Authorization: token $GH_TOKEN" \
  https://api.github.com/repos/Zokrates/ZoKrates/releases \
  -d "{\"tag_name\":\"$TAG\",\"draft\":true}"

# Build zokrates js
docker build -t zokrates_js -f zokrates_js/Dockerfile .

CID=$(docker create zokrates_js)

docker cp ${CID}:/build zokrates_js/dist
docker rm -f ${CID}

cd zokrates_js/dist

# Publish zokrates_js to npmjs
chmod +x publish.sh
./publish.sh

# Publish book
MDBOOK_TAR="https://github.com/rust-lang-nursery/mdBook/releases/download/v0.2.1/mdbook-v0.2.1-x86_64-unknown-linux-gnu.tar.gz"

cd ../../zokrates_book

## Install mdbook
wget -qO- $MDBOOK_TAR | tar xvz

## Build book
./mdbook build

## Deploy to github.io
pip3 install ghp-import
git clone https://github.com/Zokrates/zokrates.github.io.git && cd zokrates.github.io
ghp-import -n -p -f -m "Documentation upload. Version:  $TAG" -b "master" -r https://zokratesbot:"$GH_TOKEN"@github.com/Zokrates/zokrates.github.io.git ../book
echo "Published book"