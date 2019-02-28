#!/bin/bash

apt-get update -y
apt-get install -y curl gnupg sudo build-essential
curl -sL https://deb.nodesource.com/setup_11.x | bash -
apt-get install -y nodejs
npm i -g solc