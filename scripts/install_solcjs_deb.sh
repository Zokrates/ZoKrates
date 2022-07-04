#!/bin/bash

apt-get update -y
apt-get install -y curl gnupg sudo build-essential git
curl -sL https://deb.nodesource.com/setup_16.x | bash -
apt-get install -y nodejs
npm i -g solc