#!/bin/bash

apt-get update -y
apt-get install -y curl gnupg sudo build-essential git
curl -L https://foundry.paradigm.xyz | bash
export PATH="$PATH:/root/.foundry/bin"
foundryup