#!/bin/bash

apt-get update -y
apt-get install -y curl gnupg sudo build-essential git
curl -L https://foundry.paradigm.xyz | bash
$HOME/.foundry/bin/foundryup