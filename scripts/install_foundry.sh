#!/bin/bash

apt-get update -y
apt-get install -y curl gnupg sudo build-essential git
git config --global user.name "abc"
git config --global user.email "abc@example.com"
curl -L https://foundry.paradigm.xyz | bash
$HOME/.foundry/bin/foundryup