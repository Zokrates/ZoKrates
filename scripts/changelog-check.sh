#!/bin/bash

set +x

if [ -z "$CI" ]; then
   echo "This script is intended to be run only on Github Actions." >&2
   exit 1
fi

CHANGELOG_PATH='changelogs/unreleased'

pr_number=$(echo $GITHUB_REF | cut -d / -f 3)
changelog="${CHANGELOG_PATH}/${pr_number}-*"

if [ ! -f "$changelog" ]; then
    echo "Pull request #${pr_number:-?} is missing a changelog. Please add a changelog to ${CHANGELOG_PATH}."
    exit 1
fi