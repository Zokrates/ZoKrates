#!/bin/bash

set +x

if [ -z "$CI" ]; then
   echo "This script is intended to be run only on Github Actions." >&2
   exit 1
fi

CHANGELOG_PATH='changelogs/unreleased'

pr_number=$(echo $GITHUB_REF | cut -d / -f 3)
changelog="${CHANGELOG_PATH}/${pr_number}-${GITHUB_ACTOR}"

if [ ! -f "$changelog" ]; then
    echo "Pull request #${pr_number:-?} is missing a changelog. Please add a changelog to ${CHANGELOG_PATH}."
    exit 1
fi

cl_diff=$(git diff --exit-code $GITHUB_HEAD_REF CHANGELOG.md)
if [ -n "$cl_diff" ]; then
    echo "Pull requests should not directly modify the main CHANGELOG.md file. For more information, please read changelogs/README.md"
    exit 1
fi