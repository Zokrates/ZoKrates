#!/bin/bash

# This script is intended for maintainers only to generate changelog markdown before new releases.
# The generated markdown can be added to the main CHANGELOG.md file located at the root of the repository.

set -e

if [ -z "$1" ]; then
   echo "Usage: $0 TAG" >&2
   exit 1
fi

function join { local IFS="$1"; shift; echo "$*"; }
function qdate
{
    if type -p gdate > /dev/null; then
        gdate "$@";
    else
        date "$@";
    fi
}

CHANGELOG_PATH='changelogs/unreleased'

tag=$1
unreleased=$(ls -t ${CHANGELOG_PATH})

echo -e "Generating CHANGELOG markdown from ${CHANGELOG_PATH}\n"
cat << EOT
## [${tag}] - $(qdate '+%Y-%m-%d')

### Release
- https://github.com/Zokrates/ZoKrates/releases/tag/${tag}

### Changes
EOT

for file in $unreleased
do
    IFS=$'-' read -ra entry <<< "$file"
    contents=$(cat ${CHANGELOG_PATH}/${file} | tr '\n' ' ')
    author=$(join '-' ${entry[@]:1})
    echo "- ${contents} (#${entry[0]}, @${author})"
done

echo -e "\nCopy and paste the markdown above to the appropriate CHANGELOG file."
echo "Be sure to run: git rm ${CHANGELOG_PATH}/*"