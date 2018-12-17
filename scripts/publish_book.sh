# Exit if any subcommand fails
set -e

if [ "$CIRCLE_BRANCH" == "develop" ]; then
    apt-get update
    apt-get -qq install git python-minimal
    python --version
    cargo install mdbook
    cd zokrates_book && mdbook build
    git config --global user.email "stefan.deml+zokratesbot@decentriq.ch"
    git clone https://github.com/Zokrates/zokrates.github.io.git
    git clone https://github.com/davisp/ghp-import.git
    cd zokrates.github.io
    TAG=$(cat ../zokrates_cli/Cargo.toml | grep '^version' | awk '{print $3}' | sed -e 's/"//g') && echo $TAG
    ../ghp-import/ghp_import.py -n -p -f -m "Documentation upload. Version:  $TAG" -b "master" -r https://zokratesbot:"$GH_TOKEN"@github.com/Zokrates/zokrates.github.io.git ../book
    echo "Published book"
fi

