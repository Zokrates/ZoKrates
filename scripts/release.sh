# Exit if any subcommand fails
set -e

# Get tag
TAG=$(cat ./zokrates_cli/Cargo.toml | grep '^version' | awk '{print $3}' | sed -e 's/"//g') && echo $TAG

# Release on Github
git tag $TAG
# git push origin $TAG

# Release on Dockerhub

# Build
docker build -t zokrates .

## Release under `latest` tag
docker tag zokrates:latest zokrates/zokrates:latest
#docker push zokrates/zokrates:latest

## Release under $TAG tag
docker tag zokrates:latest zokrates/zokrates:$TAG
#docker push zokrates/zokrates:$TAG

# Publish book
python --version
cargo install mdbook
cd zokrates_book && mdbook build
git config --global user.email "stefan.deml+zokratesbot@decentriq.ch"
git clone https://github.com/Zokrates/zokrates.github.io.git
git clone https://github.com/davisp/ghp-import.git
cd zokrates.github.io
#../ghp-import/ghp_import.py -n -p -f -m "Documentation upload. Version:  $TAG" -b "master" -r https://zokratesbot:"$GH_TOKEN"@github.com/Zokrates/zokrates.github.io.git ../book
echo "Published book"

