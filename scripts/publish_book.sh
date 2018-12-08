# Exit if any subcommand fails
set -e

apt-get update
apt-get -qq install git python-minimal
python --version
cargo install mdbook
cd zokrates_book && mdbook build
git config --global user.email "stefan.deml+zokratesbot@decentriq.ch"
git clone https://github.com/Zokrates/zokrates.github.io.git
git clone https://github.com/davisp/ghp-import.git
cd zokrates.github.io
../ghp-import/ghp_import.py -n -p -f -m "Documentation upload" -b "master" -r https://17cd8c4c351b617eba3847d4f2af39c997e9758b@github.com/Zokrates/zokrates.github.io.git ../book
echo "Published book"
