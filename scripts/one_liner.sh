#!/bin/sh

set -e

help() {
    cat <<'EOF'
Install a binary release ZoKrates

Usage:
    one_liner.sh [options]

Options:
    -f, --force     Force overwriting an existing binary
    --tag TAG       Tag (version) of the crate to install (default <latest release>)
    --to LOCATION   Where to install the binary (default ~/.cargo/bin)
EOF
}

say() {
    echo "install.sh: $1"
}

say_err() {
    say "$1" >&2
}

err() {
    if [ ! -z $td ]; then
        rm -rf $td
    fi

    say_err "ERROR $1"
    exit 1
}

need() {
    if ! command -v $1 > /dev/null 2>&1; then
        err "need $1 (command not found)"
    fi
}

force=false
while test $# -gt 0; do
    case $1 in
        --force | -f)
            force=true
            ;;
        --tag)
            tag=$2
            shift
            ;;
        --to)
            dest=$2
            shift
            ;;
        *)
            ;;
    esac
    shift
done

# Dependencies
need basename
need curl
need install
need mkdir
need mktemp
need tar
need rustc

# Optional dependencies
if [ -z $tag ]; then
    need cut
    need rev
fi

git="schaeff/zokrates"

url="https://github.com/$git"
say_err "GitHub repository: $url"

if [ -z $crate ]; then
    crate=$(echo $git | cut -d'/' -f2)
fi

say_err "Crate: $crate"

url="$url/releases"

if [ -z $tag ]; then
    tag=$(curl -s "$url/latest" | cut -d'"' -f2 | rev | cut -d'/' -f1 | rev)
    say_err "Tag: latest ($tag)"
else
    say_err "Tag: $tag"
fi

if [ -z $target ]; then
    target=$(rustc -Vv | grep host | cut -d' ' -f2)
fi

say_err "Target: $target"

if [ -z $dest ]; then
    dest="$HOME/.cargo/bin"
fi

say_err "Installing to: $dest"

url="$url/download/$tag/$crate-$tag-$target.tar.gz"

say_err "Url: $url"

td=$(mktemp -d || mktemp -d -t tmp)
curl -sLf --show-error $url | tar -C $td -xz

for f in $(ls $td); do
    test -x $td/$f || continue

    if [ -e "$dest/$f" ] && [ $force = false ]; then
        err "$f already exists in $dest"
    else
        mkdir -p $dest
        install -m 755 $td/$f $dest
    fi
done

rm -rf $td
