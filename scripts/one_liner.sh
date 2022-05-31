#!/bin/sh

set -e

help() {
    cat <<'EOF'
Install ZoKrates

Usage:
    one_liner.sh [options]

Options:
    -f, --force     Force overwriting an existing installation
    --to LOCATION   Where to install (default ~/.zokrates)
EOF
}

check_cmd() {
    command -v "$1" > /dev/null 2>&1
}

need_cmd() {
    if ! check_cmd "$1"; then
        err "need '$1' (command not found)"
    fi
}

get_bitness() {
    need_cmd head
    # Architecture detection without dependencies beyond coreutils.
    # ELF files start out "\x7fELF", and the following byte is
    #   0x01 for 32-bit and
    #   0x02 for 64-bit.
    # The printf builtin on some shells - like dash - only supports octal
    # escape sequences, so we use those.
    local _current_exe_head
    _current_exe_head=$(head -c 5 /proc/self/exe )
    if [ "$_current_exe_head" = "$(printf '\177ELF\001')" ]; then
        echo 32
    elif [ "$_current_exe_head" = "$(printf '\177ELF\002')" ]; then
        echo 64
    else
        err "unknown platform bitness"
    fi
}

get_endianness() {
    local cputype=$1
    local suffix_eb=$2
    local suffix_el=$3

    # detect endianness without od/hexdump, like get_bitness() does.
    need_cmd head
    need_cmd tail

    local _current_exe_endianness
    _current_exe_endianness="$(head -c 6 /proc/self/exe | tail -c 1)"
    if [ "$_current_exe_endianness" = "$(printf '\001')" ]; then
        echo "${cputype}${suffix_el}"
    elif [ "$_current_exe_endianness" = "$(printf '\002')" ]; then
        echo "${cputype}${suffix_eb}"
    else
        err "unknown platform endianness"
    fi
}

get_architecture() {
    local _ostype _cputype _bitness _arch
    _ostype="$(uname -s)"
    _cputype="$(uname -m)"

    if [ "$_ostype" = Linux ]; then
        if [ "$(uname -o)" = Android ]; then
            _ostype=Android
        fi
    fi

    if [ "$_ostype" = Darwin ] && [ "$_cputype" = i386 ]; then
        # Darwin `uname -m` lies
        if sysctl hw.optional.x86_64 | grep -q ': 1'; then
            _cputype=x86_64
        fi
    fi

    case "$_ostype" in

        Android)
            _ostype=linux-android
            ;;

        Linux)
            _ostype=unknown-linux-gnu
            _bitness=$(get_bitness)
            ;;

        FreeBSD)
            _ostype=unknown-freebsd
            ;;

        NetBSD)
            _ostype=unknown-netbsd
            ;;

        DragonFly)
            _ostype=unknown-dragonfly
            ;;

        Darwin)
            _ostype=apple-darwin
            ;;

        MINGW* | MSYS* | CYGWIN*)
            _ostype=pc-windows-gnu
            ;;

        *)
            err "unrecognized OS type: $_ostype"
            ;;

    esac

    case "$_cputype" in

        i386 | i486 | i686 | i786 | x86)
            _cputype=i686
            ;;

        xscale | arm)
            _cputype=arm
            if [ "$_ostype" = "linux-android" ]; then
                _ostype=linux-androideabi
            fi
            ;;

        armv6l)
            _cputype=arm
            if [ "$_ostype" = "linux-android" ]; then
                _ostype=linux-androideabi
            else
                _ostype="${_ostype}eabihf"
            fi
            ;;

        armv7l | armv8l)
            _cputype=armv7
            if [ "$_ostype" = "linux-android" ]; then
                _ostype=linux-androideabi
            else
                _ostype="${_ostype}eabihf"
            fi
            ;;

        aarch64 | arm64)
            _cputype=aarch64
            ;;

        x86_64 | x86-64 | x64 | amd64)
            _cputype=x86_64
            ;;

        mips)
            _cputype=$(get_endianness mips '' el)
            ;;

        mips64)
            if [ "$_bitness" -eq 64 ]; then
                # only n64 ABI is supported for now
                _ostype="${_ostype}abi64"
                _cputype=$(get_endianness mips64 '' el)
            fi
            ;;

        ppc)
            _cputype=powerpc
            ;;

        ppc64)
            _cputype=powerpc64
            ;;

        ppc64le)
            _cputype=powerpc64le
            ;;

        *)
        err "unknown CPU type: $_cputype"
    esac

    # Detect 64-bit linux with 32-bit userland
    if [ "${_ostype}" = unknown-linux-gnu ] && [ "${_bitness}" -eq 32 ]; then
        case $_cputype in
            x86_64)
                _cputype=i686
                ;;
            mips64)
                _cputype=$(get_endianness mips '' el)
                ;;
            powerpc64)
                _cputype=powerpc
                ;;
        esac
    fi

    # Detect armv7 but without the CPU features Rust needs in that build,
    # and fall back to arm.
    # See https://github.com/rust-lang/rustup.rs/issues/587.
    if [ "$_ostype" = "unknown-linux-gnueabihf" ] && [ "$_cputype" = armv7 ]; then
        if ensure grep '^Features' /proc/cpuinfo | grep -q -v neon; then
            # At least one processor does not have NEON.
            _cputype=arm
        fi
    fi

    _arch="${_cputype}-${_ostype}"

    RETVAL="$_arch"
}

say() {
    echo "ZoKrates: $1"
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

main() {
    need_cmd curl

    force=false
    while test $# -gt 0; do
        case $1 in
            --force | -f)
                force=true
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
    need_cmd curl
    need_cmd install
    need_cmd mkdir
    need_cmd mktemp
    need_cmd tar

    git="ZoKrates/ZoKrates"

    url="https://github.com/$git"

    url="$url/releases"

    tag=$(curl -Ls -w %{url_effective} -o /dev/null "$url/latest" | cut -d'"' -f2 | rev | cut -d'/' -f1 | rev)
    say_err "Tag: latest ($tag)"

    # detect host architecture
    get_architecture || return 1
    arch="$RETVAL"

    # find file extension. For now always tar.gz
    ext="tar.gz"

    say_err "Detected architecture: $arch"

    # Set target directory
    if [ -z $dest ]; then
        dest="$HOME/.zokrates"
    fi

    say_err "Installing to: $dest"

    # Fetch archive
    url="$url/download/$tag/zokrates-$tag-$arch.$ext"
    say_err "Fetching: $url"

    td=$(mktemp -d || mktemp -d -t tmp)
    curl -sLf --show-error $url | tar -C $td -xzf -

    if [ -d $dest ]; then
      if [ $force = true ]; then
        rm -rf $dest/*
        cp -r $td/* $dest
      else
        read -p "ZoKrates is already installed, overwrite (y/n)? " answer < /dev/tty
        case ${answer} in
            y|Y )
                rm -rf $dest/*
                cp -r $td/* $dest
            ;;
            * )
                rm -rf $td
                exit 1
            ;;
        esac
      fi
    else
      mkdir -p $dest
      cp -r $td/* $dest
    fi

    mkdir -p $dest/bin
    mv $dest/zokrates* $dest/bin && chmod 755 $dest/bin/*
    rm -rf $td

    abspath=$(cd "$(dirname "$dest")" && pwd)/$(basename "$dest")

    cat <<EOF

ZoKrates was installed successfully!
If this is the first time you're installing ZoKrates run the following:
export PATH=\$PATH:$abspath/bin
EOF
}

main "$@" || exit 1
