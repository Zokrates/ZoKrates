#!/bin/bash
# Usage: ./clang-format.sh zokrates_core/lib

dir=$1

for file in $dir/*.cpp $dir/*.hpp $dir/*.tcc; do
  clang-format -i -style=WebKit -verbose $file
done