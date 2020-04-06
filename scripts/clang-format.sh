#!/bin/bash

dir=$1
ret=0

for file in $dir/*.cpp $dir/*.hpp; do
  clang-format -i -style=WebKit -verbose $file
  out=$(git diff --exit-code $file)

  if [ $? -ne 0 ]; then
    ret=1
    echo "ERROR: clang-format diff in: $file"
    echo "$out"
  fi
done

exit $ret