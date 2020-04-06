#!/bin/bash

cd zokrates_core/lib
clang-format -i -style=WebKit -verbose *.cpp *.hpp

modified=`git status | grep "modified"`
if [[ -z $modified ]]; then
  exit 0;
fi

git diff
git reset HEAD --hard

exit 1