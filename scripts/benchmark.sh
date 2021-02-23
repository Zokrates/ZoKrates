#!/bin/bash

cmd=$*
format="mem=%K rss=%M elapsed=%E cpu=%P cpu.sys=%S inputs=%I outputs=%O"

echo 'Benchmarking ' $cmd;
/usr/bin/time -f "$format" bash -c "$cmd"