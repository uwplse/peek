#!/usr/bin/env bash

make all_handtuned

$@

function stopwatch {
    t0=$(date +%s.%N)
    $@ > /dev/null
    t1=$(date +%s.%N)
    echo "$t1 - $t0" | bc
}

for i in $(seq 10); do
    stopwatch $@
done | sort -g | head -n 1
