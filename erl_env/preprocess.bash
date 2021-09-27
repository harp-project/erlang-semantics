#!/bin/bash

find ../erl_tests -type f -name "*.erl" -exec sed -i "s/\([^a-z'@]\)_\([^a-z'@]\)/\1~\2/g"  {} +
find ../erl_tests -type f -name "*.erl" -exec sed -i "s/\([0-9]\)\./\1 ./g"  {} +
find ../erl_tests -type f -name "*.erl" -exec sed -i "s/\([0-9]\)\([+-]\)\([0-9]\)/\1 \2 \3/g"  {} +