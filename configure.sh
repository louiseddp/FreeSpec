#!/bin/bash

for i in "core" "exec" "stdlib/console" "stdlib/env"; do
    cd ${i}
    ./configure.sh
    cd - > /dev/null
done
