#!/bin/bash

set -euo pipefail

directory_pass="local-testing/rpe/pass"
directory_fail="local-testing/rpe/fail"

./x.py build

find "$directory_pass" -type f -name "*.rs" | while read -r file; do
    echo "Checking $file (expected to pass)"
    ./x.py run --features=vir_debug --bin prusti-rustc -- --edition=2018 "$file"
    java -jar ~/silicon/target/scala-2.13/silicon.jar local-testing/simple.vpr
done

find "$directory_fail" -type f -name "*.rs" | while read -r file; do
    echo "Checking $file (expected to fail)"
    ./x.py run --features=vir_debug --bin prusti-rustc -- --edition=2018 "$file"
    set +e
    java -jar ~/silicon/target/scala-2.13/silicon.jar local-testing/simple.vpr
    if [[ $? -eq 0 ]]; then
       echo "It passed but it should have failed"
    fi
    set -e
done

echo "All tests passed successfully"
