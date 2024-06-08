#!/bin/bash

directory_pass="local-testing/rpe/pass"
directory_fail="local-testing/rpe/fail"

./x.py build

parallel_check_pass() {
    local file=$1
    echo "Checking $file (expected to pass)"
    ./x.py run --features=vir_debug --bin prusti-rustc -- --edition=2018 "$file"
    if [[ $? -ne 0 ]]; then
       echo "Test $file failed"
       exit 1
    fi
}

parallel_check_fail() {
    local file=$1
    echo "Checking $file (expected to fail)"
    ./x.py run --features=vir_debug --bin prusti-rustc -- --edition=2018 "$file"
    if [[ $? -eq 0 ]]; then
       echo "Test $file passed but it should have failed"
       exit 1
    fi
}

export -f parallel_check_pass
export -f parallel_check_fail

find "$directory_pass" -type f -name "*.rs" | parallel -j 8 --halt now,fail=1 parallel_check_pass
if [[ $? -ne 0 ]]; then
   exit 1
fi

find "$directory_fail" -type f -name "*.rs" | parallel -j 8 --halt now,fail=1 parallel_check_fail

if [[ $? -ne 0 ]]; then
   exit 1
fi

echo "All tests passed successfully"
