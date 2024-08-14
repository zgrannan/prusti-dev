#!/bin/bash

# Unset PCS_VIS_DATA_DIR if it's set
unset PCS_VIS_DATA_DIR

directory_pass="local-testing/rpe/pass"
directory_fail="local-testing/rpe/fail"

./x.py build || exit 1

check_pass() {
    local file=$1
    echo "Checking $file (expected to pass)"
    ./x.py run --features=vir_debug --bin prusti-rustc -- --edition=2018 "$file"
    if [[ $? -ne 0 ]]; then
       echo "Test $file failed"
       exit 1
    fi
}

check_fail() {
    local file=$1
    echo "Checking $file (expected to fail)"
    ./x.py run --features=vir_debug --bin prusti-rustc -- --edition=2018 "$file"
    if [[ $? -eq 0 ]]; then
       echo "Test $file passed but it should have failed"
       exit 1
    fi
}

export -f check_pass
export -f check_fail

find "$directory_pass" -type f -name "*.rs" | parallel -j 4 --halt now,fail=1 check_pass
# find "$directory_pass" -type f -name "*.rs" | while IFS= read -r FILE
# do
#     check_pass "$FILE"
# done
if [[ $? -ne 0 ]]; then
   exit 1
fi

find "$directory_fail" -type f -name "*.rs" | parallel -j 4 --halt now,fail=1 check_fail
# find "$directory_fail" -type f -name "*.rs" | while IFS= read -r FILE
# do
#     check_fail "$FILE"
# done
if [[ $? -ne 0 ]]; then
   exit 1
fi

echo "All tests passed successfully"
