#!/bin/bash

# Unset PCS_VIS_DATA_DIR if it's set
unset PCS_VIS_DATA_DIR
export NO_VIPER_FILE=true

directory_pass="local-testing/rpe/pass"
directory_fail="local-testing/rpe/fail"

./x.py build || exit 1

check_pass() {
    local file=$1
    echo "Checking $file (expected to pass)"
    target/debug/prusti-rustc --edition=2018 "$file"
    if [[ $? -ne 0 ]]; then
       echo "Test $file failed"
       exit 1
    fi
}

check_fail() {
    local file=$1
    echo "Checking $file (expected to fail)"
    target/debug/prusti-rustc --edition=2018 "$file"
    if [[ $? -eq 0 ]]; then
       echo "Test $file passed but it should have failed"
       exit 1
    fi
}

export -f check_pass
export -f check_fail

# Add this function to handle script termination
cleanup() {
    echo "Script interrupted. Exiting..."
    exit 1
}

# Set up the trap to catch SIGINT (Ctrl+C)
trap cleanup SIGINT

run_tests() {
    local directory=$1
    local check_function=$2
    if [[ "$parallel" == true ]]; then
        find "$directory" -type f -name "*.rs" | parallel -j 4 --halt now,fail=1 "$check_function"
    else
        while IFS= read -r FILE
        do
            "$check_function" "$FILE"
        done < <(find "$directory" -type f -name "*.rs")
    fi
    if [[ $? -ne 0 ]]; then
        exit 1
    fi
}

# Check if --parallel flag is passed
parallel=false
for arg in "$@"; do
    if [[ "$arg" == "--parallel" ]]; then
        parallel=true
        break
    fi
done

run_tests "$directory_pass" check_pass
run_tests "$directory_fail" check_fail

echo "All tests passed successfully"
