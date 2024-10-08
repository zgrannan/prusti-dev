#!/bin/bash

# Unset PCS_VIS_DATA_DIR if it's set
unset PCS_VIS_DATA_DIR
export NO_VIPER_FILE=true
export DYLD_LIBRARY_PATH=$(rustc --print sysroot)/lib
export PRUSTI_ENABLE_CACHE=false

# Check flags
old=false
pcs=false
for arg in "$@"; do
    if [[ "$arg" == "--old" ]]; then
        old=true
    elif [[ "$arg" == "--pcs" ]]; then
        pcs=true
    fi
done



directory_pass="local-testing/rpe/pass"
directory_fail="local-testing/rpe/fail"

prepend_failure_count() {
    local file=$1
    local count=$(grep -Fxc "$file" .failures)
    echo "$count $file"
}

list_files_by_failure_count() {
    local search_dir=$1
    local files=$(find "$search_dir" -type f -name "*.rs")
    for file in $files; do
        prepend_failure_count "$file"
    done | sort -n -r | cut -d' ' -f2-
}

check() {
    local file=$1
    local type=$2
    if [[ "$pcs" == true ]]; then
        echo "Checking $file (PCS only)"
        ../pcs/target/release/pcs_bin "$file"
        if [[ $? -ne 0 ]]; then
            echo "Test $file failed"
            exit 1
        fi
    else
        echo "Checking $file (expected to $type)"
        target/release/prusti-rustc --edition=2018 -Zpolonius "$file"
        if [[ "$type" == "pass" && $? -ne 0 ]]; then
            echo "Test $file failed (should have passed)"
            echo "$file" >> .failures
            exit 1
        elif [[ "$type" == "fail" && $? -eq 0 ]]; then
            echo "Test $file passed (should have failed)"
            echo "$file" >> .failures
            exit 1
        fi
    fi
}

export -f check

# Add this function to handle script termination
cleanup() {
    echo "Script interrupted. Exiting..."
    if [[ -n "$PRUSTI_SERVER_PID" ]]; then
        echo "Stopping Prusti server..."
        kill $PRUSTI_SERVER_PID
        wait $PRUSTI_SERVER_PID 2>/dev/null
    fi
    exit 1
}

# Set up the trap to catch SIGINT (Ctrl+C)
trap cleanup SIGINT

run_tests() {
    local directory=$1
    local check_type=$2
    local search_dir="$directory"
    if [[ "$old" == true ]]; then
        search_dir="$directory/old"
    fi
    while IFS= read -r FILE
    do
        check "$FILE" "$check_type"
    done < <(list_files_by_failure_count "$search_dir")
    if [[ $? -ne 0 ]]; then
        exit 1
    fi
}

if [[ "$pcs" == true ]]; then
    cd ../pcs/ && cargo build --all --release && cd - || exit 1
else
    ./x.py build --all --release || exit 1
    killall prusti-server-driver
    ./x.py run --release --bin prusti-server -- -p 3000 &
    PRUSTI_SERVER_PID=$!
    export PRUSTI_SERVER_ADDRESS=localhost:3000
    sleep 2
fi

run_tests "$directory_pass" "pass"
run_tests "$directory_fail" "fail"

echo "All tests passed successfully"

if [[ -n "$PRUSTI_SERVER_PID" ]]; then
    echo "Stopping Prusti server..."
    kill $PRUSTI_SERVER_PID
    wait $PRUSTI_SERVER_PID 2>/dev/null
fi
