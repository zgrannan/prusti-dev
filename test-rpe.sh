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


directory_pass="local-testing/rpe/pass"
directory_fail="local-testing/rpe/fail"


check_pass() {
    local file=$1
    if [[ "$pcs" == true ]]; then
        echo "Checking $file (PCS only)"
        ../pcs/target/release/pcs_bin "$file"
        if [[ $? -ne 0 ]]; then
            echo "Test $file failed"
            exit 1
        fi
    else
        echo "Checking $file (expected to pass)"
        target/release/prusti-rustc --edition=2018 "$file"
        if [[ $? -ne 0 ]]; then
            echo "Test $file failed"
            exit 1
        fi
    fi
}

check_fail() {
    local file=$1
    if [[ "$pcs" == true ]]; then
        echo "Checking $file (PCS only)"
        ../pcs/target/release/pcs_bin "$file"
        if [[ $? -ne 0 ]]; then
            echo "Test $file failed"
            exit 1
        fi
    else
        echo "Checking $file (expected to fail)"
        target/release/prusti-rustc --edition=2018 "$file"
        if [[ $? -eq 0 ]]; then
            echo "Test $file passed but it should have failed"
            exit 1
        fi
    fi
}

export -f check_pass
export -f check_fail

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
    local check_function=$2
    local search_dir="$directory"
    if [[ "$old" == true ]]; then
        search_dir="$directory/old"
    fi
    while IFS= read -r FILE
    do
        "$check_function" "$FILE"
    done < <(find "$search_dir" -type f -name "*.rs")
    if [[ $? -ne 0 ]]; then
        exit 1
    fi
}

run_tests "$directory_pass" check_pass
run_tests "$directory_fail" check_fail

echo "All tests passed successfully"

if [[ -n "$PRUSTI_SERVER_PID" ]]; then
    echo "Stopping Prusti server..."
    kill $PRUSTI_SERVER_PID
    wait $PRUSTI_SERVER_PID 2>/dev/null
fi
