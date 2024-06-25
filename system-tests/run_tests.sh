#!/bin/bash

CMD="_install/main.exe"
TEST_DIR="system-tests"
TMP_FILE="/tmp/.test-results"

runtest () {
    # diff weirdness -> https://unix.stackexchange.com/a/423188
    $CMD $1 | diff <(grep -vE '^\s*$' -)  <(grep -vE '^\s*$' $2) &> $TMP_FILE
    if [[ $? != 0 ]]; then
        echo "*** Test failed: $1";
        cat $TMP_FILE;
    fi
}

TEST_DIR="system-tests"
for i in {0..28}; do
    INPUT_FILE="$TEST_DIR/pt${i}_input.txt"
    OUTPUT_FILE="$TEST_DIR/pt${i}_output.txt"
    runtest $INPUT_FILE $OUTPUT_FILE
done

